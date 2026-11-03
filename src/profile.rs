//! `pqready profile`: one row per flagged program, saying what it is, what it
//! uses quantum-vulnerable crypto for, and who controls it.
//!
//! A program is flagged when `dependencies.csv` has a row for it with class
//! `quantum_vulnerable`, `review` or `pq_implementation`. Its row combines:
//!
//! - identity: security.txt (from the ELF) and, with `--rpc`, the name and
//!   version in its on-chain IDL (legacy Anchor account, then Program Metadata);
//! - crypto roles: what each dependency row is used for, from the syscall and
//!   its selectors (curve id, BN254 operation), precompile references and PQ
//!   tables;
//! - control: the upgrade authority, how many programs it controls and how
//!   many of those are flagged;
//! - joins: optional labels (by program id, then by authority), reviews and
//!   activity CSVs, whose columns are copied with a prefix.
//!
//! Input CSVs are read by header name, so extra columns are ignored.

use crate::{address, fetch, identity};
use anyhow::{Context, Result, bail};
use rayon::prelude::*;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::path::{Path, PathBuf};

pub struct ProfileOpts {
    pub raw: PathBuf,
    pub scan: PathBuf,
    pub out: PathBuf,
    pub rpc: Option<String>,
    pub labels: Option<PathBuf>,
    pub reviews: Option<PathBuf>,
    pub activity: Option<PathBuf>,
    pub sort_by: Option<String>,
}

const FLAGGING_CLASSES: [&str; 3] = ["quantum_vulnerable", "review", "pq_implementation"];

/// One dependencies.csv row, by header name.
#[derive(Debug, Clone, Default)]
pub struct Dependency {
    pub kind: String,
    pub name: String,
    pub class: String,
    pub evidence: String,
    pub selectors: Vec<u64>,
}

/// Curve ids of the sol_curve_* syscalls (solana-define-syscall 5.3.0
/// definitions, curve25519 / bls12-381 / secp256r1); 0x80 marks big-endian.
fn curve_name(id: u64) -> &'static str {
    match id & 0x7f {
        0 => "Curve25519 Edwards",
        1 => "Ristretto255",
        4 => "BLS12-381 pairing",
        5 => "BLS12-381 G1",
        6 => "BLS12-381 G2",
        7 => "secp256r1",
        _ => "unknown curve",
    }
}

/// sol_alt_bn128_group_op operations (solana-bn254 3.2.1); 0x80 = little-endian.
fn bn254_op(op: u64) -> &'static str {
    match op & 0x7f {
        0..=2 => "BN254 G1 arithmetic",
        3 => "BN254 pairing",
        4..=6 => "BN254 G2 arithmetic",
        _ => "BN254 unknown operation",
    }
}

/// sol_alt_bn128_compression operations (solana-bn254 3.2.1).
fn bn254_compression(op: u64) -> &'static str {
    match op & 0x7f {
        0 | 1 => "BN254 G1 compression",
        2 | 3 => "BN254 G2 compression",
        _ => "BN254 unknown compression",
    }
}

/// What a dependency is used for, one role per distinct selector. Empty for
/// rows that are not roles (benign, weak PQ immediates).
pub fn roles(d: &Dependency) -> Vec<String> {
    let per_selector = |f: &dyn Fn(u64) -> String, none: &str| -> Vec<String> {
        if d.selectors.is_empty() {
            vec![none.to_string()]
        } else {
            d.selectors
                .iter()
                .map(|&s| f(s))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect()
        }
    };
    match (d.kind.as_str(), d.name.as_str()) {
        ("syscall", "sol_secp256k1_recover") => vec!["secp256k1 ECDSA public-key recovery".into()],
        ("syscall", "sol_curve_validate_point") => per_selector(
            &|s| format!("{} point validation", curve_name(s)),
            "curve point validation",
        ),
        ("syscall", "sol_curve_group_op") => per_selector(
            &|s| format!("{} group arithmetic", curve_name(s)),
            "curve group arithmetic",
        ),
        ("syscall", "sol_curve_multiscalar_mul") => per_selector(
            &|s| format!("{} multiscalar multiplication", curve_name(s)),
            "curve multiscalar multiplication",
        ),
        ("syscall", "sol_curve_pairing_map") => {
            per_selector(&|s| format!("{} pairing", curve_name(s)), "curve pairing")
        }
        ("syscall", "sol_curve_decompress") => per_selector(
            &|s| format!("{} point decompression", curve_name(s)),
            "curve point decompression",
        ),
        ("syscall", "sol_alt_bn128_group_op") => {
            per_selector(&|s| bn254_op(s).into(), "BN254 group operation")
        }
        ("syscall", "sol_alt_bn128_compression") => {
            per_selector(&|s| bn254_compression(s).into(), "BN254 compression")
        }
        ("syscall", "sol_big_mod_exp") => vec!["big-integer modular exponentiation".into()],
        ("syscall", "sol_poseidon") => vec!["Poseidon hash".into()],
        ("precompile_ref", "ed25519_precompile") => {
            vec![format!("Ed25519 signature precompile [{}]", d.evidence)]
        }
        ("precompile_ref", "secp256k1_precompile") => {
            vec![format!("secp256k1 signature precompile [{}]", d.evidence)]
        }
        ("precompile_ref", "secp256r1_precompile") => {
            vec![format!("secp256r1 signature precompile [{}]", d.evidence)]
        }
        ("precompile_ref", "zk_elgamal_proof_program") => {
            vec![format!("ZK ElGamal proof program [{}]", d.evidence)]
        }
        _ => vec![],
    }
}

/// Coarse uses, from the roles. Several can apply.
pub fn uses(roles: &BTreeSet<String>) -> BTreeSet<&'static str> {
    let has = |s: &str| roles.iter().any(|r| r.contains(s));
    let mut u = BTreeSet::new();
    if has("BN254 pairing") || has("BLS12-381 pairing") {
        u.insert("zk_proof_verification");
    }
    if has("secp256k1") {
        u.insert("ethereum_signatures");
    }
    if has("secp256r1") {
        u.insert("passkey_signatures");
    }
    if has("Ed25519 signature") {
        u.insert("ed25519_signatures");
    }
    if has("ZK ElGamal") || has("Ristretto255") {
        u.insert("confidential_balances");
    }
    if has("BLS12-381") && !has("BLS12-381 pairing") {
        u.insert("bls_arithmetic");
    }
    if has("Curve25519 Edwards") {
        u.insert("curve25519_arithmetic");
    }
    if has("modular exponentiation") {
        u.insert("rsa_or_modexp");
    }
    u
}

/// Read a CSV into header-keyed maps.
fn read_csv(path: &Path) -> Result<Vec<BTreeMap<String, String>>> {
    let mut r =
        csv::Reader::from_path(path).with_context(|| format!("reading {}", path.display()))?;
    let headers = r.headers()?.clone();
    r.records()
        .map(|rec| {
            let rec = rec?;
            Ok(headers
                .iter()
                .zip(rec.iter())
                .map(|(h, v)| (h.to_string(), v.to_string()))
                .collect())
        })
        .collect()
}

fn read_dependencies(scan: &Path) -> Result<BTreeMap<String, Vec<Dependency>>> {
    let mut out: BTreeMap<String, Vec<Dependency>> = BTreeMap::new();
    for row in read_csv(&scan.join("dependencies.csv"))? {
        let get = |k: &str| row.get(k).cloned().unwrap_or_default();
        let selectors = get("selectors")
            .split(';')
            .filter_map(|s| s.trim().parse().ok())
            .collect();
        out.entry(get("program_id")).or_default().push(Dependency {
            kind: get("kind"),
            name: get("name"),
            class: get("class"),
            evidence: get("evidence"),
            selectors,
        });
    }
    Ok(out)
}

/// Output column names, and per key its (column, value) pairs.
type Joined = (Vec<String>, HashMap<String, Vec<(String, String)>>);

/// Rows of an optional CSV keyed by the first non-empty of `keys`, other
/// columns prefixed.
fn keyed(path: Option<&Path>, keys: &[&str], prefix: &str) -> Result<Joined> {
    let Some(path) = path else {
        return Ok((vec![], HashMap::new()));
    };
    let rows = read_csv(path)?;
    let mut columns = BTreeSet::new();
    let mut map = HashMap::new();
    for row in rows {
        let Some(key) = keys
            .iter()
            .find_map(|k| row.get(*k).filter(|v| !v.is_empty()))
        else {
            continue;
        };
        let vals: Vec<_> = row
            .iter()
            .filter(|(k, _)| !keys.contains(&k.as_str()))
            // "label" in labels.csv stays "label"; other columns get the prefix.
            .map(|(k, v)| {
                (
                    if *k == prefix.trim_end_matches('_') {
                        k.clone()
                    } else {
                        format!("{prefix}{k}")
                    },
                    v.clone(),
                )
            })
            .collect();
        columns.extend(vals.iter().map(|(k, _)| k.clone()));
        map.insert(key.clone(), vals);
    }
    if map.is_empty() {
        bail!(
            "{}: no rows with a {} column",
            path.display(),
            keys.join(" or ")
        );
    }
    Ok((columns.into_iter().collect(), map))
}

#[derive(Default)]
struct Identity {
    security_txt: BTreeMap<String, String>,
    idl: Option<identity::Idl>,
    idl_address: String,
    idl_error: String,
}

/// Fetch and parse each program's IDL accounts. Legacy Anchor first, then
/// Program Metadata; the first that parses wins.
/// Per program: the IDL if one parsed, the account it came from, and the
/// parse errors otherwise.
type FetchedIdl = (Option<identity::Idl>, String, String);

fn fetch_idls(rpc: &str, programs: &[String]) -> Result<HashMap<String, FetchedIdl>> {
    let addrs: Vec<(
        String,
        address::Address,
        Option<address::Address>,
        Option<address::Address>,
    )> = programs
        .par_iter()
        .filter_map(|p| {
            let id = address::from_base58(p)?;
            Some((
                p.clone(),
                id,
                identity::legacy_idl_address(&id),
                identity::metadata_idl_address(&id),
            ))
        })
        .collect();
    let mut query = Vec::new();
    for (_, _, legacy, meta) in &addrs {
        for a in [legacy, meta].into_iter().flatten() {
            query.push(address::to_base58(a));
        }
    }
    eprintln!("fetching {} IDL accounts", query.len());
    let data: HashMap<String, Option<Vec<u8>>> = query
        .iter()
        .cloned()
        .zip(fetch::fetch_accounts(rpc, &query)?)
        .collect();

    let mut out = HashMap::new();
    for (p, id, legacy, meta) in addrs {
        let mut errors = Vec::new();
        let mut found = None;
        let candidates = [
            (
                legacy,
                &(|d: &[u8], _: &address::Address| identity::parse_legacy_idl(d))
                    as &dyn Fn(&[u8], &address::Address) -> Result<identity::Idl>,
            ),
            (meta, &identity::parse_metadata_idl),
        ];
        for (addr, parse) in candidates {
            let Some(addr) = addr else { continue };
            let a = address::to_base58(&addr);
            if let Some(Some(d)) = data.get(&a) {
                match parse(d, &id) {
                    Ok(idl) => {
                        found = Some((idl, a));
                        break;
                    }
                    Err(e) => errors.push(format!("{a}: {e:#}")),
                }
            }
        }
        let entry = match found {
            Some((idl, a)) => (Some(idl), a, String::new()),
            None => (None, String::new(), errors.join("; ")),
        };
        out.insert(p, entry);
    }
    Ok(out)
}

pub fn run(o: &ProfileOpts) -> Result<()> {
    let deps = read_dependencies(&o.scan)?;
    let flagged: Vec<String> = deps
        .iter()
        .filter(|(_, ds)| {
            ds.iter()
                .any(|d| FLAGGING_CLASSES.contains(&d.class.as_str()))
        })
        .map(|(p, _)| p.clone())
        .collect();
    let flagged_set: BTreeSet<&str> = flagged.iter().map(|s| s.as_str()).collect();
    eprintln!("{} flagged programs", flagged.len());

    let programs: HashMap<String, fetch::ProgramRow> =
        csv::Reader::from_path(o.raw.join("programs.csv"))?
            .deserialize::<fetch::ProgramRow>()
            .map(|r| r.map(|p| (p.program_id.clone(), p)))
            .collect::<Result<_, _>>()?;

    // Upgrade-authority clusters over all programs and over flagged ones.
    let mut controls: HashMap<&str, (usize, usize)> = HashMap::new();
    for p in programs
        .values()
        .filter(|p| !p.upgrade_authority.is_empty())
    {
        let c = controls.entry(p.upgrade_authority.as_str()).or_default();
        c.0 += 1;
        c.1 += flagged_set.contains(p.program_id.as_str()) as usize;
    }

    let mut ids: HashMap<String, Identity> = flagged
        .par_iter()
        .map(|p| {
            let path = o.raw.join("elf").join(format!("{p}.so"));
            let security_txt = fs::read(path)
                .ok()
                .and_then(|b| identity::security_txt(&b))
                .unwrap_or_default();
            (
                p.clone(),
                Identity {
                    security_txt,
                    ..Default::default()
                },
            )
        })
        .collect();
    if let Some(rpc) = &o.rpc {
        for (p, (idl, addr, err)) in fetch_idls(rpc, &flagged)? {
            let id = ids.entry(p).or_default();
            (id.idl, id.idl_address, id.idl_error) = (idl, addr, err);
        }
    }

    let (label_cols, labels) = keyed(o.labels.as_deref(), &["program_id", "authority"], "label_")?;
    let (review_cols, reviews) = keyed(o.reviews.as_deref(), &["program_id"], "review_")?;
    let (activity_cols, activity) = keyed(o.activity.as_deref(), &["program_id"], "activity_")?;

    let mut header: Vec<String> = [
        "program_id",
        "name",
        "name_source",
        "project_url",
        "source_code",
        "contacts",
        "idl_name",
        "idl_version",
        "idl_source",
        "idl_address",
        "idl_url",
        "idl_error",
        "classes",
        "uses",
        "crypto_roles",
        "pq_tables",
        "loader",
        "upgradeable",
        "upgrade_authority",
        "authority_programs",
        "authority_flagged_programs",
        "label_matched_by",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    header.extend(
        label_cols
            .iter()
            .chain(&review_cols)
            .chain(&activity_cols)
            .cloned(),
    );

    let mut rows: Vec<Vec<String>> = Vec::new();
    for p in &flagged {
        let ds = &deps[p];
        let prog = programs.get(p);
        let id = ids.remove(p).unwrap_or_default();
        let st = |k: &str| id.security_txt.get(k).cloned().unwrap_or_default();
        let idl = id.idl.clone().unwrap_or_default();
        let (name, name_source) = if !st("name").is_empty() {
            (st("name"), "security_txt")
        } else if !idl.name.is_empty() {
            (idl.name.clone(), idl.source)
        } else {
            (String::new(), "")
        };
        let classes: BTreeSet<&str> = ds
            .iter()
            .map(|d| d.class.as_str())
            .filter(|c| FLAGGING_CLASSES.contains(c))
            .collect();
        let role_set: BTreeSet<String> = ds.iter().flat_map(roles).collect();
        let pq: BTreeSet<String> = ds
            .iter()
            .filter(|d| d.kind == "pq_table" && d.class != "weak")
            .map(|d| format!("{} [{}]", d.name, d.evidence))
            .collect();
        let authority = prog
            .map(|p| p.upgrade_authority.clone())
            .unwrap_or_default();
        let (ap, af) = controls
            .get(authority.as_str())
            .copied()
            .unwrap_or_default();

        let (label_by, label_vals) = if let Some(v) = labels.get(p) {
            ("program_id", Some(v))
        } else if let Some(v) = labels.get(&authority).filter(|_| !authority.is_empty()) {
            ("authority", Some(v))
        } else {
            ("", None)
        };
        let join = |e: &mut Vec<String>, cols: &[String], vals: Option<&Vec<(String, String)>>| {
            for c in cols {
                e.push(
                    vals.and_then(|v| v.iter().find(|(k, _)| k == c))
                        .map(|(_, v)| v.clone())
                        .unwrap_or_default(),
                );
            }
        };
        let mut row = vec![
            p.clone(),
            name,
            name_source.into(),
            st("project_url"),
            st("source_code"),
            st("contacts"),
            idl.name,
            idl.version,
            idl.source.into(),
            id.idl_address,
            idl.url,
            id.idl_error,
            classes.into_iter().collect::<Vec<_>>().join(";"),
            uses(&role_set).into_iter().collect::<Vec<_>>().join(";"),
            role_set.into_iter().collect::<Vec<_>>().join(";"),
            pq.into_iter().collect::<Vec<_>>().join(";"),
            prog.map(|p| p.loader.clone()).unwrap_or_default(),
            prog.map(|p| p.upgradeable.to_string()).unwrap_or_default(),
            authority.clone(),
            if authority.is_empty() {
                String::new()
            } else {
                ap.to_string()
            },
            if authority.is_empty() {
                String::new()
            } else {
                af.to_string()
            },
            label_by.into(),
        ];
        join(&mut row, &label_cols, label_vals);
        join(&mut row, &review_cols, reviews.get(p));
        join(&mut row, &activity_cols, activity.get(p));
        rows.push(row);
    }

    if let Some(col) = &o.sort_by {
        let i = header
            .iter()
            .position(|h| h == col)
            .with_context(|| format!("--sort-by {col}: no such column"))?;
        // Numbers descending (largest first), then text ascending; empty last.
        rows.sort_by(|a, b| {
            let (x, y) = (&a[i], &b[i]);
            match (x.parse::<f64>(), y.parse::<f64>()) {
                (Ok(x), Ok(y)) => y.total_cmp(&x),
                (Ok(_), Err(_)) => std::cmp::Ordering::Less,
                (Err(_), Ok(_)) => std::cmp::Ordering::Greater,
                _ => (x.is_empty(), x).cmp(&(y.is_empty(), y)),
            }
        });
    }

    fs::create_dir_all(&o.out)?;
    let path = o.out.join("profile.csv");
    let mut w = csv::Writer::from_path(&path)?;
    w.write_record(&header)?;
    for r in rows {
        w.write_record(&r)?;
    }
    w.flush()?;
    eprintln!("wrote {}", path.display());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dep(kind: &str, name: &str, selectors: &[u64]) -> Dependency {
        Dependency {
            kind: kind.into(),
            name: name.into(),
            evidence: "e".into(),
            selectors: selectors.to_vec(),
            ..Default::default()
        }
    }

    #[test]
    fn roles_from_selectors() {
        assert_eq!(
            roles(&dep("syscall", "sol_alt_bn128_group_op", &[0, 2, 3, 0x83])),
            ["BN254 G1 arithmetic", "BN254 pairing"]
        );
        assert_eq!(
            roles(&dep("syscall", "sol_curve_group_op", &[1])),
            ["Ristretto255 group arithmetic"]
        );
        assert_eq!(
            roles(&dep("syscall", "sol_curve_validate_point", &[0x87])),
            ["secp256r1 point validation"]
        );
        assert_eq!(
            roles(&dep("syscall", "sol_curve_multiscalar_mul", &[])),
            ["curve multiscalar multiplication"]
        );
        assert_eq!(
            roles(&dep("precompile_ref", "ed25519_precompile", &[])),
            ["Ed25519 signature precompile [e]"]
        );
        assert!(roles(&dep("pq_table", "ml-dsa", &[])).is_empty());
    }

    #[test]
    fn uses_from_roles() {
        let r: BTreeSet<String> = [
            "BN254 pairing",
            "BN254 G1 arithmetic",
            "secp256k1 ECDSA public-key recovery",
        ]
        .map(String::from)
        .into();
        assert_eq!(
            uses(&r),
            ["ethereum_signatures", "zk_proof_verification"].into()
        );
    }

    #[test]
    fn profile_end_to_end() {
        let d = std::env::temp_dir().join(format!("pqready-profile-{}", std::process::id()));
        let (raw, scan, out) = (d.join("raw"), d.join("scan"), d.join("out"));
        fs::create_dir_all(raw.join("elf")).unwrap();
        fs::create_dir_all(&scan).unwrap();
        fs::write(
            raw.join("programs.csv"),
            "program_id,loader,programdata,deploy_slot,upgradeable,upgrade_authority,status,elf_len,elf_sha256,fetched_slot\n\
             P1,upgradeable,D1,1,true,AUTH,deployed,10,x,5\n\
             P2,upgradeable,D2,1,true,AUTH,deployed,10,x,5\n\
             P3,upgradeable,D3,1,true,AUTH,deployed,10,x,5\n",
        )
        .unwrap();
        let mut elf = b"junk".to_vec();
        elf.extend_from_slice(b"=======BEGIN SECURITY.TXT V1=======\0name\0Bridge\0project_url\0https://b.example\0=======END SECURITY.TXT V1=======\0");
        fs::write(raw.join("elf/P1.so"), elf).unwrap();
        fs::write(
            scan.join("dependencies.csv"),
            "program_id,loader,upgradeable,kind,name,class,evidence,count,selectors,unknown_selector_sites,unreachable_sites,detail\n\
             P1,upgradeable,true,syscall,sol_secp256k1_recover,quantum_vulnerable,direct,1,,0,0,x\n\
             P2,upgradeable,true,syscall,sol_alt_bn128_group_op,quantum_vulnerable,direct,3,0;3,0,0,\n\
             P3,upgradeable,true,precompile_ref,instructions_sysvar,marker,rodata_bytes,1,,0,0,\n",
        )
        .unwrap();
        fs::write(d.join("labels.csv"), "authority,label\nAUTH,Example Labs\n").unwrap();
        fs::write(d.join("reviews.csv"), "program_id,verdict\nP2,confirmed\n").unwrap();
        run(&ProfileOpts {
            raw,
            scan,
            out: out.clone(),
            rpc: None,
            labels: Some(d.join("labels.csv")),
            reviews: Some(d.join("reviews.csv")),
            activity: None,
            sort_by: Some("program_id".into()),
        })
        .unwrap();
        let rows = read_csv(&out.join("profile.csv")).unwrap();
        fs::remove_dir_all(&d).unwrap();
        assert_eq!(rows.len(), 2, "P3 has only a marker row");
        let (p1, p2) = (&rows[0], &rows[1]);
        assert_eq!(
            (
                p1["program_id"].as_str(),
                p1["name"].as_str(),
                p1["name_source"].as_str()
            ),
            ("P1", "Bridge", "security_txt")
        );
        assert_eq!(p1["uses"], "ethereum_signatures");
        assert_eq!(
            (
                p1["authority_programs"].as_str(),
                p1["authority_flagged_programs"].as_str()
            ),
            ("3", "2")
        );
        assert_eq!(
            (p1["label"].as_str(), p1["label_matched_by"].as_str()),
            ("Example Labs", "authority")
        );
        assert_eq!(p2["crypto_roles"], "BN254 G1 arithmetic;BN254 pairing");
        assert_eq!(
            (p1["review_verdict"].as_str(), p2["review_verdict"].as_str()),
            ("", "confirmed")
        );
    }
}
