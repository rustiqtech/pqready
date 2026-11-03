//! Pull every program from an RPC node: metadata first, ELFs second.
//!
//! Loaders and account layouts (verify against the Agave release you scan):
//! - Upgradeable loader: `Program` accounts (36 bytes: u32 tag = 2, programdata
//!   address) and `ProgramData` accounts (u32 tag = 3, u64 deploy slot,
//!   Option<Pubkey> upgrade authority = 1 + 32 bytes; ELF from offset 45).
//!   Buffer accounts (tag 1) are excluded.
//! - Loader v1/v2: the executable account's data is the ELF; immutable.
//! - Loader v4: header = u64 slot, 32-byte authority (or next version once
//!   finalized), u64 status (0 retracted, 1 deployed, 2 finalized); ELF from 48.
//!
//! getProgramAccounts on the loaders needs `--account-index program-id` on the
//! node, otherwise each call scans the whole accounts DB and may time out.

use anyhow::{Context, Result, anyhow, bail};
use base64::Engine;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
    collections::HashMap,
    fs,
    path::{Path, PathBuf},
    thread,
    time::Duration,
};

pub const LOADER_V1: &str = "BPFLoader1111111111111111111111111111111111";
pub const LOADER_V2: &str = "BPFLoader2111111111111111111111111111111111";
pub const LOADER_UPGRADEABLE: &str = "BPFLoaderUpgradeab1e11111111111111111111111";
pub const LOADER_V4: &str = "LoaderV411111111111111111111111111111111111";

pub const UPGRADEABLE_PROGRAM_LEN: u64 = 36;
pub const PROGRAMDATA_HEADER_LEN: usize = 45;
pub const LOADER_V4_HEADER_LEN: usize = 48;

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct ProgramRow {
    pub program_id: String,
    /// v1 | v2 | upgradeable | v4
    pub loader: String,
    pub programdata: String,
    pub deploy_slot: Option<u64>,
    pub upgradeable: bool,
    /// Empty when not upgradeable.
    pub upgrade_authority: String,
    /// deployed | closed | retracted | finalized
    pub status: String,
    pub elf_len: Option<usize>,
    pub elf_sha256: String,
    pub fetched_slot: u64,
}

pub struct FetchOpts {
    pub rpc: String,
    pub out: PathBuf,
    pub batch: usize,
    pub skip_elfs: bool,
}

struct Rpc {
    client: reqwest::blocking::Client,
    url: String,
    id: u64,
}

impl Rpc {
    fn new(url: &str) -> Result<Self> {
        let parsed = reqwest::Url::parse(url.trim()).with_context(|| {
            format!("--rpc {url:?} is not a valid URL (expected e.g. http://127.0.0.1:8899)")
        })?;
        if !matches!(parsed.scheme(), "http" | "https") {
            bail!(
                "--rpc {url:?}: scheme must be http or https (expected e.g. http://127.0.0.1:8899)"
            );
        }
        let url = parsed.as_str();
        let client = reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(900))
            .build()?;
        Ok(Self {
            client,
            url: url.to_string(),
            id: 0,
        })
    }

    fn call(&mut self, method: &str, params: Value) -> Result<Value> {
        let mut delay = Duration::from_secs(2);
        for attempt in 0..5 {
            self.id += 1;
            let body = json!({"jsonrpc": "2.0", "id": self.id, "method": method, "params": params});
            let res = self
                .client
                .post(&self.url)
                .json(&body)
                .send()
                .and_then(|r| r.error_for_status())
                .and_then(|r| r.json::<Value>());
            match res {
                Ok(v) => {
                    if let Some(err) = v.get("error") {
                        bail!("{method}: {err}");
                    }
                    return v
                        .get("result")
                        .cloned()
                        .ok_or_else(|| anyhow!("{method}: no result"));
                }
                // A request that cannot be built will never succeed; don't retry it.
                Err(e) if e.is_builder() => return Err(e).context(method.to_string()),
                // A timeout on a full scan will time out again; retrying only multiplies the wait.
                Err(e) if e.is_timeout() => {
                    return Err(e).with_context(|| {
                        format!(
                            "{method} timed out. For getProgramAccounts, start the node with \
                             --account-index program-id"
                        )
                    });
                }
                Err(e) if attempt < 4 => {
                    eprintln!("{method}: {e}; retrying in {delay:?}");
                    thread::sleep(delay);
                    delay *= 2;
                }
                Err(e) => return Err(e).context(method.to_string()),
            }
        }
        unreachable!()
    }

    /// getProgramAccounts -> (pubkey, decoded data, executable)
    fn program_accounts(
        &mut self,
        owner: &str,
        filters: Value,
        data_slice: Option<(usize, usize)>,
    ) -> Result<Vec<(String, Vec<u8>, bool)>> {
        let mut cfg =
            json!({"encoding": "base64+zstd", "commitment": "finalized", "filters": filters});
        if let Some((offset, length)) = data_slice {
            cfg["dataSlice"] = json!({"offset": offset, "length": length});
        }
        eprintln!("getProgramAccounts {owner} filters={filters} ...");
        let t = std::time::Instant::now();
        let res = self.call("getProgramAccounts", json!([owner, cfg]))?;
        eprintln!("  done in {:.1}s", t.elapsed().as_secs_f64());
        let arr = res
            .as_array()
            .ok_or_else(|| anyhow!("getProgramAccounts: not an array"))?;
        arr.iter()
            .map(|item| {
                let pubkey = item["pubkey"]
                    .as_str()
                    .ok_or_else(|| anyhow!("no pubkey"))?
                    .to_string();
                let data = decode_data(&item["account"]["data"])?;
                let exec = item["account"]["executable"].as_bool().unwrap_or(false);
                Ok((pubkey, data, exec))
            })
            .collect()
    }

    /// getMultipleAccounts -> data per address (None if missing)
    fn multiple_accounts(&mut self, addrs: &[String]) -> Result<Vec<Option<Vec<u8>>>> {
        let res = self.call(
            "getMultipleAccounts",
            json!([addrs, {"encoding": "base64+zstd", "commitment": "finalized"}]),
        )?;
        let arr = res["value"]
            .as_array()
            .ok_or_else(|| anyhow!("getMultipleAccounts: no value"))?;
        arr.iter()
            .map(|a| {
                if a.is_null() {
                    Ok(None)
                } else {
                    decode_data(&a["data"]).map(Some)
                }
            })
            .collect()
    }
}

/// Data of each account in `addrs` (base58), None for accounts that do not exist, fetched in
/// batches of 100 with getMultipleAccounts.
pub fn fetch_accounts(rpc_url: &str, addrs: &[String]) -> Result<Vec<Option<Vec<u8>>>> {
    let mut rpc = Rpc::new(rpc_url)?;
    let mut out = Vec::with_capacity(addrs.len());
    for chunk in addrs.chunks(100) {
        out.extend(rpc.multiple_accounts(chunk)?);
    }
    Ok(out)
}

fn decode_data(v: &Value) -> Result<Vec<u8>> {
    let s = v[0]
        .as_str()
        .ok_or_else(|| anyhow!("data not [string, encoding]"))?;
    let enc = v[1].as_str().unwrap_or("base64");
    let raw = base64::engine::general_purpose::STANDARD.decode(s)?;
    match enc {
        "base64" => Ok(raw),
        "base64+zstd" => Ok(zstd::stream::decode_all(&raw[..])?),
        other => bail!("unsupported encoding {other}"),
    }
}

/// (deploy slot, upgrade authority) from a ProgramData header.
pub fn parse_programdata_header(d: &[u8]) -> Option<(u64, Option<String>)> {
    if d.len() < PROGRAMDATA_HEADER_LEN || d[0..4] != [3, 0, 0, 0] {
        return None;
    }
    let slot = u64::from_le_bytes(d[4..12].try_into().ok()?);
    let auth = (d[12] == 1).then(|| bs58::encode(&d[13..45]).into_string());
    Some((slot, auth))
}

/// programdata address from an upgradeable Program account.
pub fn parse_program_account(d: &[u8]) -> Option<String> {
    (d.len() == UPGRADEABLE_PROGRAM_LEN as usize && d[0..4] == [2, 0, 0, 0])
        .then(|| bs58::encode(&d[4..36]).into_string())
}

fn sha256_hex(b: &[u8]) -> String {
    hex::encode(Sha256::digest(b))
}

fn elf_path(out: &Path, program_id: &str) -> PathBuf {
    out.join("elf").join(format!("{program_id}.so"))
}

/// Write the ELF unless already present (makes reruns resumable).
fn store_elf(out: &Path, program_id: &str, elf: &[u8]) -> Result<(usize, String)> {
    let p = elf_path(out, program_id);
    if !p.exists() {
        fs::write(&p, elf).with_context(|| format!("write {}", p.display()))?;
    }
    Ok((elf.len(), sha256_hex(elf)))
}

pub fn run(opts: &FetchOpts) -> Result<()> {
    fs::create_dir_all(opts.out.join("elf"))?;
    let mut rpc = Rpc::new(&opts.rpc)?;
    let slot = rpc
        .call("getSlot", json!([{"commitment": "finalized"}]))?
        .as_u64()
        .ok_or_else(|| anyhow!("getSlot"))?;
    eprintln!("fetching at finalized slot {slot}");
    let mut rows: Vec<ProgramRow> = Vec::new();

    // --- upgradeable loader: metadata pass ---
    let programs = rpc.program_accounts(
        LOADER_UPGRADEABLE,
        json!([{"dataSize": UPGRADEABLE_PROGRAM_LEN}]),
        None,
    )?;
    eprintln!("upgradeable Program accounts: {}", programs.len());
    let tag3 = bs58::encode([3u8, 0, 0, 0]).into_string();
    let headers = rpc.program_accounts(
        LOADER_UPGRADEABLE,
        json!([{"memcmp": {"offset": 0, "bytes": tag3}}]),
        Some((0, PROGRAMDATA_HEADER_LEN)),
    )?;
    eprintln!("ProgramData headers: {}", headers.len());
    let header_by_addr: HashMap<String, (u64, Option<String>)> = headers
        .iter()
        .filter_map(|(addr, d, _)| parse_programdata_header(d).map(|h| (addr.clone(), h)))
        .collect();

    let mut upgradeable_idx: Vec<usize> = Vec::new();
    for (program_id, data, _) in &programs {
        let Some(pd) = parse_program_account(data) else {
            continue;
        };
        let row = match header_by_addr.get(&pd) {
            Some((deploy_slot, auth)) => ProgramRow {
                program_id: program_id.clone(),
                loader: "upgradeable".into(),
                programdata: pd,
                deploy_slot: Some(*deploy_slot),
                upgradeable: auth.is_some(),
                upgrade_authority: auth.clone().unwrap_or_default(),
                status: "deployed".into(),
                elf_len: None,
                elf_sha256: String::new(),
                fetched_slot: slot,
            },
            None => ProgramRow {
                program_id: program_id.clone(),
                loader: "upgradeable".into(),
                programdata: pd,
                deploy_slot: None,
                upgradeable: false,
                upgrade_authority: String::new(),
                status: "closed".into(),
                elf_len: None,
                elf_sha256: String::new(),
                fetched_slot: slot,
            },
        };
        if row.status == "deployed" {
            upgradeable_idx.push(rows.len());
        }
        rows.push(row);
    }

    // --- upgradeable loader: ELF pass (batched) ---
    if !opts.skip_elfs {
        for (n, chunk) in upgradeable_idx.chunks(opts.batch.clamp(1, 100)).enumerate() {
            // Skip already-downloaded ELFs, but still record their hash.
            let mut need: Vec<usize> = Vec::new();
            for &i in chunk {
                let p = elf_path(&opts.out, &rows[i].program_id);
                if p.exists() {
                    let b = fs::read(&p)?;
                    rows[i].elf_len = Some(b.len());
                    rows[i].elf_sha256 = sha256_hex(&b);
                } else {
                    need.push(i);
                }
            }
            if need.is_empty() {
                continue;
            }
            let addrs: Vec<String> = need.iter().map(|&i| rows[i].programdata.clone()).collect();
            let datas = rpc.multiple_accounts(&addrs)?;
            for (&i, d) in need.iter().zip(datas) {
                match d {
                    Some(d) if d.len() > PROGRAMDATA_HEADER_LEN => {
                        let (len, sha) = store_elf(
                            &opts.out,
                            &rows[i].program_id,
                            &d[PROGRAMDATA_HEADER_LEN..],
                        )?;
                        rows[i].elf_len = Some(len);
                        rows[i].elf_sha256 = sha;
                    }
                    _ => rows[i].status = "closed".into(),
                }
            }
            if n % 20 == 0 {
                eprintln!(
                    "ELF batches: {} / {}",
                    n + 1,
                    upgradeable_idx.len().div_ceil(opts.batch.clamp(1, 100))
                );
            }
        }
    }

    // --- loader v1 / v2: data is the ELF, immutable ---
    for (loader_id, label) in [(LOADER_V1, "v1"), (LOADER_V2, "v2")] {
        let accts = rpc.program_accounts(loader_id, json!([]), None)?;
        eprintln!("{label} accounts: {}", accts.len());
        for (program_id, data, executable) in accts {
            if !executable {
                continue;
            }
            let (elf_len, elf_sha256) = if opts.skip_elfs {
                (Some(data.len()), sha256_hex(&data))
            } else {
                let (l, s) = store_elf(&opts.out, &program_id, &data)?;
                (Some(l), s)
            };
            rows.push(ProgramRow {
                program_id,
                loader: label.into(),
                programdata: String::new(),
                deploy_slot: None,
                upgradeable: false,
                upgrade_authority: String::new(),
                status: "deployed".into(),
                elf_len,
                elf_sha256,
                fetched_slot: slot,
            });
        }
    }

    // --- loader v4 ---
    let accts = rpc.program_accounts(LOADER_V4, json!([]), None)?;
    eprintln!("v4 accounts: {}", accts.len());
    for (program_id, data, _) in accts {
        if data.len() < LOADER_V4_HEADER_LEN {
            continue;
        }
        let deploy_slot = u64::from_le_bytes(data[0..8].try_into().unwrap());
        let key = bs58::encode(&data[8..40]).into_string();
        let status_code = u64::from_le_bytes(data[40..48].try_into().unwrap());
        let status = match status_code {
            0 => "retracted",
            1 => "deployed",
            2 => "finalized",
            _ => "unknown",
        };
        let finalized = status_code == 2;
        let elf = &data[LOADER_V4_HEADER_LEN..];
        let (elf_len, elf_sha256) = if opts.skip_elfs || elf.is_empty() {
            (Some(elf.len()), sha256_hex(elf))
        } else {
            let (l, s) = store_elf(&opts.out, &program_id, elf)?;
            (Some(l), s)
        };
        rows.push(ProgramRow {
            program_id,
            loader: "v4".into(),
            programdata: if finalized {
                key.clone()
            } else {
                String::new()
            }, // next version
            deploy_slot: Some(deploy_slot),
            upgradeable: !finalized,
            upgrade_authority: if finalized { String::new() } else { key },
            status: status.into(),
            elf_len,
            elf_sha256,
            fetched_slot: slot,
        });
    }

    let path = opts.out.join("programs.csv");
    let mut w = csv::Writer::from_path(&path)?;
    for r in &rows {
        w.serialize(r)?;
    }
    w.flush()?;
    eprintln!("wrote {} rows to {}", rows.len(), path.display());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn programdata_header_with_and_without_authority() {
        let mut d = vec![3u8, 0, 0, 0];
        d.extend_from_slice(&123u64.to_le_bytes());
        d.push(1);
        d.extend_from_slice(&[7u8; 32]);
        let (slot, auth) = parse_programdata_header(&d).unwrap();
        assert_eq!(slot, 123);
        assert_eq!(auth.unwrap(), bs58::encode([7u8; 32]).into_string());

        d[12] = 0;
        assert_eq!(parse_programdata_header(&d).unwrap().1, None);
        d[0] = 1; // buffer tag
        assert!(parse_programdata_header(&d).is_none());
    }

    #[test]
    fn program_account() {
        let mut d = vec![2u8, 0, 0, 0];
        d.extend_from_slice(&[9u8; 32]);
        assert_eq!(
            parse_program_account(&d).unwrap(),
            bs58::encode([9u8; 32]).into_string()
        );
    }
}
