//! Who a program is, from two sources that state it rather than guess it:
//!
//! - `security.txt`, embedded in the ELF by the `solana-security-txt` crate:
//!   "=======BEGIN SECURITY.TXT V1=======\0", then NUL-terminated key and value
//!   strings in pairs, then "=======END SECURITY.TXT V1=======\0"
//!   (neodyme-labs/solana-security-txt, security-txt/src/parser.rs);
//! - the program's IDL, published on chain in one of two places:
//!   - legacy Anchor IDL account at
//!     create_with_seed(find_program_address([], program), "anchor:idl", program):
//!     8-byte discriminator, 32-byte authority, u32 data length, then
//!     zlib-compressed JSON (anchor lang/src/idl.rs);
//!   - Program Metadata program (ProgM6JCCvbYkfKqJYHePx4xxSUSqJp7rh8Lyv7nk7S),
//!     canonical IDL at find_program_address([program, "", "idl" padded to 16],
//!     PMP): a 96-byte header (discriminator 2 = Metadata, program, authority,
//!     mutable, canonical, seed[16], encoding, compression, format,
//!     data_source, data_length u32, 5 bytes padding), then the data
//!     (solana-program/program-metadata, program/src/state/header.rs).
//!     Direct data is decoded (encoding: 0 hex, 1 UTF-8, 2 base58, 3 base64),
//!     then decompressed (0 none, 1 gzip, 2 zlib), as Anchor's CLI does
//!     (cli/src/fetch/pmp.rs).
//!
//! The IDL's name is `metadata.name` (Anchor 0.30 and later) or the top-level
//! `name` (earlier versions).

use crate::address::{self, Address};
use anyhow::{Context, Result, anyhow, bail};
use base64::Engine;
use flate2::read::{GzDecoder, ZlibDecoder};
use memchr::memmem;
use std::collections::BTreeMap;
use std::io::Read;

const SECURITY_TXT_BEGIN: &[u8] = b"=======BEGIN SECURITY.TXT V1=======\0";
const SECURITY_TXT_END: &[u8] = b"=======END SECURITY.TXT V1=======\0";

/// The key/value pairs of the first security.txt block in `elf`, or None.
pub fn security_txt(elf: &[u8]) -> Option<BTreeMap<String, String>> {
    let start = memmem::find(elf, SECURITY_TXT_BEGIN)? + SECURITY_TXT_BEGIN.len();
    let end = start + memmem::find(&elf[start..], SECURITY_TXT_END)?;
    let mut parts = elf[start..end].split(|&b| b == 0);
    let mut out = BTreeMap::new();
    while let (Some(k), Some(v)) = (parts.next(), parts.next()) {
        let k = String::from_utf8_lossy(k).trim().to_string();
        if !k.is_empty() {
            out.insert(k, String::from_utf8_lossy(v).trim().to_string());
        }
    }
    Some(out)
}

pub const PROGRAM_METADATA_PROGRAM: &str = "ProgM6JCCvbYkfKqJYHePx4xxSUSqJp7rh8Lyv7nk7S";

/// Address of the legacy Anchor IDL account.
pub fn legacy_idl_address(program: &Address) -> Option<Address> {
    let (signer, _) = address::find_program_address(&[], program)?;
    address::create_with_seed(&signer, "anchor:idl", program)
}

/// Address of the canonical IDL in the Program Metadata program.
pub fn metadata_idl_address(program: &Address) -> Option<Address> {
    let pmp = address::from_base58(PROGRAM_METADATA_PROGRAM)?;
    let mut seed = [0u8; 16];
    seed[..3].copy_from_slice(b"idl");
    address::find_program_address(&[program, &[], &seed], &pmp).map(|(a, _)| a)
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Idl {
    pub name: String,
    pub version: String,
    /// "anchor_idl_account" or "program_metadata"
    pub source: &'static str,
    /// For Program Metadata stored as a URL: the URL (not fetched).
    pub url: String,
}

fn idl_from_json(json: &[u8], source: &'static str) -> Result<Idl> {
    let v: serde_json::Value = serde_json::from_slice(json).context("IDL is not JSON")?;
    let field = |k: &str| {
        v.get("metadata")
            .and_then(|m| m.get(k))
            .or_else(|| v.get(k))
            .and_then(|x| x.as_str())
            .unwrap_or_default()
            .to_string()
    };
    Ok(Idl {
        name: field("name"),
        version: field("version"),
        source,
        url: String::new(),
    })
}

fn inflate(data: &[u8], gzip: bool) -> Result<Vec<u8>> {
    let mut out = Vec::new();
    if gzip {
        GzDecoder::new(data).read_to_end(&mut out)?;
    } else {
        ZlibDecoder::new(data).read_to_end(&mut out)?;
    }
    Ok(out)
}

/// Parse a legacy Anchor IDL account's data.
pub fn parse_legacy_idl(data: &[u8]) -> Result<Idl> {
    let len = data
        .get(40..44)
        .ok_or_else(|| anyhow!("IDL account too short"))?;
    let len = u32::from_le_bytes(len.try_into().unwrap()) as usize;
    let compressed = data
        .get(44..44 + len)
        .ok_or_else(|| anyhow!("IDL data length out of range"))?;
    idl_from_json(&inflate(compressed, false)?, "anchor_idl_account")
}

const METADATA_HEADER_LEN: usize = 96;
const METADATA_DISCRIMINATOR: u8 = 2;

/// Parse a Program Metadata account holding `program`'s canonical IDL.
pub fn parse_metadata_idl(data: &[u8], program: &Address) -> Result<Idl> {
    if data.len() < METADATA_HEADER_LEN {
        bail!("metadata account too short");
    }
    if data[0] != METADATA_DISCRIMINATOR {
        bail!("not a Metadata account (discriminator {})", data[0]);
    }
    if &data[1..33] != program {
        bail!("metadata account is for another program");
    }
    let (encoding, compression, format, data_source) = (data[82], data[83], data[84], data[85]);
    let len = u32::from_le_bytes(data[86..90].try_into().unwrap()) as usize;
    let payload = data
        .get(METADATA_HEADER_LEN..METADATA_HEADER_LEN + len)
        .ok_or_else(|| anyhow!("metadata length out of range"))?;
    let decoded = match encoding {
        0 => hex::decode(std::str::from_utf8(payload)?.trim()).context("hex payload")?,
        1 => payload.to_vec(),
        2 => bs58::decode(payload).into_vec().context("base58 payload")?,
        3 => base64::engine::general_purpose::STANDARD
            .decode(payload)
            .context("base64 payload")?,
        e => bail!("unknown encoding {e}"),
    };
    let bytes = match compression {
        0 => decoded,
        1 => inflate(&decoded, true)?,
        2 => inflate(&decoded, false)?,
        c => bail!("unknown compression {c}"),
    };
    match data_source {
        0 if format == 1 => idl_from_json(&bytes, "program_metadata"),
        0 => bail!("metadata format {format} is not JSON"),
        1 => Ok(Idl {
            source: "program_metadata",
            url: String::from_utf8_lossy(&bytes).trim().to_string(),
            ..Default::default()
        }),
        s => bail!("metadata data source {s} (external) not followed"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use flate2::Compression;
    use flate2::write::{GzEncoder, ZlibEncoder};
    use std::io::Write;

    fn zlib(b: &[u8]) -> Vec<u8> {
        let mut e = ZlibEncoder::new(Vec::new(), Compression::default());
        e.write_all(b).unwrap();
        e.finish().unwrap()
    }

    #[test]
    fn security_txt_pairs() {
        let mut elf = vec![0xAAu8; 50];
        elf.extend_from_slice(SECURITY_TXT_BEGIN);
        elf.extend_from_slice(b"name\0Example\0project_url\0https://example.org\0source_code\0https://github.com/x/y\0");
        elf.extend_from_slice(SECURITY_TXT_END);
        elf.extend_from_slice(&[0xBB; 10]);
        let t = security_txt(&elf).unwrap();
        assert_eq!(t["name"], "Example");
        assert_eq!(t["project_url"], "https://example.org");
        assert_eq!(t["source_code"], "https://github.com/x/y");
        assert_eq!(security_txt(&[0u8; 100]), None);
    }

    #[test]
    fn legacy_idl_new_and_old_name_layouts() {
        for (json, name) in [
            (
                &br#"{"address":"x","metadata":{"name":"swap","version":"0.1.0","spec":"0.1.0"}}"#
                    [..],
                "swap",
            ),
            (
                br#"{"version":"0.2.0","name":"old_style","instructions":[]}"#,
                "old_style",
            ),
        ] {
            let c = zlib(json);
            let mut acct = vec![0u8; 8 + 32];
            acct.extend_from_slice(&(c.len() as u32).to_le_bytes());
            acct.extend_from_slice(&c);
            assert_eq!(parse_legacy_idl(&acct).unwrap().name, name);
        }
    }

    fn metadata_account(
        program: &Address,
        encoding: u8,
        compression: u8,
        format: u8,
        source: u8,
        payload: &[u8],
    ) -> Vec<u8> {
        let mut d = vec![0u8; METADATA_HEADER_LEN];
        d[0] = METADATA_DISCRIMINATOR;
        d[1..33].copy_from_slice(program);
        d[82] = encoding;
        d[83] = compression;
        d[84] = format;
        d[85] = source;
        d[86..90].copy_from_slice(&(payload.len() as u32).to_le_bytes());
        d.extend_from_slice(payload);
        d
    }

    #[test]
    fn metadata_idl_encodings_and_compressions() {
        let p = [7u8; 32];
        let json = br#"{"metadata":{"name":"vault","version":"1.2.0"}}"#;
        let mut gz = GzEncoder::new(Vec::new(), Compression::default());
        gz.write_all(json).unwrap();
        let gz = gz.finish().unwrap();
        let b64 = base64::engine::general_purpose::STANDARD.encode(zlib(json));
        for acct in [
            metadata_account(&p, 1, 0, 1, 0, json),
            metadata_account(&p, 1, 1, 1, 0, &gz),
            metadata_account(&p, 3, 2, 1, 0, b64.as_bytes()),
            metadata_account(&p, 0, 0, 1, 0, hex::encode(json).as_bytes()),
        ] {
            let idl = parse_metadata_idl(&acct, &p).unwrap();
            assert_eq!(
                (idl.name.as_str(), idl.version.as_str()),
                ("vault", "1.2.0")
            );
        }
        let url = parse_metadata_idl(
            &metadata_account(&p, 1, 0, 1, 1, b"https://example.org/idl.json"),
            &p,
        )
        .unwrap();
        assert_eq!(url.url, "https://example.org/idl.json");
        assert!(
            parse_metadata_idl(&metadata_account(&[8; 32], 1, 0, 1, 0, json), &p).is_err(),
            "other program"
        );
    }
}
