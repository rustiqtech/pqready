pub struct DataRegion<'a> {
    pub bytes: &'a [u8],
    pub address: u64,
}

/// The 32 bytes at virtual address `a`, if one data region holds all of them.
pub fn entry_at(regions: &[DataRegion<'_>], a: u64) -> Option<[u8; 32]> {
    regions.iter().find_map(|&DataRegion { bytes, address }| {
        let off = usize::try_from(a.checked_sub(address)?).ok()?;
        bytes
            .get(off..off + 32)
            .map(|s| <[u8; 32]>::try_from(s).unwrap())
    })
}
