use ff::Field;
use ff::PrimeField;
use libipld::cid::CidGeneric;
use libipld::Ipld;

use core::cmp::Ord;
use core::cmp::Ordering;
use multihash::Code;
use multihash::MultihashDigest;
use multihash::MultihashGeneric;

use core::ops::AddAssign;
use core::ops::MulAssign;

pub trait LurkField: ff::PrimeField {
    const FIELD_CODEC: u64;
    const HASH_CODEC: u64;
    const LURK_CODEC_PREFIX: u64 = 0xc0de;
    const NUM_BYTES: usize;

    fn from_bytes(bs: &[u8]) -> Option<Self> {
        let mut def: Self::Repr = Self::default().to_repr();
        def.as_mut().copy_from_slice(bs);
        Self::from_repr(def).into()
    }

    //// This should probably be removed
    //fn from_bytes_vartime(bs: &[u8]) -> Option<Self>;

    // Tags have to be `u32` because we're trying to fit them into `u64`
    // multicodecs without overlapping with the existing table. If we can
    // implement arbitrary-sized codecs though we can relax this to `u64`.
    // Arguably should be Option<u32> to catch larger field elems.
    fn to_tag(f: Self) -> u32;

    fn to_multicodec(f: Self) -> u64 {
        let tag: u32 = Self::to_tag(f);

        Self::LURK_CODEC_PREFIX << 48 & Self::FIELD_CODEC << 32 & u64::from(tag)
    }

    fn from_multicodec(codec: u64) -> Option<Self> {
        Self::from(codec & 0x0000_0000_ffff_ffff)
    }

    fn to_multihash(f: Self) -> MultihashGeneric<{ Self::NUM_BYTES }> {
        MultihashGeneric::wrap(Self::HASH_CODEC, f.to_repr().as_ref()).unwrap()
    }

    fn from_multihash(hash: MultihashGeneric<{ Self::NUM_BYTES }>) -> Option<Self> {
        Self::from_bytes(hash.digest())
    }

    fn to_cid(tag: Self, digest: Self) -> CidGeneric<{ Self::NUM_BYTES }> {
        CidGeneric::new_v1(Self::to_multicodec(tag), Self::to_multihash(digest))
    }
}

impl LurkField for blstrs::Scalar {
    const FIELD_CODEC: u64 = 1;
    const HASH_CODEC: u64 = 2;
    const LURK_CODEC_PREFIX: u64 = 0xc0de;
    const NUM_BYTES: usize = 32;

    //// This doesn't include a check that the bytes are canonical, so it
    //// shouldn't be used. Including it for now just as a check that we
    //// understand the byte representation
    //fn from_bytes_vartime(bs: &[u8]) -> Option<Self> {
    //    if bs.is_empty() || bs.len() != Self::NUM_BYTES {
    //        return None;
    //    }

    //    let chunks: &[[u8; 8]] = unsafe { bs.as_chunks_unchecked::<8>() };

    //    let mut res = Self::zero();

    //    let shift = Self::from(u64::MAX) + Self::from(1);

    //    for chunk in chunks.iter().rev() {
    //        let limb = u64::from_le_bytes(*chunk);
    //        res.mul_assign(&shift);
    //        res.add_assign(&Self::from(limb));
    //    }
    //    Some(res)
    //}

    fn to_tag(f: Self) -> u32 {
        let bytes: Vec<u8> = f.to_repr().as_ref().to_vec();
        let bytes: [u8; 4] = [bytes[0], bytes[1], bytes[2], bytes[3]];
        u32::from_le_bytes(bytes)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use blstrs::Scalar as Fr;

    //#[test]
    //fn test_from_bytes_consistency() {
    //    let bytes = [[0x00; 8], [0x11; 8], [0x22; 8], [0x33; 8]].concat();
    //    let f1 = <Fr as LurkField>::from_bytes(&bytes);
    //    let f2 = <Fr as LurkField>::from_bytes_vartime(&bytes);
    //    assert_eq!(f1, f2);
    //}
    #[test]
    fn test_tag_consistency() {
        let f1 = Fr::from(0xdead_beef);
        let tag = <Fr as LurkField>::to_tag(f1);
        let f2 = Fr::from(tag as u64);
        assert_eq!(f1, f2);
    }
}
