use ff::PrimeField;
use libipld::cid::CidGeneric;
use libipld::Ipld;

use multihash::Code;
use multihash::MultihashDigest;
use multihash::MultihashGeneric;

pub trait LurkField: ff::PrimeField {
    // FIELD_CODEC must only fit into u16. it's annotated u64 here to respect
    // the multicodec convention
    const FIELD_CODEC: u64;
    const HASH_CODEC: u64;
    const LURK_CODEC_PREFIX: u64 = 0xc0de;
    const REPR_LITTLE_ENDIAN: bool;
    const NUM_BYTES: usize;

    fn from_bytes(bs: &[u8]) -> Option<Self> {
        let mut def: Self::Repr = Self::default().to_repr();
        def.as_mut().copy_from_slice(bs);
        Self::from_repr(def).into()
    }

    fn from_bytes_vartime(bs: &[u8]) -> Option<Self> {
        if bs.is_empty() {
            return None;
        }
        let mut res = Self::zero();

        let _256 = Self::from(256);

        for b in bs {
            res.mul_assign(&_256);
            res.add_assign(&Self::from(u64::from(*b)));
        }
        Some(res)
    }

    fn to_multicodec(f: Self) -> u64 {
        let bytes: Vec<u8> = f.to_repr().as_ref().to_vec();
        let tag: u32 = if Self::REPR_LITTLE_ENDIAN {
            let size = bytes.len();
            let bytes: [u8; 4] = [
                bytes[size],
                bytes[size - 1],
                bytes[size - 2],
                bytes[size - 3],
            ];
            u32::from_le_bytes(bytes)
        } else {
            let bytes: [u8; 4] = [bytes[0], bytes[1], bytes[2], bytes[3]];
            u32::from_be_bytes(bytes)
        };
        Self::LURK_CODEC_PREFIX << 48 & Self::FIELD_CODEC << 32 & u64::from(tag)
    }

    fn to_multihash(f: Self) -> MultihashGeneric<{ Self::NUM_BYTES }> {
        MultihashGeneric::wrap(Self::HASH_CODEC, f.to_repr().as_ref()).unwrap()
    }
    fn to_cid(tag: Self, digest: Self) -> CidGeneric<{ Self::NUM_BYTES }> {
        CidGeneric::new_v1(Self::to_multicodec(tag), Self::to_multihash(digest))
    }
}
