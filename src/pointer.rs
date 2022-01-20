use std::{
    convert::TryInto,
    hash::{Hash, Hasher},
};

use blake3::Hasher as Blake3Hasher;

/// The value of the pointer, during evaluation.
pub type PtrValue = [u8; 32];

pub type PtrHasher = Blake3Hasher;

pub trait Tagged {
    type Tag: Into<u64>;

    fn tag(&self) -> Self::Tag;
    fn tagged_hash(&self) -> PtrValue;

    fn tagged_ptr(&self) -> TaggedPtr {
        TaggedPtr {
            tag: self.tag().into(),
            value: self.tagged_hash(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
pub struct TaggedPtr {
    tag: u64,
    value: PtrValue,
}

impl Default for TaggedPtr {
    fn default() -> Self {
        Self::null()
    }
}

#[allow(clippy::derive_hash_xor_eq)]
impl Hash for TaggedPtr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

impl<T: Tagged> From<&T> for TaggedPtr {
    fn from(val: &T) -> Self {
        TaggedPtr {
            tag: val.tag().into(),
            value: val.tagged_hash(),
        }
    }
}

impl TaggedPtr {
    const NULL: TaggedPtr = TaggedPtr {
        tag: 0,
        value: [0u8; 32],
    };

    /// Creates a null pointer.
    pub const fn null() -> Self {
        TaggedPtr::NULL
    }

    pub const fn from_tag(tag: u64) -> Self {
        TaggedPtr {
            tag,
            value: [0u8; 32],
        }
    }

    /// Hashes multiple self values.
    pub fn hash_many(preimage: &[Self]) -> PtrValue {
        let mut hasher = Blake3Hasher::new();
        for TaggedPtr { tag, value } in preimage {
            hasher.update(&tag.to_le_bytes());
            hasher.update(value);
        }
        *hasher.finalize().as_bytes()
    }

    /// Hash a value according the pointer hashing scheme.
    pub fn hash(value: &[u8]) -> PtrValue {
        *blake3::hash(value).as_bytes()
    }

    pub fn hash_string(s: &str) -> PtrValue {
        *blake3::hash(s.as_bytes()).as_bytes()
    }

    pub fn hash_num(n: u64) -> PtrValue {
        let mut out = [0u8; 32];
        out[..8].copy_from_slice(&n.to_le_bytes());
        out
    }

    pub const fn tag(&self) -> u64 {
        self.tag
    }

    pub(crate) fn value(&self) -> &PtrValue {
        &self.value
    }

    pub(crate) fn value_as_num(&self) -> u64 {
        u64::from_le_bytes(self.value[..8].try_into().unwrap())
    }
}

#[cfg(test)]
mod tests {
    // use super::*;

    // #[test]
    // fn test_hash_string() {
    //     assert_eq!(
    //         fr_from_u64s([
    //             0x5c03e517bec087a0,
    //             0xc22861c4b56986b2,
    //             0x730bf8397a7a2cf2,
    //             0x4bb2bffada9d35a2
    //         ]),
    //         hash_string(&"Test"),
    //     );

    //     assert_eq!(
    //         fr_from_u64s([
    //             0xaece3618ecf6d992,
    //             0xfccb6c0141aff847,
    //             0xc19882347797fbab,
    //             0x33e4e3e92bc14968
    //         ]),
    //         hash_string(&"NIL")
    //     );

    //     assert_eq!(
    //         fr_from_u64s([
    //             0xcd414517f70c8562,
    //             0x8df95fcf0e22705a,
    //             0xf14f6ff8429ddea0,
    //             0x6e952ecf9358ff3e
    //         ]),
    //         hash_string(&"RANDOM")
    //     );
    // }
}
