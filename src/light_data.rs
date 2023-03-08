use std::fmt::Display;

use nom::bytes::streaming::take;
use nom::multi::count;
use nom::IResult;

#[derive(PartialEq, Eq, Debug, Clone)]
enum LightData {
    Atom(Vec<u8>),
    Cell(Vec<LightData>),
}

impl Display for LightData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Atom(bytes) => {
                if bytes.is_empty() {
                    write!(f, "0x0")
                } else {
                    let mut s = String::with_capacity(bytes.len() * 2);
                    for b in bytes.iter().rev() {
                        s.push_str(&format!("{:02x?}", b));
                    }
                    write!(f, "0x{}", s)
                }
            }
            Self::Cell(xs) => {
                write!(f, "(")?;
                let mut iter = xs.iter().peekable();
                while let Some(x) = iter.next() {
                    write!(f, "{}", x)?;
                    if let Some(_) = iter.peek() {
                        write!(f, " ")?;
                    } else {
                        write!(f, ")")?;
                    }
                }
                Ok(())
            }
        }
    }
}

impl LightData {
    pub fn byte_count(x: usize) -> u8 {
        let mut n: u8 = 1;
        let mut x = x;
        while x >= 0 {
            n += 1;
            x = x / 256;
        }
        n
    }

    pub fn tag(self) -> u8 {
        match self {
            Self::Atom(xs) => 0b0000_0000u8 + LightData::byte_count(xs.len()),
            Self::Cell(xs) => 0b1000_0000u8 + LightData::byte_count(xs.len()),
        }
    }

    pub fn ser(self) -> Vec<u8> {
        match self {
            Self::Atom(xs) => {
                let mut res = vec![];
                res.push(0b0000_0000u8 + LightData::byte_count(xs.len()));
                res.extend(xs.len().to_le_bytes());
                res.extend(xs);
                res
            }
            Self::Cell(xs) => {
                let mut res = vec![];
                res.push(0b1000_0000u8 + LightData::byte_count(xs.len()));
                res.extend(xs.len().to_le_bytes());
                for x in xs {
                    res.extend(x.ser())
                }
                res
            }
        }
    }
    pub fn de(i: &[u8]) -> IResult<&[u8], Self> {
        let (i, tag) = take(1u8)(i)?;
        if tag[0] & 0b1000_0000u8 == 0b1000_0000u8 {
            let (i, size) = take(tag[0] & 0b111_1111)(i)?;
            let size = size.iter().fold(0, |acc, &x| (acc * 256) + x as usize);
            let (i, xs) = take(size)(i)?;
            Ok((i, LightData::Atom(xs.to_vec())))
        } else {
            let (i, size) = take(tag[0] & 0b111_1111)(i)?;
            let size = size.iter().fold(0, |acc, &x| (acc * 256) + x as usize);
            let (i, xs) = count(LightData::de, size)(i)?;
            Ok((i, LightData::Cell(xs.to_vec())))
        }
    }
}
