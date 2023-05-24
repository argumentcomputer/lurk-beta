use anyhow::bail;
use ff::PrimeField;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::{BufReader, Read, Seek, SeekFrom};
use std::io::{Error, ErrorKind};
use std::path::Path;

use crate::circuit::gadgets::circom::r1cs::{Constraint, R1CS};
use byteorder::{LittleEndian, ReadBytesExt};
use itertools::Itertools;

#[derive(Serialize, Deserialize)]
pub(crate) struct CircuitJson {
    constraints: Vec<Vec<BTreeMap<String, String>>>,
    #[serde(rename = "nPubInputs")]
    num_inputs: usize,
    #[serde(rename = "nOutputs")]
    num_outputs: usize,
    #[serde(rename = "nVars")]
    num_variables: usize,
}

// R1CSFile's header
#[allow(dead_code)]
#[derive(Debug, Default)]
struct Header {
    field_size: u32,
    prime_size: Vec<u8>,
    n_wires: u32,
    n_pub_out: u32,
    n_pub_in: u32,
    n_prv_in: u32,
    n_labels: u64,
    n_constraints: u32,
}

// R1CSFile parse result
#[allow(dead_code)]
#[derive(Debug, Default)]
struct R1CSFile<Fr: PrimeField> {
    version: u32,
    header: Header,
    constraints: Vec<Constraint<Fr>>,
    wire_mapping: Vec<u64>,
}

/// load witness file by filename with autodetect encoding (bin or json).
pub(crate) fn load_witness_from_file<Fr: PrimeField>(filename: &Path) -> Vec<Fr> {
    if filename.ends_with("json") {
        load_witness_from_json_file::<Fr>(filename)
    } else {
        load_witness_from_bin_file::<Fr>(filename)
    }
}

/// load witness from bin file by filename
fn load_witness_from_bin_file<Fr: PrimeField>(filename: &Path) -> Vec<Fr> {
    let reader = OpenOptions::new()
        .read(true)
        .open(filename)
        .expect("unable to open.");
    load_witness_from_bin_reader::<Fr, BufReader<File>>(BufReader::new(reader))
        .expect("read witness failed")
}

/// load witness from u8 array by a reader
fn load_witness_from_bin_reader<Fr: PrimeField, R: Read>(
    mut reader: R,
) -> Result<Vec<Fr>, anyhow::Error> {
    let mut wtns_header = [0u8; 4];
    reader.read_exact(&mut wtns_header)?;
    if wtns_header != [119, 116, 110, 115] {
        // ruby -e 'p "wtns".bytes' => [119, 116, 110, 115]
        bail!("invalid file header");
    }
    let version = reader.read_u32::<LittleEndian>()?;
    // println!("wtns version {}", version);
    if version > 2 {
        bail!("unsupported file version");
    }
    let num_sections = reader.read_u32::<LittleEndian>()?;
    if num_sections != 2 {
        bail!("invalid num sections");
    }
    // read the first section
    let sec_type = reader.read_u32::<LittleEndian>()?;
    if sec_type != 1 {
        bail!("invalid section type");
    }
    let sec_size = reader.read_u64::<LittleEndian>()?;
    if sec_size != 4 + 32 + 4 {
        bail!("invalid section len")
    }
    let field_size = reader.read_u32::<LittleEndian>()?;
    if field_size != 32 {
        bail!("invalid field byte size");
    }
    let mut prime = vec![0u8; field_size as usize];
    reader.read_exact(&mut prime)?;
    // if prime != hex!("010000f093f5e1439170b97948e833285d588181b64550b829a031e1724e6430") {
    //     bail!("invalid curve prime {:?}", prime);
    // }
    let witness_len = reader.read_u32::<LittleEndian>()?;
    //println!("witness len {}", witness_len);
    let sec_type = reader.read_u32::<LittleEndian>()?;
    if sec_type != 2 {
        bail!("invalid section type");
    }
    let sec_size = reader.read_u64::<LittleEndian>()?;
    if sec_size != (witness_len * field_size) as u64 {
        bail!("invalid witness section size {}", sec_size);
    }
    let mut result = Vec::with_capacity(witness_len as usize);
    for _ in 0..witness_len {
        result.push(read_field::<&mut R, Fr>(&mut reader)?);
    }
    Ok(result)
}

/// load witness from json file by filename
fn load_witness_from_json_file<Fr: PrimeField>(filename: &Path) -> Vec<Fr> {
    let reader = OpenOptions::new()
        .read(true)
        .open(filename)
        .expect("unable to open.");
    load_witness_from_json::<Fr, BufReader<File>>(BufReader::new(reader))
}

/// load witness from json by a reader
fn load_witness_from_json<Fr: PrimeField, R: Read>(reader: R) -> Vec<Fr> {
    let witness: Vec<String> = serde_json::from_reader(reader).expect("unable to read.");
    witness
        .into_iter()
        .map(|x| Fr::from_str_vartime(&x).unwrap())
        .collect::<Vec<Fr>>()
}

/// load r1cs from bin file by filename
fn load_r1cs_from_bin_file<Fr: PrimeField>(filename: &Path) -> R1CS<Fr> {
    let reader = OpenOptions::new()
        .read(true)
        .open(filename)
        .expect("unable to open.");
    load_r1cs_from_bin(BufReader::new(reader))
}

fn read_field<R: Read, Fr: PrimeField>(mut reader: R) -> Result<Fr, Error> {
    let mut repr = Fr::ZERO.to_repr();
    for digit in repr.as_mut().iter_mut() {
        // TODO: may need to reverse order?
        *digit = reader.read_u8()?;
    }
    let fr = Fr::from_repr(repr).unwrap();
    Ok(fr)
}

fn read_header<R: Read>(mut reader: R, size: u64) -> Result<Header, Error> {
    let field_size = reader.read_u32::<LittleEndian>()?;
    let mut prime_size = vec![0u8; field_size as usize];
    reader.read_exact(&mut prime_size)?;
    if size != 32 + field_size as u64 {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "Invalid header section size",
        ));
    }

    Ok(Header {
        field_size,
        prime_size,
        n_wires: reader.read_u32::<LittleEndian>()?,
        n_pub_out: reader.read_u32::<LittleEndian>()?,
        n_pub_in: reader.read_u32::<LittleEndian>()?,
        n_prv_in: reader.read_u32::<LittleEndian>()?,
        n_labels: reader.read_u64::<LittleEndian>()?,
        n_constraints: reader.read_u32::<LittleEndian>()?,
    })
}

fn read_constraint_vec<R: Read, Fr: PrimeField>(
    mut reader: R,
    _header: &Header,
) -> Result<Vec<(usize, Fr)>, Error> {
    let n_vec = reader.read_u32::<LittleEndian>()? as usize;
    let mut vec = Vec::with_capacity(n_vec);
    for _ in 0..n_vec {
        vec.push((
            reader.read_u32::<LittleEndian>()? as usize,
            read_field::<&mut R, Fr>(&mut reader)?,
        ));
    }
    Ok(vec)
}

fn read_constraints<R: Read, Fr: PrimeField>(
    mut reader: R,
    _size: u64,
    header: &Header,
) -> Result<Vec<Constraint<Fr>>, Error> {
    // todo check section size
    let mut vec = Vec::with_capacity(header.n_constraints as usize);
    for _ in 0..header.n_constraints {
        vec.push((
            read_constraint_vec::<&mut R, Fr>(&mut reader, header)?,
            read_constraint_vec::<&mut R, Fr>(&mut reader, header)?,
            read_constraint_vec::<&mut R, Fr>(&mut reader, header)?,
        ));
    }
    Ok(vec)
}

fn read_map<R: Read>(mut reader: R, size: u64, header: &Header) -> Result<Vec<u64>, Error> {
    if size != header.n_wires as u64 * 8 {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "Invalid map section size",
        ));
    }
    let mut vec = Vec::with_capacity(header.n_wires as usize);
    for _ in 0..header.n_wires {
        vec.push(reader.read_u64::<LittleEndian>()?);
    }
    if vec[0] != 0 {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "Wire 0 should always be mapped to 0",
        ));
    }
    Ok(vec)
}

fn from_reader<Fr: PrimeField, R: Read + Seek>(mut reader: R) -> Result<R1CSFile<Fr>, Error> {
    let mut magic = [0u8; 4];
    reader.read_exact(&mut magic)?;
    if magic != [0x72, 0x31, 0x63, 0x73] {
        // magic = "r1cs"
        return Err(Error::new(ErrorKind::InvalidData, "Invalid magic number"));
    }

    let version = reader.read_u32::<LittleEndian>()?;
    if version != 1 {
        return Err(Error::new(ErrorKind::InvalidData, "Unsupported version"));
    }

    let num_sections = reader.read_u32::<LittleEndian>()?;

    // section type -> file offset
    let mut section_offsets = HashMap::<u32, u64>::new();
    let mut section_sizes = HashMap::<u32, u64>::new();

    // get file offset of each section
    for _ in 0..num_sections {
        let section_type = reader.read_u32::<LittleEndian>()?;
        let section_size = reader.read_u64::<LittleEndian>()?;
        let offset = reader.stream_position()?;
        section_offsets.insert(section_type, offset);
        section_sizes.insert(section_type, section_size);
        reader.seek(SeekFrom::Current(section_size as i64))?;
    }

    let header_type = 1;
    let constraint_type = 2;
    let wire2label_type = 3;

    reader.seek(SeekFrom::Start(*section_offsets.get(&header_type).unwrap()))?;
    let header = read_header(&mut reader, *section_sizes.get(&header_type).unwrap())?;
    if header.field_size != 32 {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "This parser only supports 32-byte fields",
        ));
    }
    // if header.prime_size != hex!("010000f093f5e1439170b97948e833285d588181b64550b829a031e1724e6430") {
    //     return Err(Error::new(ErrorKind::InvalidData, "This parser only supports bn256"));
    // }

    reader.seek(SeekFrom::Start(
        *section_offsets.get(&constraint_type).unwrap(),
    ))?;
    let constraints = read_constraints::<&mut R, Fr>(
        &mut reader,
        *section_sizes.get(&constraint_type).unwrap(),
        &header,
    )?;

    reader.seek(SeekFrom::Start(
        *section_offsets.get(&wire2label_type).unwrap(),
    ))?;
    let wire_mapping = read_map(
        &mut reader,
        *section_sizes.get(&wire2label_type).unwrap(),
        &header,
    )?;

    Ok(R1CSFile {
        version,
        header,
        constraints,
        wire_mapping,
    })
}

/// load r1cs from bin by a reader
fn load_r1cs_from_bin<Fr: PrimeField, R: Read + Seek>(reader: R) -> R1CS<Fr> {
    let file = from_reader(reader).expect("unable to read.");
    let num_inputs = (1 + file.header.n_pub_in + file.header.n_pub_out) as usize;
    let num_variables = file.header.n_wires as usize;
    let num_aux = num_variables - num_inputs;
    R1CS {
        num_aux,
        num_inputs,
        num_variables,
        constraints: file.constraints,
    }
}

/// load r1cs file by filename with autodetect encoding (bin or json)
pub(crate) fn load_r1cs<Fr: PrimeField>(filename: &Path) -> R1CS<Fr> {
    if filename.ends_with("json") {
        load_r1cs_from_json_file(filename)
    } else {
        load_r1cs_from_bin_file(filename)
    }
}

/// load r1cs from json file by filename
fn load_r1cs_from_json_file<Fr: PrimeField>(filename: &Path) -> R1CS<Fr> {
    let reader = OpenOptions::new()
        .read(true)
        .open(filename)
        .expect("unable to open.");
    load_r1cs_from_json(BufReader::new(reader))
}

/// load r1cs from json by a reader
fn load_r1cs_from_json<Fr: PrimeField, R: Read>(reader: R) -> R1CS<Fr> {
    let circuit_json: CircuitJson = serde_json::from_reader(reader).expect("unable to read.");

    let num_inputs = circuit_json.num_inputs + circuit_json.num_outputs + 1;
    let num_aux = circuit_json.num_variables - num_inputs;

    let convert_constraint = |lc: &BTreeMap<String, String>| {
        lc.iter()
            .map(|(index, coeff)| (index.parse().unwrap(), Fr::from_str_vartime(coeff).unwrap()))
            .collect_vec()
    };

    let constraints = circuit_json
        .constraints
        .iter()
        .map(|c| {
            (
                convert_constraint(&c[0]),
                convert_constraint(&c[1]),
                convert_constraint(&c[2]),
            )
        })
        .collect_vec();

    R1CS {
        num_inputs,
        num_aux,
        num_variables: circuit_json.num_variables,
        constraints,
    }
}
