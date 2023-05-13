use std::collections::HashMap;

use crate::field::LurkField;

pub struct Package<F: LurkField> {
    name: String, // used to compute the full path
    symbols: HashMap<Vec<String>, F>,
}

impl<F: LurkField> Package<F> {
    fn str_vec_to_string_vec(input_vec: &Vec<&str>) -> Vec<String> {
        let mut vec = vec![];
        for path in input_vec.iter() {
            vec.push(path.to_string());
        }
        vec
    }

    pub fn new(name: &str, symbols: Vec<(Vec<&str>, F)>) -> Self {
        let mut map = HashMap::default();
        for (symbol, f) in symbols.iter() {
            map.insert(Self::str_vec_to_string_vec(symbol), *f);
        }
        Package {
            name: name.to_string(),
            symbols: map,
        }
    }

    pub fn field(&self, relative_path: Vec<&str>) -> F {
        *self
            .symbols
            .get(&Self::str_vec_to_string_vec(&relative_path))
            .expect("Symbol not found")
    }
}

#[inline]
pub fn lurk_package<F: LurkField>() -> Package<F> {
    Package::new("lurk", vec![(vec!["nil"], F::from_u64(0))])
}
