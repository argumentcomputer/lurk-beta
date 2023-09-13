use anyhow::{bail, Result};

use crate::field::LanguageField;

pub enum Backend {
    Nova,
    SnarkPackPlus,
}

impl std::fmt::Display for Backend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nova => write!(f, "Nova"),
            Self::SnarkPackPlus => write!(f, "SnarkPack+"),
        }
    }
}

impl Backend {
    pub(crate) fn default_field(&self) -> LanguageField {
        match self {
            Self::Nova => LanguageField::Pallas,
            Self::SnarkPackPlus => LanguageField::BLS12_381,
        }
    }

    fn compatible_fields(&self) -> Vec<LanguageField> {
        use LanguageField::*;
        match self {
            Self::Nova => vec![Pallas, Vesta],
            Self::SnarkPackPlus => vec![BLS12_381],
        }
    }

    pub(crate) fn validate_field(&self, field: &LanguageField) -> Result<()> {
        let compatible_fields = self.compatible_fields();
        if !compatible_fields.contains(field) {
            bail!(
                "Backend {self} is incompatible with field {field}. Compatible fields are:\n  {}",
                compatible_fields
                    .iter()
                    .map(|f| f.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
        Ok(())
    }
}
