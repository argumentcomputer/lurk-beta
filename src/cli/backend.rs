use anyhow::{bail, Result};

use crate::field::LanguageField;

pub enum Backend {
    Nova,
}

impl std::fmt::Display for Backend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nova => write!(f, "Nova"),
        }
    }
}

impl Backend {
    pub(crate) fn default_field(&self) -> LanguageField {
        match self {
            Self::Nova => LanguageField::Pallas,
        }
    }

    fn compatible_fields(&self) -> Vec<LanguageField> {
        use LanguageField::{Pallas, Vesta};
        match self {
            Self::Nova => vec![Pallas, Vesta],
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
