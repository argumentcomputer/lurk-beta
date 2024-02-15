use anyhow::{bail, Result};
use clap::ValueEnum;
use serde::Deserialize;

use crate::field::LanguageField;

#[derive(Clone, Default, Debug, Deserialize, ValueEnum, PartialEq, Eq)]
#[clap(rename_all = "lowercase")]
pub(crate) enum Backend {
    Nova,
    #[default]
    SuperNova,
}

impl std::fmt::Display for Backend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nova => write!(f, "nova"),
            Self::SuperNova => write!(f, "supernova"),
        }
    }
}

impl Backend {
    fn compatible_fields(&self) -> Vec<LanguageField> {
        use LanguageField::{Pallas, BN256};
        match self {
            Self::Nova | Self::SuperNova => vec![BN256, Pallas],
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
