use anyhow::Result;
use lurk::{
  field::LanguageField,
  proof::nova,
  repl::repl,
};

fn main() -> Result<()> {
  pretty_env_logger::init();

  // If an argument is passed, treat is as a Lurk file to run.
  let mut args = std::env::args();
  let lurk_file = if args.len() > 1 {
    Some(args.nth(1).expect("Lurk file missing"))
  }
  else {
    None
  };

  let default_field = LanguageField::Pallas;
  let field = if let Ok(lurk_field) = std::env::var("LURK_FIELD") {
    match lurk_field.as_str() {
      "BLS12-381" => LanguageField::BLS12_381,
      "PALLAS" => LanguageField::Pallas,
      "VESTA" => LanguageField::Vesta,
      _ => default_field,
    }
  }
  else {
    default_field
  };

  match field {
    LanguageField::BLS12_381 => repl::<_, blstrs::Scalar>(lurk_file.as_deref()),
    LanguageField::Pallas => repl::<_, nova::S1>(lurk_file.as_deref()),
    LanguageField::Vesta => repl::<_, nova::S2>(lurk_file.as_deref()),
  }
}
