use blstrs::Scalar as Fr;
use std::fs;

use lurk::light_data::{Encodable, LightData, LightExpr};

#[test]
// The following expressions were created with the following Lean code:
// def foo : IO Unit := do
//   let list : List (String × ScalarExpr) := [
//     ("Nil", .nil), ("SymNil", .symNil), ("StrNil", .strNil),
//     ("CharA", .char (.ofNat 'A'.toNat)),
//     ("Num42", .num (.ofNat 42)),
//     ("Comm0Nil", .comm (.ofNat 0) ⟨.nil, .ofNat 0⟩),
//     ("SymConsNilNil", .symCons ⟨.nil, .ofNat 0⟩ ⟨.nil, .ofNat 0⟩),
//     ("StrConsNilNil", .strCons ⟨.nil, .ofNat 0⟩ ⟨.nil, .ofNat 0⟩),
//     ("ConsNilNil", .cons ⟨.nil, .ofNat 0⟩ ⟨.nil, .ofNat 0⟩)
//   ]
//   let exprsDir := ⟨"exprs"⟩
//   IO.FS.createDir exprsDir
//   for (name, expr) in list do
//     let path := exprsDir / name |>.withExtension "expr"
//     let ld : LightData := expr
//     IO.FS.writeBinFile path ld.toByteArray
fn test_light_exprs_deserialization() {
    let directory = "tests/exprs";

    for entry in fs::read_dir(directory).expect("Failed to read directory") {
        if let Ok(entry) = entry {
            let path = entry.path();
            if let Some(extension) = path.extension() {
                if extension == "expr" {
                    let file_path = path.to_str().unwrap();
                    let file_bytes = fs::read(file_path).expect("Failed to read file");
                    let ld = LightData::de(&file_bytes).unwrap();
                    let _expr: LightExpr<Fr> = Encodable::de(&ld).unwrap();
                }
            }
        }
    }
}
