use blstrs::Scalar as Fr;
use std::{fs, path::Path};

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
fn test_light_store_deserialization() {
    let path_names = [
        "tests/exprs/Nil.expr", "tests/exprs/StrNil.expr", "tests/exprs/SymNil.expr",
        "tests/exprs/CharA", "tests/exprs/Num42", "tests/exprs/Comm0Nil",
        "tests/exprs/SymConsNilNil", "tests/exprs/StrConsNilNil", "tests/exprs/ConsNilNil"
    ];
    for path_name in path_names {
        let bytes = fs::read(Path::new(path_name)).unwrap();
        let ld = LightData::de(&bytes).unwrap();
        eprintln!("{:?}", ld);
        let _expr: LightExpr<Fr> = Encodable::de(&ld).unwrap();
    }
}
