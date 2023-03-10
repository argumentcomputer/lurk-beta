use blstrs::Scalar as Fr;
use std::{fs, path::Path};

use lurk::light_data::{Encodable, LightData, LightStore};

#[test]
// The following store was created with the following Lean code:
//  def foo : IO Unit := do
//    let ldonNil := LDON.nil
//    let ldonNum1 := LDON.num (.ofNat 0)
//    let ldonNum2 := LDON.num (.ofNat 256)
//    let ldonNum3 := LDON.num (.ofNat (2 * UInt64.size))
//    let ldonStr := LDON.str "hello, how are you?"
//    let ldonCons1 := LDON.cons ldonNil ldonNil
//    let ldonCons2 := LDON.cons ldonNum1 (LDON.cons ldonNil ldonStr)
//    let ldonCons3 := LDON.cons ldonNum1 (LDON.cons ldonNil ldonNum2)
//    let ldonCons4 := LDON.cons ldonCons3 ldonCons3
//    let ldons := [ldonNil, ldonNum1, ldonNum2, ldonNum3, ldonStr,
//      ldonCons1, ldonCons2, ldonCons3, ldonCons4]
//    let stt := ldons.foldl (init := default) fun acc ldon =>
//      let (_, acc) := ldon.commit acc; acc
//    let ld : LightData := stt.exprs
//    IO.FS.writeBinFile ⟨"foo.store"⟩ ld.toByteArray
fn test_light_store_deserialization() {
    let bytes = fs::read(Path::new("tests/foo.store")).unwrap();
    let ld = LightData::de(&bytes).unwrap();
    
    let _store: LightStore<Fr> = Encodable::de(&ld).unwrap();
}
