#[cfg(test)]
pub mod tests {
    use std::fs;
    use blstrs::Scalar as Fr;

    use lurk::{light_data::{LightData, LightStore, Encodable}};

    #[test]
    // The following store was created with the following Lean code:
    //  def foo : IO Unit := do
    //    let store : Lurk.Store := .ofList [
    //      (⟨.nil,  .ofNat 0⟩, some $ .nil),
    //      (⟨.cons, .ofNat 1⟩, some $ .cons ⟨.nil, .ofNat 0⟩ ⟨.nil, .ofNat 1⟩),
    //      (⟨.sym,  .ofNat 2⟩, some $ .symNil),
    //      (⟨.str,  .ofNat 3⟩, some $ .strNil),
    //      (⟨.num,  .ofNat 4⟩, some $ .num (.ofNat 42)),
    //      (⟨.char, .ofNat 5⟩, some $ .char (.ofNat 37)),
    //      (⟨.comm, .ofNat 6⟩, some $ .comm (.ofNat 37) ⟨.sym, .ofNat 2⟩)
    //    ] _
    //    let ld : LightData := store
    //    IO.FS.writeBinFile ⟨"foo.store"⟩ ld.toByteArray
    fn test_light_store_deserialization () {
        let bytes = fs::read("foo.store").unwrap();
        let ld = LightData::de(&bytes).unwrap();
        let _store: LightStore<Fr> = Encodable::de(&ld).unwrap();
    }
}
