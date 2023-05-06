use super::*;
use pasta_curves::pallas::Scalar as Fr;

#[test]
fn trie_lang() {
    use crate::coprocessor::trie::{install, TrieCoproc};

    let s = &mut Store::<Fr>::default();
    let mut lang = Lang::<Fr, TrieCoproc<Fr>>::new();

    install(s, &mut lang);

    let expr = "(let ((trie (.lurk.trie.new)))
                      trie)";
    let res = s
        .read("0x1f9e4f688af715843a6878202c0387841d2280b7fbec9a66c7b0aaeb39703bca")
        .unwrap();

    test_aux(s, &expr, Some(res), None, None, None, 3, Some(&lang));

    // TODO: coprocessors need to evaluate their arguments for this to work.
    // let expr2 = "(let ((trie (.lurk.trie.new))
    //                    (found (.lurk.trie.lookup trie 123)))
    //                   found)";

    let expr2 = "(.lurk.trie.lookup 0x1f9e4f688af715843a6878202c0387841d2280b7fbec9a66c7b0aaeb39703bca 123)";
    let res2 = s.intern_opaque_comm(Fr::zero());

    test_aux(s, &expr2, Some(res2), None, None, None, 1, Some(&lang));

    let expr3 = "(.lurk.trie.insert 0x1f9e4f688af715843a6878202c0387841d2280b7fbec9a66c7b0aaeb39703bca 123 456)";
    let res3 = s
        .read("0x31a82c9a2e7ebfccccc0c02a2e4341c34b0b8b563aa0cb5815d3d8355e262ff9")
        .unwrap();

    test_aux(s, &expr3, Some(res3), None, None, None, 1, Some(&lang));

    let expr4 = "(.lurk.trie.lookup 0x31a82c9a2e7ebfccccc0c02a2e4341c34b0b8b563aa0cb5815d3d8355e262ff9 123)";
    let res4 = s.intern_opaque_comm(Fr::from(456));

    test_aux(s, &expr4, Some(res4), None, None, None, 1, Some(&lang));
}
