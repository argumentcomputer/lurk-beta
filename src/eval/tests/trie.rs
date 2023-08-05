use super::*;
use pasta_curves::pallas::Scalar as Fr;

#[test]
fn trie_lang() {
    use crate::coprocessor::trie::{install, TrieCoproc};

    let s = &mut Store::<Fr>::default();
    let mut lang = Lang::<Fr, TrieCoproc<Fr>>::new();

    install(s, &mut lang);

    let expr = "(let ((trie (trie-new)))
                      trie)";
    let res = s
        .read("0x1cc5b90039db85fd519af975afa1de9d2b92960a585a546637b653b115bc3b53")
        .unwrap();

    test_aux(s, expr, Some(res), None, None, None, 3, Some(&lang));

    // TODO: Coprocessors need to evaluate their arguments for this to work.
    //       See https://github.com/lurk-lab/lurk-rs/issues/398.
    // let expr2 = "(let ((trie (.lurk.trie.new))
    //                    (found (.lurk.trie.lookup trie 123)))
    //                   found)";

    let expr2 =
        "(trie-lookup 0x1cc5b90039db85fd519af975afa1de9d2b92960a585a546637b653b115bc3b53 123)";
    let res2 = s.intern_opaque_comm(Fr::zero());

    test_aux(s, expr2, Some(res2), None, None, None, 1, Some(&lang));

    let expr3 =
        "(trie-insert 0x1cc5b90039db85fd519af975afa1de9d2b92960a585a546637b653b115bc3b53 123 456)";
    let res3 = s
        .read("0x1b22dc5a394231c34e4529af674dc56a736fbd07508acfd1d12c0e67c8b4de27")
        .unwrap();

    test_aux(s, expr3, Some(res3), None, None, None, 1, Some(&lang));

    let expr4 =
        "(trie-lookup 0x1b22dc5a394231c34e4529af674dc56a736fbd07508acfd1d12c0e67c8b4de27 123)";
    let res4 = s.intern_opaque_comm(Fr::from(456));

    test_aux(s, expr4, Some(res4), None, None, None, 1, Some(&lang));
}
