use super::*;
use pasta_curves::pallas::Scalar as Fr;

#[test]
fn trie_lang() {
    use crate::coprocessor::trie::{install, TrieCoproc};

    let s = &mut Store::<Fr>::default();
    let mut lang = Lang::<Fr, TrieCoproc<Fr>>::new();

    install(s, &mut lang);

    // TODO wrap .lurk.trie.new, .lurk.trie.lookup and .lurk.trie.insert in lambdas
    let expr = "(let ((trie .lurk.trie.new))
                      trie)";
    let res = s
        .read("0x1cc5b90039db85fd519af975afa1de9d2b92960a585a546637b653b115bc3b53")
        .unwrap();

    test_aux(s, &expr, Some(res), None, None, None, 3, Some(&lang));

    let expr2 = "((lambda (_x _y) .lurk.trie.lookup) .lurk.trie.new 123)";
    let res2 = s.intern_opaque_comm(Fr::zero());

    test_aux(s, &expr2, Some(res2), None, None, None, 9, Some(&lang));

    let expr3 = "((lambda (_x _y _z) .lurk.trie.insert) .lurk.trie.new 123 456)";
    let res3 = s
        .read("0x1b22dc5a394231c34e4529af674dc56a736fbd07508acfd1d12c0e67c8b4de27")
        .unwrap();

    test_aux(s, &expr3, Some(res3), None, None, None, 14, Some(&lang));

    let expr4 = "((lambda (_x _y) .lurk.trie.lookup) ((lambda (_x _y _z) .lurk.trie.insert) .lurk.trie.new 123 456) 123)";
    let res4 = s.intern_opaque_comm(Fr::from(456));

    test_aux(s, &expr4, Some(res4), None, None, None, 23, Some(&lang));
}
