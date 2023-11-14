#[cfg(test)]
mod test {
    use lurk_crate::store::Store;
    use lurk_macros::{let_store, lurk};
    use pasta_curves::pallas::Scalar as Fr;

    #[test]
    fn test_let_store() {
        let_store!();
    }

    #[test]
    fn test_lurk() {
        let_store!();
        let res = lurk!((cons 1 2)).unwrap();

        let res2 = s_.read("(cons 1 2)").unwrap();

        assert_eq!(res2, res);
    }

    #[test]
    fn test_let() {
        let_store!();
        let res = lurk!((let ((a 1)) a)).unwrap();

        let res2 = s_.read("(let ((a 1)) a)").unwrap();

        assert_eq!(res2, res);
    }

    #[test]
    fn test_letrec() {
        let_store!();
        let res = lurk!((letrec ((a 1)) a)).unwrap();

        lurk!((let ((a 1)
                    (b 2)
                    (c (lambda (x) (* x x))))
               (+ a (c b))))
        .unwrap();

        let res2 = s_.read("(letrec ((a 1)) a)").unwrap();

        assert_eq!(res2, res);
    }
}
