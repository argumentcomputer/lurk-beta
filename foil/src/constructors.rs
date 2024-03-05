//! Congruence Closure extended with constructors and projectors.
//! The `constructors` module is just an example of how `Foil` can be used.
//! The enum-based implementation of `Fun` is not necessary, just a somewhat simple way to
//! make a small, self-contained example.

use crate::{Func, Label, Meta, Schema};

#[derive(Clone, Copy, Eq, PartialEq, Hash)]
enum Fun {
    Car,
    Cdr,
    Cons,
    Binding,
    Add,
}

impl Fun {
    fn equivalences() -> Vec<Func<Meta>> {
        vec![Self::Binding.into()]
    }
    fn constructors() -> Vec<Func<Meta>> {
        vec![Self::Cons.into()]
    }
    fn schema() -> Schema<Meta> {
        Schema {
            equivalences: Self::equivalences(),
            constructors: Self::constructors(),
        }
    }
}

impl From<Fun> for Func<Meta> {
    fn from(fun: Fun) -> Self {
        match fun {
            Fun::Car => Self::new("Car"),
            Fun::Cdr => Self::new("Cdr"),
            Fun::Cons => Self::constructor(
                "Cons",
                vec![Fun::Car.into(), Fun::Cdr.into()],
                Meta::default(),
            ),
            Fun::Binding => Self::new("Binding"),
            Fun::Add => Self::new("Add"),
        }
    }
}

impl From<Fun> for Label {
    fn from(fun: Fun) -> Self {
        Self::from(Func::<Meta>::from(fun))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::congruence::{test::assert_expected_classes, Graph};
    use crate::{Foil, FoilConfig, Label, Meta, Var};

    /*
    * In Lurk context, we can generalize the treatment of 'Quantifier-Free Theory of Equality' with 'Extensions to Theory of List Structure'.
    *** Procedure to extend CC to deal with CAR, CDR, and CONS.
    - Start with graph of uninterpreted functions, with equivalence relation
    - For every CONS, add a unary CAR and unary CDR vertex whose target is the CONS.
    - MERGE the CAR with CONS[1] (1-indexed), and merge the CDR with CONS[2].
    *** We can generalize this for Lurk, to deal with N-ary constructors and their respective projection operators.
    **** For example, in a notional world where CONS is a binary hash (unlike Lurk's concrete use of hashes):
    - CONS = HASH2
    - CAR = HASH2-PROJECT1
    - CDR = HASH2-PROJECT2
    **** Then a 3-ary hash (i.e. a triple constructor) would yield:
    - TRIPLE = HASH3
    - HASH3-PROJECT1
    - HASH3-PROJECT2
    - HASH3-PROJECT3
    **** In each case, the same procedure is followed:
    - extend the graph to add missing projection operators
    - MERGE with the concrete projections
    *** We can also perform the complementary extension, to find congruence between the CONS(tructors) implied by projectors.
        Conder this example:

          (lambda (a)
            (let ((x (car a))
                  (y (cdr a)))
              (+ x y)))

        The proof of this expression should only require proof of a single CONS.

        This:
         A<-CAR<=X
                  \
                   +
                  /
         A<-CDR<=Y

        Becomes:
        B
         \
          CONS(1)<=A
         /          \
        C            CAR<=X
                           \
                            +
                           /
        D            CDR<=Y
         \          /
          CONS(2)<=A
         /
        E

        Then:
        - MERGE B and CAR
        - MERGE E and CDR

        But because we now have new CONSes, we need to add missing projectors. (Should this happen before or after the previous MERGEs?)

        NOTE: Actually, we don't need to add CAR(2) and CDR(2) because they are redundant. The right procedure is to check for
        the existence of CAR(1) and CDR(1). Since they exist, we should perform the next MERGE using those instead.

        B            CDR(2)
         \          /
          CONS(1)<=A
         /          \
        C            CAR(1)<=X
                              \
                               +
                              /
        D            CDR(1)<=Y
         \          /
          CONS(2)<=A
         /          \
        E            CAR(2)

        Then:
        - MERGE CDR and C
        - MERGE CAR and D

        NOTE: In this example, since we added CAR(2) and CDR(2), if we merged those just above, then we should also merge them
        with their pre-existing counterparts.
        - MERGE CAR(1) and CAR(2)
        - MERGE CDR(1) and CDR(2)

        Now we have the following partition:
        - 1: {B, CAR(1), CAR(2), D, X}
        - 2: {E, CDR(1), CDR(2), C, Y}
        - 3: {A, CONS(1), CONS(2)}
        - 4: {+}

        With this graph:

          1
         / \
        3   4
         \ /
          2

        Or equivalently:

               X:CAR
              /     \
        A:CONS       +
              \     /
               Y:CDR
        #+end_src

        */

    #[test_log::test]
    fn test_deduce_constructor() {
        // This was the original test described above.

        // (let ((x (car a))
        //       (y (cdr a)))
        //   (+ x y)))

        type G = Graph<(), Label>;
        let g = &mut G::default();

        let a = g.alloc(Var::new("a"), ());
        let x = g.alloc(Var::new("x"), ());
        let y = g.alloc(Var::new("y"), ());
        let car = g.alloc(Fun::Car, ());
        let cdr = g.alloc(Fun::Cdr, ());
        let bind_x = g.alloc(Fun::Binding, ());
        let bind_y = g.alloc(Fun::Binding, ());
        let plus = g.alloc(Fun::Add, ());

        car.connect(g, &[a]);
        cdr.connect(g, &[a]);

        // These binding nodes are not really necessary, but they may be useful for bookkeeping. Actually, for our
        // purposes, it probably makes sense to use these as the sole indicators of explicit equality.
        // These can mark the vertices to be merged, and those merges can be performed programmatically.
        // New vertices that need to be added first can add pending merges by creating these connections.
        // Binding is probably the wrong term in that context, though. TODO: Better name.
        bind_x.connect(g, &[x, car]);
        bind_y.connect(g, &[y, cdr]);

        plus.connect(g, &[x, y]);

        let cons = g.alloc(Fun::Cons, ());
        let car1 = g.alloc(Fun::Car, ());
        let cdr1 = g.alloc(Fun::Cdr, ());
        let b = g.alloc(Var::new("b"), ());
        let c = g.alloc(Var::new("c"), ());

        cons.connect(g, &[b, c]);

        car1.connect(g, &[cons]);
        cdr1.connect(g, &[cons]);

        // All merges must follow all connections.

        // This effects the equivalences the bindings signal.
        x.merge(g, &car);
        y.merge(g, &cdr);

        // This adds the Cons. We know this is needed because `a` has a predecessor that is labeled `Car` and one that is
        // labeled `Cdr`. Either would suffice to require this new vertex labeled `Cons` to be added. Such an added cons
        // must be merged with the vertex that forced its creation.
        a.merge(g, &cons);

        // When a new `Cons` is created, corresponding projection (`Car` and `Cdr`) vertices are created, and their axiomatic
        // equivalence to the `Cons`'s successors must be asserted by merging them.
        b.merge(g, &car1);
        c.merge(g, &cdr1);

        // The bindings each inhabit singleton equivalence classes and can be removed.
        let actual_classes = dbg!(g.class_info(None));
        let expected_classes = &[
            // Notice that variable a has been labeled as a cons.
            (0, vec!["Var(a): 0", "Cons: 8"], Some(vec![11, 12])),
            // Notice that now the bindings point to identical vertices. That is because their potentially distinct
            // successors have been merged, by virtue of `Binding` having been specified as an 'equivalence' in the schema.
            (5, vec!["Binding: 5"], Some(vec![11, 11])),
            (6, vec!["Binding: 6"], Some(vec![12, 12])),
            (7, vec!["Add: 7"], Some(vec![11, 12])),
            (
                11,
                vec!["Var(x): 1", "Car: 3", "Car: 9", "Var(b): 11"],
                Some(vec![0]),
            ),
            (
                12,
                vec!["Var(y): 2", "Cdr: 4", "Cdr: 10", "Var(c): 12"],
                Some(vec![0]),
            ),
        ];
        assert_expected_classes(expected_classes, &actual_classes);
    }

    #[test_log::test]
    fn test_auto_deduce_constructor() {
        // This is the original test with all the 'annotation' (i.e. the added vertices and equivalences) automated.

        // (let ((x (car a))
        //       (y (cdr a)))
        //   (+ x y)))

        let f = &mut Foil::<(), Meta>::new(Fun::schema(), FoilConfig::default());

        let a = f.alloc(Var::new("a"));
        let x = f.alloc(Var::new("x"));
        let y = f.alloc(Var::new("y"));
        let car = f.alloc(Fun::Car);
        let cdr = f.alloc(Fun::Cdr);
        let bind_x = f.alloc(Fun::Binding);
        let bind_y = f.alloc(Fun::Binding);
        let plus = f.alloc(Fun::Add);

        f.connect(&car, &[a]);
        f.connect(&cdr, &[a]);

        // These binding nodes are not really necessary, but they may be useful for bookkeeping. Actually, for our
        // purposes, it probably makes sense to use these as the sole indicators of explicit equality.
        // These can mark the vertices to be merged, and those merges can be performed programmatically.
        // New vertices that need to be added first can add pending merges by creating these connections.
        // Binding is probably the wrong term in that context, though. TODO: Better name.
        f.connect(&bind_x, &[x, car]);
        f.connect(&bind_y, &[y, cdr]);

        f.connect(&plus, &[x, y]);

        f.finalize();

        let actual_classes = dbg!(f.graph.class_info(None));

        // Notice that the final equivalence classes correspond to those predicted in the analysis (which preceded the implementation):
        /*
                Now we have the following partition:
                - 1: {B, CAR(1), CAR(2), D, X}
                - 2: {E, CDR(1), CDR(2), C, Y}
                - 3: {A, CONS(1), CONS(2)}
                - 4: {+}
        */

        let expected_classes = &[
            (
                0,
                // {A, CONS(1), CONS(2)}
                vec!["Var(a): 0", "Cons: 8", "Cons: 11"],
                Some(vec![1, 2]),
            ),
            (
                1,
                // {B, CAR(1), CAR(2), D, X}
                vec![
                    "Var(x): 1",
                    "Car: 3",
                    "Var(Car)[0]: 9",
                    "Var(Car)[2]: 12",
                    "Car: 14",
                    "Car: 16",
                ],
                Some(vec![0]),
            ),
            (
                2,
                // {E, CDR(1), CDR(2), C, Y}
                vec![
                    "Var(y): 2",
                    "Cdr: 4",
                    "Var(Cdr)[1]: 10",
                    "Var(Cdr)[3]: 13",
                    "Cdr: 15",
                    "Cdr: 17",
                ],
                Some(vec![0]),
            ),
            // These 'Binding's are syntactic and can be removed from the graph. They may have been explicit in the
            // source from which the graph was generated, but their children (the bound vars/values) are now equivalent
            // in the graph.
            (5, vec!["Binding: 5"], Some(vec![1, 1])),
            (6, vec!["Binding: 6"], Some(vec![2, 2])),
            (7, vec!["Add: 7"], Some(vec![1, 2])),
        ];

        assert_expected_classes(expected_classes, &actual_classes);
    }

    #[test_log::test]
    fn test_simplify_minimal() {
        // This is a test showing that the car of a 'cons' is understood to be the first input to the cons expression
        // that produced it.

        // (let* ((a (cons b c))
        //        (d (car a)))
        //           ...)
        let f = &mut Foil::<(), Meta>::new(Fun::schema(), FoilConfig::default());

        let a = f.alloc(Var::new("a"));
        let b = f.alloc(Var::new("b"));
        let c = f.alloc(Var::new("c"));
        let d = f.alloc(Var::new("d"));
        let cons1 = f.alloc(Fun::Cons);
        let car = f.alloc(Fun::Car);
        let bind_a = f.alloc(Fun::Binding);
        let bind_d = f.alloc(Fun::Binding);

        f.connect(&bind_a, &[a, cons1]);
        f.connect(&cons1, &[b, c]);

        f.connect(&bind_d, &[d, car]);
        f.connect(&car, &[a]);

        f.finalize();

        // We want to see that b and d are in the same equivalence class.

        let actual_classes = dbg!(f.graph.class_info(None));

        let expected_classes = &[
            (
                0,
                vec!["Var(a): 0", "Cons: 4", "Cons: 8"],
                Some(vec![3, 10]),
            ),
            (
                3,
                // Notice that variables b and d are in the same equivalence class.
                vec![
                    "Var(b): 1",
                    "Var(d): 3",
                    "Car: 5",
                    "Var(Car)[0]: 9",
                    "Car: 11",
                    "Car: 13",
                ],
                Some(vec![0]),
            ),
            (6, vec!["Binding: 6"], Some(vec![0, 0])),
            (7, vec!["Binding: 7"], Some(vec![3, 3])),
            (
                10,
                vec!["Var(c): 2", "Var(Cdr)[1]: 10", "Cdr: 12", "Cdr: 14"],
                Some(vec![0]),
            ),
        ];

        assert_expected_classes(expected_classes, &actual_classes);

        let minimized = f.minimize();
        assert!(minimized.is_minimized());
        let minimized_classes = dbg!(minimized.graph.class_info(None));

        let expected_minimized = &[
            // Notice that all equivalence classes have exactly one member,
            // and that its member corresponds to the Func it represents (if any).
            (0, vec!["Cons: 0"], Some(vec![1, 2])),
            (1, vec!["Car: 1"], Some(vec![0])),
            (2, vec!["Cdr: 2"], Some(vec![0])),
        ];

        assert_expected_classes(expected_minimized, &minimized_classes);
    }

    #[test_log::test]
    fn test_auto_simplify_harder() {
        // This is a more elaborate version of the minimal test.

        // (let* ((a (cons b c))
        //        (d (car a))
        //        (e (cdr a))
        //        (f (cons d e)))
        //   (+ a f))
        let f = &mut Foil::<(), Meta>::new(Fun::schema(), FoilConfig::default());

        let a = f.alloc(Var::new("a"));
        let b = f.alloc(Var::new("b"));
        let c = f.alloc(Var::new("c"));
        let cons1 = f.alloc(Fun::Cons);
        f.connect(&cons1, &[b, c]);
        let bind_a = f.alloc(Fun::Binding);
        f.connect(&bind_a, &[a, cons1]);

        let car = f.alloc(Fun::Car);
        f.connect(&car, &[a]);
        let d = f.alloc(Var::new("d"));
        let bind_d = f.alloc(Fun::Binding);
        f.connect(&bind_d, &[d, car]);

        let cdr = f.alloc(Fun::Cdr);
        f.connect(&cdr, &[a]);
        let e = f.alloc(Var::new("e"));
        let bind_e = f.alloc(Fun::Binding);
        f.connect(&bind_e, &[e, cdr]);

        let cons2 = f.alloc(Fun::Cons);
        f.connect(&cons2, &[d, e]);
        let bind_ff = f.alloc(Fun::Binding);
        let ff = f.alloc(Var::new("ff"));
        f.connect(&bind_ff, &[ff, cons2]);

        let plus = f.alloc(Fun::Add);
        f.connect(&plus, &[a, ff]);

        f.finalize();

        let actual_classes = dbg!(f.graph.class_info(None));

        let expected_classes = &[
            (
                6,
                vec![
                    "Var(b): 1",
                    "Car: 5",
                    "Var(d): 6",
                    "Var(Car)[0]: 16",
                    "Var(Car)[2]: 19",
                    "Car: 21",
                    "Car: 23",
                    "Car: 25",
                    "Car: 27",
                ],
                Some(vec![13]),
            ),
            (7, vec!["Binding: 7"], Some(vec![6, 6])),
            (
                9,
                vec![
                    "Var(c): 2",
                    "Cdr: 8",
                    "Var(e): 9",
                    "Var(Cdr)[1]: 17",
                    "Var(Cdr)[3]: 20",
                    "Cdr: 22",
                    "Cdr: 24",
                    "Cdr: 26",
                    "Cdr: 28",
                ],
                Some(vec![13]),
            ),
            (10, vec!["Binding: 10"], Some(vec![9, 9])),
            (12, vec!["Binding: 4", "Binding: 12"], Some(vec![13, 13])),
            (
                13,
                vec![
                    "Var(a): 0",
                    "Cons: 3",
                    "Cons: 11",
                    "Var(ff): 13",
                    "Cons: 15",
                    "Cons: 18",
                ],
                Some(vec![6, 9]),
            ),
            (14, vec!["Add: 14"], Some(vec![13, 13])),
        ];

        assert_expected_classes(expected_classes, &actual_classes);

        let minimized = f.minimize();
        assert!(minimized.is_minimized());
        let minimized_classes = dbg!(minimized.graph.class_info(None));

        let expected_minimized = &[
            (0, vec!["Car: 0"], Some(vec![2])),
            (1, vec!["Cdr: 1"], Some(vec![2])),
            (2, vec!["Cons: 2"], Some(vec![0, 1])),
            (3, vec!["Add: 3"], Some(vec![2, 2])),
        ];

        assert_expected_classes(expected_minimized, &minimized_classes);
    }

    #[test_log::test]
    fn test_var_equivalence() {
        // Allocate distinct vertices for each instance of `a`:
        //
        // TODO: But do we really *want* this behavior, or should it be possible for multiple vertices to be labeled by
        // the same var? Currently, we resolve this ambiguity by requiring 'unique' vars to be allocated when that
        // behavior is desired (for example, projectors).
        //
        // The alternate behavior might actually be more natural when variables may be shadowed and therefore share
        // names while representing unique values.
        //
        // (let ((a (cons x y))
        //       (b (car a))
        //       (c (cdr a)))
        //   (cons b c)))
        let f = &mut Foil::<(), Meta>::new(
            Fun::schema(),
            FoilConfig {
                dedup_var_names: true,
            },
        );
        let f2 = &mut Foil::<(), Meta>::new(
            Fun::schema(),
            FoilConfig {
                dedup_var_names: false,
            },
        );

        let setup = |f: &mut Foil<(), Meta>| {
            let a1 = f.alloc(Var::new("a"));
            let a2 = f.alloc(Var::new("a"));
            let a3 = f.alloc(Var::new("a"));
            let x = f.alloc(Var::new("x"));
            let y = f.alloc(Var::new("y"));
            let b = f.alloc(Var::new("b"));
            let c = f.alloc(Var::new("c"));
            let cons1 = f.alloc(Fun::Cons);
            let cons2 = f.alloc(Fun::Cons);
            let car = f.alloc(Fun::Car);
            let cdr = f.alloc(Fun::Cdr);
            let bind_a = f.alloc(Fun::Binding);
            let bind_b = f.alloc(Fun::Binding);
            let bind_c = f.alloc(Fun::Binding);

            f.connect(&cons1, &[x, y]);
            f.connect(&cons2, &[b, c]);
            f.connect(&car, &[a2]);
            f.connect(&cdr, &[a3]);
            f.connect(&bind_a, &[a1, cons1]);
            f.connect(&bind_b, &[b, car]);
            f.connect(&bind_c, &[c, cdr]);
        };

        setup(f);
        setup(f2);

        f.finalize();
        f2.finalize();

        let actual_classes = dbg!(f.graph.class_info(None));
        let f2_actual_classes = dbg!(f2.graph.class_info(None));
        let expected_classes = &[
            (
                5,
                vec![
                    "Var(x): 3",
                    "Var(b): 5",
                    "Car: 9",
                    "Var(Car)[0]: 15",
                    "Var(Car)[2]: 18",
                    "Car: 20",
                    "Car: 22",
                    "Car: 24",
                    "Car: 26",
                ],
                Some(vec![8]),
            ),
            (
                6,
                vec![
                    "Var(y): 4",
                    "Var(c): 6",
                    "Cdr: 10",
                    "Var(Cdr)[1]: 16",
                    "Var(Cdr)[3]: 19",
                    "Cdr: 21",
                    "Cdr: 23",
                    "Cdr: 25",
                    "Cdr: 27",
                ],
                Some(vec![8]),
            ),
            (
                8,
                vec![
                    "Var(a): 0",
                    "Var(a): 1",
                    "Var(a): 2",
                    "Cons: 7",
                    "Cons: 8",
                    "Cons: 14",
                    "Cons: 17",
                ],
                Some(vec![5, 6]),
            ),
            (11, vec!["Binding: 11"], Some(vec![8, 8])),
            (12, vec!["Binding: 12"], Some(vec![5, 5])),
            (13, vec!["Binding: 13"], Some(vec![6, 6])),
        ];
        assert_expected_classes(expected_classes, &actual_classes);

        let f2_expected_classes = &[
            // Notice that there are three distinct `a` variables, each of which has been deduced to be a cons.
            // Because we did not 'dedup' these (per the config), they manifest as three distinct conses.
            (0, vec!["Var(a): 0", "Cons: 7"], Some(vec![3, 4])),
            (1, vec!["Var(a): 1", "Cons: 14"], Some(vec![5, 16])),
            (2, vec!["Var(a): 2", "Cons: 17"], Some(vec![18, 6])),
            (3, vec!["Var(x): 3", "Car: 20"], Some(vec![0])),
            (4, vec!["Var(y): 4", "Cdr: 21"], Some(vec![0])),
            (
                5,
                vec!["Var(b): 5", "Car: 9", "Var(Car): 15", "Car: 22", "Car: 24"],
                Some(vec![1]),
            ),
            (
                6,
                vec!["Var(c): 6", "Cdr: 10", "Var(Cdr): 19", "Cdr: 23", "Cdr: 27"],
                Some(vec![2]),
            ),
            // Because the previous `(car a)` and `(cdr a)` were not discovered to refer to projections of the same
            // cons, The cons joining them is not identified with some existing cons and instead appears as yet another
            // unique cons in the graph.
            (8, vec!["Cons: 8"], Some(vec![5, 6])),
            (11, vec!["Binding: 11"], Some(vec![0, 0])),
            (12, vec!["Binding: 12"], Some(vec![5, 5])),
            (13, vec!["Binding: 13"], Some(vec![6, 6])),
            (16, vec!["Var(Cdr): 16", "Cdr: 25"], Some(vec![1])),
            (18, vec!["Var(Car): 18", "Car: 26"], Some(vec![2])),
        ];

        assert_expected_classes(f2_expected_classes, &f2_actual_classes);

        let minimized = f.minimize();
        let f2_minimized = f2.minimize();
        assert!(minimized.is_minimized());
        assert!(f2_minimized.is_minimized());
        let minimized_classes = dbg!(minimized.graph.class_info(None));
        let f2_minimized_classes = dbg!(f2_minimized.graph.class_info(None));

        let expected_minimized = &[
            (0, vec!["Car: 0"], Some(vec![2])),
            (1, vec!["Cdr: 1"], Some(vec![2])),
            (2, vec!["Cons: 2"], Some(vec![0, 1])),
        ];

        assert_expected_classes(expected_minimized, &minimized_classes);

        let f2_expected_minimized = &[
            (0, vec!["Cons: 0"], Some(vec![3, 4])),
            (1, vec!["Cons: 1"], Some(vec![5, 8])),
            (2, vec!["Cons: 2"], Some(vec![9, 6])),
            (3, vec!["Car: 3"], Some(vec![0])),
            (4, vec!["Cdr: 4"], Some(vec![0])),
            (5, vec!["Car: 5"], Some(vec![1])),
            (6, vec!["Cdr: 6"], Some(vec![2])),
            (7, vec!["Cons: 7"], Some(vec![5, 6])),
            (8, vec!["Cdr: 8"], Some(vec![1])),
            (9, vec!["Car: 9"], Some(vec![2])),
        ];
        assert_expected_classes(f2_expected_minimized, &f2_minimized_classes);
    }
}
