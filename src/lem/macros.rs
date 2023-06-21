#[macro_export]
macro_rules! metaptr {
    ($variable:ident) => {
        $crate::lem::MetaPtr(stringify!($variable).into())
    };
}

#[macro_export]
macro_rules! metaptrs {
    ($($variable:ident),*) => {
        [
            $($crate::metaptr!($variable)),*
        ]
    };
}

#[macro_export]
macro_rules! lemop {
    ( let $tgt:ident : $tag:ident ) => {
        $crate::lem::LEMOP::Null(
            $crate::metaptr!($tgt),
            $crate::lem::Tag::$tag,
        )
    };
    ( let $tgt:ident : $tag:ident = hash2($src1:ident, $src2:ident) ) => {
        $crate::lem::LEMOP::Hash2(
            $crate::metaptr!($tgt),
            $crate::lem::Tag::$tag,
            $crate::metaptrs!($src1, $src2),
        )
    };
    ( let $tgt:ident : $tag:ident = hash3($src1:ident, $src2:ident, $src3:ident) ) => {
        $crate::lem::LEMOP::Hash3(
            $crate::metaptr!($tgt),
            $crate::lem::Tag::$tag,
            $crate::metaptrs!($src1, $src2, $src3),
        )
    };
    ( let $tgt:ident : $tag:ident = hash4($src1:ident, $src2:ident, $src3:ident, $src4:ident) ) => {
        $crate::lem::LEMOP::Hash4(
            $crate::metaptr!($tgt),
            $crate::lem::Tag::$tag,
            $crate::metaptrs!($src1, $src2, $src3, $src4),
        )
    };
    ( let ($tgt1:ident, $tgt2:ident) = unhash2($src:ident) ) => {
        $crate::lem::LEMOP::Unhash2(
            $crate::metaptrs!($tgt1, $tgt2),
            $crate::lem::MetaPtr(stringify!($src).into()),
        )
    };
    ( let ($tgt1:ident, $tgt2:ident, $tgt3:ident) = unhash3($src:ident) ) => {
        $crate::lem::LEMOP::Unhash3(
            $crate::metaptrs!($tgt1, $tgt2, $tgt3),
            $crate::metaptr!($src),
        )
    };
    ( let ($tgt1:ident, $tgt2:ident, $tgt3:ident, $tgt4:ident) = unhash4($src:ident) ) => {
        $crate::lem::LEMOP::Unhash4(
            $crate::metaptrs!($tgt1, $tgt2, $tgt3, $tgt4),
            $crate::metaptr!($src),
        )
    };
    ( let $tgt:ident = hide($sec:ident, $src:ident) ) => {
        $crate::lem::LEMOP::Hide(
           $crate::metaptr!($tgt), $crate::metaptr!($sec), $crate::metaptr!($src),
        )
    };
    ( let ($sec:ident, $src:ident) = open($hash:ident) ) => {
        $crate::lem::LEMOP::Open(
            $crate::metaptr!($sec), $crate::metaptr!($src), $crate::metaptr!($hash),
        )
    };
}

#[macro_export]
macro_rules! lem_code {
    ( match_tag $sii:ident { $( $tag:ident => $case_ops:tt ),* $(,)? } ) => {
        {
            let mut cases = std::collections::HashMap::new();
            $(
                if cases.insert(
                    $crate::lem::Tag::$tag,
                    $crate::lem_code!( $case_ops ),
                ).is_some() {
                    panic!("Repeated tag on `match_tag`");
                };
            )*
            $crate::lem::LEMCTL::MatchTag($crate::metaptr!($sii), cases)
        }
    };
    ( match_symbol $sii:ident { $( $symbol:expr => $case_ops:tt ),* , _ => $def:tt $(,)? } ) => {
        {
            let mut cases = std::collections::HashMap::new();
            $(
                if cases.insert(
                    $symbol,
                    $crate::lem_code!( $case_ops ),
                ).is_some() {
                    panic!("Repeated path on `match_symbol`");
                };
            )*
            $crate::lem::LEMCTL::MatchSymbol($crate::metaptr!($sii), cases, Box::new($crate::lem_code!( $def )))
        }
    };
    ( return ($src1:ident, $src2:ident, $src3:ident) ) => {
        $crate::lem::LEMCTL::Return(
            $crate::metaptrs!($src1, $src2, $src3)
        )
    };
    // seq entry point, with a separate bracketing to differentiate
    ({ $($body:tt)+ }) => {
        {
            $crate::lem_code! ( @seq {}, $($body)* )
        }
    };
    // handle the recursion: as we see a statement, we push it to the limbs position in the pattern
    (@seq {$($limbs:expr)*}, let $tgt:ident : $tag:ident ; $($tail:tt)*) => {
        $crate::lem_code! (
            @seq
            {
                $crate::lemop!(let $tgt: $tag)
                $($limbs)*
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident : $tag:ident = hash2($src1:ident, $src2:ident) ; $($tail:tt)*) => {
        $crate::lem_code! (
            @seq
            {
                $crate::lemop!(let $tgt: $tag = hash2($src1, $src2) )
                $($limbs)*
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident : $tag:ident = hash3($src1:ident, $src2:ident, $src3:ident) ; $($tail:tt)*) => {
        $crate::lem_code! (
            @seq
            {
                $crate::lemop!(let $tgt: $tag = hash3($src1, $src2, $src3) )
                $($limbs)*
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident : $tag:ident = hash4($src1:ident, $src2:ident, $src3:ident, $src4:ident) ; $($tail:tt)*) => {
        $crate::lem_code! (
            @seq
            {
                $crate::lemop!(let $tgt: $tag = hash4($src1, $src2, $src3, $src4))
                $($limbs)*
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let ($tgt1:ident, $tgt2:ident) = unhash2($src:ident) ; $($tail:tt)*) => {
        $crate::lem_code! (
            @seq
            {
                $crate::lemop!(let ($tgt1, $tgt2) = unhash2($src) )
                $($limbs)*
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let ($tgt1:ident, $tgt2:ident, $tgt3:ident) = unhash3($src:ident) ; $($tail:tt)*) => {
        $crate::lem_code! (
            @seq
            {
                $crate::lemop!(let ($tgt1, $tgt2, $tgt3) = unhash3($src) )
                $($limbs)*
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let ($tgt1:ident, $tgt2:ident, $tgt3:ident, $tgt4:ident) = unhash4($src:ident) ; $($tail:tt)*) => {
        $crate::lem_code! (
            @seq
            {
                $crate::lemop!(let ($tgt1, $tgt2, $tgt3, $tgt4) = unhash4($src) )
                $($limbs)*
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = hide($sec:ident, $src:ident) ; $($tail:tt)*) => {
        $crate::lem_code! (
            @seq
            {
                $crate::lemop!(let $tgt = hide($sec, $src) )
                $($limbs)*
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let ($sec:ident, $src:ident) = open($hash:ident) ; $($tail:tt)*) => {
        $crate::lem_code! (
            @seq
            {
                $crate::lemop!(let ($sec, $src) = open($hash) )
                $($limbs)*
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, match_tag $sii:ident { $( $tag:ident => $case_ops:tt ),* $(,)? } $($tail:tt)*) => {
        $crate::lem_code! (
            @end
            {
                $($limbs)*
            },
            $crate::lem_code!( match_tag $sii { $( $tag => $case_ops ),* } ),
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, match_symbol $sii:ident { $( $symbol:expr => $case_ops:tt ),* , _ => $def:tt $(,)? } $($tail:tt)*) => {
        $crate::lem_code! (
            @end
            {
                $($limbs)*
            },
            $crate::lem_code!( match_symbol $sii { $( $symbol => $case_ops ),* , _ => $def, } ),
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, return ($src1:ident, $src2:ident, $src3:ident) $($tail:tt)*) => {
        $crate::lem_code! (
            @end
            {
                $($limbs)*
            },
            $crate::lem_code!( return ($src1, $src2, $src3) ),
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, $(;)? ) => {
        {
            compile_error!("You must provide lem with a return!");
        }
    };
    (@end {$($limbs:expr)*}, $cont:expr,  $(;)?) => {
        {
            let code = $cont;
            $(
                let code = $crate::lem::LEMCTL::Seq($limbs, Box::new(code));
            )*
            code
        }
    }
}

#[macro_export]
macro_rules! lem {
    ($in1:ident $in2:ident $in3:ident $lem:tt) => {
        $crate::lem::LEM::new(
            [stringify!($in1).into(), stringify!($in2).into(), stringify!($in3).into()],
            &$crate::lem_code!($lem),
        )
    };
}

#[cfg(test)]
mod tests {
    use crate::lem::{symbol::Symbol, tag::Tag, MetaPtr, LEMCTL, LEMOP};

    #[inline]
    fn mptr(name: &str) -> MetaPtr {
        MetaPtr(name.into())
    }

    #[inline]
    fn match_tag(i: MetaPtr, cases: Vec<(Tag, LEMCTL)>) -> LEMCTL {
        LEMCTL::MatchTag(i, std::collections::HashMap::from_iter(cases))
    }

    #[inline]
    fn match_symbol(i: MetaPtr, cases: Vec<(Symbol, LEMCTL)>, def: LEMCTL) -> LEMCTL {
        LEMCTL::MatchSymbol(
            i,
            std::collections::HashMap::from_iter(cases),
            Box::new(def),
        )
    }

    #[test]
    fn test_macros() {
        let lemops = [
            LEMOP::Null(mptr("foo"), Tag::Num),
            LEMOP::Hash2(mptr("foo"), Tag::Char, [mptr("bar"), mptr("baz")]),
            LEMOP::Hash3(
                mptr("foo"),
                Tag::Char,
                [mptr("bar"), mptr("baz"), mptr("bazz")],
            ),
            LEMOP::Hash4(
                mptr("foo"),
                Tag::Char,
                [mptr("bar"), mptr("baz"), mptr("bazz"), mptr("baxx")],
            ),
            LEMOP::Unhash2([mptr("foo"), mptr("goo")], mptr("aaa")),
            LEMOP::Unhash3([mptr("foo"), mptr("goo"), mptr("moo")], mptr("aaa")),
            LEMOP::Unhash4(
                [mptr("foo"), mptr("goo"), mptr("moo"), mptr("noo")],
                mptr("aaa"),
            ),
            LEMOP::Hide(mptr("bar"), mptr("baz"), mptr("bazz")),
            LEMOP::Open(mptr("bar"), mptr("baz"), mptr("bazz")),
        ];
        let lemops_macro = [
            lemop!(let foo: Num),
            lemop!(let foo: Char = hash2(bar, baz)),
            lemop!(let foo: Char = hash3(bar, baz, bazz)),
            lemop!(let foo: Char = hash4(bar, baz, bazz, baxx)),
            lemop!(let (foo, goo) = unhash2(aaa)),
            lemop!(let (foo, goo, moo) = unhash3(aaa)),
            lemop!(let (foo, goo, moo, noo) = unhash4(aaa)),
            lemop!(let bar = hide(baz, bazz)),
            lemop!(let (bar, baz) = open(bazz)),
        ];

        for i in 0..9 {
            assert!(lemops[i] == lemops_macro[i]);
        }

        let ret = LEMCTL::Return([mptr("bar"), mptr("baz"), mptr("bazz")]);
        let code = lemops.into_iter().rev().fold(ret,|acc, op| {
            LEMCTL::Seq(op, Box::new(acc))
        });
        let lem_macro_seq = lem_code!({
            let foo: Num;
            let foo: Char = hash2(bar, baz);
            let foo: Char = hash3(bar, baz, bazz);
            let foo: Char = hash4(bar, baz, bazz, baxx);
            let (foo, goo) = unhash2(aaa);
            let (foo, goo, moo) = unhash3(aaa);
            let (foo, goo, moo, noo) = unhash4(aaa);
            let bar = hide(baz, bazz);
            let (bar, baz) = open(bazz);
            return (bar, baz, bazz);
        });

        assert!(code == lem_macro_seq);

        // TODO: Fix these tests
        // let foo = lem!(
        //     match_tag www {
        //         Num => {
        //             let foo: Num; // a single LEMOP will not turn into a Seq
        //             return (foo, foo, foo);
        //         },
        //         Str => {
        //             let foo: Num;
        //             let goo: Char;
        //             return (foo, foo, goo);
        //         },
        //         Char => {
        //             let foo: Num;
        //             let goo: Char;
        //             return (foo, goo, goo);
        //         }
        //     }
        // );
        // assert!(
        //     foo == match_tag(
        //         mptr("www"),
        //         vec![
        //             (Tag::Num, LEM::Null(mptr("foo"), Tag::Num)),
        //             (
        //                 Tag::Str,
        //                 LEM::Seq(vec![
        //                     LEM::Null(mptr("foo"), Tag::Num),
        //                     LEM::Null(mptr("goo"), Tag::Char)
        //                 ])
        //             ),
        //             (
        //                 Tag::Char,
        //                 LEM::Seq(vec![
        //                     LEM::Null(mptr("foo"), Tag::Num),
        //                     LEM::Null(mptr("goo"), Tag::Char)
        //                 ])
        //             )
        //         ]
        //     )
        // );

        // let moo = lem!(
        //     match_symbol www {
        //         Symbol::lurk_sym("nil") => {
        //             let foo: Num; // a single LEMOP will not turn into a Seq
        //             return (foo, foo, foo);
        //         },
        //         Symbol::lurk_sym("cons") => {
        //             let foo: Num;
        //             let goo: Char;
        //             return (foo, foo, goo);
        //         },
        //         _ => {
        //             let xoo: Str;
        //             return (xoo, xoo, xoo);
        //         },
        //     }
        // );
        // assert!(
        //     moo == match_symbol(
        //         mptr("www"),
        //         vec![
        //             (Symbol::lurk_sym("nil"), LEMOP::Null(mptr("foo"), Tag::Num)),
        //             (
        //                 Symbol::lurk_sym("cons"),
        //                 LEMOP::Seq(vec![
        //                     LEMOP::Null(mptr("foo"), Tag::Num),
        //                     LEMOP::Null(mptr("goo"), Tag::Char)
        //                 ])
        //             ),
        //         ],
        //         LEMOP::Null(mptr("xoo"), Tag::Str)
        //     )
        // );
    }
}
