#[macro_export]
macro_rules! metaptr {
    ($variable:ident) => {
        $crate::lem::MetaPtr(stringify!($variable).to_string())
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
    ( let ($tgt1:ident, $tgt2:ident) = unhash2($src:ident : $tag:ident) ) => {
        $crate::lem::LEMOP::Unhash2(
            $crate::metaptrs!($tgt1, $tgt2),
            $crate::lem::MetaPtr(stringify!($src).to_string()),
            $crate::lem::Tag::$tag,
        )
    };
    ( let ($tgt1:ident, $tgt2:ident, $tgt3:ident) = unhash3($src:ident : $tag:ident) ) => {
        $crate::lem::LEMOP::Unhash3(
            $crate::metaptrs!($tgt1, $tgt2, $tgt3),
            $crate::metaptr!($src),
            $crate::lem::Tag::$tag,
        )
    };
    ( let ($tgt1:ident, $tgt2:ident, $tgt3:ident, $tgt4:ident) = unhash4($src:ident : $tag:ident) ) => {
        $crate::lem::LEMOP::Unhash4(
            $crate::metaptrs!($tgt1, $tgt2, $tgt3, $tgt4),
            $crate::metaptr!($src),
            $crate::lem::Tag::$tag,
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
    ( match_tag $sii:ident { $( $case:ident => $case_ops:tt ),* $(,)? } ) => {
        {
            let mut cases = std::collections::HashMap::new();
            $(
                if cases.insert(
                    $crate::lem::Tag::$case,
                    $crate::lemop!( $case_ops ),
                ).is_some() {
                    panic!("Repeated tag on `match_tag`");
                };
            )*
            $crate::lem::LEMOP::MatchTag($crate::metaptr!($sii), cases)
        }
    };
    ( return ($src1:ident, $src2:ident, $src3:ident) ) => {
        $crate::lem::LEMOP::Return(
            $crate::metaptrs!($src1, $src2, $src3)
        )
    };
    // seq entry point, with a separate bracketing to differentiate
    ({ $($body:tt)+ }) => {
        {
            $crate::lemop! ( @seq {}, $($body)* )
        }
    };
    // termination rule: we run out of input modulo trailing semicolumn, so we construct the Seq
    // Note the bracketed limbs pattern, which disambiguates wrt the last argument
    (@seq {$($limbs:tt)*}, $(;)? ) => {
        {
            let temp_vec = vec!($( $limbs )*);
            match &temp_vec[..] {
                [x] => x.clone(),
                _ => $crate::lem::LEMOP::Seq(temp_vec)
            }
        }
    };
    // handle the recursion: as we see a statement, we push it to the limbs position in the pattern
    (@seq {$($limbs:tt)*}, let $tgt:ident : $tag:ident ; $($tail:tt)*) => {
        $crate::lemop! (
            @seq
            {
                $($limbs)*
                $crate::lemop!(let $tgt: $tag),
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:tt)*}, let $tgt:ident : $tag:ident = hash2($src1:ident, $src2:ident) ; $($tail:tt)*) => {
        $crate::lemop! (
            @seq
            {
                $($limbs)*
                $crate::lemop!(let $tgt: $tag = hash2($src1, $src2) ),
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:tt)*}, let $tgt:ident : $tag:ident = hash3($src1:ident, $src2:ident, $src3:ident) ; $($tail:tt)*) => {
        $crate::lemop! (
            @seq
            {
                $($limbs)*
                $crate::lemop!(let $tgt: $tag = hash3($src1, $src2, $src3) ),
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:tt)*}, let $tgt:ident : $tag:ident = hash4($src1:ident, $src2:ident, $src3:ident, $src4:ident) ; $($tail:tt)*) => {
        $crate::lemop! (
            @seq
            {
                $($limbs)*
                $crate::lemop!(let $tgt: $tag = hash4($src1, $src2, $src3, $src4)),
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:tt)*}, let ($tgt1:ident, $tgt2:ident) = unhash2($src:ident : $tag:ident) ; $($tail:tt)*) => {
        $crate::lemop! (
            @seq
            {
                $($limbs)*
                $crate::lemop!(let ($tgt1, $tgt2) = unhash2($src: $tag) ),
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:tt)*}, let ($tgt1:ident, $tgt2:ident, $tgt3:ident) = unhash3($src:ident : $tag:ident) ; $($tail:tt)*) => {
        $crate::lemop! (
            @seq
            {
                $($limbs)*
                $crate::lemop!(let ($tgt1, $tgt2, $tgt3) = unhash3($src: $tag) ),
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:tt)*}, let ($tgt1:ident, $tgt2:ident, $tgt3:ident, $tgt4:ident) = unhash4($src:ident : $tag:ident) ; $($tail:tt)*) => {
        $crate::lemop! (
            @seq
            {
                $($limbs)*
                $crate::lemop!(let ($tgt1, $tgt2, $tgt3, $tgt4) = unhash4($src: $tag) ),
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:tt)*}, let $tgt:ident = hide($sec:ident, $src:ident) ; $($tail:tt)*) => {
        $crate::lemop! (
            @seq
            {
                $($limbs)*
                $crate::lemop!(let $tgt = hide($sec, $src) ),
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:tt)*}, let ($sec:ident, $src:ident) = open($hash:ident) ; $($tail:tt)*) => {
        $crate::lemop! (
            @seq
            {
                $($limbs)*
                $crate::lemop!(let ($sec, $src) = open($hash) ),
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:tt)*}, match_tag $sii:ident { $( $case:ident => $case_ops:tt ),* $(,)? } ; $($tail:tt)*) => {
        $crate::lemop! (
            @seq
            {
                $($limbs)*
                $crate::lemop!( match_tag $sii { $( $case => $case_ops ),* } ),
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:tt)*}, return ($src1:ident, $src2:ident, $src3:ident) ; $($tail:tt)*) => {
        $crate::lemop! (
            @seq
            {
                $($limbs)*
                $crate::lemop!( return ($src1, $src2, $src3) ),
            },
            $($tail)*
        )
    };
}

#[macro_export]
macro_rules! lem {
    ($in1:ident $in2:ident $in3:ident $lemop:tt) => {
        $crate::lem::LEM::new(
            [stringify!($in1), stringify!($in2), stringify!($in3)],
            &$crate::lemop!($lemop),
        )
    };
}

#[cfg(test)]
mod tests {
    use crate::lem::{tag::Tag, MetaPtr, LEMOP};

    #[inline]
    fn mptr(name: &str) -> MetaPtr {
        MetaPtr(name.to_string())
    }

    #[inline]
    fn match_tag(i: MetaPtr, cases: Vec<(Tag, LEMOP)>) -> LEMOP {
        LEMOP::MatchTag(i, std::collections::HashMap::from_iter(cases))
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
            LEMOP::Unhash2([mptr("foo"), mptr("goo")], mptr("aaa"), Tag::Num),
            LEMOP::Unhash3(
                [mptr("foo"), mptr("goo"), mptr("moo")],
                mptr("aaa"),
                Tag::Num,
            ),
            LEMOP::Unhash4(
                [mptr("foo"), mptr("goo"), mptr("moo"), mptr("noo")],
                mptr("aaa"),
                Tag::Num,
            ),
            LEMOP::Hide(mptr("bar"), mptr("baz"), mptr("bazz")),
            LEMOP::Open(mptr("bar"), mptr("baz"), mptr("bazz")),
            LEMOP::Return([mptr("bar"), mptr("baz"), mptr("bazz")]),
        ];
        let lemops_macro = [
            lemop!(let foo: Num),
            lemop!(let foo: Char = hash2(bar, baz)),
            lemop!(let foo: Char = hash3(bar, baz, bazz)),
            lemop!(let foo: Char = hash4(bar, baz, bazz, baxx)),
            lemop!(let (foo, goo) = unhash2(aaa: Num)),
            lemop!(let (foo, goo, moo) = unhash3(aaa: Num)),
            lemop!(let (foo, goo, moo, noo) = unhash4(aaa: Num)),
            lemop!(let bar = hide(baz, bazz)),
            lemop!(let (bar, baz) = open(bazz)),
            lemop!(return (bar, baz, bazz)),
        ];

        for i in 0..10 {
            assert!(lemops[i] == lemops_macro[i]);
        }

        let lemop_macro_seq = lemop!({
            let foo: Num;
            let foo: Char = hash2(bar, baz);
            let foo: Char = hash3(bar, baz, bazz);
            let foo: Char = hash4(bar, baz, bazz, baxx);
            let (foo, goo) = unhash2(aaa: Num);
            let (foo, goo, moo) = unhash3(aaa: Num);
            let (foo, goo, moo, noo) = unhash4(aaa: Num);
            let bar = hide(baz, bazz);
            let (bar, baz) = open(bazz);
            return (bar, baz, bazz);
        });

        assert!(LEMOP::Seq(lemops.to_vec()) == lemop_macro_seq);

        let foo = lemop!(
            match_tag www {
                Num => {
                    let foo: Num; // a single LEMOP will not turn into a Seq
                },
                Str => {
                    let foo: Num;
                    let goo: Char;
                },
                Char => {
                    let foo: Num;
                    let goo: Char;
                }
            }
        );
        assert!(
            foo == match_tag(
                mptr("www"),
                vec![
                    (Tag::Num, LEMOP::Null(mptr("foo"), Tag::Num)),
                    (
                        Tag::Str,
                        LEMOP::Seq(vec![
                            LEMOP::Null(mptr("foo"), Tag::Num),
                            LEMOP::Null(mptr("goo"), Tag::Char)
                        ])
                    ),
                    (
                        Tag::Char,
                        LEMOP::Seq(vec![
                            LEMOP::Null(mptr("foo"), Tag::Num),
                            LEMOP::Null(mptr("goo"), Tag::Char)
                        ])
                    )
                ]
            )
        );
    }
}
