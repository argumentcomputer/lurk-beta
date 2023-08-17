#[macro_export]
macro_rules! var {
    ($variable:ident) => {
        $crate::lem::Var(stringify!($variable).into())
    };
}

#[macro_export]
macro_rules! vars {
    ($($variable:ident),*) => {
        [
            $($crate::var!($variable)),*
        ]
    };
}

#[macro_export]
macro_rules! lit {
    ( Num($lit:literal) ) => {
        $crate::lem::Lit::Num($lit)
    };
    ( String($lit:literal) ) => {
        $crate::lem::Lit::String($lit.into())
    };
    ( Symbol($lit:literal) ) => {
        $crate::lem::Lit::Symbol($crate::state::lurk_sym(&$lit))
    };
}

#[macro_export]
macro_rules! tag {
    ( Expr::$tag:ident ) => {
        $crate::lem::Tag::Expr($crate::tag::ExprTag::$tag)
    };
    ( Cont::$tag:ident ) => {
        $crate::lem::Tag::Cont($crate::tag::ContTag::$tag)
    };
    ( Ctrl::$tag:ident ) => {
        $crate::lem::Tag::Ctrl($crate::lem::CtrlTag::$tag)
    };
}

#[macro_export]
macro_rules! op {
    ( let $tgt:ident : $kind:ident::$tag:ident ) => {
        $crate::lem::Op::Null($crate::var!($tgt), $crate::tag!($kind::$tag))
    };
    ( let $tgt:ident = $constr:ident($str:literal) ) => {
        $crate::lem::Op::Lit(
            $crate::var!($tgt),
            $crate::lit!($constr($str))
        )
    };
    ( let $tgt:ident = cast($src:ident, $kind:ident::$tag:ident) ) => {
        $crate::lem::Op::Cast(
            $crate::var!($tgt),
            $crate::tag!($kind::$tag),
            $crate::var!($src),
        )
    };
    ( let $tgt:ident = eq_tag($a:ident, $b:ident) ) => {
        $crate::lem::Op::EqTag(
            $crate::var!($tgt),
            $crate::var!($a),
            $crate::var!($b),
        )
    };
    ( let $tgt:ident = eq_val($a:ident, $b:ident) ) => {
        $crate::lem::Op::EqVal(
            $crate::var!($tgt),
            $crate::var!($a),
            $crate::var!($b),
        )
    };
    ( let $tgt:ident = add($a:ident, $b:ident) ) => {
        $crate::lem::Op::Add(
            $crate::var!($tgt),
            $crate::var!($a),
            $crate::var!($b),
        )
    };
    ( let $tgt:ident = sub($a:ident, $b:ident) ) => {
        $crate::lem::Op::Sub(
            $crate::var!($tgt),
            $crate::var!($a),
            $crate::var!($b),
        )
    };
    ( let $tgt:ident = mul($a:ident, $b:ident) ) => {
        $crate::lem::Op::Mul(
            $crate::var!($tgt),
            $crate::var!($a),
            $crate::var!($b),
        )
    };
    ( let $tgt:ident = div($a:ident, $b:ident) ) => {
        $crate::lem::Op::Div(
            $crate::var!($tgt),
            $crate::var!($a),
            $crate::var!($b),
        )
    };
    ( let $tgt:ident = lt($a:ident, $b:ident) ) => {
        $crate::lem::Op::Lt(
            $crate::var!($tgt),
            $crate::var!($a),
            $crate::var!($b),
        )
    };
    ( let $tgt:ident = bitwise_and($a:ident, $b:literal) ) => {
        $crate::lem::Op::BitAnd(
            $crate::var!($tgt),
            $crate::var!($a),
            $b,
        )
    };
    ( let ($tgt1:ident, $tgt2:ident) = div_rem64($a:ident, $b:ident) ) => {
        $crate::lem::Op::DivRem64(
            $crate::vars!($tgt1, $tgt2),
            $crate::var!($a),
            $crate::var!($b),
        )
    };
    ( emit($v:ident) ) => {
        $crate::lem::Op::Emit($crate::var!($v))
    };
    ( let $tgt:ident : $kind:ident::$tag:ident = hash2($src1:ident, $src2:ident) ) => {
        $crate::lem::Op::Hash2(
            $crate::var!($tgt),
            $crate::tag!($kind::$tag),
            $crate::vars!($src1, $src2),
        )
    };
    ( let $tgt:ident : $kind:ident::$tag:ident = hash3($src1:ident, $src2:ident, $src3:ident) ) => {
        $crate::lem::Op::Hash3(
            $crate::var!($tgt),
            $crate::tag!($kind::$tag),
            $crate::vars!($src1, $src2, $src3),
        )
    };
    ( let $tgt:ident : $kind:ident::$tag:ident = hash4($src1:ident, $src2:ident, $src3:ident, $src4:ident) ) => {
        $crate::lem::Op::Hash4(
            $crate::var!($tgt),
            $crate::tag!($kind::$tag),
            $crate::vars!($src1, $src2, $src3, $src4),
        )
    };
    ( let ($tgt1:ident, $tgt2:ident) = unhash2($src:ident) ) => {
        $crate::lem::Op::Unhash2(
            $crate::vars!($tgt1, $tgt2),
            $crate::var!($src),
        )
    };
    ( let ($tgt1:ident, $tgt2:ident, $tgt3:ident) = unhash3($src:ident) ) => {
        $crate::lem::Op::Unhash3($crate::vars!($tgt1, $tgt2, $tgt3), $crate::var!($src))
    };
    ( let ($tgt1:ident, $tgt2:ident, $tgt3:ident, $tgt4:ident) = unhash4($src:ident) ) => {
        $crate::lem::Op::Unhash4(
            $crate::vars!($tgt1, $tgt2, $tgt3, $tgt4),
            $crate::var!($src),
        )
    };
    ( let $tgt:ident = hide($sec:ident, $src:ident) ) => {
        $crate::lem::Op::Hide($crate::var!($tgt), $crate::var!($sec), $crate::var!($src))
    };
    ( let ($sec:ident, $src:ident) = open($hash:ident) ) => {
        $crate::lem::Op::Open($crate::var!($sec), $crate::var!($src), $crate::var!($hash))
    };
    ( let ($($tgt:ident),*) = $func:ident($($arg:ident),*) ) => {
        {
            let out = vec!($($crate::var!($tgt)),*);
            let inp = vec!($($crate::var!($arg)),*);
            let func = Box::new($func.clone());
            $crate::lem::Op::Call(out, func, inp)
        }
    }
}

#[macro_export]
macro_rules! ctrl {
    ( match $sii:ident.tag { $( $kind:ident::$tag:ident $(| $other_kind:ident::$other_tag:ident)* => $case_ops:tt )* } $(; $($def:tt)*)? ) => {
        {
            let mut cases = indexmap::IndexMap::new();
            $(
                if cases.insert(
                    $crate::tag!($kind::$tag),
                    $crate::block!( $case_ops ),
                ).is_some() {
                    panic!("Repeated tag on `match`");
                };
                $(
                    if cases.insert(
                        $crate::tag!($other_kind::$other_tag),
                        $crate::block!( $case_ops ),
                    ).is_some() {
                        panic!("Repeated tag on `match`");
                    };
                )*
            )*
            let default = None $( .or (Some(Box::new($crate::block!( @seq {} , $($def)* )))) )?;
            $crate::lem::Ctrl::MatchTag($crate::var!($sii), cases, default)
        }
    };
    ( match $sii:ident.val { $( $cnstr:ident($val:literal) $(| $other_cnstr:ident($other_val:literal))* => $case_ops:tt )* } $(; $($def:tt)*)? ) => {
        {
            let mut cases = indexmap::IndexMap::new();
            $(
                if cases.insert(
                    $crate::lit!($cnstr($val)),
                    $crate::block!( $case_ops ),
                ).is_some() {
                    panic!("Repeated value on `match`");
                };
                $(
                    if cases.insert(
                        $crate::lit!($other_cnstr($other_val)),
                        $crate::block!( $case_ops ),
                    ).is_some() {
                        panic!("Repeated value on `match`");
                    };
                )*
            )*
            let default = None $( .or (Some(Box::new($crate::block!( @seq {}, $($def)* )))) )?;
            $crate::lem::Ctrl::MatchVal($crate::var!($sii), cases, default)
        }
    };
    ( if $x:ident == $y:ident { $($true_block:tt)+ } $($false_block:tt)+ ) => {
        {
            let x = $crate::var!($x);
            let y = $crate::var!($y);
            let true_block = Box::new($crate::block!( @seq {}, $($true_block)+ ));
            let false_block = Box::new($crate::block!( @seq {}, $($false_block)+ ));
            $crate::lem::Ctrl::IfEq(x, y, true_block, false_block)
        }
    };
    ( if $x:ident != $y:ident { $($true_block:tt)+ } $($false_block:tt)+ ) => {
        {
            let x = $crate::var!($x);
            let y = $crate::var!($y);
            let true_block = Box::new($crate::block!( @seq {}, $($true_block)+ ));
            let false_block = Box::new($crate::block!( @seq {}, $($false_block)+ ));
            $crate::lem::Ctrl::IfEq(x, y, false_block, true_block)
        }
    };
    ( return ($($src:ident),*) ) => {
        $crate::lem::Ctrl::Return(
            vec![$($crate::var!($src)),*]
        )
    };
}

#[macro_export]
macro_rules! block {
    // seq entry point, with a separate bracketing to differentiate
    ({ $($body:tt)+ }) => {
        {
            $crate::block! ( @seq {}, $($body)* )
        }
    };
    // handle the recursion: as we see a statement, we push it to the limbs position in the pattern
    (@seq {$($limbs:expr)*}, let $tgt:ident : $kind:ident::$tag:ident ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt: $kind::$tag)
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = cast($src:ident, $kind:ident::$tag:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = cast($src, $kind::$tag))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = eq_tag($a:ident, $b:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = eq_tag($a, $b))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = eq_val($a:ident, $b:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = eq_val($a, $b))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = add($a:ident, $b:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = add($a, $b))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = sub($a:ident, $b:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = sub($a, $b))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = mul($a:ident, $b:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = mul($a, $b))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = div($a:ident, $b:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = div($a, $b))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = lt($a:ident, $b:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = lt($a, $b))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = bitwise_and($a:ident, $b:literal) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = bitwise_and($a, $b))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*},  let ($tgt1:ident, $tgt2:ident) = div_rem64($a:ident, $b:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let ($tgt1, $tgt2) = div_rem64($a, $b))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, emit($v:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(emit($v))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = Num($sym:literal) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = Num($sym))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = String($sym:literal) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = String($sym))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = Symbol($sym:literal) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = Symbol($sym))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident : $kind:ident::$tag:ident = hash2($src1:ident, $src2:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt: $kind::$tag = hash2($src1, $src2) )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident : $kind:ident::$tag:ident = hash3($src1:ident, $src2:ident, $src3:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt: $kind::$tag = hash3($src1, $src2, $src3) )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident : $kind:ident::$tag:ident = hash4($src1:ident, $src2:ident, $src3:ident, $src4:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt: $kind::$tag = hash4($src1, $src2, $src3, $src4))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let ($tgt1:ident, $tgt2:ident) = unhash2($src:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let ($tgt1, $tgt2) = unhash2($src) )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let ($tgt1:ident, $tgt2:ident, $tgt3:ident) = unhash3($src:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let ($tgt1, $tgt2, $tgt3) = unhash3($src) )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let ($tgt1:ident, $tgt2:ident, $tgt3:ident, $tgt4:ident) = unhash4($src:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let ($tgt1, $tgt2, $tgt3, $tgt4) = unhash4($src) )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = hide($sec:ident, $src:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = hide($sec, $src) )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let ($sec:ident, $src:ident) = open($hash:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let ($sec, $src) = open($hash) )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let ($($tgt:ident),*) = $func:ident($($arg:ident),*) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let ($($tgt),*) = $func($($arg),*))
            },
            $($tail)*
        )
    };

    (@seq {$($limbs:expr)*}, match $sii:ident.tag { $( $kind:ident::$tag:ident $(| $other_kind:ident::$other_tag:ident)* => $case_ops:tt )* } $(; $($def:tt)*)?) => {
        $crate::block! (
            @end
            {
                $($limbs)*
            },
            $crate::ctrl!( match $sii.tag { $( $kind::$tag $(| $other_kind::$other_tag)* => $case_ops )* } $(; $($def)*)? )
        )
    };
    (@seq {$($limbs:expr)*}, match $sii:ident.val { $( $cnstr:ident($val:literal) $(| $other_cnstr:ident($other_val:literal))* => $case_ops:tt )* } $(; $($def:tt)*)?) => {
        $crate::block! (
            @end
            {
                $($limbs)*
            },
            $crate::ctrl!( match $sii.val { $( $cnstr($val) $(| $other_cnstr($other_val))* => $case_ops )* } $(; $($def)*)? )
        )
    };
    (@seq {$($limbs:expr)*}, if $x:ident == $y:ident { $($true_block:tt)+ } $($false_block:tt)+ ) => {
        $crate::block! (
            @end
            {
                $($limbs)*
            },
            $crate::ctrl!( if $x == $y { $($true_block)+ } $($false_block)+ )
        )
    };
    (@seq {$($limbs:expr)*}, if $x:ident != $y:ident { $($true_block:tt)+ } $($false_block:tt)+ ) => {
        $crate::block! (
            @end
            {
                $($limbs)*
            },
            $crate::ctrl!( if $x != $y { $($true_block)+ } $($false_block)+ )
        )
    };
    (@seq {$($limbs:expr)*}, return ($($src:ident),*) $(;)?) => {
        $crate::block! (
            @end
            {
                $($limbs)*
            },
            $crate::lem::Ctrl::Return(vec![$($crate::var!($src)),*])
        )
    };
    (@seq {$($limbs:expr)*} ) => {
        {
            compile_error!("You must provide Func with a return at each path!");
        }
    };
    (@end {$($limbs:expr)*}, $cont:expr) => {
        {
            let ops = vec!($($limbs),*);
            let ctrl = $cont;
            $crate::lem::Block{ ops, ctrl }
        }
    }
}

#[macro_export]
macro_rules! func {
    ($name:ident($( $in:ident ),*): $size:expr => $lem:tt) => {
        $crate::lem::Func::new(
            stringify!($name).into(),
            vec![$($crate::var!($in)),*],
            $size,
            $crate::block!($lem),
        ).unwrap()
    };
}

#[cfg(test)]
mod tests {
    use crate::lem::{Block, Ctrl, Lit, Op, Tag, Var};
    use crate::state::lurk_sym;
    use crate::tag::ExprTag::*;

    #[inline]
    fn mptr(name: &str) -> Var {
        Var(name.into())
    }

    #[inline]
    fn match_tag(i: Var, cases: Vec<(Tag, Block)>) -> Ctrl {
        Ctrl::MatchTag(i, indexmap::IndexMap::from_iter(cases), None)
    }

    #[inline]
    fn match_val(i: Var, cases: Vec<(Lit, Block)>, def: Block) -> Ctrl {
        Ctrl::MatchVal(i, indexmap::IndexMap::from_iter(cases), Some(Box::new(def)))
    }

    #[test]
    fn test_macros() {
        let lemops = [
            Op::Null(mptr("foo"), Tag::Expr(Num)),
            Op::Hash2(mptr("foo"), Tag::Expr(Char), [mptr("bar"), mptr("baz")]),
            Op::Hash3(
                mptr("foo"),
                Tag::Expr(Char),
                [mptr("bar"), mptr("baz"), mptr("bazz")],
            ),
            Op::Hash4(
                mptr("foo"),
                Tag::Expr(Char),
                [mptr("bar"), mptr("baz"), mptr("bazz"), mptr("baxx")],
            ),
            Op::Unhash2([mptr("foo"), mptr("goo")], mptr("aaa")),
            Op::Unhash3([mptr("foo"), mptr("goo"), mptr("moo")], mptr("aaa")),
            Op::Unhash4(
                [mptr("foo"), mptr("goo"), mptr("moo"), mptr("noo")],
                mptr("aaa"),
            ),
            Op::Hide(mptr("bar"), mptr("baz"), mptr("bazz")),
            Op::Open(mptr("bar"), mptr("baz"), mptr("bazz")),
        ];
        let lemops_macro = vec![
            op!(let foo: Expr::Num),
            op!(let foo: Expr::Char = hash2(bar, baz)),
            op!(let foo: Expr::Char = hash3(bar, baz, bazz)),
            op!(let foo: Expr::Char = hash4(bar, baz, bazz, baxx)),
            op!(let (foo, goo) = unhash2(aaa)),
            op!(let (foo, goo, moo) = unhash3(aaa)),
            op!(let (foo, goo, moo, noo) = unhash4(aaa)),
            op!(let bar = hide(baz, bazz)),
            op!(let (bar, baz) = open(bazz)),
        ];

        for i in 0..9 {
            assert!(lemops[i] == lemops_macro[i]);
        }

        let ret = Ctrl::Return(vec![mptr("bar"), mptr("baz"), mptr("bazz")]);
        let block = Block {
            ops: lemops_macro,
            ctrl: ret,
        };
        let lem_macro_seq = block!({
            let foo: Expr::Num;
            let foo: Expr::Char = hash2(bar, baz);
            let foo: Expr::Char = hash3(bar, baz, bazz);
            let foo: Expr::Char = hash4(bar, baz, bazz, baxx);
            let (foo, goo) = unhash2(aaa);
            let (foo, goo, moo) = unhash3(aaa);
            let (foo, goo, moo, noo) = unhash4(aaa);
            let bar = hide(baz, bazz);
            let (bar, baz) = open(bazz);
            return (bar, baz, bazz);
        });

        assert!(block == lem_macro_seq);

        let foo = ctrl!(match www.tag {
            Expr::Num => {
                return (foo, foo, foo); // a single Ctrl will not turn into a Seq
            }
            Expr::Str => {
                let foo: Expr::Num;
                return (foo, foo, foo);
            }
            Expr::Char => {
                let foo: Expr::Num;
                let goo: Expr::Char;
                return (foo, goo, goo);
            }
        });
        assert!(
            foo == match_tag(
                mptr("www"),
                vec![
                    (
                        Tag::Expr(Num),
                        Block {
                            ops: vec![],
                            ctrl: Ctrl::Return(vec![mptr("foo"), mptr("foo"), mptr("foo")]),
                        }
                    ),
                    (
                        Tag::Expr(Str),
                        Block {
                            ops: vec![Op::Null(mptr("foo"), Tag::Expr(Num))],
                            ctrl: Ctrl::Return(vec![mptr("foo"), mptr("foo"), mptr("foo")]),
                        }
                    ),
                    (
                        Tag::Expr(Char),
                        Block {
                            ops: vec![
                                Op::Null(mptr("foo"), Tag::Expr(Num)),
                                Op::Null(mptr("goo"), Tag::Expr(Char))
                            ],
                            ctrl: Ctrl::Return(vec![mptr("foo"), mptr("goo"), mptr("goo")]),
                        }
                    )
                ]
            )
        );

        let moo = ctrl!(
            match www.val {
                Symbol("nil") => {
                    return (foo, foo, foo); // a single Ctrl will not turn into a Seq
                }
                Symbol("cons") => {
                    let foo: Expr::Num;
                    let goo: Expr::Char;
                    return (foo, goo, goo);
                }
            };
            let xoo: Expr::Str;
            return (xoo, xoo, xoo);
        );

        assert!(
            moo == match_val(
                mptr("www"),
                vec![
                    (
                        Lit::Symbol(lurk_sym("nil")),
                        Block {
                            ops: vec![],
                            ctrl: Ctrl::Return(vec![mptr("foo"), mptr("foo"), mptr("foo")]),
                        }
                    ),
                    (
                        Lit::Symbol(lurk_sym("cons")),
                        Block {
                            ops: vec![
                                Op::Null(mptr("foo"), Tag::Expr(Num)),
                                Op::Null(mptr("goo"), Tag::Expr(Char))
                            ],
                            ctrl: Ctrl::Return(vec![mptr("foo"), mptr("goo"), mptr("goo")]),
                        }
                    )
                ],
                Block {
                    ops: vec![Op::Null(mptr("xoo"), Tag::Expr(Str))],
                    ctrl: Ctrl::Return(vec![mptr("xoo"), mptr("xoo"), mptr("xoo")]),
                }
            )
        );
    }
}
