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
    ( Op1::$tag:ident ) => {
        $crate::lem::Tag::Op1($crate::tag::Op1::$tag)
    };
    ( Op2::$tag:ident ) => {
        $crate::lem::Tag::Op2($crate::tag::Op2::$tag)
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
    ( let $tgt:ident = not($a:ident) ) => {
        $crate::lem::Op::Not(
            $crate::var!($tgt),
            $crate::var!($a),
        )
    };
    ( let $tgt:ident = and($a:ident, $b:ident) ) => {
        $crate::lem::Op::And(
            $crate::var!($tgt),
            $crate::var!($a),
            $crate::var!($b),
        )
    };
    ( let $tgt:ident = or($a:ident, $b:ident) ) => {
        $crate::lem::Op::Or(
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
    ( let $tgt:ident = truncate($a:ident, $b:literal) ) => {
        $crate::lem::Op::Trunc(
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
    ( let $tgt:ident : $kind:ident::$tag:ident = cons2($src1:ident, $src2:ident) ) => {
        $crate::lem::Op::Cons2(
            $crate::var!($tgt),
            $crate::tag!($kind::$tag),
            $crate::vars!($src1, $src2),
        )
    };
    ( let $tgt:ident : $kind:ident::$tag:ident = cons3($src1:ident, $src2:ident, $src3:ident) ) => {
        $crate::lem::Op::Cons3(
            $crate::var!($tgt),
            $crate::tag!($kind::$tag),
            $crate::vars!($src1, $src2, $src3),
        )
    };
    ( let $tgt:ident : $kind:ident::$tag:ident = cons4($src1:ident, $src2:ident, $src3:ident, $src4:ident) ) => {
        $crate::lem::Op::Cons4(
            $crate::var!($tgt),
            $crate::tag!($kind::$tag),
            $crate::vars!($src1, $src2, $src3, $src4),
        )
    };
    ( let ($tgt1:ident, $tgt2:ident) = decons2($src:ident) ) => {
        $crate::lem::Op::Decons2(
            $crate::vars!($tgt1, $tgt2),
            $crate::var!($src),
        )
    };
    ( let ($tgt1:ident, $tgt2:ident, $tgt3:ident) = decons3($src:ident) ) => {
        $crate::lem::Op::Decons3($crate::vars!($tgt1, $tgt2, $tgt3), $crate::var!($src))
    };
    ( let ($tgt1:ident, $tgt2:ident, $tgt3:ident, $tgt4:ident) = decons4($src:ident) ) => {
        $crate::lem::Op::Decons4(
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
    ( match symbol $sii:ident { $( $sym:expr $(, $other_sym:expr)* => $case_ops:tt )* } $(; $($def:tt)*)? ) => {
        {
            let mut cases = indexmap::IndexMap::new();
            $(
                if cases.insert(
                    $crate::state::lurk_sym($sym),
                    $crate::block!( $case_ops ),
                ).is_some() {
                    panic!("Repeated value on `match`");
                };
                $(
                    if cases.insert(
                        $crate::state::lurk_sym($other_sym),
                        $crate::block!( $case_ops ),
                    ).is_some() {
                        panic!("Repeated value on `match`");
                    };
                )*
            )*
            let default = None $( .or (Some(Box::new($crate::block!( @seq {}, $($def)* )))) )?;
            $crate::lem::Ctrl::MatchSymbol($crate::var!($sii), cases, default)
        }
    };
    ( if $x:ident { $($true_block:tt)+ } $($false_block:tt)+ ) => {
        {
            let x = $crate::var!($x);
            let true_block = Box::new($crate::block!( @seq {}, $($true_block)+ ));
            let false_block = Box::new($crate::block!( @seq {}, $($false_block)+ ));
            $crate::lem::Ctrl::If(x, true_block, false_block)
        }
    };
    ( if !$x:ident { $($true_block:tt)+ } $($false_block:tt)+ ) => {
        {
            let x = $crate::var!($x);
            let true_block = Box::new($crate::block!( @seq {}, $($true_block)+ ));
            let false_block = Box::new($crate::block!( @seq {}, $($false_block)+ ));
            $crate::lem::Ctrl::If(x, false_block, true_block)
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
    (@seq {$($limbs:expr)*}, let $tgt:ident = not($a:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = not($a))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = and($a:ident, $b:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = and($a, $b))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = or($a:ident, $b:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = or($a, $b))
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
    (@seq {$($limbs:expr)*}, let $tgt:ident = truncate($a:ident, $b:literal) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt = truncate($a, $b))
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
    (@seq {$($limbs:expr)*}, let $tgt:ident : $kind:ident::$tag:ident = cons2($src1:ident, $src2:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt: $kind::$tag = cons2($src1, $src2) )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident : $kind:ident::$tag:ident = cons3($src1:ident, $src2:ident, $src3:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt: $kind::$tag = cons3($src1, $src2, $src3) )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident : $kind:ident::$tag:ident = cons4($src1:ident, $src2:ident, $src3:ident, $src4:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let $tgt: $kind::$tag = cons4($src1, $src2, $src3, $src4))
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let ($tgt1:ident, $tgt2:ident) = decons2($src:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let ($tgt1, $tgt2) = decons2($src) )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let ($tgt1:ident, $tgt2:ident, $tgt3:ident) = decons3($src:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let ($tgt1, $tgt2, $tgt3) = decons3($src) )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let ($tgt1:ident, $tgt2:ident, $tgt3:ident, $tgt4:ident) = decons4($src:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::op!(let ($tgt1, $tgt2, $tgt3, $tgt4) = decons4($src) )
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
    (@seq {$($limbs:expr)*}, match symbol $sii:ident { $( $sym:expr $(, $other_sym:expr)* => $case_ops:tt )* } $(; $($def:tt)*)?) => {
        $crate::block! (
            @end
            {
                $($limbs)*
            },
            $crate::ctrl!( match symbol $sii { $( $sym $(, $other_sym)* => $case_ops )* } $(; $($def)*)? )
        )
    };
    (@seq {$($limbs:expr)*}, if $x:ident { $($true_block:tt)+ } $($false_block:tt)+ ) => {
        $crate::block! (
            @end
            {
                $($limbs)*
            },
            $crate::ctrl!( if $x { $($true_block)+ } $($false_block)+ )
        )
    };
    (@seq {$($limbs:expr)*}, if !$x:ident { $($true_block:tt)+ } $($false_block:tt)+ ) => {
        $crate::block! (
            @end
            {
                $($limbs)*
            },
            $crate::ctrl!( if !$x { $($true_block)+ } $($false_block)+ )
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
    use crate::{
        lem::{Block, Ctrl, Op, Tag, Var},
        state::lurk_sym,
        tag::ExprTag::{Char, Num, Str},
        Symbol,
    };

    #[inline]
    fn mptr(name: &str) -> Var {
        Var(name.into())
    }

    #[inline]
    fn match_tag(i: Var, cases: Vec<(Tag, Block)>) -> Ctrl {
        Ctrl::MatchTag(i, indexmap::IndexMap::from_iter(cases), None)
    }

    #[inline]
    fn match_symbol(i: Var, cases: Vec<(Symbol, Block)>, def: Block) -> Ctrl {
        Ctrl::MatchSymbol(i, indexmap::IndexMap::from_iter(cases), Some(Box::new(def)))
    }

    #[test]
    fn test_macros() {
        let lemops = [
            Op::Null(mptr("foo"), Tag::Expr(Num)),
            Op::Cons2(mptr("foo"), Tag::Expr(Char), [mptr("bar"), mptr("baz")]),
            Op::Cons3(
                mptr("foo"),
                Tag::Expr(Char),
                [mptr("bar"), mptr("baz"), mptr("bazz")],
            ),
            Op::Cons4(
                mptr("foo"),
                Tag::Expr(Char),
                [mptr("bar"), mptr("baz"), mptr("bazz"), mptr("baxx")],
            ),
            Op::Decons2([mptr("foo"), mptr("goo")], mptr("aaa")),
            Op::Decons3([mptr("foo"), mptr("goo"), mptr("moo")], mptr("aaa")),
            Op::Decons4(
                [mptr("foo"), mptr("goo"), mptr("moo"), mptr("noo")],
                mptr("aaa"),
            ),
            Op::Hide(mptr("bar"), mptr("baz"), mptr("bazz")),
            Op::Open(mptr("bar"), mptr("baz"), mptr("bazz")),
        ];
        let lemops_macro = vec![
            op!(let foo: Expr::Num),
            op!(let foo: Expr::Char = cons2(bar, baz)),
            op!(let foo: Expr::Char = cons3(bar, baz, bazz)),
            op!(let foo: Expr::Char = cons4(bar, baz, bazz, baxx)),
            op!(let (foo, goo) = decons2(aaa)),
            op!(let (foo, goo, moo) = decons3(aaa)),
            op!(let (foo, goo, moo, noo) = decons4(aaa)),
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
            let foo: Expr::Char = cons2(bar, baz);
            let foo: Expr::Char = cons3(bar, baz, bazz);
            let foo: Expr::Char = cons4(bar, baz, bazz, baxx);
            let (foo, goo) = decons2(aaa);
            let (foo, goo, moo) = decons3(aaa);
            let (foo, goo, moo, noo) = decons4(aaa);
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
            match symbol www {
                "nil" => {
                    return (foo, foo, foo); // a single Ctrl will not turn into a Seq
                }
                "cons" => {
                    let foo: Expr::Num;
                    let goo: Expr::Char;
                    return (foo, goo, goo);
                }
            };
            let xoo: Expr::Str;
            return (xoo, xoo, xoo);
        );

        assert!(
            moo == match_symbol(
                mptr("www"),
                vec![
                    (
                        lurk_sym("nil"),
                        Block {
                            ops: vec![],
                            ctrl: Ctrl::Return(vec![mptr("foo"), mptr("foo"), mptr("foo")]),
                        }
                    ),
                    (
                        lurk_sym("cons"),
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
