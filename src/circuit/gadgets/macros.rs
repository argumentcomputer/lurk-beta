#![allow(unused_macros)]

// Enforces constraint that a implies b.
macro_rules! if_then {
    ($cs:ident, $a:expr, $b:expr) => {
        enforce_implication(
            $cs.namespace(|| format!("if {} then {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        )
    };
}

// Enforces constraint that a implies b and that (not a) implies c.
macro_rules! if_then_else {
    ($cs:ident, $a:expr, $b:expr, $c:expr) => {
        if_then!(cs, $a, $b,).and_then(|_| {
            enforce_implication(
                $cs.namespace(|| {
                    format!(
                        "if {} then {} else {}",
                        stringify!($a),
                        stringify!($b),
                        stringify!($c)
                    )
                }),
                &Boolean::not($a),
                $c,
            )
        })
    };
}

// If expression.
macro_rules! pick {
    ($cs:ident, $a:expr, $b:expr, $c:expr) => {{
        let a = $a;
        let b = $b;
        let c = $c;
        let cs = $cs.namespace(|| {
            format!(
                "ifx {} {} {}",
                stringify!($a),
                stringify!($b),
                stringify!($c)
            )
        });
        pick(cs, a, b, c)
    }};
}

macro_rules! pick_ptr {
    ($cs:ident, $a:expr, $b:expr, $c:expr) => {{
        let a = $a;
        let b = $b;
        let c = $c;
        let cs = $cs.namespace(|| {
            format!(
                "ifx_t {} {} {}",
                stringify!($a),
                stringify!($b),
                stringify!($c)
            )
        });
        AllocatedPtr::pick(cs, a, b, c)
    }};
}

// Allocates a bit (returned as Boolean) which is true if a and b are equal.
macro_rules! equal {
    ($cs:expr, $a:expr, $b:expr) => {
        alloc_equal(
            $cs.namespace(|| format!("{} equal {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        )
    };
}

// Allocates a bit (returned as Boolean) which is true if a is equal to constant, c.
macro_rules! equal_const {
    ($cs:expr, $a:expr, $c:expr) => {
        alloc_equal_const(
            $cs.namespace(|| format!("{} equal const {}", stringify!($a), stringify!($c))),
            $a,
            $c,
        )
    };
}

macro_rules! implies_equal {
    ($cs:ident, $condition:expr, $a: expr, $b: expr) => {{
        let equal = equal!($cs, $a, $b)?;
        enforce_implication(
            $cs.namespace(|| {
                format!(
                    "implies_equal: {} => {} == {}",
                    stringify!($condition),
                    stringify!($a),
                    stringify!($b)
                )
            }),
            $condition,
            &equal,
        )?;
    }};
}

macro_rules! implies_equal_t {
    ($cs:ident, $condition:expr, $a: expr, $b: expr) => {
        let equal = equal_t!($cs, $a, $b)?;

        enforce_implication(
            $cs.namespace(|| {
                format!(
                    "implies_equal_t: {} => {} == {}",
                    stringify!($condition),
                    stringify!($a),
                    stringify!($b)
                )
            }),
            $condition,
            &equal,
        )?;
    };
}

macro_rules! implies {
    ($cs:ident, $condition:expr, $implication:expr) => {{
        enforce_implication(
            $cs.namespace(|| {
                format!(
                    "implies: {} => {}",
                    stringify!($condition),
                    stringify!($implication)
                )
            }),
            $condition,
            $implication,
        )?;
    }};
}

// Returns a Boolean which is true if all of its arguments are true.
macro_rules! and {
    ($cs:expr, $a:expr, $b:expr) => {
        Boolean::and(
            $cs.namespace(|| format!("{} and {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        )
    };
    ($cs:expr, $a:expr, $b:expr, $c:expr, $($x:expr),+) => {{
        let and_tmp_cs_ =  &mut $cs.namespace(|| format!("and({})", stringify!([$a, $b, $c, $($x),*])));
        and_v(and_tmp_cs_, &[$a, $b, $c, $($x),*])
    }};
    ($cs:ident, $a:expr, $($x:expr),+) => {{
        let and_tmp_cs_ =  &mut $cs.namespace(|| format!("and({})", stringify!([$a, $($x),*])));
        let and_tmp_ = and!(and_tmp_cs_, $($x),*)?;
        and!(and_tmp_cs_, $a, &and_tmp_)
    }};

}

macro_rules! tag_and_hash_equal {
    ($cs:ident, $a_tag:expr, $b_tag:expr, $a_hash:expr, $b_hash:expr) => {{
        let tags_equal = equal!($cs, &$a_tag, &$b_tag)?;
        let hashes_equal = equal!($cs, &$a_hash, &$b_hash)?;
        let mut cs = $cs.namespace(|| {
            format!(
                "({} equals {}) and ({} equals {})",
                stringify!($a_tag),
                stringify!($b_tag),
                stringify!($a_hash),
                stringify!($b_hash)
            )
        });
        and!(cs, &tags_equal, &hashes_equal)
    }};
}

macro_rules! equal_t {
    ($cs:ident, $a:expr, $b:expr) => {{
        let tags_equal = equal!($cs, &$a.tag(), &$b.tag())?;
        let hashes_equal = equal!($cs, &$a.hash(), &$b.hash())?;
        let mut cs = $cs.namespace(|| {
            format!(
                "({} equals {}) and ({} equals {})",
                stringify!($a.tag),
                stringify!($b.tag),
                stringify!($a.hash),
                stringify!($b.hash)
            )
        });
        and!(cs, &tags_equal, &hashes_equal)
    }};
}

// Returns a Boolean which is true if any of its arguments are true.
macro_rules! or {
    ($cs:expr, $a:expr, $b:expr) => {
        or(
            $cs.namespace(|| format!("{} or {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        )
    };
    ($cs:expr, $a:expr, $b:expr, $c:expr, $($x:expr),+) => {{
        let or_tmp_cs_ =  &mut $cs.namespace(|| format!("or({})", stringify!(vec![$a, $b, $c, $($x),*])));
        or_v(or_tmp_cs_, &[$a, $b, $c, $($x),*])
    }};
    ($cs:expr, $a:expr, $($x:expr),+) => {{
        let or_tmp_cs_ =  &mut $cs.namespace(|| format!("or {}", stringify!(vec![$a, $($x),*])));
        let or_tmp_ = or!(or_tmp_cs_, $($x),*)?;
        or!(or_tmp_cs_, $a, &or_tmp_)
    }};
}

// Enforce that x is true.
macro_rules! is_true {
    ($cs:ident, $x:expr) => {
        enforce_true($cs.namespace(|| format!("{} is true!", stringify!($x))), $x)
    };
}

// Enforce that x is false.
macro_rules! is_false {
    ($cs:ident, $x:expr) => {
        enforce_false(
            $cs.namespace(|| format!("{} is false!", stringify!($x))),
            $x,
        );
    };
}

macro_rules! allocate_tag {
    ($cs:ident, $tag:expr) => {
        AllocatedNum::alloc(
            $cs.namespace(|| format!("{} tag", stringify!($tag))),
            || Ok($tag.fr()),
        )
    };
}

macro_rules! allocate_continuation_tag {
    ($cs:ident, $continuation_tag:expr) => {
        AllocatedNum::alloc(
            $cs.namespace(|| format!("{} continuation tag", stringify!($continuation_tag))),
            || Ok($continuation_tag.cont_tag_fr()),
        )
    };
}

macro_rules! boolean_num {
    ($cs:expr, $boolean:expr) => {
        boolean_to_num(
            $cs.namespace(|| format!("boolean_num({})", stringify!($boolean))),
            $boolean,
        )
    };
}
