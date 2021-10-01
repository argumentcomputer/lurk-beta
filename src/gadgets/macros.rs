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

// Enforces constraint that a implies b and that (not a) implices c.
macro_rules! if_then_else {
    ($cs:ident, $a:expr, $b:expr, $c:expr) => {
        enforce_implication(
            $cs.namespace(|| format!("if {} then {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        )
        .and_then(|_| {
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

// Allocates a bit (returned as Boolean) which is true if a and b are equal.
macro_rules! equal {
    ($cs:ident, $a:expr, $b:expr) => {
        alloc_equal(
            $cs.namespace(|| format!("{} equals {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        )
    };
}

// Returns a Boolean which is true if a and b are true.
macro_rules! and {
    ($cs:ident, $a:expr, $b:expr) => {
        Boolean::and(
            $cs.namespace(|| format!("{} and {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        )
    };
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

// Returns a Boolean which is true if a or b are true.
macro_rules! or {
    ($cs:ident, $a:expr, $b:expr) => {
        or(
            $cs.namespace(|| format!("{} or {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        )
    };
}

// Enforce that x is true.
macro_rules! is_true {
    ($cs:ident, $x:expr) => {
        enforce_true($cs.namespace(|| format!("{} is true!", stringify!($x))), $x);
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
