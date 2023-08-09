#[macro_export]
macro_rules! num {
    ($f:ty, $i:literal) => {
        $crate::syntax::Syntax::<$f>::Num(Pos::No, ($i as u64).into())
    };
    ($i:literal) => {
        $crate::syntax::Syntax::Num(Pos::No, ($i as u64).into())
    };
    ($i:expr) => {
        $crate::syntax::Syntax::Num(Pos::No, $i)
    };
}

#[macro_export]
macro_rules! uint {
    ($f:ty, $i:literal) => {
        $crate::syntax::Syntax::<$f>::UInt(Pos::No, $crate::uint::UInt::U64($i as u64))
    };
    ($i:literal) => {
        $crate::syntax::Syntax::UInt(Pos::No, $crate::uint::UInt::U64($i as u64))
    };
}

#[macro_export]
macro_rules! str {
    ($f:ty, $i:literal) => {
        $crate::syntax::Syntax::<$f>::String(Pos::No, $i.to_string())
    };
    ($i:literal) => {
        $crate::syntax::Syntax::String(Pos::No, $i.to_string())
    };
}

#[macro_export]
macro_rules! char {
    ($f:ty, $i:literal) => {
        $crate::syntax::Syntax::<$f>::Char(Pos::No, $i as char)
    };
    ($i:literal) => {
        $crate::syntax::Syntax::Char(Pos::No, $i as char)
    };
}

#[macro_export]
macro_rules! symbol {
    ( [$( $x:expr ),*] ) => {
        {
            let temp_vec = vec![ $( $x.to_string() ),* ];
            $crate::syntax::Syntax::Symbol(Pos::No, $crate::symbol::Symbol::sym_of_vec(temp_vec).into())
        }
    };
    ( $f:ty, [$( $x:expr ),*] ) => {
        {
            let temp_vec = vec![ $( $x.to_owned() ),* ];
            $crate::syntax::Syntax::<$f>::Symbol(Pos::No, $crate::symbol::Symbol::sym_of_vec(temp_vec).into())
        }
    };
}

#[macro_export]
macro_rules! keyword {
    ( [$( $x:expr ),*] ) => {
        {
            let temp_vec = vec![ $( $x.to_string() ),* ];
            $crate::syntax::Syntax::Symbol(Pos::No, $crate::symbol::Symbol::key_of_vec(temp_vec).into())
        }
    };
    ( $f:ty, [$( $x:expr ),*] ) => {
        {
            let temp_vec = vec![ $( $x.to_owned() ),* ];
            $crate::syntax::Syntax::<$f>::Path(Pos::No, $crate::symbol::Symbol::key_of_vec(temp_vec).into())
        }
    };
}

#[macro_export]
macro_rules! list {
    ([$( $x:expr ),*], $end:expr ) => {
        {
            let temp_vec = vec![ $( $x ),* ];
            $crate::syntax::Syntax::Improper(Pos::No, temp_vec, Box::new($end))
        }
    };
    ([$( $x:expr ),*] ) => {
        {
            let temp_vec = vec![ $( $x ),* ];
            $crate::syntax::Syntax::List(Pos::No, temp_vec)
        }
    };
    ($f:ty, [$( $x:expr ),*], $end:expr ) => {
        {
            let temp_vec = vec![ $( $x ),* ];
            $crate::syntax::Syntax::<$f>::Improper(Pos::No, temp_vec, Box::new($end))
        }
    };
    ($f:ty, [$( $x:expr ),*] ) => {
        {
            let temp_vec = vec![ $( $x ),* ];
            $crate::syntax::Syntax::<$f>::List(Pos::No, temp_vec)
        }
    };
}
