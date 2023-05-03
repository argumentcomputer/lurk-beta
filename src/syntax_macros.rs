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
macro_rules! u64 {
    ($f:ty, $i:literal) => {
        $crate::syntax::Syntax::<$f>::U64(Pos::No, ($i as u64))
    };
    ($i:literal) => {
        $crate::syntax::Syntax::U64(Pos::No, ($i as u64))
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

#[allow(unused_macros)]
#[macro_export]
macro_rules! symbol {
    ([$( $x:expr ),*]) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x.to_string());
            )*
            $crate::syntax::Syntax::Symbol(Pos::No, $crate::symbol::Symbol::Sym(temp_vec))
        }
    };
    ($f:ty, [$( $x:expr ),*] ) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x.to_string());
            )*
            $crate::syntax::Syntax::<$f>::Symbol(Pos::No, $crate::symbol::Symbol::Sym(temp_vec))
        }
    };
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! sym {
    [$( $x:expr ),*] => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x.to_string());
            )*
            $crate::symbol::Symbol::Sym(temp_vec)
        }
    };
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! lurksym {
    [$( $x:expr ),*] => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            temp_vec.push("lurk".to_string());
            $(
                temp_vec.push($x.to_string());
            )*
            $crate::symbol::Symbol::Sym(temp_vec)
        }
    };
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! lurkkey {
    [$( $x:expr ),*] => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            temp_vec.push("lurk".to_string());
            $(
                temp_vec.push($x.to_string());
            )*
            $crate::symbol::Symbol::Key(temp_vec)
        }
    };
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! key {
    [$( $x:expr ),*] => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x.to_string());
            )*
            $crate::symbol::Symbol::Key(temp_vec)
        }
    };
}

#[macro_export]
macro_rules! keyword {
    ([$( $x:expr ),*]) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x.to_string());
            )*
            $crate::syntax::Syntax::Symbol(Pos::No, $crate::sym::Symbol::Key(temp_vec))
        }
    };
    ($f:ty, [$( $x:expr ),*]) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x.to_string());
            )*
            $crate::syntax::Syntax::<$f>::Symbol(Pos::No, $crate::sym::Symbol::Key(temp_vec))
        }
    };
}

#[macro_export]
macro_rules! list {
    ($f:ty, [$( $x:expr ),*]) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x);
            )*
            $crate::syntax::Syntax::<$f>::List(Pos::No, temp_vec)
        }
    };
}
