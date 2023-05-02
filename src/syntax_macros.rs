#[macro_export]
macro_rules! num {
  ($f:ty, $i:literal) => {
    $lurk::syntax::Syntax::<$f>::Num(Pos::No, ($i as u64).into())
  };
  ($i:literal) => {
    $lurk::syntax::Syntax::Num(Pos::No, ($i as u64).into())
  };
  ($i:expr) => {
    $lurk::syntax::Syntax::Num(Pos::No, $i)
  };
}

#[macro_export]
macro_rules! u64 {
  ($f:ty, $i:literal) => {
    $lurk::syntax::Syntax::<$f>::U64(Pos::No, ($i as u64))
  };
  ($i:literal) => {
    $lurk::syntax::Syntax::U64(Pos::No, ($i as u64))
  };
}

#[macro_export]
macro_rules! str {
  ($f:ty, $i:literal) => {
    $lurk::syntax::Syntax::<$f>::String(Pos::No, $i.to_string())
  };
  ($i:literal) => {
    $lurk::syntax::Syntax::String(Pos::No, $i.to_string())
  };
}

#[macro_export]
macro_rules! char {
  ($f:ty, $i:literal) => {
    $lurk::syntax::Syntax::<$f>::Char(Pos::No, $i as char)
  };
  ($i:literal) => {
    $lurk::syntax::Syntax::Char(Pos::No, $i as char)
  };
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! symbol {
    ([$( $x:expr ),*] ) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x.to_string());
            )*
            $lurk::syntax::Syntax::Symbol(Pos::No, $lurk::sym::Symbol::Sym(temp_vec))
        }
    };
    ($f:ty,  [$( $x:expr ),*] ) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x.to_string());
            )*
            $lurk::syntax::Syntax::<$f>::Symbol(Pos::No, $lurk::sym::Symbol::Sym(temp_vec))
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
            $lurk::sym::Symbol::Sym(temp_vec)
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
            $lurk::sym::Symbol::Sym(temp_vec)
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
            $lurk::sym::Symbol::Key(temp_vec)
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
            $lurk::sym::Symbol::Key(temp_vec)
        }
    };
}

#[macro_export]
macro_rules! keyword {
    ([$( $x:expr ),*] ) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x.to_string());
            )*
            $lurk::syntax::Syntax::Symbol(Pos::No, $lurk::sym::Symbol::Key(temp_vec))
        }
    };
    ($f:ty,  [$( $x:expr ),*] ) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x.to_string());
            )*
            $lurk::syntax::Syntax::<$f>::Symbol(Pos::No, $lurk::sym::Symbol::Key(temp_vec))
        }
    };
}

#[macro_export]
macro_rules! list {
    ([$( $x:expr ),*], $end:expr ) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x);
            )*
            $lurk::syntax::Syntax::List(Pos::No, temp_vec, Box::new($end))
        }
    };
    ([$( $x:expr ),*] ) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x);
            )*
            $lurk::syntax::Syntax::List(Pos::No, temp_vec, Box::new($lurk::syntax::Syntax::Symbol(Pos::No, lurksym!["nil"])))
        }
    };
    ($f:ty,  [$( $x:expr ),*], $end:expr ) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x);
            )*
            $lurk::syntax::Syntax::<$f>::List(Pos::No, temp_vec, Box::new($end))
        }
    };
    ($f:ty,  [$( $x:expr ),*] ) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x);
            )*
            $lurk::syntax::Syntax::<$f>::List(Pos::No, temp_vec, Box::new($lurk::syntax::Syntax::Symbol(Pos::No, lurksym!["nil"])))
        }
    };
}
