#[macro_export]
macro_rules! num {
  ($f:ty, $i:literal) => {
    $crate::syntax::Syn::<$f>::Num(Pos::No, ($i as u64).into())
  };
  ($i:literal) => {
    $crate::syntax::Syn::Num(Pos::No, ($i as u64).into())
  };
  ($i:expr) => {
    $crate::syntax::Syn::Num(Pos::No, $i)
  };
}

#[macro_export]
macro_rules! u64 {
  ($f:ty, $i:literal) => {
    $crate::syntax::Syn::<$f>::U64(Pos::No, ($i as u64))
  };
  ($i:literal) => {
    $crate::syntax::Syn::U64(Pos::No, ($i as u64))
  };
}

#[macro_export]
macro_rules! str {
  ($f:ty, $i:literal) => {
    $crate::syntax::Syn::<$f>::String(Pos::No, $i.to_string())
  };
  ($i:literal) => {
    $crate::syntax::Syn::String(Pos::No, $i.to_string())
  };
}

#[macro_export]
macro_rules! char {
  ($f:ty, $i:literal) => {
    $crate::syntax::Syn::<$f>::Char(Pos::No, $i as char)
  };
  ($i:literal) => {
    $crate::syntax::Syn::Char(Pos::No, $i as char)
  };
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! sym {
    ([$( $x:literal ),*] ) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x.to_string());
            )*
            $crate::syntax::Syn::Symbol(Pos::No, temp_vec)
        }
    };
    ($f:ty,  [$( $x:literal ),*] ) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x.to_string());
            )*
            $crate::syntax::Syn::<$f>::Symbol(Pos::No, temp_vec)
        }
    };
}

#[macro_export]
macro_rules! key {
    ([$( $x:literal ),*] ) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x.to_string());
            )*
            $crate::syntax::Syn::Keyword(Pos::No, temp_vec)
        }
    };
    ($f:ty,  [$( $x:literal ),*] ) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x.to_string());
            )*
            $crate::syntax::Syn::<$f>::Keyword(Pos::No, temp_vec)
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
            $crate::syntax::Syn::List(Pos::No, temp_vec, Some(Box::new($end)))
        }
    };
    ([$( $x:expr ),*] ) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x);
            )*
            $crate::syntax::Syn::List(Pos::No, temp_vec, None)
        }
    };
    ($f:ty,  [$( $x:expr ),*], $end:expr ) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x);
            )*
            $crate::syntax::Syn::<$f>::List(Pos::No, temp_vec, Some(Box::new($end)))
        }
    };
    ($f:ty,  [$( $x:expr ),*] ) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x);
            )*
            $crate::syntax::Syn::<$f>::List(Pos::No, temp_vec, None)
        }
    };
}

#[macro_export]
macro_rules! map {
    ([$( ($x:expr, $y:expr) ),*]) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push(($x, $y));
            )*
            $crate::syntax::Syn::Map(Pos::No, temp_vec)
        }
    };
    ($f:ty, [$( ($x:expr, $y:expr) ),*]) => {
        {
            #[allow(unused_mut)]
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push(($x, $y));
            )*
            $crate::syntax::Syn::<$f>::Map(Pos::No, temp_vec)
        }
    };
  }
