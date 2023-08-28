
pub fn safe_uncons<F: LurkField>(store: &mut Store<F>, xs: Ptr<F>) -> [Ptr<F>; 2] {
let nil = store.intern_symbol(".lurk.nil".into());
let nil = nil.cast(Tag::Expr(Nil));
let empty_str = store.intern_string("");
match xs.tag() {
Tag::Expr(Nil) => {
return [nil, nil];
}
Tag::Expr(Cons) => {
todo_op;
return [car, cdr];
}
Tag::Expr(Str) => {
if xs == empty_str {
return [nil, empty_str];
} else {
todo_op;
return [car, cdr];
}
}
_ => unreachable!(),
}
}
pub fn env_to_use<F: LurkField>(store: &mut Store<F>, smaller_env: Ptr<F>, smaller_rec_env: Ptr<F>) -> [Ptr<F>; 1] {
match smaller_rec_env.tag() {
Tag::Expr(Nil) => {
return [smaller_env];
}
_ => {
todo_op;
return [env];
}
}
}
pub fn extract_arg<F: LurkField>(store: &mut Store<F>, args: Ptr<F>) -> [Ptr<F>; 2] {
match args.tag() {
Tag::Expr(Nil) => {
let dummy = store.intern_symbol(".lurk.dummy".into());
let nil = store.intern_symbol(".lurk.nil".into());
let nil = nil.cast(Tag::Expr(Nil));
return [dummy, nil];
}
Tag::Expr(Cons) => {
todo_op;
return [arg, rest];
}
_ => unreachable!(),
}
}
pub fn expand_bindings<F: LurkField>(store: &mut Store<F>, head: Ptr<F>, body: Ptr<F>, body1: Ptr<F>, rest_bindings: Ptr<F>) -> [Ptr<F>; 1] {
match rest_bindings.tag() {
Tag::Expr(Nil) => {
return [body1];
}
_ => {
todo_op;
todo_op;
return [expanded];
}
}
}
pub fn choose_let_cont<F: LurkField>(store: &mut Store<F>, head: Ptr<F>, var: Ptr<F>, env: Ptr<F>, expanded: Ptr<F>, cont: Ptr<F>) -> [Ptr<F>; 1] {
match &store.fetch_symbol(&head).unwrap().fmt_to_string() {
".lurk.let" => {
todo_op;
return [cont];
}
".lurk.letrec" => {
todo_op;
return [cont];
}
_ => unreachable!(),
}
}
pub fn is_unop<F: LurkField>(store: &mut Store<F>, head: Ptr<F>) -> [Ptr<F>; 1] {
let nil = store.intern_symbol(".lurk.nil".into());
let nil = nil.cast(Tag::Expr(Nil));
let t = store.intern_symbol(".lurk.t".into());
match &store.fetch_symbol(&head).unwrap().fmt_to_string() {
".lurk.car" => {
return [t];
}
".lurk.cdr" => {
return [t];
}
".lurk.commit" => {
return [t];
}
".lurk.num" => {
return [t];
}
".lurk.u64" => {
return [t];
}
".lurk.comm" => {
return [t];
}
".lurk.char" => {
return [t];
}
".lurk.open" => {
return [t];
}
".lurk.secret" => {
return [t];
}
".lurk.atom" => {
return [t];
}
".lurk.emit" => {
return [t];
}
_ => {
return [nil];
}
}
}
pub fn is_binop<F: LurkField>(store: &mut Store<F>, head: Ptr<F>) -> [Ptr<F>; 1] {
let nil = store.intern_symbol(".lurk.nil".into());
let nil = nil.cast(Tag::Expr(Nil));
let t = store.intern_symbol(".lurk.t".into());
match &store.fetch_symbol(&head).unwrap().fmt_to_string() {
".lurk.cons" => {
return [t];
}
".lurk.strcons" => {
return [t];
}
".lurk.hide" => {
return [t];
}
".lurk.+" => {
return [t];
}
".lurk.-" => {
return [t];
}
".lurk.*" => {
return [t];
}
".lurk./" => {
return [t];
}
".lurk.%" => {
return [t];
}
".lurk.=" => {
return [t];
}
".lurk.eq" => {
return [t];
}
".lurk.<" => {
return [t];
}
".lurk.>" => {
return [t];
}
".lurk.<=" => {
return [t];
}
".lurk.>=" => {
return [t];
}
_ => {
return [nil];
}
}
}
pub fn make_call<F: LurkField>(store: &mut Store<F>, head: Ptr<F>, rest: Ptr<F>, env: Ptr<F>, cont: Ptr<F>) -> [Ptr<F>; 4] {
let ret = Ptr::Atom(Tag::Ctrl(Return), F::ZERO);
match rest.tag() {
Tag::Expr(Nil) => {
todo_op;
return [head, env, cont, ret];
}
Tag::Expr(Cons) => {
todo_op;
match more_args.tag() {
Tag::Expr(Nil) => {
todo_op;
return [head, env, cont, ret];
}
_ => {
let nil = store.intern_symbol(".lurk.nil".into());
let nil = nil.cast(Tag::Expr(Nil));
todo_op;
todo_op;
todo_op;
return [expanded, env, cont, ret];
}
}
}
_ => unreachable!(),
}
}
pub fn is_potentially_fun<F: LurkField>(store: &mut Store<F>, head: Ptr<F>) -> [Ptr<F>; 1] {
let t = store.intern_symbol(".lurk.t".into());
let nil = store.intern_symbol(".lurk.nil".into());
let nil = nil.cast(Tag::Expr(Nil));
match head.tag() {
Tag::Expr(Fun) => {
return [t];
}
Tag::Expr(Cons) => {
return [t];
}
Tag::Expr(Thunk) => {
return [t];
}
_ => {
return [nil];
}
}
}
pub fn reduce<F: LurkField>(store: &mut Store<F>, expr: Ptr<F>, env: Ptr<F>, cont: Ptr<F>) -> [Ptr<F>; 4] {
let ret = Ptr::Atom(Tag::Ctrl(Return), F::ZERO);
let apply = Ptr::Atom(Tag::Ctrl(ApplyContinuation), F::ZERO);
let errctrl = Ptr::Atom(Tag::Ctrl(Error), F::ZERO);
let err = Ptr::Atom(Tag::Cont(Error), F::ZERO);
let nil = store.intern_symbol(".lurk.nil".into());
let nil = nil.cast(Tag::Expr(Nil));
let t = store.intern_symbol(".lurk.t".into());
match cont.tag() {
Tag::Cont(Terminal) => {
return [expr, env, cont, ret];
}
Tag::Cont(Error) => {
return [expr, env, cont, ret];
}
_ => {
match expr.tag() {
Tag::Expr(Nil) => {
return [expr, env, cont, apply];
}
Tag::Expr(Fun) => {
return [expr, env, cont, apply];
}
Tag::Expr(Num) => {
return [expr, env, cont, apply];
}
Tag::Expr(Str) => {
return [expr, env, cont, apply];
}
Tag::Expr(Char) => {
return [expr, env, cont, apply];
}
Tag::Expr(Comm) => {
return [expr, env, cont, apply];
}
Tag::Expr(U64) => {
return [expr, env, cont, apply];
}
Tag::Expr(Key) => {
return [expr, env, cont, apply];
}
Tag::Expr(Thunk) => {
todo_op;
return [thunk_expr, env, thunk_continuation, apply];
}
Tag::Expr(Sym) => {
match &store.fetch_symbol(&expr).unwrap().fmt_to_string() {
".lurk.nil" => {
return [expr, env, cont, apply];
}
".lurk.t" => {
return [expr, env, cont, apply];
}
_ => {
match env.tag() {
Tag::Expr(Nil) => {
return [expr, env, err, errctrl];
}
_ => {
let [binding, smaller_env] = safe_uncons(store, env);
match binding.tag() {
Tag::Expr(Nil) => {
return [expr, env, err, errctrl];
}
_ => {
let [var_or_rec_binding, val_or_more_rec_env] = safe_uncons(store, binding);
match var_or_rec_binding.tag() {
Tag::Expr(Sym) => {
if var_or_rec_binding == expr {
return [val_or_more_rec_env, env, cont, apply];
} else {
match cont.tag() {
Tag::Cont(Lookup) => {
return [expr, smaller_env, cont, ret];
}
_ => {
todo_op;
return [expr, smaller_env, cont, ret];
}
}
}
}
Tag::Expr(Cons) => {
let [v2, val2] = safe_uncons(store, var_or_rec_binding);
if v2 == expr {
match val2.tag() {
Tag::Expr(Fun) => {
todo_op;
todo_op;
todo_op;
return [fun, env, cont, apply];
}
_ => {
return [val2, env, cont, apply];
}
}
} else {
let [env_to_use] = env_to_use(store, smaller_env, val_or_more_rec_env);
match cont.tag() {
Tag::Cont(Lookup) => {
return [expr, env_to_use, cont, ret];
}
_ => {
todo_op;
return [expr, env_to_use, cont, ret];
}
}
}
}
_ => {
return [expr, env, err, errctrl];
}
}
}
}
}
}
}
}
}
Tag::Expr(Cons) => {
todo_op;
match rest.tag() {
Tag::Expr(Sym) => {
return [expr, env, err, errctrl];
}
Tag::Expr(Fun) => {
return [expr, env, err, errctrl];
}
Tag::Expr(Num) => {
return [expr, env, err, errctrl];
}
Tag::Expr(Thunk) => {
return [expr, env, err, errctrl];
}
Tag::Expr(Str) => {
return [expr, env, err, errctrl];
}
Tag::Expr(Char) => {
return [expr, env, err, errctrl];
}
Tag::Expr(Comm) => {
return [expr, env, err, errctrl];
}
Tag::Expr(U64) => {
return [expr, env, err, errctrl];
}
Tag::Expr(Key) => {
return [expr, env, err, errctrl];
}
_ => {
match head.tag() {
Tag::Expr(Sym) => {
match &store.fetch_symbol(&head).unwrap().fmt_to_string() {
".lurk.lambda" => {
let [args, body] = safe_uncons(store, rest);
let [arg, cdr_args] = extract_arg(store, args);
match arg.tag() {
Tag::Expr(Sym) => {
match cdr_args.tag() {
Tag::Expr(Nil) => {
todo_op;
return [function, env, cont, apply];
}
_ => {
todo_op;
todo_op;
todo_op;
todo_op;
return [function, env, cont, apply];
}
}
}
_ => {
return [expr, env, err, errctrl];
}
}
}
".lurk.quote" => {
let [quoted, end] = safe_uncons(store, rest);
match end.tag() {
Tag::Expr(Nil) => {
return [quoted, env, cont, apply];
}
_ => {
return [expr, env, err, errctrl];
}
}
}
".lurk.let" => {
let [bindings, body] = safe_uncons(store, rest);
let [body1, rest_body] = safe_uncons(store, body);
match body.tag() {
Tag::Expr(Nil) => {
return [expr, env, err, errctrl];
}
_ => {
match rest_body.tag() {
Tag::Expr(Nil) => {
match bindings.tag() {
Tag::Expr(Nil) => {
return [body1, env, cont, ret];
}
_ => {
let [binding1, rest_bindings] = safe_uncons(store, bindings);
let [var, vals] = safe_uncons(store, binding1);
match var.tag() {
Tag::Expr(Sym) => {
let [val, end] = safe_uncons(store, vals);
match end.tag() {
Tag::Expr(Nil) => {
let [expanded] = expand_bindings(store, head, body, body1, rest_bindings);
let [cont] = choose_let_cont(store, head, var, env, expanded, cont);
return [val, env, cont, ret];
}
_ => {
return [expr, env, err, errctrl];
}
}
}
_ => {
return [expr, env, err, errctrl];
}
}
}
}
}
_ => {
return [expr, env, err, errctrl];
}
}
}
}
}
".lurk.letrec" => {
let [bindings, body] = safe_uncons(store, rest);
let [body1, rest_body] = safe_uncons(store, body);
match body.tag() {
Tag::Expr(Nil) => {
return [expr, env, err, errctrl];
}
_ => {
match rest_body.tag() {
Tag::Expr(Nil) => {
match bindings.tag() {
Tag::Expr(Nil) => {
return [body1, env, cont, ret];
}
_ => {
let [binding1, rest_bindings] = safe_uncons(store, bindings);
let [var, vals] = safe_uncons(store, binding1);
match var.tag() {
Tag::Expr(Sym) => {
let [val, end] = safe_uncons(store, vals);
match end.tag() {
Tag::Expr(Nil) => {
let [expanded] = expand_bindings(store, head, body, body1, rest_bindings);
let [cont] = choose_let_cont(store, head, var, env, expanded, cont);
return [val, env, cont, ret];
}
_ => {
return [expr, env, err, errctrl];
}
}
}
_ => {
return [expr, env, err, errctrl];
}
}
}
}
}
_ => {
return [expr, env, err, errctrl];
}
}
}
}
}
".lurk.begin" => {
let [arg1, more] = safe_uncons(store, rest);
match more.tag() {
Tag::Expr(Nil) => {
return [arg1, env, cont, ret];
}
_ => {
todo_op;
return [arg1, env, cont, ret];
}
}
}
".lurk.eval" => {
match rest.tag() {
Tag::Expr(Nil) => {
return [expr, env, err, errctrl];
}
_ => {
let [arg1, more] = safe_uncons(store, rest);
match more.tag() {
Tag::Expr(Nil) => {
todo_op;
return [arg1, env, cont, ret];
}
_ => {
todo_op;
return [arg1, env, cont, ret];
}
}
}
}
}
".lurk.if" => {
let [condition, more] = safe_uncons(store, rest);
match more.tag() {
Tag::Expr(Nil) => {
return [expr, env, err, errctrl];
}
_ => {
todo_op;
return [condition, env, cont, ret];
}
}
}
".lurk.current-env" => {
match rest.tag() {
Tag::Expr(Nil) => {
return [env, env, cont, apply];
}
_ => {
return [expr, env, err, errctrl];
}
}
}
_ => {
let [op] = is_unop(store, head);
if op == t {
match rest.tag() {
Tag::Expr(Nil) => {
return [expr, env, err, errctrl];
}
_ => {
todo_op;
match end.tag() {
Tag::Expr(Nil) => {
todo_op;
return [arg1, env, cont, ret];
}
_ => {
return [expr, env, err, errctrl];
}
}
}
}
} else {
let [op] = is_binop(store, head);
if op == t {
match rest.tag() {
Tag::Expr(Nil) => {
return [expr, env, err, errctrl];
}
_ => {
todo_op;
match more.tag() {
Tag::Expr(Nil) => {
return [expr, env, err, errctrl];
}
_ => {
todo_op;
return [arg1, env, cont, ret];
}
}
}
}
} else {
let [fun, env, cont, ret] = make_call(store, head, rest, env, cont);
return [fun, env, cont, ret];
}
}
}
}
}
_ => {
let [potentially_fun] = is_potentially_fun(store, head);
if potentially_fun == t {
let [fun, env, cont, ret] = make_call(store, head, rest, env, cont);
return [fun, env, cont, ret];
} else {
return [expr, env, err, errctrl];
}
}
}
}
}
}
_ => unreachable!(),
}
}
}
}
pub fn make_tail_continuation<F: LurkField>(store: &mut Store<F>, env: Ptr<F>, continuation: Ptr<F>) -> [Ptr<F>; 1] {
match continuation.tag() {
Tag::Cont(Tail) => {
return [continuation];
}
_ => {
todo_op;
return [tail_continuation];
}
}
}
pub fn extend_rec<F: LurkField>(store: &mut Store<F>, env: Ptr<F>, var: Ptr<F>, result: Ptr<F>) -> [Ptr<F>; 1] {
let [binding_or_env, rest] = safe_uncons(store, env);
let [var_or_binding, _val_or_more_bindings] = safe_uncons(store, binding_or_env);
todo_op;
match var_or_binding.tag() {
Tag::Expr(Sym) => {
let nil = store.intern_symbol(".lurk.nil".into());
let nil = nil.cast(Tag::Expr(Nil));
todo_op;
todo_op;
return [res];
}
Tag::Expr(Nil) => {
let nil = store.intern_symbol(".lurk.nil".into());
let nil = nil.cast(Tag::Expr(Nil));
todo_op;
todo_op;
return [res];
}
Tag::Expr(Cons) => {
todo_op;
todo_op;
return [res];
}
_ => unreachable!(),
}
}
pub fn args_num_type<F: LurkField>(store: &mut Store<F>, arg1: Ptr<F>, arg2: Ptr<F>) -> [Ptr<F>; 1] {
let nil = store.intern_symbol(".lurk.nil".into());
let nil = nil.cast(Tag::Expr(Nil));
match arg1.tag() {
Tag::Expr(Num) => {
match arg2.tag() {
Tag::Expr(Num) => {
let ret = Ptr::Atom(Tag::Expr(Num), F::ZERO);
return [ret];
}
Tag::Expr(U64) => {
let ret = Ptr::Atom(Tag::Expr(Num), F::ZERO);
return [ret];
}
_ => {
return [nil];
}
}
}
Tag::Expr(U64) => {
match arg2.tag() {
Tag::Expr(Num) => {
let ret = Ptr::Atom(Tag::Expr(Num), F::ZERO);
return [ret];
}
Tag::Expr(U64) => {
let ret = Ptr::Atom(Tag::Expr(U64), F::ZERO);
return [ret];
}
_ => {
return [nil];
}
}
}
_ => {
return [nil];
}
}
}
pub fn apply_cont<F: LurkField>(store: &mut Store<F>, result: Ptr<F>, env: Ptr<F>, cont: Ptr<F>, ctrl: Ptr<F>) -> [Ptr<F>; 4] {
let ret = Ptr::Atom(Tag::Ctrl(Return), F::ZERO);
let makethunk = Ptr::Atom(Tag::Ctrl(MakeThunk), F::ZERO);
let errctrl = Ptr::Atom(Tag::Ctrl(Error), F::ZERO);
let err = Ptr::Atom(Tag::Cont(Error), F::ZERO);
let nil = store.intern_symbol(".lurk.nil".into());
let nil = nil.cast(Tag::Expr(Nil));
let t = store.intern_symbol(".lurk.t".into());
let zero = Ptr::num(F::from_u128(0));
let size_u64 = Ptr::num(F::from_u128(18446744073709551616));
let empty_str = store.intern_string("");
match ctrl.tag() {
Tag::Ctrl(ApplyContinuation) => {
match cont.tag() {
Tag::Cont(Terminal) => {
return [result, env, cont, ret];
}
Tag::Cont(Error) => {
return [result, env, cont, ret];
}
Tag::Cont(Outermost) => {
let cont = Ptr::Atom(Tag::Cont(Terminal), F::ZERO);
return [result, env, cont, ret];
}
Tag::Cont(Emit) => {
todo_op;
return [result, env, cont, makethunk];
}
Tag::Cont(Call0) => {
todo_op;
match result.tag() {
Tag::Expr(Fun) => {
todo_op;
match &store.fetch_symbol(&arg).unwrap().fmt_to_string() {
".lurk.dummy" => {
match body.tag() {
Tag::Expr(Nil) => {
return [result, env, err, errctrl];
}
_ => {
let [body_form, end] = safe_uncons(store, body);
match end.tag() {
Tag::Expr(Nil) => {
let [cont] = make_tail_continuation(store, saved_env, continuation);
return [body_form, closed_env, cont, ret];
}
_ => {
return [result, env, err, errctrl];
}
}
}
}
}
_ => {
return [result, env, continuation, ret];
}
}
}
_ => {
return [result, env, err, errctrl];
}
}
}
Tag::Cont(Call) => {
match result.tag() {
Tag::Expr(Fun) => {
todo_op;
todo_op;
return [unevaled_arg, env, newer_cont, ret];
}
_ => {
return [result, env, err, errctrl];
}
}
}
Tag::Cont(Call2) => {
todo_op;
match function.tag() {
Tag::Expr(Fun) => {
todo_op;
match &store.fetch_symbol(&arg).unwrap().fmt_to_string() {
".lurk.dummy" => {
return [result, env, err, errctrl];
}
_ => {
match body.tag() {
Tag::Expr(Nil) => {
return [result, env, err, errctrl];
}
_ => {
todo_op;
match end.tag() {
Tag::Expr(Nil) => {
todo_op;
todo_op;
let [cont] = make_tail_continuation(store, saved_env, continuation);
return [body_form, newer_env, cont, ret];
}
_ => {
return [result, env, err, errctrl];
}
}
}
}
}
}
}
_ => {
return [result, env, err, errctrl];
}
}
}
Tag::Cont(Let) => {
todo_op;
todo_op;
todo_op;
let [cont] = make_tail_continuation(store, saved_env, cont);
return [body, extended_env, cont, ret];
}
Tag::Cont(LetRec) => {
todo_op;
let [extended_env] = extend_rec(store, env, var, result);
let [cont] = make_tail_continuation(store, saved_env, cont);
return [body, extended_env, cont, ret];
}
Tag::Cont(Unop) => {
todo_op;
match &store.fetch_symbol(&operator).unwrap().fmt_to_string() {
".lurk.car" => {
match result.tag() {
Tag::Expr(Nil) => {
return [nil, env, continuation, makethunk];
}
Tag::Expr(Cons) => {
todo_op;
return [car, env, continuation, makethunk];
}
Tag::Expr(Str) => {
if result == empty_str {
return [nil, env, continuation, makethunk];
} else {
todo_op;
return [car, env, continuation, makethunk];
}
}
_ => {
return [result, env, err, errctrl];
}
}
}
".lurk.cdr" => {
match result.tag() {
Tag::Expr(Nil) => {
return [nil, env, continuation, makethunk];
}
Tag::Expr(Cons) => {
todo_op;
return [cdr, env, continuation, makethunk];
}
Tag::Expr(Str) => {
if result == empty_str {
return [empty_str, env, continuation, makethunk];
} else {
todo_op;
return [cdr, env, continuation, makethunk];
}
}
_ => {
return [result, env, err, errctrl];
}
}
}
".lurk.atom" => {
match result.tag() {
Tag::Expr(Cons) => {
return [nil, env, continuation, makethunk];
}
_ => {
return [t, env, continuation, makethunk];
}
}
}
".lurk.emit" => {
todo_op;
todo_op;
return [result, env, emit, makethunk];
}
".lurk.open" => {
match result.tag() {
Tag::Expr(Num) => {
let result = result.cast(Tag::Expr(Comm));
todo_op;
return [payload, env, continuation, makethunk];
}
Tag::Expr(Comm) => {
todo_op;
return [payload, env, continuation, makethunk];
}
_ => {
return [result, env, err, errctrl];
}
}
}
".lurk.secret" => {
match result.tag() {
Tag::Expr(Num) => {
let result = result.cast(Tag::Expr(Comm));
todo_op;
return [secret, env, continuation, makethunk];
}
Tag::Expr(Comm) => {
todo_op;
return [secret, env, continuation, makethunk];
}
_ => {
return [result, env, err, errctrl];
}
}
}
".lurk.commit" => {
todo_op;
return [comm, env, continuation, makethunk];
}
".lurk.num" => {
match result.tag() {
Tag::Expr(Num) => {
let cast = result.cast(Tag::Expr(Num));
return [cast, env, continuation, makethunk];
}
Tag::Expr(Comm) => {
let cast = result.cast(Tag::Expr(Num));
return [cast, env, continuation, makethunk];
}
Tag::Expr(Char) => {
let cast = result.cast(Tag::Expr(Num));
return [cast, env, continuation, makethunk];
}
Tag::Expr(U64) => {
let cast = result.cast(Tag::Expr(Num));
return [cast, env, continuation, makethunk];
}
_ => {
return [result, env, err, errctrl];
}
}
}
".lurk.u64" => {
match result.tag() {
Tag::Expr(Num) => {
todo_op;
let cast = trunc.cast(Tag::Expr(U64));
return [cast, env, continuation, makethunk];
}
Tag::Expr(U64) => {
return [result, env, continuation, makethunk];
}
_ => {
return [result, env, err, errctrl];
}
}
}
".lurk.comm" => {
match result.tag() {
Tag::Expr(Num) => {
let cast = result.cast(Tag::Expr(Comm));
return [cast, env, continuation, makethunk];
}
Tag::Expr(Comm) => {
let cast = result.cast(Tag::Expr(Comm));
return [cast, env, continuation, makethunk];
}
_ => {
return [result, env, err, errctrl];
}
}
}
".lurk.char" => {
match result.tag() {
Tag::Expr(Num) => {
todo_op;
let cast = trunc.cast(Tag::Expr(Char));
return [cast, env, continuation, makethunk];
}
Tag::Expr(Char) => {
return [result, env, continuation, makethunk];
}
_ => {
return [result, env, err, errctrl];
}
}
}
".lurk.eval" => {
return [result, nil, continuation, ret];
}
_ => {
return [result, env, err, errctrl];
}
}
}
Tag::Cont(Binop) => {
todo_op;
let [arg2, rest] = safe_uncons(store, unevaled_args);
match &store.fetch_symbol(&operator).unwrap().fmt_to_string() {
".lurk.begin" => {
match rest.tag() {
Tag::Expr(Nil) => {
return [arg2, saved_env, continuation, ret];
}
_ => {
todo_op;
return [begin_again, saved_env, continuation, ctrl];
}
}
}
_ => {
match rest.tag() {
Tag::Expr(Nil) => {
todo_op;
return [arg2, saved_env, cont, ret];
}
_ => {
return [result, env, err, errctrl];
}
}
}
}
}
Tag::Cont(Binop2) => {
todo_op;
let [args_num_type] = args_num_type(store, evaled_arg, result);
match &store.fetch_symbol(&operator).unwrap().fmt_to_string() {
".lurk.eval" => {
return [evaled_arg, result, continuation, ret];
}
".lurk.cons" => {
todo_op;
return [val, env, continuation, makethunk];
}
".lurk.strcons" => {
match evaled_arg.tag() {
Tag::Expr(Char) => {
match result.tag() {
Tag::Expr(Str) => {
todo_op;
return [val, env, continuation, makethunk];
}
_ => {
return [result, env, err, errctrl];
}
}
}
_ => {
return [result, env, err, errctrl];
}
}
}
".lurk.hide" => {
match evaled_arg.tag() {
Tag::Expr(Num) => {
todo_op;
return [hidden, env, continuation, makethunk];
}
_ => {
return [result, env, err, errctrl];
}
}
}
".lurk.eq" => {
todo_op;
todo_op;
todo_op;
if eq == zero {
return [nil, env, continuation, makethunk];
} else {
return [t, env, continuation, makethunk];
}
}
".lurk.+" => {
match args_num_type.tag() {
Tag::Expr(Nil) => {
return [result, env, err, errctrl];
}
Tag::Expr(Num) => {
todo_op;
return [val, env, continuation, makethunk];
}
Tag::Expr(U64) => {
todo_op;
todo_op;
if not_overflow == zero {
todo_op;
let val = val.cast(Tag::Expr(U64));
return [val, env, continuation, makethunk];
} else {
let val = val.cast(Tag::Expr(U64));
return [val, env, continuation, makethunk];
}
}
_ => unreachable!(),
}
}
".lurk.-" => {
match args_num_type.tag() {
Tag::Expr(Nil) => {
return [result, env, err, errctrl];
}
Tag::Expr(Num) => {
todo_op;
return [val, env, continuation, makethunk];
}
Tag::Expr(U64) => {
todo_op;
todo_op;
if is_neg == zero {
let val = val.cast(Tag::Expr(U64));
return [val, env, continuation, makethunk];
} else {
todo_op;
let val = val.cast(Tag::Expr(U64));
return [val, env, continuation, makethunk];
}
}
_ => unreachable!(),
}
}
".lurk.*" => {
match args_num_type.tag() {
Tag::Expr(Nil) => {
return [result, env, err, errctrl];
}
Tag::Expr(Num) => {
todo_op;
return [val, env, continuation, makethunk];
}
Tag::Expr(U64) => {
todo_op;
todo_op;
let cast = trunc.cast(Tag::Expr(U64));
return [cast, env, continuation, makethunk];
}
_ => unreachable!(),
}
}
".lurk./" => {
todo_op;
if is_z == zero {
match args_num_type.tag() {
Tag::Expr(Nil) => {
return [result, env, err, errctrl];
}
Tag::Expr(Num) => {
todo_op;
return [val, env, continuation, makethunk];
}
Tag::Expr(U64) => {
todo_op;
let div = div.cast(Tag::Expr(U64));
return [div, env, continuation, makethunk];
}
_ => unreachable!(),
}
} else {
return [result, env, err, errctrl];
}
}
".lurk.%" => {
todo_op;
if is_z == zero {
match args_num_type.tag() {
Tag::Expr(U64) => {
todo_op;
let rem = rem.cast(Tag::Expr(U64));
return [rem, env, continuation, makethunk];
}
_ => {
return [result, env, err, errctrl];
}
}
} else {
return [result, env, err, errctrl];
}
}
".lurk.=" => {
match args_num_type.tag() {
Tag::Expr(Nil) => {
return [result, env, err, errctrl];
}
_ => {
todo_op;
if eq == zero {
return [nil, env, continuation, makethunk];
} else {
return [t, env, continuation, makethunk];
}
}
}
}
".lurk.<" => {
todo_op;
if val == zero {
return [nil, env, continuation, makethunk];
} else {
return [t, env, continuation, makethunk];
}
}
".lurk.>" => {
todo_op;
if val == zero {
return [nil, env, continuation, makethunk];
} else {
return [t, env, continuation, makethunk];
}
}
".lurk.<=" => {
todo_op;
if val == zero {
return [t, env, continuation, makethunk];
} else {
return [nil, env, continuation, makethunk];
}
}
".lurk.>=" => {
todo_op;
if val == zero {
return [t, env, continuation, makethunk];
} else {
return [nil, env, continuation, makethunk];
}
}
_ => {
return [result, env, err, errctrl];
}
}
}
Tag::Cont(If) => {
todo_op;
let [arg1, more] = safe_uncons(store, unevaled_args);
let [arg2, end] = safe_uncons(store, more);
match end.tag() {
Tag::Expr(Nil) => {
match result.tag() {
Tag::Expr(Nil) => {
return [arg2, env, continuation, ret];
}
_ => {
return [arg1, env, continuation, ret];
}
}
}
_ => {
return [arg1, env, err, errctrl];
}
}
}
Tag::Cont(Lookup) => {
todo_op;
return [result, saved_env, continuation, makethunk];
}
Tag::Cont(Tail) => {
todo_op;
return [result, saved_env, continuation, makethunk];
}
_ => unreachable!(),
}
}
_ => {
return [result, env, cont, ctrl];
}
}
}
pub fn make_thunk<F: LurkField>(store: &mut Store<F>, expr: Ptr<F>, env: Ptr<F>, cont: Ptr<F>, ctrl: Ptr<F>) -> [Ptr<F>; 4] {
let ret = Ptr::Atom(Tag::Ctrl(Return), F::ZERO);
match ctrl.tag() {
Tag::Ctrl(MakeThunk) => {
match cont.tag() {
Tag::Cont(Tail) => {
todo_op;
todo_op;
let cont = Ptr::Atom(Tag::Cont(Dummy), F::ZERO);
return [thunk, saved_env, cont, ret];
}
Tag::Cont(Outermost) => {
let cont = Ptr::Atom(Tag::Cont(Terminal), F::ZERO);
return [expr, env, cont, ret];
}
_ => {
todo_op;
let cont = Ptr::Atom(Tag::Cont(Dummy), F::ZERO);
return [thunk, env, cont, ret];
}
}
}
_ => {
return [expr, env, cont, ctrl];
}
}
}
pub fn step<F: LurkField>(store: &mut Store<F>, expr: Ptr<F>, env: Ptr<F>, cont: Ptr<F>) -> [Ptr<F>; 3] {
let [expr, env, cont, ctrl] = reduce(store, expr, env, cont);
let [expr, env, cont, ctrl] = apply_cont(store, expr, env, cont, ctrl);
let [expr, env, cont, _ctrl] = make_thunk(store, expr, env, cont, ctrl);
return [expr, env, cont];
}