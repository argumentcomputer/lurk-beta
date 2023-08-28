use std::collections::HashSet;

use super::{Block, Ctrl, Func, Lit, Op, Var};

fn fmt_vars(vs: &[Var]) -> String {
    vs.iter()
        .map(|v| v.get_original())
        .collect::<Vec<_>>()
        .join(", ")
}

impl Op {
    pub fn compile_acc(&self, name: &str, visited: &mut HashSet<String>, _acc: &mut String) {
        if !visited.contains(name) {
            visited.insert(name.to_string());
        }
    }

    pub fn compile(&self, visited: &mut HashSet<String>, acc: &mut String) -> String {
        match self {
            Op::Call(outp, func, inp) => {
                func.compile(visited, acc);
                format!(
                    "let [{}] = {}(store, {})",
                    fmt_vars(outp),
                    func.name,
                    fmt_vars(inp)
                )
            }
            Op::Null(v, t) => format!(
                "let {} = Ptr::Atom(Tag::{:?}, F::ZERO)",
                v.get_original(),
                t
            ),
            Op::Lit(v, l) => match l {
                Lit::Num(n) => format!("let {} = Ptr::num(F::from_u128({n}))", v.get_original()),
                Lit::String(s) => {
                    format!("let {} = store.intern_string(\"{s}\")", v.get_original())
                }
                Lit::Symbol(s) => format!(
                    "let {} = store.intern_symbol(\"{s}\".into())",
                    v.get_original()
                ),
            },
            Op::Cast(v, t, a) => format!(
                "let {} = {}.cast(Tag::{:?})",
                v.get_original(),
                a.get_original(),
                t
            ),
            _ => "todo_op".into(),
        }
    }
}

impl Ctrl {
    pub fn compile(&self, visited: &mut HashSet<String>, acc: &mut String) -> String {
        match self {
            Ctrl::MatchTag(v, cases, def) => {
                let mut code = format!("match {}.tag() {{", v.get_original());
                for (t, c) in cases {
                    let mut inner_code = format!("\nTag::{:?} => {{\n", t);
                    inner_code.push_str(&c.compile(visited, acc));
                    inner_code.push_str("\n}");
                    code.push_str(&inner_code);
                }
                if let Some(def) = def {
                    let mut inner_code = "\n_ => {\n".to_string();
                    inner_code.push_str(&def.compile(visited, acc));
                    inner_code.push_str("\n}");
                    code.push_str(&inner_code);
                } else {
                    code.push_str("\n_ => unreachable!(),")
                }
                code.push_str("\n}");
                code
            }
            Ctrl::MatchSymbol(v, cases, def) => {
                let mut code = format!(
                    "match &store.fetch_symbol(&{}).unwrap().fmt_to_string() {{",
                    v.get_original()
                );
                for (s, c) in cases {
                    let mut inner_code = format!("\n\"{s}\" => {{\n");
                    inner_code.push_str(&c.compile(visited, acc));
                    inner_code.push_str("\n}");
                    code.push_str(&inner_code);
                }
                if let Some(def) = def {
                    let mut inner_code = "\n_ => {\n".to_string();
                    inner_code.push_str(&def.compile(visited, acc));
                    inner_code.push_str("\n}");
                    code.push_str(&inner_code);
                } else {
                    code.push_str("\n_ => unreachable!(),")
                }
                code.push_str("\n}");
                code
            }
            Ctrl::IfEq(a, b, t, f) => {
                let t_code = t.compile(visited, acc);
                let f_code = f.compile(visited, acc);
                format!(
                    "if {} == {} {{\n{}\n}} else {{\n{}\n}}",
                    a.get_original(),
                    b.get_original(),
                    &t_code,
                    &f_code
                )
            }
            Ctrl::Return(vs) => format!("return [{}];", &fmt_vars(vs)),
        }
    }
}

impl Block {
    pub fn compile(&self, visited: &mut HashSet<String>, acc: &mut String) -> String {
        let mut code = String::new();
        self.ops
            .iter()
            .for_each(|op| code.push_str(&format!("{};\n", op.compile(visited, acc))));
        code.push_str(&self.ctrl.compile(visited, acc));
        code
    }
}

impl Func {
    pub fn compile(&self, visited: &mut HashSet<String>, acc: &mut String) {
        if !visited.contains(&self.name) {
            let body_code = self.body.compile(visited, acc);
            let args_code = self
                .input_params
                .iter()
                .map(|v| format!("{}: Ptr<F>", v.get_original()))
                .collect::<Vec<_>>()
                .join(", ");
            let ret_code = format!("[Ptr<F>; {}]", self.output_size);
            let mut code = format!(
                "\npub fn {}<F: LurkField>(store: &mut Store<F>, {}) -> {} {{",
                &self.name, &args_code, &ret_code,
            );
            code.push('\n');
            code.push_str(&body_code);
            code.push_str("\n}");
            acc.push_str(&code);
            visited.insert(self.name.clone());
        }
    }

    pub fn compile_start(&self) -> String {
        let visited = &mut HashSet::default();
        let mut acc = String::new();
        self.compile(visited, &mut acc);
        acc
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::lem::eval::eval_step;

    #[test]
    fn print() {
        let path = Path::new("src/lem/test.rs");
        std::fs::write(path, eval_step().compile_start()).unwrap();
    }
}
