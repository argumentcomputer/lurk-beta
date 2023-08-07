use anyhow::{bail, Result};
use std::hash::Hash;

use indexmap::{IndexMap, map::Iter};

use super::{Op, Var};

struct BiIndexMap<X, Y> {
    l2r: IndexMap<X, Y>,
    r2l: IndexMap<Y, X>,
}

impl<X: Clone + PartialEq + Eq + Hash, Y: Clone + PartialEq + Eq + Hash> BiIndexMap<X, Y> {
    fn insert(&mut self, x: X, y: Y) {
        self.l2r.insert(x.clone(), y.clone());
        self.r2l.insert(y, x);
    }
    fn get_by_l(&self, x: &X) -> Option<&Y> {
        self.l2r.get(x)
    }
    fn get_by_r(&self, y: &Y) -> Option<&X> {
        self.r2l.get(y)
    }
    fn iter(&self) -> Iter<'_, X, Y> {
        self.l2r.iter()
    }
    fn is_empty(&self) -> bool {
        self.l2r.is_empty()
    }
}

impl<X, Y> Default for BiIndexMap<X, Y> {
    fn default() -> Self {
        Self { l2r: Default::default(), r2l: Default::default() }
    }
}

#[derive(Default)]
struct Context {
    rewrites: IndexMap<Var, Var>,
    hash2: BiIndexMap<[Var; 2], Var>,
    hash3: BiIndexMap<[Var; 3], Var>,
    hash4: BiIndexMap<[Var; 4], Var>,
}

impl Context {
    fn fmt_to_string(&self) -> String {
        let mut res = String::new();
        if !self.rewrites.is_empty() {
            res.push_str("Rewrites:\n");
            for (a, b) in &self.rewrites {
                res.push_str(&format!("  {a} → {b}\n"));
            }
        }
        if !self.hash2.is_empty() {
            res.push_str("Hash2:\n");
            for ([p1, p2], i) in self.hash2.iter() {
                res.push_str(&format!("  ({p1}, {p2}) ↔ {i}\n"));
            }
        }
        if !self.hash3.is_empty() {
            res.push_str("Hash3:\n");
            for ([p1, p2, p3], i) in self.hash3.iter() {
                res.push_str(&format!("  ({p1}, {p2}, {p3}) ↔ {i}\n"));
            }
        }
        if !self.hash4.is_empty() {
            res.push_str("Hash4:\n");
            for ([p1, p2, p3, p4], i) in self.hash4.iter() {
                res.push_str(&format!("  ({p1}, {p2}, {p3}, {p4}) ↔ {i}\n"));
            }
        }
        res
    }
}

impl std::fmt::Display for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.fmt_to_string())
    }
}

fn rewrite(var: &Var, ctx: &Context) -> Var {
    match ctx.rewrites.get(var) {
        None => var.to_owned(),
        Some(var) => var.to_owned(),
    }
}

fn process_op(op: &Op, ctx: &mut Context) -> Result<Option<Op>> {
    match op {
        Op::Hash2(img, tag, preimg) => {
            let preimg = [rewrite(&preimg[0], &ctx), rewrite(&preimg[1], &ctx)];
            match ctx.hash2.get_by_l(&preimg) {
                None => {
                    ctx.hash2.insert(preimg.clone(), img.clone());
                    Ok(Some(Op::Hash2(img.clone(), *tag, preimg)))
                }
                Some(img_eq) => {
                    ctx.rewrites.insert(img.clone(), img_eq.clone());
                    Ok(None)
                }
            }
        }
        Op::Unhash2(preimg, img) => {
            let img = rewrite(img, &ctx);
            if ctx.hash3.get_by_r(&img).is_some() || ctx.hash4.get_by_r(&img).is_some() {
                bail!("Indalid Unhash2")
            }
            match ctx.hash2.get_by_r(&img) {
                None => {
                    ctx.hash2.insert(preimg.clone(), img.clone());
                    Ok(Some(Op::Unhash2(preimg.clone(), img)))
                }
                Some(preimg_eq) => {
                    for (var, var_eq) in preimg.iter().zip(preimg_eq) {
                        ctx.rewrites.insert(var.clone(), var_eq.clone());
                    }
                    Ok(None)
                }
            }
        }
        _ => todo!(),
    }
}

fn extract_ops(ops: Vec<Option<Op>>) -> Vec<Op> {
    let mut res = vec![];
    for op in ops {
        match op {
            None => (),
            Some(op) => res.push(op),
        }
    }
    res
}

fn process_ops(ops: &[Op], ctx: &mut Context) -> Result<Vec<Op>> {
    let mut new_ops = vec![];
    for op in ops {
        new_ops.push(process_op(op, ctx)?);
    }
    Ok(extract_ops(new_ops))
}

#[test]
fn test() {
    use crate::op;
    let ops = [
        op!(let x: Expr::Cons = hash2(a, b)),
        op!(let xx: Expr::Cons = hash2(a, b)),
        op!(let (m, n) = unhash2(xx)),
        op!(let z: Expr::Cons = hash2(xx, x)),
        op!(let (x_, x__) = unhash2(z)),
        op!(let (aa, bb) = unhash2(x_)),
        op!(let (aaa, bbb) = unhash2(x__)),
    ];
    let ctx = &mut Context::default();
    let ops = process_ops(&ops, ctx).unwrap();
    println!("{:?}\n", ops);
    println!("{ctx}");
    assert!(false)
}
