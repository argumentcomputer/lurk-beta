use std::collections::HashMap;

use crate::field::{FWrap, LurkField};

use super::{lurk_symbol::LurkSymbol, pointers::Ptr, store::Store, tag::Tag, Witness, LEM, LEMOP};

impl<F: LurkField> LEM<F> {
    pub fn run(&self, input: [Ptr<F>; 3], store: &mut Store<F>) -> Result<Witness<F>, String> {
        // key/val pairs on these maps should never be overwritten
        let mut ptrs = HashMap::default();
        let mut vars = HashMap::default();
        ptrs.insert(self.input[0].clone(), input[0]);
        if ptrs.insert(self.input[1].clone(), input[1]).is_some() {
            return Err(format!("{} already defined", self.input[1]));
        }
        if ptrs.insert(self.input[2].clone(), input[2]).is_some() {
            return Err(format!("{} already defined", self.input[2]));
        }
        let mut output = None;
        let mut stack = vec![&self.lem_op];
        while let Some(op) = stack.pop() {
            match op {
                LEMOP::MkNull(tgt, tag) => {
                    let tgt_ptr = Ptr::null(*tag);
                    if ptrs.insert(tgt.name().clone(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Hash2Ptrs(tgt, tag, src) => {
                    let src_ptr1 = src[0].get_ptr(&ptrs)?;
                    let src_ptr2 = src[1].get_ptr(&ptrs)?;
                    let tgt_ptr = store.index_2_ptrs(*tag, src_ptr1, src_ptr2);
                    if ptrs.insert(tgt.name().clone(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Hash3Ptrs(tgt, tag, src) => {
                    let src_ptr1 = src[0].get_ptr(&ptrs)?;
                    let src_ptr2 = src[1].get_ptr(&ptrs)?;
                    let src_ptr3 = src[2].get_ptr(&ptrs)?;
                    let tgt_ptr = store.index_3_ptrs(*tag, src_ptr1, src_ptr2, src_ptr3);
                    if ptrs.insert(tgt.name().clone(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Hash4Ptrs(tgt, tag, src) => {
                    let src_ptr1 = src[0].get_ptr(&ptrs)?;
                    let src_ptr2 = src[1].get_ptr(&ptrs)?;
                    let src_ptr3 = src[2].get_ptr(&ptrs)?;
                    let src_ptr4 = src[3].get_ptr(&ptrs)?;
                    let tgt_ptr = store.index_4_ptrs(*tag, src_ptr1, src_ptr2, src_ptr3, src_ptr4);
                    if ptrs.insert(tgt.name().clone(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Unhash2Ptrs(tgts, src) => {
                    let src_ptr = src.get_ptr(&ptrs)?;
                    let Some(idx) = src_ptr.get_index2() else {
                        return Err(format!(
                            "{} isn't a Tree2 pointer",
                            src.name()
                        ));
                    };
                    let Some((a, b)) = store.fetch_2_ptrs(idx) else {
                        return Err(format!("Couldn't fetch {}'s children", src.name()))
                    };
                    if ptrs.insert(tgts[0].name().clone(), *a).is_some() {
                        return Err(format!("{} already defined", tgts[0].name()));
                    }
                    if ptrs.insert(tgts[1].name().clone(), *b).is_some() {
                        return Err(format!("{} already defined", tgts[1].name()));
                    }
                }
                LEMOP::Unhash3Ptrs(tgts, src) => {
                    let src_ptr = src.get_ptr(&ptrs)?;
                    let Some(idx) = src_ptr.get_index3() else {
                        return Err(format!(
                            "{} isn't a Tree3 pointer",
                            src.name()
                        ));
                    };
                    let Some((a, b, c)) = store.fetch_3_ptrs(idx) else {
                        return Err(format!("Couldn't fetch {}'s children", src.name()))
                    };
                    if ptrs.insert(tgts[0].name().clone(), *a).is_some() {
                        return Err(format!("{} already defined", tgts[0].name()));
                    }
                    if ptrs.insert(tgts[1].name().clone(), *b).is_some() {
                        return Err(format!("{} already defined", tgts[1].name()));
                    }
                    if ptrs.insert(tgts[2].name().clone(), *c).is_some() {
                        return Err(format!("{} already defined", tgts[2].name()));
                    }
                }
                LEMOP::Unhash4Ptrs(tgts, src) => {
                    let src_ptr = src.get_ptr(&ptrs)?;
                    let Some(idx) = src_ptr.get_index4() else {
                        return Err(format!(
                            "{} isn't a Tree4 pointer",
                            src.name()
                        ));
                    };
                    let Some((a, b, c, d)) = store.fetch_4_ptrs(idx) else {
                        return Err(format!("Couldn't fetch {}'s children", src.name()))
                    };
                    if ptrs.insert(tgts[0].name().clone(), *a).is_some() {
                        return Err(format!("{} already defined", tgts[0].name()));
                    }
                    if ptrs.insert(tgts[1].name().clone(), *b).is_some() {
                        return Err(format!("{} already defined", tgts[1].name()));
                    }
                    if ptrs.insert(tgts[2].name().clone(), *c).is_some() {
                        return Err(format!("{} already defined", tgts[2].name()));
                    }
                    if ptrs.insert(tgts[3].name().clone(), *d).is_some() {
                        return Err(format!("{} already defined", tgts[3].name()));
                    }
                }
                LEMOP::Hide(tgt, secret, src) => {
                    let src_ptr = src.get_ptr(&ptrs)?;
                    let aqua_ptr = store.hydrate_ptr(&src_ptr)?;
                    let hash =
                        store
                            .poseidon_cache
                            .hash3(&[*secret, aqua_ptr.tag.field(), aqua_ptr.val]);
                    let tgt_ptr = Ptr::comm(hash);
                    store.comms.insert(FWrap::<F>(hash), (*secret, src_ptr));
                    if ptrs.insert(tgt.name().clone(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Open(tgt_secret, tgt_ptr, hash) => {
                    let Some((secret, ptr)) = store.comms.get(&FWrap::<F>(*hash)) else {
                        return Err(format!("No committed data for hash {}", hash.hex_digits()))
                    };
                    if ptrs.insert(tgt_ptr.name().clone(), *ptr).is_some() {
                        return Err(format!("{} already defined", tgt_ptr.name()));
                    }
                    if vars.insert(tgt_secret.name().clone(), *secret).is_some() {
                        return Err(format!("{} already defined", tgt_secret.name()));
                    }
                }
                LEMOP::MatchTag(ptr, cases) => {
                    let ptr = ptr.get_ptr(&ptrs)?;
                    let ptr_tag = ptr.tag();
                    match cases.get(ptr_tag) {
                        Some(op) => stack.push(op),
                        None => return Err(format!("No match for tag {:?}", ptr_tag)),
                    }
                }
                LEMOP::MatchLurkSymbolVal(ptr, cases) => {
                    let Ptr::Leaf(Tag::LurkSymbol, f) = ptr.get_ptr(&ptrs)? else {
                        return Err(format!("{} not defined as a pointer to a Lurk symbol", ptr.name()))
                    };
                    let Some(lurk_symbol) = LurkSymbol::from_field(&f) else {
                        return Err(format!("{} contains invalid value for a Lurk symbol", ptr.name()))
                    };
                    match cases.get(&lurk_symbol) {
                        Some(op) => stack.push(op),
                        None => {
                            return Err(format!("No match for field element {}", f.hex_digits()))
                        }
                    }
                }
                LEMOP::Seq(ops) => stack.extend(ops.iter().rev()),
                LEMOP::SetReturn(o) => {
                    if output.is_some() {
                        return Err("Tried to return twice".to_string());
                    }
                    output = Some([
                        o[0].get_ptr(&ptrs)?,
                        o[1].get_ptr(&ptrs)?,
                        o[2].get_ptr(&ptrs)?,
                    ]);
                }
            }
        }
        let Some(output) = output else {
            return Err("Output not defined".to_string());
        };
        Ok(Witness {
            input,
            output,
            ptrs,
            vars,
        })
    }

    pub fn eval(&self, expr: Ptr<F>, store: &mut Store<F>) -> Result<Vec<Witness<F>>, String> {
        let mut expr = expr;
        let mut env = Ptr::lurk_sym(&LurkSymbol::Nil);
        let mut cont = Ptr::null(Tag::Outermost);
        let mut witnesses = vec![];
        let terminal = Ptr::null(Tag::Terminal);
        loop {
            let w = self.run([expr, env, cont], store)?;
            witnesses.push(w.clone());
            if w.output[2] == terminal {
                break;
            } else {
                [expr, env, cont] = w.output;
            }
        }
        Ok(witnesses)
    }
}
