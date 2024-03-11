use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;
use tracing::info;

use bellpepper::gadgets::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};

use anyhow::{anyhow, bail, Result};

use crate::{Foil, Func, Id, Label, MetaData, MetaMapper, Relation, Schema, Var, Vert};
use lurk::field::LurkField;
use lurk::lem::pointers::Ptr;
use lurk::lem::store::Store;
use lurk::lem::tag::Tag;
use lurk::sym;
use lurk::tag::ExprTag;
use lurk::Symbol;

impl From<Symbol> for Func<CoilMeta> {
    fn from(sym: Symbol) -> Self {
        Self::from(&sym)
    }
}

impl From<&Symbol> for Func<CoilMeta> {
    fn from(sym: &Symbol) -> Self {
        Self::new_with_metadata(sym.to_string(), CoilMeta::from(sym.clone()))
    }
}

impl From<Symbol> for Var {
    fn from(sym: Symbol) -> Self {
        Self::from(&sym)
    }
}

impl From<&Symbol> for Var {
    fn from(sym: &Symbol) -> Self {
        Self::new(sym.to_string())
    }
}

impl From<Symbol> for Label {
    fn from(sym: Symbol) -> Self {
        Self::from(&sym)
    }
}

impl From<&Symbol> for Label {
    fn from(sym: &Symbol) -> Self {
        Self::from(Var::from(sym))
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct CoilMeta {
    name: Symbol,
}

impl From<Symbol> for CoilMeta {
    fn from(name: Symbol) -> Self {
        Self { name }
    }
}

impl Default for CoilMeta {
    fn default() -> Self {
        let name = sym!("coil", "var");

        Self { name }
    }
}

impl MetaData for CoilMeta {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Context {
    env: Ptr,
}

/// Look up `var` in `env`, where `env` is a list of bindings from `Symbol` to `U64` representing bindings of variables to vertices
/// by id.
fn lookup_vertex_id<F: LurkField>(store: &Store<F>, env: &Ptr, var: &Ptr) -> Result<Option<Id>> {
    let Some([bound_var, id, rest_env]) = store.pop_binding(env) else {
        return Ok(None);
    };

    if *var == bound_var {
        match store.fetch_num(&id) {
            Some(f) => Ok(f.to_u64().map(|u| {
                let n = u as Id;
                info!("found {n}");
                n
            })),
            _ => {
                bail!("binding Id could not be fetched");
            }
        }
    } else {
        lookup_vertex_id(store, &rest_env, var)
    }
}

impl Context {
    fn new<F: LurkField>(store: &Store<F>) -> Self {
        Self {
            env: store.intern_empty_env(),
        }
    }

    fn lookup<F: LurkField>(&self, store: &Store<F>, var: &Ptr) -> Result<Option<Id>> {
        info!(
            "looking up {} in env: {}",
            var.fmt_to_string_simple(store),
            self.env.fmt_to_string_simple(store)
        );
        lookup_vertex_id(store, &self.env, var)
    }

    fn push_binding<F: LurkField>(&mut self, store: &Store<F>, var: Ptr, id: Id) {
        let num = store.num((id as u64).into());

        self.env = store.push_binding(var, num, self.env);
    }

    fn pop_binding<F: LurkField>(&mut self, store: &Store<F>) -> Result<Id> {
        let [_var, id, rest_env] = store
            .pop_binding(&self.env)
            .ok_or(anyhow!("failed to pop binding"))?;
        self.env = rest_env;

        Ok(match store.fetch_num(&id) {
            Some(f) => f
                .to_u64()
                .map(|u| u as Id)
                .ok_or(anyhow!("binding Id could not be fetched"))?,
            _ => {
                bail!("binding Id could not be fetched");
            }
        })
    }
}

pub trait Syntax<F: LurkField> {
    fn expand(
        &self,
        foil: &mut Foil<F, CoilMeta>,
        store: &Store<F>,
        head: &Ptr,
        rest: &[Ptr],
    ) -> Result<Vec<Ptr>>
    where
        Self: Sized;
}

#[derive(Clone, Debug)]
pub struct CoilDef<F: LurkField, R: Relation<F>, S: Syntax<F>> {
    relations: HashMap<Symbol, R>,
    syntax: HashMap<Symbol, S>,
    constructors: HashMap<Symbol, Vec<Symbol>>,
    equivalences: HashSet<Symbol>,
    _p: PhantomData<F>,
}

pub struct AsSyntax<'a, T>(&'a T);

pub struct Let {}

impl<F: LurkField> Syntax<F> for Let {
    fn expand(
        &self,
        _foil: &mut Foil<F, CoilMeta>,
        store: &Store<F>,
        _head: &Ptr,
        rest: &[Ptr],
    ) -> Result<Vec<Ptr>> {
        let bind = store.intern_symbol(&sym!("coil", "bind"));
        let pop_binding = store.intern_symbol(&sym!("coil", "pop-binding"));

        if rest.is_empty() {
            bail!("Let bindings missing");
        }

        let bindings = store.fetch_proper_list(&rest[0]).unwrap();

        let mut result = Vec::with_capacity((2 * bindings.len()) + rest.len() - 1);

        result.extend(bindings.iter().map(|binding| {
            let b = store.fetch_proper_list(binding).unwrap();

            assert_eq!(2, b.len());
            // let var = b[0];
            // let val_form = b[1];

            // This is also store.cons(bind, binding).
            store.cons(bind, *binding)
            //store.list(&[bind, var, val_form])
        }));

        result.extend(&rest[1..]);

        let pop_binding_form = store.list([pop_binding]);
        result.extend(bindings.iter().map(|_| pop_binding_form));

        Ok(result)
    }
}

#[derive(Default, Debug)]
struct BindRel {}

#[derive(Default, Debug)]
struct VarRel {}

impl<F: LurkField> Relation<F> for BindRel {
    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        _cs: &mut CS,
        _allocated_head: AllocatedNum<F>,
        _successors: Vec<AllocatedNum<F>>,
    ) -> Result<(), SynthesisError> {
        // TODO: Actually implement constraints enforcing equality of the successors. Ideally, there would also exist a
        // mechanism such that this could be implemented without allocating the head -- since the head is not required
        // for this. Similarly, we should eventually allow for 'head' values to sometimes be unallocated
        // linear-combinations. That is an optimization that can come later, when we focus on improving the generated
        // R1CS based on the computation finally assembled.
        Ok(())
    }
}
impl<F: LurkField> Relation<F> for VarRel {
    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        _cs: &mut CS,
        _allocated_head: AllocatedNum<F>,
        successors: Vec<AllocatedNum<F>>,
    ) -> Result<(), SynthesisError> {
        assert!(successors.is_empty());
        Ok(())
    }
}

pub enum CoilSyntax {
    Let(Let),
}

impl<F: LurkField> Syntax<F> for CoilSyntax {
    fn expand(
        &self,
        foil: &mut Foil<F, CoilMeta>,
        store: &Store<F>,
        head: &Ptr,
        rest: &[Ptr],
    ) -> Result<Vec<Ptr>> {
        match self {
            Self::Let(x) => x.expand(foil, store, head, rest),
        }
    }
}

impl<F: LurkField, R: Relation<F>, S: Syntax<F>> Default for CoilDef<F, R, S> {
    fn default() -> Self {
        Self {
            relations: Default::default(),
            syntax: Default::default(),
            constructors: Default::default(),
            equivalences: Default::default(),
            _p: Default::default(),
        }
    }
}

impl<F: LurkField, R: Relation<F>> CoilDef<F, R, CoilSyntax> {
    fn new_std() -> Self {
        let mut def = Self::default();

        let let_sym = sym!("lurk", "let");
        let bind = sym!("coil", "bind");
        let _var = sym!("coil", "var");

        def.register_equivalence(bind);
        def.register_syntax(let_sym, CoilSyntax::Let(Let {}));

        def
    }
}

impl<F: LurkField, R: Relation<F>, S: Syntax<F>> CoilDef<F, R, S> {
    fn register_relation(&mut self, sym: Symbol, rel: R) {
        self.relations.insert(sym, rel);
    }
    fn register_syntax(&mut self, sym: Symbol, syn: S) {
        self.syntax.insert(sym, syn);
    }
    fn register_constructor(&mut self, constructor: Symbol, projectors: Vec<Symbol>) {
        self.constructors.insert(constructor, projectors);
    }
    fn register_equivalence(&mut self, equivalence: Symbol) {
        self.equivalences.insert(equivalence);
    }
    fn symbol_func(&self, sym: Symbol) -> Func<CoilMeta> {
        if let Some(projectors) = self.constructors.get(&sym) {
            Func::constructor(
                sym.to_string(),
                projectors.iter().map(Func::from).collect(),
                CoilMeta::from(sym),
            )
        } else {
            Func::from(sym)
        }
    }

    fn schema(&self) -> Schema<CoilMeta> {
        let mut equivalences: Vec<Func<CoilMeta>> = self
            .equivalences
            .iter()
            .map(|sym| self.symbol_func(sym.clone()))
            .collect();

        equivalences.sort();

        let mut constructors: Vec<Func<CoilMeta>> = self
            .constructors
            .keys()
            .map(|sym| self.symbol_func(sym.clone()))
            .collect();
        constructors.sort();

        Schema {
            constructors,
            equivalences,
        }
    }
}

impl<F: LurkField, R: Relation<F>, S: Syntax<F>> MetaMapper<CoilMeta, R> for CoilDef<F, R, S> {
    fn find(&self, meta: &CoilMeta) -> Option<&R> {
        self.relations.get(&meta.name)
    }
}

impl<'a, F: LurkField, R: Relation<F>, S: Syntax<F>> MetaMapper<CoilMeta, S>
    for AsSyntax<'a, CoilDef<F, R, S>>
{
    fn find(&self, meta: &CoilMeta) -> Option<&S> {
        self.0.syntax.get(&meta.name)
    }
}

impl<F: LurkField, R: Relation<F>, S: Syntax<F>> CoilDef<F, R, S> {
    fn add_to_foil(
        &self,
        foil: &mut Foil<F, CoilMeta>,
        store: &Store<F>,
        context: &mut Context,
        expr: &Ptr,
    ) -> Result<Option<Vert>> {
        match expr.tag() {
            Tag::Expr(ExprTag::Cons) => {
                info!("adding sexp: {}", expr.fmt_to_string_simple(store));

                let list = store
                    .fetch_proper_list(expr)
                    .expect("sexps must be proper lists");
                let head = list.first().ok_or(anyhow!("missing head"))?;
                let sym = store.fetch_sym(head).ok_or(anyhow!("sym not in store"))?;
                let rest = &list[1..];
                let meta = CoilMeta::from(sym.clone());

                if let Some(syntax) = AsSyntax::<CoilDef<F, R, S>>(self).find(&meta) {
                    let expanded = syntax.expand(foil, store, head, rest)?;

                    let mut last = None;
                    for (i, x) in expanded.iter().enumerate() {
                        info!(
                            "expanded ({} of {}): {}",
                            i + 1,
                            expanded.len(),
                            x.fmt_to_string_simple(store)
                        );

                        if let Some(vert) = self.add_to_foil(foil, store, context, x)? {
                            last = Some(vert);
                        }
                    }
                    info!("completed expansion");
                    Ok(last)
                } else {
                    if sym == sym!("coil", "pop-binding") {
                        return self.handle_pop_binding(store, context, rest);
                    }

                    // TODO: don't actually create these literal symbols here.
                    let successor_verts = if sym == sym!("coil", "bind") {
                        let var = store
                            .fetch_sym(&rest[0])
                            .ok_or(anyhow!("bind var not in store"))?;
                        let var_vert = foil.alloc_unique_var(var.to_string());

                        let val_vert = self
                            .add_to_foil(foil, store, context, &rest[1])?
                            .ok_or(anyhow!("bind val missing"))?;

                        self.handle_bind(store, context, rest, &[var_vert])?;
                        // return Ok(Some(self.handle_bind(store, context, rest, &[val_vert])?));

                        vec![Some(var_vert), Some(val_vert)]
                    } else {
                        rest.iter()
                            .map(|succ| self.add_to_foil(foil, store, context, succ))
                            .collect::<Result<Vec<_>>>()?
                    };

                    info!("adding to foil: {sym:}, {meta:?}");
                    let func = self.symbol_func(sym);

                    Ok(Some(foil.add_with_meta(
                        func,
                        &successor_verts.into_iter().flatten().collect::<Vec<_>>(),
                        meta,
                    )))
                }
            }
            Tag::Expr(ExprTag::Sym) => {
                info!("adding symbol");
                if let Some(bound_id) = context
                    .lookup(store, expr)
                    .map_err(|_e| anyhow!("lookup error"))?
                {
                    Ok(Some(Vert::new(bound_id)))
                } else {
                    let sym = store.fetch_sym(expr).expect("missing sym");

                    Ok(Some(foil.alloc(sym)))
                }
            }
            _x => {
                //dbg!(x);
                todo!("intern constant")
            }
        }
    }

    fn handle_bind(
        &self,
        store: &Store<F>,
        context: &mut Context,
        args: &[Ptr],
        successors: &[Vert],
    ) -> Result<Vert> {
        if args.len() != 2 {
            bail!("bind needs exactly two args")
        };
        if successors.len() != 1 {
            bail!("bind needs exactly two successors")
        };

        let var = args[0];
        let vert = successors[0];
        info!(
            "binding {} to {}",
            var.fmt_to_string_simple(store),
            vert.id()
        );

        context.push_binding(store, var, vert.id());

        Ok(vert)
    }
    fn handle_pop_binding(
        &self,
        store: &Store<F>,
        context: &mut Context,
        args: &[Ptr],
    ) -> Result<Option<Vert>> {
        if !args.is_empty() {
            bail!("pop-binding needs exactly zero args")
        };

        context
            .pop_binding(store)
            .map_err(|_e| anyhow!("failed to pop binding"))?;

        Ok(None)
    }
}

impl<F: LurkField, R: Relation<F>, S: Syntax<F>> From<CoilDef<F, R, S>> for Schema<CoilMeta> {
    fn from(coil_def: CoilDef<F, R, S>) -> Self {
        coil_def.schema()
    }
}
impl<F: LurkField, R: Relation<F>, S: Syntax<F>> From<&CoilDef<F, R, S>> for Schema<CoilMeta> {
    fn from(coil_def: &CoilDef<F, R, S>) -> Self {
        coil_def.schema()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::congruence::test::assert_expected_classes;
    use crate::{FoilConfig, MappedFoil};
    use bellpepper_core::{
        num::AllocatedNum, test_cs::TestConstraintSystem, Circuit, ConstraintSystem, SynthesisError,
    };
    use generic_array::typenum::U2;
    use lurk::circuit::gadgets::constraints::enforce_equal;
    use lurk_macros::{let_store, lurk, store};
    use neptune::circuit2::poseidon_hash_allocated as poseidon_hash;
    use neptune::poseidon::PoseidonConstants;
    use once_cell::sync::Lazy;
    use pasta_curves::pallas::Scalar as Fr;

    #[derive(Default, Debug)]
    struct ConsRel {}

    #[derive(Default, Debug)]
    struct CarRel {}

    #[derive(Default, Debug)]
    struct CdrRel {}

    #[derive(Default, Debug)]
    struct XxxRel {}

    #[derive(Debug)]
    enum TestRel {
        Bind(BindRel),
        Var(VarRel),
        Cons(ConsRel),
        Car(CarRel),
        Cdr(CdrRel),
        Xxx(XxxRel),
    }

    static P: Lazy<PoseidonConstants<Fr, U2>> = Lazy::new(PoseidonConstants::new);

    impl Relation<Fr> for TestRel {
        fn synthesize<CS: ConstraintSystem<Fr>>(
            &self,
            cs: &mut CS,
            allocated_head: AllocatedNum<Fr>,
            successors: Vec<AllocatedNum<Fr>>,
        ) -> Result<(), SynthesisError> {
            match self {
                Self::Bind(x) => x.synthesize(cs, allocated_head, successors),
                Self::Var(x) => x.synthesize(cs, allocated_head, successors),
                Self::Cons(x) => x.synthesize(cs, allocated_head, successors),
                Self::Car(x) => x.synthesize(cs, allocated_head, successors),
                Self::Cdr(x) => x.synthesize(cs, allocated_head, successors),
                Self::Xxx(x) => x.synthesize(cs, allocated_head, successors),
            }
        }
    }
    impl Relation<Fr> for ConsRel {
        fn synthesize<CS: ConstraintSystem<Fr>>(
            &self,
            cs: &mut CS,
            allocated_head: AllocatedNum<Fr>,
            successors: Vec<AllocatedNum<Fr>>,
        ) -> Result<(), SynthesisError> {
            let allocated_digest =
                poseidon_hash(&mut cs.namespace(|| "poseidon hash"), successors, &*P)?;
            enforce_equal(cs, || "digest equal", &allocated_head, &allocated_digest);
            Ok(())
        }
    }
    impl Relation<Fr> for CarRel {
        fn synthesize<CS: ConstraintSystem<Fr>>(
            &self,
            _cs: &mut CS,
            _allocated_head: AllocatedNum<Fr>,
            _successors: Vec<AllocatedNum<Fr>>,
        ) -> Result<(), SynthesisError> {
            // Nothing to do. The constraints are created by the corresponding ConsRel.
            Ok(())
        }
    }
    impl Relation<Fr> for CdrRel {
        fn synthesize<CS: ConstraintSystem<Fr>>(
            &self,
            _cs: &mut CS,
            _allocated_head: AllocatedNum<Fr>,
            _successors: Vec<AllocatedNum<Fr>>,
        ) -> Result<(), SynthesisError> {
            // Nothing to do. The constraints are created by the corresponding ConsRel.
            Ok(())
        }
    }
    impl Relation<Fr> for XxxRel {
        fn synthesize<CS: ConstraintSystem<Fr>>(
            &self,
            _cs: &mut CS,
            _allocated_head: AllocatedNum<Fr>,
            _successors: Vec<AllocatedNum<Fr>>,
        ) -> Result<(), SynthesisError> {
            // Nothing to do. The constraints are created by the corresponding ConsRel.
            Ok(())
        }
    }

    #[test_log::test]
    fn test_coil_foil() {
        let mut def = CoilDef::<_, _, CoilSyntax>::new_std();

        ////////////////////////////////////////////////////////////////////////////////
        // Set up the CoilDef and Schema
        //
        // TODO: derive all this from something simpler and declarative.

        // These shouldn't really be .lurk symbols, but until we have better package support, we need to use those.
        let cons = sym!("lurk", "cons");
        let car = sym!("lurk", "car");
        let cdr = sym!("lurk", "cdr");

        let bind = sym!("coil", "bind");
        let var = sym!("coil", "var");
        let xxx = sym!("lurk", "user", "xxx");

        def.register_relation(var, TestRel::Var(VarRel {}));
        def.register_relation(bind, TestRel::Bind(BindRel {}));
        def.register_relation(cons.clone(), TestRel::Cons(ConsRel {}));
        def.register_relation(car.clone(), TestRel::Car(CarRel {}));
        def.register_relation(cdr.clone(), TestRel::Cdr(CdrRel {}));
        def.register_relation(xxx, TestRel::Xxx(XxxRel {}));

        def.register_constructor(cons, vec![car, cdr]);

        let_store!(); // TODO: take field type parameter. This macro currently hard-codes Fr.

        let prog = lurk!((let ((x (cons q r)))
                          (let ((s (let ((x (cons a b)))
                                    (car x)
                                    (xxx qqq))))
                           (car x))))
        .unwrap();

        let mut foil = Foil::<Fr, CoilMeta>::new(
            &def,
            FoilConfig {
                // This is necessary and should either be made the only option, or be required for Coil.
                dedup_var_names: true,
            },
        );

        {
            let f = &mut foil;

            let mut context = Context::new(store!());
            def.add_to_foil(f, store!(), &mut context, &prog).unwrap();

            let classes = dbg!(f.graph.class_info(None));

            let expected_classes = &[
                (0, vec!["Var(.lurk.user.x)[0]: 0"], None),
                (1, vec!["Var(.lurk.user.q): 1"], None),
                (2, vec!["Var(.lurk.user.r): 2"], None),
                (3, vec![".lurk.cons: 3"], Some(vec![1, 2])),
                (4, vec![".coil.bind: 4"], Some(vec![0, 3])),
                (5, vec!["Var(.lurk.user.s)[1]: 5"], None),
                (6, vec!["Var(.lurk.user.x)[2]: 6"], None),
                (7, vec!["Var(.lurk.user.a): 7"], None),
                (8, vec!["Var(.lurk.user.b): 8"], None),
                (9, vec![".lurk.cons: 9"], Some(vec![7, 8])),
                (10, vec![".coil.bind: 10"], Some(vec![6, 9])),
                (11, vec![".lurk.car: 11"], Some(vec![6])),
                (12, vec!["Var(.lurk.user.qqq): 12"], None),
                (13, vec![".lurk.user.xxx: 13"], Some(vec![12])),
                (14, vec![".coil.bind: 14"], Some(vec![5, 13])),
                (15, vec![".lurk.car: 15"], Some(vec![0])),
            ];
            assert_expected_classes(expected_classes, &classes);
        }

        {
            foil.finalize();
            let classes = dbg!(foil.graph.class_info(None));
            let expected_classes = &[
                (
                    0,
                    vec!["Var(.lurk.user.x)[0]: 0", ".lurk.cons: 3", ".lurk.cons: 19"],
                    Some(vec![20, 21]),
                ),
                (4, vec![".coil.bind: 4"], Some(vec![0, 0])),
                (
                    5,
                    vec!["Var(.lurk.user.s)[1]: 5", ".lurk.user.xxx: 13"],
                    Some(vec![12]),
                ),
                (
                    6,
                    vec!["Var(.lurk.user.x)[2]: 6", ".lurk.cons: 9", ".lurk.cons: 16"],
                    Some(vec![17, 18]),
                ),
                (10, vec![".coil.bind: 10"], Some(vec![6, 6])),
                (12, vec!["Var(.lurk.user.qqq): 12"], None),
                (14, vec![".coil.bind: 14"], Some(vec![5, 5])),
                (
                    17,
                    vec![
                        "Var(.lurk.user.a): 7",
                        ".lurk.car: 11",
                        "Var(.lurk.car)[3]: 17",
                        ".lurk.car: 24",
                        ".lurk.car: 26",
                    ],
                    Some(vec![6]),
                ),
                (
                    18,
                    vec![
                        "Var(.lurk.user.b): 8",
                        "Var(.lurk.cdr)[4]: 18",
                        ".lurk.cdr: 25",
                        ".lurk.cdr: 27",
                    ],
                    Some(vec![6]),
                ),
                (
                    20,
                    vec![
                        "Var(.lurk.user.q): 1",
                        ".lurk.car: 15",
                        "Var(.lurk.car)[5]: 20",
                        ".lurk.car: 22",
                        ".lurk.car: 28",
                    ],
                    Some(vec![0]),
                ),
                (
                    21,
                    vec![
                        "Var(.lurk.user.r): 2",
                        "Var(.lurk.cdr)[6]: 21",
                        ".lurk.cdr: 23",
                        ".lurk.cdr: 29",
                    ],
                    Some(vec![0]),
                ),
            ];
            assert_expected_classes(expected_classes, &classes);
        }

        info!("minimizing");

        let minimized = foil.minimize();
        let classes = dbg!(minimized.graph.class_info(None));

        let expected_classes = &[
            (0, vec![".lurk.cons: 0"], Some(vec![6, 7])),
            (1, vec![".lurk.user.xxx: 1"], Some(vec![3])),
            (2, vec![".lurk.cons: 2"], Some(vec![4, 5])),
            (3, vec!["Var(.lurk.user.qqq): 3"], None),
            (4, vec![".lurk.car: 4"], Some(vec![2])),
            (5, vec![".lurk.cdr: 5"], Some(vec![2])),
            (6, vec![".lurk.car: 6"], Some(vec![0])),
            (7, vec![".lurk.cdr: 7"], Some(vec![0])),
        ];
        assert_expected_classes(expected_classes, &classes);

        let fx = MappedFoil::new(minimized, def);
        let cs = &mut TestConstraintSystem::<Fr>::new();

        fx.synthesize(cs).unwrap();

        // Binary poseidon hash with standard strength is 237 constraints.
        // This includes a constraint (and allocation) for the returned digest,
        // and another to enforce equality with the `allocated_head` of the relation.
        // One constraint and allocation could be optimized away by calling the unallocated
        // poseidon-circuit function. However, that may add complexity to witness generation.
        //
        // 239 * 2 = 478, since there are two conses.
        assert_eq!(478, cs.num_constraints());
    }
}
