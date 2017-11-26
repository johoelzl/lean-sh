open tactic expr declaration

meta def get_declarations : tactic $ list declaration :=
(λe : environment, e.fold [] (λd xs, d :: xs)) <$> get_env

inductive fo_term : Type
| var  : name → fo_term
| func : name → list fo_term → fo_term

def fo_term.func₀ (n : name) : fo_term := fo_term.func n []
def fo_term.func₁ (n : name) (a : fo_term) : fo_term := fo_term.func n [a]
def fo_term.func₂ (n : name) (a₁ a₂ : fo_term) : fo_term := fo_term.func n [a₁, a₂]

instance : inhabited fo_term := ⟨fo_term.var $ default name⟩

meta def fo_term.to_format : fo_term → format
| (fo_term.var nm) := to_fmt nm
| (fo_term.func nm lst) :=
  to_fmt nm ++ format.paren (format.join (lst.map $ λl, l.to_format ++ format.space))

meta instance : has_to_format fo_term := ⟨fo_term.to_format⟩

inductive fo_logic : Type
| all   : name → fo_logic → fo_logic
| ex    : name → fo_logic → fo_logic
| pred  : name → list fo_term → fo_logic
| eq    : fo_term → fo_term → fo_logic
| conn  : name → list fo_logic → fo_logic

def fo_logic.conn₀ (n : name) : fo_logic := fo_logic.conn n []
def fo_logic.conn₁ (n : name) (a : fo_logic) : fo_logic := fo_logic.conn n [a]
def fo_logic.conn₂ (n : name) (a₁ a₂ : fo_logic) : fo_logic := fo_logic.conn n [a₁, a₂]

def fo_logic.imp : fo_logic → fo_logic → fo_logic := fo_logic.conn₂ `imp
def fo_logic.and : fo_logic → fo_logic → fo_logic := fo_logic.conn₂ `and
def fo_logic.or : fo_logic → fo_logic → fo_logic := fo_logic.conn₂ `or
def fo_logic.iff : fo_logic → fo_logic → fo_logic := fo_logic.conn₂ `iff
def fo_logic.neg : fo_logic → fo_logic := fo_logic.conn₁ `neg
def fo_logic.true : fo_logic := fo_logic.conn₀ `true
def fo_logic.false : fo_logic := fo_logic.conn₀ `false

def fo_logic.pred₀ (n : name) : fo_logic := fo_logic.pred n []
def fo_logic.pred₁ (n : name) (a : fo_term) : fo_logic := fo_logic.pred n [a]
def fo_logic.pred₂ (n : name) (a₁ a₂ : fo_term) : fo_logic := fo_logic.pred n [a₁, a₂]

instance : inhabited fo_logic := ⟨fo_logic.true⟩

meta def fo_logic.to_format : fo_logic → format
| (fo_logic.all nm l) := to_fmt "∀" ++ to_fmt nm ++ to_fmt ", " ++ fo_logic.to_format l
| (fo_logic.ex nm l) := to_fmt "∃" ++ to_fmt nm ++ to_fmt ", " ++ fo_logic.to_format l
| (fo_logic.pred nm lst) := to_fmt nm ++ to_fmt lst
| (fo_logic.eq a b) := to_fmt a ++ to_fmt " = " ++ to_fmt b
| (fo_logic.conn nm lst) := to_fmt nm ++ format.space ++
  format.paren (format.join $ lst.map $ λl, l.to_format ++ format.space)

meta instance : has_to_format fo_logic := ⟨fo_logic.to_format⟩

meta structure cic_to_fo_data : Type :=
(ctxt : list $ name × expr × fo_term)
(declarations : list $ name × fo_logic)

meta instance : inhabited cic_to_fo_data := ⟨⟨[], []⟩⟩

meta def cic_to_fo := state_t cic_to_fo_data tactic
meta instance : monad cic_to_fo := state_t.monad _ _
meta instance : monad.has_monad_lift tactic cic_to_fo := ⟨λα, state_t.lift⟩
meta instance (α : Type) : has_coe (tactic α) (cic_to_fo α) := ⟨monad.monad_lift⟩
meta instance : alternative cic_to_fo := state_t.alternative _ _
meta instance : monad_fail cic_to_fo :=
{ fail := λ α s, (tactic.fail (to_fmt s) : cic_to_fo α), ..cic_to_fo.monad }

meta def get_ctxt : cic_to_fo $ list $ name × expr × fo_term :=
cic_to_fo_data.ctxt <$> state_t.read

meta def update_ctxt (ctxt : list $ name × expr × fo_term) : cic_to_fo unit :=
state_t.modify $ λd, {ctxt := ctxt .. d}

meta def with_var {α : Type} (t : name × expr × fo_term) (c : cic_to_fo α) : cic_to_fo α := do
  ctxt ← get_ctxt,
  update_ctxt (t :: ctxt),
  a ← c,
  update_ctxt ctxt,
  return a

meta def add_decl (nm : name) (decl : fo_logic) : cic_to_fo unit :=
state_t.modify $ λd, { declarations := (nm, decl) :: d.declarations, .. d }

meta def get_decls : cic_to_fo $ list $ name × fo_logic :=
cic_to_fo_data.declarations <$> state_t.read

meta mutual def abstract_context, to_fo_term, to_fo_logic, to_fo_type

with abstract_context : list (name × expr × fo_term) → fo_logic → cic_to_fo fo_logic
| [] e := return e
| ((n, t, r) :: cs) e := do
  t' ← to_fo_type (fo_term.var n) t,
  abstract_context cs $ (t'.imp e).all n

with to_fo_term : expr → cic_to_fo fo_term
| (const n ls)            := return $ fo_term.func n []
| (local_const n _ _ t) := (do
    ctxt ← get_ctxt,
    let n := ctxt.find_index $ λd, d.fst = n,
    some (n, t, r) ← return $ ctxt.nth n,
    return r) <|> (do
      ctxt ← get_ctxt,
      (fail ("name not found" ++ n.to_string ++ ((to_fmt ctxt).to_string)) : cic_to_fo fo_term))
| (sort l)                := return $ fo_term.func `Type [] -- take care of the level
| e@(pi n _ t d)          := do
    ctxt ← get_ctxt,
    n' ← mk_fresh_name,
    let c := fo_term.func n' $ ctxt.map (fo_term.var ∘ prod.fst),
    infer_type e >>= to_fo_type c >>= abstract_context ctxt >>= add_decl (n' ++ "_type"),
    x ← mk_fresh_name,
    let x' := fo_term.var x,
    (fo_logic.all x <$> with_var (x, e, x')
      ((fo_logic.pred₂ `has_Type x' c).iff <$> to_fo_type x' e)) >>=
      abstract_context ctxt >>= add_decl n',
    return c
| e@(lam n _ t b)         := do
    ctxt ← get_ctxt,
    n' ← mk_fresh_name,
    let c := fo_term.func n' $ ctxt.map $ fo_term.var ∘ prod.fst,
    infer_type e >>= to_fo_type c >>= abstract_context ctxt >>= add_decl (n' ++ "_type"),
    x ← mk_fresh_name,
    let x' := fo_term.var x,
    let x'' := expr.local_const x n binder_info.default t,
    (fo_logic.all x <$> with_var (x, t, x')
      (fo_logic.eq (c.func₂ `app x') <$> to_fo_term (b.instantiate_var x''))) >>=
      abstract_context ctxt >>= add_decl n',
    return c
| (elet n t v b)          := do
    ctxt ← get_ctxt,
    c ← (λn, fo_term.func n $ ctxt.map (fo_term.var ∘ prod.fst)) <$> mk_fresh_name,
    to_fo_type c t >>= abstract_context ctxt >>= add_decl (n ++ "_type"),
    to_fo_term v >>= λv, abstract_context ctxt (fo_logic.eq c v) >>= add_decl n,
    with_var (n, t, c) $
      to_fo_term (b.instantiate_var $ expr.local_const n n binder_info.default t)
| (app f a)               := fo_term.func₂ `app <$> to_fo_term f <*> to_fo_term a
| (var n)                 := fail "unexpected bound variable"
| (mvar n pp t)           := fail "meta variables not supported" -- yet?
| (macro n es)            := fail "macros not handled"

with to_fo_logic : expr → cic_to_fo fo_logic
| (pi n bi t d) := do
    n' ← mk_fresh_name,
    let v := fo_term.var n',
    let c := expr.local_const n' n bi t,
    fo_logic.all n' <$> (fo_logic.imp <$> to_fo_type v t <*>
      (with_var (n', t, fo_term.var n') $ to_fo_logic $ d.instantiate_var c))
| `(@Exists %%t %%d) := do
    n' ← mk_fresh_name,
    let v := fo_term.var n',
    let c := expr.local_const n' n' binder_info.default t,
    let d' := if d.is_lambda then d.binding_body.instantiate_var c else d.app c,
    fo_logic.ex n' <$> (fo_logic.and <$> to_fo_type v t <*>
      (with_var (n', t, fo_term.var n') $ to_fo_logic d'))
| `(true)      := return fo_logic.true
| `(false)     := return fo_logic.false
| `(¬ %%p)     := fo_logic.neg <$> to_fo_logic p
| `(%%p ∧ %%q) := fo_logic.and <$> to_fo_logic p <*> to_fo_logic q
| `(%%p ∨ %%q) := fo_logic.or  <$> to_fo_logic p <*> to_fo_logic q
| `(%%p ↔ %%q) := fo_logic.iff <$> to_fo_logic p <*> to_fo_logic q
| `(%%a = %%b) := fo_logic.eq  <$> to_fo_term a <*> to_fo_term b
| `(%%a ≠ %%b) := fo_logic.neg <$> (fo_logic.eq <$> to_fo_term a <*> to_fo_term b)
| e := fo_logic.pred₁ `is_True <$> to_fo_term e

with to_fo_type : fo_term → expr → cic_to_fo fo_logic
| f (pi n bi t d) := do
    n' ← mk_fresh_name,
    let x := fo_term.var n',
    let c := expr.local_const n n' bi t,
    let f_v := f.func₂ `app x in
    fo_logic.all n' <$> (fo_logic.imp <$> to_fo_type f_v t <*>
      (with_var (n', t, fo_term.var n') $ to_fo_type f_v $ d.instantiate_var c))
| v e             := fo_logic.pred₂ `has_Type v <$> to_fo_term e

meta def fo_term.rename_variables : list (name × name) → fo_term → tactic fo_term
| ren t@(fo_term.var nm) := (do
  let n := ren.find_index $ λd, d.fst = nm,
  some (_, nm') ← return $ ren.nth n,
  return $ fo_term.var nm') <|> return t
| ren (fo_term.func nm ls) :=
  fo_term.func nm <$> (ls.mmap $ fo_term.rename_variables ren)

meta def fo_logic.rename_variables : ℕ → list (name × name) → fo_logic → tactic fo_logic
| n ren (fo_logic.all nm l) :=
  fo_logic.all (to_string n) <$> (l.rename_variables (n + 1) ((nm, to_string n) :: ren))
| n ren (fo_logic.ex nm l) :=
  fo_logic.ex (to_string n) <$> (l.rename_variables (n + 1) ((nm, to_string n) :: ren))
| n ren (fo_logic.pred nm ls) :=
  fo_logic.pred nm <$> (ls.mmap $ fo_term.rename_variables ren)
| n ren (fo_logic.conn nm ls) :=
  fo_logic.conn nm <$> (ls.mmap $ fo_logic.rename_variables n ren)
| n ren (fo_logic.eq a b) :=
  fo_logic.eq <$> (fo_term.rename_variables ren a) <*> (fo_term.rename_variables ren b)

meta def in_empty_context {α : Type} (m : cic_to_fo α) : tactic α :=
prod.fst <$> m (default cic_to_fo_data)

run_cmd do
  (t, d) ← in_empty_context (do
    t ← to_fo_logic `(∀α:Type, (λa:α, a) = (λa:α, a) ∧ (Πa:α, α) = (Πa:α, α)),
    d ← get_decls,
    return (t, d)),
  d.mmap (λ⟨n, d⟩, d.rename_variables 0 [] >>= trace),
  t.rename_variables 0 [] >>= trace
