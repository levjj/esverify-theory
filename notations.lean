import .syntax .etc

-- P → Q

@[reducible]
def spec.implies(P Q: spec): spec := spec.or (spec.not P) Q

@[reducible]
def prop.implies(P Q: prop): prop := prop.or (prop.not P) Q

@[reducible]
def propctx.implies(P Q: propctx): propctx := propctx.or (propctx.not P) Q

@[reducible]
def vc.implies(P Q: vc): vc := vc.or (vc.not P) Q

-- P ↔ Q

@[reducible]
def spec.iff(P Q: spec): spec := spec.and (spec.implies P Q) (spec.implies Q P)

@[reducible]
def prop.iff(P Q: prop): prop := prop.and (prop.implies P Q) (prop.implies Q P)

@[reducible]
def propctx.iff(P Q: propctx): propctx := propctx.and (propctx.implies P Q) (propctx.implies Q P)

@[reducible]
def vc.iff(P Q: vc): vc := vc.and (vc.implies P Q) (vc.implies Q P)

-- P ⋀ Q
class has_and (α : Type) := (and : α → α → α) 
instance : has_and spec := ⟨spec.and⟩
instance : has_and prop := ⟨prop.and⟩
instance : has_and propctx := ⟨propctx.and⟩
instance : has_and vc := ⟨vc.and⟩
infixr `⋀`:35 := has_and.and

-- P ⋁ Q
class has_or (α : Type) := (or : α → α → α) 
instance : has_or spec := ⟨spec.or⟩
instance : has_or prop := ⟨prop.or⟩
instance : has_or propctx := ⟨propctx.or⟩
instance : has_or vc := ⟨vc.or⟩
infixr `⋁`:30 := has_or.or

-- use • as hole
notation `•` := termctx.hole

-- history items
notation H `·` `call` := history.call H

-- simple coercions
instance value_to_term : has_coe value term := ⟨term.value⟩
instance var_to_term : has_coe var term := ⟨term.var⟩
instance term_to_prop : has_coe term prop := ⟨prop.term⟩
instance termctx_to_propctx : has_coe termctx propctx := ⟨propctx.term⟩
instance term_to_vc : has_coe term vc := ⟨vc.term⟩

-- use (t ≡ t)/(t ≣ t) to construct equality comparison
infix ≡ := term.binop binop.eq
infix `≣`:50 := termctx.binop binop.eq

-- syntax for let expressions
notation `lett` x `=`:1 `true` `in` e := exp.true x e
notation `letf` x `=`:1 `false` `in` e := exp.false x e
notation `letn` x `=`:1 n`in` e := exp.num x n e
notation `letf` f `[`:1 x `]` `req` R `ens` S `{`:1 e `}`:1 `in` e' := exp.func f x R S e e'
notation `letop` y `=`:1 op `[`:1 x `]`:1 `in` e := exp.unop y op x e
notation `letop2` z `=`:1 op `[`:1 x `,` y `]`:1 `in` e := exp.binop z op x y e
notation `letapp` y `=`:1 f `[`:1 x `]`:1 `in` e := exp.app y f x e

-- σ[x ↦ v]
notation e `[` x `↦` v `]` := env.cons e x v

-- (H, σ, e) : stack
instance : has_coe (spec × history × env × exp) stack := ⟨λe, stack.top e.1 e.2.1 e.2.2.1 e.2.2.2⟩

-- κ · [H, σ, let y = f [ x ] in e]
notation st `·` `[` R `,` H `,` env `,` `letapp` y `=`:1 f `[` x `]` `in` e `]` := stack.cons st R H env y f x e

-- env lookup as function application

@[reducible]
def env.size: env → ℕ := env.rec (λ_, ℕ) 0 (λ_ _ _ n, n + 1)
instance : has_sizeof env := ⟨env.size⟩

def env.apply: env → var → option value
| env.empty _ := none
| (σ[x↦v]) y :=
  have σ.size < (σ[x ↦ v].size), from lt_of_add_one,
  if x = y ∧ option.is_none (σ.apply y) then v else σ.apply y

def env.rest: env → env
| env.empty := env.empty
| (σ[x↦v])  := σ

instance : has_coe_to_fun env := ⟨λ _, var → option value, env.apply⟩

inductive env.contains: env → var → Prop
| same {e: env} {x: var} {v: value} : env.contains (e[x↦v]) x 
| rest {e: env} {x y: var} {v: value} : env.contains e x → env.contains (e[y↦v]) x

instance : has_mem var env := ⟨λx σ, σ.contains x⟩ 

def env.dom (σ: env): set var := λx, x ∈ σ

-- spec to prop coercion

@[reducible]
def spec.size: spec → ℕ := spec.rec (λ_, ℕ)
  (λ_, 0)
  (λ_ n, n + 1)
  (λ_ _ n m , n + m + 1)
  (λ_ _ n m , n + m + 1)
  (λ_ _ _ _ n m , n + m + 1)

instance : has_sizeof spec := ⟨spec.size⟩

@[reducible]
def prop.func (f: term) (x: var) (P: prop) (Q: prop): prop := 
  term.unop unop.isFunc f ⋀
  prop.forallc x f (prop.implies P (prop.pre f x) ⋀
                    prop.implies (prop.post f x) Q)

def spec.to_prop : spec → prop
| (spec.term t)       := prop.term t
| (spec.not S)        :=
    have S.size < S.not.size, from lt_of_add_one,
    prop.not S.to_prop
| (spec.and R S)      :=
    have R.size < (R ⋀ S).size, from lt_of_add.left,
    have S.size < (R ⋀ S).size, from lt_of_add.right,
    R.to_prop ⋀ S.to_prop
| (spec.or R S)       :=
    have R.size < (R ⋁ S).size, from lt_of_add.left,
    have S.size < (R ⋁ S).size, from lt_of_add.right,
    R.to_prop ⋁ S.to_prop
| (spec.func f x R S) :=
    have R.size < (R ⋀ S).size, from lt_of_add.left,
    have S.size < (R ⋀ S).size, from lt_of_add.right,
    prop.func f x R.to_prop S.to_prop

instance spec_to_prop : has_coe spec prop := ⟨spec.to_prop⟩

-- prop size

@[reducible]
def prop.size: prop → ℕ := @prop.rec (λ_, ℕ)
  (λ_, 0)
  (λ_ n, n + 1)
  (λ_ _ n m , n + m + 1)
  (λ_ _ n m , n + m + 1)
  (λ_ _, 0)
  (λ_ _, 0)
  (λ_ _ _, 0)
  (λ_ _, 0)
  (λ_ _, 0)
  (λ_ _ _ n, n + 1)
  (λ_ _ n, n + 1)

instance : has_sizeof prop := ⟨prop.size⟩

-- vc size

@[reducible]
def vc.size: vc → ℕ := @vc.rec (λ_, ℕ)
  (λ_, 0)
  (λ _ n, n + 1)
  (λ_ _ n m , n + m + 1)
  (λ_ _ n m , n + m + 1)
  (λ_ _, 0)
  (λ_ _, 0)
  (λ_ _ _, 0)
  (λ_ _, 0)
  (λ_ _ n, n + 1)

instance : has_sizeof vc := ⟨vc.size⟩

-- history size

@[reducible]
def historyfix: (history → ℕ) → (λ (_x : history), ℕ) history.empty :=
  assume f: history → ℕ,
  (λ (h : history), f h) history.empty 

@[reducible]
def history.size: history → ℕ := @history.rec (λ_, ℕ)
  (historyfix (λ_, 0))
  (λ _ _ _ _ _ _ _ _ _ n _, n + 1)

instance : has_sizeof history := ⟨history.size⟩

-- term to termctx coercion

def term.to_termctx : term → termctx
| (term.value v)        := termctx.value v
| (term.var x)          := termctx.var x
| (term.unop op t)      := termctx.unop op t.to_termctx
| (term.binop op t₁ t₂) := termctx.binop op t₁.to_termctx t₂.to_termctx
| (term.app t₁ t₂)      := termctx.app t₁.to_termctx t₂.to_termctx

instance term_to_termctx : has_coe term termctx := ⟨term.to_termctx⟩

-- term to termctx coercion

def prop.to_propctx : prop → propctx
| (prop.term t)        := propctx.term t
| (prop.not P)         := propctx.not P.to_propctx
| (prop.and P₁ P₂)     := P₁.to_propctx ⋀ P₂.to_propctx
| (prop.or P₁ P₂)      := P₁.to_propctx ⋁ P₂.to_propctx
| (prop.pre t₁ t₂)     := propctx.pre t₁ t₂
| (prop.pre₁ op t)     := propctx.pre₁ op t
| (prop.pre₂ op t₁ t₂) := propctx.pre₂ op t₁ t₂
| (prop.post t₁ t₂)    := propctx.post t₁ t₂
| (prop.call t₁ t₂)    := propctx.call t₁ t₂
| (prop.forallc x t P) := propctx.forallc x t P.to_propctx
| (prop.exis x P)      := propctx.exis x P.to_propctx

instance prop_to_propctx : has_coe prop propctx := ⟨prop.to_propctx⟩

-- termctx substituttion as function application

def termctx.apply: termctx → term → term
| •                           t := t
| (termctx.value v)           _ := term.value v
| (termctx.var x)             _ := term.var x
| (termctx.unop op t₁)        t := term.unop op (t₁.apply t)
| (termctx.binop op t₁ t₂)    t := term.binop op (t₁.apply t) (t₂.apply t)
| (termctx.app t₁ t₂)         t := term.app (t₁.apply t) (t₂.apply t)

instance : has_coe_to_fun termctx := ⟨λ _, term → term, termctx.apply⟩

-- propctx substituttion as function application

def propctx.apply: propctx → term → prop
| (propctx.term t₁) t        := t₁ t
| (propctx.not P) t          := prop.not (P.apply t)
| (propctx.and P₁ P₂) t      := P₁.apply t ⋀ P₂.apply t
| (propctx.or P₁ P₂) t       := P₁.apply t ⋁ P₂.apply t
| (propctx.pre t₁ t₂) t      := prop.pre (t₁ t) (t₂ t)
| (propctx.pre₁ op t₁) t     := prop.pre₁ op (t₁ t)
| (propctx.pre₂ op t₁ t₂) t  := prop.pre₂ op (t₁ t) (t₂ t)
| (propctx.post t₁ t₂) t     := prop.post (t₁ t) (t₂ t)
| (propctx.call t₁ t₂) t     := prop.call (t₁ t) (t₂ t)
| (propctx.forallc x t₁ P) t := prop.forallc x (t₁ t) (P.apply t)
| (propctx.exis x P) t       := prop.exis x (P.apply t)

instance : has_coe_to_fun propctx := ⟨λ _, term → prop, propctx.apply⟩

-- call history to prop coercion

def calls_to_prop: history → prop
| history.empty                        := value.true
| (history.call rest f x R S e H σ vₓ) :=
  have history.size rest < history.size (rest · call f x R S e H σ vₓ), from lt_of_add_one,
  calls_to_prop rest ⋀ prop.call (value.func f x R S e H σ) vₓ

instance call_to_prop: has_coe history prop := ⟨calls_to_prop⟩

-- instantiation is axiomatized in qi.lean

constant prop.instantiated: prop → vc

constant prop.instantiated_n: prop → vc

-- validity is axiomatized in logic.lean

constant valid : vc → Prop
notation `⊨` p: 20 := valid p
