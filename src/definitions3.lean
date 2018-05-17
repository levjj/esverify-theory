-- definitions that are used by the lemmas but not referenced by the soundness theorem

import .definitions2

-- top-level calls and quantifiers in positive and negative positions
mutual inductive prop.has_call_p, prop.has_call_n

with prop.has_call_p: calltrigger → prop → Prop
| calltrigger {x: term}                                 : prop.has_call_p ⟨x⟩ (prop.call x)
| not {P: prop} {c: calltrigger}                        : prop.has_call_n c P  → prop.has_call_p c P.not
| and₁ {P₁ P₂: prop} {c: calltrigger}                   : prop.has_call_p c P₁ → prop.has_call_p c (P₁ ⋀ P₂)
| and₂ {P₁ P₂: prop} {c: calltrigger}                   : prop.has_call_p c P₂ → prop.has_call_p c (P₁ ⋀ P₂)
| or₁ {P₁ P₂: prop} {c: calltrigger}                    : prop.has_call_p c P₁ → prop.has_call_p c (P₁ ⋁ P₂)
| or₂ {P₁ P₂: prop} {c: calltrigger}                    : prop.has_call_p c P₂ → prop.has_call_p c (P₁ ⋁ P₂)

with prop.has_call_n: calltrigger → prop → Prop
| not {P: prop} {c: calltrigger}                        : prop.has_call_p c P  → prop.has_call_n c P.not
| and₁ {P₁ P₂: prop} {c: calltrigger}                   : prop.has_call_n c P₁ → prop.has_call_n c (P₁ ⋀ P₂)
| and₂ {P₁ P₂: prop} {c: calltrigger}                   : prop.has_call_n c P₂ → prop.has_call_n c (P₁ ⋀ P₂)
| or₁ {P₁ P₂: prop} {c: calltrigger}                    : prop.has_call_n c P₁ → prop.has_call_n c (P₁ ⋁ P₂)
| or₂ {P₁ P₂: prop} {c: calltrigger}                    : prop.has_call_n c P₂ → prop.has_call_n c (P₁ ⋁ P₂)

-- sets of calls
def calls_p (P: prop): set calltrigger := λc, prop.has_call_p c P
def calls_n (P: prop): set calltrigger := λc, prop.has_call_n c P

mutual inductive prop.has_quantifier_p, prop.has_quantifier_n

with prop.has_quantifier_p: callquantifier → prop → Prop
| callquantifier {x: var} {P: prop}           : prop.has_quantifier_p ⟨x, P⟩ (prop.forallc x P)
| not {P: prop} {q: callquantifier}           : prop.has_quantifier_n q P  → prop.has_quantifier_p q P.not
| and₁ {P₁ P₂: prop} {q: callquantifier}      : prop.has_quantifier_p q P₁ → prop.has_quantifier_p q (P₁ ⋀ P₂)
| and₂ {P₁ P₂: prop} {q: callquantifier}      : prop.has_quantifier_p q P₂ → prop.has_quantifier_p q (P₁ ⋀ P₂)
| or₁ {P₁ P₂: prop} {q: callquantifier}       : prop.has_quantifier_p q P₁ → prop.has_quantifier_p q (P₁ ⋁ P₂)
| or₂ {P₁ P₂: prop} {q: callquantifier}       : prop.has_quantifier_p q P₂ → prop.has_quantifier_p q (P₁ ⋁ P₂)

with prop.has_quantifier_n: callquantifier → prop → Prop
| not {P: prop} {q: callquantifier}           : prop.has_quantifier_p q P  → prop.has_quantifier_n q P.not
| and₁ {P₁ P₂: prop} {q: callquantifier}      : prop.has_quantifier_n q P₁ → prop.has_quantifier_n q (P₁ ⋀ P₂)
| and₂ {P₁ P₂: prop} {q: callquantifier}      : prop.has_quantifier_n q P₂ → prop.has_quantifier_n q (P₁ ⋀ P₂)
| or₁ {P₁ P₂: prop} {q: callquantifier}       : prop.has_quantifier_n q P₁ → prop.has_quantifier_n q (P₁ ⋁ P₂)
| or₂ {P₁ P₂: prop} {q: callquantifier}       : prop.has_quantifier_n q P₂ → prop.has_quantifier_n q (P₁ ⋁ P₂)
-- universal quantifiers below existential quantifiers only occur in positive positions,
-- so can be skolemized instead of instantiated

-- sets of quantifiers
def quantifiers_p (P: prop): set callquantifier := λc, has_quantifier_p c P
def quantifiers_n (P: prop): set callquantifier := λc, has_quantifier_n c P
def quantifiers (P: prop): set callquantifier := quantifiers_p P ∪ quantifiers_n P

 -- propositions without call triggers or quantifiers do not participate in instantiations
def no_instantiations(P: prop): Prop := (calls_p P = ∅) ∧ (calls_n P = ∅) ∧
                                        (quantifiers_p P = ∅) ∧ (quantifiers_n P = ∅)

-- set of calltriggers after substitution
def calltrigger.subst (σ: env) (c: calltrigger): calltrigger := ⟨term.subst_env σ c.x⟩
def calls_p_subst (σ: env) (P: prop): set calltrigger := (calltrigger.subst σ) '' calls_p P
def calls_n_subst (σ: env) (P: prop): set calltrigger := (calltrigger.subst σ) '' calls_n P

-- uses variables (either free or quantified)

inductive prop.uses_var (x: var) : prop → Prop
| term {t: term}                        : free_in_term x t  → prop.uses_var t
| not {P: prop}                         : prop.uses_var P   → prop.uses_var (prop.not P)
| and₁ {P₁ P₂: prop}                    : prop.uses_var P₁  → prop.uses_var (prop.and P₁ P₂)
| and₂ {P₁ P₂: prop}                    : prop.uses_var P₂  → prop.uses_var (prop.and P₁ P₂)
| or₁ {P₁ P₂: prop}                     : prop.uses_var P₁  → prop.uses_var (prop.or P₁ P₂)
| or₂ {P₁ P₂: prop}                     : prop.uses_var P₂  → prop.uses_var (prop.or P₁ P₂)
| pre₁ {t₁ t₂: term}                    : free_in_term x t₁ → prop.uses_var (prop.pre t₁ t₂)
| pre₂ {t₁ t₂: term}                    : free_in_term x t₂ → prop.uses_var (prop.pre t₁ t₂)
| preop {t: term} {op: unop}            : free_in_term x t  → prop.uses_var (prop.pre₁ op t)
| preop₁ {t₁ t₂: term} {op: binop}      : free_in_term x t₁ → prop.uses_var (prop.pre₂ op t₁ t₂)
| preop₂ {t₁ t₂: term} {op: binop}      : free_in_term x t₂ → prop.uses_var (prop.pre₂ op t₁ t₂)
| post₁ {t₁ t₂: term}                   : free_in_term x t₁ → prop.uses_var (prop.post t₁ t₂)
| post₂ {t₁ t₂: term}                   : free_in_term x t₂ → prop.uses_var (prop.post t₁ t₂)
| call {t: term}                        : free_in_term x t → prop.uses_var (prop.call t)
| forallc {y: var} {P: prop}            : prop.uses_var P → prop.uses_var (prop.forallc y P)
| uquantified {P: prop}                 : prop.uses_var (prop.forallc x P)
| exis {y: var} {P: prop}               : prop.uses_var P → prop.uses_var (prop.exis y P)
| equantified {P: prop}                 : prop.uses_var (prop.exis x P)

inductive vc.uses_var (x: var) : vc → Prop
| term {t: term}                        : free_in_term x t  → vc.uses_var t
| not {P: vc}                           : vc.uses_var P     → vc.uses_var (vc.not P)
| and₁ {P₁ P₂: vc}                      : vc.uses_var P₁    → vc.uses_var (vc.and P₁ P₂)
| and₂ {P₁ P₂: vc}                      : vc.uses_var P₂    → vc.uses_var (vc.and P₁ P₂)
| or₁ {P₁ P₂: vc}                       : vc.uses_var P₁    → vc.uses_var (vc.or P₁ P₂)
| or₂ {P₁ P₂: vc}                       : vc.uses_var P₂    → vc.uses_var (vc.or P₁ P₂)
| pre₁ {t₁ t₂: term}                    : free_in_term x t₁ → vc.uses_var (vc.pre t₁ t₂)
| pre₂ {t₁ t₂: term}                    : free_in_term x t₂ → vc.uses_var (vc.pre t₁ t₂)
| preop {t: term} {op: unop}            : free_in_term x t  → vc.uses_var (vc.pre₁ op t)
| preop₁ {t₁ t₂: term} {op: binop}      : free_in_term x t₁ → vc.uses_var (vc.pre₂ op t₁ t₂)
| preop₂ {t₁ t₂: term} {op: binop}      : free_in_term x t₂ → vc.uses_var (vc.pre₂ op t₁ t₂)
| post₁ {t₁ t₂: term}                   : free_in_term x t₁ → vc.uses_var (vc.post t₁ t₂)
| post₂ {t₁ t₂: term}                   : free_in_term x t₂ → vc.uses_var (vc.post t₁ t₂)
| univ {y: var} {P: vc}                 : vc.uses_var P → vc.uses_var (vc.univ y P)
| quantified {P: vc}                    : vc.uses_var (vc.univ x P)

-- verification conditions without quantifier instantiation algorithm

notation `⦃` P `⦄`: 100 := ∀ (σ: env), closed_subst σ P → σ ⊨ P.to_vc

reserve infix `⊩`:10

-- verification of expressions

inductive exp.dvcgen : prop → exp → propctx → Prop
notation P `⊩` e `:` Q : 10 := exp.dvcgen P e Q

| tru {P: prop} {x: var} {e: exp} {Q: propctx}:
    x ∉ FV P →
    (P ⋀ x ≡ value.true ⊩ e : Q) →
    (P ⊩ lett x = true in e : propctx.exis x (x ≡ value.true ⋀ Q))

| fals {P: prop} {x: var} {e: exp} {Q: propctx}:
    x ∉ FV P →
    (P ⋀ x ≡ value.false ⊩ e : Q) →
    (P ⊩ letf x = false in e : propctx.exis x (x ≡ value.false ⋀ Q))

| num {P: prop} {x: var} {n: ℕ} {e: exp} {Q: propctx}:
    x ∉ FV P →
    (P ⋀ x ≡ value.num n ⊩ e : Q) →
    (P ⊩ letn x = n in e : propctx.exis x (x ≡ value.num n ⋀ Q))

| func {P: prop} {f x: var} {R S: spec} {e₁ e₂: exp} {Q₁ Q₂: propctx}:
    f ∉ FV P →
    x ∉ FV P →
    f ≠ x →
    x ∈ FV R.to_prop.to_vc →
    FV R.to_prop ⊆ FV P ∪ { f, x } →
    FV S.to_prop ⊆ FV P ∪ { f, x } →
    (P ⋀ spec.func f x R S ⋀ R ⊩ e₁ : Q₁) →
    (P ⋀ prop.func f x R (Q₁ (term.app f x) ⋀ S) ⊩ e₂ : Q₂) →
    ⦃ prop.implies (P ⋀ spec.func f x R S ⋀ R ⋀ Q₁ (term.app f x)) S ⦄ →
    (P ⊩ letf f[x] req R ens S {e₁} in e₂ : propctx.exis f (prop.func f x R (Q₁ (term.app f x) ⋀ S) ⋀ Q₂))

| unop {P: prop} {op: unop} {e: exp} {x y: var} {Q: propctx}:
    x ∈ FV P →
    y ∉ FV P →
    (P ⋀ y ≡ term.unop op x ⊩ e : Q) →
    ⦃ prop.implies P (prop.pre₁ op x) ⦄ →
    (P ⊩ letop y = op [x] in e : propctx.exis y (y ≡ term.unop op x ⋀ Q))

| binop {P: prop} {op: binop} {e: exp} {x y z: var} {Q: propctx}:
    x ∈ FV P →
    y ∈ FV P →
    z ∉ FV P →
    (P ⋀ z ≡ term.binop op x y ⊩ e : Q) →
    ⦃ prop.implies P (prop.pre₂ op x y) ⦄ →
    (P ⊩ letop2 z = op [x, y] in e : propctx.exis z (z ≡ term.binop op x y ⋀ Q))

| app {P: prop} {e: exp} {y f x: var} {Q: propctx}:
    f ∈ FV P →
    x ∈ FV P →
    y ∉ FV P →
    (P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⊩ e : Q) →
    ⦃ prop.implies (P ⋀ prop.call f x) (term.unop unop.isFunc f ⋀ prop.pre f x) ⦄ →
    (P ⊩ letapp y = f [x] in e : propctx.exis y (prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⋀ Q))

| ite {P: prop} {e₁ e₂: exp} {x: var} {Q₁ Q₂: propctx}:
    x ∈ FV P →
    (P ⋀ x ⊩ e₁ : Q₁) →
    (P ⋀ prop.not x ⊩ e₂ : Q₂) →
    ⦃ prop.implies P (term.unop unop.isBool x) ⦄ →
    (P ⊩ exp.ite x e₁ e₂ : propctx.implies x Q₁ ⋀ propctx.implies (prop.not x) Q₂)

| return {P: prop} {x: var}:
    x ∈ FV P →
    (P ⊩ exp.return x : x ≣ •)

notation P `⊩` e `:` Q : 10 := exp.dvcgen P e Q

-- verification of environments/translation into logic

inductive env.dvcgen : env → prop → Prop
notation `⊩` σ `:` Q : 10 := env.dvcgen σ Q

| empty:
    ⊩ env.empty : value.true

| tru {σ: env} {x: var} {Q: prop}:
    x ∉ σ →
    (⊩ σ : Q) →
    (⊩ (σ[x ↦ value.true]) : Q ⋀ x ≡ value.true)

| fls {σ: env} {x: var} {Q: prop}:
    x ∉ σ →
    (⊩ σ : Q) →
    (⊩ (σ[x ↦ value.false]) : Q ⋀ x ≡ value.false)

| num {n: ℤ} {σ: env} {x: var} {Q: prop}:
    x ∉ σ →
    (⊩ σ : Q) →
    (⊩ (σ[x ↦ value.num n]) : Q ⋀ x ≡ value.num n)

| func {σ₁ σ₂: env} {f g x: var} {R S: spec} {e: exp} {Q₁ Q₂: prop} {Q₃: propctx}:
    f ∉ σ₁ →
    g ∉ σ₂ →
    x ∉ σ₂ →
    g ≠ x →
    (⊩ σ₁ : Q₁) →
    (⊩ σ₂ : Q₂) →
    x ∈ FV R.to_prop.to_vc →
    FV R.to_prop ⊆ FV Q₂ ∪ { g, x } →
    FV S.to_prop ⊆ FV Q₂ ∪ { g, x } →
    (Q₂ ⋀ spec.func g x R S ⋀ R ⊩ e : Q₃) →
    ⦃ prop.implies (Q₂ ⋀ spec.func g x R S ⋀ R ⋀ Q₃ (term.app g x)) S ⦄ →
    (⊩ (σ₁[f ↦ value.func g x R S e σ₂]) :
      (Q₁
       ⋀ f ≡ value.func g x R S e σ₂
       ⋀ prop.subst_env (σ₂[g↦value.func g x R S e σ₂]) (prop.func g x R (Q₃ (term.app g x) ⋀ S))))

notation `⊩` σ `:` Q : 10 := env.dvcgen σ Q

-- runtime verification of stacks

inductive stack.dvcgen : stack → propctx → Prop
notation `⊩ₛ` s `:` Q : 10 := stack.dvcgen s Q

| top {R: spec} {P: prop} {σ: env} {e: exp} {Q: propctx}:
    (⊩ σ : P) →
    FV R.to_prop ⊆ FV P →
    (σ ⊨ R.to_prop.instantiated_n) →
    (R ⋀ P ⊩ e : Q) →
    (⊩ₛ (R, σ, e) : P ⋀ Q)

| cons {P₁ P₂ P₃: prop} {s: stack} {σ₁ σ₂: env}
       {f fx g x y: var} {R₁ R₂ S₂: spec} {e₁ e₂: exp} {v: value} {Q₁ Q₂ Q₂': propctx}:
    (⊩ₛ s : Q₂') →
    y ∉ σ₁ →
    (⊩ σ₁ : P₁) →
    (⊩ σ₂ : P₂ ) →
    (⊩ (σ₂[f↦value.func f fx R₂ S₂ e₂ σ₂][fx↦v]) : P₃) →
    FV R₁.to_prop ⊆ FV P₁ →
    (σ₁ ⊨ R₁.to_prop.to_vc) →
    (σ₁ g = value.func f fx R₂ S₂ e₂ σ₂) →
    (σ₁ x = v) →
    (R₁ ⋀ P₁ ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⊩ e₁ : Q₁) →
    (P₂ ⋀ spec.func f fx R₂ S₂ ⋀ R₂ ⊩ e₂ : Q₂) →
    (∀σ' t, (σ' ⊨ (Q₂' t).to_vc) → σ' ⊨ (P₃ ⋀ (Q₂ t)).to_vc) →
    (∀v: value, FV (P₃ ⋀ (Q₂ v)) ⊆ FV (Q₂' v)) →
    ⦃ prop.implies (R₁ ⋀ P₁ ⋀ prop.call g x) (term.unop unop.isFunc g ⋀ prop.pre g x) ⦄ →
    ((R₂, σ₂[f↦value.func f fx R₂ S₂ e₂ σ₂][fx↦v], e₂) ⟶* s) →
    (⊩ₛ (s · [R₁, σ₁, letapp y = g[x] in e₁]) : P₁ ⋀
          propctx.exis y (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₁))

notation `⊩ₛ` s `:` Q : 10 := stack.dvcgen s Q
