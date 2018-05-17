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

-- runtime verification of stacks

inductive stack.vcgen : stack → propctx → Prop
notation `⊢ₛ` s `:` Q : 10 := stack.vcgen s Q

| top {R: spec} {P: prop} {σ: env} {e: exp} {Q: propctx}:
    (⊢ σ : P) →
    FV R.to_prop ⊆ FV P →
    (σ ⊨ R.to_prop.instantiated_n) →
    (R ⋀ P ⊢ e : Q) →
    (⊢ₛ (R, σ, e) : P ⋀ Q)

| cons {P₁ P₂ P₃: prop} {s: stack} {σ₁ σ₂: env}
       {f fx g x y: var} {R₁ R₂ S₂: spec} {e₁ e₂: exp} {v: value} {Q₁ Q₂ Q₂': propctx}:
    (⊢ₛ s : Q₂') →
    y ∉ σ₁ →
    (⊢ σ₁ : P₁) →
    (⊢ σ₂ : P₂ ) →
    (⊢ (σ₂[f↦value.func f fx R₂ S₂ e₂ σ₂][fx↦v]) : P₃) →
    FV R₁.to_prop ⊆ FV P₁ →
    (σ₁ ⊨ R₁.to_prop.instantiated_n) →
    (σ₁ g = value.func f fx R₂ S₂ e₂ σ₂) →
    (σ₁ x = v) →
    (R₁ ⋀ P₁ ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⊢ e₁ : Q₁) →
    (P₂ ⋀ spec.func f fx R₂ S₂ ⋀ R₂ ⊢ e₂ : Q₂) →
    (∀σ' t, (σ' ⊨ (Q₂' t).instantiated_n) → σ' ⊨ (P₃ ⋀ (Q₂ t)).instantiated_n) →
    (∀v: value, FV (P₃ ⋀ (Q₂ v)) ⊆ FV (Q₂' v)) →
    ⟪ prop.implies (R₁ ⋀ P₁ ⋀ prop.call g x) (term.unop unop.isFunc g ⋀ prop.pre g x) ⟫ →
    ((R₂, σ₂[f↦value.func f fx R₂ S₂ e₂ σ₂][fx↦v], e₂) ⟶* s) →
    (⊢ₛ (s · [R₁, σ₁, letapp y = g[x] in e₁]) : P₁ ⋀
          propctx.exis y (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₁))

notation `⊢ₛ` s `:` Q : 10 := stack.vcgen s Q
