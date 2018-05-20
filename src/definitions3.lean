-- definitions that are used by the lemmas but not referenced by the a theorem

import .definitions2

-- (∀x {call(x)} ⇒ P) ∈ CallQuantifiers
structure callquantifier := (x: var) (P: prop)

-- s ∈ DStacks := (R, σ, e) | s · (R, σ, let y = f(x) in e)
inductive dstack
| top  : spec → env → exp → dstack
| cons : dstack → spec → env → var → var → var → exp → dstack

-- (R, σ, e) : dstack
instance : has_coe (spec × env × exp) dstack := ⟨λe, dstack.top e.1 e.2.1 e.2.2⟩

-- stack precondition projection

def dstack.pre: dstack → spec
| (dstack.top R _ _) := R
| (dstack.cons _ R _ _ _ _ _) := R

lemma sizeof_substack {s: dstack} {R: spec} {σ: env} {f x y: var} {e: exp}:
      s.sizeof < (dstack.cons s R σ f x y e).sizeof :=
  begin
    unfold dstack.sizeof,
    change sizeof s < 1 + sizeof s + sizeof R + sizeof σ + sizeof f + sizeof x + sizeof y + sizeof e,
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    rw[add_comm],
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

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

-- evaluation relation that includes the current function precondition for each stack frame

inductive dstep : dstack → dstack → Prop
notation s₁ `⟹` s₂:100 := dstep s₁ s₂

| ctx {s s': dstack} {R: spec} {σ: env} {y f x: var} {e: exp}:
    (s ⟹ s') →
    (dstack.cons s R σ y f x e ⟹ dstack.cons s' R σ y f x e)

| tru {R: spec} {σ: env} {x: var} {e: exp}:
    (R, σ, lett x = true in e) ⟹ (R, σ[x↦value.true], e)

| fals {R: spec} {σ: env} {x: var} {e: exp}:
    (R, σ, letf x = false in e) ⟹ (R, σ[x↦value.false], e)

| num {R: spec} {σ: env} {x: var} {e: exp} {n: ℤ}:
    (R, σ, letn x = n in e) ⟹ (R, σ[x↦value.num n], e)

| closure {σ: env} {R' R S: spec} {f x: var} {e₁ e₂: exp}:
    (R', σ, letf f[x] req R ens S {e₁} in e₂) ⟹ 
    (R', σ[f↦value.func f x R S e₁ σ], e₂)

| unop {R: spec} {op: unop} {σ: env} {x y: var} {e: exp} {v₁ v: value}:
    (σ x = v₁) →
    (unop.apply op v₁ = v) →
    ((R, σ, letop y = op [x] in e) ⟹ (R, σ[y↦v], e))

| binop {R: spec} {op: binop} {σ: env} {x y z: var} {e: exp} {v₁ v₂ v: value}:
    (σ x = v₁) →
    (σ y = v₂) →
    (binop.apply op v₁ v₂ = v) →
    ((R, σ, letop2 z = op [x, y] in e) ⟹ (R, σ[z↦v], e))

| app {σ σ': env} {R' R S: spec} {f g x y z: var} {e e': exp} {v: value}:
    (σ f = value.func g z R S e σ') →
    (σ x = v) →
    ((R', σ, letapp y = f[x] in e') ⟹
    (dstack.cons (R, (σ'[g↦value.func g z R S e σ'][z↦v]), e) R' σ y f x e'))

| return {σ₁ σ₂ σ₃: env} {f g gx x y z: var} {R₁ R₂ R S: spec} {e e': exp} {v vₓ: value}:
    (σ₁ z = v) →
    (σ₂ f = value.func g gx R S e σ₃) →
    (σ₂ x = vₓ) →
    (dstack.cons (R₁, σ₁, exp.return z) R₂ σ₂ y f x e' ⟹ (R₂, σ₂[y↦v], e'))

| ite_true {R: spec} {σ: env} {e₁ e₂: exp} {x: var}:
    (σ x = value.true) →
    ((R, σ, exp.ite x e₁ e₂) ⟹ (R, σ, e₁))

| ite_false {R: spec} {σ: env} {e₁ e₂: exp} {x: var}:
    (σ x = value.false) →
    ((R, σ, exp.ite x e₁ e₂) ⟹ (R, σ, e₂))

notation s₁ `⟹` s₂:100 := dstep s₁ s₂

-- transitive closure
inductive trans_dstep : dstack → dstack → Prop
notation s `⟹*` s':100 := trans_dstep s s'
| rfl {s: dstack}          : s ⟹* s
| trans {s s' s'': dstack} : (s ⟹* s') → (s' ⟹ s'') → (s ⟹* s'')

notation s `⟹*` s':100 := trans_dstep s s'

def is_dvalue (s: dstack) :=
  ∃(R: spec) (σ: env) (x: var) (v: value), s = (R, σ, exp.return x) ∧ (σ x = v)

-- runtime verification of stacks

inductive stack.dvcgen : dstack → propctx → Prop
notation `⊩ₛ` s `:` Q : 10 := stack.dvcgen s Q

| top {R: spec} {P: prop} {σ: env} {e: exp} {Q: propctx}:
    (⊩ σ : P) →
    FV R.to_prop ⊆ FV P →
    (σ ⊨ R.to_prop.to_vc) →
    (R ⋀ P ⊩ e : Q) →
    (⊩ₛ (R, σ, e) : P ⋀ Q)

| cons {P₁ P₂ P₃: prop} {s: dstack} {σ₁ σ₂: env}
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
    (R₁ ⋀ P₁ ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⊩ e₁ : Q₁) →
    (P₂ ⋀ spec.func f fx R₂ S₂ ⋀ R₂ ⊩ e₂ : Q₂) →
    (∀σ' t, (σ' ⊨ (Q₂' t).to_vc) → σ' ⊨ (P₃ ⋀ (Q₂ t)).to_vc) →
    (∀v: value, FV (P₃ ⋀ (Q₂ v)) ⊆ FV (Q₂' v)) →
    ⦃ prop.implies (R₁ ⋀ P₁ ⋀ prop.call x) (term.unop unop.isFunc g ⋀ prop.pre g x) ⦄ →
    ((R₂, σ₂[f↦value.func f fx R₂ S₂ e₂ σ₂][fx↦v], e₂) ⟹* s) →
    (⊩ₛ dstack.cons s R₁ σ₁ y g x e₁ : P₁ ⋀
          propctx.exis y (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₁))

notation `⊩ₛ` s `:` Q : 10 := stack.dvcgen s Q

inductive stack_equiv_dstack : stack → dstack → Prop
| top {R: spec} {σ: env} {e: exp} :
  stack_equiv_dstack (stack.top σ e) (dstack.top R σ e)
| cons {s': stack} {d': dstack} {R: spec} {σ: env} {f x y: var} {e: exp}:
  stack_equiv_dstack s' d' →
  stack_equiv_dstack (stack.cons s' σ f x y e) (dstack.cons d' R σ f x y e)
