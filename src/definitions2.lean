-- second part of definitions

import .definitions1 .qiaux

--  ################################
--  ### QUANTIFIER INSTANTIATION ###
--  ################################

-- first part is in definitions1.lean
-- the following definitions need some additional lemmas from qiaux.lean to prove termination


-- lift_all(P) performs repeated lifting of quantifiers in positive
-- positions until there is no more quantifier to be lifted
def prop.lift_all: prop → prop
| P :=
  let r := P.lift_p P.fresh_var in
  let z := r in
  have h: z = r, from rfl,
  @option.cases_on prop (λr, (z = r) → prop) r (
    assume : z = none,
    P
  ) (
    assume P': prop,
    assume : z = (some P'),
    have r_id: r = (some P'), from eq.trans h this,
    have P'.num_quantifiers < P.num_quantifiers,
    from (lifted_prop_smaller P').left r_id,
    prop.lift_all P'
  ) rfl

using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf $ λ s, s.num_quantifiers ⟩],
  dec_tac := tactic.assumption
}

-- erase_p(P) / erase_n(P) replaces all triggers and quantifiers
-- in either positive or negative position with 'true'
mutual def prop.erased_p, prop.erased_n

with prop.erased_p: prop → vc
| (prop.term t)        := vc.term t
| (prop.not P)         := have P.sizeof < P.not.sizeof, from sizeof_prop_not,
                          vc.not P.erased_n
| (prop.and P₁ P₂)     := have P₁.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₁,
                          have P₂.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₂,
                          P₁.erased_p ⋀ P₂.erased_p
| (prop.or P₁ P₂)      := have P₁.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₁,
                          have P₂.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₂,
                          P₁.erased_p ⋁ P₂.erased_p
| (prop.pre t₁ t₂)     := vc.pre t₁ t₂
| (prop.pre₁ op t)     := vc.pre₁ op t
| (prop.pre₂ op t₁ t₂) := vc.pre₂ op t₁ t₂
| (prop.post t₁ t₂)    := vc.post t₁ t₂
| (prop.call _)        := vc.term value.true
| (prop.forallc x P)   := vc.term value.true
| (prop.exis x P)      := have P.sizeof < (prop.exis x P).sizeof, from sizeof_prop_exis,
                          vc.not (vc.univ x (vc.not P.erased_p))

with prop.erased_n: prop → vc
| (prop.term t)        := vc.term t
| (prop.not P)         := have P.sizeof < P.not.sizeof, from sizeof_prop_not,
                          vc.not P.erased_p
| (prop.and P₁ P₂)     := have P₁.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₁,
                          have P₂.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₂,
                          P₁.erased_n ⋀ P₂.erased_n
| (prop.or P₁ P₂)      := have P₁.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₁,
                          have P₂.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₂,
                          P₁.erased_n ⋁ P₂.erased_n
| (prop.pre t₁ t₂)     := vc.pre t₁ t₂
| (prop.pre₁ op t)     := vc.pre₁ op t
| (prop.pre₂ op t₁ t₂) := vc.pre₂ op t₁ t₂
| (prop.post t₁ t₂)    := vc.post t₁ t₂
| (prop.call _)        := vc.term value.true
| (prop.forallc x P)   := have P.sizeof < (prop.forallc x P).sizeof, from sizeof_prop_forall,
                          vc.univ x P.erased_n
| (prop.exis x P)      := have P.sizeof < (prop.exis x P).sizeof, from sizeof_prop_exis,
                          vc.not (vc.univ x (vc.not P.erased_n))

using_well_founded {
  rel_tac := λ _ _, `[exact erased_measure],
  dec_tac := tactic.assumption
}

-- given a call trigger t, inst_with_p(P, t) / inst_with_n(P, t) instantiates all quantifiers in
-- either positive or negative positions by adding a conjunction where the quantified
-- variable is replaced by the term in the given trigger
mutual def prop.instantiate_with_p, prop.instantiate_with_n

with prop.instantiate_with_p: prop → calltrigger → prop
| (prop.term t) _        := prop.term t
| (prop.not P) t         := have P.sizeof < P.not.sizeof, from sizeof_prop_not,
                            prop.not (P.instantiate_with_n t)
| (prop.and P₁ P₂) t     := have P₁.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₁,
                            have P₂.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₂,
                            P₁.instantiate_with_p t ⋀ P₂.instantiate_with_p t
| (prop.or P₁ P₂) t      := have P₁.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₁,
                            have P₂.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₂,
                            P₁.instantiate_with_p t ⋁ P₂.instantiate_with_p t
| (prop.pre t₁ t₂) _     := prop.pre t₁ t₂
| (prop.pre₁ op t) _     := prop.pre₁ op t
| (prop.pre₂ op t₁ t₂) _ := prop.pre₂ op t₁ t₂
| (prop.post t₁ t₂) _    := prop.post t₁ t₂
| (prop.call t) _        := prop.call t
| (prop.forallc x P) t   := prop.forallc x P ⋀ P.substt x t.x -- instantiate
| (prop.exis x P) t      := prop.exis x P

with prop.instantiate_with_n: prop → calltrigger → prop
| (prop.term t) _        := prop.term t
| (prop.not P) t         := have P.sizeof < P.not.sizeof, from sizeof_prop_not,
                            prop.not (P.instantiate_with_p t)
| (prop.and P₁ P₂) t     := have P₁.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₁,
                            have P₂.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₂,
                            P₁.instantiate_with_n t ⋀ P₂.instantiate_with_n t
| (prop.or P₁ P₂) t      := have P₁.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₁,
                            have P₂.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₂,
                            P₁.instantiate_with_n t ⋁ P₂.instantiate_with_n t
| (prop.pre t₁ t₂) _     := prop.pre t₁ t₂
| (prop.pre₁ op t) _     := prop.pre₁ op t
| (prop.pre₂ op t₁ t₂) _ := prop.pre₂ op t₁ t₂
| (prop.post t₁ t₂) _    := prop.post t₁ t₂
| (prop.call t) _        := prop.call t
| (prop.forallc x P) t   := prop.forallc x P
| (prop.exis x P) t      := prop.exis x P

using_well_founded {
  rel_tac := λ _ _, `[exact instantiate_with_measure],
  dec_tac := tactic.assumption
}

-- finds all call triggers in either positive or negative positions and returns these as list
mutual def prop.find_calls_p, prop.find_calls_n

with prop.find_calls_p: prop → list calltrigger
| (prop.term t)        := []
| (prop.not P)         := have P.sizeof < P.not.sizeof, from sizeof_prop_not,
                          P.find_calls_n
| (prop.and P₁ P₂)     := have P₁.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₁,
                          have P₂.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₂,
                          P₁.find_calls_p ++ P₂.find_calls_p
| (prop.or P₁ P₂)      := have P₁.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₁,
                          have P₂.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₂,
                          P₁.find_calls_p ++ P₂.find_calls_p
| (prop.pre t₁ t₂)     := []
| (prop.pre₁ op t)     := []
| (prop.pre₂ op t₁ t₂) := []
| (prop.post t₁ t₂)    := []
| (prop.call t)        := [ ⟨ t ⟩ ]
| (prop.forallc x P)   := []
| (prop.exis x P)      := []

with prop.find_calls_n: prop → list calltrigger
| (prop.term t)        := []
| (prop.not P)         := have P.sizeof < P.not.sizeof, from sizeof_prop_not,
                          P.find_calls_p
| (prop.and P₁ P₂)     := have P₁.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₁,
                          have P₂.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₂,
                          P₁.find_calls_n ++ P₂.find_calls_n
| (prop.or P₁ P₂)      := have P₁.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₁,
                          have P₂.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₂,
                          P₁.find_calls_n ++ P₂.find_calls_n
| (prop.pre t₁ t₂)     := []
| (prop.pre₁ op t)     := []
| (prop.pre₂ op t₁ t₂) := []
| (prop.post t₁ t₂)    := []
| (prop.call t)        := []
| (prop.forallc x P)   := []
| (prop.exis x P)      := []

using_well_founded {
  rel_tac := λ _ _, `[exact find_calls_measure],
  dec_tac := tactic.assumption
}

-- performs one full instantiation for each of the triggers in the provided list
def prop.instantiate_with_all: prop → list calltrigger → prop
| P list.nil        := P
| P (list.cons t r) := (P.instantiate_with_n t).instantiate_with_all r
using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf $ λ s, s.2.sizeof⟩]
}

-- performs n rounds of instantiations. each round also involves a repeated lifting.
-- once all rounds are complete, remaining quantifiers and triggers in negative positions will be erased
def prop.instantiate_rep: prop → ℕ → vc
| P 0            := P.lift_all.erased_n
| P (nat.succ n) := have n < n + 1, from lt_of_add_one,
                    (P.lift_all.instantiate_with_all (P.lift_all.find_calls_n)).instantiate_rep n
using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf $ λ s, s.2⟩]
}

-- finds the maximum quantifier nesting level of a given proposition
def prop.max_nesting_level: prop → ℕ
| (prop.term t)        := 0
| (prop.not P)         := have P.sizeof < P.not.sizeof, from sizeof_prop_not,
                          P.max_nesting_level
| (prop.and P₁ P₂)     := have P₁.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₁,
                          have P₂.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₂,
                          max P₁.max_nesting_level P₂.max_nesting_level
| (prop.or P₁ P₂)      := have P₁.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₁,
                          have P₂.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₂,
                          max P₁.max_nesting_level P₂.max_nesting_level
| (prop.pre t₁ t₂)     := 0
| (prop.pre₁ op t)     := 0
| (prop.pre₂ op t₁ t₂) := 0
| (prop.post t₁ t₂)    := 0
| (prop.call t)        := 0
| (prop.forallc x P)   := have P.sizeof < (prop.forallc x P).sizeof, from sizeof_prop_forall,
                          nat.succ P.max_nesting_level
| (prop.exis x P)      := 0

using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf $ λ s, s.sizeof⟩],
  dec_tac := tactic.assumption
}

-- the main instantiation algorithm performs n rounds of instantiations
-- where n is the maximum quantifier nesting level and returns the erased proposition
def prop.instantiated_n (P: prop): vc := P.instantiate_rep P.max_nesting_level

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

 -- propositions without call triggers or quantifiers do not participate in instantiations
def no_instantiations(P: prop): Prop := (calls_p P = ∅) ∧ (calls_n P = ∅) ∧
                                        (quantifiers_p P = ∅) ∧ (quantifiers_n P = ∅)

-- set of calltriggers after substitution
def calltrigger.subst (σ: env) (c: calltrigger): calltrigger := ⟨term.subst_env σ c.x⟩
def calls_p_subst (σ: env) (P: prop): set calltrigger := (calltrigger.subst σ) '' calls_p P
def calls_n_subst (σ: env) (P: prop): set calltrigger := (calltrigger.subst σ) '' calls_n P

--  #############################
--  ### OPERATIONAL SEMANTICS ###
--  #############################

-- semantics of unary operators
def unop.apply: unop → value → option value
| unop.not value.true                  := value.false
| unop.not value.false                 := value.true
| unop.isInt (value.num _)             := value.true
| unop.isInt _                         := value.false
| unop.isBool value.true               := value.true
| unop.isBool value.false              := value.true
| unop.isBool _                        := value.false
| unop.isFunc (value.func _ _ _ _ _ _) := value.true
| unop.isFunc _                        := value.false
| _ _                                  := none

-- semantics of binary operators
def binop.apply: binop → value → value → option value
| binop.plus (value.num n₁) (value.num n₂)  := value.num (n₁ + n₂)
| binop.minus (value.num n₁) (value.num n₂) := value.num (n₁ - n₂)
| binop.times (value.num n₁) (value.num n₂) := value.num (n₁ * n₂)
| binop.div (value.num n₁) (value.num n₂)   := value.num (n₁ / n₂)
| binop.and value.true value.true           := value.true
| binop.and value.true value.false          := value.false
| binop.and value.false value.true          := value.false
| binop.and value.false value.false         := value.false
| binop.or value.true value.true            := value.true
| binop.or value.true value.false           := value.true
| binop.or value.false value.true           := value.true
| binop.or value.false value.false          := value.false
| binop.eq v₁ v₂                            := if v₁ = v₂ then value.true else value.false
| binop.lt (value.num n₁) (value.num n₂)    := if n₁ < n₂ then value.true else value.false
| _ _ _                                     := none

-- small-step stack-based semantics
inductive step : stack → stack → Prop
notation s₁ `⟶` s₂:100 := step s₁ s₂

| ctx {s s': stack} {R: spec} {σ: env} {y f x: var} {e: exp}:
    (s ⟶ s') →
    (s · [R, σ, letapp y = f[x] in e] ⟶ (s' · [R, σ, letapp y = f[x] in e]))

| tru {R: spec} {σ: env} {x: var} {e: exp}:
    (R, σ, lett x = true in e) ⟶ (R, σ[x↦value.true], e)

| fals {R: spec} {σ: env} {x: var} {e: exp}:
    (R, σ, letf x = false in e) ⟶ (R, σ[x↦value.false], e)

| num {R: spec} {σ: env} {x: var} {e: exp} {n: ℤ}:
    (R, σ, letn x = n in e) ⟶ (R, σ[x↦value.num n], e)

| closure {σ: env} {R' R S: spec} {f x: var} {e₁ e₂: exp}:
    (R', σ, letf f[x] req R ens S {e₁} in e₂) ⟶ 
    (R', σ[f↦value.func f x R S e₁ σ], e₂)

| unop {R: spec} {op: unop} {σ: env} {x y: var} {e: exp} {v₁ v: value}:
    (σ x = v₁) →
    (unop.apply op v₁ = v) →
    ((R, σ, letop y = op [x] in e) ⟶ (R, σ[y↦v], e))

| binop {R: spec} {op: binop} {σ: env} {x y z: var} {e: exp} {v₁ v₂ v: value}:
    (σ x = v₁) →
    (σ y = v₂) →
    (binop.apply op v₁ v₂ = v) →
    ((R, σ, letop2 z = op [x, y] in e) ⟶ (R, σ[z↦v], e))

| app {σ σ': env} {R' R S: spec} {f g x y z: var} {e e': exp} {v: value}:
    (σ f = value.func g z R S e σ') →
    (σ x = v) →
    ((R', σ, letapp y = f[x] in e') ⟶
    ((R, σ'[g↦value.func g z R S e σ'][z↦v], e) · [R', σ, letapp y = f[x] in e']))

| return {σ₁ σ₂ σ₃: env} {f g gx x y z: var} {R₁ R₂ R S: spec} {e e': exp} {v vₓ: value}:
    (σ₁ z = v) →
    (σ₂ f = value.func g gx R S e σ₃) →
    (σ₂ x = vₓ) →
    ((R₁, σ₁, exp.return z) · [R₂, σ₂, letapp y = f[x] in e'] ⟶
    (R₂, σ₂[y↦v], e'))

| ite_true {R: spec} {σ: env} {e₁ e₂: exp} {x: var}:
    (σ x = value.true) →
    ((R, σ, exp.ite x e₁ e₂) ⟶ (R, σ, e₁))

| ite_false {R: spec} {σ: env} {e₁ e₂: exp} {x: var}:
    (σ x = value.false) →
    ((R, σ, exp.ite x e₁ e₂) ⟶ (R, σ, e₂))

notation s₁ `⟶` s₂:100 := step s₁ s₂

-- transitive closure
inductive trans_step : stack → stack → Prop
notation s `⟶*` s':100 := trans_step s s'
| rfl {s: stack}          : s ⟶* s
| trans {s s' s'': stack} : (s ⟶* s') → (s' ⟶ s'') → (s ⟶* s'')

notation s `⟶*` s':100 := trans_step s s'

--  #######################################
--  ### VALIDTY OF LOGICAL PROPOSITIONS ###
--  #######################################

-- validity is axiomatized instead defined
-- see axioms below

constant valid : vc → Prop
notation `⊨` p: 20 := valid p
notation σ `⊨` p: 20 := valid (vc.subst_env σ p)
notation `⟪` P `⟫`: 100 := ∀ (σ: env), σ ⊨ (prop.instantiated_n P)

-- simple axioms for logical reasoning

axiom valid.tru:
  ⊨ value.true

axiom valid.and {P Q: vc}:
  (⊨ P) ∧ (⊨ Q)
  ↔
  ⊨ P ⋀ Q

axiom valid.or.left {P Q: vc}:
  (⊨ P) → 
  closed Q →
  ⊨ P ⋁ Q

axiom valid.or.right {P Q: vc}:
  closed P →
  (⊨ Q) → 
  ⊨ P ⋁ Q

axiom valid.or.elim {P Q: vc}:
  (⊨ P ⋁ Q)
  →
  (⊨ P) ∨ (⊨ Q)

axiom valid.not.term {t: term}:
  (⊨ term.unop unop.not t)
  ↔
  ⊨ vc.not t

-- no contradictions
axiom valid.contradiction {P: vc}:
  ¬ (⊨ P ⋀ P.not)

-- law of excluded middle
axiom valid.em {P: vc}:
  closed P →
  (⊨ P ⋁ P.not)

-- a term is valid if it equals true
axiom valid.eq.true {t: term}:
  ⊨ t
  ↔
  ⊨ value.true ≡ t

axiom valid.univ {x: var} {P: vc}:
  (∀v, ⊨ vc.subst x v P)
  ↔
  ⊨ vc.univ x P

-- unary and binary operators are decidable, so equalities with operators are decidable
axiom valid.unop {op: unop} {vₓ v: value}:
  unop.apply op vₓ = some v
  ↔
  ⊨ v ≡ term.unop op vₓ

axiom valid.binop {op: binop} {v₁ v₂ v: value}:
  binop.apply op v₁ v₂ = some v
  ↔
  ⊨ v ≡ term.binop op v₁ v₂

-- can write pre₁ and pre₂ to check domain of operators

axiom valid.pre₁ {vₓ: value} {op: unop}:
  option.is_some (unop.apply op vₓ)
  ↔
  ⊨ vc.pre₁ op vₓ

axiom valid.pre₂ {v₁ v₂: value} {op: binop}:
  option.is_some (binop.apply op v₁ v₂)
  ↔
  ⊨ vc.pre₂ op v₁ v₂

-- closedness assumption: only closed VCs can be validated

axiom valid.closed {P: vc}:
  (⊨ P) → closed P

--  #####################################
--  ### VERIFICATION RELATION (VCGEN) ###
--  #####################################

reserve infix `⊢`:10

-- verification of expressions

inductive exp.vcgen : prop → exp → propctx → Prop
notation P `⊢` e `:` Q : 10 := exp.vcgen P e Q

| tru {P: prop} {x: var} {e: exp} {Q: propctx}:
    x ∉ FV P →
    (P ⋀ x ≡ value.true ⊢ e : Q) →
    (P ⊢ lett x = true in e : propctx.exis x (x ≡ value.true ⋀ Q))

| fals {P: prop} {x: var} {e: exp} {Q: propctx}:
    x ∉ FV P →
    (P ⋀ x ≡ value.false ⊢ e : Q) →
    (P ⊢ letf x = false in e : propctx.exis x (x ≡ value.false ⋀ Q))

| num {P: prop} {x: var} {n: ℕ} {e: exp} {Q: propctx}:
    x ∉ FV P →
    (P ⋀ x ≡ value.num n ⊢ e : Q) →
    (P ⊢ letn x = n in e : propctx.exis x (x ≡ value.num n ⋀ Q))

| func {P: prop} {f x: var} {R S: spec} {e₁ e₂: exp} {Q₁ Q₂: propctx}:
    f ∉ FV P →
    x ∉ FV P →
    f ≠ x →
    x ∈ FV R.to_prop.to_vc →
    FV R.to_prop ⊆ FV P ∪ { f, x } →
    FV S.to_prop ⊆ FV P ∪ { f, x } →
    (P ⋀ spec.func f x R S ⋀ R ⊢ e₁ : Q₁) →
    (P ⋀ prop.func f x R (Q₁ (term.app f x) ⋀ S) ⊢ e₂ : Q₂) →
    ⟪prop.implies (P ⋀ spec.func f x R S ⋀ R ⋀ Q₁ (term.app f x)) S⟫ →
    (P ⊢ letf f[x] req R ens S {e₁} in e₂ : propctx.exis f (prop.func f x R (Q₁ (term.app f x) ⋀ S) ⋀ Q₂))

| unop {P: prop} {op: unop} {e: exp} {x y: var} {Q: propctx}:
    x ∈ FV P →
    y ∉ FV P →
    (P ⋀ y ≡ term.unop op x ⊢ e : Q) →
    ⟪ prop.implies P (prop.pre₁ op x) ⟫ →
    (P ⊢ letop y = op [x] in e : propctx.exis y (y ≡ term.unop op x ⋀ Q))

| binop {P: prop} {op: binop} {e: exp} {x y z: var} {Q: propctx}:
    x ∈ FV P →
    y ∈ FV P →
    z ∉ FV P →
    (P ⋀ z ≡ term.binop op x y ⊢ e : Q) →
    ⟪ prop.implies P (prop.pre₂ op x y) ⟫ →
    (P ⊢ letop2 z = op [x, y] in e : propctx.exis z (z ≡ term.binop op x y ⋀ Q))

| app {P: prop} {e: exp} {y f x: var} {Q: propctx}:
    f ∈ FV P →
    x ∈ FV P →
    y ∉ FV P →
    (P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⊢ e : Q) →
    ⟪ prop.implies (P ⋀ prop.call f x) (term.unop unop.isFunc f ⋀ prop.pre f x) ⟫ →
    (P ⊢ letapp y = f [x] in e : propctx.exis y (prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⋀ Q))

| ite {P: prop} {e₁ e₂: exp} {x: var} {Q₁ Q₂: propctx}:
    x ∈ FV P →
    (P ⋀ x ⊢ e₁ : Q₁) →
    (P ⋀ prop.not x ⊢ e₂ : Q₂) →
    ⟪ prop.implies P (term.unop unop.isBool x) ⟫ →
    (P ⊢ exp.ite x e₁ e₂ : propctx.implies x Q₁ ⋀ propctx.implies (prop.not x) Q₂)

| return {P: prop} {x: var}:
    x ∈ FV P →
    (P ⊢ exp.return x : x ≣ •)

notation P `⊢` e `:` Q : 10 := exp.vcgen P e Q

-- verification of environments/translation into logic

inductive env.vcgen : env → prop → Prop
notation `⊢` σ `:` Q : 10 := env.vcgen σ Q

| empty:
    ⊢ env.empty : value.true

| tru {σ: env} {x: var} {Q: prop}:
    x ∉ σ →
    (⊢ σ : Q) →
    (⊢ (σ[x ↦ value.true]) : Q ⋀ x ≡ value.true)

| fls {σ: env} {x: var} {Q: prop}:
    x ∉ σ →
    (⊢ σ : Q) →
    (⊢ (σ[x ↦ value.false]) : Q ⋀ x ≡ value.false)

| num {n: ℤ} {σ: env} {x: var} {Q: prop}:
    x ∉ σ →
    (⊢ σ : Q) →
    (⊢ (σ[x ↦ value.num n]) : Q ⋀ x ≡ value.num n)

| func {σ₁ σ₂: env} {f g x: var} {R S: spec} {e: exp} {Q₁ Q₂: prop} {Q₃: propctx}:
    f ∉ σ₁ →
    g ∉ σ₂ →
    x ∉ σ₂ →
    g ≠ x →
    (⊢ σ₁ : Q₁) →
    (⊢ σ₂ : Q₂) →
    x ∈ FV R.to_prop.to_vc →
    FV R.to_prop ⊆ FV Q₂ ∪ { g, x } →
    FV S.to_prop ⊆ FV Q₂ ∪ { g, x } →
    (Q₂ ⋀ spec.func g x R S ⋀ R ⊢ e : Q₃) →
    ⟪prop.implies (Q₂ ⋀ spec.func g x R S ⋀ R ⋀ Q₃ (term.app g x)) S⟫ →
    (⊢ (σ₁[f ↦ value.func g x R S e σ₂]) :
      (Q₁
       ⋀ f ≡ value.func g x R S e σ₂
       ⋀ prop.subst_env (σ₂[g↦value.func g x R S e σ₂]) (prop.func g x R (Q₃ (term.app g x) ⋀ S))))

notation `⊢` σ `:` Q : 10 := env.vcgen σ Q

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


--  #################################################################
--  ### AXIOMS ABOUT FUNCTION EXPRESSIONS, PRE and POSTCONDITIONS ###
--  #################################################################


-- The following equality axiom is non-standard and makes validity undecidable.
-- It is only used in the preservation proof of e-return and in no other lemmas.
-- The logic treats `f(x)` uninterpreted, so there is no way to derive it naturally.
-- However, given a complete evaluation derivation of a function call, we can add the
-- equality `f(x)=y` as new axiom for closed values f, x, y and the resulting set
-- of axioms is still sound due to deterministic evaluation.
axiom valid.app {vₓ v: value} {σ σ': env} {f x y: var} {R R' S: spec} {e: exp}:
  (R, σ[f↦value.func f x R S e σ][x↦vₓ], e) ⟶* (R', σ', exp.return y) →
  (σ' y = some v)
  →
  ⊨ v ≡ term.app (value.func f x R S e σ) vₓ

-- can write pre and post to extract pre- and postcondition of function values

axiom valid.pre.mp {vₓ: value} {σ: env} {f x: var} {R S: spec} {e: exp}:
  (σ[f↦value.func f x R S e σ][x↦vₓ] ⊨ R.to_prop.to_vc)
  →
  ⊨ vc.pre (value.func f x R S e σ) vₓ

axiom valid.pre.mpr {vₓ: value} {σ: env} {f x: var} {R S: spec} {e: exp}:
  (⊨ vc.pre (value.func f x R S e σ) vₓ)
  →
  (σ[f↦value.func f x R S e σ][x↦vₓ] ⊨ R.to_prop.to_vc)

axiom valid.post.mp {vₓ: value} {σ: env} {Q: prop} {Q₂: propctx} {f x: var} {R S: spec} {e: exp}:
  (⊢ σ : Q) →
  (Q ⋀ spec.func f x R S ⋀ R ⊢ e : Q₂) →
  (σ[f↦value.func f x R S e σ][x↦vₓ] ⊨ (Q₂ (term.app f x) ⋀ S.to_prop).to_vc)
  →
  (⊨ vc.post (value.func f x R S e σ) vₓ)

axiom valid.post.mpr {vₓ: value} {σ: env} {Q: prop} {Q₂: propctx} {f x: var} {R S: spec} {e: exp}:
  (⊢ σ : Q) →
  (Q ⋀ spec.func f x R S ⋀ R ⊢ e : Q₂) →
  (⊨ vc.post (value.func f x R S e σ) vₓ)
  →
  (σ[f↦value.func f x R S e σ][x↦vₓ] ⊨ (Q₂ (term.app f x) ⋀ S.to_prop).to_vc)
