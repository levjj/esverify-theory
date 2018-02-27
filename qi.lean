-- quantifier instantiation

import .syntax .notations .freevars .substitution

mutual def prop.erased, prop.erased_n

with prop.erased: prop → vc
| (prop.term t)        := vc.term t
| (prop.not P)         := have h: P.size + 1 < P.size + 2, from lt_of_add_one,
                          have P.size + 2 = 2 + P.size, from add_comm P.size 2,
                          have P.size + 1 < 2 + P.size, from this ▸ h,
                          vc.not P.erased_n
| (prop.and P₁ P₂)     := have P₁.size < (P₁ ⋀ P₂).size, from lt_of_add.left,
                          have P₂.size < (P₁ ⋀ P₂).size, from lt_of_add.right,
                          P₁.erased ⋀ P₂.erased
| (prop.or P₁ P₂)      := have P₁.size < (P₁ ⋁ P₂).size, from lt_of_add.left,
                          have P₂.size < (P₁ ⋁ P₂).size, from lt_of_add.right,
                          P₁.erased ⋁ P₂.erased
| (prop.pre t₁ t₂)     := vc.pre t₁ t₂
| (prop.pre₁ op t)     := vc.pre₁ op t
| (prop.pre₂ op t₁ t₂) := vc.pre₂ op t₁ t₂
| (prop.post t₁ t₂)    := vc.post t₁ t₂
| (prop.call _ _)      := vc.term value.true
| (prop.forallc x t P) := have P.size < (prop.forallc x t P).size, from lt_of_add_one,
                          vc.univ x P.erased
| (prop.exis x P)      := have P.size < P.size + 1, from lt_of_add_one,
                          vc.not (vc.univ x (vc.not P.erased))

with prop.erased_n: prop → vc
| (prop.term t)        := vc.term t
| (prop.not P)         := have h: P.size + 1 < P.size + 2, from lt_of_add_one,
                          have P.size + 2 = 2 + P.size, from add_comm P.size 2,
                          have P.size + 1 < 2 + P.size, from this ▸ h,
                          vc.not P.erased
| (prop.and P₁ P₂)     := have P₁.size < (P₁ ⋀ P₂).size, from lt_of_add.left,
                          have P₂.size < (P₁ ⋀ P₂).size, from lt_of_add.right,
                          P₁.erased_n ⋀ P₂.erased_n
| (prop.or P₁ P₂)      := have P₁.size < (P₁ ⋁ P₂).size, from lt_of_add.left,
                          have P₂.size < (P₁ ⋁ P₂ ).size, from lt_of_add.right,
                          P₁.erased_n ⋁ P₂.erased_n
| (prop.pre t₁ t₂)     := vc.pre t₁ t₂
| (prop.pre₁ op t)     := vc.pre₁ op t
| (prop.pre₂ op t₁ t₂) := vc.pre₂ op t₁ t₂
| (prop.post t₁ t₂)    := vc.post t₁ t₂
| (prop.call _ _)      := vc.term value.true
| (prop.forallc x t P) := vc.term value.true
| (prop.exis x P)      := have P.size < P.size + 1, from lt_of_add_one,
                          vc.not (vc.univ x (vc.not P.erased_n))

-- top-level calls and quantifiers in positive and negative positions
mutual inductive prop.has_call, prop.has_call_n

with prop.has_call: calltrigger → prop → Prop
| calltrigger {f x: term}                               : prop.has_call ⟨f, x⟩ (prop.call f x)
| not {P: prop} {c: calltrigger}                        : prop.has_call_n c P  → prop.has_call c P.not
| and₁ {P₁ P₂: prop} {c: calltrigger}                   : prop.has_call   c P₁ → prop.has_call c (P₁ ⋀ P₂)
| and₂ {P₁ P₂: prop} {c: calltrigger}                   : prop.has_call   c P₂ → prop.has_call c (P₁ ⋀ P₂)
| or₁ {P₁ P₂: prop} {c: calltrigger}                    : prop.has_call   c P₁ → prop.has_call c (P₁ ⋁ P₂)
| or₂ {P₁ P₂: prop} {c: calltrigger}                    : prop.has_call   c P₂ → prop.has_call c (P₁ ⋁ P₂)
| exis {y: var} {P: prop} {c: calltrigger}              : prop.has_call   c P  → prop.has_call c (prop.exis y P)

with prop.has_call_n: calltrigger → prop → Prop
| calltrigger {f x: term}                               : prop.has_call_n ⟨f, x⟩ (prop.call f x)
| not {P: prop} {c: calltrigger}                        : prop.has_call   c P  → prop.has_call_n c P.not
| and₁ {P₁ P₂: prop} {c: calltrigger}                   : prop.has_call_n c P₁ → prop.has_call_n c (P₁ ⋀ P₂)
| and₂ {P₁ P₂: prop} {c: calltrigger}                   : prop.has_call_n c P₂ → prop.has_call_n c (P₁ ⋀ P₂)
| or₁ {P₁ P₂: prop} {c: calltrigger}                    : prop.has_call_n c P₁ → prop.has_call_n c (P₁ ⋁ P₂)
| or₂ {P₁ P₂: prop} {c: calltrigger}                    : prop.has_call_n c P₂ → prop.has_call_n c (P₁ ⋁ P₂)
| exis {y: var} {P: prop} {c: calltrigger}              : prop.has_call_n c P  → prop.has_call_n c (prop.exis y P)

def calls (P: prop): set calltrigger := λc, prop.has_call c P
def calls_n (P: prop): set calltrigger := λc, prop.has_call_n c P

mutual inductive prop.has_quantifier, prop.has_quantifier_n

with prop.has_quantifier: callquantifier → prop → Prop
| callquantifier {x: var} {f: term} {P: prop} : prop.has_quantifier ⟨f, x, P⟩ (prop.forallc x f P)
| not {P: prop} {q: callquantifier}           : prop.has_quantifier_n q P  → prop.has_quantifier q P.not
| and₁ {P₁ P₂: prop} {q: callquantifier}      : prop.has_quantifier   q P₁ → prop.has_quantifier q (P₁ ⋀ P₂)
| and₂ {P₁ P₂: prop} {q: callquantifier}      : prop.has_quantifier   q P₂ → prop.has_quantifier q (P₁ ⋀ P₂)
| or₁ {P₁ P₂: prop} {q: callquantifier}       : prop.has_quantifier   q P₁ → prop.has_quantifier q (P₁ ⋁ P₂)
| or₂ {P₁ P₂: prop} {q: callquantifier}       : prop.has_quantifier   q P₂ → prop.has_quantifier q (P₁ ⋁ P₂)
| exis {y: var} {P: prop} {q: callquantifier} : prop.has_quantifier   q P  → prop.has_quantifier q (prop.exis y P)

with prop.has_quantifier_n: callquantifier → prop → Prop
| callquantifier {x: var} {f: term} {P: prop} : prop.has_quantifier_n ⟨f, x, P⟩ (prop.forallc x f P)
| not {P: prop} {q: callquantifier}           : prop.has_quantifier   q P  → prop.has_quantifier_n q P.not
| and₁ {P₁ P₂: prop} {q: callquantifier}      : prop.has_quantifier_n q P₁ → prop.has_quantifier_n q (P₁ ⋀ P₂)
| and₂ {P₁ P₂: prop} {q: callquantifier}      : prop.has_quantifier_n q P₂ → prop.has_quantifier_n q (P₁ ⋀ P₂)
| or₁ {P₁ P₂: prop} {q: callquantifier}       : prop.has_quantifier_n q P₁ → prop.has_quantifier_n q (P₁ ⋁ P₂)
| or₂ {P₁ P₂: prop} {q: callquantifier}       : prop.has_quantifier_n q P₂ → prop.has_quantifier_n q (P₁ ⋁ P₂)
| exis {y: var} {P: prop} {q: callquantifier} : prop.has_quantifier_n q P  → prop.has_quantifier_n q (prop.exis y P)

def quantifiers (P: prop): set callquantifier := λc, has_quantifier c P
def quantifiers_n (P: prop): set callquantifier := λc, has_quantifier_n c P

 -- propositions without call triggers or quantifiers do not participate in instantiations
def no_instantiations(P: prop): Prop := (calls P = ∅) ∧ (calls_n P = ∅) ∧ (quantifiers P = ∅) ∧ (quantifiers_n P = ∅)

def calltrigger.subst (σ: env) (c: calltrigger): calltrigger := ⟨term.subst_env σ c.f, term.subst_env σ c.x⟩

@[reducible]
def calls_env (σ: env) (P: prop): set calltrigger := (calltrigger.subst σ) '' calls P

@[reducible]
def calls_n_env (σ: env) (P: prop): set calltrigger := (calltrigger.subst σ) '' calls_n P

lemma quantifiers_smaller_than_prop {f: term} {x: var} {P Q: prop}:
     ((callquantifier.mk f x P ∈ quantifiers Q) → P.size < Q.size) ∧
     ((callquantifier.mk f x P ∈ quantifiers_n Q) → P.size < Q.size) :=
begin
  induction Q,
  case prop.term t {
    split,

    intro fxp_in_Q,
    cases fxp_in_Q,

    intro fxp_in_Q,
    cases fxp_in_Q
  },
  case prop.not P₁ P₁_ih {
    split,

    intro fxp_in_Q,
    cases fxp_in_Q with a,
    have h: prop.size P < prop.size P₁, from P₁_ih.right a,
    have h2: prop.size P₁ < prop.size P₁.not, from lt_of_add_one,
    from lt.trans h h2,

    intro fxp_in_Q,
    cases fxp_in_Q with a,
    have h: prop.size P < prop.size P₁, from P₁_ih.left a,
    have h2: prop.size P₁ < prop.size P₁.not, from lt_of_add_one,
    from lt.trans h h2
  },
  case prop.and P₁ P₂ P₁_ih P₂_ih {
    split,

    intro fxp_in_Q,
    cases fxp_in_Q with a,
    have h: prop.size P < prop.size P₁, from P₁_ih.left a,
    have h2: prop.size P₁ < prop.size (P₁ ⋀ P₂), from lt_of_add.left,
    from lt.trans h h2,
    have h: prop.size P < prop.size P₂, from P₂_ih.left a,
    have h2: prop.size P₂ < prop.size (P₁ ⋀ P₂), from lt_of_add.right,
    from lt.trans h h2,

    intro fxp_in_Q,
    cases fxp_in_Q with a,
    have h: prop.size P < prop.size P₁, from P₁_ih.right a,
    have h2: prop.size P₁ < prop.size (P₁ ⋀ P₂), from lt_of_add.left,
    from lt.trans h h2,
    have h: prop.size P < prop.size P₂, from P₂_ih.right a,
    have h2: prop.size P₂ < prop.size (P₁ ⋀ P₂), from lt_of_add.right,
    from lt.trans h h2
  },
  case prop.or P₁ P₂ P₁_ih P₂_ih {
    split,

    intro fxp_in_Q,
    cases fxp_in_Q with a,
    have h: prop.size P < prop.size P₁, from P₁_ih.left a,
    have h2: prop.size P₁ < prop.size (P₁ ⋁ P₂), from lt_of_add.left,
    from lt.trans h h2,
    have h: prop.size P < prop.size P₂, from P₂_ih.left a,
    have h2: prop.size P₂ < prop.size (P₁ ⋁ P₂), from lt_of_add.right,
    from lt.trans h h2,

    intro fxp_in_Q,
    cases fxp_in_Q with a,
    have h: prop.size P < prop.size P₁, from P₁_ih.right a,
    have h2: prop.size P₁ < prop.size (P₁ ⋁ P₂), from lt_of_add.left,
    from lt.trans h h2,
    have h: prop.size P < prop.size P₂, from P₂_ih.right a,
    have h2: prop.size P₂ < prop.size (P₁ ⋁ P₂), from lt_of_add.right,
    from lt.trans h h2
  },
  case prop.pre {
    split,

    intro fxp_in_Q,
    cases fxp_in_Q,

    intro fxp_in_Q,
    cases fxp_in_Q
  },
  case prop.pre₁ {
    split,

    intro fxp_in_Q,
    cases fxp_in_Q,

    intro fxp_in_Q,
    cases fxp_in_Q
  },
  case prop.pre₂ {
    split,

    intro fxp_in_Q,
    cases fxp_in_Q,

    intro fxp_in_Q,
    cases fxp_in_Q
  },
  case prop.post {
    split,

    intro fxp_in_Q,
    cases fxp_in_Q,

    intro fxp_in_Q,
    cases fxp_in_Q
  },
  case prop.call {
    split,

    intro fxp_in_Q,
    cases fxp_in_Q,

    intro fxp_in_Q,
    cases fxp_in_Q
  },
  case prop.forallc y t P₁ P₁_ih {
    split,

    intro fxp_in_Q,
    cases fxp_in_Q,
    from lt_of_add_one,

    intro fxp_in_Q,
    cases fxp_in_Q,
    from lt_of_add_one
  },
  case prop.exis y P₁ P₁_ih {
    split,

    intro fxp_in_Q,
    cases fxp_in_Q with a,
    have h: prop.size P < prop.size P₁, from P₁_ih.left a,
    have h2: prop.size P₁ < prop.size P₁.not, from lt_of_add_one,
    from lt.trans h h2,

    intro fxp_in_Q,
    cases fxp_in_Q with a,
    have h: prop.size P < prop.size P₁, from P₁_ih.right a,
    have h2: prop.size P₁ < prop.size P₁.not, from lt_of_add_one,
    from lt.trans h h2
  }
end

def dominates': prop → prop → env → Prop
| P' P σ :=
    (σ ⊨ vc.implies P.instantiated_n P'.instantiated_n) ∧
    (calls_env σ P = calls_env σ P') ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v])))

-- given a environment σ, P dominates P' if P implies P' and
-- P has matching or stronger triggers and quantifiers than P'
@[reducible]
def dominates (σ: env) (P P': prop): Prop := dominates' P' P σ

-- axioms about instantiation

axiom instantiated.forallc {x: var} {t: term} {P: prop}:
  (prop.forallc x t P).instantiated = vc.univ x P.instantiated

axiom not_dist_instantiated {P: prop}:
  P.not.instantiated = P.instantiated_n.not

axiom not_dist_instantiated_n {P: prop}:
  P.not.instantiated_n = P.instantiated.not

axiom and_dist_of_no_instantiations {P Q: prop}:
  no_instantiations Q → ((P ⋀ Q).instantiated = (P.instantiated ⋀ Q.erased))

axiom or_dist_of_no_instantiations {P Q: prop}:
  no_instantiations Q → ((P ⋁ Q).instantiated = (P.instantiated ⋁ Q.erased))

axiom and_dist_of_no_instantiations_n {P Q: prop}:
  no_instantiations Q → ((P ⋀ Q).instantiated_n = (P.instantiated_n ⋀ Q.erased))

axiom or_dist_of_no_instantiations_n {P Q: prop}:
  no_instantiations Q → ((P ⋁ Q).instantiated_n = (P.instantiated_n ⋁ Q.erased))

axiom free_in_erased_of_free_in_instantiated {P: prop} {x: var}:
   x ∈ FV P.instantiated → x ∈ FV P.erased

axiom instantiated_distrib_subst {P: prop} {x: var} {v: value}:
  vc.subst x v P.instantiated = (prop.subst x v P).instantiated

axiom instantiated_n_distrib_subst {P: prop} {x: var} {v: value}:
  vc.subst x v P.instantiated_n = (prop.subst x v P).instantiated_n

--  inst(P)   ⇒   inst_n(P)
--         ⇘    ⇗  
--     ⇑      P      ⇓
--         ⇗    ⇘ 
-- erased(P)  ⇒  erased_n(P)

axiom valid_env.instantiated_of_erased {σ: env} {P: prop}:
  (σ ⊨ P.erased) →
  σ ⊨ P.instantiated

axiom valid_env.instantiated_n_of_instantiated {σ: env} {P: prop}:
  (σ ⊨ P.instantiated) →
  σ ⊨ P.instantiated_n

axiom valid_env.erased_n_of_instantiated_n {σ: env} {P: prop}:
  (σ ⊨ P.instantiated_n) →
  σ ⊨ P.erased_n

-- if a conjunction or disjunciton is valid without cross-instantiations
-- then it remains valid, as potential new instantiations are in negative positions
axiom valid_env.instantiated_and {σ: env} {P Q: prop}:
  (σ ⊨ P.instantiated ⋀ Q.instantiated) →
  σ ⊨ (P ⋀ Q).instantiated

axiom valid_env.instantiated_or {σ: env} {P Q: prop}:
  (σ ⊨ P.instantiated ⋁ Q.instantiated) →
  σ ⊨ (P ⋁ Q).instantiated

-- if P and P' have the same substituted triggers and every quantifier
-- in P' is dominated by a quantifier in P then any
-- any cross-instantiations with an arbitrary propostion Q are also the same,
-- so if (P') implies (P) without cross-instantiations,
-- then (P' ∧ Q) implies (P ∧ Q) without cross-instantiations
axiom valid_env.strengthen_and_with_dominating_instantiations {σ: env} {P P' Q: prop}:
  dominates σ P P' →
  σ ⊨ vc.implies (P ⋀ Q).instantiated_n (P' ⋀ Q).instantiated_n

axiom valid_env.or_not_dist_with_instantiations {σ: env} {P Q: prop}:
  (σ ⊨ (P ⋁ Q).not.instantiated_n) ↔ (σ ⊨ (P.not ⋀ Q.not).instantiated_n)

axiom valid_env.and_comm_with_instantiations {σ: env} {P₁ P₂ P₃: prop}:
  (σ ⊨ (P₁ ⋀ P₂ ⋀ P₃).instantiated_n) ↔ (σ ⊨ ((P₁ ⋀ P₂) ⋀ P₃).instantiated_n)

-- lemmas

lemma valid.instantiated_of_erased {P: prop}: (⊨ P.erased) → ⊨ P.instantiated :=
  assume h: ⊨ P.erased,
  have P.erased = vc.subst_env env.empty P.erased, by unfold vc.subst_env,
  have env.empty ⊨ P.erased, from this ▸ h,
  have h2: env.empty ⊨ P.instantiated, from valid_env.instantiated_of_erased this,
  have  vc.subst_env env.empty P.instantiated = P.instantiated, by unfold vc.subst_env,
  show ⊨ P.instantiated, from this ▸ h2

lemma valid.instantiated_n_of_instantiated {P: prop}: (⊨ P.instantiated) → ⊨ P.instantiated_n :=
  assume h: ⊨ P.instantiated,
  have P.instantiated = vc.subst_env env.empty P.instantiated, by unfold vc.subst_env,
  have env.empty ⊨ P.instantiated, from this ▸ h,
  have h2: env.empty ⊨ P.instantiated_n, from valid_env.instantiated_n_of_instantiated this,
  have  vc.subst_env env.empty P.instantiated_n = P.instantiated_n, by unfold vc.subst_env,
  show ⊨ P.instantiated_n, from this ▸ h2

lemma valid.erased_n_of_instantiated_n {P: prop}: (⊨ P.instantiated_n) → ⊨ P.erased_n :=
  assume h: ⊨ P.instantiated_n,
  have P.instantiated_n = vc.subst_env env.empty P.instantiated_n, by unfold vc.subst_env,
  have env.empty ⊨ P.instantiated_n, from this ▸ h,
  have h2: env.empty ⊨ P.erased_n, from valid_env.erased_n_of_instantiated_n this,
  have vc.subst_env env.empty P.erased_n = P.erased_n, by unfold vc.subst_env,
  show ⊨ P.erased_n, from this ▸ h2

lemma valid.instantiated_and {P Q: prop}:
      (⊨ P.instantiated ⋀ Q.instantiated) → ⊨ (P ⋀ Q).instantiated :=
  assume h: ⊨ (P.instantiated ⋀ Q.instantiated),
  have (P.instantiated ⋀ Q.instantiated) = vc.subst_env env.empty (P.instantiated ⋀ Q.instantiated),
  by unfold vc.subst_env,
  have env.empty ⊨ (P.instantiated ⋀ Q.instantiated), from this ▸ h,
  have h2: env.empty ⊨ (P ⋀ Q).instantiated, from valid_env.instantiated_and this,
  have vc.subst_env env.empty (P ⋀ Q).instantiated = (P ⋀ Q).instantiated, by unfold vc.subst_env,
  show ⊨ (P ⋀ Q).instantiated, from this ▸ h2

lemma valid.instantiated_or {P Q: prop}:
      (⊨ P.instantiated ⋁ Q.instantiated) → ⊨ (P ⋁ Q).instantiated :=
  assume h: ⊨ (P.instantiated ⋁ Q.instantiated),
  have (P.instantiated ⋁ Q.instantiated) = vc.subst_env env.empty (P.instantiated ⋁ Q.instantiated),
  by unfold vc.subst_env,
  have env.empty ⊨ (P.instantiated ⋁ Q.instantiated), from this ▸ h,
  have h2: env.empty ⊨ (P ⋁ Q).instantiated, from valid_env.instantiated_or this,
  have vc.subst_env env.empty (P ⋁ Q).instantiated = (P ⋁ Q).instantiated, by unfold vc.subst_env,
  show ⊨ (P ⋁ Q).instantiated, from this ▸ h2

lemma valid.instantiated_implies {P Q: prop}:
      (⊨ vc.implies P.instantiated_n Q.instantiated) → ⊨ (prop.implies P Q).instantiated :=
  assume : ⊨ (vc.implies P.instantiated_n Q.instantiated),
  have h1: ⊨ (vc.or P.instantiated_n.not Q.instantiated), from this,
  have P.not.instantiated = P.instantiated_n.not, from not_dist_instantiated,
  have ⊨ (vc.or P.not.instantiated Q.instantiated), from this.symm ▸ h1,
  have ⊨ (prop.or P.not Q).instantiated, from valid.instantiated_or this,
  show ⊨ (prop.implies P Q).instantiated, from this

lemma dominates_of {σ: env} {P P': prop}:
    (σ ⊨ vc.implies P.instantiated_n P'.instantiated_n) →
    (calls_env σ P = calls_env σ P') →
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v]))) →
    dominates σ P P' :=
  
  assume h_impl: σ ⊨ vc.implies P.instantiated_n P'.instantiated_n,
  assume h_calls: calls_env σ P = calls_env σ P',
  assume h_quantifiers:
    ∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v])),
  
  have h: 
    ((σ ⊨ vc.implies P.instantiated_n P'.instantiated_n) ∧
    (calls_env σ P = calls_env σ P') ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v])))),
  from ⟨h_impl, ⟨h_calls, h_quantifiers⟩⟩,
  have
    dominates' P' P σ = (
    ((σ ⊨ vc.implies P.instantiated_n P'.instantiated_n) ∧
    (calls_env σ P = calls_env σ P') ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v]))))),
  by unfold1 dominates',
  have dominates' P' P σ, from this.symm ▸ h,
  show dominates σ P P', from this

lemma instantiated_distrib_subst_env {P: prop} {σ: env}:
      vc.subst_env σ P.instantiated = (prop.subst_env σ P).instantiated :=
begin
  induction σ with σ' x v ih,

  show (vc.subst_env env.empty (prop.instantiated P) = prop.instantiated (prop.subst_env env.empty P)),
  by calc
        vc.subst_env env.empty (prop.instantiated P) 
      = P.instantiated : by unfold vc.subst_env
  ... = (prop.subst_env env.empty P).instantiated : by unfold prop.subst_env,

  show (vc.subst_env (σ'[x↦v]) (prop.instantiated P) = prop.instantiated (prop.subst_env (σ'[x↦v]) P)),
  by calc
        vc.subst_env (σ'[x↦v]) P.instantiated
      = vc.subst x v (vc.subst_env σ' P.instantiated) : by unfold vc.subst_env
  ... = vc.subst x v (prop.subst_env σ' P).instantiated : by rw[ih]
  ... = (prop.subst x v (prop.subst_env σ' P)).instantiated : instantiated_distrib_subst
  ... = (prop.subst_env (σ'[x↦v]) P).instantiated : by unfold prop.subst_env

end

lemma instantiated_n_distrib_subst_env {P: prop} {σ: env}:
      vc.subst_env σ P.instantiated_n = (prop.subst_env σ P).instantiated_n :=
begin
  induction σ with σ' x v ih,

  show (vc.subst_env env.empty (prop.instantiated_n P) = prop.instantiated_n (prop.subst_env env.empty P)),
  by calc
        vc.subst_env env.empty (prop.instantiated_n P) 
      = P.instantiated_n : by unfold vc.subst_env
  ... = (prop.subst_env env.empty P).instantiated_n : by unfold prop.subst_env,

  show (vc.subst_env (σ'[x↦v]) (prop.instantiated_n P) = prop.instantiated_n (prop.subst_env (σ'[x↦v]) P)),
  by calc
        vc.subst_env (σ'[x↦v]) P.instantiated_n
      = vc.subst x v (vc.subst_env σ' P.instantiated_n) : by unfold vc.subst_env
  ... = vc.subst x v (prop.subst_env σ' P).instantiated_n : by rw[ih]
  ... = (prop.subst x v (prop.subst_env σ' P)).instantiated_n : instantiated_n_distrib_subst
  ... = (prop.subst_env (σ'[x↦v]) P).instantiated_n : by unfold prop.subst_env

end

lemma prop.has_call.term.inv {c: calltrigger} {t: term}: c ∉ calls t :=
  assume t_has_call: has_call c t,
  show «false», by cases t_has_call

lemma prop.has_call.not.inv {c: calltrigger} {P: prop}: c ∈ calls P.not → c ∈ calls_n P :=
  assume not_has_call: c ∈ calls P.not,
  begin
    cases not_has_call,
    from a
  end

lemma prop.has_call.and.inv {c: calltrigger} {P₁ P₂: prop}: c ∈ calls (P₁ ⋀ P₂) → c ∈ calls P₁ ∨ c ∈ calls P₂ :=
  assume and_has_call: c ∈ calls (P₁ ⋀ P₂),
  begin
    cases and_has_call,
    show c ∈ calls P₁ ∨ c ∈ calls P₂, from or.inl a,
    show c ∈ calls P₁ ∨ c ∈ calls P₂, from or.inr a
  end

lemma prop.has_call.or.inv {c: calltrigger} {P₁ P₂: prop}: c ∈ calls (P₁ ⋁ P₂) → c ∈ calls P₁ ∨ c ∈ calls P₂ :=
  assume or_has_call: c ∈ calls (P₁ ⋁ P₂),
  begin
    cases or_has_call,
    show c ∈ calls P₁ ∨ c ∈ calls P₂, from or.inl a,
    show c ∈ calls P₁ ∨ c ∈ calls P₂, from or.inr a
  end

lemma prop.has_call.pre₁.inv {c: calltrigger} {op: unop} {t: term}: c ∉ calls (prop.pre₁ op t) :=
  assume pre_has_call: c ∈ calls (prop.pre₁ op t),
  show «false», by cases pre_has_call

lemma prop.has_call.pre₂.inv {c: calltrigger} {op: binop} {t₁ t₂: term}: c ∉ calls (prop.pre₂ op t₁ t₂) :=
  assume pre_has_call: c ∈ calls (prop.pre₂ op t₁ t₂),
  show «false», by cases pre_has_call

lemma prop.has_call.pre.inv {c: calltrigger} {t₁ t₂: term}: c ∉ calls (prop.pre t₁ t₂) :=
  assume pre_has_call: c ∈ calls (prop.pre t₁ t₂),
  show «false», by cases pre_has_call

lemma prop.has_call.post.inv {c: calltrigger} {t₁ t₂: term}: c ∉ calls (prop.post t₁ t₂) :=
  assume post_has_call: c ∈ calls (prop.post t₁ t₂),
  show «false», by cases post_has_call

lemma prop.has_call.forallc.inv {c: calltrigger} {x: var} {t: term} {P: prop}:
      c ∉ calls (prop.forallc x t P) :=
  assume forall_has_call: c ∈ calls (prop.forallc x t P),
  begin
    cases forall_has_call
  end

lemma prop.has_call.exis.inv {c: calltrigger} {x: var} {P: prop}: c ∈ calls (prop.exis x P) → c ∈ calls P :=
  assume exis_has_call: c ∈ calls (prop.exis x P),
  begin
    cases exis_has_call,
    from a
  end

lemma prop.has_call_n.term.inv {c: calltrigger} {t: term}: c ∉ calls_n t :=
  assume t_has_call_n: has_call_n c t,
  show «false», by cases t_has_call_n

lemma prop.has_call_n.not.inv {c: calltrigger} {P: prop}: c ∈ calls_n P.not → c ∈ calls P :=
  assume not_has_call_n: c ∈ calls_n P.not,
  begin
    cases not_has_call_n,
    from a
  end

lemma prop.has_call_n.and.inv {c: calltrigger} {P₁ P₂: prop}: c ∈ calls_n (P₁ ⋀ P₂) → c ∈ calls_n P₁ ∨ c ∈ calls_n P₂ :=
  assume and_has_call_n: c ∈ calls_n (P₁ ⋀ P₂),
  begin
    cases and_has_call_n,
    show c ∈ calls_n P₁ ∨ c ∈ calls_n P₂, from or.inl a,
    show c ∈ calls_n P₁ ∨ c ∈ calls_n P₂, from or.inr a
  end

lemma prop.has_call_n.or.inv {c: calltrigger} {P₁ P₂: prop}: c ∈ calls_n (P₁ ⋁ P₂) → c ∈ calls_n P₁ ∨ c ∈ calls_n P₂ :=
  assume or_has_call_n: c ∈ calls_n (P₁ ⋁ P₂),
  begin
    cases or_has_call_n,
    show c ∈ calls_n P₁ ∨ c ∈ calls_n P₂, from or.inl a,
    show c ∈ calls_n P₁ ∨ c ∈ calls_n P₂, from or.inr a
  end

lemma prop.has_call_n.pre₁.inv {c: calltrigger} {op: unop} {t: term}: c ∉ calls_n (prop.pre₁ op t) :=
  assume pre_has_call_n: c ∈ calls_n (prop.pre₁ op t),
  show «false», by cases pre_has_call_n

lemma prop.has_call_n.pre₂.inv {c: calltrigger} {op: binop} {t₁ t₂: term}: c ∉ calls_n (prop.pre₂ op t₁ t₂) :=
  assume pre_has_call_n: c ∈ calls_n (prop.pre₂ op t₁ t₂),
  show «false», by cases pre_has_call_n

lemma prop.has_call_n.pre.inv {c: calltrigger} {t₁ t₂: term}: c ∉ calls_n (prop.pre t₁ t₂) :=
  assume pre_has_call_n: c ∈ calls_n (prop.pre t₁ t₂),
  show «false», by cases pre_has_call_n

lemma prop.has_call_n.post.inv {c: calltrigger} {t₁ t₂: term}: c ∉ calls_n (prop.post t₁ t₂) :=
  assume post_has_call_n: c ∈ calls_n (prop.post t₁ t₂),
  show «false», by cases post_has_call_n

lemma prop.has_call_n.forallc.inv {c: calltrigger} {x: var} {t: term} {P: prop}:
      c ∉ calls_n (prop.forallc x t P) :=
  assume forall_has_call_n: c ∈ calls_n (prop.forallc x t P),
  begin
    cases forall_has_call_n
  end

lemma prop.has_call_n.exis.inv {c: calltrigger} {x: var} {P: prop}: c ∈ calls_n (prop.exis x P) → c ∈ calls_n P :=
  assume exis_has_call_n: c ∈ calls_n (prop.exis x P),
  begin
    cases exis_has_call_n,
    from a
  end

lemma prop.has_quantifier.term.inv {q: callquantifier} {t: term}: q ∉ quantifiers t :=
  assume t_has_quantifier: prop.has_quantifier q t,
  show «false», by cases t_has_quantifier

lemma prop.has_quantifier.not.inv {q: callquantifier} {P: prop}: q ∈ quantifiers P.not → q ∈ quantifiers_n P :=
  assume not_has_quantifier: q ∈ quantifiers P.not,
  begin
    cases not_has_quantifier with a,
    from a
  end

lemma prop.has_quantifier.and.inv {q: callquantifier} {P₁ P₂: prop}:
      q ∈ quantifiers (P₁ ⋀ P₂) → q ∈ quantifiers P₁ ∨ q ∈ quantifiers P₂ :=
  assume and_has_quantifier: q ∈ quantifiers (P₁ ⋀ P₂),
  begin
    cases and_has_quantifier,
    show q ∈ quantifiers P₁ ∨ q ∈ quantifiers P₂, from or.inl a,
    show q ∈ quantifiers P₁ ∨ q ∈ quantifiers P₂, from or.inr a
  end

lemma prop.has_quantifier.or.inv {q: callquantifier} {P₁ P₂: prop}:
      q ∈ quantifiers (P₁ ⋁ P₂) → q ∈ quantifiers P₁ ∨ q ∈ quantifiers P₂ :=
  assume or_has_quantifier: q ∈ quantifiers (P₁ ⋁ P₂),
  begin
    cases or_has_quantifier,
    show q ∈ quantifiers P₁ ∨ q ∈ quantifiers P₂, from or.inl a,
    show q ∈ quantifiers P₁ ∨ q ∈ quantifiers P₂, from or.inr a
  end

lemma prop.has_quantifier.pre₁.inv {q: callquantifier} {op: unop} {t: term}: q ∉ quantifiers (prop.pre₁ op t) :=
  assume pre_has_quantifier: q ∈ quantifiers (prop.pre₁ op t),
  show «false», by cases pre_has_quantifier

lemma prop.has_quantifier.pre₂.inv {q: callquantifier} {op: binop} {t₁ t₂: term}: q ∉ quantifiers (prop.pre₂ op t₁ t₂) :=
  assume pre_has_quantifier: q ∈ quantifiers (prop.pre₂ op t₁ t₂),
  show «false», by cases pre_has_quantifier

lemma prop.has_quantifier.pre.inv {q: callquantifier} {t₁ t₂: term}: q ∉ quantifiers (prop.pre t₁ t₂) :=
  assume pre_has_quantifier: q ∈ quantifiers (prop.pre t₁ t₂),
  show «false», by cases pre_has_quantifier

lemma prop.has_quantifier.post.inv {q: callquantifier} {t₁ t₂: term}: q ∉ quantifiers (prop.post t₁ t₂) :=
  assume post_has_quantifier: q ∈ quantifiers (prop.post t₁ t₂),
  show «false», by cases post_has_quantifier

lemma prop.has_quantifier.forallc.inv {q: callquantifier} {x: var} {t: term} {P: prop}:
      q ∈ quantifiers (prop.forallc x t P) → (q = ⟨t, x, P⟩) ∨ q ∈ quantifiers P :=
  assume forall_has_quantifier: q ∈ quantifiers (prop.forallc x t P),
  begin
    cases forall_has_quantifier,
    from or.inl rfl
  end

lemma prop.has_quantifier.exis.inv {q: callquantifier} {x: var} {P: prop}:
      q ∈ quantifiers (prop.exis x P) → q ∈ quantifiers P :=
  assume exis_has_quantifier: q ∈ quantifiers (prop.exis x P),
  begin
    cases exis_has_quantifier,
    from a
  end

lemma prop.has_quantifier_n.term.inv {q: callquantifier} {t: term}: q ∉ quantifiers_n t :=
  assume t_has_quantifier_n: prop.has_quantifier_n q t,
  show «false», by cases t_has_quantifier_n

lemma prop.has_quantifier_n.not.inv {q: callquantifier} {P: prop}: q ∈ quantifiers_n P.not → q ∈ quantifiers P :=
  assume not_has_quantifier_n: q ∈ quantifiers_n P.not,
  begin
    cases not_has_quantifier_n with a,
    from a
  end

lemma prop.has_quantifier_n.and.inv {q: callquantifier} {P₁ P₂: prop}:
      q ∈ quantifiers_n (P₁ ⋀ P₂) → q ∈ quantifiers_n P₁ ∨ q ∈ quantifiers_n P₂ :=
  assume and_has_quantifier_n: q ∈ quantifiers_n (P₁ ⋀ P₂),
  begin
    cases and_has_quantifier_n,
    show q ∈ quantifiers_n P₁ ∨ q ∈ quantifiers_n P₂, from or.inl a,
    show q ∈ quantifiers_n P₁ ∨ q ∈ quantifiers_n P₂, from or.inr a
  end

lemma prop.has_quantifier_n.or.inv {q: callquantifier} {P₁ P₂: prop}:
      q ∈ quantifiers_n (P₁ ⋁ P₂) → q ∈ quantifiers_n P₁ ∨ q ∈ quantifiers_n P₂ :=
  assume or_has_quantifier_n: q ∈ quantifiers_n (P₁ ⋁ P₂),
  begin
    cases or_has_quantifier_n,
    show q ∈ quantifiers_n P₁ ∨ q ∈ quantifiers_n P₂, from or.inl a,
    show q ∈ quantifiers_n P₁ ∨ q ∈ quantifiers_n P₂, from or.inr a
  end

lemma prop.has_quantifier_n.pre₁.inv {q: callquantifier} {op: unop} {t: term}: q ∉ quantifiers_n (prop.pre₁ op t) :=
  assume pre_has_quantifier_n: q ∈ quantifiers_n (prop.pre₁ op t),
  show «false», by cases pre_has_quantifier_n

lemma prop.has_quantifier_n.pre₂.inv {q: callquantifier} {op: binop} {t₁ t₂: term}: q ∉ quantifiers_n (prop.pre₂ op t₁ t₂) :=
  assume pre_has_quantifier_n: q ∈ quantifiers_n (prop.pre₂ op t₁ t₂),
  show «false», by cases pre_has_quantifier_n

lemma prop.has_quantifier_n.pre.inv {q: callquantifier} {t₁ t₂: term}: q ∉ quantifiers_n (prop.pre t₁ t₂) :=
  assume pre_has_quantifier_n: q ∈ quantifiers_n (prop.pre t₁ t₂),
  show «false», by cases pre_has_quantifier_n

lemma prop.has_quantifier_n.post.inv {q: callquantifier} {t₁ t₂: term}: q ∉ quantifiers_n (prop.post t₁ t₂) :=
  assume post_has_quantifier_n: q ∈ quantifiers_n (prop.post t₁ t₂),
  show «false», by cases post_has_quantifier_n

lemma prop.has_quantifier_n.forallc.inv {q: callquantifier} {x: var} {t: term} {P: prop}:
      q ∈ quantifiers_n (prop.forallc x t P) → (q = ⟨t, x, P⟩) ∨ q ∈ quantifiers_n P :=
  assume forall_has_quantifier_n: q ∈ quantifiers_n (prop.forallc x t P),
  begin
    cases forall_has_quantifier_n,
    from or.inl rfl
  end

lemma prop.has_quantifier_n.exis.inv {q: callquantifier} {x: var} {P: prop}:
      q ∈ quantifiers_n (prop.exis x P) → q ∈ quantifiers_n P :=
  assume exis_has_quantifier_n: q ∈ quantifiers_n (prop.exis x P),
  begin
    cases exis_has_quantifier_n,
    from a
  end

lemma prop.has_call_env.and₁ {c: calltrigger} {P₁ P₂: prop} {σ: env}:
      c ∈ calls_env σ P₁ → c ∈ calls_env σ (P₁ ⋀ P₂) :=
  assume : c ∈ calls_env σ P₁,
  have c ∈ (calltrigger.subst σ) '' calls P₁, from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls P₁)
      (λa, a ∈ calls_env σ (P₁ ⋀ P₂)) c this (
    assume c': calltrigger,
    assume : c' ∈ calls P₁,
    have c' ∈ calls (P₁ ⋀ P₂), from prop.has_call.and₁ this,
    show calltrigger.subst σ c' ∈ calls_env σ (P₁ ⋀ P₂), from set.mem_image this rfl
  )

lemma prop.has_call_env.and₂ {c: calltrigger} {P₁ P₂: prop} {σ: env}:
      c ∈ calls_env σ P₂ → c ∈ calls_env σ (P₁ ⋀ P₂) :=
  assume : c ∈ calls_env σ P₂,
  have c ∈ (calltrigger.subst σ) '' calls P₂, from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls P₂)
      (λa, a ∈ calls_env σ (P₁ ⋀ P₂)) c this (
    assume c': calltrigger,
    assume : c' ∈ calls P₂,
    have c' ∈ calls (P₁ ⋀ P₂), from prop.has_call.and₂ this,
    show calltrigger.subst σ c' ∈ calls_env σ (P₁ ⋀ P₂), from set.mem_image this rfl
  )

lemma prop.has_call_env.not {c: calltrigger} {P: prop} {σ: env}:
      c ∈ calls_env σ P → c ∈ calls_n_env σ P.not :=
  assume : c ∈ calls_env σ P,
  have c ∈ (calltrigger.subst σ) '' calls P, from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls P)
      (λa, a ∈ calls_n_env σ P.not) c this (
    assume c': calltrigger,
    assume : c' ∈ calls P,
    have c' ∈ calls_n P.not, from prop.has_call_n.not this,
    show calltrigger.subst σ c' ∈ calls_n_env σ P.not, from set.mem_image this rfl
  )

lemma prop.has_call_n_env.not {c: calltrigger} {P: prop} {σ: env}:
      c ∈ calls_n_env σ P → c ∈ calls_env σ P.not :=
  assume : c ∈ calls_n_env σ P,
  have c ∈ (calltrigger.subst σ) '' calls_n P, from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_n P)
      (λa, a ∈ calls_env σ P.not) c this (
    assume c': calltrigger,
    assume : c' ∈ calls_n P,
    have c' ∈ calls P.not, from prop.has_call.not this,
    show calltrigger.subst σ c' ∈ calls_env σ P.not, from set.mem_image this rfl
  )

lemma prop.has_call_env.not.inv {c: calltrigger} {P: prop} {σ: env}:
      c ∈ calls_env σ P.not → c ∈ calls_n_env σ P :=
  assume : c ∈ calls_env σ P.not,
  have c ∈ (calltrigger.subst σ) '' calls P.not, from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls P.not)
      (λa, a ∈ calls_n_env σ P) c this (
    assume c': calltrigger,
    assume : c' ∈ calls P.not,
    have c' ∈ calls_n P, from prop.has_call.not.inv this,
    show calltrigger.subst σ c' ∈ calls_n_env σ P, from set.mem_image this rfl
  )

lemma prop.has_call_n_env.not.inv {c: calltrigger} {P: prop} {σ: env}:
      c ∈ calls_n_env σ P.not → c ∈ calls_env σ P :=
  assume : c ∈ calls_n_env σ P.not,
  have c ∈ (calltrigger.subst σ) '' calls_n P.not, from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_n P.not)
      (λa, a ∈ calls_env σ P) c this (
    assume c': calltrigger,
    assume : c' ∈ calls_n P.not,
    have c' ∈ calls P, from prop.has_call_n.not.inv this,
    show calltrigger.subst σ c' ∈ calls_env σ P, from set.mem_image this rfl
  )

lemma prop.has_call_env.and.inv {c: calltrigger} {P₁ P₂: prop} {σ: env}:
      c ∈ calls_env σ (P₁ ⋀ P₂) → c ∈ calls_env σ P₁ ∨ c ∈ calls_env σ P₂ :=
  assume : c ∈ calls_env σ (P₁ ⋀ P₂),
  have c ∈ (calltrigger.subst σ) '' calls (P₁ ⋀ P₂), from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls (P₁ ⋀ P₂))
      (λa, a ∈ calls_env σ P₁ ∨ a ∈ calls_env σ P₂) c this (
    assume c': calltrigger,
    assume : c' ∈ calls (P₁ ⋀ P₂),
    or.elim (prop.has_call.and.inv this) (
      assume : c' ∈ calls P₁,
      have calltrigger.subst σ c' ∈ calls_env σ P₁, from set.mem_image this rfl,
      show calltrigger.subst σ c' ∈ calls_env σ P₁
         ∨ calltrigger.subst σ c' ∈ calls_env σ P₂, from or.inl this
    ) (
      assume : c' ∈ calls P₂,
      have calltrigger.subst σ c' ∈ calls_env σ P₂, from set.mem_image this rfl,
      show calltrigger.subst σ c' ∈ calls_env σ P₁
         ∨ calltrigger.subst σ c' ∈ calls_env σ P₂, from or.inr this
    )
  )

lemma no_instantiations.term {t: term}: no_instantiations t :=
  have h1: calls t = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls t,
    show «false», from prop.has_call.term.inv this
  ),
  have h2: calls_n t = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n t,
    show «false», from prop.has_call_n.term.inv this
  ),
  have h3: quantifiers t = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers t,
    show «false», from prop.has_quantifier.term.inv  this
  ),
  have h4: quantifiers_n t = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n t,
    show «false», from prop.has_quantifier_n.term.inv  this
  ),
  ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩

lemma no_instantiations.not {P: prop}: no_instantiations P → no_instantiations P.not :=
  assume ⟨no_calls_in_P, ⟨no_calls_n_in_P, ⟨no_quantifiers_in_P, no_quantifiers_n_in_P⟩⟩⟩,
  have h1: calls P.not = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls P.not,
    have c_in_calls_P: c ∈ calls_n P, from prop.has_call.not.inv this,
    have c_not_in_calls_P: c ∉ calls_n P, from set.forall_not_mem_of_eq_empty no_calls_n_in_P c,
    show «false», from c_not_in_calls_P c_in_calls_P
  ),
  have h2: calls_n P.not = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n P.not,
    have c_in_calls_P: c ∈ calls P, from prop.has_call_n.not.inv this,
    have c_not_in_calls_P: c ∉ calls P, from set.forall_not_mem_of_eq_empty no_calls_in_P c,
    show «false», from c_not_in_calls_P c_in_calls_P
  ),
  have h3: quantifiers P.not = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers P.not,
    have c_in_quantifiers_P: q ∈ quantifiers_n P, from prop.has_quantifier.not.inv this,
    have c_not_in_quantifiers_P: q ∉ quantifiers_n P, from set.forall_not_mem_of_eq_empty no_quantifiers_n_in_P q,
    show «false», from c_not_in_quantifiers_P c_in_quantifiers_P
  ),
  have h4: quantifiers_n P.not = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n P.not,
    have c_in_quantifiers_P: q ∈ quantifiers P, from prop.has_quantifier_n.not.inv this,
    have c_not_in_quantifiers_P: q ∉ quantifiers P, from set.forall_not_mem_of_eq_empty no_quantifiers_in_P q,
    show «false», from c_not_in_quantifiers_P c_in_quantifiers_P
  ),
  ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩

lemma no_instantiations.and {P₁ P₂: prop}:
      no_instantiations P₁ → no_instantiations P₂ → no_instantiations (prop.and P₁ P₂) :=
  assume ⟨no_calls_in_P₁, ⟨no_calls_n_in_P₁, ⟨no_quantifiers_in_P₁, no_quantifiers_n_in_P₁⟩⟩⟩,
  assume ⟨no_calls_in_P₂, ⟨no_calls_n_in_P₂, ⟨no_quantifiers_in_P₂, no_quantifiers_n_in_P₂⟩⟩⟩,
  have h1: calls (P₁ ⋀ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls (P₁ ⋀ P₂),
    have c ∈ calls P₁ ∨ c ∈ calls P₂, from prop.has_call.and.inv this,
    or.elim this (
      assume c_in_calls_P₁: c ∈ calls P₁,
      have c_not_in_calls_P₁: c ∉ calls P₁, from set.forall_not_mem_of_eq_empty no_calls_in_P₁ c,
      show «false», from c_not_in_calls_P₁ c_in_calls_P₁
    ) (
      assume c_in_calls_P₂: c ∈ calls P₂,
      have c_not_in_calls_P₂: c ∉ calls P₂, from set.forall_not_mem_of_eq_empty no_calls_in_P₂ c,
      show «false», from c_not_in_calls_P₂ c_in_calls_P₂
    )
  ),
  have h2: calls_n (P₁ ⋀ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n (P₁ ⋀ P₂),
    have c ∈ calls_n P₁ ∨ c ∈ calls_n P₂, from prop.has_call_n.and.inv this,
    or.elim this (
      assume c_in_calls_P₁: c ∈ calls_n P₁,
      have c_not_in_calls_P₁: c ∉ calls_n P₁, from set.forall_not_mem_of_eq_empty no_calls_n_in_P₁ c,
      show «false», from c_not_in_calls_P₁ c_in_calls_P₁
    ) (
      assume c_in_calls_P₂: c ∈ calls_n P₂,
      have c_not_in_calls_P₂: c ∉ calls_n P₂, from set.forall_not_mem_of_eq_empty no_calls_n_in_P₂ c,
      show «false», from c_not_in_calls_P₂ c_in_calls_P₂
    )
  ),
  have h3: quantifiers (P₁ ⋀ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers (P₁ ⋀ P₂),
    have q ∈ quantifiers P₁ ∨ q ∈ quantifiers P₂, from prop.has_quantifier.and.inv this,
    or.elim this (
      assume q_in_quantifiers_P₁: q ∈ quantifiers P₁,
      have q_not_in_quantifiers_P₁: q ∉ quantifiers P₁, from set.forall_not_mem_of_eq_empty no_quantifiers_in_P₁ q,
      show «false», from q_not_in_quantifiers_P₁ q_in_quantifiers_P₁
    ) (
      assume q_in_quantifiers_P₂: q ∈ quantifiers P₂,
      have q_not_in_quantifiers_P₂: q ∉ quantifiers P₂, from set.forall_not_mem_of_eq_empty no_quantifiers_in_P₂ q,
      show «false», from q_not_in_quantifiers_P₂ q_in_quantifiers_P₂
    )
  ),
  have h4: quantifiers_n (P₁ ⋀ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n (P₁ ⋀ P₂),
    have q ∈ quantifiers_n P₁ ∨ q ∈ quantifiers_n P₂, from prop.has_quantifier_n.and.inv this,
    or.elim this (
      assume q_in_quantifiers_P₁: q ∈ quantifiers_n P₁,
      have q_not_in_quantifiers_P₁: q ∉ quantifiers_n P₁, from set.forall_not_mem_of_eq_empty no_quantifiers_n_in_P₁ q,
      show «false», from q_not_in_quantifiers_P₁ q_in_quantifiers_P₁
    ) (
      assume q_in_quantifiers_P₂: q ∈ quantifiers_n P₂,
      have q_not_in_quantifiers_P₂: q ∉ quantifiers_n P₂, from set.forall_not_mem_of_eq_empty no_quantifiers_n_in_P₂ q,
      show «false», from q_not_in_quantifiers_P₂ q_in_quantifiers_P₂
    )
  ),
  ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩

lemma no_instantiations.or {P₁ P₂: prop}:
      no_instantiations P₁ → no_instantiations P₂ → no_instantiations (prop.or P₁ P₂) :=
  assume ⟨no_calls_in_P₁, ⟨no_calls_n_in_P₁, ⟨no_quantifiers_in_P₁, no_quantifiers_n_in_P₁⟩⟩⟩,
  assume ⟨no_calls_in_P₂, ⟨no_calls_n_in_P₂, ⟨no_quantifiers_in_P₂, no_quantifiers_n_in_P₂⟩⟩⟩,
  have h1: calls (P₁ ⋁ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls (P₁ ⋁ P₂),
    have c ∈ calls P₁ ∨ c ∈ calls P₂, from prop.has_call.or.inv this,
    or.elim this (
      assume c_in_calls_P₁: c ∈ calls P₁,
      have c_not_in_calls_P₁: c ∉ calls P₁, from set.forall_not_mem_of_eq_empty no_calls_in_P₁ c,
      show «false», from c_not_in_calls_P₁ c_in_calls_P₁
    ) (
      assume c_in_calls_P₂: c ∈ calls P₂,
      have c_not_in_calls_P₂: c ∉ calls P₂, from set.forall_not_mem_of_eq_empty no_calls_in_P₂ c,
      show «false», from c_not_in_calls_P₂ c_in_calls_P₂
    )
  ),
  have h2: calls_n (P₁ ⋁ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n (P₁ ⋁ P₂),
    have c ∈ calls_n P₁ ∨ c ∈ calls_n P₂, from prop.has_call_n.or.inv this,
    or.elim this (
      assume c_in_calls_P₁: c ∈ calls_n P₁,
      have c_not_in_calls_P₁: c ∉ calls_n P₁, from set.forall_not_mem_of_eq_empty no_calls_n_in_P₁ c,
      show «false», from c_not_in_calls_P₁ c_in_calls_P₁
    ) (
      assume c_in_calls_P₂: c ∈ calls_n P₂,
      have c_not_in_calls_P₂: c ∉ calls_n P₂, from set.forall_not_mem_of_eq_empty no_calls_n_in_P₂ c,
      show «false», from c_not_in_calls_P₂ c_in_calls_P₂
    )
  ),
  have h3: quantifiers (P₁ ⋁ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers (P₁ ⋁ P₂),
    have q ∈ quantifiers P₁ ∨ q ∈ quantifiers P₂, from prop.has_quantifier.or.inv this,
    or.elim this (
      assume q_in_quantifiers_P₁: q ∈ quantifiers P₁,
      have q_not_in_quantifiers_P₁: q ∉ quantifiers P₁, from set.forall_not_mem_of_eq_empty no_quantifiers_in_P₁ q,
      show «false», from q_not_in_quantifiers_P₁ q_in_quantifiers_P₁
    ) (
      assume q_in_quantifiers_P₂: q ∈ quantifiers P₂,
      have q_not_in_quantifiers_P₂: q ∉ quantifiers P₂, from set.forall_not_mem_of_eq_empty no_quantifiers_in_P₂ q,
      show «false», from q_not_in_quantifiers_P₂ q_in_quantifiers_P₂
    )
  ),
  have h4: quantifiers_n (P₁ ⋁ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n (P₁ ⋁ P₂),
    have q ∈ quantifiers_n P₁ ∨ q ∈ quantifiers_n P₂, from prop.has_quantifier_n.or.inv this,
    or.elim this (
      assume q_in_quantifiers_P₁: q ∈ quantifiers_n P₁,
      have q_not_in_quantifiers_P₁: q ∉ quantifiers_n P₁, from set.forall_not_mem_of_eq_empty no_quantifiers_n_in_P₁ q,
      show «false», from q_not_in_quantifiers_P₁ q_in_quantifiers_P₁
    ) (
      assume q_in_quantifiers_P₂: q ∈ quantifiers_n P₂,
      have q_not_in_quantifiers_P₂: q ∉ quantifiers_n P₂, from set.forall_not_mem_of_eq_empty no_quantifiers_n_in_P₂ q,
      show «false», from q_not_in_quantifiers_P₂ q_in_quantifiers_P₂
    )
  ),
  ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩

lemma no_instantiations.pre {t₁ t₂: term}: no_instantiations (prop.pre t₁ t₂) :=
  have h1: calls (prop.pre t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls (prop.pre t₁ t₂),
    show «false», from prop.has_call.pre.inv this
  ),
  have h2: calls_n (prop.pre t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n (prop.pre t₁ t₂),
    show «false», from prop.has_call_n.pre.inv this
  ),
  have h3: quantifiers (prop.pre t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers (prop.pre t₁ t₂),
    show «false», from prop.has_quantifier.pre.inv  this
  ),
  have h4: quantifiers_n (prop.pre t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n (prop.pre t₁ t₂),
    show «false», from prop.has_quantifier_n.pre.inv  this
  ),
  ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩

lemma no_instantiations.pre₁ {t: term} {op: unop}: no_instantiations (prop.pre₁ op t) :=
  have h1: calls (prop.pre₁ op t) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls (prop.pre₁ op t),
    show «false», from prop.has_call.pre₁.inv this
  ),
  have h2: calls_n (prop.pre₁ op t) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n (prop.pre₁ op t),
    show «false», from prop.has_call_n.pre₁.inv this
  ),
  have h3: quantifiers (prop.pre₁ op t) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers (prop.pre₁ op t),
    show «false», from prop.has_quantifier.pre₁.inv  this
  ),
  have h4: quantifiers_n (prop.pre₁ op t) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n (prop.pre₁ op t),
    show «false», from prop.has_quantifier_n.pre₁.inv  this
  ),
  ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩

lemma no_instantiations.pre₂ {t₁ t₂: term} {op: binop}: no_instantiations (prop.pre₂ op t₁ t₂) :=
  have h1: calls (prop.pre₂ op t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls (prop.pre₂ op t₁ t₂),
    show «false», from prop.has_call.pre₂.inv this
  ),
  have h2: calls_n (prop.pre₂ op t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n (prop.pre₂ op t₁ t₂),
    show «false», from prop.has_call_n.pre₂.inv this
  ),
  have h3: quantifiers (prop.pre₂ op t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers (prop.pre₂ op t₁ t₂),
    show «false», from prop.has_quantifier.pre₂.inv  this
  ),
  have h4: quantifiers_n (prop.pre₂ op t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n (prop.pre₂ op t₁ t₂),
    show «false», from prop.has_quantifier_n.pre₂.inv  this
  ),
  ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩

lemma no_instantiations.post {t₁ t₂: term}: no_instantiations (prop.post t₁ t₂) :=
  have h1: calls (prop.post t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls (prop.post t₁ t₂),
    show «false», from prop.has_call.post.inv this
  ),
  have h2: calls_n (prop.post t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n (prop.post t₁ t₂),
    show «false», from prop.has_call_n.post.inv this
  ),
  have h3: quantifiers (prop.post t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers (prop.post t₁ t₂),
    show «false», from prop.has_quantifier.post.inv  this
  ),
  have h4: quantifiers_n (prop.post t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n (prop.post t₁ t₂),
    show «false», from prop.has_quantifier_n.post.inv  this
  ),
  ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩

lemma prop.erased.implies {P Q: prop}:
      (prop.implies P Q).erased = vc.implies P.erased_n Q.erased :=
  by calc 
       (prop.implies P Q).erased = (prop.or (prop.not P) Q).erased : rfl
                             ... = ((prop.not P).erased ⋁ Q.erased) : by unfold prop.erased
                             ... = ((vc.not P.erased_n) ⋁ Q.erased) : by unfold prop.erased

lemma prop.erased_n.implies {P Q: prop}:
      (prop.implies P Q).erased_n = vc.implies P.erased Q.erased_n :=
  by calc 
       (prop.implies P Q).erased_n = (prop.or (prop.not P) Q).erased_n : rfl
                               ... = ((prop.not P).erased_n ⋁ Q.erased_n) : by unfold prop.erased_n
                               ... = (vc.not P.erased ⋁ Q.erased_n) : by unfold prop.erased_n

lemma free_of_erased_free {x: var} {P: prop}: (x ∈ FV P.erased ∨ x ∈ FV P.erased_n) → x ∈ FV P :=
  assume x_free_in_erased_or_erased_n: x ∈ FV P.erased ∨ x ∈ FV P.erased_n,
  begin
    induction P,
    case prop.term t { from (
      or.elim x_free_in_erased_or_erased_n
      (
        assume x_free_in_t: free_in_vc x (prop.term t).erased,
        have (prop.term t).erased = vc.term t, by unfold prop.erased,
        have free_in_vc x (vc.term t), from this ▸ x_free_in_t,
        have free_in_term x t, from free_in_vc.term.inv this,
        show free_in_prop x (prop.term t), from free_in_prop.term this
      ) (
        assume x_free_in_t: free_in_vc x (prop.term t).erased_n,
        have (prop.term t).erased_n = vc.term t, by unfold prop.erased_n,
        have free_in_vc x (vc.term t), from this ▸ x_free_in_t,
        have free_in_term x t, from free_in_vc.term.inv this,
        show free_in_prop x (prop.term t), from free_in_prop.term this
      )
    )},
    case prop.not P₁ ih { from (
      or.elim x_free_in_erased_or_erased_n
      (
        assume x_free: x ∈ FV (prop.not P₁).erased,
        have (prop.not P₁).erased = vc.not P₁.erased_n, by unfold prop.erased,
        have x ∈ FV (vc.not P₁.erased_n), from this ▸ x_free,
        have x ∈ FV P₁.erased_n, from free_in_vc.not.inv this,
        have x ∈ FV P₁, from ih (or.inr this),
        show x ∈ FV P₁.not, from free_in_prop.not this
      ) (
        assume x_free: x ∈ FV (prop.not P₁).erased_n,
        have (prop.not P₁).erased_n = vc.not P₁.erased, by unfold prop.erased_n,
        have x ∈ FV (vc.not P₁.erased), from this ▸ x_free,
        have x ∈ FV P₁.erased, from free_in_vc.not.inv this,
        have x ∈ FV P₁, from ih (or.inl this),
        show x ∈ FV P₁.not, from free_in_prop.not this
      )
    )},
    case prop.and P₁ P₂ P₁_ih P₂_ih { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free: x ∈ FV (P₁ ⋀ P₂).erased,
        have (prop.and P₁ P₂).erased = (P₁.erased ⋀ P₂.erased), by unfold prop.erased,
        have x ∈ FV (P₁.erased ⋀ P₂.erased), from this ▸ x_free,
        have x ∈ FV P₁.erased ∨ x ∈ FV P₂.erased, from free_in_vc.and.inv this,
        or.elim this (
          assume : x ∈ FV P₁.erased,
          have x ∈ FV P₁, from P₁_ih (or.inl this),
          show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₁ this
        ) (
          assume : x ∈ FV P₂.erased,
          have x ∈ FV P₂, from P₂_ih (or.inl this),
          show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₂ this
        )
      ) (
        assume x_free: x ∈ FV (P₁ ⋀ P₂).erased_n,
        have (prop.and P₁ P₂).erased_n = (P₁.erased_n ⋀ P₂.erased_n), by unfold prop.erased_n,
        have x ∈ FV (P₁.erased_n ⋀ P₂.erased_n), from this ▸ x_free,
        have x ∈ FV P₁.erased_n ∨ x ∈ FV P₂.erased_n, from free_in_vc.and.inv this,
        or.elim this (
          assume : x ∈ FV P₁.erased_n,
          have x ∈ FV P₁, from P₁_ih (or.inr this),
          show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₁ this
        ) (
          assume : x ∈ FV P₂.erased_n,
          have x ∈ FV P₂, from P₂_ih (or.inr this),
          show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₂ this
        )
      )
    )},
    case prop.or P₁ P₂ P₁_ih P₂_ih { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free: x ∈ FV (P₁ ⋁ P₂).erased,
        have (prop.or P₁ P₂).erased = (P₁.erased ⋁ P₂.erased), by unfold prop.erased,
        have x ∈ FV (P₁.erased ⋁ P₂.erased), from this ▸ x_free,
        have x ∈ FV P₁.erased ∨ x ∈ FV P₂.erased, from free_in_vc.or.inv this,
        or.elim this (
          assume : x ∈ FV P₁.erased,
          have x ∈ FV P₁, from P₁_ih (or.inl this),
          show x ∈ FV (P₁ ⋁ P₂), from free_in_prop.or₁ this
        ) (
          assume : x ∈ FV P₂.erased,
          have x ∈ FV P₂, from P₂_ih (or.inl this),
          show x ∈ FV (P₁ ⋁ P₂), from free_in_prop.or₂ this
        )
      ) (
        assume x_free: x ∈ FV (P₁ ⋁ P₂).erased_n,
        have (prop.or P₁ P₂).erased_n = (P₁.erased_n ⋁ P₂.erased_n), by unfold prop.erased_n,
        have x ∈ FV (P₁.erased_n ⋁ P₂.erased_n), from this ▸ x_free,
        have x ∈ FV P₁.erased_n ∨ x ∈ FV P₂.erased_n, from free_in_vc.or.inv this,
        or.elim this (
          assume : x ∈ FV P₁.erased_n,
          have x ∈ FV P₁, from P₁_ih (or.inr this),
          show x ∈ FV (P₁ ⋁ P₂), from free_in_prop.or₁ this
        ) (
          assume : x ∈ FV P₂.erased_n,
          have x ∈ FV P₂, from P₂_ih (or.inr this),
          show x ∈ FV (P₁ ⋁ P₂), from free_in_prop.or₂ this
        )
      )
    )},
    case prop.pre t₁ t₂ { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free: x ∈ FV (prop.pre t₁ t₂).erased,
        have (prop.pre t₁ t₂).erased = vc.pre t₁ t₂, by unfold prop.erased,
        have x ∈ FV (vc.pre t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.pre.inv this,
        or.elim this (
          assume : x ∈ FV t₁,
          show free_in_prop x (prop.pre t₁ t₂), from free_in_prop.pre₁ this
        ) (
          assume : x ∈ FV t₂,
          show free_in_prop x (prop.pre t₁ t₂), from free_in_prop.pre₂ this
        )
      ) (
        assume x_free: x ∈ FV (prop.pre t₁ t₂).erased_n,
        have (prop.pre t₁ t₂).erased_n = vc.pre t₁ t₂, by unfold prop.erased_n,
        have x ∈ FV (vc.pre t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.pre.inv this,
        or.elim this (
          assume : x ∈ FV t₁,
          show free_in_prop x (prop.pre t₁ t₂), from free_in_prop.pre₁ this
        ) (
          assume : x ∈ FV t₂,
          show free_in_prop x (prop.pre t₁ t₂), from free_in_prop.pre₂ this
        )
      )
    )},
    case prop.pre₁ op t { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free_in_t: free_in_vc x (prop.pre₁ op t).erased,
        have (prop.pre₁ op t).erased = vc.pre₁ op t, by unfold prop.erased,
        have free_in_vc x (vc.pre₁ op t), from this ▸ x_free_in_t,
        have free_in_term x t, from free_in_vc.pre₁.inv this,
        show free_in_prop x (prop.pre₁ op t), from free_in_prop.preop this
      ) (
        assume x_free_in_t: free_in_vc x (prop.pre₁ op t).erased_n,
        have (prop.pre₁ op t).erased_n = vc.pre₁ op t, by unfold prop.erased_n,
        have free_in_vc x (vc.pre₁ op t), from this ▸ x_free_in_t,
        have free_in_term x t, from free_in_vc.pre₁.inv this,
        show free_in_prop x (prop.pre₁ op t), from free_in_prop.preop this
      )
    )},
    case prop.pre₂ op t₁ t₂ { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free: x ∈ FV (prop.pre₂ op t₁ t₂).erased,
        have (prop.pre₂ op t₁ t₂).erased = vc.pre₂ op t₁ t₂, by unfold prop.erased,
        have x ∈ FV (vc.pre₂ op t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.pre₂.inv this,
        or.elim this (
          assume : x ∈ FV t₁,
          show free_in_prop x (prop.pre₂ op t₁ t₂), from free_in_prop.preop₁ this
        ) (
          assume : x ∈ FV t₂,
          show free_in_prop x (prop.pre₂ op t₁ t₂), from free_in_prop.preop₂ this
        )
      ) (
        assume x_free: x ∈ FV (prop.pre₂ op t₁ t₂).erased_n,
        have (prop.pre₂ op t₁ t₂).erased_n = vc.pre₂ op t₁ t₂, by unfold prop.erased_n,
        have x ∈ FV (vc.pre₂ op t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.pre₂.inv this,
        or.elim this (
          assume : x ∈ FV t₁,
          show free_in_prop x (prop.pre₂ op t₁ t₂), from free_in_prop.preop₁ this
        ) (
          assume : x ∈ FV t₂,
          show free_in_prop x (prop.pre₂ op t₁ t₂), from free_in_prop.preop₂ this
        )
      )
    )},
    case prop.post t₁ t₂ { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free: x ∈ FV (prop.post t₁ t₂).erased,
        have (prop.post t₁ t₂).erased = vc.post t₁ t₂, by unfold prop.erased,
        have x ∈ FV (vc.post t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.post.inv this,
        or.elim this (
          assume : x ∈ FV t₁,

          show free_in_prop x (prop.post t₁ t₂), from free_in_prop.post₁ this
        ) (
          assume : x ∈ FV t₂,

          show free_in_prop x (prop.post t₁ t₂), from free_in_prop.post₂ this
        )
      ) (
        assume x_free: x ∈ FV (prop.post t₁ t₂).erased_n,
        have (prop.post t₁ t₂).erased_n = vc.post t₁ t₂, by unfold prop.erased_n,
        have x ∈ FV (vc.post t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.post.inv this,
        or.elim this (
          assume : x ∈ FV t₁,

          show free_in_prop x (prop.post t₁ t₂), from free_in_prop.post₁ this
        ) (
          assume : x ∈ FV t₂,

          show free_in_prop x (prop.post t₁ t₂), from free_in_prop.post₂ this
        )
      )
    )},
    case prop.call t₁ t₂ { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free: x ∈ FV (prop.call t₁ t₂).erased,
        have (prop.call t₁ t₂).erased = vc.term value.true, by unfold prop.erased,
        have x ∈ FV (vc.term value.true), from this ▸ x_free,
        have x ∈ FV (term.value value.true), from free_in_vc.term.inv this,
        absurd this (free_in_term.value.inv)
      ) (
        assume x_free: x ∈ FV (prop.call t₁ t₂).erased_n,
        have (prop.call t₁ t₂).erased_n = vc.term value.true, by unfold prop.erased_n,
        have x ∈ FV (vc.term value.true), from this ▸ x_free,
        have x ∈ FV (term.value value.true), from free_in_vc.term.inv this,
        absurd this (free_in_term.value.inv)
      )
    )},
    case prop.forallc y t P₁ ih { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free: x ∈ FV (prop.forallc y t P₁).erased,
        have (prop.forallc y t P₁).erased = vc.univ y P₁.erased, by unfold prop.erased,
        have x ∈ FV (vc.univ y P₁.erased), from this ▸ x_free,
        have h2: (x ≠ y) ∧ free_in_vc x P₁.erased, from free_in_vc.univ.inv this,
        have x ∈ FV P₁, from ih (or.inl h2.right),
        show x ∈ FV (prop.forallc y t P₁), from free_in_prop.forallc₂ h2.left this
      ) (
        assume x_free: x ∈ FV (prop.forallc y t P₁).erased_n,
        have (prop.forallc y t P₁).erased_n = vc.term value.true, by unfold prop.erased_n,
        have x ∈ FV (vc.term value.true), from this ▸ x_free,
        have x ∈ FV (term.value value.true), from free_in_vc.term.inv this,
        absurd this (free_in_term.value.inv)
      )
    )},
    case prop.exis y P₁ ih { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free: x ∈ FV (prop.exis y P₁).erased,
        have (prop.exis y P₁).erased = vc.not (vc.univ y (vc.not P₁.erased)), by unfold prop.erased,
        have x ∈ FV (vc.not (vc.univ y (vc.not P₁.erased))), from this ▸ x_free,
        have x ∈ FV (vc.univ y (vc.not P₁.erased)), from free_in_vc.not.inv this,
        have h2: (x ≠ y) ∧ free_in_vc x (vc.not P₁.erased), from free_in_vc.univ.inv this,
        have h3: x ∈ FV P₁.erased, from free_in_vc.not.inv h2.right,
        have x ∈ FV P₁, from ih (or.inl h3),
        show x ∈ FV (prop.exis y P₁), from free_in_prop.exis h2.left this
      )
      (
        assume x_free: x ∈ FV (prop.exis y P₁).erased_n,
        have (prop.exis y P₁).erased_n = vc.not (vc.univ y (vc.not P₁.erased_n)), by unfold prop.erased_n,
        have x ∈ FV (vc.not (vc.univ y (vc.not P₁.erased_n))), from this ▸ x_free,
        have x ∈ FV (vc.univ y (vc.not P₁.erased_n)), from free_in_vc.not.inv this,
        have h2: (x ≠ y) ∧ free_in_vc x (vc.not P₁.erased_n), from free_in_vc.univ.inv this,
        have h3: x ∈ FV P₁.erased_n, from free_in_vc.not.inv h2.right,
        have x ∈ FV P₁, from ih (or.inr h3),
        show x ∈ FV (prop.exis y P₁), from free_in_prop.exis h2.left this
      )
    )}
  end

lemma prop.has_call.and.comm {P₁ P₂ P₃: prop}:
      calls (P₁ ⋀ P₂ ⋀ P₃) = calls ((P₁ ⋀ P₂) ⋀ P₃) :=
  set.eq_of_subset_of_subset (
    assume c: calltrigger,
    assume : c ∈ calls (P₁ ⋀ P₂ ⋀ P₃),
    or.elim (prop.has_call.and.inv this) (
      assume : c ∈ calls P₁,
      have c ∈ calls (P₁ ⋀ P₂), from prop.has_call.and₁ this,
      show c ∈ calls ((P₁ ⋀ P₂) ⋀ P₃), from prop.has_call.and₁ this
    ) (
      assume : c ∈ calls (P₂ ⋀ P₃),
      or.elim (prop.has_call.and.inv this) (
        assume : c ∈ calls P₂,
        have c ∈ calls (P₁ ⋀ P₂), from prop.has_call.and₂ this,
        show c ∈ calls ((P₁ ⋀ P₂) ⋀ P₃), from prop.has_call.and₁ this
      ) (
        assume : c ∈ calls P₃,
        show c ∈ calls ((P₁ ⋀ P₂) ⋀ P₃), from prop.has_call.and₂ this
      )
    )
  ) (
    assume c: calltrigger,
    assume : c ∈ calls ((P₁ ⋀ P₂) ⋀ P₃),
    or.elim (prop.has_call.and.inv this) (
      assume : c ∈ calls (P₁ ⋀ P₂),
      or.elim (prop.has_call.and.inv this) (
        assume : c ∈ calls P₁,
        show c ∈ calls (P₁ ⋀ P₂ ⋀ P₃), from prop.has_call.and₁ this
      ) (
        assume : c ∈ calls P₂,
        have c ∈ calls (P₂ ⋀ P₃), from prop.has_call.and₁ this,
        show c ∈ calls (P₁ ⋀ P₂ ⋀ P₃), from prop.has_call.and₂ this
      )
    ) (
      assume : c ∈ calls P₃,
      have c ∈ calls (P₂ ⋀ P₃), from prop.has_call.and₂ this,
      show c ∈ calls (P₁ ⋀ P₂ ⋀ P₃), from prop.has_call.and₂ this
    )
  )

lemma prop.has_quantifier.and.comm {P₁ P₂ P₃: prop}:
      quantifiers (P₁ ⋀ P₂ ⋀ P₃) = quantifiers ((P₁ ⋀ P₂) ⋀ P₃) :=
  set.eq_of_subset_of_subset (
    assume q: callquantifier,
    assume : q ∈ quantifiers (P₁ ⋀ P₂ ⋀ P₃),
    or.elim (prop.has_quantifier.and.inv this) (
      assume : q ∈ quantifiers P₁,
      have q ∈ quantifiers (P₁ ⋀ P₂), from prop.has_quantifier.and₁ this,
      show q ∈ quantifiers ((P₁ ⋀ P₂) ⋀ P₃), from prop.has_quantifier.and₁ this
    ) (
      assume : q ∈ quantifiers (P₂ ⋀ P₃),
      or.elim (prop.has_quantifier.and.inv this) (
        assume : q ∈ quantifiers P₂,
        have q ∈ quantifiers (P₁ ⋀ P₂), from prop.has_quantifier.and₂ this,
        show q ∈ quantifiers ((P₁ ⋀ P₂) ⋀ P₃), from prop.has_quantifier.and₁ this
      ) (
        assume : q ∈ quantifiers P₃,
        show q ∈ quantifiers ((P₁ ⋀ P₂) ⋀ P₃), from prop.has_quantifier.and₂ this
      )
    )
  ) (
    assume q: callquantifier,
    assume : q ∈ quantifiers ((P₁ ⋀ P₂) ⋀ P₃),
    or.elim (prop.has_quantifier.and.inv this) (
      assume : q ∈ quantifiers (P₁ ⋀ P₂),
      or.elim (prop.has_quantifier.and.inv this) (
        assume : q ∈ quantifiers P₁,
        show q ∈ quantifiers (P₁ ⋀ P₂ ⋀ P₃), from prop.has_quantifier.and₁ this
      ) (
        assume : q ∈ quantifiers P₂,
        have q ∈ quantifiers (P₂ ⋀ P₃), from prop.has_quantifier.and₁ this,
        show q ∈ quantifiers (P₁ ⋀ P₂ ⋀ P₃), from prop.has_quantifier.and₂ this
      )
    ) (
      assume : q ∈ quantifiers P₃,
      have q ∈ quantifiers (P₂ ⋀ P₃), from prop.has_quantifier.and₂ this,
      show q ∈ quantifiers (P₁ ⋀ P₂ ⋀ P₃), from prop.has_quantifier.and₂ this
    )
  )
