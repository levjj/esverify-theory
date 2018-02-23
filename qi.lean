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

inductive has_call (c: calltrigger) : prop → Prop
| calltrigger                           : has_call (prop.call c.f c.x)
| not {P: prop}                         : has_call P  → has_call P.not
| and₁ {P₁ P₂: prop}                    : has_call P₁ → has_call (P₁ ⋀ P₂)
| and₂ {P₁ P₂: prop}                    : has_call P₂ → has_call (P₁ ⋀ P₂)
| or₁ {P₁ P₂: prop}                     : has_call P₁ → has_call (P₁ ⋁ P₂)
| or₂ {P₁ P₂: prop}                     : has_call P₂ → has_call (P₁ ⋁ P₂)
| forallc {y: var} {t: term} {P: prop}  : has_call P  → has_call (prop.forallc y t P)
| exis {y: var} {P: prop}               : has_call P  → has_call (prop.exis y P)

def calls (p: prop): set calltrigger := λc, has_call c p

inductive has_quantifier (q: callquantifier) : prop → Prop
| callquantifier                        : has_quantifier (prop.forallc q.x q.f q.P)
| not {P: prop}                         : has_quantifier P  → has_quantifier P.not
| and₁ {P₁ P₂: prop}                    : has_quantifier P₁ → has_quantifier (P₁ ⋀ P₂)
| and₂ {P₁ P₂: prop}                    : has_quantifier P₂ → has_quantifier (P₁ ⋀ P₂)
| or₁ {P₁ P₂: prop}                     : has_quantifier P₁ → has_quantifier (P₁ ⋁ P₂)
| or₂ {P₁ P₂: prop}                     : has_quantifier P₂ → has_quantifier (P₁ ⋁ P₂)
| forallc {y: var} {t: term} {P: prop}  : has_quantifier P  → has_quantifier (prop.forallc y t P)
| exis {y: var} {P: prop}               : has_quantifier P  → has_quantifier (prop.exis y P)

def quantifiers (p: prop): set callquantifier := λc, has_quantifier c p

 -- propositions without call triggers or quantifiers do not participate in instantiations
def no_instantiations(P: prop): Prop := (calls P = ∅) ∧ (quantifiers P = ∅)

def calltrigger.subst (σ: env) (c: calltrigger): calltrigger := ⟨term.subst_env σ c.f, term.subst_env σ c.x⟩

@[reducible]
def calls_env (σ: env) (P: prop): set calltrigger := (calltrigger.subst σ) '' calls P

@[reducible]
def qualifiers_dominate (σ: env) (P P': prop): Prop :=
  ∀(t': term) (x: var) (Q': prop), callquantifier.mk t' x Q' ∈ quantifiers P' →
  ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers P ∧
                        ∀v: value, σ[x↦v] ⊨ vc.implies Q.instantiated Q'.instantiated

-- given a environment σ, P dominates P' if P implies P' and
-- P has matching or stronger triggers and quantifiers than P'
@[reducible]
def dominates (σ: env) (P P': prop): Prop :=
  calls_env σ P = calls_env σ P' ∧
  qualifiers_dominate σ P P' ∧
  σ ⊨ vc.implies P.instantiated_n P'.instantiated_n

-- axioms about instantiation

axiom instantiated.forallc {x: var} {t: term} {P: prop}:
  (prop.forallc x t P).instantiated = vc.univ x P.instantiated

axiom not_dist_instantiated {P: prop}:
  P.not.instantiated = P.instantiated_n.not

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

-- lemmas

lemma instantiated_distrib_subst_env {P: prop} {σ: env}:
      vc.subst_env σ P.instantiated = (prop.subst_env σ P).instantiated :=
begin
  induction σ with x v σ' ih,

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
  induction σ with x v σ' ih,

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

lemma has_call.term.inv {c: calltrigger} {t: term}: c ∉ calls t :=
  assume t_has_call: has_call c t,
  show «false», by cases t_has_call

lemma has_call.not.inv {c: calltrigger} {P: prop}: c ∈ calls P.not → c ∈ calls P :=
  assume not_has_call: c ∈ calls P.not,
  begin
    cases not_has_call,
    case has_call.not P_has_call { from P_has_call }
  end

lemma has_call.and.inv {c: calltrigger} {P₁ P₂: prop}: c ∈ calls (P₁ ⋀ P₂) → c ∈ calls P₁ ∨ c ∈ calls P₂ :=
  assume and_has_call: c ∈ calls (P₁ ⋀ P₂),
  begin
    cases and_has_call,
    case has_call.and₁ P₁_has_call {
      show c ∈ calls P₁ ∨ c ∈ calls P₂, from or.inl P₁_has_call
    },
    case has_call.and₂ P₂_has_call {
      show c ∈ calls P₁ ∨ c ∈ calls P₂, from or.inr P₂_has_call
    }
  end

lemma has_call.or.inv {c: calltrigger} {P₁ P₂: prop}: c ∈ calls (P₁ ⋁ P₂) → c ∈ calls P₁ ∨ c ∈ calls P₂ :=
  assume or_has_call: c ∈ calls (P₁ ⋁ P₂),
  begin
    cases or_has_call,
    case has_call.or₁ P₁_has_call {
      show c ∈ calls P₁ ∨ c ∈ calls P₂, from or.inl P₁_has_call
    },
    case has_call.or₂ P₂_has_call {
      show c ∈ calls P₁ ∨ c ∈ calls P₂, from or.inr P₂_has_call
    }
  end

lemma has_call.pre₁.inv {c: calltrigger} {op: unop} {t: term}: c ∉ calls (prop.pre₁ op t) :=
  assume pre_has_call: c ∈ calls (prop.pre₁ op t),
  show «false», by cases pre_has_call

lemma has_call.pre₂.inv {c: calltrigger} {op: binop} {t₁ t₂: term}: c ∉ calls (prop.pre₂ op t₁ t₂) :=
  assume pre_has_call: c ∈ calls (prop.pre₂ op t₁ t₂),
  show «false», by cases pre_has_call

lemma has_call.pre.inv {c: calltrigger} {t₁ t₂: term}: c ∉ calls (prop.pre t₁ t₂) :=
  assume pre_has_call: c ∈ calls (prop.pre t₁ t₂),
  show «false», by cases pre_has_call

lemma has_call.post.inv {c: calltrigger} {t₁ t₂: term}: c ∉ calls (prop.post t₁ t₂) :=
  assume post_has_call: c ∈ calls (prop.post t₁ t₂),
  show «false», by cases post_has_call

lemma has_call.forallc.inv {c: calltrigger} {x: var} {t: term} {P: prop}:
      c ∈ calls (prop.forallc x t P) → c ∈ calls P :=
  assume forall_has_call: c ∈ calls (prop.forallc x t P),
  begin
    cases forall_has_call,
    case has_call.forallc P_has_call { from P_has_call }
  end

lemma has_call.exis.inv {c: calltrigger} {x: var} {P: prop}: c ∈ calls (prop.exis x P) → c ∈ calls P :=
  assume exis_has_call: c ∈ calls (prop.exis x P),
  begin
    cases exis_has_call,
    case has_call.exis P_has_call { from P_has_call }
  end

lemma has_quantifier.term.inv {q: callquantifier} {t: term}: q ∉ quantifiers t :=
  assume t_has_quantifier: has_quantifier q t,
  show «false», by cases t_has_quantifier

lemma has_quantifier.not.inv {q: callquantifier} {P: prop}: q ∈ quantifiers P.not → q ∈ quantifiers P :=
  assume not_has_quantifier: q ∈ quantifiers P.not,
  begin
    cases not_has_quantifier,
    case has_quantifier.not P_has_quantifier { from P_has_quantifier }
  end

lemma has_quantifier.and.inv {q: callquantifier} {P₁ P₂: prop}:
      q ∈ quantifiers (P₁ ⋀ P₂) → q ∈ quantifiers P₁ ∨ q ∈ quantifiers P₂ :=
  assume and_has_quantifier: q ∈ quantifiers (P₁ ⋀ P₂),
  begin
    cases and_has_quantifier,
    case has_quantifier.and₁ P₁_has_quantifier {
      show q ∈ quantifiers P₁ ∨ q ∈ quantifiers P₂, from or.inl P₁_has_quantifier
    },
    case has_quantifier.and₂ P₂_has_quantifier {
      show q ∈ quantifiers P₁ ∨ q ∈ quantifiers P₂, from or.inr P₂_has_quantifier
    }
  end

lemma has_quantifier.or.inv {q: callquantifier} {P₁ P₂: prop}:
      q ∈ quantifiers (P₁ ⋁ P₂) → q ∈ quantifiers P₁ ∨ q ∈ quantifiers P₂ :=
  assume or_has_quantifier: q ∈ quantifiers (P₁ ⋁ P₂),
  begin
    cases or_has_quantifier,
    case has_quantifier.or₁ P₁_has_quantifier {
      show q ∈ quantifiers P₁ ∨ q ∈ quantifiers P₂, from or.inl P₁_has_quantifier
    },
    case has_quantifier.or₂ P₂_has_quantifier {
      show q ∈ quantifiers P₁ ∨ q ∈ quantifiers P₂, from or.inr P₂_has_quantifier
    }
  end

lemma has_quantifier.pre₁.inv {q: callquantifier} {op: unop} {t: term}: q ∉ quantifiers (prop.pre₁ op t) :=
  assume pre_has_quantifier: q ∈ quantifiers (prop.pre₁ op t),
  show «false», by cases pre_has_quantifier

lemma has_quantifier.pre₂.inv {q: callquantifier} {op: binop} {t₁ t₂: term}: q ∉ quantifiers (prop.pre₂ op t₁ t₂) :=
  assume pre_has_quantifier: q ∈ quantifiers (prop.pre₂ op t₁ t₂),
  show «false», by cases pre_has_quantifier

lemma has_quantifier.pre.inv {q: callquantifier} {t₁ t₂: term}: q ∉ quantifiers (prop.pre t₁ t₂) :=
  assume pre_has_quantifier: q ∈ quantifiers (prop.pre t₁ t₂),
  show «false», by cases pre_has_quantifier

lemma has_quantifier.post.inv {q: callquantifier} {t₁ t₂: term}: q ∉ quantifiers (prop.post t₁ t₂) :=
  assume post_has_quantifier: q ∈ quantifiers (prop.post t₁ t₂),
  show «false», by cases post_has_quantifier

lemma has_quantifier.forallc.inv {q: callquantifier} {x: var} {t: term} {P: prop}:
      q ∈ quantifiers (prop.forallc x t P) → (q = ⟨t, x, P⟩) ∨ q ∈ quantifiers P :=
  assume forall_has_quantifier: q ∈ quantifiers (prop.forallc x t P),
  begin
    cases forall_has_quantifier,
    case has_quantifier.callquantifier {
      have : (q = { f := q.f, x := q.x, P := q.P}), by { cases q, simp },
      show (q = {f := q.f, x := q.x, P := q.P}) ∨ q ∈ quantifiers (q.P), from or.inl this
    },
    case has_quantifier.forallc P_has_quantifier {
      show (q = ⟨t, x, P⟩) ∨ q ∈ quantifiers P, from or.inr P_has_quantifier
    }
  end

lemma has_quantifier.exis.inv {q: callquantifier} {x: var} {P: prop}:
      q ∈ quantifiers (prop.exis x P) → q ∈ quantifiers P :=
  assume exis_has_quantifier: q ∈ quantifiers (prop.exis x P),
  begin
    cases exis_has_quantifier,
    case has_quantifier.exis P_has_quantifier { from P_has_quantifier }
  end

lemma has_call_env.and₁ {c: calltrigger} {P₁ P₂: prop} {σ: env}:
      c ∈ calls_env σ P₁ → c ∈ calls_env σ (P₁ ⋀ P₂) :=
  assume : c ∈ calls_env σ P₁,
  have c ∈ (calltrigger.subst σ) '' calls P₁, from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls P₁)
      (λa, a ∈ calls_env σ (P₁ ⋀ P₂)) c this (
    assume c': calltrigger,
    assume : c' ∈ calls P₁,
    have c' ∈ calls (P₁ ⋀ P₂), from has_call.and₁ this,
    show calltrigger.subst σ c' ∈ calls_env σ (P₁ ⋀ P₂), from set.mem_image this rfl
  )

lemma has_call_env.and₂ {c: calltrigger} {P₁ P₂: prop} {σ: env}:
      c ∈ calls_env σ P₂ → c ∈ calls_env σ (P₁ ⋀ P₂) :=
  assume : c ∈ calls_env σ P₂,
  have c ∈ (calltrigger.subst σ) '' calls P₂, from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls P₂)
      (λa, a ∈ calls_env σ (P₁ ⋀ P₂)) c this (
    assume c': calltrigger,
    assume : c' ∈ calls P₂,
    have c' ∈ calls (P₁ ⋀ P₂), from has_call.and₂ this,
    show calltrigger.subst σ c' ∈ calls_env σ (P₁ ⋀ P₂), from set.mem_image this rfl
  )

lemma has_call_env.and.inv {c: calltrigger} {P₁ P₂: prop} {σ: env}:
      c ∈ calls_env σ (P₁ ⋀ P₂) → c ∈ calls_env σ P₁ ∨ c ∈ calls_env σ P₂ :=
  assume : c ∈ calls_env σ (P₁ ⋀ P₂),
  have c ∈ (calltrigger.subst σ) '' calls (P₁ ⋀ P₂), from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls (P₁ ⋀ P₂))
      (λa, a ∈ calls_env σ P₁ ∨ a ∈ calls_env σ P₂) c this (
    assume c': calltrigger,
    assume : c' ∈ calls (P₁ ⋀ P₂),
    or.elim (has_call.and.inv this) (
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
    show «false», from has_call.term.inv this
  ),
  have h2: quantifiers t = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers t,
    show «false», from has_quantifier.term.inv  this
  ),
  show (calls t = ∅) ∧ (quantifiers t = ∅), from ⟨h1, h2⟩

lemma no_instantiations.not {P: prop}: no_instantiations P → no_instantiations P.not :=
  assume ⟨no_calls_in_P, no_quantifiers_in_P⟩,
  have h1: calls P.not = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls P.not,
    have c_in_calls_P: c ∈ calls P, from has_call.not.inv this,
    have c_not_in_calls_P: c ∉ calls P, from set.forall_not_mem_of_eq_empty no_calls_in_P c,
    show «false», from c_not_in_calls_P c_in_calls_P
  ),
  have h2: quantifiers P.not = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers P.not,
    have c_in_quantifiers_P: q ∈ quantifiers P, from has_quantifier.not.inv this,
    have c_not_in_quantifiers_P: q ∉ quantifiers P, from set.forall_not_mem_of_eq_empty no_quantifiers_in_P q,
    show «false», from c_not_in_quantifiers_P c_in_quantifiers_P
  ),
  show (calls P.not = ∅) ∧ (quantifiers P.not = ∅), from ⟨h1, h2⟩

lemma no_instantiations.and {P₁ P₂: prop}:
      no_instantiations P₁ → no_instantiations P₂ → no_instantiations (prop.and P₁ P₂) :=
  assume ⟨no_calls_in_P₁, no_quantifiers_in_P₁⟩,
  assume ⟨no_calls_in_P₂, no_quantifiers_in_P₂⟩,
  have h1: calls (P₁ ⋀ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls (P₁ ⋀ P₂),
    have c ∈ calls P₁ ∨ c ∈ calls P₂, from has_call.and.inv this,
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
  have h2: quantifiers (P₁ ⋀ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers (P₁ ⋀ P₂),
    have q ∈ quantifiers P₁ ∨ q ∈ quantifiers P₂, from has_quantifier.and.inv this,
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
  show (calls (prop.and P₁ P₂) = ∅) ∧ (quantifiers (prop.and P₁ P₂) = ∅), from ⟨h1, h2⟩

lemma no_instantiations.or {P₁ P₂: prop}:
      no_instantiations P₁ → no_instantiations P₂ → no_instantiations (prop.or P₁ P₂) :=
  assume ⟨no_calls_in_P₁, no_quantifiers_in_P₁⟩,
  assume ⟨no_calls_in_P₂, no_quantifiers_in_P₂⟩,
  have h1: calls (P₁ ⋁ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls (P₁ ⋁ P₂),
    have c ∈ calls P₁ ∨ c ∈ calls P₂, from has_call.or.inv this,
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
  have h2: quantifiers (P₁ ⋁ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers (P₁ ⋁ P₂),
    have q ∈ quantifiers P₁ ∨ q ∈ quantifiers P₂, from has_quantifier.or.inv this,
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
  show (calls (prop.or P₁ P₂) = ∅) ∧ (quantifiers (prop.or P₁ P₂) = ∅), from ⟨h1, h2⟩

lemma no_instantiations.pre {t₁ t₂: term}: no_instantiations (prop.pre t₁ t₂) :=
  have h1: calls (prop.pre t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls (prop.pre t₁ t₂),
    show «false», from has_call.pre.inv this
  ),
  have h2: quantifiers (prop.pre t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers (prop.pre t₁ t₂),
    show «false», from has_quantifier.pre.inv  this
  ),
  show (calls (prop.pre t₁ t₂) = ∅) ∧ (quantifiers (prop.pre t₁ t₂) = ∅), from ⟨h1, h2⟩

lemma no_instantiations.pre₁ {t: term} {op: unop}: no_instantiations (prop.pre₁ op t) :=
  have h1: calls (prop.pre₁ op t) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls (prop.pre₁ op t),
    show «false», from has_call.pre₁.inv this
  ),
  have h2: quantifiers (prop.pre₁ op t) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers (prop.pre₁ op t),
    show «false», from has_quantifier.pre₁.inv  this
  ),
  show (calls (prop.pre₁ op t) = ∅) ∧ (quantifiers (prop.pre₁ op t) = ∅), from ⟨h1, h2⟩

lemma no_instantiations.pre₂ {t₁ t₂: term} {op: binop}: no_instantiations (prop.pre₂ op t₁ t₂) :=
  have h1: calls (prop.pre₂ op t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls (prop.pre₂ op t₁ t₂),
    show «false», from has_call.pre₂.inv this
  ),
  have h2: quantifiers (prop.pre₂ op t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers (prop.pre₂ op t₁ t₂),
    show «false», from has_quantifier.pre₂.inv  this
  ),
  show (calls (prop.pre₂ op t₁ t₂) = ∅) ∧ (quantifiers (prop.pre₂ op t₁ t₂) = ∅), from ⟨h1, h2⟩

lemma no_instantiations.post {t₁ t₂: term}: no_instantiations (prop.post t₁ t₂) :=
  have h1: calls (prop.post t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls (prop.post t₁ t₂),
    show «false», from has_call.post.inv this
  ),
  have h2: quantifiers (prop.post t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers (prop.post t₁ t₂),
    show «false», from has_quantifier.post.inv  this
  ),
  show (calls (prop.post t₁ t₂) = ∅) ∧ (quantifiers (prop.post t₁ t₂) = ∅), from ⟨h1, h2⟩

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
