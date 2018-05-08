-- lemmas about validity of logical propositions

import .definitions2 .freevars .substitution .evaluation

lemma valid.false.elim {P: vc}: closed P → (⊨ vc.implies value.false P) :=
  assume P_closed: closed P,
  have h1: ⊨ value.true, from valid.tru,
  have unop.apply unop.not value.false = value.true, by unfold unop.apply,
  have ⊨ value.true ≡ term.unop unop.not value.false, from valid.unop.mp this,
  have ⊨ term.unop unop.not value.false, from valid.eq.true.mpr this,
  have ⊨ vc.not value.false, from valid.not.term.mp this,
  have ⊨ vc.not value.false ⋁ P, from valid.or.left this P_closed,
  show ⊨ vc.implies value.false P, from this

lemma valid.implies.mp {P Q: vc}: closed P → closed Q → ((⊨ P) → (⊨ Q)) → ⊨ vc.implies P Q :=
  assume P_closed: closed P,
  assume Q_closed: closed Q,
  assume h1: (⊨ P) → (⊨ Q),
  have ⊨ P ⋁ P.not, from valid.em P_closed,
  or.elim (valid.or.elim this) (
    assume : ⊨ P,
    have ⊨ Q, from h1 this,
    show ⊨ P.not ⋁ Q, from valid.or.right (vc.closed.not P_closed) this
  ) (
    assume : ⊨ P.not,
    show ⊨ P.not ⋁ Q, from valid.or.left this Q_closed
  )

lemma valid.implies.mpr {P Q: vc}: (⊨ vc.implies P Q) → (⊨ P) → (⊨ Q) :=
  assume h1: (⊨ P.not ⋁ Q),
  assume h2: (⊨ P),
  or.elim (valid.or.elim h1) (
    assume : ⊨ P.not,
    have ⊨ P ⋀ P.not, from valid.and.mp ⟨h2, this⟩,
    show ⊨ Q, from false.elim (valid.contradiction this)
  ) id

lemma valid.not.mp {P: vc}: closed P → (¬ ⊨ P) → ⊨ P.not :=
  assume P_closed: closed P,
  assume h1: ¬ (⊨ P),
  have ⊨ P ⋁ P.not, from valid.em P_closed,
  or.elim (valid.or.elim this) (
    assume : ⊨ P,
    show ⊨ P.not, from absurd this h1
  ) id

lemma valid.not.mpr {P: vc}: (⊨ P.not) → ¬ ⊨ P :=
  assume h2: ⊨ P.not,
  assume h3: ⊨ P,
  have ⊨ (P ⋀ P.not), from valid.and.mp ⟨h3, h2⟩,
  show «false», from valid.contradiction this

lemma valid.not_not {P: vc}: (⊨ P.not.not) ↔ ⊨ P :=
  iff.intro (
    assume h1: ⊨ P.not.not,
    have closed P.not, from vc.closed.not.inv (valid.closed h1),
    have h2: closed P, from vc.closed.not.inv this,
    have h3: ¬ ⊨ P.not, from valid.not.mpr h1,
    have h4: ¬ ¬ ⊨ P, from (
      assume : ¬ ⊨ P,
      have ⊨ P.not, from valid.not.mp h2 this,
      show «false», from h3 this
    ),
    or.elim (valid.or.elim (valid.em h2)) id (
      assume : ⊨ P.not,
      have ¬ ⊨ P, from valid.not.mpr this,
      show ⊨ P, from absurd this h4
    )
  ) (
    assume h1: ⊨ P,
    have h2: ¬ ⊨ P.not, from (
      assume : ⊨ P.not,
      have ¬ ⊨ P, from valid.not.mpr this,
      show «false», from this h1
    ),
    show ⊨ P.not.not, from valid.not.mp (vc.closed.not (valid.closed h1)) h2
  )

lemma valid.mt {P Q: vc}: (⊨ vc.implies P Q) → (⊨ Q.not) → ⊨ P.not :=
  assume h1: ⊨ vc.implies P Q,
  have P_closed: closed P, from (vc.closed.implies.inv (valid.closed h1)).left,
  assume : ⊨ Q.not,
  have h2: ¬ ⊨ Q, from valid.not.mpr this,
  have ¬ ⊨ P, from (
    assume : ⊨ P,
    have ⊨ Q, from valid.implies.mpr h1 this,
    show «false», from h2 this
  ),
  show ⊨ P.not, from valid.not.mp P_closed this

lemma valid.refl {v: value}: ⊨ (v ≡ v) :=
  have binop.apply binop.eq v v = value.true, from binop.eq_of_equal_values,
  have ⊨ (value.true ≡ (v ≡ v)), from valid.binop.mp this,
  show ⊨ (v ≡ v), from valid.eq.true.mpr this

lemma valid.implies.trans {P₁ P₂ P₃: vc}:
      (⊨ vc.implies P₁ P₂) → (⊨ vc.implies P₂ P₃) → ⊨ vc.implies P₁ P₃ :=
  assume h1: ⊨ vc.implies P₁ P₂,
  have P₁_closed: closed P₁, from (vc.closed.implies.inv (valid.closed h1)).left,
  assume h2: ⊨ vc.implies P₂ P₃,
  have P₃_closed: closed P₃, from (vc.closed.implies.inv (valid.closed h2)).right,
  show ⊨ vc.implies P₁ P₃, from valid.implies.mp P₁_closed P₃_closed (
    assume : ⊨ P₁,
    have ⊨ P₂, from valid.implies.mpr h1 this,
    show ⊨ P₃, from valid.implies.mpr h2 this
  )

lemma valid_env.closed {σ: env} {P: vc}: (σ ⊨ P) → closed_subst σ P :=
  assume : σ ⊨ P,
  have ⊨ vc.subst_env σ P, from this,
  have closed (vc.subst_env σ P), from valid.closed this,
  show closed_subst σ P, from vc.closed_subst_of_closed this

lemma valid_env.true {σ: env}: σ ⊨ value.true :=
  have h1: ⊨ value.true, from valid.tru,
  have term.subst_env σ value.true = value.true, from term.subst_env.value,
  have h2: ⊨ term.subst_env σ value.true, from this.symm ▸ h1,
  have vc.subst_env σ value.true = vc.term (term.subst_env σ value.true), from vc.subst_env.term,
  show σ ⊨ value.true, from this.symm ▸ h2

lemma valid_env.mt {σ: env} {P Q: vc}: (σ ⊨ vc.implies P Q) → (σ ⊨ Q.not) → σ ⊨ P.not :=
  assume h1: σ ⊨ vc.implies P Q,
  have vc.subst_env σ (vc.implies P Q) = vc.implies (vc.subst_env σ P) (vc.subst_env σ Q),
  from vc.subst_env.implies,
  have h2: ⊨ vc.implies (vc.subst_env σ P) (vc.subst_env σ Q), from this ▸ h1,
  assume h3: σ ⊨ Q.not,
  have vc.subst_env σ Q.not = (vc.subst_env σ Q).not, from vc.subst_env.not,
  have h4: ⊨ (vc.subst_env σ Q).not, from this ▸ h3,
  have h5: ⊨ (vc.subst_env σ P).not, from valid.mt h2 h4,
  have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  show σ ⊨ P.not, from this.symm ▸ h5

lemma valid_env.eq.true {σ: env} {t: term}: σ ⊨ t ↔ σ ⊨ (value.true ≡ t) :=
  iff.intro (
    assume t_valid: ⊨ vc.subst_env σ t,
    have vc.subst_env σ t = vc.term (term.subst_env σ t), from vc.subst_env.term,
    have ⊨ vc.term (term.subst_env σ t), from this ▸ t_valid,
    have h: ⊨ vc.term (value.true ≡ (term.subst_env σ t)), from valid.eq.true.mp this,
    have term.subst_env σ value.true = value.true, from term.subst_env.value,
    have h2: ⊨ vc.term ((term.subst_env σ value.true) ≡ (term.subst_env σ t)),
    from this.symm ▸ h,
    have (term.subst_env σ (value.true ≡ t)) = ((term.subst_env σ value.true) ≡ (term.subst_env σ t)),
    from term.subst_env.binop,
    have h3: ⊨ term.subst_env σ (value.true ≡ t), from this.symm ▸ h2,
    have vc.subst_env σ (value.true ≡ t) = vc.term (term.subst_env σ (value.true ≡ t)), from vc.subst_env.term,
    show σ ⊨ (value.true ≡ t), from this.symm ▸ h3
  ) (
    assume t_valid: ⊨ vc.subst_env σ (value.true ≡ t),
    have vc.subst_env σ (value.true ≡ t) = vc.term (term.subst_env σ (value.true ≡ t)), from vc.subst_env.term,
    have h: ⊨ vc.term (term.subst_env σ (value.true ≡ t)),
    from this ▸ t_valid,
    have (term.subst_env σ (value.true ≡ t)) = ((term.subst_env σ value.true) ≡ (term.subst_env σ t)),
    from term.subst_env.binop,
    have h2: ⊨ vc.term ((term.subst_env σ value.true) ≡ (term.subst_env σ t)),
    from this ▸ h,
    have term.subst_env σ value.true = value.true, from term.subst_env.value,
    have ⊨ vc.term (value.true ≡ (term.subst_env σ t)), from this ▸ h2,
    have h3: ⊨ vc.term (term.subst_env σ t), from valid.eq.true.mpr this,
    have vc.subst_env σ t = vc.term (term.subst_env σ t), from vc.subst_env.term,
    show ⊨ vc.subst_env σ t, from this.symm ▸ h3
  )

lemma valid_env.not_not {σ: env} {P: vc}: (σ ⊨ P.not.not) ↔ σ ⊨ P :=
  iff.intro (
    assume h1: σ ⊨ P.not.not,
    have vc.subst_env σ P.not.not = (vc.subst_env σ P.not).not, from vc.subst_env.not,
    have h2: ⊨ (vc.subst_env σ P.not).not, from this ▸ h1,
    have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
    have  ⊨ (vc.subst_env σ P).not.not, from this ▸ h2,
    show σ ⊨ P, from valid.not_not.mp this
  ) (
    assume : σ ⊨ P,
    have h1: ⊨ (vc.subst_env σ P).not.not, from valid.not_not.mpr this,
    have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
    have h2: ⊨ (vc.subst_env σ P.not).not, from this.symm ▸ h1,
    have vc.subst_env σ P.not.not = (vc.subst_env σ P.not).not, from vc.subst_env.not,
    show σ ⊨ P.not.not, from this.symm ▸ h2
  )

lemma valid_env.and {σ: env} {P Q: vc}: (σ ⊨ P) → (σ ⊨ Q) → σ ⊨ (P ⋀ Q) :=
  assume p_valid: ⊨ vc.subst_env σ P,
  assume q_valid: ⊨ vc.subst_env σ Q,
  have vc.subst_env σ (P ⋀ Q) = (vc.subst_env σ P ⋀ vc.subst_env σ Q), from vc.subst_env.and,
  show σ ⊨ (P ⋀ Q), from this.symm ▸ valid.and.mp ⟨p_valid, q_valid⟩

lemma valid_env.and.elim {σ: env} {P Q: vc}: (σ ⊨ P ⋀ Q) → (σ ⊨ P) ∧ σ ⊨ Q :=
  assume p_and_q_valid: ⊨ vc.subst_env σ (P ⋀ Q),
  have vc.subst_env σ (P ⋀ Q) = (vc.subst_env σ P ⋀ vc.subst_env σ Q), from vc.subst_env.and,
  have ⊨ (vc.subst_env σ P ⋀ vc.subst_env σ Q), from this ▸ p_and_q_valid,
  show (σ ⊨ P) ∧ (σ ⊨ Q), from valid.and.mpr this

lemma valid_env.or₁ {σ: env} {P Q: vc}: (σ ⊨ P) → closed_subst σ Q → σ ⊨ (P ⋁ Q) :=
  assume h1: ⊨ vc.subst_env σ P,
  assume : closed_subst σ Q,
  have h2: closed (vc.subst_env σ Q), from vc.closed_of_closed_subst this,
  have h: ⊨ vc.subst_env σ P ⋁ vc.subst_env σ Q, from valid.or.left h1 h2,
  have vc.subst_env σ (P ⋁ Q) = (vc.subst_env σ P ⋁ vc.subst_env σ Q), from vc.subst_env.or,
  show σ ⊨ (P ⋁ Q), from this.symm ▸ h

lemma valid_env.or₂ {σ: env} {P Q: vc}: closed_subst σ P → (σ ⊨ Q) → σ ⊨ (P ⋁ Q) :=
  assume : closed_subst σ P,
  have h1: closed (vc.subst_env σ P), from vc.closed_of_closed_subst this,
  assume h2: ⊨ vc.subst_env σ Q,
  have h: ⊨ vc.subst_env σ P ⋁ vc.subst_env σ Q, from valid.or.right h1 h2,
  have vc.subst_env σ (P ⋁ Q) = (vc.subst_env σ P ⋁ vc.subst_env σ Q), from vc.subst_env.or,
  show σ ⊨ (P ⋁ Q), from this.symm ▸ h

lemma valid_env.or.elim {σ: env} {P Q: vc}: (σ ⊨ P ⋁ Q) → (σ ⊨ P) ∨ σ ⊨ Q :=
  assume p_or_q_valid: ⊨ vc.subst_env σ (P ⋁ Q),
  have vc.subst_env σ (P ⋁ Q) = (vc.subst_env σ P ⋁ vc.subst_env σ Q), from vc.subst_env.or,
  have ⊨ (vc.subst_env σ P ⋁ vc.subst_env σ Q), from this ▸ p_or_q_valid,
  show (σ ⊨ P) ∨ (σ ⊨ Q), from valid.or.elim this

lemma valid_env.not.mp {σ: env} {P: vc}: closed_subst σ P → ¬ (σ ⊨ P) → (σ ⊨ P.not) :=
  assume P_closed: closed_subst σ P,
  assume h1: ¬ (σ ⊨ P),
  have h2: vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  have ¬ ⊨ (vc.subst_env σ P), from h2 ▸ h1,
  have ⊨ (vc.subst_env σ P).not, from valid.not.mp (vc.closed_of_closed_subst P_closed) this,
  show σ ⊨ P.not, from h2.symm ▸ this

lemma valid_env.not.mpr {σ: env} {P: vc}: (σ ⊨ P.not) → ¬ (σ ⊨ P) :=
  assume h1: σ ⊨ P.not,
  have h2: vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  have ⊨ (vc.subst_env σ P).not, from h2 ▸ h1,
  have ¬ ⊨ (vc.subst_env σ P), from valid.not.mpr this,
  show ¬ (σ ⊨ P), from h2.symm ▸ this

lemma valid_env.mp {σ: env} {P Q: vc}: (σ ⊨ vc.implies P Q) → (σ ⊨ P) → σ ⊨ Q :=
  assume impl: σ ⊨ (vc.implies P Q),
  assume p: σ ⊨ P,
  have vc.subst_env σ (vc.implies P Q) = (vc.subst_env σ P.not ⋁ vc.subst_env σ Q), from vc.subst_env.or,
  have h: ⊨ (vc.subst_env σ P.not ⋁ vc.subst_env σ Q), from this ▸ impl,
  have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  have ⊨ ((vc.subst_env σ P).not ⋁ vc.subst_env σ Q), from this ▸ h,
  have ⊨ vc.implies (vc.subst_env σ P) (vc.subst_env σ Q), from this,
  show σ ⊨ Q, from valid.implies.mpr this p

lemma valid_env.mpr {σ: env} {P Q: vc}:
      closed_subst σ P → closed_subst σ Q → ((σ ⊨ P) → (σ ⊨ Q)) → σ ⊨ vc.implies P Q :=
  assume : closed_subst σ P,
  have P_closed: closed (vc.subst_env σ P), from vc.closed_of_closed_subst this,
  assume : closed_subst σ Q,
  have Q_closed: closed (vc.subst_env σ Q), from vc.closed_of_closed_subst this,
  assume : ((σ ⊨ P) → σ ⊨ Q),
  have ⊨ vc.implies (vc.subst_env σ P) (vc.subst_env σ Q), from valid.implies.mp P_closed Q_closed this,
  have h1: ⊨ vc.or (vc.subst_env σ P).not (vc.subst_env σ Q), from this,
  have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  have h2: ⊨ vc.or (vc.subst_env σ P.not) (vc.subst_env σ Q), from this.symm ▸ h1,
  have vc.subst_env σ (P.not ⋁ Q) = (vc.subst_env σ P.not ⋁ vc.subst_env σ Q),
  from vc.subst_env.or,
  have ⊨ vc.subst_env σ (P.not ⋁ Q), from this.symm ▸ h2,
  show σ ⊨ vc.implies P Q, from this

lemma valid_env.implies.trans {σ: env} {P₁ P₂ P₃: vc}:
      (σ ⊨ vc.implies P₁ P₂) → (σ ⊨ vc.implies P₂ P₃) → σ ⊨ vc.implies P₁ P₃ :=
  assume h1: σ ⊨ vc.implies P₁ P₂,
  have P₁_closed: closed_subst σ P₁, from (vc.closed_subst.implies.inv (valid_env.closed h1)).left,
  assume h2: σ ⊨ vc.implies P₂ P₃,
  have P₃_closed: closed_subst σ P₃, from (vc.closed_subst.implies.inv (valid_env.closed h2)).right,
  show σ ⊨ vc.implies P₁ P₃, from valid_env.mpr P₁_closed P₃_closed (
    assume : σ ⊨ P₁,
    have σ ⊨ P₂, from valid_env.mp h1 this,
    show σ ⊨ P₃, from valid_env.mp h2 this
  )

lemma env.contains_of_valid_env_term {σ: env} {x: var} {t: term}:
      x ∈ FV t → (σ ⊨ t) → (x ∈ σ) :=
  assume x_free_in_t: x ∈ FV t,
  assume h1: σ ⊨ vc.term t,
  have h2: ⊨ vc.subst_env σ (vc.term t), from h1,
  have vc.subst_env σ (vc.term t) = vc.term (term.subst_env σ t),
  from vc.subst_env.term,
  have ⊨ vc.term (term.subst_env σ t), from this ▸ h2,
  have closed (vc.term (term.subst_env σ t)), from valid.closed this,
  have h3: closed (term.subst_env σ t), from vc.closed.term.inv this,
  show x ∈ σ, from by_contradiction (
    assume : x ∉ σ,
    have x ∈ FV (term.subst_env σ t), from term.free_of_subst_env x_free_in_t this,
    show «false», from h3 x this
  )

lemma valid_env.subst_of_eq {σ: env} {x: var} {v: value}:
      (σ ⊨ x ≡ v) → (σ x = v) :=
  assume h1: σ ⊨ vc.term (x ≡ v),
  have h2: ⊨ vc.subst_env σ (vc.term (x ≡ v)), from h1,
  have vc.subst_env σ (vc.term (x ≡ v)) = vc.term (term.subst_env σ (x ≡ v)),
  from vc.subst_env.term,
  have h3: ⊨ vc.term (term.subst_env σ (x ≡ v)), from this ▸ h2,
  have term.subst_env σ (x ≡ v) = (term.subst_env σ x ≡ term.subst_env σ v),
  from term.subst_env.binop,
  have h4: ⊨ (term.subst_env σ x ≡ term.subst_env σ v), from this ▸ h3,
  have term.subst_env σ v = v, from term.subst_env.value,
  have h5: ⊨ (term.subst_env σ x ≡ v), from this ▸ h4,
  have x ∈ σ, from env.contains_of_valid_env_term (free_in_term.binop₁ (free_in_term.var x)) h1,
  have ∃v', σ x = some v', from env.contains_apply_equiv.right.mpr this,
  let ⟨v', h6⟩ := this in
  have term.subst_env σ x = v', from (term.subst_env.var.right v').mp h6,
  have ⊨ (v' ≡ v), from this ▸ h5,
  have ⊨ value.true ≡ (v' ≡ v), from valid.eq.true.mp this,
  have binop.apply binop.eq v' v = some value.true, from valid.binop.mpr this,
  have v' = v, from binop.eq.inv this,
  show σ x = some v, from h6.symm ▸ (some.inj.inv this)

/-

lemma valid_env.subst_of_eq_instantiated_p {σ: env} {x: var} {v: value}:
      (σ ⊨ prop.instantiated_p (x ≡ v)) → (σ x = v) :=
  assume h0: σ ⊨ prop.instantiated_p (x ≡ v),
  have calls_p (prop.term (x ≡ v)) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_p (prop.term (x ≡ v)),
    show «false», from prop.has_call_p.term.inv this
  ),
  have (prop.term (x ≡ v)).instantiated_p = (prop.term (x ≡ v)).erased_p,
  from instantiated_p_eq_erased_p_without_calls this,
  have h1: σ ⊨ prop.erased_p (x ≡ v), from this ▸ h0,
  have prop.erased_p (prop.term (x ≡ v)) = vc.term (x ≡ v),
  by unfold prop.erased_p,
  have σ ⊨ vc.term (x ≡ v), from this.symm ▸ h1,
  show σ x = v, from valid_env.subst_of_eq this

lemma valid_env.subst_of_eq_instantiated_n {σ: env} {x: var} {v: value}:
      (σ ⊨ prop.instantiated_n (x ≡ v)) → (σ x = v) :=
  assume h0: σ ⊨ prop.instantiated_n (x ≡ v),
  have calls_n (prop.term (x ≡ v)) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n (prop.term (x ≡ v)),
    show «false», from prop.has_call_n.term.inv this
  ),
  have (prop.term (x ≡ v)).instantiated_n = (prop.term (x ≡ v)).erased_n,
  from instantiated_n_eq_erased_n_without_calls this,
  have h1: σ ⊨ prop.erased_n (x ≡ v), from this ▸ h0,
  have prop.erased_n (prop.term (x ≡ v)) = vc.term (x ≡ v),
  by unfold prop.erased_n,
  have σ ⊨ vc.term (x ≡ v), from this.symm ▸ h1,
  show σ x = v, from valid_env.subst_of_eq this

lemma history_valid {H: history}: ⟪calls_to_prop H⟫ :=
  assume σ: env,
  begin
    induction H with H₁ f y R S e H₂ σ₂ v ih₁ ih₂,

    show σ ⊨ (calls_to_prop history.empty).instantiated_n, from (
      have h1: σ ⊨ value.true, from valid_env.true,
      have (prop.term value.true).erased_n = vc.term value.true, by unfold prop.erased_n,
      have h2: σ ⊨ (prop.term value.true).erased_n, from this ▸ h1,
      have calls_n (prop.term value.true) = ∅, from set.eq_empty_of_forall_not_mem (
        assume c: calltrigger,
        assume : c ∈ calls_n (prop.term value.true),
        show «false», from prop.has_call_n.term.inv this
      ),
      have (prop.term value.true).instantiated_n = (prop.term value.true).erased_n,
      from instantiated_n_eq_erased_n_without_calls this,
      have h3: σ ⊨ (prop.term value.true).instantiated_n, from this.symm ▸ h2, 
      have calls_to_prop history.empty = value.true, by unfold calls_to_prop,
      show σ ⊨ (calls_to_prop history.empty).instantiated_n, from this ▸ h3
    ),

    show σ ⊨ prop.instantiated_n (calls_to_prop (H₁ · call f y R S e H₂ σ₂ v)), from (
      have h1: σ ⊨ (calls_to_prop H₁).instantiated_n, from ih₁,
      have h2: σ ⊨ value.true, from valid_env.true,
      have (prop.call (value.func f y R S e H₂ σ₂) v).erased_n = vc.term value.true, by unfold prop.erased_n,
      have h3: σ ⊨ (prop.call (value.func f y R S e H₂ σ₂) v).erased_n, from this ▸ h2,

      have quantifiers_n (prop.call (value.func f y R S e H₂ σ₂) v) = ∅, from set.eq_empty_of_forall_not_mem (
        assume q: callquantifier,
        assume : q ∈ quantifiers_n (prop.call (value.func f y R S e H₂ σ₂) v),
        show «false», from prop.has_quantifier_n.call.inv this
      ),
      have (prop.call (value.func f y R S e H₂ σ₂) v).instantiated_n
         = (prop.call (value.func f y R S e H₂ σ₂) v).erased_n,
      from instantiated_n_eq_erased_n_without_quantifiers this,

      have h4: σ ⊨ (prop.call (value.func f y R S e H₂ σ₂) v).instantiated_n,
      from this.symm ▸ h3,

      have σ ⊨ ((calls_to_prop H₁).instantiated_n ⋀ (prop.call (value.func f y R S e H₂ σ₂) v).instantiated_n),
      from valid_env.and h1 h4,
      have h4: σ ⊨ (calls_to_prop H₁ ⋀ prop.call (value.func f y R S e H₂ σ₂) v).instantiated_n,
      from valid_env.instantiated_n_and this,
      have calls_to_prop (H₁ · call f y R S e H₂ σ₂ v)
        = (calls_to_prop H₁ ⋀ prop.call (value.func f y R S e H₂ σ₂) v),
      by unfold calls_to_prop,
      show σ ⊨ (calls_to_prop (H₁ · call f y R S e H₂ σ₂ v)).instantiated_n, from this ▸ h4
    )
  end

lemma val_of_free_in_env {P: prop} {σ: env} {x: var}: (⊢ σ : P) → x ∈ FV P → ∃v, σ x = some v :=
  assume env_verified: ⊢ σ: P,
  assume x_free_in_P: x ∈ FV P,
  have x ∈ σ, from contains_of_free env_verified x_free_in_P,
  show ∃v, σ x = some v, from env.contains_apply_equiv.right.mpr this

lemma val_of_free_in_hist_env {R: spec} {H: history} {σ: env} {P: prop} {x: var}:
                              (⊢ σ : P) → FV R.to_prop ⊆ FV P → x ∈ FV (R.to_prop ⋀ ↑H ⋀ P) → ∃v, σ x = some v :=
  assume σ_verified: ⊢ σ : P,
  assume fv_R: FV R.to_prop ⊆ FV P,
  assume x_free_in_R_H_P: x ∈ FV (R.to_prop ⋀ ↑H ⋀ P),
  have FV (R.to_prop ⋀ ↑H ⋀ P) = FV ((R.to_prop ⋀ ↑H) ⋀ P), from free_in_prop.and_assoc,
  have x ∈ FV ((R.to_prop ⋀ ↑H) ⋀ P), from this ▸ x_free_in_R_H_P,
  have free_in_prop x (R.to_prop ⋀ ↑H) ∨ free_in_prop x P, from free_in_prop.and.inv this,
  have x ∈ FV P, from or.elim this.symm id (
    assume : free_in_prop x (R.to_prop ⋀ ↑H),
    or.elim (free_in_prop.and.inv this) (
      assume : free_in_prop x R.to_prop,
      show x ∈ FV P, from set.mem_of_mem_of_subset this fv_R
    ) (
      assume : free_in_prop x H,
      show free_in_prop x P, from absurd this (call_history_closed H x)
    )
  ),
  show ∃v, σ x = some v, from val_of_free_in_env σ_verified this

lemma simple_equality_valid {σ: env} {x: var} {v: value}:
  x ∉ σ → (σ[x↦v]) ⊨ (prop.term (x ≡ v)).erased_n :=
  assume x_not_free_in_σ: x ∉ σ,
  have σ.apply x = none, from env.contains_apply_equiv.left.mpr x_not_free_in_σ,
  have h1: term.subst_env σ x = x, from term.subst_env.var.left.mp this,
  have (term.subst_env (σ[x↦v]) x = term.subst x v (term.subst_env σ x)),
  by unfold term.subst_env,
  have h2: term.subst_env (σ[x↦v]) x = term.subst x v x,
  from @eq.subst term (λa, term.subst_env (σ[x↦v]) x = term.subst x v a) (term.subst_env σ x) x h1 this,
  have term.subst x v (term.var x) = (if x = x then v else x), by unfold term.subst,
  have term.subst x v (term.var x) = v, by simp[this],
  have h3: term.subst_env (σ[x↦v]) x = v, from eq.trans h2 this,
  have h4: term.subst_env (σ[x↦v]) v = v, from term.subst_env.value,
  have term.subst_env (σ[x↦v]) (x ≡ v) = (term.subst_env (σ[x↦v]) x ≡ term.subst_env (σ[x↦v]) v),
  from term.subst_env.binop,
  have term.subst_env (σ[x↦v]) (x ≡ v) = (v ≡ term.subst_env (σ[x↦v]) v),
  from @eq.subst term (λa, term.subst_env (σ[x↦v]) (x ≡ v) = (a ≡ term.subst_env (σ[x↦v]) v))
                      (term.subst_env (σ[x↦v]) x) v h3 this,
  have h5: term.subst_env (σ[x↦v]) (x ≡ v) = (v ≡ v),
  from @eq.subst term (λa, term.subst_env (σ[x↦v]) (x ≡ v) = (v ≡ a))
                      (term.subst_env (σ[x↦v]) v) v h4 this,
  have h6: vc.term (term.subst_env (σ[x↦v]) (x ≡ v)) = vc.term (v ≡ v), by simp[h5],
  have vc.subst_env (σ[x↦v]) (x ≡ v) = vc.term (term.subst_env (σ[x↦v]) (x ≡ v)), from vc.subst_env.term,
  have h7: vc.subst_env (σ[x↦v]) (vc.term (x ≡ v)) = vc.term (v ≡ v), from eq.trans this h6,
  have prop.erased_n (prop.term (x ≡ v)) = vc.term (x ≡ v), by unfold prop.erased_n,
  have h8: vc.subst_env (σ[x↦v]) (prop.term (x ≡ v)).erased_n = vc.term (v ≡ v), from this.symm ▸ h7,
  have ⊨ vc.term (v ≡ v), from valid.refl,
  show (σ[x↦v]) ⊨ prop.erased_n (x ≡ v), from h8.symm ▸ this

lemma simple_equality_env_valid {P: prop} {σ: env} {x: var} {v: value}:
                                   (⊢ σ: P) → x ∉ σ → (σ ⊨ P.instantiated_n) → ((σ[x↦v]) ⊨ P.instantiated_n)
                                                             ∧ ((σ[x↦v]) ⊨ (prop.term (x ≡ v)).instantiated_n) :=
  assume σ_verified: ⊢ σ: P,
  assume x_not_free_in_σ: x ∉ σ,
  assume ih: σ ⊨ P.instantiated_n,
  have σ.apply x = none, from env.contains_apply_equiv.left.mpr x_not_free_in_σ,
  have h1: ⊨ vc.subst_env σ P.instantiated_n, from ih,
  have x_not_in_P: x ∉ FV (vc.subst_env σ P.instantiated_n), from (
    assume : x ∈ FV (vc.subst_env σ P.instantiated_n),
    have x ∈ FV P.instantiated_n, from free_in_vc.subst_env this,
    have x ∈ FV P, from free_of_instantiated_n_free this,
    have ∃v, σ x = some v, from val_of_free_in_env σ_verified this,
    have x ∈ σ, from env.contains_apply_equiv.right.mp this,
    show «false», from x_not_free_in_σ this
  ),
  have vc.subst x v (vc.subst_env σ P.instantiated_n) = vc.subst_env σ P.instantiated_n,
  from unchanged_of_subst_nonfree_vc x_not_in_P,
  have h2: ⊨ vc.subst x v (vc.subst_env σ P.instantiated_n),
  from @eq.subst vc (λa, ⊨ a) (vc.subst_env σ P.instantiated_n)
          (vc.subst x v (vc.subst_env σ P.instantiated_n)) this.symm h1,
  have vc.subst x v (vc.subst_env σ P.instantiated_n)
      = vc.subst_env (σ[x↦v]) P.instantiated_n, by unfold vc.subst_env, 
  have h3: ⊨ vc.subst_env (σ[x↦v]) P.instantiated_n, from this ▸ h2,
  have h4: (σ[x↦v]) ⊨ (prop.term (x ≡ v)).erased_n,
  from simple_equality_valid x_not_free_in_σ,

  have calls_n (prop.term (x ≡ v)) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n (prop.term (x ≡ v)),
    show «false», from prop.has_call_n.term.inv this
  ),
  have (prop.term (x ≡ v)).instantiated_n = (prop.term (x ≡ v)).erased_n,
  from instantiated_n_eq_erased_n_without_calls this,
  have (σ[x↦v]) ⊨ (prop.term (x ≡ v)).instantiated_n, from this.symm ▸ h4,
  ⟨h3, this⟩

lemma simple_equality_env_inst_valid {P: prop} {σ: env} {x: var} {v: value}:
                                   (⊢ σ: P) → x ∉ σ → (σ ⊨ P.instantiated_n) → (σ[x↦v]) ⊨ (P ⋀ x ≡ v).instantiated_n :=
  assume σ_verified: ⊢ σ: P,
  assume x_not_free_in_σ: x ∉ σ,
  assume ih: σ ⊨ P.instantiated_n,
  have ((σ[x↦v]) ⊨ P.instantiated_n) ∧ ((σ[x↦v]) ⊨ (prop.term (x ≡ v)).instantiated_n),
  from simple_equality_env_valid σ_verified x_not_free_in_σ ih,
  have (σ[x↦v]) ⊨ (P.instantiated_n ⋀ (prop.term (x ≡ v)).instantiated_n),
  from valid_env.and this.left this.right,
  show (σ[x↦v]) ⊨ prop.instantiated_n (P ⋀ (x ≡ v)), from valid_env.instantiated_n_and this

lemma env_translation_instantiated_n_valid {P: prop} {σ: env}: (⊢ σ: P) → σ ⊨ P.instantiated_n :=
  assume env_verified: (⊢ σ : P),
  begin
    induction env_verified,
    case env.vcgen.empty {
      show env.empty ⊨ prop.instantiated_n (value.true), from (
        have h: prop.erased_n (prop.term ↑value.true) = vc.term ↑value.true, by unfold prop.erased_n,
        have env.empty ⊨ value.true, from valid.tru,
        have h2: env.empty ⊨ prop.erased_n (value.true), from h ▸ this,

        have calls_n (prop.term value.true) = ∅, from set.eq_empty_of_forall_not_mem (
          assume c: calltrigger,
          assume : c ∈ calls_n (prop.term value.true),
          show «false», from prop.has_call_n.term.inv this
        ),
        have (prop.term value.true).instantiated_n = (prop.term value.true).erased_n,
        from instantiated_n_eq_erased_n_without_calls this,
        
        show env.empty ⊨ prop.instantiated_n (value.true), from this.symm ▸ h2
      )
    },
    case env.vcgen.tru σ' x' Q x_not_free_in_σ' σ'_verified ih {
      show (σ'[x'↦value.true]) ⊨ prop.instantiated_n (Q ⋀ (x' ≡ value.true)),
      from simple_equality_env_inst_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.vcgen.fls σ' x' Q x_not_free_in_σ' σ'_verified ih {
      show (σ'[x'↦value.false]) ⊨ prop.instantiated_n (Q ⋀ (x' ≡ value.false)),
      from simple_equality_env_inst_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.vcgen.num n σ' x' Q x_not_free_in_σ' σ'_verified ih {
      show (σ'[x'↦value.num n]) ⊨ prop.instantiated_n (Q ⋀ (x' ≡ value.num n)),
      from simple_equality_env_inst_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.vcgen.func σ₁ σ₂ f g gx R S e H Q₁ Q₂ Q₃
      f_not_free_in_σ₁ g_not_free_in_σ₂ gx_not_free_in_σ₂ g_neq_gx σ₁_verified σ₂_verified gx_free_in_R R_fv S_fv func_verified
      S_valid ih₁ ih₂ { from (
      let vf := value.func g gx R S e H σ₂ in
      have h1: ((σ₁[f↦vf]) ⊨ Q₁.instantiated_n) ∧ ((σ₁[f↦vf]) ⊨ (prop.term (f ≡ vf)).instantiated_n),
      from simple_equality_env_valid σ₁_verified f_not_free_in_σ₁ ih₁,

      have g_subst: term.subst_env (σ₂[g↦vf]) g = vf, from (
        have h1: term.subst g vf g = vf, from term.subst.var.same,
        have σ₂ g = none, from env.contains_apply_equiv.left.mpr g_not_free_in_σ₂,
        have term.subst_env σ₂ g = g, from term.subst_env.var.left.mp this,
        have h2: term.subst g vf (term.subst_env σ₂ g) = vf, from this.symm ▸ h1,
        have term.subst_env (σ₂[g↦vf]) g = term.subst g vf (term.subst_env σ₂ g), by unfold term.subst_env,
        show term.subst_env (σ₂[g↦vf]) g = vf, from eq.trans this h2
      ),

      have h2: ⊨ prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from (
        have unop.apply unop.isFunc vf = value.true, by unfold unop.apply,
        have ⊨ (value.true ≡ term.unop unop.isFunc vf), from valid.unop.mp this,
        have ⊨ term.unop unop.isFunc vf, from valid.eq.true.mpr this,
        have h3: ⊨ term.unop unop.isFunc (term.subst_env (σ₂[g↦vf]) g), from g_subst.symm ▸ this,
        have term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g) = term.unop unop.isFunc (term.subst_env (σ₂[g↦vf]) g),
        from term.subst_env.unop,
        have h4: ⊨ vc.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from this.symm ▸ h3,
        have prop.erased_n (prop.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)))
           = vc.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)),
        by unfold prop.erased_n,
        have h5: ⊨ prop.erased_n (prop.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g))), from this.symm ▸ h4,
        have prop.subst_env (σ₂[g↦vf]) (prop.term (term.unop unop.isFunc g))
           = prop.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from prop.subst_env.term,
        have h6: ⊨ prop.erased_n (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from this.symm ▸ h5,

        have calls_n (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)) = ∅, from set.eq_empty_of_forall_not_mem (
          assume c: calltrigger,
          assume : c ∈ calls_n (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)),
          have ∃c', c' ∈ calls_n (term.unop unop.isFunc g), from prop.has_call_of_subst_env_has_call.right c this,
          let ⟨c', h7⟩ := this in
          show «false», from prop.has_call_n.term.inv h7
        ),
        have (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)).instantiated_n
           = (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)).erased_n,
        from instantiated_n_eq_erased_n_without_calls this,

        show ⊨ prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)),
        from this.symm ▸ h6
      ),

      let forallp := prop.implies R.to_prop (prop.pre g gx)
                  ⋀ prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop) in
      let pfunc: prop := prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S)) in

      have h4: ∀v, ⊨ vc.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp).instantiated_n, from (
        assume v: value,

        have h5: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))).instantiated_n, from (

          have h51: (σ₂[g↦vf][gx↦v]).dom = σ₂.dom ∪ {g, gx}, from env.dom.two_elems,
          have σ₂.dom = FV Q₂, from free_iff_contains σ₂_verified,
          have h52: (σ₂[g↦vf][gx↦v]).dom = FV Q₂ ∪ {g, gx}, from this ▸ h51,
          have FV R.to_prop ⊆ (σ₂[g↦vf][gx↦v]).dom, from h52.symm ▸ R_fv,
          have closed (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop), from prop.closed_of_closed_subst this,
          have h53: closed (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).instantiated_p,
          from instantiated_p_closed_of_closed this,

          have FV (prop.pre g gx) ⊆ FV Q₂ ∪ {g, gx}, from (
            assume x: var,
            assume : x ∈ FV (prop.pre g gx),
            or.elim (free_in_prop.pre.inv this) (
              assume : free_in_term x g,
              have x = g, from free_in_term.var.inv this,
              have x ∈ {g, gx}, from set.two_elems_mem.inv (or.inl this),
              show x ∈ FV Q₂ ∪ {g, gx}, from set.mem_union_right (FV Q₂) this
            ) (
              assume : free_in_term x gx,
              have x = gx, from free_in_term.var.inv this,
              have x ∈ {g, gx}, from set.two_elems_mem.inv (or.inr this),
              show x ∈ FV Q₂ ∪ {g, gx}, from set.mem_union_right (FV Q₂) this
            )
          ),
          have FV (prop.pre g gx) ⊆ (σ₂[g↦vf][gx↦v]).dom, from h52.symm ▸ this,
          have closed (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)), from prop.closed_of_closed_subst this,
          have h54: closed (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).instantiated_n,
          from instantiated_n_closed_of_closed this,

          have h6: ⊨ vc.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).instantiated_p
                                (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).instantiated_n,
          from valid.implies.mp h53 h54 (
            assume h8: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).instantiated_p,
            have vc.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop.instantiated_p
                = (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).instantiated_p, from instantiated_p_distrib_subst_env,
            have ⊨ vc.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop.instantiated_p, from this.symm ▸ h8,
            have h9: ⊨ vc.pre vf v, from valid.pre.mp this,
            have term.subst gx v gx = v, from term.subst.var.same,
            have h10: ⊨ vc.pre vf (term.subst gx v gx), from this.symm ▸ h9,
            have ¬(gx = g ∨ gx ∈ σ₂), from not_or_distrib.mpr ⟨g_neq_gx.symm, gx_not_free_in_σ₂⟩,
            have gx ∉ (σ₂[g↦vf]), from (mt env.contains.inv) this,
            have (σ₂[g↦vf]) gx = none, from env.contains_apply_equiv.left.mpr this,
            have term.subst_env (σ₂[g↦vf]) gx = gx, from term.subst_env.var.left.mp this,
            have h11: ⊨ vc.pre vf (term.subst gx v (term.subst_env (σ₂[g↦vf]) gx)),
            from this.symm ▸ h10,
            have term.subst_env (σ₂[g↦vf][gx↦v]) gx = term.subst gx v (term.subst_env (σ₂[g↦vf]) gx),
            by unfold term.subst_env,
            have h12: ⊨ vc.pre vf (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from this.symm ▸ h11,
            have term.subst gx v (term.value vf) = vf, by unfold term.subst,
            have ⊨ vc.pre (term.subst gx v vf) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from this.symm ▸ h12,
            have h13: ⊨ vc.pre (term.subst gx v (term.subst_env (σ₂[g↦vf]) g)) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from g_subst.symm ▸ this,
            have term.subst_env (σ₂[g↦vf][gx↦v]) g = term.subst gx v (term.subst_env (σ₂[g↦vf]) g),
            by unfold term.subst_env,
            have h14: ⊨ vc.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from this.symm ▸ h13,
            have prop.erased_n (prop.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx))
               = (vc.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx)),
            by unfold prop.erased_n,
            have h15: ⊨ (prop.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx)).erased_n,
            from this.symm ▸ h14,
            have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)
               = prop.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from prop.subst_env.pre,
            have h16: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).erased_n, from this.symm ▸ h15,

            have calls_n (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)) = ∅,
            from set.eq_empty_of_forall_not_mem (
              assume c: calltrigger,
              assume : c ∈ calls_n (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)),
              have ∃c', c' ∈ calls_n (prop.pre g gx), from prop.has_call_of_subst_env_has_call.right c this,
              let ⟨c', h17⟩ := this in
              show «false», from prop.has_call_n.pre.inv h17
            ),
            have (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).instantiated_n
              = (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).erased_n,
            from instantiated_n_eq_erased_n_without_calls this,

            show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).instantiated_n,
            from this.symm ▸ h16
          ),
          have h8: ⊨ (prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop)
                                   (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx))).instantiated_n,
          from valid.instantiated_n_implies h6,
          have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))
             = prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop)
                            (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)),
          from prop.subst_env.implies,
          show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))).instantiated_n,
          from this.symm ▸ h8
        ),

        have h6: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                     (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated_n, from (

          have h61: (σ₂[g↦vf][gx↦v]).dom = σ₂.dom ∪ {g, gx}, from env.dom.two_elems,
          have σ₂.dom = FV Q₂, from free_iff_contains σ₂_verified,
          have h62: (σ₂[g↦vf][gx↦v]).dom = FV Q₂ ∪ {g, gx}, from this ▸ h61,

          have FV (Q₃ (term.app g gx) ⋀ S.to_prop) ⊆ FV Q₂ ∪ {g, gx}, from (
            assume x: var,
            assume : x ∈ FV (Q₃ (term.app g gx) ⋀ S.to_prop),
            or.elim (free_in_prop.and.inv this) (
              assume : x ∈ FV (Q₃ (term.app g gx)),
              have x ∈ FV (term.app g gx) ∨ x ∈ FV (↑H ⋀ Q₂ ⋀ spec.func ↑g gx R S ⋀ R),
              from exp.post_free func_verified (term.app g gx) this,
              or.elim this (
                assume : x ∈ FV (term.app g gx),
                or.elim (free_in_term.app.inv this) (
                  assume : free_in_term x g,
                  have x = g, from free_in_term.var.inv this,
                  have x ∈ {g, gx}, from set.two_elems_mem.inv (or.inl this),
                  show x ∈ FV Q₂ ∪ {g, gx}, from set.mem_union_right (FV Q₂) this
                ) (
                  assume : free_in_term x gx,
                  have x = gx, from free_in_term.var.inv this,
                  have x ∈ {g, gx}, from set.two_elems_mem.inv (or.inr this),
                  show x ∈ FV Q₂ ∪ {g, gx}, from set.mem_union_right (FV Q₂) this
                )
              ) (
                assume : x ∈ FV (↑H ⋀ Q₂ ⋀ spec.func ↑g gx R S ⋀ R),
                or.elim (free_in_prop.and.inv this) (
                  assume : free_in_prop x H,
                  show x ∈ FV Q₂ ∪ {g, gx}, from absurd this (call_history_closed H x)
                ) (
                  assume : x ∈ FV (Q₂ ⋀ spec.func ↑g gx R S ⋀ R),
                  or.elim (free_in_prop.and.inv this) (
                    assume : x ∈ FV Q₂,
                    show x ∈ FV Q₂ ∪ {g, gx}, from set.mem_union_left {g, gx} this
                  ) (
                    assume : free_in_prop x (spec.func ↑g gx R S ⋀ R),
                    have free_in_prop x (spec.func ↑g gx R S ⋀ R), from this,
                    or.elim (free_in_prop.and.inv this) (
                      assume : free_in_prop x (spec.func ↑g gx R S),
                      have h63: free_in_prop x (spec.func ↑g gx R S).to_prop, from this,
                      have spec.to_prop (spec.func ↑g gx R S) = (prop.func ↑g gx R.to_prop S.to_prop),
                      by unfold spec.to_prop,
                      have h64: free_in_prop x (prop.func ↑g gx R S), from this ▸ h63,
                      let forallp := prop.implies R.to_prop (prop.pre g gx)
                                  ⋀ prop.implies (prop.post g gx) S.to_prop in
                      have prop.func g gx R.to_prop S.to_prop
                        = (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp),
                      by unfold prop.func,
                      have free_in_prop x (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp),
                      from this ▸ h64,
                      or.elim (free_in_prop.and.inv this) (
                        assume : free_in_prop x (term.unop unop.isFunc g),
                        have free_in_term x (term.unop unop.isFunc g), from free_in_prop.term.inv this,
                        have free_in_term x g, from free_in_term.unop.inv this,
                        have x = g, from free_in_term.var.inv this,
                        have x ∈ {g, gx}, from set.two_elems_mem.inv (or.inl this),
                        show x ∈ FV Q₂ ∪ {g, gx}, from set.mem_union_right (FV Q₂) this
                      ) (
                        assume : free_in_prop x (prop.forallc gx g forallp),
                        have x_neq_gx: x ≠ gx, from (free_in_prop.forallc.inv this).left,
                        have free_in_term x g ∨ free_in_prop x forallp,
                        from (free_in_prop.forallc.inv this).right,
                        or.elim this (
                          assume : free_in_term x g,
                          have x = g, from free_in_term.var.inv this,
                          have x ∈ {g, gx}, from set.two_elems_mem.inv (or.inl this),
                          show x ∈ FV Q₂ ∪ {g, gx}, from set.mem_union_right (FV Q₂) this
                        ) (
                          assume : free_in_prop x forallp,
                          or.elim (free_in_prop.and.inv this) (
                            assume : free_in_prop x (prop.implies R.to_prop (prop.pre g gx)),
                            or.elim (free_in_prop.implies.inv this) (
                              assume : free_in_prop x R.to_prop,
                              show x ∈ FV Q₂ ∪ {g, gx}, from R_fv this
                            ) (
                              assume : x ∈ FV (prop.pre g gx),
                              or.elim (free_in_prop.pre.inv this) (
                                assume : free_in_term x g,
                                have x = g, from free_in_term.var.inv this,
                                have x ∈ {g, gx}, from set.two_elems_mem.inv (or.inl this),
                                show x ∈ FV Q₂ ∪ {g, gx}, from set.mem_union_right (FV Q₂) this
                              ) (
                                assume : free_in_term x gx,
                                have x = gx, from free_in_term.var.inv this,
                                have x ∈ {g, gx}, from set.two_elems_mem.inv (or.inr this),
                                show x ∈ FV Q₂ ∪ {g, gx}, from set.mem_union_right (FV Q₂) this
                              )
                            )
                          ) (
                            assume : free_in_prop x (prop.implies (prop.post g gx) S.to_prop),
                            or.elim (free_in_prop.implies.inv this) (
                              assume : x ∈ FV (prop.post g gx),
                              or.elim (free_in_prop.post.inv this) (
                                assume : free_in_term x g,
                                have x = g, from free_in_term.var.inv this,
                                have x ∈ {g, gx}, from set.two_elems_mem.inv (or.inl this),
                                show x ∈ FV Q₂ ∪ {g, gx}, from set.mem_union_right (FV Q₂) this
                              ) (
                                assume : free_in_term x gx,
                                have x = gx, from free_in_term.var.inv this,
                                have x ∈ {g, gx}, from set.two_elems_mem.inv (or.inr this),
                                show x ∈ FV Q₂ ∪ {g, gx}, from set.mem_union_right (FV Q₂) this
                              )
                            ) (
                              assume : free_in_prop x S.to_prop,
                              show x ∈ FV Q₂ ∪ {g, gx}, from S_fv this
                            )
                          )
                        )
                      )
                    ) (
                      assume : free_in_prop x R,
                      show x ∈ FV Q₂ ∪ {g, gx}, from R_fv this
                    )
                  )
                )
              )
            ) (
              assume : free_in_prop x S.to_prop,
              show x ∈ FV Q₂ ∪ {g, gx}, from S_fv this
            )
          ),

          have FV (Q₃ (term.app g gx) ⋀ S.to_prop) ⊆ (σ₂[g↦vf][gx↦v]).dom, from h62.symm ▸ this,
          have closed (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)),
          from prop.closed_of_closed_subst this,
          have h63: closed (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).instantiated_n,
          from instantiated_n_closed_of_closed this,

          have FV (prop.post g gx) ⊆ FV Q₂ ∪ {g, gx}, from (
            assume x: var,
            assume : x ∈ FV (prop.post g gx),
            or.elim (free_in_prop.post.inv this) (
              assume : free_in_term x g,
              have x = g, from free_in_term.var.inv this,
              have x ∈ {g, gx}, from set.two_elems_mem.inv (or.inl this),
              show x ∈ FV Q₂ ∪ {g, gx}, from set.mem_union_right (FV Q₂) this
            ) (
              assume : free_in_term x gx,
              have x = gx, from free_in_term.var.inv this,
              have x ∈ {g, gx}, from set.two_elems_mem.inv (or.inr this),
              show x ∈ FV Q₂ ∪ {g, gx}, from set.mem_union_right (FV Q₂) this
            )
          ),
          have FV (prop.post g gx) ⊆ (σ₂[g↦vf][gx↦v]).dom, from h62.symm ▸ this,
          have closed (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)), from prop.closed_of_closed_subst this,
          have h64: closed (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)).instantiated_p,
          from instantiated_p_closed_of_closed this,

          have h7: ⊨ vc.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)).instantiated_p
                                (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).instantiated_n,
          from valid.implies.mp h64 h63 (
            assume h8: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)).instantiated_p,
            have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)
               = prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from prop.subst_env.post,
            have h81: ⊨ (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx))
                          .instantiated_p,
            from this ▸ h8,

            have calls_p (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g)
                                    (term.subst_env (σ₂[g↦vf][gx↦v]) gx)) = ∅,
            from set.eq_empty_of_forall_not_mem (
              assume c: calltrigger,
              assume : c ∈ calls_p (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g)
                                   (term.subst_env (σ₂[g↦vf][gx↦v]) gx)),
              show «false», from prop.has_call_p.post.inv this
            ),
            have (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g)
                            (term.subst_env (σ₂[g↦vf][gx↦v]) gx)).instantiated_p
              = (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g)
                           (term.subst_env (σ₂[g↦vf][gx↦v]) gx)).erased_p,
            from instantiated_p_eq_erased_p_without_calls this,

            have h9: ⊨ (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g)
                                  (term.subst_env (σ₂[g↦vf][gx↦v]) gx)).erased_p,
            from this ▸ h81,

            have (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx)).erased_n
                = vc.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            by unfold prop.erased_n,
            have h10: ⊨ vc.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from this ▸ h9,
            have term.subst_env (σ₂[g↦vf][gx↦v]) g = term.subst gx v (term.subst_env (σ₂[g↦vf]) g),
            by unfold term.subst_env,
            have ⊨ vc.post (term.subst gx v (term.subst_env (σ₂[g↦vf]) g)) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from this ▸ h10,
            have h11: ⊨ vc.post (term.subst gx v vf) (term.subst_env (σ₂[g↦vf][gx↦v]) gx), from g_subst ▸ this,
            have term.subst gx v (term.value vf) = vf, by unfold term.subst,
            have h12: ⊨ vc.post vf (term.subst_env (σ₂[g↦vf][gx↦v]) gx), from this ▸ h11,
            have term.subst_env (σ₂[g↦vf][gx↦v]) gx = term.subst gx v (term.subst_env (σ₂[g↦vf]) gx),
            by unfold term.subst_env,
            have h13: ⊨ vc.post vf (term.subst gx v (term.subst_env (σ₂[g↦vf]) gx)), from this ▸ h12,
            have ¬(gx = g ∨ gx ∈ σ₂), from not_or_distrib.mpr ⟨g_neq_gx.symm, gx_not_free_in_σ₂⟩,
            have gx ∉ (σ₂[g↦vf]), from (mt env.contains.inv) this,
            have (σ₂[g↦vf]) gx = none, from env.contains_apply_equiv.left.mpr this,
            have term.subst_env (σ₂[g↦vf]) gx = gx, from term.subst_env.var.left.mp this,
            have h14: ⊨ vc.post vf (term.subst gx v gx), from this ▸ h13,
            have term.subst gx v gx = v, from term.subst.var.same,
            have ⊨ vc.post vf v, from this ▸ h14,
            have (σ₂[g↦vf][gx↦v] ⊨ (Q₃ (term.app g gx)).instantiated_n ⋀ S.to_prop.instantiated_n),
            from valid.post.mpr σ₂_verified func_verified this,
            have h15: (σ₂[g↦vf][gx↦v] ⊨ (Q₃ (term.app g gx) ⋀ S.to_prop).instantiated_n),
            from valid_env.instantiated_n_and this,
            have vc.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop).instantiated_n
              = (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).instantiated_n,
            from instantiated_n_distrib_subst_env,
            show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).instantiated_n,
            from this ▸ h15
          ),
          have h8: ⊨ (prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx))
                                   (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated_n,
          from valid.instantiated_n_implies h7,
          have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop))
             = prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx))
                            (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)),
          from prop.subst_env.implies,
          show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                      (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated_n,
          from this.symm ▸ h8
        ),

        have ⊨ ((prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))).instantiated_n ⋀
                (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                                (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated_n),
        from valid.and.mp ⟨h5, h6⟩,
        have h7: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx)) ⋀
                    prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                                   (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated_n,
        from valid.instantiated_n_and this,
        have prop.subst_env (σ₂[g↦vf][gx↦v]) forallp
           = (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx)) ⋀
             prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop))),
        from prop.subst_env.and,
        have h8: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) forallp).instantiated_n, from this.symm ▸ h7,
        have prop.subst_env (σ₂[g↦vf][gx↦v]) forallp = prop.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp),
        by unfold prop.subst_env,
        have h9: ⊨ (prop.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp)).instantiated_n, from this ▸ h8,
        have vc.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp).instantiated_n
           = (prop.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp)).instantiated_n, from instantiated_n_distrib_subst,
        show ⊨ vc.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp).instantiated_n, from this.symm ▸ h9
      ),

      have h5: ⊨ prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)), from (
        have h6: ⊨ vc.univ gx (prop.subst_env (σ₂[g↦vf]) forallp).instantiated_n, from valid.univ.mp h4,
        have prop.instantiated_n (prop.forallc gx (term.subst_env (σ₂[g↦vf]) g) (prop.subst_env (σ₂[g↦vf]) forallp))
           = vc.univ gx (prop.subst_env (σ₂[g↦vf]) forallp).instantiated_n, from instantiated_n.forallc,
        have h7: ⊨ prop.instantiated_n (prop.forallc gx (term.subst_env (σ₂[g↦vf]) g) (prop.subst_env (σ₂[g↦vf]) forallp)), from this.symm ▸ h6,
        have ¬(gx = g ∨ gx ∈ σ₂), from not_or_distrib.mpr ⟨g_neq_gx.symm, gx_not_free_in_σ₂⟩,
        have gx ∉ (σ₂[g↦vf]), from (mt env.contains.inv) this,
        have (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)
            = prop.forallc gx (term.subst_env (σ₂[g↦vf]) g) (prop.subst_env (σ₂[g↦vf]) forallp)),
        from prop.subst_env.forallc_not_in this,
        show ⊨ prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)), from this.symm ▸ h7
      ),

      have ⊨ (prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)) ⋀
                  prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp))),
      from valid.and.mp ⟨h2, h5⟩,
      have h7: ⊨ prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g) ⋀
                                    prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)),
      from valid.instantiated_n_and this,
      have prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp)
         = (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g) ⋀ prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)),
      from prop.subst_env.and,
      have h8: ⊨ prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp)),
      from this.symm ▸ h7,
      have prop.func g gx R.to_prop (Q₃ (term.app g gx) ⋀ S.to_prop)
         = (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp),
      by unfold prop.func,
      have ⊨ prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
      from this.symm ▸ h8,
      have h9: ⊨ prop.instantiated_n pfunc, from this,

      have h10: (∀x, x ∉ FV pfunc), from (
        have ⊢ (σ₂[g↦vf]) : Q₂
          ⋀ (g ≡ (vf))
          ⋀ prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S)),
        from env.vcgen.func g_not_free_in_σ₂ g_not_free_in_σ₂ gx_not_free_in_σ₂ g_neq_gx
             σ₂_verified σ₂_verified gx_free_in_R R_fv S_fv func_verified S_valid,
        prop_func_closed this
      ),

      have h11: (∀x, x ∉ FV pfunc.instantiated_n), from (
        assume x: var,
        assume : x ∈ FV pfunc.instantiated_n,
        have x ∈ FV pfunc, from free_of_instantiated_n_free this,
        show «false», from (h10 x) this
      ),

      have vc.subst_env (σ₁[f↦vf]) pfunc.instantiated_n = pfunc.instantiated_n,
      from unchanged_of_subst_env_nonfree_vc h11 (σ₁[f↦vf]),
      have (σ₁[f↦vf]) ⊨ pfunc.instantiated_n, from this.symm ▸ h9,

      have (σ₁[f↦vf]) ⊨ ((prop.term (f ≡ vf)).instantiated_n ⋀ prop.instantiated_n pfunc), from valid_env.and h1.right this,
      have (σ₁[f↦vf]) ⊨ ((prop.term (f ≡ vf)) ⋀ pfunc).instantiated_n, from valid_env.instantiated_n_and this,
      have (σ₁[f↦vf]) ⊨ Q₁.instantiated_n ⋀ ((prop.term (f ≡ vf)) ⋀ pfunc).instantiated_n, from valid_env.and h1.left this,
      show (σ₁[f↦vf]) ⊨ (Q₁ ⋀ (f ≡ vf) ⋀ pfunc).instantiated_n,
      from valid_env.instantiated_n_and this
    )}
  end

lemma env_translation_valid {R: spec} {H: history} {P: prop} {σ: env}:
  (⊢ σ: P) → (σ ⊨ R.to_prop.instantiated_n) → σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_n :=
  assume env_verified: (⊢ σ : P),
  assume R_valid: (σ ⊨ R.to_prop.instantiated_n),
  have h1: σ ⊨ prop.instantiated_n ↑H, from history_valid σ,
  have h2: σ ⊨ P.instantiated_n, from env_translation_instantiated_n_valid env_verified,
  have σ ⊨ (prop.instantiated_n ↑H ⋀ P.instantiated_n), from valid_env.and h1 h2,
  have σ ⊨ (↑H ⋀ P).instantiated_n, from valid_env.instantiated_n_and this,
  have σ ⊨ R.to_prop.instantiated_n ⋀ (↑H ⋀ P).instantiated_n, from valid_env.and R_valid this,
  show σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_n, from valid_env.instantiated_n_and this

lemma consequent_of_H_P {R: spec} {H: history} {σ: env} {P Q: prop}:
      (⊢ σ: P) → closed_subst σ R.to_prop → (σ ⊨ R.to_prop.instantiated_n) →
     closed_subst σ Q → ⟪prop.implies (R ⋀ ↑H ⋀ P) Q⟫ → σ ⊨ Q.instantiated_p :=
  assume env_verified: (⊢ σ : P),
  assume R_closed: closed_subst σ R.to_prop,
  assume R_valid: (σ ⊨ R.to_prop.instantiated_n),
  assume Q_closed: closed_subst σ Q,
  assume : ⟪prop.implies (R ⋀ ↑H ⋀ P) Q⟫,
  have impl: σ ⊨ (prop.implies (↑R ⋀ ↑H ⋀ P) Q).instantiated_n, from this σ,
  have closed (calls_to_prop H), from call_history_closed H,
  have h1: closed_subst σ (calls_to_prop H), from prop.closed_any_subst_of_closed this,
  have closed_subst σ P, from env_translation_closed_subst env_verified,
  have closed_subst σ (↑H ⋀ P), from prop.closed_subst.and h1 this,
  have closed_subst σ (↑R ⋀ ↑H ⋀ P), from prop.closed_subst.and R_closed this,
  have closed_subst σ (prop.implies (↑R ⋀ ↑H ⋀ P) Q), from prop.closed_subst.implies this Q_closed,
  have closed_subst σ (prop.implies (↑R ⋀ ↑H ⋀ P) Q).instantiated_p, from instantiated_p_closed_subst_of_closed this,
  have σ ⊨ (prop.implies (↑R ⋀ ↑H ⋀ P) Q).instantiated_p, from valid_env.instantiated_p_of_instantiated_n this impl,
  have σ ⊨ ((↑R ⋀ ↑H ⋀ P).not ⋁ Q).instantiated_p, from this,
  have h2: σ ⊨ ((↑R ⋀ ↑H ⋀ P).not.instantiated_p ⋁ Q.instantiated_p), from valid_env.instantiated_p_or_elim this,
  have (↑R ⋀ ↑H ⋀ P).not.instantiated_p = (↑R ⋀ ↑H ⋀ P).instantiated_n.not, from not_dist_instantiated_p,
  have σ ⊨ ((↑R ⋀ ↑H ⋀ P).instantiated_n.not ⋁ Q.instantiated_p), from this ▸ h2,
  have h3: σ ⊨ vc.implies (↑R ⋀ ↑H ⋀ P).instantiated_n Q.instantiated_p, from this,
  have σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_n, from env_translation_valid env_verified R_valid,
  show σ ⊨ Q.instantiated_p, from valid_env.mp h3 this

lemma env_translation_call_valid {R: spec} {H: history} {P: prop} {σ: env} {f x: var}:
  (⊢ σ: P) → (σ ⊨ R.to_prop.instantiated_n) → σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n :=
  assume env_verified: (⊢ σ : P),
  assume R_valid: (σ ⊨ R.to_prop.instantiated_n),
  have h1: σ ⊨ prop.instantiated_n ↑H, from history_valid σ,
  have h2: σ ⊨ P.instantiated_n, from env_translation_instantiated_n_valid env_verified,
  have σ ⊨ (prop.instantiated_n ↑H ⋀ P.instantiated_n), from valid_env.and h1 h2,
  have σ ⊨ (↑H ⋀ P).instantiated_n, from valid_env.instantiated_n_and this,
  have σ ⊨ R.to_prop.instantiated_n ⋀ (↑H ⋀ P).instantiated_n, from valid_env.and R_valid this,
  have h3: σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_n, from valid_env.instantiated_n_and this,
  have h4: ⊨ value.true, from valid.tru,
  have term.subst_env σ value.true = value.true, from term.subst_env.value,
  have h5: ⊨ term.subst_env σ value.true, from this.symm ▸ h4,
  have vc.subst_env σ value.true = vc.term (term.subst_env σ value.true), from vc.subst_env.term,
  have h6: σ ⊨ value.true, from this.symm ▸ h5,
  have (prop.call f x).erased_n = vc.term value.true, by unfold prop.erased_n,
  have h7: σ ⊨ (prop.call f x).erased_n, from this.symm ▸ h6,

  have quantifiers_n (prop.call f x) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n (prop.call f x),
    show «false», from prop.has_quantifier_n.call.inv this
  ),
  have (prop.call f x).instantiated_n = (prop.call f x).erased_n,
  from instantiated_n_eq_erased_n_without_quantifiers this,
  have σ ⊨ (prop.call f x).instantiated_n, from this.symm ▸ h7,

  have σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_n ⋀ (prop.call f x).instantiated_n, from valid_env.and h3 this,
  show σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n, from valid_env.instantiated_n_and this

lemma consequent_of_H_P_call {R: spec} {H: history} {σ: env} {P Q: prop} {f x: var}:
  (⊢ σ: P) → closed_subst σ R.to_prop → (σ ⊨ R.to_prop.instantiated_n) →
  ⟪prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q⟫ → f ∈ σ → x ∈ σ → closed_subst σ Q → σ ⊨ Q.instantiated_p :=
  assume env_verified: (⊢ σ : P),
  assume R_closed: closed_subst σ R.to_prop,
  assume R_valid: (σ ⊨ R.to_prop.instantiated_n),
  assume impl_vc: ⟪prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q⟫,
  assume f_in_σ: f ∈ σ,
  assume x_in_σ: x ∈ σ,
  assume Q_closed: closed_subst σ Q,
  have h1: σ ⊨ (prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q).instantiated_n, from impl_vc σ,

  have closed (calls_to_prop H), from call_history_closed H,
  have h2: closed_subst σ (calls_to_prop H), from prop.closed_any_subst_of_closed this,
  have closed_subst σ P, from env_translation_closed_subst env_verified,
  have closed_subst σ (↑H ⋀ P), from prop.closed_subst.and h2 this,
  have h10: closed_subst σ (↑R ⋀ ↑H ⋀ P), from prop.closed_subst.and R_closed this,
  have closed_subst σ (prop.call f x), from (
    assume z: var,
    assume : z ∈ FV (prop.call f x),
    or.elim (free_in_prop.call.inv this) (
      assume : free_in_term z f,
      have z = f, from free_in_term.var.inv this,
      show z ∈ σ, from this.symm ▸ f_in_σ
    ) (
      assume : free_in_term z x,
      have z = x, from free_in_term.var.inv this,
      show z ∈ σ, from this.symm ▸ x_in_σ
    )
  ),
  have closed_subst σ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x), from prop.closed_subst.and h10 this,
  have closed_subst σ (prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q), from prop.closed_subst.implies this Q_closed,
  have closed_subst σ (prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q).instantiated_p,
  from instantiated_p_closed_subst_of_closed this,
  have σ ⊨ (prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q).instantiated_p,
  from valid_env.instantiated_p_of_instantiated_n this h1,
  have σ ⊨ (((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).not ⋁ Q).instantiated_p, from this,
  have h2: σ ⊨ (((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).not.instantiated_p ⋁ Q.instantiated_p), from valid_env.instantiated_p_or_elim this,
  have ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).not.instantiated_p = ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n.not,
  from not_dist_instantiated_p,
  have σ ⊨ (((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n.not ⋁ Q.instantiated_p), from this ▸ h2,
  have h3: σ ⊨ vc.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n Q.instantiated_p, from this,
  have σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n, from env_translation_call_valid env_verified R_valid,
  show σ ⊨ Q.instantiated_p, from valid_env.mp h3 this

lemma dominates_p_equiv_subst {σ₁ σ₂: env} {P: prop}:
  (∀y, y ∈ σ₁ → (σ₁ y = σ₂ y)) → dominates_p σ₂ (prop.subst_env σ₁ P) P :=
  begin
    assume env_equiv,
    
    induction σ₁ with σ' x v ih,

    show dominates_p σ₂ (prop.subst_env env.empty P) P, by begin
      unfold prop.subst_env,
      from dominates_p.self
    end,

    show dominates_p σ₂ (prop.subst_env (σ'[x↦v]) P) P, by begin
      unfold prop.subst_env,
      have h2: dominates_p σ₂ (prop.subst x v (prop.subst_env σ' P)) (prop.subst_env σ' P), by begin
        by_cases (x ∈ σ') with h,

        have h3: x ∉ FV (prop.subst_env σ' P), from prop.not_free_of_subst_env h,
        have h4: (prop.subst x v (prop.subst_env σ' P) = prop.subst_env σ' P),
        from unchanged_of_subst_nonfree_prop h3,
        have h5: dominates_p σ₂ (prop.subst_env σ' P) (prop.subst_env σ' P), from dominates_p.self,
        show dominates_p σ₂ (prop.subst x v (prop.subst_env σ' P)) (prop.subst_env σ' P), from h4.symm ▸ h5,

        have h2, from env_equiv x env.contains.same,
        have h3: ((σ'[x↦v]) x = v), from env.apply_of_contains h,
        have h4: (σ₂ x = v), from eq.trans h2.symm h3,
        show dominates_p σ₂ (prop.subst x v (prop.subst_env σ' P)) (prop.subst_env σ' P),
        from dominates_p.subst h4
      end,
      have h3: (∀ (y : var), y ∈ σ' → (σ' y = σ₂ y)), by begin
        assume y,
        assume h3,
        have h4: y ∈ (σ'[x↦v]), from env.contains.rest h3,
        have h5, from env_equiv y h4,
        have h6: (∃ (v : value), env.apply σ' y = some v), from env.contains_apply_equiv.right.mpr h3,
        have h7, from option.is_some_iff_exists.mpr h6,
        have h8, from option.some_iff_not_none.mp h7,
        have h9: (x ≠ y ∨ ¬ (option.is_none (env.apply σ' y))), from or.inr h8,
        have h10: ¬ (x = y ∧ (option.is_none (env.apply σ' y))), from not_and_distrib.mpr h9,
        have h11: (env.apply (σ'[x↦v]) y = (σ' y)), by { unfold env.apply, simp[h10], refl },
        from eq.trans h11.symm h5
      end,
      have h4, from ih h3,
      from dominates_p.trans h2 h4
    end,
  end

lemma dominates_n_equiv_subst {σ₁ σ₂: env} {P: prop}:
  (∀y, y ∈ σ₁ → (σ₁ y = σ₂ y)) → dominates_n σ₂ (prop.subst_env σ₁ P) P :=
  begin
    assume env_equiv,
    
    induction σ₁ with σ' x v ih,

    show dominates_n σ₂ (prop.subst_env env.empty P) P, by begin
      unfold prop.subst_env,
      from dominates_n.self
    end,

    show dominates_n σ₂ (prop.subst_env (σ'[x↦v]) P) P, by begin
      unfold prop.subst_env,
      have h2: dominates_n σ₂ (prop.subst x v (prop.subst_env σ' P)) (prop.subst_env σ' P), by begin
        by_cases (x ∈ σ') with h,

        have h3: x ∉ FV (prop.subst_env σ' P), from prop.not_free_of_subst_env h,
        have h4: (prop.subst x v (prop.subst_env σ' P) = prop.subst_env σ' P),
        from unchanged_of_subst_nonfree_prop h3,
        have h5: dominates_n σ₂ (prop.subst_env σ' P) (prop.subst_env σ' P), from dominates_n.self,
        show dominates_n σ₂ (prop.subst x v (prop.subst_env σ' P)) (prop.subst_env σ' P), from h4.symm ▸ h5,

        have h2, from env_equiv x env.contains.same,
        have h3: ((σ'[x↦v]) x = v), from env.apply_of_contains h,
        have h4: (σ₂ x = v), from eq.trans h2.symm h3,
        show dominates_n σ₂ (prop.subst x v (prop.subst_env σ' P)) (prop.subst_env σ' P),
        from dominates_n.subst h4
      end,
      have h3: (∀ (y : var), y ∈ σ' → (σ' y = σ₂ y)), by begin
        assume y,
        assume h3,
        have h4: y ∈ (σ'[x↦v]), from env.contains.rest h3,
        have h5, from env_equiv y h4,
        have h6: (∃ (v : value), env.apply σ' y = some v), from env.contains_apply_equiv.right.mpr h3,
        have h7, from option.is_some_iff_exists.mpr h6,
        have h8, from option.some_iff_not_none.mp h7,
        have h9: (x ≠ y ∨ ¬ (option.is_none (env.apply σ' y))), from or.inr h8,
        have h10: ¬ (x = y ∧ (option.is_none (env.apply σ' y))), from not_and_distrib.mpr h9,
        have h11: (env.apply (σ'[x↦v]) y = (σ' y)), by { unfold env.apply, simp[h10], refl },
        from eq.trans h11.symm h5
      end,
      have h4, from ih h3,
      from dominates_n.trans h2 h4
    end,
  end

lemma valid_env.subst_non_free_of_valid_env {σ: env} {x: var} {v: value} {P: vc}:
      (σ ⊨ P) → x ∉ FV P → (σ[x↦v] ⊨ P) :=
  assume : σ ⊨ P,
  have h1: ⊨ vc.subst_env σ P, from this,
  assume : x ∉ FV P,
  have x ∉ FV (vc.subst_env σ P), from mt free_in_vc.subst_env this,
  have vc.subst x v (vc.subst_env σ P) = (vc.subst_env σ P),
  from unchanged_of_subst_nonfree_vc this,
  have h2: ⊨ vc.subst x v (vc.subst_env σ P), from this.symm ▸ h1,
  have vc.subst_env (σ[x↦v]) P =  vc.subst x v (vc.subst_env σ P),
  by unfold vc.subst_env,
  have ⊨ vc.subst_env (σ[x↦v]) P, from this.symm ▸ h2,
  show σ[x↦v] ⊨ P, from this

lemma dominates_n.quantifier {σ: env} {x: var} {t₁ t₂: term} {P Q: prop} : 
      (∀v: value, dominates_n (σ.without x[x↦v]) P Q) →
      dominates_n σ (prop.forallc x t₁ P) (prop.forallc x t₂ Q) :=
  assume h0: ∀v: value, dominates_n (σ.without x[x↦v]) P Q,
  
  have h_impl: ((σ ⊨ (prop.forallc x t₁ P).instantiated_n) → (σ ⊨ (prop.forallc x t₂ Q).instantiated_n)), from (
    assume : σ ⊨ (prop.forallc x t₁ P).instantiated_n,
    have ⊨ vc.subst_env σ (prop.forallc x t₁ P).instantiated_n, from this,
    have h1: ⊨ (prop.subst_env σ (prop.forallc x t₁ P)).instantiated_n,
    from @instantiated_n_distrib_subst_env (prop.forallc x t₁ P) σ ▸ this,
    have prop.subst_env σ (prop.forallc x t₁ P) = prop.forallc x (term.subst_env (σ.without x) t₁)
                                                                 (prop.subst_env (σ.without x) P),
    from prop.subst_env.forallc,
    have ⊨ (prop.forallc x (term.subst_env (σ.without x) t₁)
                           (prop.subst_env (σ.without x) P)).instantiated_n,
    from this ▸ h1,
    have ⊨ vc.univ x (prop.subst_env (σ.without x) P).instantiated_n,
    from @instantiated_n.forallc x (term.subst_env (σ.without x) t₁) (prop.subst_env (σ.without x) P) ▸ this,
    have h2: ∀v, ⊨ vc.subst x v (prop.subst_env (σ.without x) P).instantiated_n,
    from valid.univ.mpr this,

    have ∀v, ⊨ vc.subst x v (prop.subst_env (σ.without x) Q).instantiated_n, from (
      assume v: value,
      have ⊨ vc.subst x v (prop.subst_env (σ.without x) P).instantiated_n,
      from h2 v,
      have h3: ⊨ (prop.subst x v (prop.subst_env (σ.without x) P)).instantiated_n,
      from @instantiated_n_distrib_subst (prop.subst_env (σ.without x) P) x v ▸ this,
      have prop.subst x v (prop.subst_env (σ.without x) P) = prop.subst_env ((σ.without x)[x↦v]) P,
      by unfold prop.subst_env,
      have ⊨ (prop.subst_env ((σ.without x)[x↦v]) P).instantiated_n,
      from this ▸ h3,
      have ⊨ vc.subst_env ((σ.without x)[x↦v]) P.instantiated_n,
      from (@instantiated_n_distrib_subst_env P ((σ.without x)[x↦v])).symm ▸ this,
      have h4: ⊨ vc.subst_env ((σ.without x)[x↦v]) Q.instantiated_n,
      from dominates_n.elim (h0 v) this,
      have vc.subst_env ((σ.without x)[x↦v]) Q.instantiated_n
         = vc.subst x v (vc.subst_env (σ.without x) Q.instantiated_n),
      by unfold vc.subst_env,
      have ⊨ vc.subst x v (vc.subst_env (σ.without x) Q.instantiated_n),
      from this ▸ h4,
      show ⊨ vc.subst x v (prop.subst_env (σ.without x) Q).instantiated_n,
      from (@instantiated_n_distrib_subst_env Q (σ.without x)) ▸ this
    ),
    have ⊨ vc.univ x (prop.subst_env (σ.without x) Q).instantiated_n, from valid.univ.mp this,
    have h3: ⊨ (prop.forallc x (term.subst_env (σ.without x) t₂)
                           (prop.subst_env (σ.without x) Q)).instantiated_n,
    from (@instantiated_n.forallc x (term.subst_env (σ.without x) t₂) (prop.subst_env (σ.without x) Q)).symm ▸ this,
    have prop.subst_env σ (prop.forallc x t₂ Q) = prop.forallc x (term.subst_env (σ.without x) t₂)
                                                                 (prop.subst_env (σ.without x) Q),
    from prop.subst_env.forallc,
    have ⊨ (prop.subst_env σ (prop.forallc x t₂ Q)).instantiated_n, from this.symm ▸ h3,
    have ⊨ vc.subst_env σ (prop.forallc x t₂ Q).instantiated_n,
    from (@instantiated_n_distrib_subst_env (prop.forallc x t₂ Q) σ).symm ▸ this,
    show σ ⊨ (prop.forallc x t₂ Q).instantiated_n, from this
  ),
  have h_calls: (calls_n_subst σ (prop.forallc x t₂ Q) ⊆ calls_n_subst σ (prop.forallc x t₁ P)), from (
    assume c: calltrigger,
    assume : c ∈ calls_n_subst σ (prop.forallc x t₂ Q),
    have c ∈ (calltrigger.subst σ) '' calls_n (prop.forallc x t₂ Q), from this,
    @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_n (prop.forallc x t₂ Q))
        (λa, a ∈ calls_n_subst σ (prop.forallc x t₁ P)) c this (
      assume c': calltrigger,
      assume : c' ∈ calls_n (prop.forallc x t₂ Q),
      show calltrigger.subst σ c' ∈ calls_n_subst σ (prop.forallc x t₁ P), from absurd this prop.has_call_n.forallc.inv
    )
  ),
  have h_quantifiers: quantifiers_n (prop.forallc x t₂ Q) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n (prop.forallc x t₂ Q),
    show «false», from prop.has_quantifier_n.forallc.inv this
  ),
  show dominates_n σ (prop.forallc x t₁ P) (prop.forallc x t₂ Q),
  from dominates_n.no_quantifiers h_impl h_calls h_quantifiers

lemma dominates_p.true {σ: env} {P: prop}:
      dominates_p σ P value.true :=

  have h1: σ ⊨ value.true, from valid_env.true,
  have (prop.term value.true).erased_n = vc.term value.true, by unfold prop.erased_n,
  have h2: σ ⊨ (prop.term value.true).erased_n, from this ▸ h1,
  have calls_p (prop.term value.true) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_p (prop.term value.true),
    show «false», from prop.has_call_p.term.inv this
  ),
  have (prop.term value.true).instantiated_p = (prop.term value.true).erased_p,
  from instantiated_p_eq_erased_p_without_calls this,
  have h_impl: (σ ⊨ P.instantiated_p) → σ ⊨ (prop.term value.true).instantiated_p, from (λ_, this.symm ▸ h2),
  have h_calls: calls_p_subst σ value.true ⊆ calls_p_subst σ P, from (
    assume c: calltrigger,
    assume : c ∈ calls_p_subst σ value.true,
    show c ∈ calls_p_subst σ P, from absurd this prop.has_call_p_subst.term.inv
  ),
  have h_quantifiers: quantifiers_p value.true = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_p value.true,
    show «false», from prop.has_quantifier_p.term.inv this
  ),
  show dominates_p σ P value.true, from dominates_p.no_quantifiers h_impl h_calls h_quantifiers

lemma dominates_n.true {σ: env} {P: prop}:
      dominates_n σ P value.true :=

  have h1: σ ⊨ value.true, from valid_env.true,
  have (prop.term value.true).erased_n = vc.term value.true, by unfold prop.erased_n,
  have h2: σ ⊨ (prop.term value.true).erased_n, from this ▸ h1,
  have calls_n (prop.term value.true) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n (prop.term value.true),
    show «false», from prop.has_call_n.term.inv this
  ),
  have (prop.term value.true).instantiated_n = (prop.term value.true).erased_n,
  from instantiated_n_eq_erased_n_without_calls this,
  have h_impl: (σ ⊨ P.instantiated_n) → σ ⊨ (prop.term value.true).instantiated_n, from (λ_, this.symm ▸ h2),
  have h_calls: calls_n_subst σ value.true ⊆ calls_n_subst σ P, from (
    assume c: calltrigger,
    assume : c ∈ calls_n_subst σ value.true,
    show c ∈ calls_n_subst σ P, from absurd this prop.has_call_n_subst.term.inv
  ),
  have h_quantifiers: quantifiers_n value.true = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n value.true,
    show «false», from prop.has_quantifier_n.term.inv this
  ),
  show dominates_n σ P value.true, from dominates_n.no_quantifiers h_impl h_calls h_quantifiers

lemma dominates_p.and_intro_of_no_calls {P Q: prop} {σ: env}:
      (closed_subst σ P) → (σ ⊨ P.instantiated_n) → (calls_p P = ∅) → (calls_n P = ∅) →
      dominates_p σ Q (P ⋀ Q) :=
  assume h1: closed_subst σ P,
  assume h2: σ ⊨ P.instantiated_n,
  assume h3: calls_p P = ∅,
  assume h4: calls_n P = ∅,
  have h5: dominates_p σ Q (Q ⋀ Q), from dominates_p.and_dup,
  have h6: dominates_p σ (Q ⋀ Q) (value.true ⋀ Q), from dominates_p.same_right (λ_, dominates_p.true),
  have h7: dominates_p σ (value.true ⋀ Q) (P ⋀ Q),
  from dominates_p.same_right (λ_, dominates_p.no_calls h1 h2 h3 h4),
  show dominates_p σ Q (P ⋀ Q),
  from dominates_p.trans h5 (dominates_p.trans h6 h7)

lemma dominates_p.and_right_intro_of_no_calls {P Q: prop} {σ: env}:
      ((σ ⊨ P.instantiated_p) → (closed_subst σ Q ∧ (σ ⊨ Q.instantiated_n) ∧ (calls_p Q = ∅) ∧ (calls_n Q = ∅))) →
      dominates_p σ P (P ⋀ Q) :=
  assume h1: ((σ ⊨ P.instantiated_p) → (closed_subst σ Q ∧ (σ ⊨ Q.instantiated_n) ∧ (calls_p Q = ∅) ∧ (calls_n Q = ∅))),
  have h2: dominates_p σ P (P ⋀ P), from dominates_p.and_dup,
  have h3: dominates_p σ (P ⋀ P) (P ⋀ value.true), from dominates_p.same_left (λ_, dominates_p.true),
  have h4: dominates_p σ (P ⋀ value.true) (P ⋀ Q),
  from dominates_p.same_left (
    assume : σ ⊨ P.instantiated_p,
    have h5: closed_subst σ Q, from (h1 this).left,
    have h6: σ ⊨ Q.instantiated_n, from (h1 this).right.left,
    have h7: calls_p Q = ∅, from (h1 this).right.right.left,
    have h8: calls_n Q = ∅, from (h1 this).right.right.right,
    dominates_p.no_calls h5 h6 h7 h8
  ),
  show dominates_p σ P (P ⋀ Q),
  from dominates_p.trans h2 (dominates_p.trans h3 h4)

-/
