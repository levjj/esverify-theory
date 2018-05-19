-- lemmas about validity of logical propositions

import .definitions2 .freevars .substitution .evaluation .bindings

lemma valid.false.elim {P: vc}: ⊨ vc.implies value.false P :=
  have h1: ⊨ value.true, from valid.tru,
  have unop.apply unop.not value.false = value.true, by unfold unop.apply,
  have ⊨ value.true ≡ term.unop unop.not value.false, from valid.unop.mp this,
  have ⊨ term.unop unop.not value.false, from valid.eq.true.mpr this,
  have ⊨ vc.not value.false, from valid.not.term.mp this,
  have ⊨ vc.not value.false ⋁ P, from valid.or.left this,
  show ⊨ vc.implies value.false P, from this

lemma valid.implies.mp {P Q: vc}: ((⊨ P) → (⊨ Q)) → ⊨ vc.implies P Q :=
  assume h1: (⊨ P) → (⊨ Q),
  have ⊨ P ⋁ P.not, from valid.em,
  or.elim (valid.or.elim this) (
    assume : ⊨ P,
    have ⊨ Q, from h1 this,
    show ⊨ P.not ⋁ Q, from valid.or.right this
  ) (
    assume : ⊨ P.not,
    show ⊨ P.not ⋁ Q, from valid.or.left this
  )

lemma valid.implies.mpr {P Q: vc}: (⊨ vc.implies P Q) → (⊨ P) → (⊨ Q) :=
  assume h1: (⊨ P.not ⋁ Q),
  assume h2: (⊨ P),
  or.elim (valid.or.elim h1) (
    assume : ⊨ P.not,
    have ⊨ P ⋀ P.not, from valid.and.mp ⟨h2, this⟩,
    show ⊨ Q, from false.elim (valid.contradiction this)
  ) id

lemma valid.not.mp {P: vc}: (¬ ⊨ P) → ⊨ P.not :=
  assume h1: ¬ (⊨ P),
  have ⊨ P ⋁ P.not, from valid.em,
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
    have h3: ¬ ⊨ P.not, from valid.not.mpr h1,
    have h4: ¬ ¬ ⊨ P, from (
      assume : ¬ ⊨ P,
      have ⊨ P.not, from valid.not.mp this,
      show «false», from h3 this
    ),
    or.elim (valid.or.elim valid.em) id (
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
    show ⊨ P.not.not, from valid.not.mp h2
  )

lemma valid.mt {P Q: vc}: (⊨ vc.implies P Q) → (⊨ Q.not) → ⊨ P.not :=
  assume h1: ⊨ vc.implies P Q,
  assume : ⊨ Q.not,
  have h2: ¬ ⊨ Q, from valid.not.mpr this,
  have ¬ ⊨ P, from (
    assume : ⊨ P,
    have ⊨ Q, from valid.implies.mpr h1 this,
    show «false», from h2 this
  ),
  show ⊨ P.not, from valid.not.mp this

lemma valid.refl {v: value}: ⊨ (v ≡ v) :=
  have binop.apply binop.eq v v = value.true, from binop.eq_of_equal_values,
  have ⊨ (value.true ≡ (v ≡ v)), from valid.binop.mp this,
  show ⊨ (v ≡ v), from valid.eq.true.mpr this

lemma valid.implies.trans {P₁ P₂ P₃: vc}:
      (⊨ vc.implies P₁ P₂) → (⊨ vc.implies P₂ P₃) → ⊨ vc.implies P₁ P₃ :=
  assume h1: ⊨ vc.implies P₁ P₂,
  assume h2: ⊨ vc.implies P₂ P₃,
  show ⊨ vc.implies P₁ P₃, from valid.implies.mp (
    assume : ⊨ P₁,
    have ⊨ P₂, from valid.implies.mpr h1 this,
    show ⊨ P₃, from valid.implies.mpr h2 this
  )

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

lemma valid.eq.terms {v₁ v₂: value}: (⊨ v₁ ≡ v₂) → (v₁ = v₂) :=
  begin
    assume h1,
    have h2, from valid.eq.true.mp h1,
    have h3, from valid.binop.mpr h2,
    from binop.eq.inv h3
  end

lemma valid.not_false: ⊨ vc.not value.false :=
  begin
    apply valid.not.term.mp,
    apply valid.eq.true.mpr,
    apply valid.unop.mp,
    unfold unop.apply,
    congr
  end

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

lemma valid_env.or₁ {σ: env} {P Q: vc}: (σ ⊨ P) → σ ⊨ (P ⋁ Q) :=
  assume h1: ⊨ vc.subst_env σ P,
  have h: ⊨ vc.subst_env σ P ⋁ vc.subst_env σ Q, from valid.or.left h1,
  have vc.subst_env σ (P ⋁ Q) = (vc.subst_env σ P ⋁ vc.subst_env σ Q), from vc.subst_env.or,
  show σ ⊨ (P ⋁ Q), from this.symm ▸ h

lemma valid_env.or₂ {σ: env} {P Q: vc}: (σ ⊨ Q) → σ ⊨ (P ⋁ Q) :=
  assume h1: ⊨ vc.subst_env σ Q,
  have h: ⊨ vc.subst_env σ P ⋁ vc.subst_env σ Q, from valid.or.right h1,
  have vc.subst_env σ (P ⋁ Q) = (vc.subst_env σ P ⋁ vc.subst_env σ Q), from vc.subst_env.or,
  show σ ⊨ (P ⋁ Q), from this.symm ▸ h

lemma valid_env.or.elim {σ: env} {P Q: vc}: (σ ⊨ P ⋁ Q) → (σ ⊨ P) ∨ σ ⊨ Q :=
  assume p_or_q_valid: ⊨ vc.subst_env σ (P ⋁ Q),
  have vc.subst_env σ (P ⋁ Q) = (vc.subst_env σ P ⋁ vc.subst_env σ Q), from vc.subst_env.or,
  have ⊨ (vc.subst_env σ P ⋁ vc.subst_env σ Q), from this ▸ p_or_q_valid,
  show (σ ⊨ P) ∨ (σ ⊨ Q), from valid.or.elim this

lemma valid_env.not.mp {σ: env} {P: vc}: ¬ (σ ⊨ P) → (σ ⊨ P.not) :=
  assume h1: ¬ (σ ⊨ P),
  have h2: vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  have ¬ ⊨ (vc.subst_env σ P), from h2 ▸ h1,
  have ⊨ (vc.subst_env σ P).not, from valid.not.mp this,
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

lemma valid_env.mpr {σ: env} {P Q: vc}: ((σ ⊨ P) → (σ ⊨ Q)) → σ ⊨ vc.implies P Q :=
  assume : ((σ ⊨ P) → σ ⊨ Q),
  have ⊨ vc.implies (vc.subst_env σ P) (vc.subst_env σ Q), from valid.implies.mp this,
  have h1: ⊨ vc.or (vc.subst_env σ P).not (vc.subst_env σ Q), from this,
  have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  have h2: ⊨ vc.or (vc.subst_env σ P.not) (vc.subst_env σ Q), from this.symm ▸ h1,
  have vc.subst_env σ (P.not ⋁ Q) = (vc.subst_env σ P.not ⋁ vc.subst_env σ Q),
  from vc.subst_env.or,
  have ⊨ vc.subst_env σ (P.not ⋁ Q), from this.symm ▸ h2,
  show σ ⊨ vc.implies P Q, from this

lemma valid_env.nmt {σ: env} {P Q: vc}: (σ ⊨ vc.implies P.not Q.not) → (σ ⊨ vc.implies Q P) :=
  begin
    assume h1,
    apply valid_env.mpr,
    assume h2,
    unfold vc.implies at h1,
    cases valid_env.or.elim h1 with h3 h4,
    from valid_env.not_not.mp h3,
    have h5, from valid_env.not.mpr h4,
    contradiction
  end

lemma valid_env.implies.trans {σ: env} {P₁ P₂ P₃: vc}:
      (σ ⊨ vc.implies P₁ P₂) → (σ ⊨ vc.implies P₂ P₃) → σ ⊨ vc.implies P₁ P₃ :=
  assume h1: σ ⊨ vc.implies P₁ P₂,
  assume h2: σ ⊨ vc.implies P₂ P₃,
  show σ ⊨ vc.implies P₁ P₃, from valid_env.mpr (
    assume : σ ⊨ P₁,
    have σ ⊨ P₂, from valid_env.mp h1 this,
    show σ ⊨ P₃, from valid_env.mp h2 this
  )

lemma vc.implies.trans {σ: env} {P₁ P₂ P₃: vc}:
      (σ ⊨ vc.implies P₁ P₂) → (σ ⊨ vc.implies P₂ P₃) → σ ⊨ vc.implies P₁ P₃ := valid_env.implies.trans

lemma valid_env.univ.mp {σ: env} {x: var} {P: vc}: (∀v, σ ⊨ vc.subst x v P) → σ ⊨ vc.univ x P :=
  assume h1: ∀v, σ ⊨ vc.subst x v P,
  have h2: ⊨ vc.univ x (vc.subst_env (σ.without x) P), from valid.univ.mp (
    assume v: value,
    have h3: ⊨ vc.subst_env σ (vc.subst x v P), from h1 v,
    have vc.subst_env σ (vc.subst x v P) = vc.subst x v (vc.subst_env (σ.without x) P),
    from vc.subst_env.reorder,
    show ⊨ vc.subst x v (vc.subst_env (σ.without x) P), from this ▸ h3
  ),
  have vc.subst_env σ (vc.univ x P) = vc.univ x (vc.subst_env (σ.without x) P),
  from vc.subst_env.univ,
  have ⊨ vc.subst_env σ (vc.univ x P), from this.symm ▸ h2,
  show σ ⊨ vc.univ x P, from this

lemma env.contains_of_valid_env_term {σ: env} {x: var} {t: term}:
      x ∈ FV t → closed_subst σ t → (x ∈ σ) :=
  assume x_free_in_t: x ∈ FV t,
  assume t_closed: closed_subst σ t,
  show x ∈ σ, from t_closed x_free_in_t

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
  have x ∈ σ, by begin
    by_contradiction h6,
    have h7: x ∈ FV (x ≡ v), from free_in_term.binop₁ (free_in_term.var x),
    have h8, from free_in_vc.term h7,
    have h9, from vc.free_of_subst_env h8 h6,
    have h10, from valid.univ.free ⟨h9, h2⟩,
    have h11: (∀v': value, v ≠ v' → «false»), by begin
      assume v',
      assume h11,

      have h12, from valid.univ.mpr h10 v',
      have h13: (vc.substt x v' (vc.subst_env σ ↑(↑x ≡ ↑v))
              = vc.subst x v' (vc.subst_env σ ↑(↑x ≡ ↑v))),
      from vc.substt_value_eq_subst,
      rw[h13] at h12,
      have h14: (vc.subst_env σ (vc.subst x v' ↑(↑x ≡ ↑v))
              = vc.subst x v' (vc.subst_env σ ↑(↑x ≡ ↑v))),
      from vc.subst_env.order (or.inl h6),
      rw[h14.symm] at h12,
      have h15: σ ⊨ vc.subst x v' (vc.term (↑x ≡ ↑v)), from h12,
      unfold vc.subst at h15,
      unfold term.subst at h15,
      have h16: σ ⊨ ↑(term.subst x v' (term.var x) ≡ term.subst x v' (term.value v)),
      from h15,
      unfold term.subst at h16,
      simp at h16,
      have h17: closed (vc.term (↑v' ≡ ↑v)), by begin
        assume z,
        assume h18,
        have h19, from free_in_vc.term.inv h18,
        cases (free_in_term.binop.inv h19) with h20 h21,
        have h22: ¬ free_in_term z ↑v', from free_in_term.value.inv,
        contradiction,
        have h22: ¬ free_in_term z ↑v, from free_in_term.value.inv,
        contradiction
      end,
      have h18: (vc.subst_env σ (vc.term (↑v' ≡ ↑v)) = vc.term (↑v' ≡ ↑v)),
      from unchanged_of_subst_env_nonfree_vc h17 σ,
      have h19: ⊨ vc.subst_env σ (vc.term (↑v' ≡ ↑v)), from h16,
      rw[h18] at h19,
      have h20, from (valid.eq.terms h19).symm,
      contradiction
    end,
    
    by_cases (v = value.true) with h12,

    have h13: value.true ≠ value.false, by { assume h14, contradiction },
    from h11 value.false (h12.symm ▸ h13),

    have h13: value.true ≠ v, by { assume h14, have h15, from h14.symm, contradiction },
    from h11 value.true h13.symm,
  end,
  have ∃v', σ x = some v', from env.contains_apply_equiv.right.mpr this,
  let ⟨v', h6⟩ := this in
  have term.subst_env σ x = v', from (term.subst_env.var.right v').mp h6,
  have ⊨ (v' ≡ v), from this ▸ h5,
  have ⊨ value.true ≡ (v' ≡ v), from valid.eq.true.mp this,
  have binop.apply binop.eq v' v = some value.true, from valid.binop.mpr this,
  have v' = v, from binop.eq.inv this,
  show σ x = some v, from h6.symm ▸ (some.inj.inv this)

lemma valid.alpha_equiv {x y: var} {P: vc}: (⊨ P) → ⊨ vc.substt x y P :=
  begin
    assume h1,
    by_cases (free_in_vc x P) with h2,

    have h3, from valid.univ.free ⟨h2, h1⟩,
    from valid.univ.mpr h3 y,

    have h4: (vc.substt x y P = P),
    from unchanged_of_substt_nonfree_vc h2,
    rw[h4],
    from h1
  end

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
-/

lemma valid.to_vc_and {P Q: prop}: (⊨ P.to_vc) → (⊨ Q.to_vc) → ⊨ (P ⋀ Q).to_vc :=
  begin
    assume h1: ⊨ P.to_vc,
    assume h2: ⊨ Q.to_vc,
    change ⊨ prop.to_vc (prop.and P Q),
    unfold prop.to_vc,
    from valid.and.mp ⟨h1, h2⟩
  end

lemma valid_env.to_vc_and {P Q: prop} {σ: env}: (σ ⊨ P.to_vc) → (σ ⊨ Q.to_vc) → σ ⊨ (P ⋀ Q).to_vc :=
  begin
    assume h1: σ ⊨ P.to_vc,
    assume h2: σ ⊨ Q.to_vc,
    change σ ⊨ prop.to_vc (prop.and P Q),
    unfold prop.to_vc,
    from valid_env.and h1 h2
  end

lemma valid_env.to_vc_and.elim {P Q: prop} {σ: env}: (σ ⊨ (P ⋀ Q).to_vc) → ((σ ⊨ P.to_vc) ∧ (σ ⊨ Q.to_vc)) :=
  begin
    assume h1: σ ⊨ (P ⋀ Q).to_vc,
    have h2: σ ⊨ (prop.and P Q).to_vc, from h1,
    unfold prop.to_vc at h2,
    from valid_env.and.elim h2
  end

lemma val_of_free_in_env {P: prop} {σ: env} {x: var}: (⊩ σ : P) → x ∈ FV P → ∃v, σ x = some v :=
  assume env_verified: ⊩ σ: P,
  assume x_free_in_P: x ∈ FV P,
  have x ∈ σ, from contains_of_free env_verified x_free_in_P,
  show ∃v, σ x = some v, from env.contains_apply_equiv.right.mpr this

lemma val_of_free_in_pre_env {R: spec} {σ: env} {P: prop} {x: var}:
                              (⊩ σ : P) → FV R.to_prop ⊆ FV P → x ∈ FV (R.to_prop ⋀ P) → ∃v, σ x = some v :=
  assume σ_verified: ⊩ σ : P,
  assume fv_R: FV R.to_prop ⊆ FV P,
  assume x_free_in_R_P: x ∈ FV (R.to_prop ⋀ P),
  have free_in_prop x R.to_prop ∨ free_in_prop x P, from free_in_prop.and.inv x_free_in_R_P,
  have x ∈ FV P, from or.elim this.symm id (
    assume : free_in_prop x R.to_prop,
    show x ∈ FV P, from set.mem_of_mem_of_subset this fv_R
  ),
  show ∃v, σ x = some v, from val_of_free_in_env σ_verified this

lemma to_vc_implies {P Q: prop}: (prop.implies P Q).to_vc = vc.implies P.to_vc Q.to_vc :=
  begin
    unfold prop.implies,
    unfold vc.implies,
    unfold prop.to_vc,
    congr
  end

lemma valid.to_vc_implies {P Q: prop}: (⊨ (prop.implies P Q).to_vc) ↔ ⊨ vc.implies P.to_vc Q.to_vc :=
  begin
    have h1: ((prop.implies P Q).to_vc = vc.implies P.to_vc Q.to_vc), from to_vc_implies,
    rw[h1]
  end

lemma valid_env.to_vc_implies {P Q: prop} {σ: env}: (σ ⊨ (prop.implies P Q).to_vc) ↔ σ ⊨ vc.implies P.to_vc Q.to_vc :=
  begin
    have h1: ((prop.implies P Q).to_vc = vc.implies P.to_vc Q.to_vc), from to_vc_implies,
    rw[h1]
  end

lemma simple_equality_valid {σ: env} {x: var} {v: value}:
  x ∉ σ → (σ[x↦v]) ⊨ (prop.term (x ≡ v)).to_vc :=
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
  have prop.to_vc (prop.term (x ≡ v)) = vc.term (x ≡ v), by unfold prop.to_vc,
  have h8: vc.subst_env (σ[x↦v]) (prop.term (x ≡ v)).to_vc = vc.term (v ≡ v), from this.symm ▸ h7,
  have ⊨ vc.term (v ≡ v), from valid.refl,
  show (σ[x↦v]) ⊨ prop.to_vc (x ≡ v), from h8.symm ▸ this

lemma simple_equality_env_valid {P: prop} {σ: env} {x: var} {v: value}:
                                     (⊩ σ: P) → x ∉ σ → (σ ⊨ P.to_vc) → (σ[x↦v]) ⊨ (P ⋀ x ≡ v).to_vc :=
  assume σ_verified: ⊩ σ: P,
  assume x_not_free_in_σ: x ∉ σ,
  assume ih: σ ⊨ P.to_vc,
  have σ.apply x = none, from env.contains_apply_equiv.left.mpr x_not_free_in_σ,
  have h1: ⊨ vc.subst_env σ P.to_vc, from ih,
  have x_not_in_P: x ∉ FV (vc.subst_env σ P.to_vc), from (
    assume : x ∈ FV (vc.subst_env σ P.to_vc),
    have x ∈ FV P.to_vc, from free_in_vc.subst_env this,
    have x ∈ FV P, from set.mem_of_mem_of_subset this free_in_prop_of_free_in_to_vc,
    have ∃v, σ x = some v, from val_of_free_in_env σ_verified this,
    have x ∈ σ, from env.contains_apply_equiv.right.mp this,
    show «false», from x_not_free_in_σ this
  ),
  have vc.subst x v (vc.subst_env σ P.to_vc) = vc.subst_env σ P.to_vc,
  from unchanged_of_subst_nonfree_vc x_not_in_P,
  have h2: ⊨ vc.subst x v (vc.subst_env σ P.to_vc),
  from @eq.subst vc (λa, ⊨ a) (vc.subst_env σ P.to_vc)
          (vc.subst x v (vc.subst_env σ P.to_vc)) this.symm h1,
  have vc.subst x v (vc.subst_env σ P.to_vc)
      = vc.subst_env (σ[x↦v]) P.to_vc, by unfold vc.subst_env, 
  have h3: ⊨ vc.subst_env (σ[x↦v]) P.to_vc, from this ▸ h2,
  have h4: (σ[x↦v]) ⊨ (prop.term (x ≡ v)).to_vc,
  from simple_equality_valid x_not_free_in_σ,
  have h5: (σ[x↦v]) ⊨ (P.to_vc ⋀ (prop.term (x ≡ v)).to_vc),
  from valid_env.and h3 h4,
  have (P.to_vc ⋀ (prop.term (x ≡ v)).to_vc) = prop.to_vc (prop.and P (prop.term (x ≡ v))),
  by unfold prop.to_vc,
  have (σ[x↦v]) ⊨ prop.to_vc (prop.and P (prop.term (x ≡ v))), from this ▸ h5,
  show (σ[x↦v]) ⊨ (P ⋀ x ≡ v).to_vc, from this

lemma env_translation_valid {P: prop} {σ: env}: (⊩ σ: P) → σ ⊨ P.to_vc :=
  assume env_verified: (⊩ σ : P),
  begin
    induction env_verified,
    case env.dvcgen.empty {
      unfold vc.subst_env,
      change ⊨ prop.to_vc (prop.term value.true),
      unfold prop.to_vc,
      from valid.tru
    },
    case env.dvcgen.tru σ' x' Q x_not_free_in_σ' σ'_verified ih {
      from simple_equality_env_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.dvcgen.fls σ' x' Q x_not_free_in_σ' σ'_verified ih {
      from simple_equality_env_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.dvcgen.num n σ' x' Q x_not_free_in_σ' σ'_verified ih {
      from simple_equality_env_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.dvcgen.func σ₁ σ₂ f g gx R S e Q₁ Q₂ Q₃
      f_not_free_in_σ₁ g_not_free_in_σ₂ gx_not_free_in_σ₂ g_neq_gx σ₁_verified σ₂_verified gx_free_in_R R_fv S_fv func_verified
      S_valid ih₁ ih₂ { from (
      let vf := value.func g gx R S e σ₂ in
      have h1: ((σ₁[f↦vf]) ⊨ (Q₁ ⋀ f ≡ vf).to_vc),
      from simple_equality_env_valid σ₁_verified f_not_free_in_σ₁ ih₁,
      have h1a: (σ₁[f↦vf]) ⊨ Q₁.to_vc,
      from (valid_env.to_vc_and.elim h1).left,
      have h1b: (σ₁[f↦vf]) ⊨ (prop.term (f ≡ vf)).to_vc,
      from (valid_env.to_vc_and.elim h1).right,

      have g_subst: term.subst_env (σ₂[g↦vf]) g = vf, from (
        have h1: term.subst g vf g = vf, from term.subst.var.same,
        have σ₂ g = none, from env.contains_apply_equiv.left.mpr g_not_free_in_σ₂,
        have term.subst_env σ₂ g = g, from term.subst_env.var.left.mp this,
        have h2: term.subst g vf (term.subst_env σ₂ g) = vf, from this.symm ▸ h1,
        have term.subst_env (σ₂[g↦vf]) g = term.subst g vf (term.subst_env σ₂ g), by unfold term.subst_env,
        show term.subst_env (σ₂[g↦vf]) g = vf, from eq.trans this h2
      ),

      have h2: ⊨ prop.to_vc (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from (
        have unop.apply unop.isFunc vf = value.true, by unfold unop.apply,
        have ⊨ (value.true ≡ term.unop unop.isFunc vf), from valid.unop.mp this,
        have ⊨ term.unop unop.isFunc vf, from valid.eq.true.mpr this,
        have h3: ⊨ term.unop unop.isFunc (term.subst_env (σ₂[g↦vf]) g), from g_subst.symm ▸ this,
        have term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g) = term.unop unop.isFunc (term.subst_env (σ₂[g↦vf]) g),
        from term.subst_env.unop,
        have h4: ⊨ vc.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from this.symm ▸ h3,
        have prop.to_vc (prop.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)))
           = vc.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)),
        by unfold prop.to_vc,
        have h5: ⊨ prop.to_vc (prop.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g))), from this.symm ▸ h4,
        have prop.subst_env (σ₂[g↦vf]) (prop.term (term.unop unop.isFunc g))
           = prop.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from prop.subst_env.term,
        show ⊨ prop.to_vc (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from this.symm ▸ h5
      ),

      let forallp := prop.implies R.to_prop (prop.pre g gx)
                  ⋀ prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop) in
      let pfunc: prop := prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S)) in

      have h4: ∀v, ⊨ vc.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp).to_vc, from (
        assume v: value,

        have h5: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))).to_vc, from (

          have h51: (σ₂[g↦vf][gx↦v]).dom = σ₂.dom ∪ {g, gx}, from env.dom.two_elems,
          have σ₂.dom = FV Q₂, from free_iff_contains σ₂_verified,
          have h52: (σ₂[g↦vf][gx↦v]).dom = FV Q₂ ∪ {g, gx}, from this ▸ h51,
          have FV R.to_prop ⊆ (σ₂[g↦vf][gx↦v]).dom, from h52.symm ▸ R_fv,
          have closed (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop), from prop.closed_of_closed_subst this,
          have h53: closed (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).to_vc,
          from to_vc_closed_of_closed this,

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
          have h54: closed (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).to_vc,
          from to_vc_closed_of_closed this,

          have h6: ⊨ vc.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).to_vc
                                (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).to_vc,
          from valid.implies.mp (
            assume h8: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).to_vc,
            have vc.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop.to_vc
                = (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).to_vc,
            from subst_env_distrib_to_vc,
            have ⊨ vc.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop.to_vc, from this.symm ▸ h8,
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
            have prop.to_vc (prop.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx))
               = (vc.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx)),
            by unfold prop.to_vc,
            have h15: ⊨ (prop.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx)).to_vc,
            from this.symm ▸ h14,
            have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)
               = prop.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from prop.subst_env.pre,
            show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).to_vc, from this.symm ▸ h15
          ),
          have h8: ⊨ (prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop)
                                   (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx))).to_vc,
          from valid.to_vc_implies.mp h6,
          have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))
             = prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop)
                            (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)),
          from prop.subst_env.implies,
          show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))).to_vc,
          from this.symm ▸ h8
        ),

        have h6: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                     (Q₃ (term.app g gx) ⋀ S.to_prop))).to_vc, from (

          have h61: (σ₂[g↦vf][gx↦v]).dom = σ₂.dom ∪ {g, gx}, from env.dom.two_elems,
          have σ₂.dom = FV Q₂, from free_iff_contains σ₂_verified,
          have h62: (σ₂[g↦vf][gx↦v]).dom = FV Q₂ ∪ {g, gx}, from this ▸ h61,

          have FV (Q₃ (term.app g gx) ⋀ S.to_prop) ⊆ FV Q₂ ∪ {g, gx}, from (
            assume x: var,
            assume : x ∈ FV (Q₃ (term.app g gx) ⋀ S.to_prop),
            or.elim (free_in_prop.and.inv this) (
              assume : x ∈ FV (Q₃ (term.app g gx)),
              have x ∈ FV (term.app g gx) ∨ x ∈ FV (Q₂ ⋀ spec.func ↑g gx R S ⋀ R),
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
                      = (term.unop unop.isFunc g ⋀ prop.forallc gx forallp),
                    by unfold prop.func,
                    have free_in_prop x (term.unop unop.isFunc g ⋀ prop.forallc gx forallp),
                    from this ▸ h64,
                    or.elim (free_in_prop.and.inv this) (
                      assume : free_in_prop x (term.unop unop.isFunc g),
                      have free_in_term x (term.unop unop.isFunc g), from free_in_prop.term.inv this,
                      have free_in_term x g, from free_in_term.unop.inv this,
                      have x = g, from free_in_term.var.inv this,
                      have x ∈ {g, gx}, from set.two_elems_mem.inv (or.inl this),
                      show x ∈ FV Q₂ ∪ {g, gx}, from set.mem_union_right (FV Q₂) this
                    ) (
                      assume : free_in_prop x (prop.forallc gx forallp),
                      have x_neq_gx: x ≠ gx, from (free_in_prop.forallc.inv this).left,
                      have free_in_prop x forallp, from (free_in_prop.forallc.inv this).right,
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
                  ) (
                    assume : free_in_prop x R,
                    show x ∈ FV Q₂ ∪ {g, gx}, from R_fv this
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
          have h63: closed (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).to_vc,
          from to_vc_closed_of_closed this,

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
          have h64: closed (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)).to_vc,
          from to_vc_closed_of_closed this,

          have h7: ⊨ vc.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)).to_vc
                                (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).to_vc,
          from valid.implies.mp (
            assume h8: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)).to_vc,
            have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)
               = prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from prop.subst_env.post,
            have h9: ⊨ (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g)
                                  (term.subst_env (σ₂[g↦vf][gx↦v]) gx)).to_vc,
            from this ▸ h8,

            have (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx)).to_vc
                = vc.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            by unfold prop.to_vc,
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
            have (σ₂[g↦vf][gx↦v] ⊨ (Q₃ (term.app g gx)).to_vc ⋀ S.to_prop.to_vc),
            from valid.post.mpr σ₂_verified func_verified this,
            have h15: (σ₂[g↦vf][gx↦v] ⊨ (Q₃ (term.app g gx) ⋀ S.to_prop).to_vc),
            from valid_env.to_vc_and (valid_env.and.elim this).left (valid_env.and.elim this).right,
            have vc.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop).to_vc
              = (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).to_vc,
            from subst_env_distrib_to_vc,
            show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).to_vc,
            from this ▸ h15
          ),
          have h8: ⊨ (prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx))
                                   (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop))).to_vc,
          from valid.to_vc_implies.mp h7,
          have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop))
             = prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx))
                            (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)),
          from prop.subst_env.implies,
          show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                      (Q₃ (term.app g gx) ⋀ S.to_prop))).to_vc,
          from this.symm ▸ h8
        ),

        have h7: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx)) ⋀
                    prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                                   (Q₃ (term.app g gx) ⋀ S.to_prop))).to_vc,
        from valid.to_vc_and h5 h6,
        have prop.subst_env (σ₂[g↦vf][gx↦v]) forallp
           = (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx)) ⋀
             prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop))),
        from prop.subst_env.and,
        have h8: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) forallp).to_vc, from this.symm ▸ h7,
        have prop.subst_env (σ₂[g↦vf][gx↦v]) forallp = prop.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp),
        by unfold prop.subst_env,
        have h9: ⊨ (prop.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp)).to_vc, from this ▸ h8,
        have vc.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp).to_vc
           = (prop.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp)).to_vc,
        from subst_distrib_to_vc,
        show ⊨ vc.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp).to_vc, from this.symm ▸ h9
      ),

      have h5: ⊨ prop.to_vc (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx forallp)), from (
        have h6: ⊨ vc.univ gx (prop.subst_env (σ₂[g↦vf]) forallp).to_vc, from valid.univ.mp h4,
        have prop.to_vc (prop.forallc gx (prop.subst_env (σ₂[g↦vf]) forallp))
           = vc.univ gx (prop.subst_env (σ₂[g↦vf]) forallp).to_vc,
        by unfold prop.to_vc,
        have h7: ⊨ prop.to_vc (prop.forallc gx (prop.subst_env (σ₂[g↦vf]) forallp)), from this.symm ▸ h6,
        have ¬(gx = g ∨ gx ∈ σ₂), from not_or_distrib.mpr ⟨g_neq_gx.symm, gx_not_free_in_σ₂⟩,
        have gx ∉ (σ₂[g↦vf]), from (mt env.contains.inv) this,
        have (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx forallp)
            = prop.forallc gx (prop.subst_env (σ₂[g↦vf]) forallp)),
        from prop.subst_env.forallc_not_in this,
        show ⊨ prop.to_vc (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx forallp)), from this.symm ▸ h7
      ),

      have h7: ⊨ prop.to_vc (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g) ⋀
                             prop.subst_env (σ₂[g↦vf]) (prop.forallc gx forallp)),
      from valid.to_vc_and h2 h5,
      have prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g ⋀ prop.forallc gx forallp)
         = (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g) ⋀ prop.subst_env (σ₂[g↦vf]) (prop.forallc gx forallp)),
      from prop.subst_env.and,
      have h8: ⊨ prop.to_vc (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g ⋀ prop.forallc gx forallp)),
      from this.symm ▸ h7,
      have prop.func g gx R.to_prop (Q₃ (term.app g gx) ⋀ S.to_prop)
         = (term.unop unop.isFunc g ⋀ prop.forallc gx forallp),
      by unfold prop.func,
      have ⊨ prop.to_vc (prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
      from this.symm ▸ h8,
      have h9: ⊨ prop.to_vc pfunc, from this,

      have h10: (∀x, x ∉ FV pfunc), from (
        have ⊩ (σ₂[g↦vf]) : Q₂
          ⋀ (g ≡ (vf))
          ⋀ prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S)),
        from env.dvcgen.func g_not_free_in_σ₂ g_not_free_in_σ₂ gx_not_free_in_σ₂ g_neq_gx
             σ₂_verified σ₂_verified gx_free_in_R R_fv S_fv func_verified S_valid,
        prop_func_closed this
      ),

      have h11: (∀x, x ∉ FV pfunc.to_vc), from (
        assume x: var,
        assume : x ∈ FV pfunc.to_vc,
        have x ∈ FV pfunc, from set.mem_of_mem_of_subset this free_in_prop_of_free_in_to_vc,
        show «false», from (h10 x) this
      ),

      have vc.subst_env (σ₁[f↦vf]) pfunc.to_vc = pfunc.to_vc,
      from unchanged_of_subst_env_nonfree_vc h11 (σ₁[f↦vf]),
      have (σ₁[f↦vf]) ⊨ pfunc.to_vc, from this.symm ▸ h9,

      have (σ₁[f↦vf]) ⊨ ((prop.term (f ≡ vf)) ⋀ pfunc).to_vc,
      from valid_env.to_vc_and h1b this,
      show (σ₁[f↦vf]) ⊨ (Q₁ ⋀ (f ≡ vf) ⋀ pfunc).to_vc,
      from valid_env.to_vc_and h1a this
    )}
  end

lemma consequent_of_pre_P {R: spec} {σ: env} {P Q: prop}:
      (⊩ σ: P) → closed_subst σ R.to_prop → (σ ⊨ R.to_prop.to_vc) →
     closed_subst σ Q → ⦃ prop.implies (R ⋀ P) Q ⦄ → σ ⊨ Q.to_vc :=
  assume env_verified: (⊩ σ : P),
  assume R_closed: closed_subst σ R.to_prop,
  assume R_valid: (σ ⊨ R.to_prop.to_vc),
  assume Q_closed: closed_subst σ Q,
  assume vc_valid: ⦃ prop.implies (R ⋀ P) Q ⦄,

  have closed_subst σ P, from env_translation_closed_subst env_verified,
  have closed_subst σ (↑R ⋀ P), from prop.closed_subst.and R_closed this,
  have closed_subst σ (prop.implies (↑R ⋀ P) Q), from prop.closed_subst.implies this Q_closed,
  have impl: σ ⊨ (prop.implies (↑R ⋀ P) Q).to_vc, from vc_valid σ this,
  have (prop.implies (↑R ⋀ P) Q).to_vc = vc.implies (↑R ⋀ P).to_vc Q.to_vc,
  by { unfold prop.implies, unfold vc.implies, unfold prop.to_vc, congr },
  have impl2: σ ⊨ vc.implies (↑R ⋀ P).to_vc Q.to_vc, from this ▸ impl,
  have σ ⊨ P.to_vc, from env_translation_valid env_verified,
  have σ ⊨ (↑R ⋀ P).to_vc, from valid_env.to_vc_and R_valid this,
  show σ ⊨ Q.to_vc, from valid_env.mp impl2 this

/-

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

-/

lemma consequent_of_pre_P_call {R: spec} {σ: env} {P Q: prop} {x: var}:
      (⊩ σ: P) → closed_subst σ R.to_prop → (σ ⊨ R.to_prop.to_vc) → x ∈ σ →
     closed_subst σ Q → ⦃ prop.implies ((R ⋀ P) ⋀ prop.call x) Q ⦄ → σ ⊨ Q.to_vc :=
  assume env_verified: (⊩ σ : P),
  assume R_closed: closed_subst σ R.to_prop,
  assume R_valid: (σ ⊨ R.to_prop.to_vc),
  assume env_has_x: x ∈ σ,
  assume Q_closed: closed_subst σ Q,
  assume vc_valid: ⦃ prop.implies ((R ⋀ P) ⋀ prop.call x) Q ⦄,

  have closed_subst σ P, from env_translation_closed_subst env_verified,
  have h1: closed_subst σ (↑R ⋀ P), from prop.closed_subst.and R_closed this,
  have closed_subst σ (prop.call x), by begin
    assume y: var,
    assume h1,
    have h2, from free_in_prop.call.inv h1,
    have h3: (y = x), from free_in_term.var.inv h2,
    rw[←h3] at env_has_x,
    from env_has_x
  end,
  have closed_subst σ ((↑R ⋀ P) ⋀ prop.call x), from prop.closed_subst.and h1 this,
  have closed_subst σ (prop.implies ((↑R ⋀ P) ⋀ prop.call x) Q),
  from prop.closed_subst.implies this Q_closed,
  have impl: σ ⊨ (prop.implies ((↑R ⋀ P) ⋀ prop.call x) Q).to_vc, from vc_valid σ this,
  have (prop.implies (↑R ⋀ P) Q).to_vc = vc.implies (↑R ⋀ P).to_vc Q.to_vc,
  by { unfold prop.implies, unfold vc.implies, unfold prop.to_vc, congr },
  have impl2: σ ⊨ vc.implies ((↑R ⋀ P) ⋀ prop.call x).to_vc Q.to_vc, from this ▸ impl,
  have σ ⊨ P.to_vc, from env_translation_valid env_verified,
  have h2: σ ⊨ (↑R ⋀ P).to_vc, from valid_env.to_vc_and R_valid this,
  have h3: σ ⊨ value.true, from valid_env.true,
  have prop.to_vc (prop.call x) = value.true, by { unfold prop.to_vc, congr },
  have σ ⊨ (prop.call x).to_vc, from this.symm ▸ h3,
  have σ ⊨ ((↑R ⋀ P) ⋀ prop.call x).to_vc, from valid_env.to_vc_and h2 this,
  show σ ⊨ Q.to_vc, from valid_env.mp impl2 this

/-

lemma dominates_p_equiv_subst {σ₁ σ₂: env} {P: prop}:
  (∀y, y ∈ σ₁ → (σ₁ y = σ₂ y)) → dominates_p σ₂ (prop.subst_env σ₁ P) P :=
  begin
    assume env_equiv,
    
    induction σ₁ with σ' x v ih,

    show dominates_p σ₂ (prop.subst_env env.empty P) P, by begin
      unfold prop.subst_env,
      from vc.implies.self
    end,

    show dominates_p σ₂ (prop.subst_env (σ'[x↦v]) P) P, by begin
      unfold prop.subst_env,
      have h2: dominates_p σ₂ (prop.subst x v (prop.subst_env σ' P)) (prop.subst_env σ' P), by begin
        by_cases (x ∈ σ') with h,

        have h3: x ∉ FV (prop.subst_env σ' P), from prop.not_free_of_subst_env h,
        have h4: (prop.subst x v (prop.subst_env σ' P) = prop.subst_env σ' P),
        from unchanged_of_subst_nonfree_prop h3,
        have h5: dominates_p σ₂ (prop.subst_env σ' P) (prop.subst_env σ' P), from vc.implies.self,
        show dominates_p σ₂ (prop.subst x v (prop.subst_env σ' P)) (prop.subst_env σ' P), from h4.symm ▸ h5,

        have h2, from env_equiv x env.contains.same,
        have h3: ((σ'[x↦v]) x = v), from env.apply_of_contains h,
        have h4: (σ₂ x = v), from eq.trans h2.symm h3,
        show dominates_p σ₂ (prop.subst x v (prop.subst_env σ' P)) (prop.subst_env σ' P),
        from vc.implies.subst h4
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
      from vc.implies.trans h2 h4
    end,
  end

-/

lemma vc.implies.self {σ: env} {P: vc}: σ ⊨ vc.implies P P :=
  begin
    apply valid_env.mpr,
    from id
  end

/-

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

lemma vc.implies.quantifier {σ: env} {x: var} {t₁ t₂: term} {P Q: prop} : 
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
      from vc.implies.elim (h0 v) this,
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
  from vc.implies.no_quantifiers h_impl h_calls h_quantifiers

lemma vc.implies.true {σ: env} {P: prop}:
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
  show dominates_p σ P value.true, from vc.implies.no_quantifiers h_impl h_calls h_quantifiers

lemma vc.implies.true {σ: env} {P: prop}:
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
  show dominates_n σ P value.true, from vc.implies.no_quantifiers h_impl h_calls h_quantifiers

-/

lemma vc.implies.and_left_intro {P Q: prop} {σ: env}:
      ((σ ⊨ Q.to_vc) → σ ⊨ P.to_vc) → σ ⊨ vc.implies Q.to_vc (P ⋀ Q).to_vc :=
  begin
    assume h1,
    apply valid_env.mpr,
    assume h2,
    apply valid_env.to_vc_and,
    from h1 h2,
    from h2
  end

lemma vc.implies.and_right_intro {P Q: prop} {σ: env}:
      ((σ ⊨ P.to_vc) → σ ⊨ Q.to_vc) → σ ⊨ vc.implies P.to_vc (P ⋀ Q).to_vc :=
  begin
    assume h1,
    apply valid_env.mpr,
    assume h2,
    apply valid_env.to_vc_and,
    from h2,
    from h1 h2
  end

lemma vc.implies.and_intro {σ: env} {P P' Q Q': prop}:
      (σ ⊨ vc.implies P.to_vc P'.to_vc) → ((σ ⊨ P.to_vc) → σ ⊨ vc.implies Q.to_vc Q'.to_vc) →
      (σ ⊨ vc.implies (P ⋀ Q).to_vc (P' ⋀ Q').to_vc) :=
  begin
    assume h1,
    assume h2,
    apply valid_env.mpr,
    assume h3,
    have h4, from (valid_env.to_vc_and.elim h3).left,
    have h5, from (valid_env.to_vc_and.elim h3).right,
    have h6, from h2 h4,
    apply valid_env.to_vc_and,
    from valid_env.mp h1 h4,
    from valid_env.mp h6 h5
  end

lemma vc.implies.and_symm {σ: env} {P Q: prop}: (σ ⊨ vc.implies (P ⋀ Q).to_vc (Q ⋀ P).to_vc) :=
  begin
    apply valid_env.mpr,
    assume h1,
    apply valid_env.to_vc_and,
    from (valid_env.to_vc_and.elim h1).right,
    from (valid_env.to_vc_and.elim h1).left
  end

lemma vc.implies.and_elim_left {σ: env} {P₁ P₂ P₃: prop}:
      (σ ⊨ vc.implies P₁.to_vc (P₂ ⋀ P₃).to_vc) → (σ ⊨ vc.implies P₁.to_vc P₂.to_vc) :=
  begin
    assume h1,
    apply valid_env.mpr,
    assume h2,
    have h3, from valid_env.mp h1 h2,
    from (valid_env.to_vc_and.elim h3).left
  end

lemma vc.implies.and_assoc {σ: env} {P₁ P₂ P₃: prop}:
      σ ⊨ vc.implies (P₁ ⋀ P₂ ⋀ P₃).to_vc ((P₁ ⋀ P₂) ⋀ P₃).to_vc :=
  begin
    apply valid_env.mpr,
    assume h1,
    have h2, from (valid_env.to_vc_and.elim h1).right,

    apply valid_env.to_vc_and,
    apply valid_env.to_vc_and,
    from (valid_env.to_vc_and.elim h1).left,
    from (valid_env.to_vc_and.elim h2).left,
    from (valid_env.to_vc_and.elim h2).right
  end

lemma vc.implies.subst {σ: env} {x: var} {v: value} {P: prop}:
      (σ x = v) → (σ ⊨ vc.implies (prop.subst x v P).to_vc P.to_vc) :=
  begin
    assume h1,
    apply valid_env.mpr,
    assume h2,
    have h3: (vc.subst x v (prop.to_vc P) = prop.to_vc (prop.subst x v P)),
    from subst_distrib_to_vc,
    rw[h3.symm] at h2,
    have h4: (vc.subst_env σ (vc.subst x v (prop.to_vc P)) = vc.subst_env σ (prop.to_vc P)),
    from vc.subst_env_inner h1,
    rw[h4] at h2,
    from h2
  end

lemma valid_with_additional_var {P: vc} {x: var} {v: value} {σ: env}:
      (σ ⊨ P) → ((σ[x↦v]) ⊨ P) :=
  begin
    assume h1,

    by_cases (x ∈ σ) with h4,
    unfold vc.subst_env,
    have h7: x ∉ FV (vc.subst_env σ P), from vc.not_free_of_subst_env h4,
    have h8: (vc.subst x v (vc.subst_env σ P) = vc.subst_env σ P),
    from unchanged_of_subst_nonfree_vc h7,
    rw[←h8] at h1,
    from h1,

    by_cases (free_in_vc x P) with h5,

    have h8: x ∈ FV (vc.subst_env σ P),
    from vc.free_of_subst_env h5 h4,
    have h9, from valid.univ.free ⟨h8, h1⟩,
    have h10, from valid.univ.mpr h9 v,

    have h11: (vc.substt x ↑v (vc.subst_env σ P) = vc.subst x v (vc.subst_env σ P)),
    from vc.substt_value_eq_subst,
    rw[h11] at h10,
    unfold vc.subst_env,
    from h10,

    have h9: x ∉ FV (vc.subst_env σ P), by begin
      assume h10,
      have h11, from vc.free_of_free_subst_env h10,
      contradiction
    end,
    have h10: (vc.substt x v (vc.subst_env σ P) = vc.subst_env σ P),
    from unchanged_of_substt_nonfree_vc h9,
    unfold vc.subst_env,
    have h11: (vc.substt x ↑v (vc.subst_env σ P) = vc.subst x v (vc.subst_env σ P)),
    from vc.substt_value_eq_subst,
    have h12: (vc.subst_env σ P = vc.subst x v (vc.subst_env σ P)), from eq.trans h10.symm h11,
    rw[←h12],
    from h1
  end

lemma valid_with_additional_vars {P: vc} {σ: env}: (⊨ P) → (σ ⊨ P) :=
  begin
    assume h1,
    
    induction σ with σ' x v ih,

    show env.empty ⊨ P, by begin
      unfold vc.subst_env,
      from h1
    end,

    show (σ'[x↦v]) ⊨ P, by begin
      from valid_with_additional_var ih
    end
  end

lemma vc.implies.exis {σ: env} {x: var} {P: prop}:
      σ ⊨ vc.implies P.to_vc (prop.exis x P).to_vc :=
  begin
    apply valid_env.nmt,
    apply valid_env.mpr,
    assume h1,
    apply valid_env.not.mp,
    by_contradiction h2,
    unfold prop.to_vc at h1,
    have h3, from valid_env.not_not.mp h1,
    have h4: (vc.subst_env σ (vc.univ x (vc.not (prop.to_vc P)))
           = vc.univ x (vc.subst_env (σ.without x) (vc.not (prop.to_vc P)))),
    from vc.subst_env.univ,
    rw[h4] at h3,

    by_cases (x ∈ σ) with h4,
    have h5, from env.contains_apply_equiv.right.mpr h4,
    cases h5 with v h6,
    have h7, from valid.univ.mpr h3 v,
    have h8: (vc.substt x ↑v (vc.subst_env (env.without σ x) (vc.not (prop.to_vc P)))
            = vc.subst x v (vc.subst_env (env.without σ x) (vc.not (prop.to_vc P)))),
    from vc.substt_value_eq_subst,
    rw[h8] at h7,
    have h9: (vc.subst x v (vc.subst_env (env.without σ x) (vc.not (prop.to_vc P)))
     = vc.subst_env ((env.without σ x)[x↦v]) (vc.not (prop.to_vc P))),
    by unfold vc.subst_env,
    rw[h9] at h7,
    have h10: (vc.subst_env ((env.without σ x)[x↦v]) (vc.not (prop.to_vc P)) = vc.subst_env σ (vc.not (prop.to_vc P))),
    from vc.subst_env_with_without_equivalent h6,
    rw[h10] at h7,
    have h11, from valid_env.not.mpr h7,
    contradiction,

    have h5: (env.without σ x = σ), from env.without_nonexisting h4,
    rw[h5] at h3,
    by_cases (free_in_vc x P.to_vc) with h6,

    have h7: x ∈ FV P.to_vc, from h6,
    have h8: x ∈ FV (vc.subst_env σ P.to_vc),
    from vc.free_of_subst_env h7 h4,
    have h9, from valid.univ.free ⟨h8, h2⟩,
    have h10, from valid.univ.mpr h3 value.true,
    have h11, from valid.univ.mpr h9 value.true,
    have h12: (vc.subst_env σ (vc.substt x value.true (vc.not (prop.to_vc P)))
             = vc.substt x value.true (vc.subst_env σ (vc.not (prop.to_vc P)))),
    from vc.substt_env.order (λx, free_in_term.value.inv) h4,
    rw[h12.symm] at h10,
    have h13: (vc.subst_env σ (vc.substt x value.true (prop.to_vc P))
             = vc.substt x value.true (vc.subst_env σ (prop.to_vc P))),
    from vc.substt_env.order (λx, free_in_term.value.inv) h4,
    rw[h13.symm] at h11,
    unfold vc.substt at h10,
    have h14, from valid_env.not.mpr h10,
    contradiction,

    have h7, from valid.univ.mpr h3 value.true,
    have h8: x ∉ FV (vc.not P.to_vc), by begin
      assume h9,
      have h10, from free_in_vc.not.inv h9,
      contradiction
    end,
    have h9: x ∉ FV (vc.subst_env σ (vc.not (prop.to_vc P))), by begin
      assume h10,
      have h11, from vc.free_of_free_subst_env h10,
      contradiction
    end,
    have h10: (vc.substt x ↑value.true (vc.subst_env σ (vc.not (prop.to_vc P)))
            = (vc.subst_env σ (vc.not (prop.to_vc P)))),
    from unchanged_of_substt_nonfree_vc h9,
    rw[h10] at h7,
    have h11, from valid_env.not.mpr h7,
    contradiction
  end

lemma vc.implies.same_right {σ: env} {P P' Q: prop}:
  ((σ ⊨ Q.to_vc) → σ ⊨ vc.implies P.to_vc P'.to_vc) → (σ ⊨ vc.implies (P ⋀ Q).to_vc (P' ⋀ Q).to_vc) :=
  begin
    assume h1: (σ ⊨ Q.to_vc) → σ ⊨ vc.implies P.to_vc P'.to_vc,
    apply valid_env.mpr,
    assume h2: σ ⊨ (P ⋀ Q).to_vc,
    apply valid_env.to_vc_and,
    have h3, from (valid_env.to_vc_and.elim h2).left,
    from valid_env.mp (h1 (valid_env.to_vc_and.elim h2).right) h3,
    from (valid_env.to_vc_and.elim h2).right
  end

lemma vc.implies.and_assoc.symm {P₁ P₂ P₃: prop} {σ: env}:
      σ ⊨ vc.implies ((P₁ ⋀ P₂) ⋀ P₃).to_vc (P₁ ⋀ P₂ ⋀ P₃).to_vc :=
  have h1: σ ⊨ vc.implies ((P₁ ⋀ P₂) ⋀ P₃).to_vc (P₃ ⋀ P₁ ⋀ P₂).to_vc, from vc.implies.and_symm,
  have h2: σ ⊨ vc.implies (P₃ ⋀ P₁ ⋀ P₂).to_vc ((P₃ ⋀ P₁) ⋀ P₂).to_vc, from vc.implies.and_assoc,
  have h3: σ ⊨ vc.implies ((P₃ ⋀ P₁) ⋀ P₂).to_vc (P₂ ⋀ P₃ ⋀ P₁).to_vc, from vc.implies.and_symm,
  have h4: σ ⊨ vc.implies (P₂ ⋀ P₃ ⋀ P₁).to_vc ((P₂ ⋀ P₃) ⋀ P₁).to_vc, from vc.implies.and_assoc,
  have h5: σ ⊨ vc.implies ((P₂ ⋀ P₃) ⋀ P₁).to_vc (P₁ ⋀ P₂ ⋀ P₃).to_vc , from vc.implies.and_symm,
  show σ ⊨ vc.implies ((P₁ ⋀ P₂) ⋀ P₃).to_vc (P₁ ⋀ P₂ ⋀ P₃).to_vc,
  from vc.implies.trans h1 (vc.implies.trans h2 (vc.implies.trans h3 (vc.implies.trans h4 h5)))

lemma vc.implies.shuffle {P Q R S: prop} {σ: env}:
      σ ⊨ vc.implies (P ⋀ Q ⋀ R ⋀ S).to_vc ((P ⋀ Q ⋀ R) ⋀ S).to_vc :=
  have h1: σ ⊨ vc.implies (P ⋀ Q ⋀ R ⋀ S).to_vc ((Q ⋀ R ⋀ S) ⋀ P).to_vc, from vc.implies.and_symm,
  have h2: σ ⊨ vc.implies ((Q ⋀ R ⋀ S) ⋀ P).to_vc (((Q ⋀ R) ⋀ S) ⋀ P).to_vc,
  from vc.implies.same_right (λ_, vc.implies.and_assoc),
  have h3: σ ⊨ vc.implies  (((Q ⋀ R) ⋀ S) ⋀ P).to_vc ((Q ⋀ R) ⋀ S ⋀ P).to_vc, from vc.implies.and_assoc.symm,
  have h4: σ ⊨ vc.implies ((Q ⋀ R) ⋀ S ⋀ P).to_vc ((S ⋀ P) ⋀ Q ⋀ R).to_vc, from vc.implies.and_symm,
  have h5: σ ⊨ vc.implies ((S ⋀ P) ⋀ Q ⋀ R).to_vc (S ⋀ P ⋀ Q ⋀ R).to_vc, from vc.implies.and_assoc.symm,
  have h6: σ ⊨ vc.implies (S ⋀ P ⋀ Q ⋀ R).to_vc ((P ⋀ Q ⋀ R) ⋀ S).to_vc, from vc.implies.and_symm,
  show σ ⊨ vc.implies  (P ⋀ Q ⋀ R ⋀ S).to_vc ((P ⋀ Q ⋀ R) ⋀ S).to_vc,
  from vc.implies.trans h1 (vc.implies.trans h2 (vc.implies.trans h3 (vc.implies.trans h4 (vc.implies.trans h5 h6))))

lemma vc.implies.same_left {σ: env} {P Q Q': prop}:
      ((σ ⊨ P.to_vc) → σ ⊨ vc.implies Q.to_vc Q'.to_vc) → σ ⊨ vc.implies (P ⋀ Q).to_vc (P ⋀ Q').to_vc :=
  assume h1: (σ ⊨ P.to_vc) → σ ⊨ vc.implies Q.to_vc Q'.to_vc,
  have h2: σ ⊨ vc.implies (P ⋀ Q).to_vc (Q ⋀ P).to_vc, from vc.implies.and_symm,
  have h3: σ ⊨ vc.implies (Q ⋀ P).to_vc (Q' ⋀ P).to_vc, from vc.implies.same_right h1,
  have h4: σ ⊨ vc.implies (Q' ⋀ P).to_vc (P ⋀ Q').to_vc, from vc.implies.and_symm,
  show σ ⊨ vc.implies (P ⋀ Q).to_vc (P ⋀ Q').to_vc,
  from vc.implies.trans h2 (vc.implies.trans h3 h4)

lemma vc.implies.and_elim_right {σ: env} {P₁ P₂ P₃: prop}:
      (σ ⊨ vc.implies P₁.to_vc (P₂ ⋀ P₃).to_vc) → σ ⊨ vc.implies P₁.to_vc P₃.to_vc :=
  assume h1: σ ⊨ vc.implies P₁.to_vc (P₂ ⋀ P₃).to_vc,
  have h2: σ ⊨ vc.implies (P₂ ⋀ P₃).to_vc (P₃ ⋀ P₂).to_vc, from vc.implies.and_symm,
  have h3: σ ⊨ vc.implies P₁.to_vc (P₃ ⋀ P₂).to_vc, from vc.implies.trans h1 h2,
  show σ ⊨ vc.implies P₁.to_vc P₃.to_vc, from vc.implies.and_elim_left h3

lemma vc.implies.left_elim {P₁ P₂ P₃: prop} {σ: env}:
      ((σ ⊨ P₁.to_vc) → σ ⊨ vc.implies P₂.to_vc P₃.to_vc) → σ ⊨ vc.implies (P₁ ⋀ P₂).to_vc P₃.to_vc :=
  assume h1: (σ ⊨ P₁.to_vc) → σ ⊨ vc.implies P₂.to_vc P₃.to_vc,
  have h2: σ ⊨ vc.implies (P₁ ⋀ P₂).to_vc (P₁ ⋀ P₃).to_vc, from vc.implies.same_left h1,
  show σ ⊨ vc.implies (P₁ ⋀ P₂).to_vc P₃.to_vc, from vc.implies.and_elim_right h2

lemma vc.implies.right_elim {P₁ P₂ P₃: prop} {σ: env}:
      ((σ ⊨ P₂.to_vc) → σ ⊨ vc.implies P₁.to_vc P₃.to_vc) → σ ⊨ vc.implies (P₁ ⋀ P₂).to_vc P₃.to_vc :=
  assume h1: (σ ⊨ P₂.to_vc) → σ ⊨ vc.implies P₁.to_vc P₃.to_vc,
  have h2: σ ⊨ vc.implies (P₁ ⋀ P₂).to_vc (P₃ ⋀ P₂).to_vc, from vc.implies.same_right h1,
  show σ ⊨ vc.implies (P₁ ⋀ P₂).to_vc P₃.to_vc, from vc.implies.and_elim_left h2

lemma vc.implies.of_and_left {P₁ P₂: prop} {σ: env}: σ ⊨ vc.implies (P₁ ⋀ P₂).to_vc P₁.to_vc :=
  have σ ⊨ vc.implies (P₁ ⋀ P₂).to_vc (P₁ ⋀ P₂).to_vc, from vc.implies.self,
  show σ ⊨ vc.implies (P₁ ⋀ P₂).to_vc P₁.to_vc, from vc.implies.and_elim_left this

lemma vc.implies.of_and_right {P₁ P₂: prop} {σ: env}: σ ⊨ vc.implies (P₁ ⋀ P₂).to_vc P₂.to_vc :=
  have h1: σ ⊨ vc.implies (P₁ ⋀ P₂).to_vc (P₂ ⋀ P₁).to_vc, from vc.implies.and_symm,
  have h2: σ ⊨ vc.implies (P₂ ⋀ P₁).to_vc P₂.to_vc, from vc.implies.of_and_left,
  show σ ⊨ vc.implies (P₁ ⋀ P₂).to_vc P₂.to_vc, from vc.implies.trans h1 h2

lemma vc.implies.equiv_subst {σ₁ σ₂: env} {P: prop}:
  (∀y, y ∈ σ₁ → (σ₁ y = σ₂ y)) → σ₂ ⊨ vc.implies (prop.subst_env σ₁ P).to_vc P.to_vc :=
  begin
    assume env_equiv,
    
    induction σ₁ with σ' x v ih,

    show σ₂ ⊨ vc.implies (prop.to_vc (prop.subst_env env.empty P)) (prop.to_vc P), by begin
      unfold prop.subst_env,
      from vc.implies.self
    end,

    unfold prop.subst_env,
    have h2: σ₂ ⊨ vc.implies (prop.subst x v (prop.subst_env σ' P)).to_vc (prop.subst_env σ' P).to_vc, by begin
      by_cases (x ∈ σ') with h,

      have h3: x ∉ FV (prop.subst_env σ' P), from prop.not_free_of_subst_env h,
      have h4: (prop.subst x v (prop.subst_env σ' P) = prop.subst_env σ' P),
      from unchanged_of_subst_nonfree_prop h3,
      have h5: σ₂ ⊨ vc.implies (prop.subst_env σ' P).to_vc (prop.subst_env σ' P).to_vc, from vc.implies.self,
      from h4.symm ▸ h5,

      have h2, from env_equiv x env.contains.same,
      have h3: ((σ'[x↦v]) x = v), from env.apply_of_contains h,
      have h4: (σ₂ x = v), from eq.trans h2.symm h3,
      show σ₂ ⊨ vc.implies (prop.subst x v (prop.subst_env σ' P)).to_vc (prop.subst_env σ' P).to_vc,
      from vc.implies.subst h4
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
    from vc.implies.trans h2 h4
  end

lemma valid_env.equiv_env {σ₁ σ₂: env} {P: prop}: (∀y, y ∈ σ₁ → (σ₁ y = σ₂ y)) → (σ₁ ⊨ P.to_vc) → σ₂ ⊨ P.to_vc :=
  begin
    assume h1,
    have h2: σ₂ ⊨ vc.implies (prop.subst_env σ₁ P).to_vc P.to_vc, from vc.implies.equiv_subst h1,
    have h3, from valid_env.mp h2,
    assume h4,
    have h5: (σ₂ ⊨ prop.to_vc (prop.subst_env σ₁ P)), by begin
      have h6: (vc.subst_env σ₁ (prop.to_vc P) = prop.to_vc (prop.subst_env σ₁ P)),
      from subst_env_distrib_to_vc,
      rw[h6] at h4,
      from valid_with_additional_vars h4
    end,
    from h3 h5
  end
