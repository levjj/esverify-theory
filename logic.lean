import .syntax .notations .evaluation .substitution .qi .vcgen .bindings

-- simple axioms for logical reasoning

axiom valid.tru:
  ⊨ value.true

axiom valid.not {P: vc}:
  ¬ (⊨ P)
  ↔
  ⊨ P.not

axiom valid.and {P Q: vc}:
  (⊨ P) ∧ (⊨ Q)
  ↔
  ⊨ P ⋀ Q

axiom valid.or {P Q: vc}:
  (⊨ P) ∨ (⊨ Q)
  ↔
  ⊨ P ⋁ Q

axiom valid.implies  {P Q: vc}:
  (⊨ P) → (⊨ Q)
  ↔
  ⊨ vc.implies P Q

axiom valid.univ {x: var} {P: vc}:
  (∀v, ⊨ vc.subst x v P)
  ↔
  ⊨ vc.univ x P

-- axioms for equality

-- a term is valid if it equals true
axiom valid.eq.true {t: term}:
  ⊨ t
  ↔
  ⊨ t ≡ value.true

-- unary and binary operators are decidable, so equalities with operators are decidable
axiom valid.eq.unop {op: unop} {vₓ v: value}:
  unop.apply op vₓ = some v
  ↔
  ⊨ term.unop op vₓ ≡ v

axiom valid.eq.binop {op: binop} {v₁ v₂ v: value}:
  binop.apply op v₁ v₂ = some v
  ↔
  ⊨ term.binop op v₁ v₂ ≡ v

-- The following equality axiom is non-standard and makes validity undecidable.
-- It is only used in the preservation proof of e-return and in no other lemmas.
-- The logic treats `f(x)` uninterpreted, so there is no way to derive it naturally.
-- However, given a complete evaluation derivation of a function call, we can add the
-- equality `f(x)=y` as new axiom for closed values f, x, y and the resulting set
-- of axioms is still sound due to deterministic evaluation.
axiom valid.eq.app {vₓ v: value} {σ σ': env} {H H': history} {f x y: var} {R S: spec} {e: exp}:
  (R, H, σ[x↦vₓ], e) ⟶* (R, H', σ', exp.return y) ∧
  (σ' y = some v)
  →
  ⊨ term.app (value.func f x R S e H σ) vₓ ≡ v

-- can write pre₁ and pre₂ to check domain of operators

axiom valid.pre₁ {vₓ: value} {op: unop}:
  option.is_some (unop.apply op vₓ)
  ↔
  ⊨ vc.pre₁ op vₓ

axiom valid.pre₂ {v₁ v₂: value} {op: binop}:
  option.is_some (binop.apply op v₁ v₂)
  ↔
  ⊨ vc.pre₂ op v₁ v₂

-- can write pre and post to extract pre- and postcondition of function values

axiom valid.pre.mp {vₓ: value} {σ: env} {f x: var} {R S: spec} {e: exp} {H: history}:
  (σ[f↦value.func f x R S e H σ][x↦vₓ] ⊨ R.to_prop.instantiated_n)
  →
  ⊨ vc.pre (value.func f x R S e H σ) vₓ

axiom valid.pre.mpr {vₓ: value} {σ: env} {f x: var} {R S: spec} {e: exp} {H: history}:
  (⊨ vc.pre (value.func f x R S e H σ) vₓ)
  →
  (σ[f↦value.func f x R S e H σ][x↦vₓ] ⊨ R.to_prop.instantiated)

axiom valid.post {vₓ: value} {σ: env} {Q: prop} {Q₂: propctx} {f x: var} {R S: spec} {e: exp} {H: history}:
  (⊢ σ : Q) →
  (H ⋀ Q ⋀ spec.func f x R S ⋀ R ⊢ e : Q₂) →
  (⊨ vc.post (value.func f x R S e H σ) vₓ)
  →
  (σ[f↦value.func f x R S e H σ][x↦vₓ] ⊨ (Q₂ (term.app f x) ⋀ S.to_prop).instantiated)

-- lemmas

lemma valid.neg_neg {P: vc}: (⊨ P.not.not) ↔ ⊨ P :=
  iff.intro (
    assume : ⊨ P.not.not,
    have h1: ¬ ⊨ P.not, from valid.not.mpr this,
    have h2: ¬ ¬ ⊨ P, from (
      assume : ¬ ⊨ P,
      have ⊨ P.not, from valid.not.mp this,
      show «false», from h1 this
    ),
    show ⊨ P, from classical.by_contradiction (
      assume : ¬ ⊨ P,
      show «false», from h2 this
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
  have binop.apply binop.eq v v = @ite (v = v)
                                  (classical.prop_decidable (v = v))
                                  value value.true value.false, by unfold binop.apply,
  have binop.apply binop.eq v v = value.true, by simp[this],
  have ⊨ ((v ≡ v) ≡ value.true), from valid.eq.binop.mp this,
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

lemma valid_env.eq.true {σ: env} {t: term}: σ ⊨ t ↔ σ ⊨ (t ≡ value.true) :=
  iff.intro (
    assume t_valid: ⊨ vc.subst_env σ t,
    have vc.subst_env σ t = vc.term (term.subst_env σ t), from vc.subst_env.term,
    have ⊨ vc.term (term.subst_env σ t), from this ▸ t_valid,
    have h: ⊨ vc.term ((term.subst_env σ t) ≡ value.true), from valid.eq.true.mp this,
    have term.subst_env σ value.true = value.true, from term.subst_env.value,
    have h2: ⊨ vc.term ((term.subst_env σ t) ≡ (term.subst_env σ value.true)),
    from this.symm ▸ h,
    have (term.subst_env σ (t ≡ value.true)) = ((term.subst_env σ t) ≡ (term.subst_env σ value.true)),
    from term.subst_env.binop,
    have h3: ⊨ term.subst_env σ (t ≡ value.true),
    from this.symm ▸ h2,
    have vc.subst_env σ (t ≡ value.true) = vc.term (term.subst_env σ (t ≡ value.true)), from vc.subst_env.term,
    show σ ⊨ (t ≡ value.true), from this.symm ▸ h3
  ) (
    assume t_valid: ⊨ vc.subst_env σ (t ≡ value.true),
    have vc.subst_env σ (t ≡ value.true) = vc.term (term.subst_env σ (t ≡ value.true)), from vc.subst_env.term,
    have h: ⊨ vc.term (term.subst_env σ (t ≡ value.true)),
    from this ▸ t_valid,
    have (term.subst_env σ (t ≡ value.true)) = ((term.subst_env σ t) ≡ (term.subst_env σ value.true)),
    from term.subst_env.binop,
    have h2: ⊨ vc.term ((term.subst_env σ t) ≡ (term.subst_env σ value.true)),
    from this ▸ h,
    have term.subst_env σ value.true = value.true, from term.subst_env.value,
    have ⊨ vc.term ((term.subst_env σ t) ≡ value.true), from this ▸ h2,
    have h3: ⊨ vc.term (term.subst_env σ t), from valid.eq.true.mpr this,
    have vc.subst_env σ t = vc.term (term.subst_env σ t), from vc.subst_env.term,
    show ⊨ vc.subst_env σ t, from this.symm ▸ h3
  )

lemma valid_env.neg_neg {σ: env} {P: vc}: (σ ⊨ P.not.not) ↔ σ ⊨ P :=
  iff.intro (
    assume h1: σ ⊨ P.not.not,
    have vc.subst_env σ P.not.not = (vc.subst_env σ P.not).not, from vc.subst_env.not,
    have h2: ⊨ (vc.subst_env σ P.not).not, from this ▸ h1,
    have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
    have  ⊨ (vc.subst_env σ P).not.not, from this ▸ h2,
    show σ ⊨ P, from valid.neg_neg.mp this
  ) (
    assume : σ ⊨ P,
    have h1: ⊨ (vc.subst_env σ P).not.not, from valid.neg_neg.mpr this,
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
  assume : ⊨ vc.subst_env σ P,
  have h: ⊨ vc.subst_env σ P ⋁ vc.subst_env σ Q, from valid.or.mp (or.inl this),
  have vc.subst_env σ (P ⋁ Q) = (vc.subst_env σ P ⋁ vc.subst_env σ Q), from vc.subst_env.or,
  show σ ⊨ (P ⋁ Q), from this.symm ▸ h

lemma valid_env.or₂ {σ: env} {P Q: vc}: (σ ⊨ Q) → σ ⊨ (P ⋁ Q) :=
  assume : ⊨ vc.subst_env σ Q,
  have h: ⊨ vc.subst_env σ P ⋁ vc.subst_env σ Q, from valid.or.mp (or.inr this),
  have vc.subst_env σ (P ⋁ Q) = (vc.subst_env σ P ⋁ vc.subst_env σ Q), from vc.subst_env.or,
  show σ ⊨ (P ⋁ Q), from this.symm ▸ h

lemma valid_env.or.elim {σ: env} {P Q: vc}: (σ ⊨ P ⋁ Q) → (σ ⊨ P) ∨ σ ⊨ Q :=
  assume p_or_q_valid: ⊨ vc.subst_env σ (P ⋁ Q),
  have vc.subst_env σ (P ⋁ Q) = (vc.subst_env σ P ⋁ vc.subst_env σ Q), from vc.subst_env.or,
  have ⊨ (vc.subst_env σ P ⋁ vc.subst_env σ Q), from this ▸ p_or_q_valid,
  show (σ ⊨ P) ∨ (σ ⊨ Q), from valid.or.mpr this

lemma valid_env.not {σ: env} {P: vc}: ¬ (σ ⊨ P) ↔ (σ ⊨ P.not) :=
  iff.intro (
    assume h1: ¬ (σ ⊨ P),
    have h2: vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
    have ¬ ⊨ (vc.subst_env σ P), from h2 ▸ h1,
    have ⊨ (vc.subst_env σ P).not, from valid.not.mp this,
    show σ ⊨ P.not, from h2.symm ▸ this
  ) (
    assume h1: σ ⊨ P.not,
    have h2: vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
    have ⊨ (vc.subst_env σ P).not, from h2 ▸ h1,
    have ¬ ⊨ (vc.subst_env σ P), from valid.not.mpr this,
    show ¬ (σ ⊨ P), from h2.symm ▸ this
  )

lemma valid_env.mp {σ: env} {P Q: vc}: (σ ⊨ vc.implies P Q) → (σ ⊨ P) → σ ⊨ Q :=
  assume impl: σ ⊨ (vc.implies P Q),
  assume p: σ ⊨ P,
  have vc.subst_env σ (vc.implies P Q) = (vc.subst_env σ P.not ⋁ vc.subst_env σ Q), from vc.subst_env.or,
  have h: ⊨ (vc.subst_env σ P.not ⋁ vc.subst_env σ Q), from this ▸ impl,
  have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  have ⊨ ((vc.subst_env σ P).not ⋁ vc.subst_env σ Q), from this ▸ h,
  have ⊨ vc.implies (vc.subst_env σ P) (vc.subst_env σ Q), from this,
  show σ ⊨ Q, from valid.implies.mpr this p

lemma valid_env.mpr {σ: env} {P Q: vc}: ((σ ⊨ P) → σ ⊨ Q) → σ ⊨ vc.implies P Q :=
  assume : ((σ ⊨ P) → σ ⊨ Q),
  have ⊨ vc.implies (vc.subst_env σ P) (vc.subst_env σ Q), from valid.implies.mp this,
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
  assume h2: σ ⊨ vc.implies P₂ P₃,
  show σ ⊨ vc.implies P₁ P₃, from valid_env.mpr (
    assume : σ ⊨ P₁,
    have σ ⊨ P₂, from valid_env.mp h1 this,
    show σ ⊨ P₃, from valid_env.mp h2 this
  )

lemma history_valid {H: history}: ⟪calls_to_prop H⟫ :=
  assume σ: env,
  begin
    induction H with H₁ f y R S e H₂ σ₂ v ih₁ ih₂,

    show σ ⊨ (calls_to_prop history.empty).instantiated, from (
      have h1: σ ⊨ value.true, from valid_env.true,
      have (prop.term value.true).erased = vc.term value.true, by unfold prop.erased,
      have σ ⊨ (prop.term value.true).erased, from this ▸ h1,
      have h2: σ ⊨ (prop.term value.true).instantiated, from valid_env.instantiated_of_erased this,
      have calls_to_prop history.empty = value.true, by unfold calls_to_prop,
      show σ ⊨ (calls_to_prop history.empty).instantiated, from this ▸ h2
    ),

    show σ ⊨ prop.instantiated (calls_to_prop (H₁ · call f y R S e H₂ σ₂ v)), from (
      have h1: σ ⊨ (calls_to_prop H₁).instantiated, from ih₁,
      have h2: σ ⊨ value.true, from valid_env.true,
      have (prop.call (value.func f y R S e H₂ σ₂) v).erased = vc.term value.true, by unfold prop.erased,
      have σ ⊨ (prop.call (value.func f y R S e H₂ σ₂) v).erased, from this ▸ h2,
      have h3: σ ⊨ (prop.call (value.func f y R S e H₂ σ₂) v).instantiated, from valid_env.instantiated_of_erased this,
      have σ ⊨ ((calls_to_prop H₁).instantiated ⋀ (prop.call (value.func f y R S e H₂ σ₂) v).instantiated),
      from valid_env.and h1 h3,
      have h4: σ ⊨ (calls_to_prop H₁ ⋀ prop.call (value.func f y R S e H₂ σ₂) v).instantiated,
      from valid_env.instantiated_and this,
      have calls_to_prop (H₁ · call f y R S e H₂ σ₂ v)
        = (calls_to_prop H₁ ⋀ prop.call (value.func f y R S e H₂ σ₂) v),
      by unfold calls_to_prop,
      show σ ⊨ (calls_to_prop (H₁ · call f y R S e H₂ σ₂ v)).instantiated, from this ▸ h4
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
  have FV (R.to_prop ⋀ ↑H ⋀ P) = FV ((R.to_prop ⋀ ↑H) ⋀ P), from free_in_prop.and_comm,
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
  x ∉ σ → (σ[x↦v]) ⊨ (prop.term (x ≡ v)).erased :=
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
  have prop.erased (prop.term (x ≡ v)) = vc.term (x ≡ v), by unfold prop.erased,
  have h8: vc.subst_env (σ[x↦v]) (prop.term (x ≡ v)).erased = vc.term (v ≡ v), from this.symm ▸ h7,
  have ⊨ vc.term (v ≡ v), from valid.refl,
  show (σ[x↦v]) ⊨ prop.erased (x ≡ v), from h8.symm ▸ this

lemma simple_equality_env_valid {P: prop} {σ: env} {x: var} {v: value}:
                                   (⊢ σ: P) → x ∉ σ → (σ ⊨ P.instantiated) → ((σ[x↦v]) ⊨ P.instantiated)
                                                             ∧ ((σ[x↦v]) ⊨ (prop.term (x ≡ v)).instantiated) :=
  assume σ_verified: ⊢ σ: P,
  assume x_not_free_in_σ: x ∉ σ,
  assume ih: σ ⊨ P.instantiated,
  have σ.apply x = none, from env.contains_apply_equiv.left.mpr x_not_free_in_σ,
  have h1: ⊨ vc.subst_env σ P.instantiated, from ih,
  have x_not_in_P: x ∉ FV (vc.subst_env σ P.instantiated), from (
    assume : x ∈ FV (vc.subst_env σ P.instantiated),
    have x ∈ FV P.instantiated, from free_in_vc.subst_env this,
    have x ∈ FV P.erased, from free_in_erased_of_free_in_instantiated this,
    have x ∈ FV P, from free_of_erased_free (or.inl this),
    have ∃v, σ x = some v, from val_of_free_in_env σ_verified this,
    have x ∈ σ, from env.contains_apply_equiv.right.mp this,
    show «false», from x_not_free_in_σ this
  ),
  have vc.subst x v (vc.subst_env σ P.instantiated) = vc.subst_env σ P.instantiated,
  from unchanged_of_subst_nonfree_vc x_not_in_P,
  have h2: ⊨ vc.subst x v (vc.subst_env σ P.instantiated),
  from @eq.subst vc (λa, ⊨ a) (vc.subst_env σ P.instantiated)
          (vc.subst x v (vc.subst_env σ P.instantiated)) this.symm h1,
  have vc.subst x v (vc.subst_env σ P.instantiated)
      = vc.subst_env (σ[x↦v]) P.instantiated, by unfold vc.subst_env, 
  have h3: ⊨ vc.subst_env (σ[x↦v]) P.instantiated, from this ▸ h2,
  have (σ[x↦v]) ⊨ (prop.term (x ≡ v)).erased,
  from simple_equality_valid x_not_free_in_σ,
  have (σ[x↦v]) ⊨ (prop.term (x ≡ v)).instantiated, from valid_env.instantiated_of_erased this,
  ⟨h3, this⟩

lemma simple_equality_env_inst_valid {P: prop} {σ: env} {x: var} {v: value}:
                                   (⊢ σ: P) → x ∉ σ → (σ ⊨ P.instantiated) → (σ[x↦v]) ⊨ (P ⋀ x ≡ v).instantiated :=
  assume σ_verified: ⊢ σ: P,
  assume x_not_free_in_σ: x ∉ σ,
  assume ih: σ ⊨ P.instantiated,
  have ((σ[x↦v]) ⊨ P.instantiated) ∧ ((σ[x↦v]) ⊨ (prop.term (x ≡ v)).instantiated),
  from simple_equality_env_valid σ_verified x_not_free_in_σ ih,
  have (σ[x↦v]) ⊨ (P.instantiated ⋀ (prop.term (x ≡ v)).instantiated),
  from valid_env.and this.left this.right,
  show (σ[x↦v]) ⊨ prop.instantiated (P ⋀ (x ≡ v)), from valid_env.instantiated_and this

lemma env_translation_erased_valid {P: prop} {σ: env}: (⊢ σ: P) → σ ⊨ P.instantiated :=
  assume env_verified: (⊢ σ : P),
  begin
    induction env_verified,
    case env.vcgen.empty {
      show env.empty ⊨ prop.instantiated (value.true), from (
        have h: prop.erased (prop.term ↑value.true) = vc.term ↑value.true, by unfold prop.erased,
        have env.empty ⊨ value.true, from valid.tru,
        have env.empty ⊨ prop.erased (value.true), from h ▸ this,
        show env.empty ⊨ prop.instantiated (value.true), from valid_env.instantiated_of_erased this
      )
    },
    case env.vcgen.tru σ' x' Q x_not_free_in_σ' σ'_verified ih {
      show (σ'[x'↦value.true]) ⊨ prop.instantiated (Q ⋀ (x' ≡ value.true)),
      from simple_equality_env_inst_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.vcgen.fls σ' x' Q x_not_free_in_σ' σ'_verified ih {
      show (σ'[x'↦value.false]) ⊨ prop.instantiated (Q ⋀ (x' ≡ value.false)),
      from simple_equality_env_inst_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.vcgen.num n σ' x' Q x_not_free_in_σ' σ'_verified ih {
      show (σ'[x'↦value.num n]) ⊨ prop.instantiated (Q ⋀ (x' ≡ value.num n)),
      from simple_equality_env_inst_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.vcgen.func σ₁ σ₂ f g gx R S e H Q₁ Q₂ Q₃
      f_not_free_in_σ₁ g_not_free_in_σ₂ gx_not_free_in_σ₂ g_neq_gx σ₁_verified σ₂_verified gx_free_in_R R_fv S_fv func_verified
      S_valid ih₁ ih₂ { from (
      let vf := value.func g gx R S e H σ₂ in
      have h1: ((σ₁[f↦vf]) ⊨ Q₁.instantiated) ∧ ((σ₁[f↦vf]) ⊨ (prop.term (f ≡ vf)).instantiated),
      from simple_equality_env_valid σ₁_verified f_not_free_in_σ₁ ih₁,

      have g_subst: term.subst_env (σ₂[g↦vf]) g = vf, from (
        have h1: term.subst g vf g = vf, from term.subst.var.same,
        have σ₂ g = none, from env.contains_apply_equiv.left.mpr g_not_free_in_σ₂,
        have term.subst_env σ₂ g = g, from term.subst_env.var.left.mp this,
        have h2: term.subst g vf (term.subst_env σ₂ g) = vf, from this.symm ▸ h1,
        have term.subst_env (σ₂[g↦vf]) g = term.subst g vf (term.subst_env σ₂ g), by unfold term.subst_env,
        show term.subst_env (σ₂[g↦vf]) g = vf, from eq.trans this h2
      ),

      have h2: ⊨ prop.instantiated (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from (
        have unop.apply unop.isFunc vf = value.true, by unfold unop.apply,
        have ⊨ (term.unop unop.isFunc vf ≡ value.true), from valid.eq.unop.mp this,
        have ⊨ term.unop unop.isFunc vf, from valid.eq.true.mpr this,
        have h3: ⊨ term.unop unop.isFunc (term.subst_env (σ₂[g↦vf]) g), from g_subst.symm ▸ this,
        have term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g) = term.unop unop.isFunc (term.subst_env (σ₂[g↦vf]) g),
        from term.subst_env.unop,
        have h4: ⊨ vc.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from this.symm ▸ h3,
        have prop.erased (prop.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)))
           = vc.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)),
        by unfold prop.erased,
        have h5: ⊨ prop.erased (prop.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g))), from this.symm ▸ h4,
        have prop.subst_env (σ₂[g↦vf]) (prop.term (term.unop unop.isFunc g))
           = prop.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from prop.subst_env.term,
        have ⊨ prop.erased (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from this.symm ▸ h5,
        show ⊨ prop.instantiated (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)),
        from valid.instantiated_of_erased this
      ),

      let forallp := prop.implies R.to_prop (prop.pre g gx)
                  ⋀ prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop) in
      let pfunc: prop := prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S)) in

      have h4: ∀v, ⊨ vc.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp).instantiated, from (
        assume v: value,

        have h5: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))).instantiated, from (
          have h6: ⊨ vc.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).instantiated_n
                                (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).instantiated, from valid.implies.mp (
            assume h8: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).instantiated_n,
            have vc.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop.instantiated_n
                = (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).instantiated_n, from instantiated_n_distrib_subst_env,
            have ⊨ vc.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop.instantiated_n, from this.symm ▸ h8,
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
            have prop.erased (prop.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx))
               = (vc.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx)),
            by unfold prop.erased,
            have h15: ⊨ (prop.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx)).erased,
            from this.symm ▸ h14,
            have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)
               = prop.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from prop.subst_env.pre,
            have ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).erased, from this.symm ▸ h15,
            show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).instantiated,
            from valid.instantiated_of_erased this
          ),
          have h8: ⊨ (prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop)
                                   (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx))).instantiated,
          from valid.instantiated_implies h6,
          have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))
             = prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop)
                            (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)),
          from prop.subst_env.implies,
          show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))).instantiated,
          from this.symm ▸ h8
        ),

        have h6: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                     (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated, from (
          have h7: ⊨ vc.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)).instantiated_n
                                (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).instantiated,
          from valid.implies.mp (
            assume h8: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)).instantiated_n,
            have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)
               = prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from prop.subst_env.post,
            have ⊨ (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx))
                          .instantiated_n,
            from this ▸ h8,
            have h9: ⊨ (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx))
                          .erased_n, from valid.erased_n_of_instantiated_n this,
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
            have h15: (σ₂[g↦vf][gx↦v] ⊨ (Q₃ (term.app g gx) ⋀ S.to_prop).instantiated),
            from valid.post σ₂_verified func_verified this,
            have vc.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop).instantiated
              = (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).instantiated,
            from instantiated_distrib_subst_env,
            show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).instantiated,
            from this ▸ h15
          ),
          have h8: ⊨ (prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx))
                                   (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated,
          from valid.instantiated_implies h7,
          have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop))
             = prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx))
                            (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)),
          from prop.subst_env.implies,
          show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                      (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated,
          from this.symm ▸ h8
        ),

        have ⊨ ((prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))).instantiated ⋀
                (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                                (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated),
        from valid.and.mp ⟨h5, h6⟩,
        have h7: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx)) ⋀
                    prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                                   (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated,
        from valid.instantiated_and this,
        have prop.subst_env (σ₂[g↦vf][gx↦v]) forallp
           = (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx)) ⋀
             prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop))),
        from prop.subst_env.and,
        have h8: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) forallp).instantiated, from this.symm ▸ h7,
        have prop.subst_env (σ₂[g↦vf][gx↦v]) forallp = prop.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp),
        by unfold prop.subst_env,
        have h9: ⊨ (prop.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp)).instantiated, from this ▸ h8,
        have vc.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp).instantiated
           = (prop.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp)).instantiated, from instantiated_distrib_subst,
        show ⊨ vc.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp).instantiated, from this.symm ▸ h9
      ),

      have h5: ⊨ prop.instantiated (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)), from (
        have h6: ⊨ vc.univ gx (prop.subst_env (σ₂[g↦vf]) forallp).instantiated, from valid.univ.mp h4,
        have prop.instantiated (prop.forallc gx (term.subst_env (σ₂[g↦vf]) g) (prop.subst_env (σ₂[g↦vf]) forallp))
           = vc.univ gx (prop.subst_env (σ₂[g↦vf]) forallp).instantiated, from instantiated.forallc,
        have h7: ⊨ prop.instantiated (prop.forallc gx (term.subst_env (σ₂[g↦vf]) g) (prop.subst_env (σ₂[g↦vf]) forallp)), from this.symm ▸ h6,
        have ¬(gx = g ∨ gx ∈ σ₂), from not_or_distrib.mpr ⟨g_neq_gx.symm, gx_not_free_in_σ₂⟩,
        have gx ∉ (σ₂[g↦vf]), from (mt env.contains.inv) this,
        have (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)
            = prop.forallc gx (term.subst_env (σ₂[g↦vf]) g) (prop.subst_env (σ₂[g↦vf]) forallp)),
        from prop.subst_env.forallc this,
        show ⊨ prop.instantiated (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)), from this.symm ▸ h7
      ),

      have ⊨ (prop.instantiated (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)) ⋀
                  prop.instantiated (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp))),
      from valid.and.mp ⟨h2, h5⟩,
      have h7: ⊨ prop.instantiated (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g) ⋀
                                    prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)),
      from valid.instantiated_and this,
      have prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp)
         = (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g) ⋀ prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)),
      from prop.subst_env.and,
      have h8: ⊨ prop.instantiated (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp)),
      from this.symm ▸ h7,
      have prop.func g gx R.to_prop (Q₃ (term.app g gx) ⋀ S.to_prop)
         = (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp),
      by unfold prop.func,
      have ⊨ prop.instantiated (prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
      from this.symm ▸ h8,
      have h9: ⊨ prop.instantiated pfunc, from this,

      have h10: (∀x, x ∉ FV pfunc), from (
        have ⊢ (σ₂[g↦vf]) : Q₂
          ⋀ (g ≡ (vf))
          ⋀ prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S)),
        from env.vcgen.func g_not_free_in_σ₂ g_not_free_in_σ₂ gx_not_free_in_σ₂ g_neq_gx
             σ₂_verified σ₂_verified gx_free_in_R R_fv S_fv func_verified S_valid,
        prop_func_closed func_verified this
      ),

      have h11: (∀x, x ∉ FV pfunc.instantiated), from (
        assume x: var,
        assume : x ∈ FV pfunc.instantiated,
        have x ∈ FV pfunc.erased, from free_in_erased_of_free_in_instantiated this,
        have x ∈ FV pfunc.erased ∨ x ∈ FV pfunc.erased_n, from or.inl this,
        have x ∈ FV pfunc, from free_of_erased_free this,
        show «false», from (h10 x) this
      ),

      have vc.subst_env (σ₁[f↦vf]) pfunc.instantiated = pfunc.instantiated,
      from unchanged_of_subst_env_nonfree_vc h11 (σ₁[f↦vf]),
      have (σ₁[f↦vf]) ⊨ pfunc.instantiated, from this.symm ▸ h9,

      have (σ₁[f↦vf]) ⊨ ((prop.term (f ≡ vf)).instantiated ⋀ prop.instantiated pfunc), from valid_env.and h1.right this,
      have (σ₁[f↦vf]) ⊨ ((prop.term (f ≡ vf)) ⋀ pfunc).instantiated, from valid_env.instantiated_and this,
      have (σ₁[f↦vf]) ⊨ Q₁.instantiated ⋀ ((prop.term (f ≡ vf)) ⋀ pfunc).instantiated, from valid_env.and h1.left this,
      show (σ₁[f↦vf]) ⊨ (Q₁ ⋀ (f ≡ vf) ⋀ pfunc).instantiated,
      from valid_env.instantiated_and this
    )}
  end

lemma env_translation_valid {R: spec} {H: history} {P: prop} {σ: env}:
  (⊢ σ: P) → (σ ⊨ R.to_prop.instantiated) → σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_n :=
  assume env_verified: (⊢ σ : P),
  assume R_valid: (σ ⊨ R.to_prop.instantiated),
  have h1: σ ⊨ prop.instantiated ↑H, from history_valid σ,
  have h2: σ ⊨ P.instantiated, from env_translation_erased_valid env_verified,
  have σ ⊨ (prop.instantiated ↑H ⋀ P.instantiated), from valid_env.and h1 h2,
  have σ ⊨ (↑H ⋀ P).instantiated, from valid_env.instantiated_and this,
  have σ ⊨ R.to_prop.instantiated ⋀ (↑H ⋀ P).instantiated, from valid_env.and R_valid this,
  have σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated, from valid_env.instantiated_and this,
  show σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_n, from valid_env.instantiated_n_of_instantiated this

lemma consequent_of_H_P {R: spec} {H: history} {σ: env} {P Q: prop}:
  (⊢ σ: P) → (σ ⊨ R.to_prop.instantiated) → ⟪prop.implies (R ⋀ ↑H ⋀ P) Q⟫ → no_instantiations Q → σ ⊨ Q.erased :=
  assume env_verified: (⊢ σ : P),
  assume R_valid: (σ ⊨ R.to_prop.instantiated),
  assume impl_vc: ⟪prop.implies (R ⋀ ↑H ⋀ P) Q⟫,
  assume : no_instantiations Q,
  have h1: (prop.implies (R ⋀ ↑H ⋀ P) Q).instantiated = vc.or (↑R ⋀ ↑H ⋀ P).not.instantiated Q.erased,
  from or_dist_of_no_instantiations this,
  have h2: (↑R ⋀ ↑H ⋀ P).not.instantiated = (↑R ⋀ ↑H ⋀ P).instantiated_n.not, from not_dist_instantiated,
  have σ ⊨ (prop.implies (↑R ⋀ ↑H ⋀ P) Q).instantiated, from impl_vc σ,
  have σ ⊨ vc.or (↑R ⋀ ↑H ⋀ P).instantiated_n.not Q.erased, from h2 ▸ h1 ▸ this,
  have h4: σ ⊨ vc.implies (↑R ⋀ ↑H ⋀ P).instantiated_n Q.erased, from this,
  have σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_n, from env_translation_valid env_verified R_valid,
  show σ ⊨ Q.erased, from valid_env.mp h4 this

lemma env_translation_call_valid {R: spec} {H: history} {P: prop} {σ: env} {f x: var}:
  (⊢ σ: P) → (σ ⊨ R.to_prop.instantiated) → σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n :=
  assume env_verified: (⊢ σ : P),
  assume R_valid: (σ ⊨ R.to_prop.instantiated),
  have h1: σ ⊨ prop.instantiated ↑H, from history_valid σ,
  have h2: σ ⊨ P.instantiated, from env_translation_erased_valid env_verified,
  have σ ⊨ (prop.instantiated ↑H ⋀ P.instantiated), from valid_env.and h1 h2,
  have σ ⊨ (↑H ⋀ P).instantiated, from valid_env.instantiated_and this,
  have σ ⊨ R.to_prop.instantiated ⋀ (↑H ⋀ P).instantiated, from valid_env.and R_valid this,
  have h3: σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated, from valid_env.instantiated_and this,
  have h4: ⊨ value.true, from valid.tru,
  have term.subst_env σ value.true = value.true, from term.subst_env.value,
  have h5: ⊨ term.subst_env σ value.true, from this.symm ▸ h4,
  have vc.subst_env σ value.true = vc.term (term.subst_env σ value.true), from vc.subst_env.term,
  have h6: σ ⊨ value.true, from this.symm ▸ h5,
  have (prop.call f x).erased = vc.term value.true, by unfold prop.erased,
  have σ ⊨ (prop.call f x).erased, from this.symm ▸ h6,
  have σ ⊨ (prop.call f x).instantiated, from valid_env.instantiated_of_erased this,
  have σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated ⋀ (prop.call f x).instantiated, from valid_env.and h3 this,
  have σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated, from valid_env.instantiated_and this,
  show σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n, from valid_env.instantiated_n_of_instantiated this

lemma consequent_of_H_P_call {R: spec} {H: history} {σ: env} {P Q: prop} {f x: var}:
  (⊢ σ: P) → (σ ⊨ R.to_prop.instantiated) → ⟪prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q⟫ → no_instantiations Q → σ ⊨ Q.erased :=
  assume env_verified: (⊢ σ : P),
  assume R_valid: (σ ⊨ R.to_prop.instantiated),
  assume impl_vc: ⟪prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q⟫,
  assume : no_instantiations Q,
  have h1: (prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q).instantiated
         = vc.or ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).not.instantiated Q.erased,
  from or_dist_of_no_instantiations this,
  have h2: ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).not.instantiated = ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n.not,
  from not_dist_instantiated,
  have σ ⊨ (prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q).instantiated, from impl_vc σ,
  have σ ⊨ vc.or ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n.not Q.erased, from h2 ▸ h1 ▸ this,
  have h4: σ ⊨ vc.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n Q.erased, from this,
  have σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n, from env_translation_call_valid env_verified R_valid,
  show σ ⊨ Q.erased, from valid_env.mp h4 this