import .syntax .notations .logic .evaluation .vcgen .bindings

lemma no_calls_in_env_translation {P: prop} {σ: env}: (⊢ σ : P) → (calls_p P = ∅) :=
  assume env_verified: ⊢ σ : P,
  show calls_p P = ∅, by begin
    apply set.eq_empty_of_forall_not_mem,
    intro c,
    intro c_in_calls_p_P,
    induction env_verified,
    case env.vcgen.empty {
      cases c_in_calls_p_P
    },
    case env.vcgen.tru σ' y Q _ _ ih { from
      or.elim (prop.has_call_p.and.inv c_in_calls_p_P) (
        assume : c ∈ calls_p Q,
        show «false», from ih this
      ) (
        assume : c ∈ calls_p (y ≡ value.true),
        show «false», from prop.has_call_p.term.inv this
      )
    },
    case env.vcgen.fls σ' y Q _ _ ih { from
      or.elim (prop.has_call_p.and.inv c_in_calls_p_P) (
        assume : c ∈ calls_p Q,
        show «false», from ih this
      ) (
        assume : c ∈ calls_p (y ≡ value.false),
        show «false», from prop.has_call_p.term.inv this
      )
    },
    case env.vcgen.num n σ' y Q _ _ ih { from
      or.elim (prop.has_call_p.and.inv c_in_calls_p_P) (
        assume : c ∈ calls_p Q,
        show «false», from ih this
      ) (
        assume : c ∈ calls_p (y ≡ value.num n),
        show «false», from prop.has_call_p.term.inv this
      )
    },
    case env.vcgen.func f σ₂ σ₁ g gx R S e H Q₁ Q₂ Q₃ _ _ _ _ _ _ _ fv_R fv_S e_verified _ ih₁ ih₂ { from
      or.elim (prop.has_call_p.and.inv c_in_calls_p_P) (
        assume : c ∈ calls_p Q₁,
        show «false», from ih₁ this
      ) (
        assume : c ∈ calls_p (↑(f ≡ value.func g gx R S e H σ₂)
            ⋀ prop.subst_env (σ₂[g↦value.func g gx R S e H σ₂])
                             (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
        or.elim (prop.has_call_p.and.inv this) (
          assume : c ∈ calls_p (f ≡ value.func g gx R S e H σ₂),
          show «false», from prop.has_call_p.term.inv this
        ) (
          assume : c ∈ calls_p (prop.subst_env (σ₂[g↦value.func g gx R S e H σ₂])
                                               (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
          have ∃c', c' ∈ calls_p (prop.func g gx R (Q₃ (term.app g gx) ⋀ S)),
          from prop.has_call_of_subst_env_has_call.left c this,
          let ⟨c', h1⟩ := this in
          or.elim (prop.has_call_p.and.inv h1) (
            assume : c' ∈ calls_p (term.unop unop.isFunc g),
            show «false», from prop.has_call_p.term.inv this
          ) (
            assume h2,
            show «false», from prop.has_call_p.forallc.inv h2
          )
        )
      )
    }
  end

lemma same_free_and_left {P P' Q: prop}: FV P' = FV P → (FV (P' ⋀ Q) = FV (P ⋀ Q)) :=
  assume free_P'_P: FV P' = FV P,
  set.eq_of_subset_of_subset (
    assume x,
    assume : x ∈ FV (P' ⋀ Q),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P',
      have x ∈ FV P, from free_P'_P ▸ this,
      show x ∈ FV (P ⋀ Q), from free_in_prop.and₁ this
    ) (
      assume : x ∈ FV Q,
      show x ∈ FV (P ⋀ Q), from free_in_prop.and₂ this
    )
  ) (
    assume x,
    assume : x ∈ FV (P ⋀ Q),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P,
      have x ∈ FV P', from free_P'_P.symm ▸ this,
      show x ∈ FV (P' ⋀ Q), from free_in_prop.and₁ this
    ) (
      assume : x ∈ FV Q,
      show x ∈ FV (P' ⋀ Q), from free_in_prop.and₂ this
    )
  )

lemma dominates_true (σ: env) (P: prop):
      dominates σ P value.true :=

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
  show dominates σ P value.true, from dominates.no_quantifiers h_impl h_calls h_quantifiers

lemma exp.vcgen.inj {P: prop} {Q: propctx} {e: exp}: (P ⊢ e : Q) → ∀Q', (P ⊢ e : Q') → (Q = Q') :=
  assume h1: P ⊢ e : Q,
  begin
    induction h1,

    intros Q' h2,
    cases h2,
    have : (Q_1 = Q_2), from ih_1 Q_2 a_3,
    rw[this],

    intros Q' h2,
    cases h2,
    have : (Q_1 = Q_2), from ih_1 Q_2 a_3,
    rw[this],

    intros Q' h2,
    cases h2,
    have : (Q_1 = Q_2), from ih_1 Q_2 a_3,
    rw[this],

    intros Q' h2,
    cases h2,
    have h3: (Q₁ = Q₁_1), from ih_1 Q₁_1 a_15,
    rw[←h3] at a_16,
    have : (Q₂ = Q₂_1), from ih_2 Q₂_1 a_16,
    rw[this],
    rw[h3],

    intros Q' h2,
    cases h2,
    have : (Q_1 = Q_2), from ih_1 Q_2 a_6,
    rw[this],

    intros Q' h2,
    cases h2,
    have : (Q_1 = Q_2), from ih_1 Q_2 a_8,
    rw[this],

    intros Q' h2,
    cases h2,
    have : (Q_1 = Q_2), from ih_1 Q_2 a_8,
    rw[this],

    intros Q' h2,
    cases h2,
    have : (Q₁ = Q₁_1), from ih_1 Q₁_1 a_5,
    rw[this],
    have : (Q₂ = Q₂_1), from ih_2 Q₂_1 a_6,
    rw[this],
    refl,

    intros Q' h2,
    cases h2,
    refl
  end

lemma env.vcgen.inj {P: prop} {σ: env}: (⊢ σ : P) → ∀Q, (⊢ σ : Q) → (P = Q) :=
  assume h1: ⊢ σ : P,
  begin
    induction h1,

    intros Q h2,
    cases h2,
    refl,

    intros Q h2,
    cases h2,
    have : (Q = Q_1), from ih_1 Q_1 a_3,
    rw[this],
    refl,

    intros Q h2,
    cases h2,
    have : (Q = Q_1), from ih_1 Q_1 a_3,
    rw[this],
    refl,

    intros Q h2,
    cases h2,
    have : (Q = Q_1), from ih_1 Q_1 a_3,
    rw[this],
    refl,

    intros Q h2,
    cases h2,
    have h3: (Q₁ = Q₁_1), from ih_1 Q₁_1 a_15,
    rw[h3],
    have h4: (Q₂ = Q₂_1), from ih_2 Q₂_1 a_16,
    rw[←h4] at a_20,
    have : (Q₃ = Q₃_1), from exp.vcgen.inj a_9 Q₃_1 a_20,
    rw[this],
    refl
  end

lemma env_equiv_of_translation_valid {σ: env} {P: prop}:
      (⊢ σ: P) → ∀σ', (σ' ⊨ P.instantiated_p) → (∀x, x ∈ σ → (σ x = σ' x)) :=
  assume σ_verified: ⊢ σ: P,
  assume σ': env,
  assume P_valid: σ' ⊨ P.instantiated_p,
  assume x: var,
  assume x_in_σ: x ∈ σ,
  begin
    induction σ_verified,

    case env.vcgen.empty {
      cases x_in_σ
    },

    case env.vcgen.tru σ'' y Q _ _ ih {
      by_cases (y = x ∧ option.is_none (env.apply σ'' x)) with h,

      have h1: σ' ⊨ prop.instantiated_p (y ≡ value.true),
      from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_valid)).right,
      have h2: (σ' y = value.true), from valid_env.subst_of_eq_instantiated h1,
      change (env.apply (σ''[y↦value.true]) x = σ' x),
      unfold env.apply,
      simp[h],
      rw[←h.left],
      from h2.symm,

      change (env.apply (σ''[y↦value.true]) x = σ' x),
      unfold env.apply,
      simp[h],

      cases not_and_distrib.mp h,
      cases env.contains.inv x_in_σ,
      have : (y ≠ x), from a_2,
      have : (x ≠ y), from this.symm,
      contradiction,
      
      have h1: σ' ⊨ prop.instantiated_p Q,
      from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_valid)).left,
      from ih h1 a_3,

      have h1: σ' ⊨ prop.instantiated_p Q,
      from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_valid)).left,
      have h2, from option.some_iff_not_none.mpr a_2,
      have h4, from option.is_some_iff_exists.mp h2,
      have h5, from env.contains_apply_equiv.right.mp h4,
      from ih h1 h5
    },

    case env.vcgen.fls σ'' y Q _ _ ih {
      by_cases (y = x ∧ option.is_none (env.apply σ'' x)) with h,

      have h1: σ' ⊨ prop.instantiated_p (y ≡ value.false),
      from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_valid)).right,
      have h2: (σ' y = value.false), from valid_env.subst_of_eq_instantiated h1,
      change (env.apply (σ''[y↦value.false]) x = σ' x),
      unfold env.apply,
      simp[h],
      rw[←h.left],
      from h2.symm,

      change (env.apply (σ''[y↦value.false]) x = σ' x),
      unfold env.apply,
      simp[h],

      cases not_and_distrib.mp h,
      cases env.contains.inv x_in_σ,
      have : (y ≠ x), from a_2,
      have : (x ≠ y), from this.symm,
      contradiction,
      
      have h1: σ' ⊨ prop.instantiated_p Q,
      from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_valid)).left,
      from ih h1 a_3,

      have h1: σ' ⊨ prop.instantiated_p Q,
      from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_valid)).left,
      have h2, from option.some_iff_not_none.mpr a_2,
      have h4, from option.is_some_iff_exists.mp h2,
      have h5, from env.contains_apply_equiv.right.mp h4,
      from ih h1 h5
    },

    case env.vcgen.num n σ'' y Q _ _ ih {
      by_cases (y = x ∧ option.is_none (env.apply σ'' x)) with h,

      have h1: σ' ⊨ prop.instantiated_p (y ≡ value.num n),
      from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_valid)).right,
      have h2: (σ' y = value.num n), from valid_env.subst_of_eq_instantiated h1,
      change (env.apply (σ''[y↦value.num n]) x = σ' x),
      unfold env.apply,
      simp[h],
      rw[←h.left],
      from h2.symm,

      change (env.apply (σ''[y↦value.num n]) x = σ' x),
      unfold env.apply,
      simp[h],

      cases not_and_distrib.mp h,
      cases env.contains.inv x_in_σ,
      have : (y ≠ x), from a_2,
      have : (x ≠ y), from this.symm,
      contradiction,
      
      have h1: σ' ⊨ prop.instantiated_p Q,
      from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_valid)).left,
      from ih h1 a_3,

      have h1: σ' ⊨ prop.instantiated_p Q,
      from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_valid)).left,
      have h2, from option.some_iff_not_none.mpr a_2,
      have h4, from option.is_some_iff_exists.mp h2,
      have h5, from env.contains_apply_equiv.right.mp h4,
      from ih h1 h5
    },

    case env.vcgen.func f σ₂ σ₁ g gx R S e H Q₁ Q₂ Q₃ _ _ _ _ _ _ _ fv_R fv_S e_verified _ ih₁ ih₂ {
      by_cases (f = x ∧ option.is_none (env.apply σ₁ x)) with h,

      have h0, from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_valid)).right,
      have h1: σ' ⊨ prop.instantiated_p (f ≡ value.func g gx R S e H σ₂),
      from (valid_env.and.elim (valid_env.instantiated_p_and_elim h0)).left,
      have h2: (σ' f = value.func g gx R S e H σ₂), from valid_env.subst_of_eq_instantiated h1,
      change (env.apply (σ₁[f↦value.func g gx R S e H σ₂]) x = σ' x),
      unfold env.apply,
      simp[h],
      rw[←h.left],
      from h2.symm,

      change (env.apply (σ₁[f↦value.func g gx R S e H σ₂]) x = σ' x),
      unfold env.apply,
      simp[h],

      cases not_and_distrib.mp h,
      cases env.contains.inv x_in_σ,
      have : (f ≠ x), from a_7,
      have : (x ≠ f), from this.symm,
      contradiction,
      
      have h1: σ' ⊨ prop.instantiated_p Q₁,
      from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_valid)).left,
      from ih₁ h1 a_8,

      have h1: σ' ⊨ prop.instantiated_p Q₁,
      from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_valid)).left,
      have h2, from option.some_iff_not_none.mpr a_7,
      have h4, from option.is_some_iff_exists.mp h2,
      have h5, from env.contains_apply_equiv.right.mp h4,
      from ih₁ h1 h5
    }
  end

lemma env_dominates_rest {P: prop} {σ: env} {x: var} {v: value}:
      (⊢ (σ[x↦v]) : P) → (∃Q, (⊢ σ : Q) ∧ ∀σ', dominates σ' P Q) :=
  assume σ_verified: ⊢ (σ[x↦v]) : P,
  begin
    cases σ_verified,
    case env.vcgen.tru Q _ σ_verified ih { from
      have ∀σ', dominates σ' (prop.and Q (x ≡ value.true)) Q,
      from λσ', dominates.of_and_left,
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ ∀σ', dominates σ' (prop.and Q (x ≡ value.true)) Q_1,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.fls Q _ σ_verified { from
      have ∀σ', dominates σ' (prop.and Q (x ≡ value.false)) Q,
      from λσ', dominates.of_and_left,
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ ∀σ', dominates σ' (prop.and Q (x ≡ value.false)) Q_1,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.num n Q _ σ_verified { from
      have ∀σ', dominates σ' (prop.and Q (x ≡ value.num n)) Q,
      from λσ', dominates.of_and_left,
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ ∀σ', dominates σ' (prop.and Q (x ≡ value.num n)) Q_1,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.func σ₂ f fx R S H e Q Q₂ Q₃ x_not_in_σ f_not_in_σ₂
         fx_not_in_σ₂ f_neq_fx σ₁_verified σ₂_verified fx_in_R fv_R fv_S e_verified func_vc { from
      let funcp := prop.subst_env (σ₂[f↦value.func f fx R S e H σ₂])
                                  (prop.func f fx R (Q₃ (term.app f fx) ⋀ S)) in
      have ∀σ', dominates σ' (Q ⋀ x ≡ value.func f fx R S e H σ₂ ⋀ funcp) Q,
      from λσ', dominates.of_and_left,
      show ∃Q_1, (⊢ σ : Q_1) ∧ ∀σ', dominates σ' (prop.and Q ((x ≡ (value.func f fx R S e H σ₂)) ⋀ funcp)) Q_1,
      from exists.intro Q ⟨σ₁_verified, this⟩
    }
  end

lemma strengthen_and_with_dominating_instantiations {σ: env} {P P' Q: prop}:
  dominates σ P P' → (σ ⊨ (P ⋀ Q).instantiated_p) → σ ⊨ (P' ⋀ Q).instantiated_p :=
  assume h1: dominates σ P P',
  assume h2: (σ ⊨ (P ⋀ Q).instantiated_p),
  have dominates σ (P ⋀ Q) (P' ⋀ Q), from dominates.same_right (λ_, h1),
  dominates.elim this h2

lemma strengthen_impl_with_dominating_instantiations {σ: env} {P P' Q: prop}:
  dominates σ P' P → FV P' ⊆ FV P → (σ ⊨ (prop.implies P Q).instantiated_n) → (σ ⊨ (prop.implies P' Q).instantiated_n) :=
  assume P'_dominates_P: dominates σ P' P,
  assume fv_P'_P: FV P' ⊆ FV P,
  assume h0: σ ⊨ (P.not ⋁ Q).instantiated_n,
  have h11: closed_subst σ (P'.not ⋁ Q).not.instantiated_p, from (
    assume x: var,
    assume h12: x ∈ FV (P'.not ⋁ Q).not.instantiated_p,
    have (P'.not ⋁ Q).not.instantiated_p = (P'.not ⋁ Q).instantiated_n.not, from not_dist_instantiated_p,
    have x ∈ FV (P'.not ⋁ Q).instantiated_n.not, from this ▸ h12,
    have h13: x ∈ FV (P'.not ⋁ Q).instantiated_n, from free_in_vc.not.inv this,
    have FV P'.not ⊆ FV P.not, from (
      assume y: var,
      assume : y ∈ FV P'.not,
      have y ∈ FV P', from free_in_prop.not.inv this,
      have y ∈ FV P, from set.mem_of_subset_of_mem fv_P'_P this,
      show y ∈ FV P.not, from free_in_prop.not this
    ),
    have FV (P'.not ⋁ Q).instantiated_n ⊆ FV (P.not ⋁ Q).instantiated_n,
    from free_in_prop.strengthen_or_with_instantiations this,
    have x ∈ FV (P.not ⋁ Q).instantiated_n, from set.mem_of_subset_of_mem this h13,
    show x ∈ σ.dom,
    from set.mem_of_subset_of_mem (valid_env.closed h0) this
  ),
  have h12: σ ⊨ (P.not ⋁ Q).instantiated_n.not.not, from valid_env.not_not.mpr h0,
  have (P.not ⋁ Q).not.instantiated_p = (P.not ⋁ Q).instantiated_n.not, from not_dist_instantiated_p,
  have σ ⊨ (P.not ⋁ Q).not.instantiated_p.not, from this.symm ▸ h12,
  have h2: ¬ σ ⊨ (P.not ⋁ Q).not.instantiated_p, from valid_env.not.mpr this,
  have h3: (σ ⊨ (P'.not ⋁ Q).not.instantiated_p) → (σ ⊨ (P.not ⋁ Q).not.instantiated_p), from (
    assume : σ ⊨ (P'.not ⋁ Q).not.instantiated_p,
    have h4: σ ⊨ (P'.not.not ⋀ Q.not).instantiated_p, from valid_env.or_not_dist_with_instantiations.mp this,
    have h41: σ ⊨ P'.not.not.instantiated_p, from (valid_env.and.elim (valid_env.instantiated_p_and_elim h4)).left,
    have h42: P'.not.not.instantiated_p = P'.not.instantiated_n.not, from not_dist_instantiated_p,
    have h43: P'.not.instantiated_n = P'.instantiated_p.not, from not_dist_instantiated_n,
    have σ ⊨ P'.instantiated_p.not.not, from h43 ▸ h42 ▸ h41,
    have σ ⊨ P'.instantiated_p, from valid_env.not_not.mp this,
    have dominates σ P'.not.not P', from dominates.not_not,
    have h5: σ ⊨ (P' ⋀ Q.not).instantiated_p,
    from strengthen_and_with_dominating_instantiations this h4,
    have h6: σ ⊨ (P ⋀ Q.not).instantiated_p,
    from strengthen_and_with_dominating_instantiations P'_dominates_P h5,
    have dominates σ P P.not.not, from dominates.of_not_not,
    have σ ⊨ (P.not.not ⋀ Q.not).instantiated_p,
    from strengthen_and_with_dominating_instantiations this h6,
    show σ ⊨ (P.not ⋁ Q).not.instantiated_p, from valid_env.or_not_dist_with_instantiations.mpr this
  ),
  have ¬ σ ⊨ (P'.not ⋁ Q).not.instantiated_p, from mt h3 h2,
  have h9: σ ⊨ (P'.not ⋁ Q).not.instantiated_p.not, from valid_env.not.mp h11 this,
  have (P'.not ⋁ Q).not.instantiated_p = (P'.not ⋁ Q).instantiated_n.not, from not_dist_instantiated_p,
  have σ ⊨ (P'.not ⋁ Q).instantiated_n.not.not, from this ▸ h9,
  show σ ⊨ (P'.not ⋁ Q).instantiated_n, from valid_env.not_not.mp this

lemma strengthen_vc {P P' Q S: prop} {σ: env}:
  dominates σ P' P → FV P' ⊆ FV P →
  (σ ⊨ (prop.implies (P ⋀ Q) S).instantiated_n) → σ ⊨ (prop.implies (P' ⋀ Q) S).instantiated_n :=
  assume : dominates σ P' P,
  assume fv_P'_P: FV P' ⊆ FV P,
  have h1: dominates σ (P' ⋀ Q) (P ⋀ Q), from dominates.same_right (λ_, this),
  have h2: FV (P' ⋀ Q) ⊆ FV (P ⋀ Q), from (
    assume x: var,
    assume : x ∈ FV (P' ⋀ Q),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P',
      have x ∈ FV P, from set.mem_of_subset_of_mem fv_P'_P this,
      show x ∈ FV (P ⋀ Q), from free_in_prop.and₁ this
    ) (
      assume : x ∈ FV Q,
      show x ∈ FV (P ⋀ Q), from free_in_prop.and₂ this
    )
  ),
  strengthen_impl_with_dominating_instantiations h1 h2

lemma strengthen_exp {P: prop} {Q: propctx} {e: exp}:
      (P ⊢ e : Q) → ∀P': prop, (FV P' = FV P) → (∀σ, dominates σ P' P) → (P' ⊢ e: Q) :=
  assume e_verified: (P ⊢ e : Q),
  begin
    induction e_verified,
    case exp.vcgen.tru x P e' Q x_not_free_in_P e'_verified ih { from (
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_P: (∀σ, dominates σ P' P),

      have h1: FV (P' ⋀ x ≡ value.true) = FV (P ⋀ x ≡ value.true),
      from same_free_and_left free_P'_P,
      have h2: (∀σ, dominates σ (P' ⋀ x ≡ value.true) (P ⋀ x ≡ value.true)),
      from λσ, dominates.same_right (λ_, P'_dominates_P σ),
      have e'_verified': P' ⋀ x ≡ value.true ⊢ e': Q, from ih (P' ⋀ x ≡ value.true) h1 h2,
      have x_not_free_in_P': x ∉ FV P', from free_P'_P.symm ▸ x_not_free_in_P,
      show P' ⊢ lett x = true in e' : propctx.exis x (x ≡ value.true ⋀ Q),
      from exp.vcgen.tru x_not_free_in_P' e'_verified'
    )},
    case exp.vcgen.fals x P e' Q x_not_free_in_P e'_verified ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_P: (∀σ, dominates σ P' P),

      have h1: FV (P' ⋀ (x ≡ value.false)) = FV (P ⋀ x ≡ value.false),
      from same_free_and_left free_P'_P,
      have h2: (∀σ, dominates σ (P' ⋀ x ≡ value.false) (P ⋀ x ≡ value.false)),
      from λσ, dominates.same_right (λ_, P'_dominates_P σ),
      have e'_verified': P' ⋀ x ≡ value.false ⊢ e': Q, from ih (P' ⋀ x ≡ value.false) h1 h2,
      have x_not_free_in_P': x ∉ FV P', from free_P'_P.symm ▸ x_not_free_in_P,
      show P' ⊢ letf x = false in e' : propctx.exis x ((x ≡ value.false) ⋀ Q),
      from exp.vcgen.fals x_not_free_in_P' e'_verified'
    },
    case exp.vcgen.num x n P e' Q x_not_free_in_P e'_verified ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_P: (∀σ, dominates σ P' P),

      have h1: FV (P' ⋀ x ≡ value.num n) = FV (P ⋀ x ≡ value.num n),
      from same_free_and_left free_P'_P,
      have h2: (∀σ, dominates σ (P' ⋀ x ≡ value.num n) (P ⋀ x ≡ value.num n)),
      from λσ, dominates.same_right (λ_, P'_dominates_P σ),
      have e'_verified': P' ⋀ (x ≡ value.num n) ⊢ e': Q, from ih (P' ⋀ (x ≡ value.num n)) h1 h2,
      have x_not_free_in_P': x ∉ FV P', from free_P'_P.symm ▸ x_not_free_in_P,
      show P' ⊢ letn x = n in e' : propctx.exis x ((x ≡ value.num n) ⋀ Q),
      from exp.vcgen.num x_not_free_in_P' e'_verified'
    },
    case exp.vcgen.func f x R S e₁ e₂ P Q₁ Q₂ f_not_free_in_P x_not_free_in_P f_neq_x x_free_in_R fv_R fv_S
                        e₁_verified e₂_verified func_vc ih₁ ih₂ { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_P: (∀σ, dominates σ P' P),

      have f_not_free_in_P': f ∉ FV P', from free_P'_P.symm ▸ f_not_free_in_P,
      have x_not_free_in_P': x ∉ FV P', from free_P'_P.symm ▸ x_not_free_in_P,
      have fv_R': FV R.to_prop ⊆ FV P' ∪ { f, x }, from free_P'_P.symm ▸ fv_R,
      have fv_S': FV S.to_prop ⊆ FV P' ∪ { f, x }, from free_P'_P.symm ▸ fv_S,

      have h1: FV (P' ⋀ ((spec.func f x R S) ⋀ R)) = FV (P ⋀ ((spec.func f x R S) ⋀ R)),
      from same_free_and_left free_P'_P,
      have h2: (∀σ, dominates σ (P' ⋀ (spec.func f x R S) ⋀ R) (P ⋀ (spec.func f x R S) ⋀ R)),
      from λσ, dominates.same_right (λ_, P'_dominates_P σ),
      have e₁_verified': P' ⋀ (spec.func f x R S) ⋀ R ⊢ e₁ : Q₁,
      from ih₁ (P' ⋀ (spec.func f x R S) ⋀ R) h1 h2,

      have h3: FV (P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)))
             = FV (P ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S))),
      from same_free_and_left free_P'_P,

      have h5: (∀σ, dominates σ (P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)))
                      (P ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)))),
      from (λσ, dominates.same_right (λ_, P'_dominates_P σ)),

      have e₂_verified': P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)) ⊢ e₂ : Q₂,
      from ih₂ (P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S))) h3 h5,

      have func_vc': ∀ (σ : env),
             σ ⊨ prop.instantiated_n (prop.implies (P' ⋀ ↑(spec.func ↑f x R S) ⋀ R ⋀ Q₁ (term.app ↑f ↑x)) ↑S),
      from (λσ, strengthen_vc (P'_dominates_P σ) (set.subset_of_eq free_P'_P) (func_vc σ)),

      show P' ⊢ letf f[x] req R ens S {e₁} in e₂ : propctx.exis f (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S) ⋀ Q₂),
      from exp.vcgen.func f_not_free_in_P' x_not_free_in_P' f_neq_x x_free_in_R fv_R' fv_S' e₁_verified'
           e₂_verified' func_vc'
    },
    case exp.vcgen.unop op x y P e' Q' x_free_in_P y_not_free_in_P e'_verified vc_valid ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_P: (∀σ, dominates σ P' P),

      have x_free_in_P': x ∈ FV P', from free_P'_P.symm ▸ x_free_in_P,
      have y_not_free_in_P': y ∉ FV P', from free_P'_P.symm ▸ y_not_free_in_P,

      have h1: FV (P' ⋀ y ≡ term.unop op x) = FV (P ⋀ y ≡ term.unop op x),
      from same_free_and_left free_P'_P,
      have h2: (∀σ, dominates σ (P' ⋀ y ≡ term.unop op x) (P ⋀ y ≡ term.unop op x)),
      from (λσ, dominates.same_right (λ_, P'_dominates_P σ)),
      have e'_verified': P' ⋀ y ≡ term.unop op x ⊢ e' : Q',
      from ih (P' ⋀ y ≡ term.unop op x) h1 h2,

      have FV P' ⊆ FV P, from set.subset_of_eq free_P'_P,
      have vc_valid': ∀ (σ : env), σ ⊨ prop.instantiated_n (prop.implies P' (prop.pre₁ op x)),
      from (λσ, strengthen_impl_with_dominating_instantiations (P'_dominates_P σ) this (vc_valid σ)),

      show P' ⊢ letop y = op [x] in e' : propctx.exis y (y ≡ term.unop op x ⋀ Q'),
      from exp.vcgen.unop x_free_in_P' y_not_free_in_P' e'_verified' vc_valid'
    },
    case exp.vcgen.binop op x y z e' P Q' x_free_in_P y_free_in_P z_not_free_in_P e'_verified vc_valid ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_P: (∀σ, dominates σ P' P),

      have x_free_in_P': x ∈ FV P', from free_P'_P.symm ▸ x_free_in_P,
      have y_free_in_P': y ∈ FV P', from free_P'_P.symm ▸ y_free_in_P,
      have z_not_free_in_P': z ∉ FV P', from free_P'_P.symm ▸ z_not_free_in_P,

      have h1: FV (P' ⋀ z ≡ term.binop op x y) = FV (P ⋀ z ≡ term.binop op x y),
      from same_free_and_left free_P'_P,
      have h2: (∀σ, dominates σ (P' ⋀ z ≡ term.binop op x y) (P ⋀ z ≡ term.binop op x y)),
      from (λσ, dominates.same_right (λ_, P'_dominates_P σ)),
      have e'_verified': P' ⋀ z ≡ term.binop op x y ⊢ e' : Q',
      from ih (P' ⋀ z ≡ term.binop op x y) h1 h2,

      have FV P' ⊆ FV P, from set.subset_of_eq free_P'_P,
      have vc_valid': ∀ (σ : env), σ ⊨ prop.instantiated_n (prop.implies P' (prop.pre₂ op x y)),
      from (λσ, strengthen_impl_with_dominating_instantiations (P'_dominates_P σ) this (vc_valid σ)),

      show P' ⊢ letop2 z = op [x, y] in e' : propctx.exis z (z ≡ term.binop op x y ⋀ Q'),
      from exp.vcgen.binop x_free_in_P' y_free_in_P' z_not_free_in_P' e'_verified' vc_valid'
    },
    case exp.vcgen.app y f x e' P Q' f_free_in_P x_free_in_P y_not_free_in_P e'_verified vc_valid ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_P: (∀σ, dominates σ P' P),

      have f_free_in_P': f ∈ FV P', from free_P'_P.symm ▸ f_free_in_P,
      have x_free_in_P': x ∈ FV P', from free_P'_P.symm ▸ x_free_in_P,
      have y_not_free_in_P': y ∉ FV P', from free_P'_P.symm ▸ y_not_free_in_P,

      have h1: FV (P' ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
             = FV (P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
      from same_free_and_left free_P'_P,

      have h2: (∀σ, dominates σ (P' ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                                (P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)),
      from (λσ, dominates.same_right (λ_, P'_dominates_P σ)),

      have e'_verified': P' ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⊢ e' : Q',
      from ih (P' ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) h1 h2,

      have vc_valid': ∀ (σ : env),
             σ ⊨ prop.instantiated_n (prop.implies (P' ⋀ prop.call f x) (term.unop unop.isFunc f ⋀ prop.pre f x)),
      from (λσ, strengthen_vc (P'_dominates_P σ) (set.subset_of_eq free_P'_P) (vc_valid σ)),

      show P' ⊢ letapp y = f [x] in e' : propctx.exis y (prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⋀ Q'),
      from exp.vcgen.app f_free_in_P' x_free_in_P' y_not_free_in_P' e'_verified' vc_valid'
    },
    case exp.vcgen.ite x e₂ e₁ P Q₁ Q₂ x_free_in_P e₁_verified e₂_verified vc_valid ih₁ ih₂ { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_P: (∀σ, dominates σ P' P),

      have x_free_in_P': x ∈ FV P', from free_P'_P.symm ▸ x_free_in_P,

      have h1: FV (P' ⋀ x) = FV (P ⋀ x), from same_free_and_left free_P'_P,
      have h2: (∀σ, dominates σ (P' ⋀ x) (P ⋀ x)), from (λσ, dominates.same_right (λ_, P'_dominates_P σ)),
      have e₁_verified': P' ⋀ x ⊢ e₁ : Q₁, from ih₁ (P' ⋀ x) h1 h2,

      have h1: FV (P' ⋀ term.unop unop.not x) = FV (P ⋀ term.unop unop.not x), from same_free_and_left free_P'_P,
      have h2: (∀σ, dominates σ (P' ⋀ term.unop unop.not x) (P ⋀ term.unop unop.not x)),
      from (λσ, dominates.same_right (λ_, P'_dominates_P σ)),
      have e₂_verified': P' ⋀ term.unop unop.not x ⊢ e₂ : Q₂, from ih₂ (P' ⋀ term.unop unop.not x) h1 h2,

      have FV P' ⊆ FV P, from set.subset_of_eq free_P'_P,
      have vc_valid': ∀ (σ : env),
             σ ⊨ prop.instantiated_n (prop.implies P' (term.unop unop.isBool x)),
      from (λσ, strengthen_impl_with_dominating_instantiations (P'_dominates_P σ) this (vc_valid σ)),

      show P' ⊢ exp.ite x e₁ e₂ : propctx.implies x Q₁ ⋀ propctx.implies (term.unop unop.not x) Q₂,
      from exp.vcgen.ite x_free_in_P' e₁_verified' e₂_verified' vc_valid'
    },
    case exp.vcgen.return x P x_free_in_P { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_P: (∀σ, dominates σ P' P),

      have x_free_in_P': x ∈ FV P', from free_P'_P.symm ▸ x_free_in_P,

      show P' ⊢ exp.return x : (x ≣ •), from exp.vcgen.return x_free_in_P'
    }
  end

lemma exp.preservation {R: spec} {H: history} {σ σ': env} {P: prop} {e e': exp} {Q: propctx}:
      (⊢ σ : P) → FV (spec.to_prop R) ⊆ FV P → (σ ⊨ R.to_prop.instantiated_n) → (R ⋀ H ⋀ P ⊢ e : Q) →
      ((R, H, σ, e) ⟶ (R, H, σ', e')) → ⊢ₛ (R, H, σ', e') :=
  sorry

lemma inlined_dominates_spec {σ σ₁: env} {P: prop} {Q: propctx} {f x: var} {R S: spec} {e: exp} {H: history}:
  (⊢ σ₁ : P) → (f ∉ σ₁) → (x ∉ σ₁) → (x ≠ f) → (σ ⊨ P.instantiated_p) → (σ f = value.func f x R S e H σ₁) →
  (⊢ (σ₁[f↦value.func f x R S e H σ₁]) : (P ⋀ f ≡ value.func f x R S e H σ₁ ⋀
                  prop.subst_env (σ₁[f↦value.func f x R S e H σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)))) →
  dominates σ (prop.subst_env (σ₁[f↦value.func f x R S e H σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)))
              (spec.func f x R S) :=
  
  let vf := value.func f x R S e H σ₁ in
  let forallp' := (prop.implies R.to_prop (prop.pre f x) ⋀
                   prop.implies (prop.post f x) (Q (term.app f x) ⋀ S.to_prop)) in

  let forallp := (prop.implies R.to_prop (prop.pre f x) ⋀ prop.implies (prop.post f x) S.to_prop) in

  let P' := P ⋀ f ≡ value.func f x R S e H σ₁ ⋀
            prop.subst_env (σ₁[f↦vf]) (prop.func f x R (Q (term.app f x) ⋀ S)) in

  assume σ₁_verified: ⊢ σ₁ : P,
  assume f_not_in_σ₁: f ∉ σ₁,
  assume x_not_in_σ₁: x ∉ σ₁,
  assume x_neq_f: x ≠ f,
  assume P_valid: σ ⊨ P.instantiated_p,
  assume f_is_vf: σ f = value.func f x R S e H σ₁,
  assume σ₁f_verified: ⊢ (σ₁[f↦vf]) : P',

  have (∀y, y ∈ σ₁ → (σ₁ y = σ y)),
  from env_equiv_of_translation_valid σ₁_verified σ P_valid,

  have env_equiv: (∀y, y ∈ (σ₁[f↦vf]) → ((σ₁[f↦vf]) y = σ y)),
  from env.equiv_of_rest_and_same this f_not_in_σ₁ f_is_vf,

  have h1: (σ₁[f↦vf]) f = σ f, from env_equiv f (env.contains.same),
  have σ f = vf, from eq.trans h1.symm (env.apply_of_contains f_not_in_σ₁),
  have h2: term.subst_env σ f = vf, from (term.subst_env.var.right vf).mp this,

  have h3: (prop.subst_env (σ₁[f↦vf]) (prop.func f x R (Q (term.app f x) ⋀ S)))
         = (term.unop unop.isFunc vf ⋀ prop.forallc x vf (prop.subst_env (σ₁[f↦vf]) forallp')), from (

    have h3: prop.func f x R (Q (term.app f x) ⋀ S) = (term.unop unop.isFunc f ⋀ prop.forallc x f forallp'),
    from rfl,
    have h4: prop.subst_env (σ₁[f↦vf]) (term.unop unop.isFunc f ⋀ prop.forallc x f forallp')
      = (prop.subst_env (σ₁[f↦vf]) (term.unop unop.isFunc f) ⋀ prop.subst_env (σ₁[f↦vf]) (prop.forallc x f forallp')),
    from prop.subst_env.and,
    have h5: prop.subst_env (σ₁[f↦vf]) (term.unop unop.isFunc f) =
            term.subst_env (σ₁[f↦vf]) (term.unop unop.isFunc f),
    from prop.subst_env.term,
    have h6: term.subst_env (σ₁[f↦vf]) (term.unop unop.isFunc f) =
            term.unop unop.isFunc (term.subst_env (σ₁[f↦vf]) f),
    from term.subst_env.unop,
    have h7: term.subst_env (σ₁[f↦vf]) f = vf, from (term.subst_env.var.right vf).mp (env.apply_of_contains f_not_in_σ₁),

    have ¬ (x = f ∨ x ∈ σ₁), from not_or_distrib.mpr ⟨x_neq_f, x_not_in_σ₁⟩,
    have x ∉ (σ₁[f↦vf]), from mt env.contains.inv this,
    have h8: prop.subst_env (σ₁[f↦vf]) (prop.forallc x f forallp')
          = prop.forallc x (term.subst_env (σ₁[f↦vf]) f) (prop.subst_env (σ₁[f↦vf]) forallp'),
    from prop.subst_env.forallc this,

    show (prop.subst_env (σ₁[f↦vf]) (prop.func f x R (Q (term.app f x) ⋀ S)))
          = (term.unop unop.isFunc vf ⋀ prop.forallc x vf (prop.subst_env (σ₁[f↦vf]) forallp')),
    from h7 ▸ h8 ▸ h7 ▸ h6 ▸ h5 ▸ h3.symm ▸ h4
  ),

  have h4: spec.to_prop (spec.func f x R S) = (term.unop unop.isFunc f ⋀ prop.forallc x f forallp),
  by unfold spec.to_prop,

  have h5: dominates σ (term.unop unop.isFunc vf) (term.unop unop.isFunc f),
  from dominates.no_quantifiers (
    assume : σ ⊨ prop.instantiated_p (term.unop unop.isFunc vf),
    have unop.apply unop.isFunc vf = value.true, by unfold unop.apply,
    have ⊨ term.unop unop.isFunc vf ≡ value.true, from valid.unop.mp this,
    have ⊨ term.unop unop.isFunc vf, from valid.eq.true.mpr this,
    have h72: ⊨ term.unop unop.isFunc (term.subst_env σ f), from h2.symm ▸ this,
    have term.subst_env σ (term.unop unop.isFunc f) = term.unop unop.isFunc (term.subst_env σ f),
    from term.subst_env.unop,
    have ⊨ term.subst_env σ (term.unop unop.isFunc f), from this.symm ▸ h72,
    have h73: ⊨ vc.term (term.subst_env σ (term.unop unop.isFunc f)), from this,
    have vc.subst_env σ (term.unop unop.isFunc f) = vc.term (term.subst_env σ (term.unop unop.isFunc f)),
    from vc.subst_env.term,
    have ⊨ vc.subst_env σ (term.unop unop.isFunc f), from this.symm ▸ h73,
    have h74: σ ⊨ term.unop unop.isFunc f, from this,
    have prop.erased_p (prop.term (term.unop unop.isFunc f)) = vc.term (term.unop unop.isFunc f),
    by unfold prop.erased_p,
    have h8: σ ⊨ (prop.term (term.unop unop.isFunc f)).erased_p, from this.symm ▸ h74,
    have calls_p (prop.term (term.unop unop.isFunc f)) = ∅, from set.eq_empty_of_forall_not_mem (
      assume c': calltrigger,
      assume : c' ∈ calls_p (term.unop unop.isFunc f),
      show «false», from prop.has_call_p.term.inv this
    ),
    have (prop.term (term.unop unop.isFunc f)).instantiated_p = (prop.term (term.unop unop.isFunc f)).erased_p,
    from instantiated_p_eq_erased_p_without_calls this,
    show σ ⊨ (prop.term (term.unop unop.isFunc f)).instantiated_p, from this.symm ▸ h8
  ) (
    show calls_p_subst σ (term.unop unop.isFunc f) ⊆ calls_p_subst σ (term.unop unop.isFunc vf), from (
      assume c: calltrigger,
      assume : c ∈ calls_p_subst σ (term.unop unop.isFunc f),
      @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_p (term.unop unop.isFunc f))
          (λa, a ∈ calls_p_subst σ (term.unop unop.isFunc vf)) c this (
        assume c': calltrigger,
        assume : c' ∈ calls_p (term.unop unop.isFunc f),
        show calltrigger.subst σ c' ∈ calls_p_subst σ (term.unop unop.isFunc vf),
        from absurd this prop.has_call_p.term.inv
      )
    )
  ) (
    show quantifiers_p (term.unop unop.isFunc f) = ∅, from set.eq_empty_of_forall_not_mem (
      assume q: callquantifier,
      assume : q ∈ quantifiers_p (term.unop unop.isFunc f),
      show «false», from prop.has_quantifier_p.term.inv this
    )
  ),

  have h6: dominates σ (prop.forallc x vf (prop.subst_env (σ₁[f↦vf]) forallp')) (prop.forallc x f forallp),
  from dominates.quantifier (
    assume : σ ⊨ vf ≡ f,
    assume v: value,

    have ¬ (x = f ∨ x ∈ σ₁), from not_or_distrib.mpr ⟨x_neq_f, x_not_in_σ₁⟩,
    have x ∉ (σ₁[f↦vf]), from mt env.contains.inv this,
    have (∀y, y ∈ (σ₁[f↦vf]) → ((σ₁[f↦vf]) y = (σ[x↦v]) y)),
    from env.equiv_of_not_contains env_equiv this,
    have h7: dominates (σ[x↦v]) (prop.subst_env (σ₁[f↦vf]) forallp') forallp',
    from dominates_equiv_subst this,
    have h82: dominates (σ[x↦v]) (prop.implies (prop.post f x) (Q (term.app f x) ⋀ S.to_prop))
                                 (prop.implies (prop.post f x) S.to_prop),
    from dominates.or_intro dominates.self dominates.of_and_right,
    have h8: dominates (σ[x↦v]) forallp' forallp,
    from dominates.same_left (λ_, h82),
    show dominates (σ[x↦v]) (prop.subst_env (σ₁[f↦vf]) forallp') forallp,
    from dominates.trans h7 h8
  ),
  have h7: dominates σ (term.unop unop.isFunc vf ⋀ prop.forallc x vf (prop.subst_env (σ₁[f↦vf]) forallp'))
                       (term.unop unop.isFunc f ⋀ prop.forallc x f forallp),
  from dominates.and_intro h5 (λ_, h6),
  show dominates σ (prop.subst_env (σ₁[f↦value.func f x R S e H σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)))
                   (spec.to_prop (spec.func f x R S)),
  from h3.symm ▸ h4.symm ▸ h7

theorem preservation {s: stack} : (⊢ₛ s) → (∀s', (s ⟶ s') → (⊢ₛ s')) :=
  assume s_verified:  ⊢ₛ s,
  begin
    induction s_verified,
    case stack.vcgen.top σ e P Q H R σ_verified fv_R R_valid e_verified {
      assume s',
      assume s_steps: ((R, H, σ, e) ⟶ s'),

      have R_closed: closed_subst σ R.to_prop, from (
        assume z: var,
        assume : z ∈ FV R.to_prop,
        have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
        show z ∈ σ.dom, from (free_iff_contains σ_verified).symm ▸ this
      ),

      cases s_steps,
      case step.tru x e { from
        show ⊢ₛ (R, H, σ[x↦value.true], e), from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case step.fals x e { from
        show ⊢ₛ (R, H, σ[x↦value.false], e), from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case step.num n e x { from
        show ⊢ₛ (R, H, σ[x↦value.num n], e), from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case step.closure R' S' f x e₁ e₂ { from
        show ⊢ₛ (R, H, σ[f↦value.func f x R' S' e₁ H σ], e₂),
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case step.unop op x y e { from
        show ⊢ₛ (R, H, σ[y↦v], e), from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case step.binop op x y z e { from
        show ⊢ₛ (R, H, σ[z↦v], e), from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case step.app f x y S₂ H₂ g σ₂ R₂ gx e₁ e₂ vₓ f_is_func x_is_vₓ {
        cases e_verified,
        case exp.vcgen.app Q f_free x_free y_not_free e₂_verified func_vc { from

          have h5: ⊢ₛ (R₂, H₂, σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂][gx↦vₓ], e₁), from (

            have ∃σ' Q', ⊢ (σ'[f ↦ value.func g gx R₂ S₂ e₁ H₂ σ₂]) : Q',
            from env.vcgen.inv σ_verified f_is_func,
            let ⟨σ', Q', ha1⟩ := this in

            have ∃Q₁ Q₂ Q₃,
              f ∉ σ' ∧
              g ∉ σ₂ ∧
              gx ∉ σ₂ ∧
              g ≠ gx ∧
              (⊢ σ' : Q₁) ∧
              (⊢ σ₂ : Q₂) ∧
              gx ∈ FV R₂.to_prop ∧
              FV R₂.to_prop ⊆ FV Q₂ ∪ { g, gx } ∧
              FV S₂.to_prop ⊆ FV Q₂ ∪ { g, gx } ∧
              (H₂ ⋀ Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂ ⊢ e₁ : Q₃) ∧
              ⟪prop.implies (H₂ ⋀ Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂ ⋀ Q₃ (term.app g gx)) S₂⟫ ∧
              (Q' = (Q₁ ⋀
                  ((f ≡ (value.func g gx R₂ S₂ e₁ H₂ σ₂)) ⋀
                  prop.subst_env (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂])
                  (prop.func g gx R₂ (Q₃ (term.app g gx) ⋀ S₂))))),
            from env.vcgen.func.inv ha1,

            let ⟨Q₁, Q₂, Q₃, ha2⟩ := this in
            let Q₂' := (Q₂ ⋀
                  ((g ≡ (value.func g gx R₂ S₂ e₁ H₂ σ₂)) ⋀
                  prop.subst_env (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂])
                  (prop.func g gx R₂ (Q₃ (term.app g gx) ⋀ S₂)))) in

            have ha3: ⊢ (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂]) : Q₂',
            from env.vcgen.func
                 ha2.right.left
                 ha2.right.left
                 ha2.right.right.left
                 ha2.right.right.right.left
                 ha2.right.right.right.right.right.left
                 ha2.right.right.right.right.right.left
                 ha2.right.right.right.right.right.right.left
                 ha2.right.right.right.right.right.right.right.left
                 ha2.right.right.right.right.right.right.right.right.left
                 ha2.right.right.right.right.right.right.right.right.right.left
                 ha2.right.right.right.right.right.right.right.right.right.right.left,

            have ∃σ'' Q'', ⊢ (σ''[x ↦ vₓ]) : Q'',
            from env.vcgen.inv σ_verified x_is_vₓ,
            let ⟨σ'', Q'', ha4⟩ := this in

            have gx ∉ (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂]), from (
              assume : gx ∈ (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂]),
              or.elim (env.contains.inv this) (
                assume : gx = g,
                show «false», from ha2.right.right.right.left this.symm
              ) (
                assume : gx ∈ σ₂,
                show «false», from ha2.right.right.left this
              )
            ),
            have ∃P₃, ⊢ (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂][gx↦vₓ]) : P₃,
            from env.vcgen.copy ha3 this ha4,
            let ⟨P₃, ha5⟩ := this in

            have ha6: H₂ ⋀ Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂ ⊢ e₁ : Q₃,
            from ha2.right.right.right.right.right.right.right.right.right.left,

            have ha7: FV R₂.to_prop ⊆ FV P₃, from (
              have hb1: FV P₃ = (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂][gx↦vₓ]).dom, from (free_iff_contains ha5).symm,
              have hb2: (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂][gx↦vₓ]).dom
                      = (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂]).dom ∪ set.insert gx ∅, from env.dom.inv,
              have hb3: (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂]).dom
                      = σ₂.dom ∪ set.insert g ∅, from env.dom.inv,
              have hb4: FV P₃ = σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅, from eq.trans hb1 (hb3 ▸ hb2),
              have hb5: FV P₃ = σ₂.dom ∪ {g, gx}, by {simp at hb4, rw[set.two_elems_of_insert] at hb4, from hb4},

              have hb6: FV Q₂ = σ₂.dom, from (free_iff_contains ha2.right.right.right.right.right.left).symm,

              have hb7: FV R₂.to_prop ⊆ σ₂.dom ∪ {g, gx}, from (
                assume x: var,
                assume : x ∈ FV R₂.to_prop,
                have x ∈ FV Q₂ ∪ {g, gx},
                from set.mem_of_mem_of_subset this ha2.right.right.right.right.right.right.right.left,
                show x ∈ σ₂.dom ∪ {g, gx}, from hb6 ▸ this
              ),
              show FV R₂.to_prop ⊆ FV P₃, from hb5.symm ▸ hb7
            ),

            have ha8: FV (↑R₂ ⋀ ↑H₂ ⋀ P₃) = FV (↑H₂ ⋀ Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from (
              have ha8: FV (P₃ ⋀ ↑R₂) = FV (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from (
                have hb1: FV P₃ = (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂][gx↦vₓ]).dom, from (free_iff_contains ha5).symm,
                have hb2: (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂][gx↦vₓ]).dom
                        = (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂]).dom ∪ set.insert gx ∅, from env.dom.inv,
                have hb3: (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂]).dom
                        = σ₂.dom ∪ set.insert g ∅, from env.dom.inv,
                have hb4: FV P₃ = σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅, from eq.trans hb1 (hb3 ▸ hb2),
                have hb8: FV (P₃ ⋀ R₂) = FV P₃ ∪ FV R₂.to_prop, from free_in_prop.and_elim,
                have FV P₃ ∪ FV R₂.to_prop = FV P₃, from set.union_eq_self_of_subset_right ha7,
                have hb9: FV (P₃ ⋀ R₂) = FV P₃, from eq.trans hb8 this,
                let forallp := (prop.implies R₂.to_prop (prop.pre g gx)
                              ⋀ prop.implies (prop.post g gx) S₂.to_prop) in
                have hb5: FV (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂) = σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅,
                from set.eq_of_subset_of_subset (
                  assume x: var,

                  have hb6: x ∈ FV Q₂ ∪ {g, gx} → x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅, from (
                    assume : x ∈ FV Q₂ ∪ {g, gx},
                    or.elim (set.mem_or_mem_of_mem_union this) (
                      assume hb2: x ∈ FV Q₂,
                      have FV Q₂ = σ₂.dom, from (free_iff_contains ha2.right.right.right.right.right.left).symm,
                      have x ∈ σ₂.dom, from this ▸ hb2,
                      have x ∈ σ₂.dom ∪ set.insert g ∅, from set.mem_union_left (set.insert g ∅) this,
                      show x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅,
                      from set.mem_union_left (set.insert gx ∅) this
                    ) (
                      assume : x ∈ {g, gx},
                      have (x = g) ∨ (x = gx), from set.two_elems_mem this,
                      or.elim this (
                        assume : x = g,
                        have x ∈ set.insert g ∅, from set.mem_singleton_of_eq this,
                        have x ∈ σ₂.dom ∪ set.insert g ∅, from set.mem_union_right σ₂.dom this,
                        show x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅,
                        from set.mem_union_left (set.insert gx ∅) this
                      ) (
                        assume : x = gx,
                        have x ∈ set.insert gx ∅, from set.mem_singleton_of_eq this,
                        show x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅,
                        from set.mem_union_right (σ₂.dom ∪ set.insert g ∅) this
                      )
                    )
                  ),

                  assume : x ∈ FV (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂),

                  or.elim (free_in_prop.and.inv this) (
                    assume hb2: x ∈ FV Q₂,
                    have FV Q₂ = σ₂.dom, from (free_iff_contains ha2.right.right.right.right.right.left).symm,
                    have x ∈ σ₂.dom, from this ▸ hb2,
                    have x ∈ σ₂.dom ∪ set.insert g ∅, from set.mem_union_left (set.insert g ∅) this,
                    show x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅,
                    from set.mem_union_left (set.insert gx ∅) this
                  ) (
                    assume : free_in_prop x (spec.func g gx R₂ S₂ ⋀ R₂),
                    or.elim (free_in_prop.and.inv this) (
                      assume h1: free_in_prop x (spec.func g gx R₂ S₂),
                      have spec.to_prop (spec.func g gx R₂ S₂) = (prop.func g gx R₂.to_prop S₂.to_prop),
                      by unfold spec.to_prop,
                      have free_in_prop x (prop.func g gx R₂.to_prop S₂.to_prop), from this ▸ h1,
                      or.elim (free_in_prop.and.inv this) (
                        assume : free_in_prop x (term.unop unop.isFunc g),
                        have free_in_term x (term.unop unop.isFunc g), from free_in_prop.term.inv this,
                        have free_in_term x g, from free_in_term.unop.inv this,
                        have x = g, from free_in_term.var.inv this,
                        have x ∈ set.insert g ∅, from set.mem_singleton_of_eq this,
                        have x ∈ σ₂.dom ∪ set.insert g ∅, from set.mem_union_right σ₂.dom this,
                        show x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅,
                        from set.mem_union_left (set.insert gx ∅) this
                      ) (
                        assume x_free_in_forallp: free_in_prop x (prop.forallc gx g forallp),
                        have free_in_term x g ∨ free_in_prop x forallp,
                        from (free_in_prop.forallc.inv x_free_in_forallp).right,
                        or.elim this (
                          assume : free_in_term x g,
                          have x = g, from free_in_term.var.inv this,
                          have x ∈ set.insert g ∅, from set.mem_singleton_of_eq this,
                          have x ∈ σ₂.dom ∪ set.insert g ∅, from set.mem_union_right σ₂.dom this,
                          show x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅,
                          from set.mem_union_left (set.insert gx ∅) this
                        ) (
                          assume : free_in_prop x forallp,
                          or.elim (free_in_prop.and.inv this) (
                            assume : free_in_prop x (prop.implies R₂.to_prop (prop.pre g gx)),
                            or.elim (free_in_prop.implies.inv this) (
                              assume : x ∈ FV R₂.to_prop,
                              have x ∈ FV Q₂ ∪ {g, gx},
                              from set.mem_of_mem_of_subset this ha2.right.right.right.right.right.right.right.left,
                              show x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅, from hb6 this
                            ) (
                              assume : free_in_prop x (prop.pre g gx),
                              have free_in_term x g ∨ free_in_term x gx, from free_in_prop.pre.inv this,
                              or.elim this (
                                assume : free_in_term x g,
                                have x = g, from free_in_term.var.inv this,
                                have x ∈ set.insert g ∅, from set.mem_singleton_of_eq this,
                                have x ∈ σ₂.dom ∪ set.insert g ∅, from set.mem_union_right σ₂.dom this,
                                show x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅,
                                from set.mem_union_left (set.insert gx ∅) this
                              ) (
                                assume : free_in_term x gx,
                                have x = gx, from free_in_term.var.inv this,
                                have x ∈ set.insert gx ∅, from set.mem_singleton_of_eq this,
                                show x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅,
                                from set.mem_union_right (σ₂.dom ∪ set.insert g ∅) this
                              )
                            )
                          ) (
                            assume : free_in_prop x (prop.implies (prop.post g gx) S₂.to_prop),
                            or.elim (free_in_prop.implies.inv this) (
                              assume : free_in_prop x (prop.post g gx),
                              have free_in_term x g ∨ free_in_term x gx, from free_in_prop.post.inv this,
                              or.elim this (
                                assume : free_in_term x g,
                                have x = g, from free_in_term.var.inv this,
                                have x ∈ set.insert g ∅, from set.mem_singleton_of_eq this,
                                have x ∈ σ₂.dom ∪ set.insert g ∅, from set.mem_union_right σ₂.dom this,
                                show x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅,
                                from set.mem_union_left (set.insert gx ∅) this
                              ) (
                                assume : free_in_term x gx,
                                have x = gx, from free_in_term.var.inv this,
                                have x ∈ set.insert gx ∅, from set.mem_singleton_of_eq this,
                                show x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅,
                                from set.mem_union_right (σ₂.dom ∪ set.insert g ∅) this
                              )
                            ) (
                              assume : free_in_prop x S₂.to_prop,
                              have x ∈ FV Q₂ ∪ {g, gx},
                              from set.mem_of_mem_of_subset this
                                   ha2.right.right.right.right.right.right.right.right.left,
                              show x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅, from hb6 this
                            )
                          )
                        )
                      ) 
                    ) (
                      assume : x ∈ FV R₂.to_prop,
                      have x ∈ FV Q₂ ∪ {g, gx},
                      from set.mem_of_mem_of_subset this ha2.right.right.right.right.right.right.right.left,
                      show x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅, from hb6 this
                    )
                  )
                ) (
                  assume x: var,
                  assume : x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅,
                  or.elim (set.mem_or_mem_of_mem_union this) (
                    assume : x ∈ σ₂.dom ∪ set.insert g ∅,
                    or.elim (set.mem_or_mem_of_mem_union this) (
                      assume hb2: x ∈ σ₂.dom,
                      have FV Q₂ = σ₂.dom, from (free_iff_contains ha2.right.right.right.right.right.left).symm,
                      have x ∈ FV Q₂, from this.symm ▸ hb2,
                      show x ∈ FV (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from free_in_prop.and₁ this
                    ) (
                      assume : x ∈ set.insert g ∅,
                      have x = g, from (set.mem_singleton_iff x g).mp this,
                      have free_in_term x g, from this ▸ free_in_term.var x,
                      have free_in_term x (term.unop unop.isFunc g), from free_in_term.unop this,
                      have free_in_prop x (term.unop unop.isFunc g), from free_in_prop.term this,
                      have h1: x ∈ FV (prop.func g gx R₂ S₂), from free_in_prop.and₁ this,
                      have spec.to_prop (spec.func g gx R₂ S₂) = (prop.func g gx R₂.to_prop S₂.to_prop),
                      by unfold spec.to_prop,
                      have free_in_prop x (spec.to_prop (spec.func g gx R₂ S₂)), from this.symm ▸ h1,
                      have free_in_prop x (spec.func g gx R₂ S₂), from this,
                      have free_in_prop x (spec.func g gx R₂ S₂ ⋀ R₂), from free_in_prop.and₁ this,
                      show x ∈ FV (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from free_in_prop.and₂ this
                    )
                  ) (
                    assume : x ∈ set.insert gx ∅,
                    have x = gx, from (set.mem_singleton_iff x gx).mp this,
                    have x ∈ FV R₂.to_prop,
                    from this.symm ▸ ha2.right.right.right.right.right.right.left,
                    have free_in_prop x (spec.func g gx R₂ S₂ ⋀ R₂), from free_in_prop.and₂ this,
                    show x ∈ FV (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from free_in_prop.and₂ this
                  )
                ),

                have FV P₃ = FV (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from eq.trans hb4 hb5.symm,
                show FV (P₃ ⋀ ↑R₂) = FV (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from eq.trans hb9 this
              ),
              show FV (↑R₂ ⋀ ↑H₂ ⋀ P₃) = FV (↑H₂ ⋀ Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), by calc
                   FV (↑R₂ ⋀ ↑H₂ ⋀ P₃) = FV ((↑H₂ ⋀ P₃) ⋀ ↑R₂) : free_in_prop.and_symm
                             ... = FV (↑H₂ ⋀ P₃ ⋀ ↑R₂) : free_in_prop.and_comm.symm
                             ... = FV ((P₃ ⋀ ↑R₂) ⋀ ↑H₂) : free_in_prop.and_symm
                             ... = FV ((Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂) ⋀ ↑H₂) : same_free_and_left ha8
                             ... = FV (↑H₂ ⋀ Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂) : free_in_prop.and_symm
            ),

            have ha9: σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂][gx↦vₓ] ⊨ prop.instantiated_n (spec.to_prop R₂),
            from (
              have env_has_f: f ∈ σ,
              from env.contains_apply_equiv.right.mp (exists.intro (value.func g gx R₂ S₂ e₁ H₂ σ₂) f_is_func),
              have env_has_x: x ∈ σ, from env.contains_apply_equiv.right.mp (exists.intro vₓ x_is_vₓ),

              have h1: no_instantiations (term.unop unop.isFunc f), from no_instantiations.term,
              have h2: no_instantiations (prop.pre f x), from no_instantiations.pre,
              have no_instantiations (↑(term.unop unop.isFunc f) ⋀ prop.pre f x), from no_instantiations.and h1 h2,
              have h3: σ ⊨ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased_n,
              from consequent_of_H_P_call σ_verified R_closed R_valid func_vc env_has_f env_has_x this,
              have (prop.and (prop.term (term.unop unop.isFunc f)) (prop.pre f x)).erased_n
                = ((prop.term (term.unop unop.isFunc f)).erased_n ⋀ (prop.pre f x).erased_n), by unfold prop.erased_n,
              have σ ⊨ ((prop.term (term.unop unop.isFunc f)).erased_n ⋀ (prop.pre f x).erased_n), from this ▸ h3,
              have h4: σ ⊨ (prop.pre f x).erased_n, from (valid_env.and.elim this).right,
              have (prop.pre f x).erased_n = vc.pre f x, by unfold prop.erased_n,
              have h5: σ ⊨ vc.pre f x, from this ▸ h4,
              have vc.subst_env σ (vc.pre f x) = vc.pre (term.subst_env σ f) (term.subst_env σ x),
              from vc.subst_env.pre,
              have h6: ⊨ vc.pre (term.subst_env σ f) (term.subst_env σ x), from this ▸ h5,
              have term.subst_env σ f = value.func g gx R₂ S₂ e₁ H₂ σ₂,
              from (term.subst_env.var.right (value.func g gx R₂ S₂ e₁ H₂ σ₂)).mp f_is_func,
              have h7: ⊨ vc.pre (value.func g gx R₂ S₂ e₁ H₂ σ₂) (term.subst_env σ x), from this ▸ h6,
              have term.subst_env σ x = vₓ, from (term.subst_env.var.right vₓ).mp x_is_vₓ,
              have ⊨ vc.pre (value.func g gx R₂ S₂ e₁ H₂ σ₂) vₓ, from this ▸ h7,
              show (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂][gx↦vₓ] ⊨ R₂.to_prop.instantiated_n),
              from valid.pre.mpr this
            ),

            have ∀σ, dominates σ (R₂ ⋀ H₂ ⋀ P₃) (H₂ ⋀ Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from (
              assume σ: env,

              have hb1: dominates σ (R₂ ⋀ H₂ ⋀ P₃) ((H₂ ⋀ P₃) ⋀ R₂),
              from dominates.and_symm,

              have hb2: dominates σ ((H₂ ⋀ P₃) ⋀ R₂) (H₂ ⋀ P₃ ⋀ R₂),
              from dominates.and_assoc.symm,

              have hb3: dominates σ (↑H₂ ⋀ P₃ ⋀ ↑R₂) ((P₃ ⋀ ↑R₂) ⋀ H₂),
              from dominates.and_symm,

              have hb4: dominates σ (P₃ ⋀ ↑R₂) (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from (

                have (∃Q, (⊢ (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂]) : Q) ∧ ∀σ', dominates σ' P₃ Q),
                from env_dominates_rest ha5,
                let ⟨Q₂'', ⟨hb1, hb2⟩⟩ := this in
                have Q₂' = Q₂'', from env.vcgen.inj ha3 Q₂'' hb1,
                have hb3: dominates σ P₃ Q₂', from this.symm ▸ hb2 σ,

                have dominates σ Q₂' (Q₂ ⋀ spec.func g gx R₂ S₂), from (
                  dominates.same_left (
                    assume Q₂_valid: σ ⊨ Q₂.instantiated_p,
                    dominates.pre_elim (
                      assume : σ ⊨ (prop.term (g ≡ value.func g gx R₂ S₂ e₁ H₂ σ₂)).instantiated_p,
                      have (σ g = value.func g gx R₂ S₂ e₁ H₂ σ₂), from valid_env.subst_of_eq_instantiated this,
                      inlined_dominates_spec ha2.right.right.right.right.right.left
                      ha2.right.left ha2.right.right.left ha2.right.right.right.left.symm Q₂_valid this ha3
                    )
                  )
                ),
                have dominates σ P₃ (Q₂ ⋀ spec.func g gx R₂ S₂),
                from dominates.trans hb3 this,

                have hb8: dominates σ (P₃ ⋀ ↑R₂) ((Q₂ ⋀ spec.func g gx R₂ S₂) ⋀ R₂),
                from dominates.same_right (λ_, this),

                have hb9: dominates σ ((Q₂ ⋀ spec.func g gx R₂ S₂) ⋀ R₂) (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂),
                from dominates.and_assoc.symm,

                show dominates σ (P₃ ⋀ ↑R₂) (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂),
                from dominates.trans hb8 hb9
              ),

              have hb5: dominates σ ((P₃ ⋀ ↑R₂) ⋀ H₂) ((Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂) ⋀ H₂),
              from dominates.same_right (λ_, hb4),

              have hb6: dominates σ ((Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂) ⋀ H₂) (↑H₂ ⋀ Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂),
              from dominates.and_symm,

              show dominates σ (R₂ ⋀ H₂ ⋀ P₃) (H₂ ⋀ Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂),
              from dominates.trans (dominates.trans (dominates.trans (dominates.trans hb1 hb2) hb3) hb5) hb6
            ),
            have R₂ ⋀ H₂ ⋀ P₃ ⊢ e₁ : Q₃,
            from strengthen_exp ha6 (R₂ ⋀ H₂ ⋀ P₃) ha8 this,

            show ⊢ₛ (R₂, H₂, σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂][gx↦vₓ], e₁),
            from stack.vcgen.top ha5 ha7 ha9 this
          ),

          have h6: y ∉ σ, from (
            have y ∉ FV P, from (
              assume : y ∈ FV P,
              have y ∈ FV (↑H ⋀ P), from free_in_prop.and₂ this,
              have y ∈ FV (R.to_prop ⋀ ↑H ⋀ P), from free_in_prop.and₂ this,
              show «false», from y_not_free this
            ),
            show y ∉ σ, from mt (free_of_contains σ_verified) this
          ),

          have h7: (R ⋀ H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⊢ e₂ : Q), from (
            have ha1: FV (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                   =  FV ((↑R ⋀ (↑H ⋀ P)) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x), from (

              have haa1: FV (↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                       = FV ((↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from free_in_prop.and_comm,

              have haa2: FV (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                       = FV ((↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑R),
              from free_in_prop.and_symm,

              have haa3: FV ((↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑R)
                       = FV (((↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑ R),
              from same_free_and_left haa1,

              have haa4: FV (((↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑R)
                       = FV (↑R ⋀ (↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from free_in_prop.and_symm,
              
              have haa5: FV (↑R ⋀ (↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                       = FV ((↑R ⋀ (↑H ⋀ P)) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from free_in_prop.and_comm,
              
              show FV (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                =  FV ((↑R ⋀ (↑H ⋀ P)) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from eq.trans (eq.trans (eq.trans haa2 haa3) haa4) haa5
            ),

            have ∀σ, dominates σ (R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                             ((↑R ⋀ (↑H ⋀ P)) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x), from (
              assume σ: env,

              have haa1: dominates σ (↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                               ((↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from dominates.and_assoc,

              have haa2: dominates σ (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                                     ((↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑R),
              from dominates.and_symm,

              have haa3: dominates σ ((↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑R)
                                     (((↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑ R),
              from dominates.same_right (λ_, haa1),

              have haa4: dominates σ (((↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑R)
                                     (↑R ⋀ (↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from dominates.and_symm,
              
              have haa5: dominates σ (↑R ⋀ (↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                                     ((↑R ⋀ (↑H ⋀ P)) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from dominates.and_assoc,
              
              show dominates σ (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                               ((↑R ⋀ (↑H ⋀ P)) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from dominates.trans (dominates.trans (dominates.trans haa2 haa3) haa4) haa5
            ),
            show (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⊢ e₂ : Q),
            from strengthen_exp e₂_verified (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ha1 this
          ),

          have h8: ⟪ prop.implies (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x) (↑(term.unop unop.isFunc f) ⋀ prop.pre f x) ⟫, from (
            assume σ: env,
            have ha1: dominates σ (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x) ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x), from dominates.shuffle,

            have ha2: FV (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x) ⊆ FV ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x), from (
              assume z: var,
              assume : z ∈ FV (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x),
              or.elim (free_in_prop.and.inv this) (
                assume : free_in_prop z R,
                have z ∈ FV (↑R ⋀ ↑H ⋀ P), from free_in_prop.and₁ this,
                show z ∈ FV ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x), from free_in_prop.and₁ this
              ) (
                assume : z ∈ FV (↑H ⋀ P ⋀ prop.call f x),
                or.elim (free_in_prop.and.inv this) (
                  assume : free_in_prop z H,
                  have z ∈ FV (↑H ⋀ P), from free_in_prop.and₁ this,
                  have z ∈ FV (↑R ⋀ ↑H ⋀ P), from free_in_prop.and₂ this,
                  show z ∈ FV ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x), from free_in_prop.and₁ this
                ) (
                  assume : free_in_prop z (P ⋀ prop.call f x),
                  or.elim (free_in_prop.and.inv this) (
                    assume : z ∈ FV P,
                    have z ∈ FV (↑H ⋀ P), from free_in_prop.and₂ this,
                    have z ∈ FV (↑R ⋀ ↑H ⋀ P), from free_in_prop.and₂ this,
                    show z ∈ FV ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x), from free_in_prop.and₁ this
                  ) (
                    assume : free_in_prop z (prop.call f x),
                    show z ∈ FV ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x), from free_in_prop.and₂ this
                  )
                )
              )
            ),

            have ha3: σ ⊨ (((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).not
                          ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated_n,
            from func_vc σ,

            show σ ⊨ (prop.implies (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x)
                                    (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated_n,
            from strengthen_impl_with_dominating_instantiations ha1 ha2 ha3
          ),

          have h9: (R₂, H₂, σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂][gx↦vₓ], e₁)
              ⟶* (R₂, H₂, σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂][gx↦vₓ], e₁),
          from trans_step.rfl,

          show ⊢ₛ ((R₂, H₂, σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂][gx↦vₓ], e₁) · [R, H, σ, letapp y = f[x] in e₂]),
          from stack.vcgen.cons h5 σ_verified fv_R R_valid f_is_func x_is_vₓ h6 h7 h8 h9
        }
      },
      case step.ite_true x e₁ e₂ { from
        show ⊢ₛ (R, H, σ, e₂), from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case step.ite_false x e₁ e₂ { from
        show ⊢ₛ (R, H, σ, e₁), from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      }
    },
    case stack.vcgen.cons H P H' s' σ σ' f g x y fx R' R S e e' vₓ Q₃ s'_verified σ_verified fv_R R'_valid g_is_func x_is_v y_not_in_σ cont pre_vc steps ih {
      assume s''',
      assume s_steps: ((s' · [R', H, σ, letapp y = g[x] in e]) ⟶ s'''),
      cases s_steps,
      case step.ctx s'' s'_steps {
        have : (sizeof s' < sizeof (s'·[R', H, σ, letapp y = g[x] in e])),
        from sizeof_substack,
        have : (sizeof s'' < sizeof (s''·[R', H, σ, letapp y = g[x] in e])),
        from sizeof_substack,
        have s''_verified: ⊢ₛ s'', from ih s'' s'_steps,
        have new_steps: ((S, H', σ'[f↦value.func f fx S R e' H' σ'][fx↦vₓ], e') ⟶* s''),
        from trans_step.trans steps s'_steps,
        show ⊢ₛ (s'' · [R', H, σ, letapp y = g[x] in e]),
        from stack.vcgen.cons s''_verified σ_verified fv_R R'_valid g_is_func x_is_v y_not_in_σ cont pre_vc new_steps
      },
      admit
    }
  end
