import .syntax .notations .logic .evaluation .vcgen .bindings .strengthening

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
            have ∃P₃', ⊢ (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂][gx↦vₓ]) : Q₂' ⋀ P₃',
            from env.vcgen.copy ha3 this ha4,
            let ⟨P₃', ha5⟩ := this in
            let P₃ := Q₂' ⋀ P₃' in

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
      case step.return H₁ H₂ σ₁ σ₂ f₁ x₁ y₁ R'₁ R₁ S₁ e₁ vy₁ vx₁ y_is_vy₁ g_is_func₁ x_is_vx₁ {
        have h1: ∃P₁ Q₁, (⊢ σ₁: P₁) ∧ (FV R'₁.to_prop ⊆ FV P₁) ∧ (σ₁ ⊨ R'₁.to_prop.instantiated_n) ∧
                                                                   (R'₁ ⋀ H₁ ⋀ P₁ ⊢ exp.return y₁ : Q₁),
        from stack.vcgen.top.inv s'_verified,
        cases h1 with P₁ h2,
        cases h2 with Q₁ h3,
        have σ₁_verified, from h3.left,
        have h4: ∃σ' Q', ⊢ (σ'[y₁↦vy₁]) : Q', from env.vcgen.inv σ₁_verified y_is_vy₁,
        cases h4 with σ₁' h5,
        cases h5 with Q₁' h6,
        have h6: ∃P₃, (⊢ (σ[y↦vy₁]) : P ⋀ P₃), from env.vcgen.copy σ_verified y_not_in_σ h6,
        cases h6 with P₃ h7,

        have h8: FV R'.to_prop ⊆ FV (P ⋀ P₃), from (
          assume z: var,
          assume : z ∈ FV R'.to_prop,
          have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
          show z ∈ FV (P ⋀ P₃), from free_in_prop.and₁ this
        ),

        have h9: y ∉ FV R'.to_prop.instantiated_n, from (
          assume : y ∈ FV R'.to_prop.instantiated_n,
          have y ∈ FV R'.to_prop, from free_of_instantiated_n_free this,
          have h10: y ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
          have σ.dom = FV P, from free_iff_contains σ_verified,
          have y ∈ σ.dom, from this.symm ▸ h10,
          have y ∈ σ, from this,
          show «false», from y_not_in_σ this
        ),
        have h10: (σ[y↦vy₁] ⊨ R'.to_prop.instantiated_n),
        from valid_env.subst_non_free_of_valid_env R'_valid h9,

        have g_in_σ: g ∈ σ,
        from env.contains_apply_equiv.right.mp (exists.intro (value.func f fx S R e' H' σ') g_is_func),

        have x_in_σ: x ∈ σ,
        from env.contains_apply_equiv.right.mp (exists.intro vₓ x_is_v),

        have h11: (FV (↑R' ⋀ ↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃)
             = FV (↑R' ⋀ ↑H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x)), from (
          let sy: set var := set.insert y ∅ in

          have h12: (σ[y↦vy₁]).dom = FV (P ⋀ P₃), from free_iff_contains h7,
          have h13: (σ[y↦vy₁]).dom = (σ.dom ∪ sy), from env.dom.inv,
          have h14: FV (P ⋀ P₃) = (σ.dom ∪ sy), from eq.trans h12.symm h13,

          have h15: FV (↑R' ⋀ ↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃) = (σ.dom ∪ sy),
          from set.eq_of_subset_of_subset (
            assume z: var,
            assume : z ∈ FV (↑R' ⋀ ↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃),
            or.elim (free_in_prop.and.inv this) (
              assume : free_in_prop z R',
              have h10: z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
              have σ.dom = FV P, from free_iff_contains σ_verified,
              have z ∈ σ.dom, from this.symm ▸ h10,
              show z ∈ σ.dom ∪ sy, from set.mem_union_left sy this
            ) (
              assume : z ∈ FV (↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃),
              or.elim (free_in_prop.and.inv this) (
                assume h10: free_in_prop z (H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁),
                have ¬ free_in_prop z (H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁),
                from call_history_closed (H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) z,
                show z ∈ σ.dom ∪ sy, from absurd h10 this
              ) (
                assume : z ∈ FV (P ⋀ P₃),
                show z ∈ (σ.dom ∪ sy), from h14 ▸ this
              )
            )
          ) (
            assume z: var,
            assume : z ∈ σ.dom ∪ sy,
            have z ∈ FV (P ⋀ P₃), from h14.symm ▸ this,
            have z ∈ FV (↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃), from free_in_prop.and₂ this,
            show z ∈ FV (↑R' ⋀ ↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃), from free_in_prop.and₂ this
          ),

          have h18: FV (↑R' ⋀ ↑H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x) = σ.dom ∪ sy,
          from set.eq_of_subset_of_subset (
            assume z: var,
            assume : z ∈ FV (↑R' ⋀ ↑H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
            or.elim (free_in_prop.and.inv this) (
              assume : free_in_prop z R',
              have h10: z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
              have σ.dom = FV P, from free_iff_contains σ_verified,
              have z ∈ σ.dom, from this.symm ▸ h10,
              show z ∈ σ.dom ∪ sy, from set.mem_union_left sy this
            ) (
              assume : z ∈ FV (↑H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
              or.elim (free_in_prop.and.inv this) (
                assume h10: free_in_prop z H,
                have ¬ free_in_prop z H,
                from call_history_closed H z,
                show z ∈ σ.dom ∪ sy, from absurd h10 this
              ) (
                assume : z ∈ FV (P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
                or.elim (free_in_prop.and.inv this) (
                  assume h10: z ∈ FV P,
                  have σ.dom = FV P, from free_iff_contains σ_verified,
                  have z ∈ σ.dom, from this.symm ▸ h10,
                  show z ∈ σ.dom ∪ sy, from set.mem_union_left sy this
                ) (
                  assume : z ∈ FV (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
                  or.elim (free_in_prop.and.inv this) (
                    assume : z ∈ FV (prop.call g x),
                    or.elim (free_in_prop.call.inv this) (
                      assume : free_in_term z g,
                      have z = g, from free_in_term.var.inv this,
                      have z ∈ σ, from this.symm ▸ g_in_σ,
                      show z ∈ σ.dom ∪ sy, from set.mem_union_left sy this
                    ) (
                      assume : free_in_term z x,
                      have z = x, from free_in_term.var.inv this,
                      have z ∈ σ, from this.symm ▸ x_in_σ,
                      show z ∈ σ.dom ∪ sy, from set.mem_union_left sy this
                    )
                  ) (
                    assume : z ∈ FV (prop.post g x ⋀ y ≡ term.app g x),
                    or.elim (free_in_prop.and.inv this) (
                      assume : z ∈ FV (prop.post g x),
                      or.elim (free_in_prop.post.inv this) (
                        assume : free_in_term z g,
                        have z = g, from free_in_term.var.inv this,
                        have z ∈ σ, from this.symm ▸ g_in_σ,
                        show z ∈ σ.dom ∪ sy, from set.mem_union_left sy this
                      ) (
                        assume : free_in_term z x,
                        have z = x, from free_in_term.var.inv this,
                        have z ∈ σ, from this.symm ▸ x_in_σ,
                        show z ∈ σ.dom ∪ sy, from set.mem_union_left sy this
                      )
                    ) (
                      assume : free_in_prop z (y ≡ term.app g x),
                      have free_in_term z (y ≡ term.app g x), from free_in_prop.term.inv this,
                      or.elim (free_in_term.binop.inv this) (
                        assume : free_in_term z y,
                        have z = y, from free_in_term.var.inv this,
                        have z ∈ sy, from set.mem_singleton_of_eq this,
                        show z ∈ σ.dom ∪ sy, from set.mem_union_right σ.dom this
                      ) (
                        assume : free_in_term z (term.app g x),
                        or.elim (free_in_term.app.inv this) (
                          assume : free_in_term z g,
                          have z = g, from free_in_term.var.inv this,
                          have z ∈ σ, from this.symm ▸ g_in_σ,
                          show z ∈ σ.dom ∪ sy, from set.mem_union_left sy this
                        ) (
                          assume : free_in_term z x,
                          have z = x, from free_in_term.var.inv this,
                          have z ∈ σ, from this.symm ▸ x_in_σ,
                          show z ∈ σ.dom ∪ sy, from set.mem_union_left sy this
                        )
                      )
                    )
                  )
                )
              )
            )
          ) (
            assume z: var,
            assume : z ∈ σ.dom ∪ sy,
            or.elim (set.mem_or_mem_of_mem_union this) (
              assume h10: z ∈ σ.dom,
              have σ.dom = FV P, from free_iff_contains σ_verified,
              have z ∈ FV P, from this ▸ h10,
              have z ∈ FV (P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x), from free_in_prop.and₁ this,
              have z ∈ FV (↑H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x), from free_in_prop.and₂ this,
              show z ∈ FV (↑R' ⋀ ↑H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
              from free_in_prop.and₂ this
            ) (
              assume : z ∈ sy,
              have h: z = y, from (set.mem_singleton_iff z y).mp this,
              have free_in_term y (term.var y), from free_in_term.var y,
              have free_in_term z y, from h.symm ▸ this,
              have free_in_term z (y ≡ term.app g x), from free_in_term.binop₁ this,
              have free_in_prop z (y ≡ term.app g x), from free_in_prop.term this,
              have z ∈ FV (prop.post g x ⋀ y ≡ term.app g x), from free_in_prop.and₂ this,
              have z ∈ FV (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x), from free_in_prop.and₂ this,
              have z ∈ FV (P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x), from free_in_prop.and₂ this,
              have z ∈ FV (↑H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x), from free_in_prop.and₂ this,
              show z ∈ FV (↑R' ⋀ ↑H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
              from free_in_prop.and₂ this
            )
          ),

          eq.trans h15 h18.symm
        ),

        have h12: ∀σ, dominates σ (R' ⋀ (H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃)
                                  (R' ⋀ H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
        from (
          assume σ₃: env,
          dominates.same_left (
            assume : σ₃ ⊨ R'.to_prop.instantiated_p,
            have calls_to_prop (H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁)
               = (calls_to_prop H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁),
            by unfold calls_to_prop,
            have calls_to_prop (H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃
              = ((calls_to_prop H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁) ⋀ P ⋀ P₃),
            from this ▸ rfl,
            have h13: ↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃
              = ((↑H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁) ⋀ P ⋀ P₃),
            from this,

            have h15: dominates σ₃ ((↑H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁) ⋀ P ⋀ P₃)
                                   (↑H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P ⋀ P₃),
            from dominates.and_assoc.symm,

            have h16: dominates σ₃ (↑H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P ⋀ P₃)
                                   (↑H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
            from dominates.same_left (
              assume : σ₃ ⊨ prop.instantiated_p ↑H,
              have h17: dominates σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P ⋀ P₃)
                                ((prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P) ⋀ P₃),
              from dominates.and_assoc,
              have h18: dominates σ₃ ((prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P) ⋀ P₃)
                                     ((P ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁) ⋀ P₃),
              from dominates.same_right (λ_, dominates.and_symm),
              have h19: dominates σ₃ ((P ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁) ⋀ P₃)
                                     (P ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P₃),
              from dominates.and_assoc.symm,
              have h20: dominates σ₃ (P ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P₃)
                                     (P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
              from dominates.same_left (
                assume P_valid: σ₃ ⊨ P.instantiated_p,

                have env_equiv: (∀y, y ∈ σ → (σ y = σ₃ y)),
                from env_equiv_of_translation_valid σ_verified σ₃ P_valid,

                have h_impl: (σ₃ ⊨ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P₃).instantiated_p)
                           → (σ₃ ⊨ (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x).instantiated_p), from (
                  assume h21: σ₃ ⊨ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P₃).instantiated_p,

                  show σ₃ ⊨ (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x).instantiated_p, from sorry
                ),

                have h_calls: calls_p_subst σ₃ (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x)
                            ⊆ calls_p_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P₃), from (
                  assume c: calltrigger,
                  assume : c ∈ calls_p_subst σ₃ (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),

                  show c ∈ calls_p_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P₃),
                  from @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ₃)
                       (calls_p (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x))
                       (λa, a ∈ calls_p_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P₃)) c this (
                    assume c': calltrigger,
                    assume : c' ∈ calls_p (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
                    or.elim (prop.has_call_p.and.inv this) (
                      assume : c' ∈ calls_p (prop.call g x),
                      have c'_is_g_x: c' = ⟨g, x⟩, from prop.has_call_p.call.inv this,
                      have h22: calltrigger.subst σ₃ ⟨g, x⟩ = ⟨term.subst_env σ₃ g, term.subst_env σ₃ x⟩,
                      by unfold calltrigger.subst,
                      have σ₃ g = (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂),
                      from eq.trans (env_equiv g g_in_σ).symm g_is_func₁,
                      have h23: term.subst_env σ₃ g = value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂,
                      from (term.subst_env.var.right (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂)).mp this,
                      have σ₃ x = vx₁,
                      from eq.trans (env_equiv x x_in_σ).symm x_is_vx₁,
                      have h24: term.subst_env σ₃ x = vx₁,
                      from (term.subst_env.var.right vx₁).mp this,
                      have h25: calltrigger.subst σ₃ c' = ⟨(value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂), vx₁⟩,
                      from h24 ▸ h23 ▸ c'_is_g_x.symm ▸ h22,
                      have h26: calltrigger.mk (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁
                           ∈ calls_p (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁),
                      from prop.has_call_p.calltrigger,
                      have h27: calltrigger.subst σ₃ (calltrigger.mk (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)
                             = ⟨term.subst_env σ₃ (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂), term.subst_env σ₃ vx₁⟩,
                      by unfold calltrigger.subst,
                      have h28: term.subst_env σ₃ (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) = (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂),
                      from term.subst_env.value,
                      have h29: term.subst_env σ₃ vx₁ = vx₁, from term.subst_env.value,
                      have h30: calltrigger.subst σ₃ (calltrigger.mk (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)
                                                   = ⟨value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂, term.subst_env σ₃ vx₁⟩,
                      from @eq.subst term
                      (λa, calltrigger.subst σ₃ (calltrigger.mk (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)
                            = ⟨a, term.subst_env σ₃ vx₁⟩)
                      (term.subst_env σ₃ (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂))
                      (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) h28 h27,
                      have h31: calltrigger.subst σ₃ (calltrigger.mk (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)
                                                   = ⟨value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂, vx₁⟩,
                      from @eq.subst term
                      (λa, calltrigger.subst σ₃ (calltrigger.mk (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)
                            = ⟨value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂, a⟩)
                      (term.subst_env σ₃ vx₁) vx₁ h29 h30,
                      have calltrigger.mk (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁
                           ∈ calls_p_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁),
                      from set.mem_image h26 h31,
                      have calltrigger.mk (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁
                           ∈ calls_p_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P₃),
                      from prop.has_call_p_subst.and₁ this,
                      show calltrigger.subst σ₃ c' ∈ calls_p_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁
                                                                    ⋀ P₃),
                      from h25.symm ▸ this
                    ) (
                      assume : c' ∈ calls_p (prop.post g x ⋀ y ≡ term.app g x),
                      or.elim (prop.has_call_p.and.inv this) (
                        assume : c' ∈ calls_p (prop.post g x),
                        show calltrigger.subst σ₃ c' ∈ calls_p_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁
                                                                      ⋀ P₃),
                        from absurd this prop.has_call_p.post.inv
                      ) (
                        assume : c' ∈ calls_p (y ≡ term.app g x),
                        show calltrigger.subst σ₃ c' ∈ calls_p_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁
                                                                      ⋀ P₃),
                        from absurd this prop.has_call_p.term.inv
                      )
                    )
                  )
                ),

                have h_quantifiers: quantifiers_p (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x) = ∅,
                from set.eq_empty_of_forall_not_mem (
                  assume q: callquantifier,
                  assume : q ∈ quantifiers_p (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
                  or.elim (prop.has_quantifier_p.and.inv this) (
                    assume : q ∈ quantifiers_p (prop.call g x),
                    show «false», from prop.has_quantifier_p.call.inv this
                  ) (
                    assume : q ∈ quantifiers_p (prop.post g x ⋀ y ≡ term.app g x),
                    or.elim (prop.has_quantifier_p.and.inv this) (
                      assume : q ∈ quantifiers_p (prop.post g x),
                      show «false», from prop.has_quantifier_p.post.inv this
                    ) (
                      assume : q ∈ quantifiers_p (y ≡ term.app g x),
                      show «false», from prop.has_quantifier_p.term.inv this
                    )
                  )
                ),

                show dominates σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P₃)
                                  (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
                from dominates.no_quantifiers h_impl h_calls h_quantifiers
              ),

              show dominates σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P ⋀ P₃)
                                (P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
              from dominates.trans h17 (dominates.trans h18 (dominates.trans h19 h20))
            ),

            have dominates σ₃ ((↑H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁) ⋀ P ⋀ P₃)
                              (↑H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
            from dominates.trans h15 h16,
            show dominates σ₃ (↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃)
                              (↑H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
            from h13.symm ▸ this
          )
        ),
                       
        have h13: R' ⋀ (H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃ ⊢ e : Q₃,
        from strengthen_exp cont (R' ⋀ (H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃) h11 h12,

        show ⊢ₛ (R', H · call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁, σ[y↦vy₁], e),
        from stack.vcgen.top h7 h8 h10 h13
      }
    }
  end
