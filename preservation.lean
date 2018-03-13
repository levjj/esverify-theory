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

lemma dominates_p_true (σ: env) (P: prop):
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

lemma dominates_n_true (σ: env) (P: prop):
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

lemma env_dominates_p_rest {P: prop} {σ: env} {x: var} {v: value}:
      (⊢ (σ[x↦v]) : P) → (∃Q, (⊢ σ : Q) ∧ ∀σ', dominates_p σ' P Q) :=
  assume σ_verified: ⊢ (σ[x↦v]) : P,
  begin
    cases σ_verified,
    case env.vcgen.tru Q _ σ_verified ih { from
      have ∀σ', dominates_p σ' (prop.and Q (x ≡ value.true)) Q,
      from λσ', dominates_p.of_and_left,
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ ∀σ', dominates_p σ' (prop.and Q (x ≡ value.true)) Q_1,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.fls Q _ σ_verified { from
      have ∀σ', dominates_p σ' (prop.and Q (x ≡ value.false)) Q,
      from λσ', dominates_p.of_and_left,
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ ∀σ', dominates_p σ' (prop.and Q (x ≡ value.false)) Q_1,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.num n Q _ σ_verified { from
      have ∀σ', dominates_p σ' (prop.and Q (x ≡ value.num n)) Q,
      from λσ', dominates_p.of_and_left,
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ ∀σ', dominates_p σ' (prop.and Q (x ≡ value.num n)) Q_1,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.func σ₂ f fx R S H e Q Q₂ Q₃ x_not_in_σ f_not_in_σ₂
         fx_not_in_σ₂ f_neq_fx σ₁_verified σ₂_verified fx_in_R fv_R fv_S e_verified func_vc { from
      let funcp := prop.subst_env (σ₂[f↦value.func f fx R S e H σ₂])
                                  (prop.func f fx R (Q₃ (term.app f fx) ⋀ S)) in
      have ∀σ', dominates_p σ' (Q ⋀ x ≡ value.func f fx R S e H σ₂ ⋀ funcp) Q,
      from λσ', dominates_p.of_and_left,
      show ∃Q_1, (⊢ σ : Q_1) ∧ ∀σ', dominates_p σ' (prop.and Q ((x ≡ (value.func f fx R S e H σ₂)) ⋀ funcp)) Q_1,
      from exists.intro Q ⟨σ₁_verified, this⟩
    }
  end

lemma propctx_apply_hpq {P₁ P₂: prop} {Q: propctx} {t: term}: (↑P₁ ⋀ ↑P₂ ⋀ Q) t = (P₁ ⋀ P₂ ⋀ Q t) :=
  have h1: P₁.to_propctx t = P₁, from unchanged_of_apply_propctx_without_hole,
  have h2: P₂.to_propctx t = P₂, from unchanged_of_apply_propctx_without_hole,
  show (↑P₁ ⋀ ↑P₂ ⋀ Q) t = (P₁ ⋀ P₂ ⋀ Q t), by calc
  (↑P₁ ⋀ ↑P₂ ⋀ Q) t = propctx.apply (propctx.and ↑P₁ (propctx.and ↑P₂ Q)) t : rfl
                  ... = (propctx.apply ↑P₁ t ⋀ propctx.apply (propctx.and ↑P₂ Q) t) : by unfold propctx.apply
                  ... = (P₁.to_propctx t ⋀ propctx.apply (propctx.and ↑P₂ Q) t) : rfl
                  ... = (P₁ ⋀ propctx.apply (propctx.and ↑P₂ Q) t) : by rw[h1]
                  ... = (P₁ ⋀ propctx.apply ↑P₂ t ⋀ propctx.apply Q t) : by unfold propctx.apply
                  ... = (P₁ ⋀ P₂.to_propctx t ⋀ propctx.apply Q t) : rfl
                  ... = (P₁ ⋀ P₂ ⋀ propctx.apply Q t) : by rw[h2]

lemma exp.preservation {R: spec} {H: history} {σ σ': env} {P: prop} {e e': exp} {Q: propctx}:
      (⊢ σ : P) → FV (spec.to_prop R) ⊆ FV P → (σ ⊨ R.to_prop.instantiated_n) → (R ⋀ H ⋀ P ⊢ e : Q) →
      ((R, H, σ, e) ⟶ (R, H, σ', e')) →
      ∃Q', (⊢ₛ (R, H, σ', e') : Q') ∧ ∀σ' t, dominates_n σ' (Q' t) ((↑H ⋀ ↑P ⋀ Q) t) ∧
                                             (FV ((↑H ⋀ ↑P ⋀ Q) t) ⊆ FV (Q' t)) :=
  sorry

lemma inlined_dominates_p_spec {σ σ₁: env} {P: prop} {Q: propctx} {f x: var} {R S: spec} {e: exp} {H: history}:
  (⊢ σ₁ : P) → (f ∉ σ₁) → (x ∉ σ₁) → (x ≠ f) → (σ ⊨ P.instantiated_p) → (σ f = value.func f x R S e H σ₁) →
  (⊢ (σ₁[f↦value.func f x R S e H σ₁]) : (P ⋀ f ≡ value.func f x R S e H σ₁ ⋀
                  prop.subst_env (σ₁[f↦value.func f x R S e H σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)))) →
  dominates_p σ (prop.subst_env (σ₁[f↦value.func f x R S e H σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)))
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

  have h5: dominates_p σ (term.unop unop.isFunc vf) (term.unop unop.isFunc f),
  from dominates_p.no_quantifiers (
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

  have h6: dominates_p σ (prop.forallc x vf (prop.subst_env (σ₁[f↦vf]) forallp')) (prop.forallc x f forallp),
  from dominates_p.quantifier (
    assume : σ ⊨ vf ≡ f,
    assume v: value,

    have ¬ (x = f ∨ x ∈ σ₁), from not_or_distrib.mpr ⟨x_neq_f, x_not_in_σ₁⟩,
    have x ∉ (σ₁[f↦vf]), from mt env.contains.inv this,
    have (∀y, y ∈ (σ₁[f↦vf]) → ((σ₁[f↦vf]) y = (σ[x↦v]) y)),
    from env.equiv_of_not_contains env_equiv this,
    have h7: dominates_p (σ[x↦v]) (prop.subst_env (σ₁[f↦vf]) forallp') forallp',
    from dominates_p_equiv_subst this,
    have h82: dominates_p (σ[x↦v]) (prop.implies (prop.post f x) (Q (term.app f x) ⋀ S.to_prop))
                                 (prop.implies (prop.post f x) S.to_prop),
    from dominates_p.or_intro dominates_p.self dominates_p.of_and_right,
    have h8: dominates_p (σ[x↦v]) forallp' forallp,
    from dominates_p.same_left (λ_, h82),
    show dominates_p (σ[x↦v]) (prop.subst_env (σ₁[f↦vf]) forallp') forallp,
    from dominates_p.trans h7 h8
  ),
  have h7: dominates_p σ (term.unop unop.isFunc vf ⋀ prop.forallc x vf (prop.subst_env (σ₁[f↦vf]) forallp'))
                       (term.unop unop.isFunc f ⋀ prop.forallc x f forallp),
  from dominates_p.and_intro h5 (λ_, h6),
  show dominates_p σ (prop.subst_env (σ₁[f↦value.func f x R S e H σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)))
                   (spec.to_prop (spec.func f x R S)),
  from h3.symm ▸ h4.symm ▸ h7

theorem preservation {s: stack} {Q: propctx}:
   (⊢ₛ s : Q) → ∀s', (s ⟶ s') →
   ∃Q', (⊢ₛ s' : Q') ∧ ∀σ' t, dominates_n σ' (Q' t) (Q t) ∧ (FV (Q t) ⊆ FV (Q' t)) :=
  assume s_verified:  ⊢ₛ s : Q,
  begin
    induction s_verified,
    case stack.vcgen.top σ e P R H Q σ_verified fv_R R_valid e_verified {
      assume s',
      assume s_steps: ((R, H, σ, e) ⟶ s'),

      have R_closed: closed_subst σ R.to_prop, from (
        assume z: var,
        assume : z ∈ FV R.to_prop,
        have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
        show z ∈ σ.dom, from (free_iff_contains σ_verified).symm ▸ this
      ),

      cases s_steps,
      case step.tru x e {
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case step.fals x e {
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case step.num n e x {
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case step.closure R' S' f x e₁ e₂ {
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case step.unop op x y e {
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case step.binop op x y z e {
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case step.app f x y S₂ H₂ g σ₂ R₂ gx e₁ e₂ vₓ f_is_func x_is_vₓ {
        cases e_verified,
        case exp.vcgen.app Q f_free x_free y_not_free e₂_verified func_vc { from

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
            have closed_subst σ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x), from (
              assume z: var,
              assume : z ∈ FV (↑(term.unop unop.isFunc f) ⋀ prop.pre f x),
              or.elim (free_in_prop.and.inv this) (
                assume : free_in_prop z (term.unop unop.isFunc f),
                have free_in_term z (term.unop unop.isFunc f), from free_in_prop.term.inv this,
                have free_in_term z f, from free_in_term.unop.inv this,
                have z = f, from free_in_term.var.inv this,
                show z ∈ σ, from this.symm ▸ env_has_f
              ) (
                assume : z ∈ FV (prop.pre f x),
                or.elim (free_in_prop.pre.inv this) (
                  assume : free_in_term z f,
                  have z = f, from free_in_term.var.inv this,
                  show z ∈ σ, from this.symm ▸ env_has_f
                ) (
                  assume : free_in_term z x,
                  have z = x, from free_in_term.var.inv this,
                  show z ∈ σ, from this.symm ▸ env_has_x
                )
              )
            ),
            have σ ⊨ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).instantiated_p,
            from consequent_of_H_P_call σ_verified R_closed R_valid func_vc env_has_f env_has_x this,
            have h3: σ ⊨ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased_p,
            from valid_env.erased_p_of_instantiated_p this,
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

          have ∀σ, dominates_p σ (R₂ ⋀ H₂ ⋀ P₃) (H₂ ⋀ Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from (
            assume σ: env,

            have hb1: dominates_p σ (R₂ ⋀ H₂ ⋀ P₃) ((H₂ ⋀ P₃) ⋀ R₂),
            from dominates_p.and_symm,

            have hb2: dominates_p σ ((H₂ ⋀ P₃) ⋀ R₂) (H₂ ⋀ P₃ ⋀ R₂),
            from dominates_p.and_assoc.symm,

            have hb3: dominates_p σ (↑H₂ ⋀ P₃ ⋀ ↑R₂) ((P₃ ⋀ ↑R₂) ⋀ H₂),
            from dominates_p.and_symm,

            have hb4: dominates_p σ (P₃ ⋀ ↑R₂) (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from (

              have (∃Q, (⊢ (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂]) : Q) ∧ ∀σ', dominates_p σ' P₃ Q),
              from env_dominates_p_rest ha5,
              let ⟨Q₂'', ⟨hb1, hb2⟩⟩ := this in
              have Q₂' = Q₂'', from env.vcgen.inj ha3 Q₂'' hb1,
              have hb3: dominates_p σ P₃ Q₂', from this.symm ▸ hb2 σ,

              have dominates_p σ Q₂' (Q₂ ⋀ spec.func g gx R₂ S₂), from (
                dominates_p.same_left (
                  assume Q₂_valid: σ ⊨ Q₂.instantiated_p,
                  dominates_p.left_elim (
                    assume : σ ⊨ (prop.term (g ≡ value.func g gx R₂ S₂ e₁ H₂ σ₂)).instantiated_p,
                    have (σ g = value.func g gx R₂ S₂ e₁ H₂ σ₂), from valid_env.subst_of_eq_instantiated this,
                    inlined_dominates_p_spec ha2.right.right.right.right.right.left
                    ha2.right.left ha2.right.right.left ha2.right.right.right.left.symm Q₂_valid this ha3
                  )
                )
              ),
              have dominates_p σ P₃ (Q₂ ⋀ spec.func g gx R₂ S₂),
              from dominates_p.trans hb3 this,

              have hb8: dominates_p σ (P₃ ⋀ ↑R₂) ((Q₂ ⋀ spec.func g gx R₂ S₂) ⋀ R₂),
              from dominates_p.same_right (λ_, this),

              have hb9: dominates_p σ ((Q₂ ⋀ spec.func g gx R₂ S₂) ⋀ R₂) (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂),
              from dominates_p.and_assoc.symm,

              show dominates_p σ (P₃ ⋀ ↑R₂) (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂),
              from dominates_p.trans hb8 hb9
            ),

            have hb5: dominates_p σ ((P₃ ⋀ ↑R₂) ⋀ H₂) ((Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂) ⋀ H₂),
            from dominates_p.same_right (λ_, hb4),

            have hb6: dominates_p σ ((Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂) ⋀ H₂) (↑H₂ ⋀ Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂),
            from dominates_p.and_symm,

            show dominates_p σ (R₂ ⋀ H₂ ⋀ P₃) (H₂ ⋀ Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂),
            from dominates_p.trans (dominates_p.trans (dominates_p.trans (dominates_p.trans hb1 hb2) hb3) hb5) hb6
          ),
          have R₂ ⋀ H₂ ⋀ P₃ ⊢ e₁ : Q₃,
          from strengthen_exp ha6 (R₂ ⋀ H₂ ⋀ P₃) ha8 this,

          have h5: ⊢ₛ (R₂, H₂, σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂][gx↦vₓ], e₁) : H₂ ⋀ P₃ ⋀ Q₃,
          from stack.vcgen.top ha5 ha7 ha9 this,

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

            have ∀σ, dominates_p σ (R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                                   ((↑R ⋀ (↑H ⋀ P)) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x), from (
              assume σ: env,

              have haa1: dominates_p σ (↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                               ((↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from dominates_p.and_assoc,

              have haa2: dominates_p σ (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                                     ((↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑R),
              from dominates_p.and_symm,

              have haa3: dominates_p σ ((↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑R)
                                     (((↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑ R),
              from dominates_p.same_right (λ_, haa1),

              have haa4: dominates_p σ (((↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑R)
                                     (↑R ⋀ (↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from dominates_p.and_symm,
              
              have haa5: dominates_p σ (↑R ⋀ (↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                                     ((↑R ⋀ (↑H ⋀ P)) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from dominates_p.and_assoc,
              
              show dominates_p σ (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                               ((↑R ⋀ (↑H ⋀ P)) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from dominates_p.trans (dominates_p.trans (dominates_p.trans haa2 haa3) haa4) haa5
            ),
            show (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⊢ e₂ : Q),
            from strengthen_exp e₂_verified (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ha1 this
          ),

          have h8: ⟪ prop.implies (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x) (↑(term.unop unop.isFunc f) ⋀ prop.pre f x) ⟫, from (
            assume σ: env,
            have ha1: dominates_p σ (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x) ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x),
            from dominates_p.shuffle,

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

          have h10: ∀σ' t, dominates_n σ' ((↑H₂ ⋀ ↑P₃ ⋀ Q₃) t) (↑H₂ ⋀ (Q₂'⋀P₃') ⋀ Q₃ t)
                        ∧ (FV (↑H₂ ⋀ (Q₂'⋀P₃') ⋀ Q₃ t) ⊆ FV ((↑H₂ ⋀ ↑P₃ ⋀ Q₃) t)), from (
            assume σ': env,
            assume t: term,
            have h11: (↑H₂ ⋀ ↑P₃ ⋀ Q₃) t = (↑H₂ ⋀ P₃ ⋀ Q₃ t), from propctx_apply_hpq,

            have dominates_n σ' (↑H₂ ⋀ P₃ ⋀ Q₃ t) (↑H₂ ⋀ (Q₂'⋀ P₃') ⋀ Q₃ t),
            from dominates_n.self,
            have h12: dominates_n σ' ((↑H₂ ⋀ ↑P₃ ⋀ Q₃) t) (↑H₂ ⋀ (Q₂'⋀ P₃') ⋀ Q₃ t), from h11.symm ▸ this,
            have FV (↑H₂ ⋀ (Q₂'⋀ P₃') ⋀ Q₃ t) ⊆ FV (↑H₂ ⋀ P₃ ⋀ Q₃ t),
            from set.subset.refl (FV (↑H₂ ⋀ P₃ ⋀ Q₃ t)),
            have h13: FV (↑H₂ ⋀ (Q₂'⋀ P₃') ⋀ Q₃ t) ⊆ FV ((↑H₂ ⋀ ↑P₃ ⋀ Q₃) t), from h11.symm ▸ this,
            ⟨h12, h13⟩
          ),

          have h11: ⊢ₛ ((R₂, H₂, σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂][gx↦vₓ], e₁) · [R, H, σ, letapp y = f[x] in e₂])
                    : H ⋀ P ⋀ propctx.exis y (prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⋀ Q),
          from stack.vcgen.cons h5 h6 σ_verified ha2.right.right.right.right.right.left ha5 fv_R R_valid
                                f_is_func x_is_vₓ h7 
                                ha2.right.right.right.right.right.right.right.right.right.left
                                h10 h8 h9,

          have h12: ∀σ' t, dominates_n σ'
            ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call f x) ⋀ ↑(prop.post f x) ⋀ ↑(y ≡ term.app f x) ⋀ Q)) t)
            ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call f x) ⋀ ↑(prop.post f x) ⋀ ↑(y ≡ term.app f x) ⋀ Q)) t)
          ∧ (FV ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call f x) ⋀ ↑(prop.post f x) ⋀ ↑(y ≡ term.app f x) ⋀ Q)) t)
           ⊆ FV ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call f x) ⋀ ↑(prop.post f x) ⋀ ↑(y ≡ term.app f x) ⋀ Q)) t)),
          from λσ' t, ⟨dominates_n.self, (set.subset.refl
            (FV ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call f x) ⋀ ↑(prop.post f x) ⋀ ↑(y ≡ term.app f x) ⋀ Q)) t)))⟩,
          exists.intro (H ⋀ P ⋀ propctx.exis y (prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⋀ Q)) ⟨h11, h12⟩
        }
      },
      case step.ite_true x e₁ e₂ {
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case step.ite_false x e₁ e₂ {
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      }
    },
    case stack.vcgen.cons H H' P P' P'' s' σ σ' f g x y fx R' R S e e' vₓ Q₂ Q₃ Q₂' s'_verified y_not_in_σ σ_verified
                          σ'_verified σ''_verified fv_R' R'_valid g_is_func x_is_v cont e'_verified Q₂'_dom pre_vc steps ih {
      assume s''',
      assume s_steps: ((s' · [R', H, σ, letapp y = g[x] in e]) ⟶ s'''),
      cases s_steps,
      case step.ctx s'' s'_steps { from
        have (∃ (Q' : propctx), (⊢ₛ s'' : Q') ∧ ∀ (σ' : env) (t : term), dominates_n σ' (Q' t) (Q₂' t) ∧
                                                                         (FV (Q₂' t) ⊆ FV (Q' t))),
        from ih s'' s'_steps,
        let ⟨Q', ⟨h1, h2⟩⟩ := this in
        have new_steps: ((R, H', σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ], e') ⟶* s''),
        from trans_step.trans steps s'_steps,

        have h3: ∀ (σ' : env) (t : term), dominates_n σ' (Q' t) (↑H' ⋀ P'' ⋀ Q₂ t)
                                  ∧ (FV (↑H' ⋀ P'' ⋀ Q₂ t) ⊆ FV (Q' t)), from (
          assume σ'': env,
          assume t: term,
          have h4: dominates_n σ'' (Q' t) (Q₂' t), from (h2 σ'' t).left,
          have h5: dominates_n σ'' (Q₂' t) (↑H' ⋀ P'' ⋀ Q₂ t), from (Q₂'_dom σ'' t).left,
          have h6: dominates_n σ'' (Q' t) (↑H' ⋀ P'' ⋀ Q₂ t), from dominates_n.trans h4 h5,

          have h7: FV (Q₂' t) ⊆ FV (Q' t), from (h2 σ'' t).right,
          have h8: FV (↑H' ⋀ P'' ⋀ Q₂ t) ⊆ FV (Q₂' t), from (Q₂'_dom σ'' t).right,
          have h9: FV (↑H' ⋀ P'' ⋀ Q₂ t) ⊆ FV (Q' t), from set.subset.trans h8 h7,

          ⟨h6, h9⟩
        ),
        have h4: ⊢ₛ (s'' · [R', H, σ, letapp y = g[x] in e])
                 : H ⋀ P ⋀ propctx.exis y (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃),
        from stack.vcgen.cons h1 y_not_in_σ σ_verified σ'_verified σ''_verified fv_R' R'_valid
                              g_is_func x_is_v cont e'_verified h3 pre_vc new_steps,

        have h7: ∀σ'' t, dominates_n σ''
          ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call g x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) t)
          ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call g x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) t)
        ∧ (FV ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call g x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) t)
         ⊆ FV ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call g x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) t)),
        from λσ'' t, ⟨dominates_n.self, set.subset.refl
          (FV ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call g x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) t))⟩,
        exists.intro (H ⋀ P ⋀ propctx.exis y (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃)) ⟨h4, h7⟩
      },
      case step.return H₁ H₂ σ₁ σ₂ f₁ x₁ y₁ R'₁ R₁ S₁ e₁ vy₁ vx₁ y_is_vy₁ g_is_func₁ x_is_vx₁ { from
        have ∃P₁ Q₁, (⊢ σ₁: P₁) ∧ (FV R'₁.to_prop ⊆ FV P₁) ∧ (σ₁ ⊨ R'₁.to_prop.instantiated_n) ∧
                                                                   (R'₁ ⋀ H₁ ⋀ P₁ ⊢ exp.return y₁ : Q₁),
        from stack.vcgen.top.inv s'_verified,
        let ⟨P₁, Q₁, ⟨σ₁_verified, ⟨h1, ⟨h2, h3⟩⟩⟩⟩ := this in
        have ∃σ' Q', ⊢ (σ'[y₁↦vy₁]) : Q', from env.vcgen.inv σ₁_verified y_is_vy₁,
        let ⟨σ₁', Q₁', h4⟩ := this in
        have ∃P₃, (⊢ (σ[y↦vy₁]) : P ⋀ P₃), from env.vcgen.copy σ_verified y_not_in_σ h4,
        let ⟨P₃, h5⟩ := this in

        have h6: FV R'.to_prop ⊆ FV (P ⋀ P₃), from (
          assume z: var,
          assume : z ∈ FV R'.to_prop,
          have z ∈ FV P, from set.mem_of_subset_of_mem fv_R' this,
          show z ∈ FV (P ⋀ P₃), from free_in_prop.and₁ this
        ),

        have h7: y ∉ FV R'.to_prop.instantiated_n, from (
          assume : y ∈ FV R'.to_prop.instantiated_n,
          have y ∈ FV R'.to_prop, from free_of_instantiated_n_free this,
          have h10: y ∈ FV P, from set.mem_of_subset_of_mem fv_R' this,
          have σ.dom = FV P, from free_iff_contains σ_verified,
          have y ∈ σ.dom, from this.symm ▸ h10,
          have y ∈ σ, from this,
          show «false», from y_not_in_σ this
        ),
        have h8: (σ[y↦vy₁] ⊨ R'.to_prop.instantiated_n),
        from valid_env.subst_non_free_of_valid_env R'_valid h7,

        have g_in_σ: g ∈ σ,
        from env.contains_apply_equiv.right.mp (exists.intro (value.func f fx R S e' H' σ') g_is_func),

        have x_in_σ: x ∈ σ,
        from env.contains_apply_equiv.right.mp (exists.intro vₓ x_is_v),

        have h9: (FV (↑R' ⋀ ↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃)
             = FV (↑R' ⋀ ↑H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x)), from (
          let sy: set var := set.insert y ∅ in

          have h12: (σ[y↦vy₁]).dom = FV (P ⋀ P₃), from free_iff_contains h5,
          have h13: (σ[y↦vy₁]).dom = (σ.dom ∪ sy), from env.dom.inv,
          have h14: FV (P ⋀ P₃) = (σ.dom ∪ sy), from eq.trans h12.symm h13,

          have h15: FV (↑R' ⋀ ↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃) = (σ.dom ∪ sy),
          from set.eq_of_subset_of_subset (
            assume z: var,
            assume : z ∈ FV (↑R' ⋀ ↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃),
            or.elim (free_in_prop.and.inv this) (
              assume : free_in_prop z R',
              have h10: z ∈ FV P, from set.mem_of_subset_of_mem fv_R' this,
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
              have h10: z ∈ FV P, from set.mem_of_subset_of_mem fv_R' this,
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

        have h10: ∀σ₃, (σ₃ ⊨ (P ⋀ P₃).instantiated_p) → (σ₃ ⊨ vc.post g x ⋀ y ≡ term.app g x), from (
          assume σ₃: env,
          assume P_P₃_valid: σ₃ ⊨ (P ⋀ P₃).instantiated_p,
          have P_valid: σ₃ ⊨ P.instantiated_p,
          from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_P₃_valid)).left,

          have env_equiv: (∀z, z ∈ σ → (σ z = σ₃ z)),
          from env_equiv_of_translation_valid σ_verified σ₃ P_valid,

          have env_equiv2: (∀z, z ∈ (σ[y↦vy₁]) → ((σ[y↦vy₁]) z = σ₃ z)),
          from env_equiv_of_translation_valid h5 σ₃ P_P₃_valid,

          have h21: σ₃ ⊨ P₃.instantiated_p,
          from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_P₃_valid)).right,

          have σ₃ g = (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂),
          from eq.trans (env_equiv g g_in_σ).symm g_is_func₁,
          have h23: term.subst_env σ₃ g = value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂,
          from (term.subst_env.var.right (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂)).mp this,

          have σ₃ x = vx₁,
          from eq.trans (env_equiv x x_in_σ).symm x_is_vx₁,
          have h24: term.subst_env σ₃ x = vx₁,
          from (term.subst_env.var.right vx₁).mp this,

          have (σ[y↦vy₁]) y = vy₁, from env.apply_of_contains y_not_in_σ,
          have σ₃ y = vy₁,
          from eq.trans (env_equiv2 y env.contains.same).symm this,
          have h25: term.subst_env σ₃ y = vy₁,
          from (term.subst_env.var.right vy₁).mp this,

          have some vx₁ = some vₓ,
          from eq.trans x_is_vx₁.symm x_is_v,
          have h65: vx₁ = vₓ, from option.some.inj this,

          have some (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) = some (value.func f fx R S e' H' σ'),
          from eq.trans g_is_func₁.symm g_is_func,
          have (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) = (value.func f fx R S e' H' σ'),
          from option.some.inj this,
          have h66: f₁ = f, from (value.func.inj this).left,
          have h67: x₁ = fx, from (value.func.inj this).right.left,
          have h68: R₁ = R, from (value.func.inj this).right.right.left,
          have h69: S₁ = S, from (value.func.inj this).right.right.right.left,
          have h70: e₁ = e', from (value.func.inj this).right.right.right.right.left,
          have h71: H₂ = H', from (value.func.inj this).right.right.right.right.right.left,
          have h72: σ₂ = σ', from (value.func.inj this).right.right.right.right.right.right,

          have h49: σ₃ ⊨ vc.post g x, from (

            have ∃P₁ Q₁', (⊢ σ₁: P₁) ∧ (FV R'₁.to_prop ⊆ FV P₁) ∧ (σ₁ ⊨ R'₁.to_prop.instantiated_n) ∧
                          (R'₁ ⋀ H₁ ⋀ P₁ ⊢ exp.return y₁: Q₁'),
            from stack.vcgen.top.inv s'_verified,

            let ⟨P₁, Q₁', ⟨σ₁_verified, ⟨fv_R'₁, ⟨R'₁_valid, return_verified⟩⟩⟩⟩ := this in

            have h42: σ₁.dom = FV P₁, from free_iff_contains σ₁_verified,
            have y₁_in_σ₁: y₁ ∈ σ₁, from env.contains_apply_equiv.right.mp (exists.intro vy₁ y_is_vy₁),
            have h26: term.subst_env σ₁ y₁ = vy₁,
            from (term.subst_env.var.right vy₁).mp y_is_vy₁,

            have R'₁ ⋀ H₁ ⋀ P₁ ⊢ exp.return y₁ : y₁ ≣ •,
            from exp.vcgen.return (exp.vcgen.return.inv return_verified),

            have ⊢ₛ (R'₁, H₁, σ₁, exp.return y₁) : H₁ ⋀ P₁ ⋀ y₁ ≣ •,
            from stack.vcgen.top σ₁_verified fv_R'₁ R'₁_valid this,

            have h44: Q₂' = (H₁ ⋀ P₁ ⋀ y₁ ≣ •),
            from stack.vcgen.inj s'_verified (H₁ ⋀ P₁ ⋀ y₁ ≣ •) this,

            have h45a: σ₁ ⊨ prop.instantiated_n ↑H₁, from history_valid σ₁,
            have h45b: σ₁ ⊨ P₁.instantiated_n, from env_translation_instantiated_n_valid σ₁_verified,
            have σ₁ ⊨ (prop.instantiated_n ↑H₁ ⋀ P₁.instantiated_n), from valid_env.and h45a h45b,
            have h45d: σ₁ ⊨ (↑H₁ ⋀ P₁).instantiated_n, from valid_env.instantiated_n_and this,

            have h46: σ₁ ⊨ P''.instantiated_p, from (
              have h47: Q₂' vy₁ = (↑H₁ ⋀ P₁.to_propctx ⋀ y₁ ≣ •) vy₁,
              from h44 ▸ rfl,

              have h48: (↑H₁ ⋀ P₁.to_propctx ⋀ y₁ ≣ •) vy₁
                      = (↑H₁ ⋀ P₁ ⋀ (y₁ ≣ •) vy₁), from propctx_apply_hpq,

              have ((y₁ ≣ •):propctx) vy₁ = (y₁ ≡ vy₁),
              by {
                change (propctx.apply (propctx.term (y₁ ≣ •)) vy₁ = ↑(y₁ ≡ vy₁)),
                unfold propctx.apply,
                change (↑(termctx.apply (termctx.binop binop.eq y₁ •) vy₁) = ↑(y₁ ≡ vy₁)),
                unfold termctx.apply,
                change (↑((term.to_termctx y₁) vy₁ ≡ vy₁) = ↑(↑y₁ ≡ vy₁)),
                rw[@unchanged_of_apply_termctx_without_hole y₁ vy₁]
              },

              have h49: Q₂' vy₁ = (↑H₁ ⋀ P₁ ⋀ y₁ ≡ vy₁), from eq.trans h47 (this ▸ h48),
              have ⊨ vy₁ ≡ vy₁, from valid.refl,
              have ⊨ (term.subst_env σ₁ y₁) ≡ vy₁, from h26.symm ▸ this,
              have h50: ⊨ (term.subst_env σ₁ y₁) ≡ (term.subst_env σ₁ vy₁),
              from (@term.subst_env.value σ₁ vy₁).symm ▸ this,
              have term.subst_env σ₁ (y₁ ≡ vy₁) = (term.subst_env σ₁ y₁ ≡ term.subst_env σ₁ vy₁),
              from term.subst_env.binop,
              have h51: ⊨ term.subst_env σ₁ (y₁ ≡ vy₁), from this.symm ▸ h50,
              have vc.subst_env σ₁ (y₁ ≡ vy₁) = vc.term (term.subst_env σ₁ (y₁ ≡ vy₁)),
              from vc.subst_env.term,
              have ⊨ vc.subst_env σ₁ (y₁ ≡ vy₁), from this.symm ▸ h51,
              have h52: σ₁ ⊨ y₁ ≡ vy₁, from this,
              have prop.erased_n (prop.term (y₁ ≡ vy₁)) = vc.term (y₁ ≡ vy₁), by unfold prop.erased_n,
              have h53: σ₁ ⊨ prop.erased_n (y₁ ≡ vy₁) , from this.symm ▸ h52,
              have h53b: closed_subst σ₁ (prop.term (y₁ ≡ vy₁)), from (
                assume z: var,
                assume : free_in_prop z (y₁ ≡ vy₁),
                have free_in_term z (y₁ ≡ vy₁), from free_in_prop.term.inv this,
                or.elim (free_in_term.binop.inv this) (
                  assume : free_in_term z y₁,
                  have z = y₁, from free_in_term.var.inv this,
                  have z ∈ σ₁, from this.symm ▸ y₁_in_σ₁,
                  show z ∈ σ₁.dom, from this
                ) (
                  assume : free_in_term z vy₁,
                  show z ∈ σ₁.dom, from absurd this free_in_term.value.inv
                )
              ),
              have closed_subst σ₁ (prop.term (y₁ ≡ vy₁)).instantiated_n,
              from instantiated_n_closed_subst_of_closed h53b,
              have σ₁ ⊨ prop.instantiated_n (y₁ ≡ vy₁), from valid_env.instantiated_n_of_erased_n this h53,
              have σ₁ ⊨ P₁.instantiated_n ⋀ prop.instantiated_n (y₁ ≡ vy₁),
              from valid_env.and h45b this,
              have σ₁ ⊨ (P₁ ⋀ y₁ ≡ vy₁).instantiated_n,
              from valid_env.instantiated_n_and this,
              have σ₁ ⊨ prop.instantiated_n ↑H₁ ⋀ (P₁ ⋀ y₁ ≡ vy₁).instantiated_n,
              from valid_env.and h45a this,
              have σ₁ ⊨ (↑H₁ ⋀ P₁ ⋀ y₁ ≡ vy₁).instantiated_n,
              from valid_env.instantiated_n_and this,
              have h54: σ₁ ⊨ (Q₂' vy₁).instantiated_n, from h49.symm ▸ this,

              have dominates_n σ₁ (Q₂' vy₁) (H'⋀ P'' ⋀ Q₂ vy₁), from (Q₂'_dom σ₁ vy₁).left,

              have h55: σ₁ ⊨ (↑H'⋀ P'' ⋀ Q₂ vy₁).instantiated_n,
              from dominates_n.elim this h54,

              have h56: FV (↑H'⋀ P'' ⋀ Q₂ vy₁) ⊆ FV (Q₂' vy₁), from (Q₂'_dom σ₁ vy₁).right,

              have closed_subst σ₁ P₁, from env_translation_closed_subst σ₁_verified,
              have h53c: closed_subst σ₁ (P₁ ⋀ y₁ ≡ vy₁), from prop.closed_subst.and this h53b,
              have closed ↑H₁, from call_history_closed H₁,
              have closed_subst σ₁ ↑H₁, from prop.closed_any_subst_of_closed this,
              have closed_subst σ₁ (↑H₁ ⋀ P₁ ⋀ y₁ ≡ vy₁), from prop.closed_subst.and this h53c,
              have h53d: closed_subst σ₁ (Q₂' vy₁), from h49.symm ▸ this,
              have closed_subst σ₁ (↑H'⋀ P'' ⋀ Q₂ vy₁), from (
                assume z: var,
                assume : z ∈ FV (↑H'⋀ P'' ⋀ Q₂ vy₁),
                have z ∈ FV (Q₂' vy₁), from set.mem_of_subset_of_mem h56 this,
                show z ∈ σ₁, from h53d this
              ),
              have closed_subst σ₁ (↑H'⋀ P'' ⋀ Q₂ vy₁).instantiated_p,
              from instantiated_p_closed_subst_of_closed this,

              have σ₁ ⊨ (↑H'⋀ P'' ⋀ Q₂ vy₁).instantiated_p,
              from valid_env.instantiated_p_of_instantiated_n this h55,
              have σ₁ ⊨ (P'' ⋀ Q₂ vy₁).instantiated_p,
              from (valid_env.and.elim (valid_env.instantiated_p_and_elim this)).right,
              show σ₁ ⊨ P''.instantiated_p,
              from (valid_env.and.elim (valid_env.instantiated_p_and_elim this)).left
            ),

            have env_equiv3: (∀z, z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]) →
                                       (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ] z = σ₁ z)),
            from env_equiv_of_translation_valid σ''_verified σ₁ h46,

            have fx_is_vₓ: (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]) fx = vₓ,
            from env.apply_of_vcgen σ''_verified,
            have fx_in_σ'': fx ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.same,
            have σ₁ fx = vₓ,
            from eq.trans (env_equiv3 fx fx_in_σ'').symm fx_is_vₓ,
            have h34: term.subst_env σ₁ fx = vₓ,
            from (term.subst_env.var.right vₓ).mp this,
            have fx_in_σ₁: fx ∈ σ₁,
            from env.contains_apply_equiv.right.mp (exists.intro vₓ this),

            have (σ'[f↦value.func f fx R S e' H' σ']) f = value.func f fx R S e' H' σ',
            from exists.elim (env.rest_verified σ''_verified) (λ_, env.apply_of_vcgen),
            have f_is_vf: (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]) f = value.func f fx R S e' H' σ',
            from env.apply_of_rest_apply this,
            have f_in_σ'': f ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]),
            from env.contains.rest env.contains.same,
            have σ₁ f = (value.func f fx R S e' H' σ'),
            from eq.trans (env_equiv3 f f_in_σ'').symm f_is_vf,
            have h35: term.subst_env σ₁ f = value.func f fx R S e' H' σ',
            from (term.subst_env.var.right (value.func f fx R S e' H' σ')).mp this,
            have f_in_σ₁: f ∈ σ₁,
            from env.contains_apply_equiv.right.mp (exists.intro (value.func f fx R S e' H' σ') this),

            have h36: σ₁ ⊨ (↑H'⋀ P'' ⋀ Q₂ (term.app f fx)).instantiated_n, from (
              have h37: Q₂' (term.app f fx) = (↑H₁ ⋀ P₁.to_propctx ⋀ y₁ ≣ •) (term.app f fx),
              from h44 ▸ rfl,

              have h38: (↑H₁ ⋀ P₁.to_propctx ⋀ y₁ ≣ •) (term.app f fx)
                      = (↑H₁ ⋀ P₁ ⋀ (y₁ ≣ •) (term.app f fx)), from propctx_apply_hpq,

              have ((y₁ ≣ •):propctx) (term.app f fx) = (y₁ ≡ term.app f fx),
              by {
                change (propctx.apply (propctx.term (y₁ ≣ •)) (term.app f fx) = (y₁ ≡ term.app f fx)),
                unfold propctx.apply,
                change (↑(termctx.apply (termctx.binop binop.eq y₁ •) (term.app f fx)) = ↑(y₁ ≡ term.app f fx)),
                unfold termctx.apply,
                change (↑((term.to_termctx y₁) (term.app ↑f ↑fx) ≡ term.app ↑f ↑fx) = ↑(↑y₁ ≡ term.app ↑f ↑fx)),
                rw[@unchanged_of_apply_termctx_without_hole y₁ (term.app f fx)]
              },

              have h39: Q₂' (term.app f fx) = (↑H₁ ⋀ P₁ ⋀ (y₁ ≡ term.app f fx)),
              from eq.trans h37 (this ▸ h38),

              have h40: σ₁ ⊨ y₁ ≡ term.app f fx, from (
                have h73: (R₁, H₂, σ₂[f₁↦value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂][x₁↦vx₁], e₁)
                ⟶* (R'₁, H₁, σ₁, exp.return y₁),
                from h65.symm ▸ h66.symm ▸ h67.symm ▸ h68.symm ▸ h69.symm ▸ h70.symm ▸ h71.symm ▸ h72.symm ▸ steps, 

                have ⊨ vy₁ ≡ term.app (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁,
                from valid.app h73 y_is_vy₁,
                have ⊨ vy₁ ≡ term.app (value.func f fx R S e' H' σ') vₓ,
                from h65 ▸ h66 ▸ h67 ▸ h68 ▸ h69 ▸ h70 ▸ h71 ▸ h72 ▸ this, 
                have h76: ⊨ (term.subst_env σ₁ y₁) ≡ term.app (term.subst_env σ₁ f) (term.subst_env σ₁ fx),
                from h26.symm ▸ h34.symm ▸ h35.symm ▸ this,
                have term.subst_env σ₁ (term.app f fx) = term.app (term.subst_env σ₁ f) (term.subst_env σ₁ fx),
                from term.subst_env.app,
                have h77: ⊨ term.subst_env σ₁ y₁ ≡ term.subst_env σ₁ (term.app f fx), from this.symm ▸ h76,
                have term.subst_env σ₁ (y₁ ≡ term.app f fx)
                   = (term.subst_env σ₁ y₁ ≡ term.subst_env σ₁ (term.app f fx)),
                from term.subst_env.binop,
                have h78: ⊨ term.subst_env σ₁ (y₁ ≡ term.app f fx), from this.symm ▸ h77,
                have vc.subst_env σ₁ (y₁ ≡ term.app f fx) = vc.term (term.subst_env σ₁ (y₁ ≡ term.app f fx)),
                from vc.subst_env.term,
                have ⊨ vc.subst_env σ₁ (y₁ ≡ term.app f fx), from this.symm ▸ h78,
                show σ₁ ⊨ y₁ ≡ term.app f fx, from this
              ),
              have prop.erased_n (prop.term (y₁ ≡ term.app f fx)) = vc.term (y₁ ≡ term.app f fx),
              by unfold prop.erased_n,
              have h41: σ₁ ⊨ prop.erased_n (y₁ ≡ term.app f fx) , from this.symm ▸ h40,
              have h42b: closed_subst σ₁ (prop.term (y₁ ≡ term.app f fx)), from (
                assume z: var,
                assume : free_in_prop z (y₁ ≡ term.app f fx),
                have free_in_term z (y₁ ≡ term.app f fx), from free_in_prop.term.inv this,
                or.elim (free_in_term.binop.inv this) (
                  assume : free_in_term z y₁,
                  have z = y₁, from free_in_term.var.inv this,
                  have z ∈ σ₁, from this.symm ▸ y₁_in_σ₁,
                  show z ∈ σ₁.dom, from this
                ) (
                  assume : free_in_term z (term.app f fx),
                  or.elim (free_in_term.app.inv this) (
                    assume : free_in_term z f,
                    have z = f, from free_in_term.var.inv this,
                    have z ∈ σ₁, from this.symm ▸ f_in_σ₁,
                    show z ∈ σ₁.dom, from this
                  ) (
                    assume : free_in_term z fx,
                    have z = fx, from free_in_term.var.inv this,
                    have z ∈ σ₁, from this.symm ▸ fx_in_σ₁,
                    show z ∈ σ₁.dom, from this
                  )
                )
              ),
              have closed_subst σ₁ (prop.term (y₁ ≡ term.app f fx)).instantiated_n,
              from instantiated_n_closed_subst_of_closed h42b,
              have σ₁ ⊨ prop.instantiated_n (y₁ ≡ term.app f fx), from valid_env.instantiated_n_of_erased_n this h41,
              have σ₁ ⊨ P₁.instantiated_n ⋀ prop.instantiated_n (y₁ ≡ term.app f fx),
              from valid_env.and h45b this,
              have σ₁ ⊨ (P₁ ⋀ y₁ ≡ term.app f fx).instantiated_n,
              from valid_env.instantiated_n_and this,
              have σ₁ ⊨ prop.instantiated_n ↑H₁ ⋀ (P₁ ⋀ y₁ ≡ term.app f fx).instantiated_n,
              from valid_env.and h45a this,
              have σ₁ ⊨ (↑H₁ ⋀ P₁ ⋀ y₁ ≡ term.app f fx).instantiated_n,
              from valid_env.instantiated_n_and this,
              have h43: σ₁ ⊨ (Q₂' (term.app f fx)).instantiated_n, from h39.symm ▸ this,

              have dominates_n σ₁ (Q₂' (term.app f fx)) (H'⋀ P'' ⋀ Q₂ (term.app f fx)),
              from (Q₂'_dom σ₁ (term.app f fx)).left,

              show σ₁ ⊨ (↑H'⋀ P'' ⋀ Q₂ (term.app f fx)).instantiated_n,
              from dominates_n.elim this h43
            ),

            have ∃Q', ⊢ (σ'[f↦value.func f fx R S e' H' σ']) : Q',
            from env.rest_verified σ''_verified,

            let ⟨Q', h90⟩ := this in
            
            have ∃Q₁ Q₂ Q₃,
              f ∉ σ' ∧
              f ∉ σ' ∧
              fx ∉ σ' ∧
              f ≠ fx ∧
              (⊢ σ' : Q₁) ∧
              (⊢ σ' : Q₂) ∧
              fx ∈ FV R.to_prop ∧
              FV R.to_prop ⊆ FV Q₂ ∪ { f, fx } ∧
              FV S.to_prop ⊆ FV Q₂ ∪ { f, fx } ∧
              (H' ⋀ Q₂ ⋀ spec.func f fx R S ⋀ R ⊢ e' : Q₃) ∧
              ⟪prop.implies (H' ⋀ Q₂ ⋀ spec.func f fx R S ⋀ R ⋀ Q₃ (term.app f fx)) S⟫ ∧
              (Q' = (Q₁ ⋀
                  ((f ≡ (value.func f fx R S e' H' σ')) ⋀
                  prop.subst_env (σ'[f↦value.func f fx R S e' H' σ'])
                  (prop.func f fx R (Q₃ (term.app f fx) ⋀ S))))),
            from env.vcgen.func.inv h90,

-- lemma vc.subst_env_equivalent_env {P: vc} {σ₁ σ₂: env}:
--   (∀z, z ∈ σ₁ → (σ₁ z = σ₂ z)) → closed_subst σ₁ P → (vc.subst_env σ₁ P = vc.subst_env σ₂ P) :=

            have h97: ⊨ vc.subst_env (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]) (Q₂ (term.app f fx)).instantiated_p,
            from sorry,

            have ⊨ vc.subst_env σ₁ S.to_prop.instantiated_p,
            from sorry,
            have h98: ⊨ vc.subst_env (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]) S.to_prop.instantiated_p,
            from sorry,
            have ⊨ vc.subst_env (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ])
                                (vc.and (Q₂ (term.app f fx)).instantiated_p S.to_prop.instantiated_p),
            from valid_env.and h97 h98,
            have (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ] ⊨ (Q₂ (term.app f fx)).instantiated_p ⋀
                                                                S.to_prop.instantiated_p),
            from this,
            have ⊨ vc.post (value.func f fx R S e' H' σ') vₓ,
            from valid.post.mp σ'_verified e'_verified this,
            have ⊨ vc.post (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁,
            from h65.symm ▸ h66.symm ▸ h67.symm ▸ h68.symm ▸ h69.symm ▸ h70.symm ▸ h71.symm ▸ h72.symm ▸ this, 
            have h56: ⊨ vc.post (term.subst_env σ₃ g) (term.subst_env σ₃ x),
            from h23.symm ▸ h24.symm ▸ h25.symm ▸ this,
            have vc.subst_env σ₃ (vc.post g x) = vc.post (term.subst_env σ₃ g) (term.subst_env σ₃ x),
            from vc.subst_env.post,
            have ⊨ vc.subst_env σ₃ (vc.post g x), from this.symm ▸ h56,
            show σ₃ ⊨ vc.post g x, from this
          ),

          have h79: σ₃ ⊨ y ≡ term.app g x, from (
            have h73: (R₁, H₂, σ₂[f₁↦value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂][x₁↦vx₁], e₁)
            ⟶* (R'₁, H₁, σ₁, exp.return y₁),
            from h65.symm ▸ h66.symm ▸ h67.symm ▸ h68.symm ▸ h69.symm ▸ h70.symm ▸ h71.symm ▸ h72.symm ▸ steps, 

            have ⊨ vy₁ ≡ term.app (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁,
            from valid.app h73 y_is_vy₁,
            have h76: ⊨ (term.subst_env σ₃ y) ≡ term.app (term.subst_env σ₃ g) (term.subst_env σ₃ x),
            from h23.symm ▸ h24.symm ▸ h25.symm ▸ this,
            have term.subst_env σ₃ (term.app g x) = term.app (term.subst_env σ₃ g) (term.subst_env σ₃ x),
            from term.subst_env.app,
            have h77: ⊨ term.subst_env σ₃ y ≡ term.subst_env σ₃ (term.app g x), from this.symm ▸ h76,
            have term.subst_env σ₃ (y ≡ term.app g x) = (term.subst_env σ₃ y ≡ term.subst_env σ₃ (term.app g x)),
            from term.subst_env.binop,
            have h78: ⊨ term.subst_env σ₃ (y ≡ term.app g x), from this.symm ▸ h77,
            have vc.subst_env σ₃ (y ≡ term.app g x) = vc.term (term.subst_env σ₃ (y ≡ term.app g x)),
            from vc.subst_env.term,
            have ⊨ vc.subst_env σ₃ (y ≡ term.app g x), from this.symm ▸ h78,
            show σ₃ ⊨ y ≡ term.app g x, from this
          ),

          show σ₃ ⊨ vc.post g x ⋀ y ≡ term.app g x, from valid_env.and h49 h79
        ),

        have h10p: ∀σ₃, dominates_p σ₃ ((P ⋀ P₃) ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)
                                       ((P ⋀ P₃) ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
        from λσ₃, dominates_p.same_left (
          assume P_P₃_valid: σ₃ ⊨ (P ⋀ P₃).instantiated_p,

          have P_valid: σ₃ ⊨ P.instantiated_p,
          from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_P₃_valid)).left,

          have env_equiv: (∀z, z ∈ σ → (σ z = σ₃ z)),
          from env_equiv_of_translation_valid σ_verified σ₃ P_valid,

          have env_equiv2: (∀z, z ∈ (σ[y↦vy₁]) → ((σ[y↦vy₁]) z = σ₃ z)),
          from env_equiv_of_translation_valid h5 σ₃ P_P₃_valid,

          have h_impl: (σ₃ ⊨ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁).instantiated_p)
                      → (σ₃ ⊨ (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x).instantiated_p), from (
            assume : σ₃ ⊨ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁).instantiated_p,

            have h49: σ₃ ⊨ vc.post g x ⋀ y ≡ term.app g x, from h10 σ₃ P_P₃_valid,

            have prop.erased_p (prop.post g x) = vc.post g x,
            by unfold prop.erased_p,

            have h50: σ₃ ⊨ (prop.post g x).erased_p ⋀ y ≡ term.app g x,
            from this.symm ▸ h49,

            have prop.erased_p (prop.term (y ≡ term.app g x)) = vc.term (y ≡ term.app g x),
            by unfold prop.erased_p,

            have h80: σ₃ ⊨ (prop.post g x).erased_p ⋀ prop.erased_p (y ≡ term.app g x),
            from this.symm ▸ h50,

            have prop.erased_p (prop.and (prop.post g x) (y ≡ term.app g x))
               = ((prop.post g x).erased_p ⋀ prop.erased_p (y ≡ term.app g x)),
            by unfold prop.erased_p,

            have h81: σ₃ ⊨ (prop.post g x ⋀ y ≡ term.app g x).erased_p,
            from this.symm ▸ h80,

            have prop.erased_p (prop.call g x) = vc.term value.true,
            by unfold prop.erased_p,
            have h82: σ₃ ⊨ prop.erased_p (prop.call g x), from this.symm ▸ valid_env.true,

            have h83: σ₃ ⊨ (prop.call g x).erased_p ⋀ (prop.post g x ⋀ y ≡ term.app g x).erased_p,
            from valid_env.and h82 h81,

            have prop.erased_p (prop.and (prop.call g x) (prop.post g x ⋀ y ≡ term.app g x))
               = ((prop.call g x).erased_p ⋀ (prop.post g x ⋀ y ≡ term.app g x).erased_p),
            by unfold prop.erased_p,

            have h84: σ₃ ⊨ (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x).erased_p, from this.symm ▸ h83,

            have quantifiers_p (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x) = ∅,
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

            have (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x).instantiated_p
               = (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x).erased_p,
            from instantiated_p_eq_erased_p_without_quantifiers this,
            show σ₃ ⊨ (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x).instantiated_p,
            from this.symm ▸ h84
          ),

          have h_calls: calls_p_subst σ₃ (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x)
                      ⊆ calls_p_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁), from (
            assume c: calltrigger,
            assume : c ∈ calls_p_subst σ₃ (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),

            show c ∈ calls_p_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁),
            from @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ₃)
                  (calls_p (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x))
                  (λa, a ∈ calls_p_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) c this (
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
                show calltrigger.subst σ₃ c' ∈ calls_p_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁),
                from h25.symm ▸ this
              ) (
                assume : c' ∈ calls_p (prop.post g x ⋀ y ≡ term.app g x),
                or.elim (prop.has_call_p.and.inv this) (
                  assume : c' ∈ calls_p (prop.post g x),
                  show calltrigger.subst σ₃ c' ∈ calls_p_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁),
                  from absurd this prop.has_call_p.post.inv
                ) (
                  assume : c' ∈ calls_p (y ≡ term.app g x),
                  show calltrigger.subst σ₃ c' ∈ calls_p_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁),
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

          show dominates_p σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)
                              (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
          from dominates_p.no_quantifiers h_impl h_calls h_quantifiers
        ),

        have h10n: ∀σ₃, dominates_n σ₃ ((P ⋀ P₃) ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)
                                       ((P ⋀ P₃) ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
        from λσ₃, dominates_n.same_left (
          assume P_P₃_valid: σ₃ ⊨ (P ⋀ P₃).instantiated_p,

          have P_valid: σ₃ ⊨ P.instantiated_p,
          from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_P₃_valid)).left,

          have env_equiv: (∀z, z ∈ σ → (σ z = σ₃ z)),
          from env_equiv_of_translation_valid σ_verified σ₃ P_valid,

          have env_equiv2: (∀z, z ∈ (σ[y↦vy₁]) → ((σ[y↦vy₁]) z = σ₃ z)),
          from env_equiv_of_translation_valid h5 σ₃ P_P₃_valid,

          have h_impl: (σ₃ ⊨ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁).instantiated_n)
                      → (σ₃ ⊨ (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x).instantiated_n), from (
            assume : σ₃ ⊨ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁).instantiated_n,

            have h49: σ₃ ⊨ vc.post g x ⋀ y ≡ term.app g x, from h10 σ₃ P_P₃_valid,

            have prop.erased_n (prop.post g x) = vc.post g x,
            by unfold prop.erased_n,

            have h50: σ₃ ⊨ (prop.post g x).erased_n ⋀ y ≡ term.app g x,
            from this.symm ▸ h49,

            have prop.erased_n (prop.term (y ≡ term.app g x)) = vc.term (y ≡ term.app g x),
            by unfold prop.erased_n,

            have h80: σ₃ ⊨ (prop.post g x).erased_n ⋀ prop.erased_n (y ≡ term.app g x),
            from this.symm ▸ h50,

            have prop.erased_n (prop.and (prop.post g x) (y ≡ term.app g x))
               = ((prop.post g x).erased_n ⋀ prop.erased_n (y ≡ term.app g x)),
            by unfold prop.erased_n,

            have h81: σ₃ ⊨ (prop.post g x ⋀ y ≡ term.app g x).erased_n,
            from this.symm ▸ h80,

            have prop.erased_n (prop.call g x) = vc.term value.true,
            by unfold prop.erased_n,
            have h82: σ₃ ⊨ prop.erased_n (prop.call g x), from this.symm ▸ valid_env.true,

            have h83: σ₃ ⊨ (prop.call g x).erased_n ⋀ (prop.post g x ⋀ y ≡ term.app g x).erased_n,
            from valid_env.and h82 h81,

            have prop.erased_n (prop.and (prop.call g x) (prop.post g x ⋀ y ≡ term.app g x))
               = ((prop.call g x).erased_n ⋀ (prop.post g x ⋀ y ≡ term.app g x).erased_n),
            by unfold prop.erased_n,

            have h84: σ₃ ⊨ (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x).erased_n, from this.symm ▸ h83,

            have closed_subst σ₃ (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x), from (

              have σ₃ g = (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂),
              from eq.trans (env_equiv g g_in_σ).symm g_is_func₁,
              have h23: g ∈ σ₃,
              from env.contains_apply_equiv.right.mp (exists.intro (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) this),

              have σ₃ x = vx₁,
              from eq.trans (env_equiv x x_in_σ).symm x_is_vx₁,
              have h24: x ∈ σ₃,
              from env.contains_apply_equiv.right.mp (exists.intro vx₁ this),

              have (σ[y↦vy₁]) y = vy₁, from env.apply_of_contains y_not_in_σ,
              have σ₃ y = vy₁,
              from eq.trans (env_equiv2 y env.contains.same).symm this,
              have h25: y ∈ σ₃,
              from env.contains_apply_equiv.right.mp (exists.intro vy₁ this),

              assume z: var,
              assume : z ∈ FV (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
              or.elim (free_in_prop.and.inv this) (
                assume : z ∈ FV (prop.call g x),
                or.elim (free_in_prop.call.inv this) (
                  assume : free_in_term z g,
                  have z = g, from free_in_term.var.inv this,
                  show z ∈ σ₃, from this.symm ▸ h23
                ) (
                  assume : free_in_term z x,
                  have z = x, from free_in_term.var.inv this,
                  show z ∈ σ₃, from this.symm ▸ h24
                )
              ) (
                assume : z ∈ FV (prop.post g x ⋀ y ≡ term.app g x),
                or.elim (free_in_prop.and.inv this) (
                  assume : z ∈ FV (prop.post g x ),
                  or.elim (free_in_prop.post.inv this) (
                    assume : free_in_term z g,
                    have z = g, from free_in_term.var.inv this,
                    show z ∈ σ₃, from this.symm ▸ h23
                  ) (
                    assume : free_in_term z x,
                    have z = x, from free_in_term.var.inv this,
                    show z ∈ σ₃, from this.symm ▸ h24
                  )
                ) (
                  assume : free_in_prop z (y ≡ term.app g x),
                  have free_in_term z (y ≡ term.app g x), from free_in_prop.term.inv this,
                  or.elim (free_in_term.binop.inv this) (
                    assume : free_in_term z y,
                    have z = y, from free_in_term.var.inv this,
                    show z ∈ σ₃, from this.symm ▸ h25
                  ) (
                    assume : free_in_term z (term.app g x),
                    or.elim (free_in_term.app.inv this) (
                      assume : free_in_term z g,
                      have z = g, from free_in_term.var.inv this,
                      show z ∈ σ₃, from this.symm ▸ h23
                    ) (
                      assume : free_in_term z x,
                      have z = x, from free_in_term.var.inv this,
                      show z ∈ σ₃, from this.symm ▸ h24
                    )
                  )
                )
              )
            ),

            have closed_subst σ₃ (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x).instantiated_n,
            from instantiated_n_closed_subst_of_closed this,

            show σ₃ ⊨ (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x).instantiated_n,
            from valid_env.instantiated_n_of_erased_n this h84
          ),

          have h_calls: calls_n_subst σ₃ (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x)
                      ⊆ calls_n_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁), from (
            assume c: calltrigger,
            assume : c ∈ calls_n_subst σ₃ (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),

            show c ∈ calls_n_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁),
            from @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ₃)
                  (calls_n (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x))
                  (λa, a ∈ calls_n_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) c this (
              assume c': calltrigger,
              assume : c' ∈ calls_n (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
              or.elim (prop.has_call_n.and.inv this) (
                assume : c' ∈ calls_n (prop.call g x),
                show calltrigger.subst σ₃ c' ∈ calls_n_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁),
                from absurd this prop.has_call_n.call.inv
              ) (
                assume : c' ∈ calls_n (prop.post g x ⋀ y ≡ term.app g x),
                or.elim (prop.has_call_n.and.inv this) (
                  assume : c' ∈ calls_n (prop.post g x),
                  show calltrigger.subst σ₃ c' ∈ calls_n_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁),
                  from absurd this prop.has_call_n.post.inv
                ) (
                  assume : c' ∈ calls_n (y ≡ term.app g x),
                  show calltrigger.subst σ₃ c' ∈ calls_n_subst σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁),
                  from absurd this prop.has_call_n.term.inv
                )
              )
            )
          ),

          have h_quantifiers: quantifiers_n (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x) = ∅,
          from set.eq_empty_of_forall_not_mem (
            assume q: callquantifier,
            assume : q ∈ quantifiers_n (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
            or.elim (prop.has_quantifier_n.and.inv this) (
              assume : q ∈ quantifiers_n (prop.call g x),
              show «false», from prop.has_quantifier_n.call.inv this
            ) (
              assume : q ∈ quantifiers_n (prop.post g x ⋀ y ≡ term.app g x),
              or.elim (prop.has_quantifier_n.and.inv this) (
                assume : q ∈ quantifiers_n (prop.post g x),
                show «false», from prop.has_quantifier_n.post.inv this
              ) (
                assume : q ∈ quantifiers_n (y ≡ term.app g x),
                show «false», from prop.has_quantifier_n.term.inv this
              )
            )
          ),

          show dominates_n σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)
                              (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
          from dominates_n.no_quantifiers h_impl h_calls h_quantifiers
        ),

        have h11: ∀σ, dominates_p σ (R' ⋀ (H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃)
                                    (R' ⋀ H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
        from (
          assume σ₃: env,
          dominates_p.same_left (
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

            have h15: dominates_p σ₃ ((↑H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁) ⋀ P ⋀ P₃)
                                   (↑H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P ⋀ P₃),
            from dominates_p.and_assoc.symm,

            have h16: dominates_p σ₃ (↑H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P ⋀ P₃)
                                   (↑H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
            from dominates_p.same_left (
              assume : σ₃ ⊨ prop.instantiated_p ↑H,

              have h17: dominates_p σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P ⋀ P₃)
                                     ((P ⋀ P₃) ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁),
              from dominates_p.and_symm,

              have h18: dominates_p σ₃ ((P ⋀ P₃) ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)
                                     ((P ⋀ P₃) ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
              from h10p σ₃,

              have h19: dominates_p σ₃ ((P ⋀ P₃) ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x)
                                     ((P₃ ⋀ P) ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
              from dominates_p.same_right (λ_, dominates_p.and_symm),

              have h20: dominates_p σ₃ ((P₃ ⋀ P) ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x)
                                     (P₃ ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
              from dominates_p.and_assoc.symm,

              have dominates_p σ₃ (P₃ ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x)
                                ((P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x) ⋀ P₃),
              from dominates_p.and_symm,

              have h21: dominates_p σ₃ (P₃ ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x)
                                     (P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
              from dominates_p.and_elim_left this,

              show dominates_p σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ P ⋀ P₃)
                                (P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
              from dominates_p.trans h17 (dominates_p.trans h18 (dominates_p.trans h19 (dominates_p.trans h20 h21)))
            ),

            have dominates_p σ₃ ((↑H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁) ⋀ P ⋀ P₃)
                              (↑H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
            from dominates_p.trans h15 h16,
            show dominates_p σ₃ (↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃)
                              (↑H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
            from h13.symm ▸ this
          )
        ),
                       
        have h12: R' ⋀ (H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃ ⊢ e : Q₃,
        from strengthen_exp cont (R' ⋀ (H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ P ⋀ P₃) h9 h11,

        have h13: ⊢ₛ (R', H · call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁, σ[y↦vy₁], e)
                  : ↑(H · call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ ↑(P ⋀ P₃) ⋀ Q₃,
        from stack.vcgen.top h5 h6 h8 h12,

        have h14: ∀σ₃ t,
          dominates_n σ₃ ((↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ ↑(P ⋀ P₃) ⋀ Q₃) t)
                       ((↑H ⋀ ↑P⋀ propctx.exis y
                           (↑(prop.call ↑g ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t),
        from (
          assume σ₃: env,
          assume t: term,

          have dominates_n σ₃ ((P ⋀ P₃) ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)
                            ((P ⋀ P₃) ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x),
          from h10n σ₃,

          have dominates_n σ₃ ((P ⋀ P₃) ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁) 
                            (((P ⋀ P₃) ⋀ prop.call g x) ⋀ prop.post g x ⋀ y ≡ term.app g x),
          from dominates_n.trans this dominates_n.and_assoc,

          have dominates_n σ₃ ((P ⋀ P₃) ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁) 
                            ((((P ⋀ P₃) ⋀ prop.call g x) ⋀ prop.post g x) ⋀ y ≡ term.app g x),
          from dominates_n.trans this dominates_n.and_assoc,

          have dominates_n σ₃ (((P ⋀ P₃) ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁) ⋀ Q₃ t) 
                            (((((P ⋀ P₃) ⋀ prop.call g x) ⋀ prop.post g x) ⋀ y ≡ term.app g x) ⋀ Q₃ t),
          from dominates_n.same_right (λ_, this),

          have dominates_n σ₃ (((P ⋀ P₃) ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁) ⋀ Q₃ t) 
                            ((((P ⋀ P₃) ⋀ prop.call g x) ⋀ prop.post g x) ⋀ y ≡ term.app g x ⋀ Q₃ t),

          from dominates_n.trans this dominates_n.and_assoc.symm,

          have dominates_n σ₃ (((P ⋀ P₃) ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁) ⋀ Q₃ t) 
                            (((P ⋀ P₃) ⋀ prop.call g x) ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t),
          from dominates_n.trans this dominates_n.and_assoc.symm,

          have dominates_n σ₃ (((P ⋀ P₃) ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁) ⋀ Q₃ t) 
                            ((P ⋀ P₃) ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t),
          from dominates_n.trans this dominates_n.and_assoc.symm,

          have dominates_n σ₃ ((P ⋀ P₃) ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ Q₃ t) 
                            ((P ⋀ P₃) ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t),
          from dominates_n.trans dominates_n.and_assoc this,

          have dominates_n σ₃ ((P ⋀ P₃) ⋀ Q₃ t ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)
                            ((P ⋀ P₃) ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t),
          from dominates_n.trans (dominates_n.same_left (λ_, dominates_n.and_symm)) this,

          have dominates_n σ₃ (((P ⋀ P₃) ⋀ Q₃ t) ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)
                            ((P ⋀ P₃) ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t),
          from dominates_n.trans dominates_n.and_assoc.symm this,

          have dominates_n σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ (P ⋀ P₃) ⋀ Q₃ t)
                            ((P ⋀ P₃) ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t),
          from dominates_n.trans dominates_n.and_symm this,

          have dominates_n σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ (P ⋀ P₃) ⋀ Q₃ t)
                            ((P₃ ⋀ P) ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t),
          from dominates_n.trans this (dominates_n.same_right (λ_, dominates_n.and_symm)),

          have dominates_n σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ (P ⋀ P₃) ⋀ Q₃ t)
                            (P₃ ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t),
          from dominates_n.trans this dominates_n.and_assoc.symm,

          have h17: dominates_n σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ (P ⋀ P₃) ⋀ Q₃ t)
                                 (P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t),
          from dominates_n.and_elim_right this,

          have dominates_n σ₃ (P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t)
                            (P ⋀ prop.exis y (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t)),
          from dominates_n.same_left (λ_, dominates_n.exis),
          have h18: dominates_n σ₃ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ (P ⋀ P₃) ⋀ Q₃ t)
                                 (P ⋀ prop.exis y (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t)),
          from dominates_n.trans h17 this,

          have h19: dominates_n σ₃ (↑H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ (P ⋀ P₃) ⋀ Q₃ t)
                                 (↑H ⋀ P ⋀ prop.exis y (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t)),
          from dominates_n.same_left (λ_, h18),

          have dominates_n σ₃ ((↑H ⋀ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t)
                            (↑H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁ ⋀ (P ⋀ P₃) ⋀ Q₃ t),
          from dominates_n.and_assoc.symm,
          have h20: dominates_n σ₃ ((↑H ⋀ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t)
                                 (↑H ⋀ P ⋀ prop.exis y (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t)),
          from dominates_n.trans this h19,

          have h21a: (prop.call g x).to_propctx t = prop.call g x, from unchanged_of_apply_propctx_without_hole,
          have h21b: (prop.post g x).to_propctx t = prop.post g x, from unchanged_of_apply_propctx_without_hole,
          have h21c: (prop.term (y ≡ term.app g x)).to_propctx t = prop.term (y ≡ term.app g x),
          from unchanged_of_apply_propctx_without_hole,

          have (propctx.exis y (↑(prop.call ↑g ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t
              = prop.exis y (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t),
          by calc
               (propctx.exis y (↑(prop.call ↑g ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t
             = propctx.apply (propctx.exis y (↑(prop.call g x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) t : rfl
         ... = prop.exis y (propctx.apply (↑(prop.call g x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃) t)
                                   : by unfold propctx.apply
         ... = prop.exis y (propctx.apply (propctx.and ↑(prop.call g x)
                                                       (↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) t) : rfl
         ... = prop.exis y (propctx.apply ↑(prop.call g x) t ⋀
                            propctx.apply (↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃) t) : by unfold propctx.apply
         ... = prop.exis y ((prop.call g x).to_propctx t ⋀
                            propctx.apply (↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃) t) : rfl
         ... = prop.exis y (prop.call g x ⋀
                            propctx.apply (↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃) t)
                                  : by rw[h21a]
         ... = prop.exis y (prop.call g x ⋀
                            propctx.apply (propctx.and ↑(prop.post g x) (↑(y ≡ term.app g x) ⋀ Q₃)) t) : rfl
         ... = prop.exis y (prop.call g x ⋀
                            propctx.apply ↑(prop.post g x) t ⋀ propctx.apply (↑(y ≡ term.app g x) ⋀ Q₃) t)
                                   : by unfold propctx.apply
         ... = prop.exis y (prop.call g x ⋀
                            (prop.post g x).to_propctx t ⋀ propctx.apply (↑(y ≡ term.app g x) ⋀ Q₃) t)
                                   : rfl
         ... = prop.exis y (prop.call g x ⋀
                            prop.post g x ⋀ propctx.apply (↑(y ≡ term.app g x) ⋀ Q₃) t)
                                   : by rw[h21b]
         ... = prop.exis y (prop.call g x ⋀
                            prop.post g x ⋀ propctx.apply (propctx.and ↑(prop.term (y ≡ term.app g x)) Q₃) t)
                                   : rfl
         ... = prop.exis y (prop.call g x ⋀
                            prop.post g x ⋀ propctx.apply ↑(prop.term (y ≡ term.app g x)) t ⋀ propctx.apply Q₃ t)
                                   : by unfold propctx.apply
         ... = prop.exis y (prop.call g x ⋀
                            prop.post g x ⋀ (prop.term (y ≡ term.app g x)).to_propctx t ⋀ propctx.apply Q₃ t)
                                   : rfl
         ... = prop.exis y (prop.call g x ⋀
                            prop.post g x ⋀ prop.term (y ≡ term.app g x) ⋀ propctx.apply Q₃ t)
                                   : by rw[h21c],

          have h21: dominates_n σ₃ ((↑H ⋀ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t)
                    (↑H ⋀ P⋀ (propctx.exis y
                       (↑(prop.call ↑g ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t),
          from this.symm ▸ h20,

          have ((↑H ⋀ ↑P⋀ propctx.exis y
                          (↑(prop.call ↑g ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t)
             = (↑H ⋀ P⋀ (propctx.exis y
                          (↑(prop.call ↑g ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t),
          from propctx_apply_hpq,

          have h22: dominates_n σ₃ ((↑H ⋀ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t)
                            ((↑H ⋀ ↑P⋀ propctx.exis y
                               (↑(prop.call ↑g ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t),
          from this.symm ▸ h21,

          have ((↑(↑H ⋀ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) ⋀ ↑(P ⋀ P₃) ⋀ Q₃) t)
             = ((↑H ⋀ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t),
          from propctx_apply_hpq,

          have h23: dominates_n σ₃ ((↑(↑H ⋀ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) ⋀ ↑(P ⋀ P₃) ⋀ Q₃) t)
                                 ((↑H ⋀ ↑P⋀ propctx.exis y
                                   (↑(prop.call ↑g ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t),
          from this.symm ▸ h22,

          have calls_to_prop (H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁)
             = (calls_to_prop H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁),
          by unfold calls_to_prop,
          have ↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) = (↑H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁),
          from this,

          show dominates_n σ₃ ((↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ ↑(P ⋀ P₃) ⋀ Q₃) t)
                       ((↑H ⋀ ↑P⋀ propctx.exis y
                           (↑(prop.call ↑g ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t),
          from this.symm ▸ h23
        ),
        exists.intro (↑(H · call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ ↑(P ⋀ P₃) ⋀ Q₃) ⟨h13, h14⟩

      }
    }
  end
