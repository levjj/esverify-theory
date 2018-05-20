import .definitions3 .strengthening .vcgen

lemma env_implies_rest {P: prop} {σ: env} {x: var} {v: value}:
      (⊩ (σ[x↦v]) : P) → (∃Q, (⊩ σ : Q) ∧ ∀σ', σ' ⊨ vc.implies P.to_vc Q.to_vc) :=
  assume σ_verified: ⊩ (σ[x↦v]) : P,
  begin
    cases σ_verified,
    case env.dvcgen.tru Q _ σ_verified ih { from
      have ∀σ', σ' ⊨ vc.implies (prop.and Q (x ≡ value.true)).to_vc Q.to_vc,
      from λσ', vc.implies.of_and_left,
      show ∃(Q_1 : prop), (⊩ σ : Q_1) ∧ ∀σ', σ' ⊨ vc.implies (prop.and Q (x ≡ value.true)).to_vc Q_1.to_vc,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.dvcgen.fls Q _ σ_verified { from
      have ∀σ', σ' ⊨ vc.implies (prop.and Q (x ≡ value.false)).to_vc Q.to_vc,
      from λσ', vc.implies.of_and_left,
      show ∃(Q_1 : prop), (⊩ σ : Q_1) ∧ ∀σ', σ' ⊨ vc.implies (prop.and Q (x ≡ value.false)).to_vc Q_1.to_vc,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.dvcgen.num n Q _ σ_verified { from
      have ∀σ', σ' ⊨ vc.implies (prop.and Q (x ≡ value.num n)).to_vc Q.to_vc,
      from λσ', vc.implies.of_and_left,
      show ∃(Q_1 : prop), (⊩ σ : Q_1) ∧ ∀σ', σ' ⊨ vc.implies (prop.and Q (x ≡ value.num n)).to_vc Q_1.to_vc,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.dvcgen.func σ₂ f fx R S e Q Q₂ Q₃ x_not_in_σ f_not_in_σ₂
         fx_not_in_σ₂ f_neq_fx σ₁_verified σ₂_verified fx_in_R fv_R fv_S e_verified func_vc { from
      let funcp := prop.subst_env (σ₂[f↦value.func f fx R S e σ₂])
                                  (prop.func f fx R (Q₃ (term.app f fx) ⋀ S)) in
      have ∀σ', σ' ⊨ vc.implies (Q ⋀ x ≡ value.func f fx R S e σ₂ ⋀ funcp).to_vc Q.to_vc,
      from λσ', vc.implies.of_and_left,
      show ∃Q_1, (⊩ σ : Q_1) ∧
                 ∀σ', σ' ⊨ vc.implies (prop.and Q ((x ≡ (value.func f fx R S e σ₂)) ⋀ funcp)).to_vc Q_1.to_vc,
      from exists.intro Q ⟨σ₁_verified, this⟩
    }
  end

/-

lemma no_calls_in_env_translation {P: prop} {σ: env}: (⊩ σ : P) → (calls_p P = ∅) :=
  assume env_verified: ⊩ σ : P,
  show calls_p P = ∅, by begin
    apply set.eq_empty_of_forall_not_mem,
    intro c,
    intro c_in_calls_p_P,
    induction env_verified,
    case env.dvcgen.empty {
      cases c_in_calls_p_P
    },
    case env.dvcgen.tru σ' y Q _ _ ih { from
      or.elim (prop.has_call_p.and.inv c_in_calls_p_P) (
        assume : c ∈ calls_p Q,
        show «false», from ih this
      ) (
        assume : c ∈ calls_p (y ≡ value.true),
        show «false», from prop.has_call_p.term.inv this
      )
    },
    case env.dvcgen.fls σ' y Q _ _ ih { from
      or.elim (prop.has_call_p.and.inv c_in_calls_p_P) (
        assume : c ∈ calls_p Q,
        show «false», from ih this
      ) (
        assume : c ∈ calls_p (y ≡ value.false),
        show «false», from prop.has_call_p.term.inv this
      )
    },
    case env.dvcgen.num n σ' y Q _ _ ih { from
      or.elim (prop.has_call_p.and.inv c_in_calls_p_P) (
        assume : c ∈ calls_p Q,
        show «false», from ih this
      ) (
        assume : c ∈ calls_p (y ≡ value.num n),
        show «false», from prop.has_call_p.term.inv this
      )
    },
    case env.dvcgen.func f σ₂ σ₁ g gx R S e H Q₁ Q₂ Q₃ _ _ _ _ _ _ _ fv_R fv_S e_verified _ ih₁ ih₂ { from
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

-/

lemma env_equiv_of_translation_valid {σ: env} {P: prop}:
      (⊩ σ: P) → ∀σ', (σ' ⊨ P.to_vc) → (∀x, x ∈ σ → (σ x = σ' x)) :=
  assume σ_verified: ⊩ σ: P,
  assume σ': env,
  assume P_valid: σ' ⊨ P.to_vc,
  assume x: var,
  assume x_in_σ: x ∈ σ,
  begin
    induction σ_verified,

    case env.dvcgen.empty {
      cases x_in_σ
    },

    case env.dvcgen.tru σ'' y Q _ _ ih {
      by_cases (y = x ∧ option.is_none (env.apply σ'' x)) with h,

      have h1: σ' ⊨ prop.to_vc (prop.term (y ≡ value.true)),
      from (valid_env.to_vc_and.elim P_valid).right,
      unfold prop.to_vc at h1,

      have h2: (σ' y = value.true), from valid_env.subst_of_eq h1,
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
      
      have h1: σ' ⊨ prop.to_vc Q,
      from (valid_env.to_vc_and.elim P_valid).left,
      from ih h1 a_3,

      have h1: σ' ⊨ prop.to_vc Q,
      from (valid_env.to_vc_and.elim P_valid).left,
      have h2, from option.some_iff_not_none.mpr a_2,
      have h4, from option.is_some_iff_exists.mp h2,
      have h5, from env.contains_apply_equiv.right.mp h4,
      from ih h1 h5
    },

    case env.dvcgen.fls σ'' y Q _ _ ih {
      by_cases (y = x ∧ option.is_none (env.apply σ'' x)) with h,

      have h1: σ' ⊨ prop.to_vc (y ≡ value.false),
      from (valid_env.to_vc_and.elim P_valid).right,
      have h2: (σ' y = value.false), from valid_env.subst_of_eq h1,
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
      
      have h1: σ' ⊨ prop.to_vc Q,
      from (valid_env.to_vc_and.elim P_valid).left,
      from ih h1 a_3,

      have h1: σ' ⊨ prop.to_vc Q,
      from (valid_env.to_vc_and.elim P_valid).left,
      have h2, from option.some_iff_not_none.mpr a_2,
      have h4, from option.is_some_iff_exists.mp h2,
      have h5, from env.contains_apply_equiv.right.mp h4,
      from ih h1 h5
    },

    case env.dvcgen.num n σ'' y Q _ _ ih {
      by_cases (y = x ∧ option.is_none (env.apply σ'' x)) with h,

      have h1: σ' ⊨ prop.to_vc (y ≡ value.num n),
      from (valid_env.to_vc_and.elim P_valid).right,
      have h2: (σ' y = value.num n), from valid_env.subst_of_eq h1,
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
      
      have h1: σ' ⊨ prop.to_vc Q,
      from (valid_env.to_vc_and.elim P_valid).left,
      from ih h1 a_3,

      have h1: σ' ⊨ prop.to_vc Q,
      from (valid_env.to_vc_and.elim P_valid).left,
      have h2, from option.some_iff_not_none.mpr a_2,
      have h4, from option.is_some_iff_exists.mp h2,
      have h5, from env.contains_apply_equiv.right.mp h4,
      from ih h1 h5
    },

    case env.dvcgen.func f σ₂ σ₁ g gx R S e Q₁ Q₂ Q₃ _ _ _ _ _ _ _ fv_R fv_S e_verified _ ih₁ ih₂ {
      by_cases (f = x ∧ option.is_none (env.apply σ₁ x)) with h,
      have h0, from (valid_env.to_vc_and.elim P_valid).right,
      have h1: σ' ⊨ prop.to_vc (f ≡ value.func g gx R S e σ₂),
      from (valid_env.to_vc_and.elim h0).left,
      have h2: (σ' f = value.func g gx R S e σ₂), from valid_env.subst_of_eq h1,
      change (env.apply (σ₁[f↦value.func g gx R S e σ₂]) x = σ' x),
      unfold env.apply,
      simp[h],
      rw[←h.left],
      from h2.symm,

      change (env.apply (σ₁[f↦value.func g gx R S e σ₂]) x = σ' x),
      unfold env.apply,
      simp[h],

      cases not_and_distrib.mp h,
      cases env.contains.inv x_in_σ,
      have : (f ≠ x), from a_7,
      have : (x ≠ f), from this.symm,
      contradiction,
      
      have h1: σ' ⊨ prop.to_vc Q₁,
      from (valid_env.to_vc_and.elim P_valid).left,
      from ih₁ h1 a_8,

      have h1: σ' ⊨ prop.to_vc Q₁,
      from (valid_env.to_vc_and.elim P_valid).left,
      have h2, from option.some_iff_not_none.mpr a_7,
      have h4, from option.is_some_iff_exists.mp h2,
      have h5, from env.contains_apply_equiv.right.mp h4,
      from ih₁ h1 h5
    }
  end

lemma propctx_apply_pq {P: prop} {Q: propctx} {t: term}: (↑P ⋀ Q) t = (P ⋀ Q t) :=
  have h1: P.to_propctx t = P, from unchanged_of_apply_propctx_without_hole,
  show (↑P ⋀ Q) t = (P ⋀ Q t), by calc
  (↑P ⋀ Q) t = propctx.apply (propctx.and ↑P Q) t : rfl
         ... = (propctx.apply ↑P t ⋀ propctx.apply Q t) : by unfold propctx.apply
         ... = (P.to_propctx t ⋀ propctx.apply Q t) : rfl
         ... = (P ⋀ propctx.apply Q t) : by rw[h1]

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

lemma free_in_prop.apply_propctx_exis {P₁: prop} {Q: propctx} {x: var} {t: term} {S: set var}:
      FV P₁ ⊆ (S ∪ set.insert x ∅) → FV ((propctx.exis x (P₁ ⋀ Q)) t) ⊆ S ∪ FV (Q t) :=
  
  assume h0: FV P₁ ⊆ S ∪ set.insert x ∅,
  have h1: P₁.to_propctx t = P₁, from unchanged_of_apply_propctx_without_hole,

  have ((propctx.exis x (P₁ ⋀ Q)) t) = prop.exis x (P₁ ⋀ Q t),
  by calc
        (propctx.exis x (↑P₁ ⋀ Q)) t
      = propctx.apply (propctx.exis x (↑P₁ ⋀ Q)) t : rfl
  ... = prop.exis x (propctx.apply (↑P₁ ⋀ Q) t) : by unfold propctx.apply
  ... = prop.exis x (propctx.apply (propctx.and ↑P₁ Q) t) : rfl
  ... = prop.exis x (propctx.apply ↑P₁ t ⋀ propctx.apply Q t) : by unfold propctx.apply
  ... = prop.exis x (P₁.to_propctx t ⋀ propctx.apply Q t) : rfl
  ... = prop.exis x (P₁ ⋀ propctx.apply Q t) : by rw[h1],

  have h2: FV ((propctx.exis x (P₁ ⋀ Q)) t) ⊆ FV (prop.exis x (P₁ ⋀ Q t)),
  from @eq.subst prop (λa, FV a ⊆ FV (prop.exis x (P₁ ⋀ Q t))) (prop.exis x (P₁ ⋀ Q t))
       ((propctx.exis x (P₁ ⋀ Q)) t) this.symm (set.subset.refl (FV (prop.exis x (P₁ ⋀ Q t)))),
  have h3: FV (prop.exis x (P₁ ⋀ Q t)) ⊆ S ∪ FV (Q t), from (
    assume z: var,
    assume : z ∈ FV (prop.exis x (P₁ ⋀ Q t)),
    have z_neq_x: z ≠ x, from (free_in_prop.exis.inv this).left,
    have z ∈ FV (P₁ ⋀ Q t), from (free_in_prop.exis.inv this).right,
    or.elim (free_in_prop.and.inv this) (
      assume : z ∈ FV P₁,
      have z ∈ (S ∪ set.insert x ∅), from set.mem_of_subset_of_mem h0 this,
      or.elim (set.mem_or_mem_of_mem_union this) (
        assume : z ∈ S,
        show z ∈ S ∪ FV (Q t), from set.mem_union_left (FV (Q t)) this
      ) (
        assume : z ∈ set.insert x ∅,
        have z = x, from set.eq_of_mem_singleton this,
        show z ∈ S ∪ FV (Q t), from absurd this z_neq_x
      )
    ) (
      assume : z ∈ FV (Q t),
      show z ∈ S ∪ FV (Q t), from set.mem_union_right S this
    )
  ),
  show FV ((propctx.exis x (P₁ ⋀ Q)) t) ⊆ S ∪ FV (Q t), 
  from set.subset.trans h2 h3

lemma vc.implies.apply_propctx_exis {P₁ P₂: prop} {Q: propctx} {x: var} {t: term} {σ: env}:
      (σ ⊨ vc.implies P₁.to_vc P₂.to_vc) → σ ⊨ vc.implies (P₁ ⋀ Q t).to_vc ((propctx.exis x (P₂ ⋀ Q)) t).to_vc :=
  
  assume h0: σ ⊨ vc.implies P₁.to_vc P₂.to_vc,
  have h1: P₂.to_propctx t = P₂, from unchanged_of_apply_propctx_without_hole,

  have ((propctx.exis x (P₂ ⋀ Q)) t) = prop.exis x (P₂ ⋀ Q t),
  by calc
        (propctx.exis x (↑P₂ ⋀ Q)) t
      = propctx.apply (propctx.exis x (↑P₂ ⋀ Q)) t : rfl
  ... = prop.exis x (propctx.apply (↑P₂ ⋀ Q) t) : by unfold propctx.apply
  ... = prop.exis x (propctx.apply (propctx.and ↑P₂ Q) t) : rfl
  ... = prop.exis x (propctx.apply ↑P₂ t ⋀ propctx.apply Q t) : by unfold propctx.apply
  ... = prop.exis x (P₂.to_propctx t ⋀ propctx.apply Q t) : rfl
  ... = prop.exis x (P₂ ⋀ propctx.apply Q t) : by rw[h1],

  have h2: σ ⊨ vc.implies (prop.exis x (P₂ ⋀ propctx.apply Q t)).to_vc ((propctx.exis x (P₂ ⋀ Q)) t).to_vc,
  from this ▸ vc.implies.self,
  have h3: σ ⊨ vc.implies (P₁ ⋀ Q t).to_vc (P₂ ⋀ Q t).to_vc,
  from vc.implies.same_right (λ_, h0),
  have h4: σ ⊨ vc.implies (P₂ ⋀ Q t).to_vc (prop.exis x (P₂ ⋀ Q t)).to_vc,
  from vc.implies.exis,
  show σ ⊨ vc.implies (P₁ ⋀ Q t).to_vc ((propctx.exis x (P₂ ⋀ Q)) t).to_vc,
  from vc.implies.trans (vc.implies.trans h3 h4) h2

lemma free_dominates_helper {R: spec} {P P₁ P₂: prop} {Q: propctx} {x: var}:
      (∀σ, (σ ⊨ P.to_vc) → σ ⊨ vc.implies P₁.to_vc P₂.to_vc) →
      (∀σ, (σ ⊨ P.to_vc) → σ ⊨ vc.implies P₁.to_vc P₂.to_vc) →
      (FV P₁ = set.insert x ∅) → 
      (x ∈ FV P₂) → 
      (FV P₂ ⊆ FV P ∪ set.insert x ∅) → 
      (FV (↑R ⋀ P ⋀ P₁) = FV ((↑R ⋀ P) ⋀ P₂)) ∧
      (∀σ, σ ⊨ vc.implies (↑R ⋀ P ⋀ P₁).to_vc ((↑R ⋀ P) ⋀ P₂).to_vc) ∧
      (∀σ t, σ ⊨ vc.implies ((↑(P ⋀ P₁) ⋀ Q) t).to_vc ((↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) t).to_vc) ∧
      (∀v: value, FV ((↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) v) ⊆ FV ((↑(P ⋀ P₁) ⋀ Q) v)) :=
  assume h1: ∀σ, (σ ⊨ P.to_vc) → σ ⊨ vc.implies P₁.to_vc P₂.to_vc,
  assume h2: ∀σ, (σ ⊨ P.to_vc) → σ ⊨ vc.implies P₁.to_vc P₂.to_vc,
  assume h3a: FV P₁ = set.insert x ∅,
  assume h3b: x ∈ FV P₂,
  assume h3c: FV P₂ ⊆ FV P ∪ set.insert x ∅,

  have h4a: FV (↑R ⋀ P ⋀ P₁) = FV (↑R ⋀ P ⋀ P₂), from set.eq_of_subset_of_subset (
    assume z: var,
    assume : z ∈ FV (↑R ⋀ P ⋀ P₁),
    or.elim (free_in_prop.and.inv this) (
      assume : free_in_prop z R,
      show z ∈ FV (↑R ⋀ P ⋀ P₂), from free_in_prop.and₁ this
    ) (
      assume : z ∈ FV (P ⋀ P₁),
      or.elim (free_in_prop.and.inv this) (
        assume : z ∈ FV P,
        have z ∈ FV (P ⋀ P₂), from free_in_prop.and₁ this,
        show z ∈ FV (↑R ⋀ P ⋀ P₂), from free_in_prop.and₂ this
      ) (
        assume : z ∈ FV P₁,
        have z ∈ set.insert x ∅, from h3a ▸ this,
        have z = x, from set.eq_of_mem_singleton this,
        have z ∈ FV P₂, from this.symm ▸ h3b,
        have z ∈ FV (P ⋀ P₂), from free_in_prop.and₂ this,
        show z ∈ FV (↑R ⋀ P ⋀ P₂), from free_in_prop.and₂ this
      )
    )
  ) (
    assume z: var,
    assume : z ∈ FV (↑R ⋀ P ⋀ P₂),
    or.elim (free_in_prop.and.inv this) (
      assume : free_in_prop z R,
      show z ∈ FV (↑R ⋀ P ⋀ P₁), from free_in_prop.and₁ this
    ) (
      assume : z ∈ FV (P ⋀ P₂),
      or.elim (free_in_prop.and.inv this) (
        assume : z ∈ FV P,
        have z ∈ FV (P ⋀ P₁), from free_in_prop.and₁ this,
        show z ∈ FV (↑R ⋀ P ⋀ P₁), from free_in_prop.and₂ this
      ) (
        assume : z ∈ FV P₂,
        have z ∈ FV P ∪ set.insert x ∅, from set.mem_of_subset_of_mem h3c this,
        or.elim (set.mem_or_mem_of_mem_union this) (
          assume : z ∈ FV P,
          have z ∈ FV (P ⋀ P₁), from free_in_prop.and₁ this,
          show z ∈ FV (↑R ⋀ P ⋀ P₁), from free_in_prop.and₂ this
        ) (
          assume : z ∈ set.insert x ∅,
          have z ∈ FV P₁, from h3a.symm ▸ this,
          have z ∈ FV (P ⋀ P₁), from free_in_prop.and₂ this,
          show z ∈ FV (↑R ⋀ P ⋀ P₁), from free_in_prop.and₂ this
        )
      )
    )
  ),
  have h4b: FV (↑R ⋀ P ⋀ P₂) = FV ((↑R ⋀ P) ⋀ P₂),
  from free_in_prop.and_assoc,
  have h4: FV (↑R ⋀ P ⋀ P₁ ) = FV ((↑R ⋀ P) ⋀ P₂),
  from eq.trans h4a h4b,

  have h5: ∀σ, σ ⊨ vc.implies (↑R ⋀ P ⋀ P₁).to_vc ((↑R ⋀ P) ⋀ P₂).to_vc, from (
    assume σ: env,
    have h5a: σ ⊨ vc.implies (↑R ⋀ P ⋀ P₁).to_vc ((↑R ⋀ P) ⋀ P₁).to_vc,
    from vc.implies.and_assoc,
    have h5b: σ ⊨ vc.implies ((↑R ⋀ P) ⋀ P₁).to_vc ((↑R ⋀ P) ⋀ P₂).to_vc,
    from vc.implies.same_left (
      assume : σ ⊨ (↑R ⋀ P).to_vc,
      have σ ⊨ (P).to_vc,
      from (valid_env.to_vc_and.elim this).right,
      h1 σ this
    ),
    show σ ⊨ vc.implies (↑R ⋀ P ⋀ P₁).to_vc ((↑R ⋀ P) ⋀ P₂).to_vc,
    from vc.implies.trans h5a h5b
  ),

  have h6: (∀σ t,
      σ ⊨ vc.implies ((↑(P ⋀ P₁) ⋀ Q) t).to_vc ((↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) t).to_vc), from (
    assume σ: env,
    assume t: term,
    have h6: ((↑(P ⋀ P₁) ⋀ Q) t) = ((P ⋀ P₁) ⋀ Q t), from propctx_apply_pq,
    have h7: ((↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) t)
        = (P ⋀ (propctx.exis x (↑P₂ ⋀ Q)) t), from propctx_apply_pq,
    have h8a: σ ⊨ vc.implies ((P ⋀ P₁) ⋀ Q t).to_vc
                              (P ⋀ P₁ ⋀ Q t).to_vc,
    from vc.implies.and_assoc.symm,
    have h8b: σ ⊨ vc.implies (P ⋀ P₁ ⋀ Q t).to_vc
                            (P ⋀ (propctx.exis x (↑P₂ ⋀ Q)) t).to_vc,
    from vc.implies.same_left (
      assume : σ ⊨ P.to_vc,
      show σ ⊨ vc.implies (P₁ ⋀ Q t).to_vc
                            ((propctx.exis x (↑P₂ ⋀ Q)) t).to_vc,
      from vc.implies.apply_propctx_exis (h2 σ this)
    ),
    have h9: σ ⊨ vc.implies ((P ⋀ P₁) ⋀ Q t).to_vc
                          (P ⋀ (propctx.exis x (↑P₂ ⋀ Q)) t).to_vc,
    from vc.implies.trans h8a h8b,
    show σ ⊨ vc.implies ((↑(P ⋀ P₁) ⋀ Q) t).to_vc ((↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) t).to_vc,
    from h6.symm ▸ h7.symm ▸ h9
  ),
  have h7: (∀v: value,
      FV ((↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) v) ⊆ FV ((↑(P ⋀ P₁) ⋀ Q) v)), from (
    assume v: value,
    have h6: ((↑(P ⋀ P₁) ⋀ Q) v) = ((P ⋀ P₁) ⋀ Q v), from propctx_apply_pq,
    have h7: ((↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) v)
        = (P ⋀ (propctx.exis x (↑P₂ ⋀ Q)) v), from propctx_apply_pq,
    have h9a: FV ((propctx.exis x (P₂.to_propctx ⋀ Q)) v) ⊆ FV P ∪ FV (Q v),
    from @free_in_prop.apply_propctx_exis P₂ Q x v (FV P) h3c,

    have h9a: FV (P ⋀ (propctx.exis x (↑P₂ ⋀ Q)) v)
            ⊆ FV (P ⋀ P₁ ⋀ Q v),
    from (
      assume z: var,
      assume : z ∈ FV (P ⋀ (propctx.exis x (↑P₂ ⋀ Q)) v),
      or.elim (free_in_prop.and.inv this) (
        assume : z ∈ FV P,
        show z ∈ FV (P ⋀ P₁ ⋀ Q v), from free_in_prop.and₁ this
      ) (
        assume : z ∈ FV ((propctx.exis x (↑P₂ ⋀ Q)) v),
        have z ∈ FV P ∪ FV (Q v), from set.mem_of_subset_of_mem h9a this,
        or.elim (set.mem_or_mem_of_mem_union this) (
          assume : z ∈ FV P,
          show z ∈ FV (P ⋀ P₁ ⋀ Q v), from free_in_prop.and₁ this
        ) (
          assume : z ∈ FV (Q v),
          have z ∈ FV (P₁ ⋀ Q v), from free_in_prop.and₂ this,
          show z ∈ FV (P ⋀ P₁ ⋀ Q v), from free_in_prop.and₂ this
        )
      )
    ),
    have h9b: FV (P ⋀ P₁ ⋀ Q v)
            ⊆ FV ((P ⋀ P₁) ⋀ Q v),
    from set.subset_of_eq free_in_prop.and_assoc,
    have h9c: FV (P ⋀ (propctx.exis x (↑P₂ ⋀ Q)) v)
            ⊆ FV ((P ⋀ P₁) ⋀ Q v),
    from set.subset.trans h9a h9b,
    show FV ((↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) v) ⊆ FV ((↑(P ⋀ P₁) ⋀ Q) v),
    from h6.symm ▸ h7.symm ▸ h9c
  ),
  ⟨h4, ⟨h5, ⟨h6, h7⟩⟩⟩

lemma free_dominates_helper_eq_free {R: spec} {P P₁ P₂: prop} {Q: propctx} {x: var}:
      (∀σ, (σ ⊨ P.to_vc) → σ ⊨ vc.implies P₁.to_vc P₂.to_vc) →
      (∀σ, (σ ⊨ P.to_vc) → σ ⊨ vc.implies P₁.to_vc P₂.to_vc) →
      (FV P₁ = set.insert x ∅) → 
      (FV P₂ = set.insert x ∅) → 
      (FV (↑R ⋀ P ⋀ P₁) = FV ((↑R ⋀ P) ⋀ P₂)) ∧
      (∀σ, σ ⊨ vc.implies (↑R ⋀ P ⋀ P₁).to_vc ((↑R ⋀ P) ⋀ P₂).to_vc) ∧
      (∀σ t, σ ⊨ vc.implies ((↑(P ⋀ P₁) ⋀ Q) t).to_vc ((↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) t).to_vc) ∧
      (∀v: value, FV ((↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) v) ⊆ FV ((↑(P ⋀ P₁) ⋀ Q) v)) :=
  assume h1: ∀σ, (σ ⊨ P.to_vc) → σ ⊨ vc.implies P₁.to_vc P₂.to_vc,
  assume h2: ∀σ, (σ ⊨ P.to_vc) → σ ⊨ vc.implies P₁.to_vc P₂.to_vc,
  assume h3a: FV P₁ = set.insert x ∅,
  assume h3a2: FV P₂ = set.insert x ∅,

  have x ∈ set.insert x ∅, from set.mem_singleton x,
  have h3b: x ∈ FV P₂, from h3a2.symm ▸ this,
  have h3c: FV P₂ ⊆ FV P ∪ set.insert x ∅, from (
    assume z: var,
    assume : z ∈ FV P₂,
    have z ∈ set.insert x ∅, from h3a2 ▸ this,
    have z = x, from set.eq_of_mem_singleton this,
    have z ∈ set.insert x ∅, from this.symm ▸ set.mem_singleton x,
    show z ∈ FV P ∪ set.insert x ∅, from set.mem_union_right (FV P) this
  ),
  free_dominates_helper h1 h2 h3a h3b h3c

lemma exp.preservation {R: spec} {σ σ': env} {P: prop} {e e': exp} {Q: propctx}:
      (⊩ σ : P) → FV (spec.to_prop R) ⊆ FV P → (σ ⊨ R.to_prop.to_vc) → (R ⋀ P ⊩ e : Q) →
      ((R, σ, e) ⟹ (R, σ', e')) →
      ∃Q', (⊩ₛ (R, σ', e') : Q') ∧ (∀σ' t, σ' ⊨ vc.implies (Q' t).to_vc ((↑P ⋀ Q) t).to_vc) ∧
                                   (∀v: value, FV ((↑P ⋀ Q) v) ⊆ FV (Q' v)) :=
  assume σ_verified: ⊩ σ : P,
  assume fv_R: FV (spec.to_prop R) ⊆ FV P,
  assume R_valid: (σ ⊨ R.to_prop.to_vc),
  assume e_verified: R ⋀ P ⊩ e : Q,
  assume e_steps: ((R, σ, e) ⟹ (R, σ', e')),
  begin
    cases e_verified,

    case exp.dvcgen.tru x e' Q x_not_free e'_verified {
      cases e_steps,
      
      case dstep.tru { from
        have x ∉ σ, from (
          assume : x ∈ σ,
          have x ∈ σ.dom, from this,
          have x ∈ FV P, from (free_iff_contains σ_verified) ▸ this,
          have x ∈ FV (↑R ⋀ P), from free_in_prop.and₂ this,
          show «false», from x_not_free this
        ),
        have σ'_verified: ⊩ (σ[x↦value.true]) : P ⋀ x ≡ value.true, from env.dvcgen.tru this σ_verified,
        have fv_R': FV R.to_prop ⊆ FV (P ⋀ x ≡ value.true), from set.subset.trans fv_R free_in_prop.and_left_subset,
        have R_valid': σ[x↦value.true] ⊨ R.to_prop.to_vc, from valid_with_additional_var R_valid,

        have h1: (∀σ, (σ ⊨ P.to_vc) → σ ⊨ vc.implies (x ≡ value.true) (x ≡ value.true)),
        from λ_ _, vc.implies.self,
        have h2: FV (prop.term (x ≡ value.true)) = set.insert x ∅, from set.eq_of_subset_of_subset (
          assume z: var,
          assume : free_in_prop z (x ≡ value.true),
          have free_in_term z (x ≡ value.true), from free_in_prop.term.inv this,
          or.elim (free_in_term.binop.inv this) (
            assume : free_in_term z x,
            have z = x, from free_in_term.var.inv this,
            show z ∈ set.insert x ∅, from (set.mem_singleton_iff z x).mpr this
          ) (
            assume : free_in_term z value.true,
            show z ∈ set.insert x ∅, from absurd this free_in_term.value.inv
          )
        ) (
          assume z: var,
          assume : z ∈ set.insert x ∅,
          have z = x, from (set.mem_singleton_iff z x).mp this,
          have free_in_term z x, from this ▸ free_in_term.var z,
          have free_in_term z (x ≡ value.true), from free_in_term.binop₁ this,
          show free_in_prop z (x ≡ value.true), from free_in_prop.term this
        ),
        have h3: (FV (↑R ⋀ P ⋀ (x ≡ value.true)) = FV ((↑R ⋀ P) ⋀ (x ≡ value.true))) ∧
          (∀σ, σ ⊨ vc.implies (↑R ⋀ P ⋀ (x ≡ value.true)).to_vc ((↑R ⋀ P) ⋀ (x ≡ value.true)).to_vc) ∧
          (∀σ t, σ ⊨ vc.implies ((↑(P ⋀ (x ≡ value.true)) ⋀ Q) t).to_vc
                                 ((↑P ⋀ propctx.exis x (↑(x ≡ value.true) ⋀ Q)) t).to_vc) ∧
          (∀v: value, FV ((↑P ⋀ propctx.exis x (↑(x ≡ value.true) ⋀ Q)) v)
                    ⊆ FV ((↑(P ⋀ (x ≡ value.true)) ⋀ Q) v)),
        from @free_dominates_helper_eq_free R P (x ≡ value.true) (x ≡ value.true) Q x h1 h1 h2 h2,
        have e'_verified': ↑R ⋀ P ⋀ x ≡ value.true ⊩ e' : Q,
        from strengthen_exp e'_verified (↑R ⋀ P ⋀ x ≡ value.true) h3.left h3.right.left,
        have h4: ⊩ₛ (R, σ[x↦value.true], e') : ↑(P ⋀ x ≡ value.true) ⋀ Q,
        from stack.dvcgen.top σ'_verified fv_R' R_valid' e'_verified',
        exists.intro (↑(P ⋀ x ≡ value.true) ⋀ Q) ⟨h4, h3.right.right⟩
      }
    },
    case exp.dvcgen.fals x e' Q x_not_free e'_verified {

      cases e_steps,
      
      case dstep.fals { from
        have x ∉ σ, from (
          assume : x ∈ σ,
          have x ∈ σ.dom, from this,
          have x ∈ FV P, from (free_iff_contains σ_verified) ▸ this,
          have x ∈ FV (↑R ⋀ P), from free_in_prop.and₂ this,
          show «false», from x_not_free this
        ),
        have σ'_verified: ⊩ (σ[x↦value.false]) : P ⋀ x ≡ value.false, from env.dvcgen.fls this σ_verified,
        have fv_R': FV R.to_prop ⊆ FV (P ⋀ x ≡ value.false), from set.subset.trans fv_R free_in_prop.and_left_subset,
        have R_valid': σ[x↦value.false] ⊨ R.to_prop.to_vc, from valid_with_additional_var R_valid,

        have h1: (∀σ, (σ ⊨ P.to_vc) → σ ⊨ vc.implies (x ≡ value.false) (x ≡ value.false)),
        from λ_ _, vc.implies.self,
        have h2: FV (prop.term (x ≡ value.false)) = set.insert x ∅, from set.eq_of_subset_of_subset (
          assume z: var,
          assume : free_in_prop z (x ≡ value.false),
          have free_in_term z (x ≡ value.false), from free_in_prop.term.inv this,
          or.elim (free_in_term.binop.inv this) (
            assume : free_in_term z x,
            have z = x, from free_in_term.var.inv this,
            show z ∈ set.insert x ∅, from (set.mem_singleton_iff z x).mpr this
          ) (
            assume : free_in_term z value.false,
            show z ∈ set.insert x ∅, from absurd this free_in_term.value.inv
          )
        ) (
          assume z: var,
          assume : z ∈ set.insert x ∅,
          have z = x, from (set.mem_singleton_iff z x).mp this,
          have free_in_term z x, from this ▸ free_in_term.var z,
          have free_in_term z (x ≡ value.false), from free_in_term.binop₁ this,
          show free_in_prop z (x ≡ value.false), from free_in_prop.term this
        ),
        have h3: (FV (↑R ⋀ P ⋀ (x ≡ value.false)) = FV ((↑R ⋀ P) ⋀ (x ≡ value.false))) ∧
          (∀σ, σ ⊨ vc.implies (↑R ⋀ P ⋀ (x ≡ value.false)).to_vc ((↑R ⋀ P) ⋀ (x ≡ value.false)).to_vc) ∧
          (∀σ t, σ ⊨ vc.implies ((↑(P ⋀ (x ≡ value.false)) ⋀ Q) t).to_vc
                               ((↑P ⋀ propctx.exis x (↑(x ≡ value.false) ⋀ Q)) t).to_vc) ∧
          (∀v: value, FV ((↑P ⋀ propctx.exis x (↑(x ≡ value.false) ⋀ Q)) v)
                    ⊆ FV ((↑(P ⋀ (x ≡ value.false)) ⋀ Q) v)),
        from @free_dominates_helper_eq_free R P (x ≡ value.false) (x ≡ value.false) Q x h1 h1 h2 h2,
        have e'_verified': ↑R ⋀ P ⋀ x ≡ value.false ⊩ e' : Q,
        from strengthen_exp e'_verified (↑R ⋀ P ⋀ x ≡ value.false) h3.left h3.right.left,
        have h4: ⊩ₛ (R, σ[x↦value.false], e') : ↑(P ⋀ x ≡ value.false) ⋀ Q,
        from stack.dvcgen.top σ'_verified fv_R' R_valid' e'_verified',
        exists.intro (↑(P ⋀ x ≡ value.false) ⋀ Q) ⟨h4, h3.right.right⟩
      }
    },
    case exp.dvcgen.num x n e' Q x_not_free e'_verified {

      cases e_steps,
      
      case dstep.num { from
        have x ∉ σ, from (
          assume : x ∈ σ,
          have x ∈ σ.dom, from this,
          have x ∈ FV P, from (free_iff_contains σ_verified) ▸ this,
          have x ∈ FV (↑R ⋀ P), from free_in_prop.and₂ this,
          show «false», from x_not_free this
        ),
        have σ'_verified: ⊩ (σ[x↦value.num n]) : P ⋀ x ≡ value.num n, from env.dvcgen.num this σ_verified,
        have fv_R': FV R.to_prop ⊆ FV (P ⋀ x ≡ value.num n), from set.subset.trans fv_R free_in_prop.and_left_subset,
        have R_valid': σ[x↦value.num n] ⊨ R.to_prop.to_vc, from valid_with_additional_var R_valid,
        have h1: (∀σ, (σ ⊨ P.to_vc) → σ ⊨ vc.implies (x ≡ value.num n) (x ≡ value.num n)),
        from λ_ _, vc.implies.self,
        have h2: FV (prop.term (x ≡ value.num n)) = set.insert x ∅, from set.eq_of_subset_of_subset (
          assume z: var,
          assume : free_in_prop z (x ≡ value.num n),
          have free_in_term z (x ≡ value.num n), from free_in_prop.term.inv this,
          or.elim (free_in_term.binop.inv this) (
            assume : free_in_term z x,
            have z = x, from free_in_term.var.inv this,
            show z ∈ set.insert x ∅, from (set.mem_singleton_iff z x).mpr this
          ) (
            assume : free_in_term z (value.num n),
            show z ∈ set.insert x ∅, from absurd this free_in_term.value.inv
          )
        ) (
          assume z: var,
          assume : z ∈ set.insert x ∅,
          have z = x, from (set.mem_singleton_iff z x).mp this,
          have free_in_term z x, from this ▸ free_in_term.var z,
          have free_in_term z (x ≡ value.num n), from free_in_term.binop₁ this,
          show free_in_prop z (x ≡ value.num n), from free_in_prop.term this
        ),
        have h3: (FV (↑R ⋀ P ⋀ (x ≡ value.num n)) = FV ((↑R ⋀ P) ⋀ (x ≡ value.num n))) ∧
          (∀σ, σ ⊨ vc.implies (↑R ⋀ P ⋀ (x ≡ value.num n)).to_vc ((↑R ⋀ P) ⋀ (x ≡ value.num n)).to_vc) ∧
          (∀σ t, σ ⊨ vc.implies ((↑(P ⋀ (x ≡ value.num n)) ⋀ Q) t).to_vc
                                ((↑P ⋀ propctx.exis x (↑(x ≡ value.num n) ⋀ Q)) t).to_vc) ∧
          (∀v: value, FV ((↑P ⋀ propctx.exis x (↑(x ≡ value.num n) ⋀ Q)) v)
                    ⊆ FV ((↑(P ⋀ (x ≡ value.num n)) ⋀ Q) v)),
        from @free_dominates_helper_eq_free R P (x ≡ value.num n) (x ≡ value.num n) Q x h1 h1 h2 h2,
        have e'_verified': ↑R ⋀ P ⋀ x ≡ value.num n ⊩ e' : Q,
        from strengthen_exp e'_verified (↑R ⋀ P ⋀ x ≡ value.num n) h3.left h3.right.left,
        have h4: ⊩ₛ (R, σ[x↦value.num n], e') : ↑(P ⋀ x ≡ value.num n) ⋀ Q,
        from stack.dvcgen.top σ'_verified fv_R' R_valid' e'_verified',
        exists.intro (↑(P ⋀ x ≡ value.num n) ⋀ Q) ⟨h4, h3.right.right⟩
      }
    },
    case exp.dvcgen.func f x R' S' e₁ e₂ Q₁ Q₂ f_not_in x_not_in f_neq_x x_free_in_R' fv_R' fv_S' e₁_verified
                        e₂_verified func_vc {

      cases e_steps,
      
      case dstep.closure { from
        have f_not_in_σ: f ∉ σ, from (
          assume : f ∈ σ,
          have f ∈ σ.dom, from this,
          have f ∈ FV P, from (free_iff_contains σ_verified) ▸ this,
          have f ∈ FV (↑R ⋀ P), from free_in_prop.and₂ this,
          show «false», from f_not_in this
        ),
        have x_not_in_σ: x ∉ σ, from (
          assume : x ∈ σ,
          have x ∈ σ.dom, from this,
          have x ∈ FV P, from (free_iff_contains σ_verified) ▸ this,
          have x ∈ FV (↑R ⋀ P), from free_in_prop.and₂ this,
          show «false», from x_not_in this
        ),
        have fv_R'': FV R'.to_prop ⊆ FV P ∪ { f, x }, from (
          assume z: var,
          assume : z ∈ FV R'.to_prop,
          have z ∈ FV (prop.and ↑R P) ∪ {f, x}, from set.mem_of_subset_of_mem fv_R' this,
          or.elim (set.mem_or_mem_of_mem_union this) (
            assume : z ∈ FV (↑R ⋀ P),
            or.elim (free_in_prop.and.inv this) (
              assume : z ∈ FV R.to_prop,
              have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
              show z ∈ FV P ∪ { f, x }, from set.mem_union_left { f, x } this
            ) (
              assume : z ∈ FV P,
              show z ∈ FV P ∪ { f, x }, from set.mem_union_left { f, x } this
            )
          ) (
            assume : z ∈ {f, x},
            show z ∈ FV P ∪ { f, x }, from set.mem_union_right (FV P) this
          )
        ),
        have fv_S'': FV S'.to_prop ⊆ FV P ∪ { f, x }, from (
          assume z: var,
          assume : z ∈ FV S'.to_prop,
          have z ∈ FV (prop.and ↑R P) ∪ {f, x}, from set.mem_of_subset_of_mem fv_S' this,
          or.elim (set.mem_or_mem_of_mem_union this) (
            assume : z ∈ FV (↑R ⋀ P),
            or.elim (free_in_prop.and.inv this) (
              assume : z ∈ FV R.to_prop,
              have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
              show z ∈ FV P ∪ { f, x }, from set.mem_union_left { f, x } this
            ) (
              assume : z ∈ FV P,
              show z ∈ FV P ∪ { f, x }, from set.mem_union_left { f, x } this
            )
          ) (
            assume : z ∈ {f, x},
            show z ∈ FV P ∪ { f, x }, from set.mem_union_right (FV P) this
          )
        ),
        have e₁_verified': P ⋀ spec.func f x R' S' ⋀ R' ⊩ e₁ : Q₁, from (
          have FV P = FV (↑R ⋀ P), from set.eq_of_subset_of_subset (
            assume z: var,
            assume : z ∈ FV P,
            show z ∈ FV (↑R ⋀ P), from free_in_prop.and₂ this
          ) (
            assume z: var,
            assume : z ∈ FV (↑R ⋀ P),
            or.elim (free_in_prop.and.inv this) (
              assume : z ∈ FV ↑R,
              show z ∈ FV P, from set.mem_of_subset_of_mem fv_R this
            ) id
          ),
          have h1: FV (P ⋀ spec.func f x R' S' ⋀ R')
                 = FV ((↑R ⋀ P) ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R'),
          from free_in_prop.same_right this,
          have h2: ∀σ', σ' ⊨ vc.implies (P ⋀ spec.func f x R' S' ⋀ R').to_vc
                                        ((↑R ⋀ P) ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R').to_vc,
          from (
            assume σ': env,

            show σ' ⊨ vc.implies (P ⋀ spec.func f x R' S' ⋀ R').to_vc
                                 ((↑R ⋀ P) ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R').to_vc,
            from vc.implies.same_right (
              assume _,

              show σ' ⊨ vc.implies P.to_vc (↑R ⋀ P).to_vc, by begin
                apply valid_env.mpr,
                assume h4,
                apply valid_env.to_vc_and,

                have h5: (∀y, y ∈ σ → (σ y = σ' y)),
                from env_equiv_of_translation_valid σ_verified σ' h4,
                from valid_env.equiv_env h5 R_valid,
                from h4
              end
            )
          ),
          show (P ⋀ spec.func f x R' S' ⋀ R') ⊩ e₁ : Q₁,
          from strengthen_exp e₁_verified (P ⋀ spec.func f x R' S' ⋀ R') h1 h2
        ),
        have func_vc': ⦃prop.implies (P ⋀ spec.func f x R' S' ⋀ R' ⋀ Q₁ (term.app f x)) S'⦄,
        from (
          assume σ': env,
          
          have h2: σ' ⊨ vc.implies P.to_vc (↑R ⋀ P).to_vc, by begin
            apply valid_env.mpr,
            assume h4,
            apply valid_env.to_vc_and,

            have h5: (∀y, y ∈ σ → (σ y = σ' y)),
            from env_equiv_of_translation_valid σ_verified σ' h4,
            from valid_env.equiv_env h5 R_valid,
            from h4
          end,
          have h3: FV (↑R ⋀ P) ⊆ FV P, by begin
            assume y,
            assume h4,
            cases (free_in_prop.and.inv h4) with h5 h5,
            have h6: y ∈ FV R.to_prop, from h5,
            from set.mem_of_mem_of_subset h6 fv_R,
            from h5
          end,

          strengthen_vc_with_q h2 h3 (func_vc σ')
        ),
        let vf := value.func f x R' S' e₁ σ in
        let P' := (↑(f ≡ vf)
                ⋀ prop.subst_env (σ[f↦vf]) (prop.func f x R' (Q₁ (term.app f x) ⋀ S'))) in
        let Q' := (prop.func f x R' (Q₁ (term.app f x) ⋀ S')) in
        have σ'_verified: ⊩ (σ[f↦vf]) : P ⋀ P',
        from env.dvcgen.func f_not_in_σ f_not_in_σ x_not_in_σ f_neq_x σ_verified σ_verified
             x_free_in_R' fv_R'' fv_S'' e₁_verified' func_vc',
        have fv_R'': FV R.to_prop ⊆ FV (P ⋀ P'),
        from set.subset.trans fv_R free_in_prop.and_left_subset,
        have R_valid': σ[f↦vf] ⊨ R.to_prop.to_vc,
        from valid_with_additional_var R_valid,
        have h1: (∀σ', (σ' ⊨ P.to_vc) → σ' ⊨ vc.implies P'.to_vc Q'.to_vc), from (
          assume σ': env,
          assume P_valid: σ' ⊨ P.to_vc,
          show σ' ⊨ vc.implies (↑(f ≡ vf)
                ⋀ prop.subst_env (σ[f↦vf]) (prop.func f x R' (Q₁ (term.app f x) ⋀ S'))).to_vc Q'.to_vc,
          from vc.implies.left_elim (
            assume : σ' ⊨ prop.to_vc (f ≡ vf),
            have f_is_vf: σ' f = vf, from valid_env.subst_of_eq this,
            have (∀y, y ∈ σ → (σ y = σ' y)),
            from env_equiv_of_translation_valid σ_verified σ' P_valid,
            have (∀y, y ∈ (σ[f↦vf]) → ((σ[f↦vf]) y = σ' y)),
            from env.equiv_of_rest_and_same this f_not_in_σ f_is_vf,
            show σ' ⊨ vc.implies (prop.subst_env (σ[f↦vf]) (prop.func f x R' (Q₁ (term.app f x) ⋀ S'))).to_vc
                                 (prop.func f x R' (Q₁ (term.app f x) ⋀ S')).to_vc,
            from vc.implies.equiv_subst this
          )
        ),
        have h2: (∀σ', (σ' ⊨ P.to_vc) → σ' ⊨ vc.implies P'.to_vc Q'.to_vc), from (
          assume σ': env,
          assume P_valid: σ' ⊨ P.to_vc,
          show σ' ⊨ vc.implies (↑(f ≡ vf)
                ⋀ prop.subst_env (σ[f↦vf]) (prop.func f x R' (Q₁ (term.app f x) ⋀ S'))).to_vc Q'.to_vc,
          from vc.implies.left_elim (
            assume : σ' ⊨ prop.to_vc (f ≡ vf),
            have f_is_vf: σ' f = vf, from valid_env.subst_of_eq this,
            have (∀y, y ∈ σ → (σ y = σ' y)),
            from env_equiv_of_translation_valid σ_verified σ' P_valid,
            have (∀y, y ∈ (σ[f↦vf]) → ((σ[f↦vf]) y = σ' y)),
            from env.equiv_of_rest_and_same this f_not_in_σ f_is_vf,
            show σ' ⊨ vc.implies (prop.subst_env (σ[f↦vf]) (prop.func f x R' (Q₁ (term.app f x) ⋀ S'))).to_vc
                                 (prop.func f x R' (Q₁ (term.app f x) ⋀ S')).to_vc,
            from vc.implies.equiv_subst this
          )
        ),

        have h3a: FV P' = set.insert f ∅, from set.eq_of_subset_of_subset (
          assume z: var,
          assume : z ∈ FV P',
          have z ∈ FV (↑(f ≡ vf) ⋀ prop.subst_env (σ[f↦vf]) (prop.func f x R' (Q₁ (term.app f x) ⋀ S'))),
          from this,
          or.elim (free_in_prop.and.inv this) (
            assume : free_in_prop z (f ≡ vf),
            have free_in_term z (f ≡ vf), from free_in_prop.term.inv this,
            or.elim (free_in_term.binop.inv this) (
              assume : free_in_term z f,
              have z = f, from free_in_term.var.inv this,
              show z ∈ set.insert f ∅, from (set.mem_singleton_iff z f).mpr this
            ) (
              assume : free_in_term z vf,
              show z ∈ set.insert f ∅, from absurd this free_in_term.value.inv
            )
          ) (
            assume h: z ∈ FV (prop.subst_env (σ[f↦vf]) (prop.func f x R' (Q₁ (term.app f x) ⋀ S'))),
            have closed (prop.subst_env (σ[f↦vf]) (prop.func f x R' (Q₁ (term.app f x) ⋀ S'))),
            from prop_func_closed σ'_verified,
            show z ∈ set.insert f ∅, from absurd h (this z)
          )
        ) (
          assume z: var,
          assume : z ∈ set.insert f ∅,
          have z = f, from (set.mem_singleton_iff z f).mp this,
          have free_in_term z f, from this ▸ free_in_term.var z,
          have free_in_term z (f ≡ vf), from free_in_term.binop₁ this,
          have free_in_prop z (f ≡ vf), from free_in_prop.term this,
          show z ∈ FV (↑(f ≡ vf) ⋀ prop.subst_env (σ[f↦vf]) (prop.func f x R' (Q₁ (term.app f x) ⋀ S'))),
          from free_in_prop.and₁ this
        ),
        have h3b: f ∈ FV Q', from (
          have free_in_term f f, from free_in_term.var f,
          have free_in_term f (term.unop unop.isFunc f), from free_in_term.unop this,
          have free_in_prop f (term.unop unop.isFunc f), from free_in_prop.term this,
          show f ∈ FV Q', from free_in_prop.and₁ this
        ),
        have h3c: FV Q' ⊆ FV P ∪ set.insert f ∅, from (
          assume z: var,
          assume : z ∈ FV Q',
          have z ∈ FV (prop.func f x R' (Q₁ (term.app f x) ⋀ S')), from this,
          or.elim (free_in_prop.func.inv this) (
            assume : free_in_term z f,
            have z = f, from free_in_term.var.inv this,
            have z ∈ set.insert f ∅, from (set.mem_singleton_iff z f).mpr this,
            show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_right (FV P) this
          ) (
            assume h3c1: (z ≠ x ∧ (free_in_prop z R' ∨ free_in_prop z (Q₁ (term.app f x) ⋀ S'))),
            have z_neq_x: z ≠ x, from h3c1.left,
            or.elim (h3c1.right) (
              assume : free_in_prop z R',
              have z ∈ FV (prop.and ↑R P) ∪ {f, x}, from set.mem_of_subset_of_mem fv_R' this,
              or.elim (set.mem_or_mem_of_mem_union this) (
                assume : z ∈ FV (↑R ⋀ P),
                or.elim (free_in_prop.and.inv this) (
                  assume : z ∈ FV R.to_prop,
                  have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                  show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                ) (
                  assume : z ∈ FV P,
                  show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                )
              ) (
                assume : z ∈ {f, x},
                or.elim (set.two_elems_mem this) (
                  assume : z = f,
                  have z ∈ set.insert f ∅, from (set.mem_singleton_iff z f).mpr this,
                  show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_right (FV P) this
                ) (
                  assume : z = x,
                  show z ∈ FV P ∪ set.insert f ∅, from absurd this z_neq_x
                )
              )
            ) (
              assume : free_in_prop z (Q₁ (term.app f x) ⋀ S'),
              or.elim (free_in_prop.and.inv this) (
                assume : free_in_prop z (Q₁ (term.app f x)),
                have z ∈ FV (term.app f x) ∨ z ∈ FV ((↑R ⋀ P) ⋀ (spec.func f x R' S') ⋀ R'),
                from exp.post_free e₁_verified (term.app f x) this,
                or.elim this (
                  assume : z ∈ FV (term.app f x),
                  or.elim (free_in_term.app.inv this) (
                    assume : free_in_term z f,
                    have z = f, from free_in_term.var.inv this,
                    have z ∈ set.insert f ∅, from (set.mem_singleton_iff z f).mpr this,
                    show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_right (FV P) this
                  ) (
                    assume : free_in_term z x,
                    have z = x, from free_in_term.var.inv this,
                    show z ∈ FV P ∪ set.insert f ∅, from absurd this z_neq_x
                  )
                ) (
                  assume : z ∈ FV ((↑R ⋀ P) ⋀ (spec.func f x R' S') ⋀ R'),
                  or.elim (free_in_prop.and.inv this) (
                    assume : z ∈ FV (↑R ⋀ P),
                    or.elim (free_in_prop.and.inv this) (
                      assume : z ∈ FV R.to_prop,
                      have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                      show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                    ) (
                      assume : z ∈ FV P,
                      show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                    )
                  ) (
                    assume : free_in_prop z (↑(spec.func f x R' S') ⋀ ↑R'),
                    or.elim (free_in_prop.and.inv this) (
                      assume : free_in_prop z (spec.func f x R' S'),
                      have h: free_in_prop z (spec.func f x R' S').to_prop, from this,
                      have (spec.func f x R' S').to_prop = (prop.func f x R'.to_prop S'.to_prop),
                      by unfold spec.to_prop,
                      have free_in_prop z (prop.func f x R' S'), from this ▸ h,
                      or.elim (free_in_prop.func.inv this) (
                        assume : free_in_term z f,
                        have z = f, from free_in_term.var.inv this,
                        have z ∈ set.insert f ∅, from (set.mem_singleton_iff z f).mpr this,
                        show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_right (FV P) this
                      ) (
                        assume h3c1: (z ≠ x ∧ (free_in_prop z R' ∨ free_in_prop z S')),
                        or.elim (h3c1.right) (
                          assume : free_in_prop z R',
                          have z ∈ FV (prop.and ↑R P) ∪ {f, x}, from set.mem_of_subset_of_mem fv_R' this,
                          or.elim (set.mem_or_mem_of_mem_union this) (
                            assume : z ∈ FV (↑R ⋀ P),
                            or.elim (free_in_prop.and.inv this) (
                              assume : z ∈ FV R.to_prop,
                              have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                              show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                            ) (
                              assume : z ∈ FV P,
                              show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                            )
                          ) (
                            assume : z ∈ {f, x},
                            or.elim (set.two_elems_mem this) (
                              assume : z = f,
                              have z ∈ set.insert f ∅, from (set.mem_singleton_iff z f).mpr this,
                              show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_right (FV P) this
                            ) (
                              assume : z = x,
                              show z ∈ FV P ∪ set.insert f ∅, from absurd this z_neq_x
                            )
                          )
                        ) (
                          assume : free_in_prop z S',
                          have z ∈ FV (prop.and ↑R P) ∪ {f, x}, from set.mem_of_subset_of_mem fv_S' this,
                          or.elim (set.mem_or_mem_of_mem_union this) (
                            assume : z ∈ FV (↑R ⋀ P),
                            or.elim (free_in_prop.and.inv this) (
                              assume : z ∈ FV R.to_prop,
                              have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                              show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                            ) (
                              assume : z ∈ FV P,
                              show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                            )
                          ) (
                            assume : z ∈ {f, x},
                            or.elim (set.two_elems_mem this) (
                              assume : z = f,
                              have z ∈ set.insert f ∅, from (set.mem_singleton_iff z f).mpr this,
                              show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_right (FV P) this
                            ) (
                              assume : z = x,
                              show z ∈ FV P ∪ set.insert f ∅, from absurd this z_neq_x
                            )
                          )
                        )
                      )
                    ) (
                      assume : free_in_prop z R',
                      have z ∈ FV (prop.and ↑R P) ∪ {f, x}, from set.mem_of_subset_of_mem fv_R' this,
                      or.elim (set.mem_or_mem_of_mem_union this) (
                        assume : z ∈ FV (↑R ⋀ P),
                        or.elim (free_in_prop.and.inv this) (
                          assume : z ∈ FV R.to_prop,
                          have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                          show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                        ) (
                          assume : z ∈ FV P,
                          show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                        )
                      ) (
                        assume : z ∈ {f, x},
                        or.elim (set.two_elems_mem this) (
                          assume : z = f,
                          have z ∈ set.insert f ∅, from (set.mem_singleton_iff z f).mpr this,
                          show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_right (FV P) this
                        ) (
                          assume : z = x,
                          show z ∈ FV P ∪ set.insert f ∅, from absurd this z_neq_x
                        )
                      )
                    )
                  )
                )
              ) (
                assume : free_in_prop z S',
                have z ∈ FV (prop.and ↑R P) ∪ {f, x}, from set.mem_of_subset_of_mem fv_S' this,
                or.elim (set.mem_or_mem_of_mem_union this) (
                  assume : z ∈ FV (↑R ⋀ P),
                  or.elim (free_in_prop.and.inv this) (
                    assume : z ∈ FV R.to_prop,
                    have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                    show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                  ) (
                    assume : z ∈ FV (P),
                    show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                  )
                ) (
                  assume : z ∈ {f, x},
                  or.elim (set.two_elems_mem this) (
                    assume : z = f,
                    have z ∈ set.insert f ∅, from (set.mem_singleton_iff z f).mpr this,
                    show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_right (FV P) this
                  ) (
                    assume : z = x,
                    show z ∈ FV P ∪ set.insert f ∅, from absurd this z_neq_x
                  )
                )
              )
            )
          )
        ),
        have h4: (FV (↑R ⋀ P ⋀ P') = FV ((↑R ⋀ P) ⋀ Q')) ∧
          (∀σ, σ ⊨ vc.implies (↑R ⋀ P ⋀ P').to_vc ((↑R ⋀ P) ⋀ Q').to_vc) ∧
          (∀σ t, σ ⊨ vc.implies ((↑(P ⋀ P') ⋀ Q₂) t).to_vc ((↑P ⋀ propctx.exis f (↑Q' ⋀ Q₂)) t).to_vc) ∧
          (∀v: value, FV ((↑P ⋀ propctx.exis f (↑Q' ⋀ Q₂)) v) ⊆ FV ((↑(P ⋀ P') ⋀ Q₂) v)),
        from @free_dominates_helper R P P' Q' Q₂ f h1 h2 h3a h3b h3c,
        have e'_verified': ↑R ⋀ P ⋀ P' ⊩ e' : Q₂,
        from strengthen_exp e₂_verified (↑R ⋀ P ⋀ P') h4.left h4.right.left,
        have h3: ⊩ₛ (R, σ[f↦value.func f x R' S' e₁ σ], e') : ↑(P ⋀ P') ⋀ Q₂,
        from stack.dvcgen.top σ'_verified fv_R'' R_valid' e'_verified',
        exists.intro (↑(P ⋀ P') ⋀ Q₂) ⟨h3, h4.right.right⟩
      }
    },
    case exp.dvcgen.unop op x y e' Q x_free_in_P y_not_free e'_verified vc_valid {
      cases e_steps,
      case dstep.unop vx vy x_is_vx vy_is_op { from
        have y_not_in_σ: y ∉ σ, from (
          assume : y ∈ σ,
          have y ∈ σ.dom, from this,
          have y ∈ FV P, from (free_iff_contains σ_verified) ▸ this,
          have y ∈ FV (↑R ⋀ P), from free_in_prop.and₂ this,
          show «false», from y_not_free this
        ),
        have σ'_verified: ⊩ (σ[y↦vy]) : P ⋀ y ≡ vy, from (
          or.elim (unop_result_not_function vy_is_op) (
            assume vy_is_true: vy = value.true,
            have σ'_verified: ⊩ (σ[y↦value.true]) : P ⋀ y ≡ value.true, from env.dvcgen.tru y_not_in_σ σ_verified,
            show ⊩ (σ[y↦vy]) : P ⋀ y ≡ vy, from vy_is_true.symm ▸ σ'_verified
          ) (
            assume vy_is_false: vy = value.false,
            have σ'_verified: ⊩ (σ[y↦value.false]) : P ⋀ y ≡ value.false, from env.dvcgen.fls y_not_in_σ σ_verified,
            show ⊩ (σ[y↦vy]) : P ⋀ y ≡ vy, from vy_is_false.symm ▸ σ'_verified
          )
        ),
        have fv_R': FV R.to_prop ⊆ FV (P ⋀ y ≡ vy), from set.subset.trans fv_R free_in_prop.and_left_subset,
        have R_valid': σ[y↦vy] ⊨ R.to_prop.to_vc, from valid_with_additional_var R_valid,
        have h1: (∀σ, (σ ⊨ P.to_vc) → σ ⊨ vc.implies (prop.term (y ≡ vy)).to_vc (prop.term (y ≡ term.unop op x)).to_vc),
        from (
          assume σ': env,
          assume : σ' ⊨ P.to_vc,
          have env_equiv: (∀y, y ∈ σ → (σ y = σ' y)),
          from env_equiv_of_translation_valid σ_verified σ' this,

          have h_impl: ((σ' ⊨ prop.to_vc (y ≡ vy))
                      → (σ' ⊨ prop.to_vc (y ≡ term.unop op x))),
          from (
            assume : σ' ⊨ prop.to_vc (y ≡ vy),
            have y_is_vy: σ' y = some vy, from valid_env.subst_of_eq this,
            have y_subst: term.subst_env σ' y = vy, from (term.subst_env.var.right vy).mp y_is_vy,

            have σ' x = vx, from eq_value_of_equiv_subst env_equiv x_is_vx,
            have x_subst: term.subst_env σ' x = vx, from (term.subst_env.var.right vx).mp this,

            have unop.apply op vx = some vy, from vy_is_op,
            have ⊨ vy ≡ term.unop op vx, from valid.unop.mp this,
            have h2: ⊨ (term.subst_env σ' y) ≡ term.unop op (term.subst_env σ' x),
            from x_subst.symm ▸ y_subst.symm ▸ this,

            have term.subst_env σ' (term.unop op x) = term.unop op (term.subst_env σ' x),
            from term.subst_env.unop,
            have ⊨ term.subst_env σ' y ≡ term.subst_env σ' (term.unop op x),
            from this.symm ▸ h2,
            have h3: ⊨ term.binop binop.eq (term.subst_env σ' y) (term.subst_env σ' (term.unop op x)),
            from this,

            have term.subst_env σ' (term.binop binop.eq y (term.unop op x))
                = term.binop binop.eq (term.subst_env σ' y) (term.subst_env σ' (term.unop op x)),
            from term.subst_env.binop,

            have h4: ⊨ term.subst_env σ' (term.binop binop.eq y (term.unop op x)),
            from this.symm ▸ h3,

            have vc.subst_env σ' (term.binop binop.eq y (term.unop op x))
                = term.subst_env σ' (term.binop binop.eq y (term.unop op x)),
            from vc.subst_env.term,

            have ⊨ vc.subst_env σ' (term.binop binop.eq y (term.unop op x)),
            from this.symm ▸ h4,
            have h5: σ' ⊨ vc.term (y ≡ term.unop op x),
            from this,
            have (prop.term (y ≡ term.unop op x)).to_vc = vc.term (y ≡ term.unop op x),
            by unfold prop.to_vc,

            show σ' ⊨ (prop.term (y ≡ term.unop op x)).to_vc,
            from this.symm ▸ h5
          ),
          valid_env.mpr h_impl
        ),
        have h2: (∀σ, (σ ⊨ P.to_vc) → σ ⊨ vc.implies (prop.term (y ≡ vy)).to_vc (prop.term (y ≡ term.unop op x)).to_vc),
        from (
          assume σ': env,
          assume : σ' ⊨ P.to_vc,

          have env_equiv: (∀y, y ∈ σ → (σ y = σ' y)),
          from env_equiv_of_translation_valid σ_verified σ' this,

          have h_impl: ((σ' ⊨ prop.to_vc (y ≡ vy))
                      → (σ' ⊨ prop.to_vc (y ≡ term.unop op x))),
          from (
            assume : σ' ⊨ prop.to_vc (y ≡ vy),
            have y_is_vy: σ' y = some vy, from valid_env.subst_of_eq this,
            have y_subst: term.subst_env σ' y = vy, from (term.subst_env.var.right vy).mp y_is_vy,

            have σ' x = vx, from eq_value_of_equiv_subst env_equiv x_is_vx,
            have x_subst: term.subst_env σ' x = vx, from (term.subst_env.var.right vx).mp this,

            have unop.apply op vx = some vy, from vy_is_op,
            have ⊨ vy ≡ term.unop op vx, from valid.unop.mp this,
            have h2: ⊨ (term.subst_env σ' y) ≡ term.unop op (term.subst_env σ' x),
            from x_subst.symm ▸ y_subst.symm ▸ this,

            have term.subst_env σ' (term.unop op x) = term.unop op (term.subst_env σ' x),
            from term.subst_env.unop,
            have ⊨ term.subst_env σ' y ≡ term.subst_env σ' (term.unop op x),
            from this.symm ▸ h2,
            have h3: ⊨ term.binop binop.eq (term.subst_env σ' y) (term.subst_env σ' (term.unop op x)),
            from this,

            have term.subst_env σ' (term.binop binop.eq y (term.unop op x))
                = term.binop binop.eq (term.subst_env σ' y) (term.subst_env σ' (term.unop op x)),
            from term.subst_env.binop,

            have h4: ⊨ term.subst_env σ' (term.binop binop.eq y (term.unop op x)),
            from this.symm ▸ h3,

            have vc.subst_env σ' (term.binop binop.eq y (term.unop op x))
                = term.subst_env σ' (term.binop binop.eq y (term.unop op x)),
            from vc.subst_env.term,

            have ⊨ vc.subst_env σ' (term.binop binop.eq y (term.unop op x)),
            from this.symm ▸ h4,
            have h5: σ' ⊨ vc.term (y ≡ term.unop op x),
            from this,
            have (prop.term (y ≡ term.unop op x)).to_vc = vc.term (y ≡ term.unop op x),
            by unfold prop.to_vc,

            show σ' ⊨ (prop.term (y ≡ term.unop op x)).to_vc,
            from this.symm ▸ h5
          ),
          valid_env.mpr h_impl
        ),
        have h3a: FV (prop.term (y ≡ vy)) = set.insert y ∅, from set.eq_of_subset_of_subset (
          assume z: var,
          assume : free_in_prop z (y ≡ vy),
          have free_in_term z (y ≡ vy), from free_in_prop.term.inv this,
          or.elim (free_in_term.binop.inv this) (
            assume : free_in_term z y,
            have z = y, from free_in_term.var.inv this,
            show z ∈ set.insert y ∅, from (set.mem_singleton_iff z y).mpr this
          ) (
            assume : free_in_term z vy,
            show z ∈ set.insert y ∅, from absurd this free_in_term.value.inv
          )
        ) (
          assume z: var,
          assume : z ∈ set.insert y ∅,
          have z = y, from (set.mem_singleton_iff z y).mp this,
          have free_in_term z y, from this ▸ free_in_term.var z,
          have free_in_term z (y ≡ vy), from free_in_term.binop₁ this,
          show free_in_prop z (y ≡ vy), from free_in_prop.term this
        ),
        have h3b: y ∈ FV (prop.term (y ≡ term.unop op x)), from (
          have free_in_term y y, from free_in_term.var y,
          have free_in_term y (y ≡ term.unop op x), from free_in_term.binop₁ this,
          show free_in_prop y (y ≡ term.unop op x), from free_in_prop.term this
        ),
        have h3c: FV (prop.term (y ≡ term.unop op x)) ⊆ FV P ∪ set.insert y ∅, from (
          assume z: var,
          assume : z ∈ FV (prop.term (y ≡ term.unop op x)),
          have free_in_term z (y ≡ term.unop op x), from free_in_prop.term.inv this,
          or.elim (free_in_term.binop.inv this) (
            assume : free_in_term z y,
            have z = y, from free_in_term.var.inv this,
            have z ∈ set.insert y ∅, from (set.mem_singleton_iff z y).mpr this,
            show z ∈ FV P ∪ set.insert y ∅, from set.mem_union_right (FV P) this
          ) (
            assume : free_in_term z (term.unop op x),
            have free_in_term z x, from free_in_term.unop.inv this,
            have z = x, from free_in_term.var.inv this,
            have z ∈ FV (↑R ⋀ P), from this.symm ▸ x_free_in_P,
            or.elim (free_in_prop.and.inv this) (
              assume : z ∈ FV ↑R,
              have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
              show z ∈ FV P ∪ set.insert y ∅, from set.mem_union_left (set.insert y ∅) this
            ) (
              assume : z ∈ FV P,
              show z ∈ FV P ∪ set.insert y ∅, from set.mem_union_left (set.insert y ∅) this
            )
          )
        ),
        have h4: (FV (↑R ⋀ P ⋀ (y ≡ vy)) = FV ((↑R ⋀ P) ⋀ (y ≡ term.unop op x))) ∧
          (∀σ, σ ⊨ vc.implies (↑R ⋀ P ⋀ (y ≡ vy)).to_vc ((↑R ⋀ P) ⋀ (y ≡ term.unop op x)).to_vc) ∧
          (∀σ t, σ ⊨ vc.implies ((↑(P ⋀ (y ≡ vy)) ⋀ Q) t).to_vc
                               ((↑P ⋀ propctx.exis y (↑(y ≡ term.unop op x) ⋀ Q)) t).to_vc) ∧
          (∀v: value, FV ((↑P ⋀ propctx.exis y (↑(y ≡ term.unop op x) ⋀ Q)) v)
                    ⊆ FV ((↑(P ⋀ (y ≡ vy)) ⋀ Q) v)),
        from @free_dominates_helper R P (y ≡ vy) (y ≡ term.unop op x) Q y h1 h2 h3a h3b h3c,
        have e'_verified': ↑R ⋀ P ⋀ y ≡ vy ⊩ e' : Q,
        from strengthen_exp e'_verified (↑R ⋀ P ⋀ y ≡ vy) h4.left h4.right.left,
        have h3: ⊩ₛ (R, σ[y↦vy], e') : ↑(P ⋀ y ≡ vy) ⋀ Q,
        from stack.dvcgen.top σ'_verified fv_R' R_valid' e'_verified',
        exists.intro (↑(P ⋀ y ≡ vy) ⋀ Q) ⟨h3, h4.right.right⟩
      }
    },
    case exp.dvcgen.binop op x y z e' Q x_free_in_P y_free_in_P z_not_free e'_verified vc_valid {
      cases e_steps,
      case dstep.binop vx vy vz x_is_vx y_is_vy vz_is_op { from
        have z_not_in_σ: z ∉ σ, from (
          assume : z ∈ σ,
          have z ∈ σ.dom, from this,
          have z ∈ FV P, from (free_iff_contains σ_verified) ▸ this,
          have z ∈ FV (↑R ⋀ P), from free_in_prop.and₂ this,
          show «false», from z_not_free this
        ),
        have σ'_verified: ⊩ (σ[z↦vz]) : P ⋀ z ≡ vz, from (
          or.elim (binop_result_not_function vz_is_op) (
            assume vz_is_true: vz = value.true,
            have σ'_verified: ⊩ (σ[z↦value.true]) : P ⋀ z ≡ value.true, from env.dvcgen.tru z_not_in_σ σ_verified,
            show ⊩ (σ[z↦vz]) : P ⋀ z ≡ vz, from vz_is_true.symm ▸ σ'_verified
          ) (
            assume : (vz = value.false) ∨ (∃n, vz = value.num n),
            or.elim this (
              assume vz_is_false: vz = value.false,
              have σ'_verified: ⊩ (σ[z↦value.false]) : P ⋀ z ≡ value.false, from env.dvcgen.fls z_not_in_σ σ_verified,
              show ⊩ (σ[z↦vz]) : P ⋀ z ≡ vz, from vz_is_false.symm ▸ σ'_verified
            ) (
              assume : ∃n, vz = value.num n,
              let ⟨n, vz_is_num⟩ := this in
              have σ'_verified: ⊩ (σ[z↦value.num n]) : P ⋀ z ≡ value.num n, from env.dvcgen.num z_not_in_σ σ_verified,
              show ⊩ (σ[z↦vz]) : P ⋀ z ≡ vz, from vz_is_num.symm ▸ σ'_verified
            )
          )
        ),
        have fv_R': FV R.to_prop ⊆ FV (P ⋀ z ≡ vz), from set.subset.trans fv_R free_in_prop.and_left_subset,
        have R_valid': σ[z↦vz] ⊨ R.to_prop.to_vc, from valid_with_additional_var R_valid,
        have h1: (∀σ, (σ ⊨ P.to_vc) →
                  σ ⊨ vc.implies (prop.term (z ≡ vz)).to_vc (prop.term (z ≡ term.binop op x y)).to_vc),
        from (
          assume σ': env,
          assume : σ' ⊨ P.to_vc,
          have env_equiv: (∀y, y ∈ σ → (σ y = σ' y)),
          from env_equiv_of_translation_valid σ_verified σ' this,

          have h_impl: ((σ' ⊨ prop.to_vc (z ≡ vz))
                      → (σ' ⊨ prop.to_vc (z ≡ term.binop op x y))),
          from (
            assume : σ' ⊨ prop.to_vc (z ≡ vz),
            have z_is_vz: σ' z = some vz, from valid_env.subst_of_eq this,
            have z_subst: term.subst_env σ' z = vz, from (term.subst_env.var.right vz).mp z_is_vz,

            have σ' x = vx, from eq_value_of_equiv_subst env_equiv x_is_vx,
            have x_subst: term.subst_env σ' x = vx, from (term.subst_env.var.right vx).mp this,

            have σ' y = vy, from eq_value_of_equiv_subst env_equiv y_is_vy,
            have y_subst: term.subst_env σ' y = vy, from (term.subst_env.var.right vy).mp this,

            have binop.apply op vx vy = some vz, from vz_is_op,
            have ⊨ vz ≡ term.binop op vx vy, from valid.binop.mp this,
            have h2: ⊨ (term.subst_env σ' z) ≡ term.binop op (term.subst_env σ' x) (term.subst_env σ' y),
            from x_subst.symm ▸ y_subst.symm ▸ z_subst.symm ▸ this,

            have term.subst_env σ' (term.binop op x y) = term.binop op (term.subst_env σ' x) (term.subst_env σ' y),
            from term.subst_env.binop,
            have ⊨ term.subst_env σ' z ≡ term.subst_env σ' (term.binop op x y),
            from this.symm ▸ h2,
            have h3: ⊨ term.binop binop.eq (term.subst_env σ' z) (term.subst_env σ' (term.binop op x y)),
            from this,

            have term.subst_env σ' (term.binop binop.eq z (term.binop op x y))
                = term.binop binop.eq (term.subst_env σ' z) (term.subst_env σ' (term.binop op x y)),
            from term.subst_env.binop,

            have h4: ⊨ term.subst_env σ' (term.binop binop.eq z (term.binop op x y)),
            from this.symm ▸ h3,

            have vc.subst_env σ' (term.binop binop.eq z (term.binop op x y))
                = term.subst_env σ' (term.binop binop.eq z (term.binop op x y)),
            from vc.subst_env.term,

            have ⊨ vc.subst_env σ' (term.binop binop.eq z (term.binop op x y)),
            from this.symm ▸ h4,
            have h5: σ' ⊨ vc.term (z ≡ term.binop op x y),
            from this,
            have (prop.term (z ≡ term.binop op x y)).to_vc = vc.term (z ≡ term.binop op x y),
            by unfold prop.to_vc,

            show σ' ⊨ (prop.term (z ≡ term.binop op x y)).to_vc,
            from this.symm ▸ h5
          ),
          valid_env.mpr h_impl
        ),
        have h2: (∀σ, (σ ⊨ P.to_vc) →
                 σ ⊨ vc.implies (prop.term (z ≡ vz)).to_vc (prop.term (z ≡ term.binop op x y)).to_vc),
        from (
          assume σ': env,
          assume : σ' ⊨ P.to_vc,

          have env_equiv: (∀y, y ∈ σ → (σ y = σ' y)),
          from env_equiv_of_translation_valid σ_verified σ' this,

          have h_impl: ((σ' ⊨ prop.to_vc (z ≡ vz))
                      → (σ' ⊨ prop.to_vc (z ≡ term.binop op x y))),
          from (
            assume : σ' ⊨ prop.to_vc (z ≡ vz),
            have z_is_vz: σ' z = some vz, from valid_env.subst_of_eq this,
            have z_subst: term.subst_env σ' z = vz, from (term.subst_env.var.right vz).mp z_is_vz,

            have σ' x = vx, from eq_value_of_equiv_subst env_equiv x_is_vx,
            have x_subst: term.subst_env σ' x = vx, from (term.subst_env.var.right vx).mp this,

            have σ' y = vy, from eq_value_of_equiv_subst env_equiv y_is_vy,
            have y_subst: term.subst_env σ' y = vy, from (term.subst_env.var.right vy).mp this,

            have binop.apply op vx vy = some vz, from vz_is_op,
            have ⊨ vz ≡ term.binop op vx vy, from valid.binop.mp this,
            have h2: ⊨ (term.subst_env σ' z) ≡ term.binop op (term.subst_env σ' x) (term.subst_env σ' y),
            from x_subst.symm ▸ y_subst.symm ▸ z_subst.symm ▸ this,

            have term.subst_env σ' (term.binop op x y) = term.binop op (term.subst_env σ' x) (term.subst_env σ' y),
            from term.subst_env.binop,
            have ⊨ term.subst_env σ' z ≡ term.subst_env σ' (term.binop op x y),
            from this.symm ▸ h2,
            have h3: ⊨ term.binop binop.eq (term.subst_env σ' z) (term.subst_env σ' (term.binop op x y)),
            from this,

            have term.subst_env σ' (term.binop binop.eq z (term.binop op x y))
                = term.binop binop.eq (term.subst_env σ' z) (term.subst_env σ' (term.binop op x y)),
            from term.subst_env.binop,

            have h4: ⊨ term.subst_env σ' (term.binop binop.eq z (term.binop op x y)),
            from this.symm ▸ h3,

            have vc.subst_env σ' (term.binop binop.eq z (term.binop op x y))
                = term.subst_env σ' (term.binop binop.eq z (term.binop op x y)),
            from vc.subst_env.term,

            have ⊨ vc.subst_env σ' (term.binop binop.eq z (term.binop op x y)),
            from this.symm ▸ h4,
            have h5: σ' ⊨ vc.term (z ≡ term.binop op x y),
            from this,
            have ((prop.term (z ≡ term.binop op x y)).to_vc = vc.term (z ≡ term.binop op x y)),
            by unfold prop.to_vc,

            show (σ' ⊨ (prop.term (z ≡ term.binop op x y)).to_vc),
            from this.symm ▸ h5
          ),
          valid_env.mpr h_impl
        ),
        have h3a: FV (prop.term (z ≡ vz)) = set.insert z ∅, from set.eq_of_subset_of_subset (
          assume x: var,
          assume : free_in_prop x (z ≡ vz),
          have free_in_term x (z ≡ vz), from free_in_prop.term.inv this,
          or.elim (free_in_term.binop.inv this) (
            assume : free_in_term x z,
            have x = z, from free_in_term.var.inv this,
            show x ∈ set.insert z ∅, from (set.mem_singleton_iff x z).mpr this
          ) (
            assume : free_in_term x vz,
            show x ∈ set.insert z ∅, from absurd this free_in_term.value.inv
          )
        ) (
          assume x: var,
          assume : x ∈ set.insert z ∅,
          have x = z, from (set.mem_singleton_iff x z).mp this,
          have free_in_term x z, from this ▸ free_in_term.var x,
          have free_in_term x (z ≡ vz), from free_in_term.binop₁ this,
          show free_in_prop x (z ≡ vz), from free_in_prop.term this
        ),
        have h3b: z ∈ FV (prop.term (z ≡ term.binop op x y)), from (
          have free_in_term z z, from free_in_term.var z,
          have free_in_term z (z ≡ term.binop op x y), from free_in_term.binop₁ this,
          show free_in_prop z (z ≡ term.binop op x y), from free_in_prop.term this
        ),
        have h3c: FV (prop.term (z ≡ term.binop op x y)) ⊆ FV P ∪ set.insert z ∅, from (
          assume a: var,
          assume : a ∈ FV (prop.term (z ≡ term.binop op x y)),
          have free_in_term a (z ≡ term.binop op x y), from free_in_prop.term.inv this,
          or.elim (free_in_term.binop.inv this) (
            assume : free_in_term a z,
            have a = z, from free_in_term.var.inv this,
            have a ∈ set.insert z ∅, from (set.mem_singleton_iff a z).mpr this,
            show a ∈ FV P ∪ set.insert z ∅, from set.mem_union_right (FV P) this
          ) (
            assume : free_in_term a (term.binop op x y),
            or.elim (free_in_term.binop.inv this) (
              assume : free_in_term a x,
              have a = x, from free_in_term.var.inv this,
              have a ∈ FV (↑R ⋀ P), from this.symm ▸ x_free_in_P,
              or.elim (free_in_prop.and.inv this) (
                assume : a ∈ FV ↑R,
                have a ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                show a ∈ FV P ∪ set.insert z ∅, from set.mem_union_left (set.insert z ∅) this
              ) (
                assume : a ∈ FV P,
                show a ∈ FV P ∪ set.insert z ∅, from set.mem_union_left (set.insert z ∅) this
              )
            ) (
              assume : free_in_term a y,
              have a = y, from free_in_term.var.inv this,
              have a ∈ FV (↑R ⋀ P), from this.symm ▸ y_free_in_P,
              or.elim (free_in_prop.and.inv this) (
                assume : a ∈ FV ↑R,
                have a ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                show a ∈ FV P ∪ set.insert z ∅, from set.mem_union_left (set.insert z ∅) this
              ) (
                assume : a ∈ FV P,
                show a ∈ FV P ∪ set.insert z ∅, from set.mem_union_left (set.insert z ∅) this
              )
            )
          )
        ),
        have h4: (FV (↑R ⋀ P ⋀ (z ≡ vz)) = FV ((↑R ⋀ P) ⋀ (z ≡ term.binop op x y))) ∧
          (∀σ, σ ⊨ vc.implies (↑R ⋀ P ⋀ (z ≡ vz)).to_vc ((↑R ⋀ P) ⋀ (z ≡ term.binop op x y)).to_vc) ∧
          (∀σ t, σ ⊨ vc.implies ((↑(P ⋀ (z ≡ vz)) ⋀ Q) t).to_vc
                               ((↑P ⋀ propctx.exis z (↑(z ≡ term.binop op x y) ⋀ Q)) t).to_vc) ∧
          (∀v: value, FV ((↑P ⋀ propctx.exis z (↑(z ≡ term.binop op x y) ⋀ Q)) v)
                    ⊆ FV ((↑(P ⋀ (z ≡ vz)) ⋀ Q) v)),
        from @free_dominates_helper R P (z ≡ vz) (z ≡ term.binop op x y) Q z h1 h2 h3a h3b h3c,
        have e'_verified': ↑R ⋀ P ⋀ z ≡ vz ⊩ e' : Q,
        from strengthen_exp e'_verified (↑R ⋀ P ⋀ z ≡ vz) h4.left h4.right.left,
        have h3: ⊩ₛ (R, σ[z↦vz], e') : ↑(P ⋀ z ≡ vz) ⋀ Q,
        from stack.dvcgen.top σ'_verified fv_R' R_valid' e'_verified',
        exists.intro (↑(P ⋀ z ≡ vz) ⋀ Q) ⟨h3, h4.right.right⟩
      }
    },
    case exp.dvcgen.app y f x e' Q' f_free_in_P x_free_in_P _ e'_verified vc_valid {
      cases e_steps
    },
    case exp.dvcgen.ite x e₂ e₁ Q₁ Q₂ x_free_in_P e₁_verified e₂_verified vc_valid {
      cases e_steps,

      case dstep.ite_true x_is_true { from

        have h1: FV (↑R ⋀ P) = FV ((↑R ⋀ P) ⋀ x), from set.eq_of_subset_of_subset (
          assume z: var,
          assume : z ∈ FV (↑R ⋀ P),
          show z ∈ FV ((↑R ⋀ P) ⋀ x), from free_in_prop.and₁ this
        ) (
          assume z: var,
          assume : z ∈ FV ((↑R ⋀ P) ⋀ x),
          or.elim (free_in_prop.and.inv this) id (
            assume : free_in_prop z x,
            have free_in_term z x, from free_in_prop.term.inv this,
            have z = x, from free_in_term.var.inv this,
            show z ∈ FV (↑R ⋀ P), from this.symm ▸ x_free_in_P
          )
        ),

        have h2: ∀σ', σ' ⊨ vc.implies (↑R ⋀ P).to_vc ((↑R ⋀ P) ⋀ x).to_vc,
        from λσ', vc.implies.and_right_intro (
          assume : σ' ⊨ (↑R ⋀ P).to_vc,
          have σ' ⊨ P.to_vc, from (valid_env.to_vc_and.elim this).right,
          have env_equiv: (∀y, y ∈ σ → (σ y = σ' y)),
          from env_equiv_of_translation_valid σ_verified σ' this,

          show σ' ⊨ (prop.term x).to_vc, from (
            have σ' x = some value.true, from eq_value_of_equiv_subst env_equiv x_is_true,
            have x_subst: term.subst_env σ' x = value.true, from (term.subst_env.var.right value.true).mp this,

            have ⊨ value.true, from valid.tru,
            have h7: ⊨ term.subst_env σ' x, from x_subst.symm ▸ this,
            have vc.subst_env σ' x = term.subst_env σ' x, from vc.subst_env.term,
            have ⊨ vc.subst_env σ' x, from this.symm ▸ h7,
            have h8: σ' ⊨ vc.term x, from this,
            have (prop.term x).to_vc = vc.term x, by unfold prop.to_vc,
            show σ' ⊨ (prop.term x).to_vc, from this.symm ▸ h8
          )
        ),

        have e'_verified: ↑R ⋀ P ⊩ e' : Q₁,
        from strengthen_exp e₁_verified (↑R ⋀ P) h1 h2,
        have h3: ⊩ₛ (R, σ, e') : P ⋀ Q₁,
        from stack.dvcgen.top σ_verified fv_R R_valid e'_verified,

        have hb1: ∀t, ((↑P ⋀ Q₁) t) = (P ⋀ Q₁ t), from λt, propctx_apply_pq,
        have hb2: ∀t, ((↑P ⋀ (propctx.implies ↑x Q₁) ⋀ (propctx.implies ↑(prop.not x) Q₂)) t)
                     = (P ⋀ (propctx.and (propctx.implies ↑x Q₁) (propctx.implies ↑(prop.not x) Q₂)) t),
        from λt, propctx_apply_pq,
        have hb5: ∀t, (propctx.and (propctx.implies ↑x Q₁) (propctx.implies ↑(prop.not x) Q₂)) t
                    = (prop.implies ↑x (Q₁ t) ⋀ prop.implies (prop.not x) (Q₂ t)),
        from (
          assume t: term,

          have hb3: (prop.term x).to_propctx t = (prop.term x), from unchanged_of_apply_propctx_without_hole,
          have hb4: (prop.not x).to_propctx t = (prop.not x), from unchanged_of_apply_propctx_without_hole,

          show (propctx.and (propctx.implies ↑x Q₁) (propctx.implies ↑(prop.not x) Q₂)) t
             = (prop.implies ↑x (Q₁ t) ⋀ prop.implies (prop.not x) (Q₂ t)),
          by calc
                    (propctx.and (propctx.implies ↑x Q₁) (propctx.implies ↑(prop.not x) Q₂)) t
                  = propctx.apply (propctx.and (propctx.implies ↑x Q₁) (propctx.implies ↑(prop.not x) Q₂)) t : rfl
              ... = (propctx.apply (propctx.implies ↑x Q₁) t ⋀ propctx.apply (propctx.implies ↑(prop.not x) Q₂) t)
                                : by unfold propctx.apply
              ... = (propctx.apply (propctx.or (propctx.not ↑x) Q₁) t ⋀ (propctx.implies ↑(prop.not x) Q₂) t) : rfl
              ... = (((propctx.apply (propctx.not ↑x) t) ⋁ (propctx.apply Q₁ t)) ⋀ (propctx.implies ↑(prop.not x) Q₂) t)
                                : by unfold propctx.apply
              ... = (((prop.not (propctx.apply ↑x t)) ⋁ (propctx.apply Q₁ t)) ⋀
                    (propctx.implies ↑(prop.not x) Q₂) t)
                                : by unfold propctx.apply
              ... = (((prop.not ((prop.term x).to_propctx t)) ⋁ (Q₁ t)) ⋀
                    (propctx.implies ↑(prop.not x) Q₂) t)
                                : rfl
              ... = ((prop.not (prop.term x) ⋁ (Q₁ t)) ⋀
                    (propctx.implies ↑(prop.not x) Q₂) t)
                                : by rw[hb3]
              ... = ((prop.implies x (Q₁ t)) ⋀
                    propctx.apply (propctx.or (propctx.not ↑(prop.not x)) Q₂) t)
                                : rfl
              ... = ((prop.implies x (Q₁ t)) ⋀
                    (propctx.apply (propctx.not ↑(prop.not x)) t ⋁ propctx.apply Q₂ t))
                                : by unfold propctx.apply
              ... = ((prop.implies x (Q₁ t)) ⋀
                    (prop.not (propctx.apply ↑(prop.not x) t) ⋁ propctx.apply Q₂ t))
                                : by unfold propctx.apply
              ... = ((prop.implies x (Q₁ t)) ⋀
                    (prop.not ((prop.not x).to_propctx t) ⋁ propctx.apply Q₂ t))
                                : rfl
              ... = ((prop.implies x (Q₁ t)) ⋀
                    (prop.not (prop.not x) ⋁ propctx.apply Q₂ t))
                                : by rw[hb4]
              ... = ((prop.implies x (Q₁ t)) ⋀ (prop.implies (prop.not x) (Q₂ t))) : rfl
        ),

        have h4: ∀σ' t,
          σ' ⊨ vc.implies ((↑P ⋀ Q₁) t).to_vc
                         ((↑P ⋀ (propctx.implies ↑x Q₁) ⋀ (propctx.implies ↑(prop.not x) Q₂)) t).to_vc, from (
          assume σ': env,
          assume t: term,

          have h5: σ' ⊨ vc.implies (P ⋀ Q₁ t).to_vc
                                  (P ⋀ prop.implies x (Q₁ t) ⋀ prop.implies (prop.not x) (Q₂ t)).to_vc,
          from vc.implies.same_left begin
            assume : σ' ⊨ P.to_vc,
            have env_equiv: (∀y, y ∈ σ → (σ y = σ' y)),
            from env_equiv_of_translation_valid σ_verified σ' this,
            have h6: (σ' x = some value.true), from eq_value_of_equiv_subst env_equiv x_is_true,
            have x_subst: (term.subst_env σ' x = value.true), from (term.subst_env.var.right value.true).mp h6,
            apply valid_env.mpr,
            assume h7,
            apply valid_env.to_vc_and,
            unfold prop.implies,
            unfold prop.to_vc,
            apply valid_env.or₂,
            from h7,
            unfold prop.implies,
            unfold prop.to_vc,
            apply valid_env.or₁,
            apply valid_env.not_not.mpr,
            change (σ'⊨prop.to_vc (prop.term (term.var x))),
            unfold prop.to_vc,
            change (⊨ vc.subst_env σ' (term.var x)),
            rw[vc.subst_env.term],
            change (⊨vc.term (term.subst_env σ' x)),
            rw[x_subst],
            from valid.tru
          end,

          (hb1 t).symm ▸ (hb2 t).symm ▸ (hb5 t).symm ▸ h5
        ),

        have h5: ∀v: value,
             FV ((↑P ⋀ propctx.and (propctx.implies ↑x Q₁) (propctx.implies ↑(prop.not x) Q₂)) v)
           ⊆ FV ((↑P ⋀ Q₁) v), from (
          assume v: value,

          have h6: FV (P ⋀ prop.implies x (Q₁ v) ⋀ prop.implies (prop.not x) (Q₂ v))
                 ⊆ FV (P ⋀ Q₁ v),
          from (
            assume z: var,
            assume : z ∈ FV (P ⋀ prop.implies x (Q₁ v) ⋀ prop.implies (prop.not x) (Q₂ v)),
            or.elim (free_in_prop.and.inv this) (
              assume : z ∈ FV P,
              show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
            ) (
              assume : z ∈ FV (prop.implies x (Q₁ v) ⋀ prop.implies (prop.not x) (Q₂ v)),
              or.elim (free_in_prop.and.inv this) (
                assume : z ∈ FV (prop.implies x (Q₁ v)),
                or.elim (free_in_prop.implies.inv this) (
                  assume : free_in_prop z x,
                  have free_in_term z x, from free_in_prop.term.inv this,
                  have z = x, from free_in_term.var.inv this,
                  have z ∈ FV (↑R ⋀ P), from this.symm ▸ x_free_in_P,
                  or.elim (free_in_prop.and.inv this) (
                    assume : z ∈ FV ↑R,
                    have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                    show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
                  ) (
                    assume : z ∈ FV P,
                    show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
                  )
                ) (
                  assume : z ∈ FV (Q₁ v),
                  show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₂ this
                )
              ) (
                assume : z ∈ FV (prop.implies (prop.not x) (Q₂ v)),
                or.elim (free_in_prop.implies.inv this) (
                  assume : z ∈ FV (prop.not x),
                  have free_in_prop z x, from free_in_prop.not.inv this,
                  have free_in_term z x, from free_in_prop.term.inv this,
                  have z = x, from free_in_term.var.inv this,
                  have z ∈ FV (↑R ⋀ P), from this.symm ▸ x_free_in_P,
                  or.elim (free_in_prop.and.inv this) (
                    assume : z ∈ FV ↑R,
                    have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                    show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
                  ) (
                    assume : z ∈ FV P,
                    show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
                  )
                ) (
                  assume : z ∈ FV (Q₂ v),
                  or.elim (exp.post_free e₂_verified v this) (
                    assume : z ∈ FV (term.value v),
                    show z ∈ FV (P ⋀ Q₁ v), from absurd this free_in_term.value.inv
                  ) (
                    assume : z ∈ FV ((↑R ⋀ P) ⋀ prop.not x),
                    or.elim (free_in_prop.and.inv this) (
                      assume : z ∈ FV (↑R ⋀ P),
                      or.elim (free_in_prop.and.inv this) (
                        assume : z ∈ FV ↑R,
                        have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                        show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
                      ) (
                        assume : z ∈ FV P,
                        show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
                      )
                    ) (
                      assume : z ∈ FV (prop.not x),
                      have free_in_prop z x, from free_in_prop.not.inv this,
                      have free_in_term z x, from free_in_prop.term.inv this,
                      have z = x, from free_in_term.var.inv this,
                      have z ∈ FV (↑R ⋀ P), from this.symm ▸ x_free_in_P,
                      or.elim (free_in_prop.and.inv this) (
                        assume : z ∈ FV ↑R,
                        have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                        show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
                      ) (
                        assume : z ∈ FV P,
                        show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
                      )
                    )
                  )
                )
              )
            )
          ),
          (hb1 v).symm ▸ (hb2 v).symm ▸ (hb5 v).symm ▸ h6
        ),
        exists.intro (↑P ⋀ Q₁) ⟨h3, ⟨h4, h5⟩⟩
      },

      case dstep.ite_false x_is_false { from

        have h1: FV (↑R ⋀ P) = FV ((↑R ⋀ P) ⋀ prop.not x), from set.eq_of_subset_of_subset (
          assume z: var,
          assume : z ∈ FV (↑R ⋀ P),
          show z ∈ FV ((↑R ⋀ P) ⋀ prop.not x), from free_in_prop.and₁ this
        ) (
          assume z: var,
          assume : z ∈ FV ((↑R ⋀ P) ⋀ prop.not x),
          or.elim (free_in_prop.and.inv this) id (
            assume : free_in_prop z (prop.not x),
            have free_in_prop z x, from free_in_prop.not.inv this,
            have free_in_term z x, from free_in_prop.term.inv this,
            have z = x, from free_in_term.var.inv this,
            show z ∈ FV (↑R ⋀ P), from this.symm ▸ x_free_in_P
          )
        ),

        have h2: ∀σ', σ' ⊨ vc.implies (↑R ⋀ P).to_vc ((↑R ⋀ P) ⋀ prop.not x).to_vc,
        from λσ', vc.implies.and_right_intro (
          assume : σ' ⊨ (↑R ⋀ P).to_vc,
          have σ' ⊨ P.to_vc, from (valid_env.to_vc_and.elim this).right,
          have env_equiv: (∀y, y ∈ σ → (σ y = σ' y)),
          from env_equiv_of_translation_valid σ_verified σ' this,

          show σ' ⊨ (prop.not x).to_vc, from (
            have σ' x = some value.false, from eq_value_of_equiv_subst env_equiv x_is_false,
            have x_subst: term.subst_env σ' x = value.false, from (term.subst_env.var.right value.false).mp this,

            have ⊨ vc.not value.false, from valid.not_false,
            have h7: ⊨ vc.not (term.subst_env σ' x), from x_subst.symm ▸ this,
            have vc.subst_env σ' x = term.subst_env σ' x, from vc.subst_env.term,
            have h8: ⊨ vc.not (vc.subst_env σ' x), from this.symm ▸ h7,
            have vc.subst_env σ' (vc.not x) = vc.not (vc.subst_env σ' x), from vc.subst_env.not,
            have ⊨ vc.subst_env σ' (vc.not x), from this.symm ▸ h8,
            have h9: σ' ⊨ vc.not x, from this,
            have (prop.not x).to_vc = vc.not x, by begin
              unfold prop.to_vc,
              change (vc.not (prop.to_vc (prop.term x)) = vc.not ↑x),
              unfold prop.to_vc,
              congr
            end,
            show σ' ⊨ (prop.not x).to_vc, from this.symm ▸ h9
          )
        ),

        have e'_verified: ↑R ⋀ P ⊩ e' : Q₂,
        from strengthen_exp e₂_verified (↑R ⋀ P) h1 h2,
        have h3: ⊩ₛ (R, σ, e') : P ⋀ Q₂,
        from stack.dvcgen.top σ_verified fv_R R_valid e'_verified,

        have hb1: ∀t, ((↑P ⋀ Q₂) t) = (P ⋀ Q₂ t), from λt, propctx_apply_pq,
        have hb2: ∀t, ((↑P ⋀ (propctx.implies ↑x Q₁) ⋀ (propctx.implies ↑(prop.not x) Q₂)) t)
                     = (P ⋀ (propctx.and (propctx.implies ↑x Q₁) (propctx.implies ↑(prop.not x) Q₂)) t),
        from λt, propctx_apply_pq,
        have hb5: ∀t, (propctx.and (propctx.implies ↑x Q₁) (propctx.implies ↑(prop.not x) Q₂)) t
                    = (prop.implies ↑x (Q₁ t) ⋀ prop.implies (prop.not x) (Q₂ t)),
        from (
          assume t: term,

          have hb3: (prop.term x).to_propctx t = (prop.term x), from unchanged_of_apply_propctx_without_hole,
          have hb4: (prop.not x).to_propctx t = (prop.not x), from unchanged_of_apply_propctx_without_hole,

          show (propctx.and (propctx.implies ↑x Q₁) (propctx.implies ↑(prop.not x) Q₂)) t
             = (prop.implies ↑x (Q₁ t) ⋀ prop.implies (prop.not x) (Q₂ t)),
          by calc
                    (propctx.and (propctx.implies ↑x Q₁) (propctx.implies ↑(prop.not x) Q₂)) t
                  = propctx.apply (propctx.and (propctx.implies ↑x Q₁) (propctx.implies ↑(prop.not x) Q₂)) t : rfl
              ... = (propctx.apply (propctx.implies ↑x Q₁) t ⋀ propctx.apply (propctx.implies ↑(prop.not x) Q₂) t)
                                : by unfold propctx.apply
              ... = (propctx.apply (propctx.or (propctx.not ↑x) Q₁) t ⋀ (propctx.implies ↑(prop.not x) Q₂) t) : rfl
              ... = (((propctx.apply (propctx.not ↑x) t) ⋁ (propctx.apply Q₁ t)) ⋀ (propctx.implies ↑(prop.not x) Q₂) t)
                                : by unfold propctx.apply
              ... = (((prop.not (propctx.apply ↑x t)) ⋁ (propctx.apply Q₁ t)) ⋀
                    (propctx.implies ↑(prop.not x) Q₂) t)
                                : by unfold propctx.apply
              ... = (((prop.not ((prop.term x).to_propctx t)) ⋁ (Q₁ t)) ⋀
                    (propctx.implies ↑(prop.not x) Q₂) t)
                                : rfl
              ... = ((prop.not (prop.term x) ⋁ (Q₁ t)) ⋀
                    (propctx.implies ↑(prop.not x) Q₂) t)
                                : by rw[hb3]
              ... = ((prop.implies x (Q₁ t)) ⋀
                    propctx.apply (propctx.or (propctx.not ↑(prop.not x)) Q₂) t)
                                : rfl
              ... = ((prop.implies x (Q₁ t)) ⋀
                    (propctx.apply (propctx.not ↑(prop.not x)) t ⋁ propctx.apply Q₂ t))
                                : by unfold propctx.apply
              ... = ((prop.implies x (Q₁ t)) ⋀
                    (prop.not (propctx.apply ↑(prop.not x) t) ⋁ propctx.apply Q₂ t))
                                : by unfold propctx.apply
              ... = ((prop.implies x (Q₁ t)) ⋀
                    (prop.not ((prop.not x).to_propctx t) ⋁ propctx.apply Q₂ t))
                                : rfl
              ... = ((prop.implies x (Q₁ t)) ⋀
                    (prop.not (prop.not x) ⋁ propctx.apply Q₂ t))
                                : by rw[hb4]
              ... = ((prop.implies x (Q₁ t)) ⋀ (prop.implies (prop.not x) (Q₂ t))) : rfl
        ),

        have h4: ∀σ' t,
          σ' ⊨ vc.implies ((↑P ⋀ Q₂) t).to_vc
                         ((↑P ⋀ (propctx.implies ↑x Q₁) ⋀ (propctx.implies ↑(prop.not x) Q₂)) t).to_vc, from (
          assume σ': env,
          assume t: term,

          have h5: σ' ⊨ vc.implies (P ⋀ Q₂ t).to_vc
                                  (P ⋀ prop.implies x (Q₁ t) ⋀ prop.implies (prop.not x) (Q₂ t)).to_vc,
          from vc.implies.same_left begin
            assume : σ' ⊨ P.to_vc,
            have env_equiv: (∀y, y ∈ σ → (σ y = σ' y)),
            from env_equiv_of_translation_valid σ_verified σ' this,
            have h6: (σ' x = some value.false), from eq_value_of_equiv_subst env_equiv x_is_false,
            have x_subst: (term.subst_env σ' x = value.false), from (term.subst_env.var.right value.false).mp h6,
            apply valid_env.mpr,
            assume h7,
            apply valid_env.to_vc_and,
            unfold prop.implies,
            unfold prop.to_vc,
            apply valid_env.or₁,
            change (σ' ⊨ prop.to_vc (prop.not (term.var x))),
            unfold prop.to_vc,
            change (σ' ⊨ vc.not (prop.to_vc (prop.term (term.var x)))),
            unfold prop.to_vc,
            change (⊨ vc.subst_env σ' (vc.not (term.var x))),
            rw[vc.subst_env.not],
            rw[vc.subst_env.term],
            change (⊨ vc.not (vc.term (term.subst_env σ' x))),
            rw[x_subst],
            from valid.not_false,

            unfold prop.implies,
            unfold prop.to_vc,
            apply valid_env.or₂,
            from h7
          end,

          (hb1 t).symm ▸ (hb2 t).symm ▸ (hb5 t).symm ▸ h5
        ),

        have h5: ∀v: value,
             FV ((↑P ⋀ propctx.and (propctx.implies ↑x Q₁) (propctx.implies ↑(prop.not x) Q₂)) v)
           ⊆ FV ((↑P ⋀ Q₂) v), from (
          assume v: value,

          have h6: FV (P ⋀ prop.implies x (Q₁ v) ⋀ prop.implies (prop.not x) (Q₂ v))
                 ⊆ FV (P ⋀ Q₂ v),
          from (
            assume z: var,
            assume : z ∈ FV (P ⋀ prop.implies x (Q₁ v) ⋀ prop.implies (prop.not x) (Q₂ v)),
            or.elim (free_in_prop.and.inv this) (
              assume : z ∈ FV P,
              show z ∈ FV (P ⋀ Q₂ v), from free_in_prop.and₁ this
            ) (
              assume : z ∈ FV (prop.implies x (Q₁ v) ⋀ prop.implies (prop.not x) (Q₂ v)),
              or.elim (free_in_prop.and.inv this) (
                assume : z ∈ FV (prop.implies x (Q₁ v)),
                or.elim (free_in_prop.implies.inv this) (
                  assume : free_in_prop z x,
                  have free_in_term z x, from free_in_prop.term.inv this,
                  have z = x, from free_in_term.var.inv this,
                  have z ∈ FV (↑R ⋀ P), from this.symm ▸ x_free_in_P,
                  or.elim (free_in_prop.and.inv this) (
                    assume : z ∈ FV ↑R,
                    have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                    show z ∈ FV (P ⋀ Q₂ v), from free_in_prop.and₁ this
                  ) (
                    assume : z ∈ FV P,
                    show z ∈ FV (P ⋀ Q₂ v), from free_in_prop.and₁ this
                  )
                ) (
                  assume : z ∈ FV (Q₁ v),
                  or.elim (exp.post_free e₁_verified v this) (
                    assume : z ∈ FV (term.value v),
                    show z ∈ FV (P ⋀ Q₂ v), from absurd this free_in_term.value.inv
                  ) (
                    assume : z ∈ FV ((↑R ⋀ P) ⋀ x),
                    or.elim (free_in_prop.and.inv this) (
                      assume : z ∈ FV (↑R ⋀ P),
                      or.elim (free_in_prop.and.inv this) (
                        assume : z ∈ FV ↑R,
                        have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                        show z ∈ FV (P ⋀ Q₂ v), from free_in_prop.and₁ this
                      ) (
                        assume : z ∈ FV P,
                        show z ∈ FV (P ⋀ Q₂ v), from free_in_prop.and₁ this
                      )
                    ) (
                      assume : z ∈ FV (prop.term x),
                      have free_in_term z x, from free_in_prop.term.inv this,
                      have z = x, from free_in_term.var.inv this,
                      have z ∈ FV (↑R ⋀ P), from this.symm ▸ x_free_in_P,
                      or.elim (free_in_prop.and.inv this) (
                        assume : z ∈ FV ↑R,
                        have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                        show z ∈ FV (P ⋀ Q₂ v), from free_in_prop.and₁ this
                      ) (
                        assume : z ∈ FV P,
                        show z ∈ FV (P ⋀ Q₂ v), from free_in_prop.and₁ this
                      )
                    )
                  )
                )
              ) (
                assume : z ∈ FV (prop.implies (prop.not x) (Q₂ v)),
                or.elim (free_in_prop.implies.inv this) (
                  assume : z ∈ FV (prop.not x),
                  have free_in_prop z x, from free_in_prop.not.inv this,
                  have free_in_term z x, from free_in_prop.term.inv this,
                  have z = x, from free_in_term.var.inv this,
                  have z ∈ FV (↑R ⋀ P), from this.symm ▸ x_free_in_P,
                  or.elim (free_in_prop.and.inv this) (
                    assume : z ∈ FV ↑R,
                    have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                    show z ∈ FV (P ⋀ Q₂ v), from free_in_prop.and₁ this
                  ) (
                    assume : z ∈ FV P,
                    show z ∈ FV (P ⋀ Q₂ v), from free_in_prop.and₁ this
                  )
                ) (
                  assume : z ∈ FV (Q₂ v),
                  show z ∈ FV (P ⋀ Q₂ v), from free_in_prop.and₂ this
                )
              )
            )
          ),
          (hb1 v).symm ▸ (hb2 v).symm ▸ (hb5 v).symm ▸ h6
        ),
        exists.intro (↑P ⋀ Q₂) ⟨h3, ⟨h4, h5⟩⟩
      }
    },
    case exp.dvcgen.return x x_free_in_P {
      cases e_steps
    }
  end

lemma inlined_dominates_spec {σ σ₁: env} {P: prop} {Q: propctx} {f x: var} {R S: spec} {e: exp}:
  (⊩ σ₁ : P) → (f ∉ σ₁) → (x ∉ σ₁) → (x ≠ f) → (σ ⊨ P.to_vc) → (σ f = value.func f x R S e σ₁) →
  (⊩ (σ₁[f↦value.func f x R S e σ₁]) : (P ⋀ f ≡ value.func f x R S e σ₁ ⋀
                  prop.subst_env (σ₁[f↦value.func f x R S e σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)))) →
  (σ ⊨ vc.implies (prop.subst_env (σ₁[f↦value.func f x R S e σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S))).to_vc
                  (spec.func f x R S).to_prop.to_vc) :=
  
  let vf := value.func f x R S e σ₁ in
  let forallp' := (prop.implies R.to_prop (prop.pre f x) ⋀
                   prop.implies (prop.post f x) (Q (term.app f x) ⋀ S.to_prop)) in

  let forallp := (prop.implies R.to_prop (prop.pre f x) ⋀ prop.implies (prop.post f x) S.to_prop) in

  let P' := P ⋀ f ≡ value.func f x R S e σ₁ ⋀
            prop.subst_env (σ₁[f↦vf]) (prop.func f x R (Q (term.app f x) ⋀ S)) in

  assume σ₁_verified: ⊩ σ₁ : P,
  assume f_not_in_σ₁: f ∉ σ₁,
  assume x_not_in_σ₁: x ∉ σ₁,
  assume x_neq_f: x ≠ f,
  assume P_valid: σ ⊨ P.to_vc,
  assume f_is_vf: σ f = value.func f x R S e σ₁,
  assume σ₁f_verified: ⊩ (σ₁[f↦vf]) : P',

  have (∀y, y ∈ σ₁ → (σ₁ y = σ y)),
  from env_equiv_of_translation_valid σ₁_verified σ P_valid,

  have env_equiv: (∀y, y ∈ (σ₁[f↦vf]) → ((σ₁[f↦vf]) y = σ y)),
  from env.equiv_of_rest_and_same this f_not_in_σ₁ f_is_vf,

  have h1: (σ₁[f↦vf]) f = σ f, from env_equiv f (env.contains.same),
  have σ f = vf, from eq.trans h1.symm (env.apply_of_contains f_not_in_σ₁),
  have h2: term.subst_env σ f = vf, from (term.subst_env.var.right vf).mp this,

  have h3: (prop.subst_env (σ₁[f↦vf]) (prop.func f x R (Q (term.app f x) ⋀ S)))
         = (term.unop unop.isFunc vf ⋀ prop.forallc x (prop.subst_env (σ₁[f↦vf]) forallp')), from (

    have h3: prop.func f x R (Q (term.app f x) ⋀ S) = (term.unop unop.isFunc f ⋀ prop.forallc x forallp'),
    from rfl,
    have h4: prop.subst_env (σ₁[f↦vf]) (term.unop unop.isFunc f ⋀ prop.forallc x forallp')
      = (prop.subst_env (σ₁[f↦vf]) (term.unop unop.isFunc f) ⋀ prop.subst_env (σ₁[f↦vf]) (prop.forallc x forallp')),
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
    have h8: prop.subst_env (σ₁[f↦vf]) (prop.forallc x forallp')
          = prop.forallc x (prop.subst_env (σ₁[f↦vf]) forallp'),
    from prop.subst_env.forallc_not_in this,

    show (prop.subst_env (σ₁[f↦vf]) (prop.func f x R (Q (term.app f x) ⋀ S)))
          = (term.unop unop.isFunc vf ⋀ prop.forallc x (prop.subst_env (σ₁[f↦vf]) forallp')),
    from h7 ▸ h8 ▸ h7 ▸ h6 ▸ h5 ▸ h3.symm ▸ h4
  ),

  have h4: spec.to_prop (spec.func f x R S) = (term.unop unop.isFunc f ⋀ prop.forallc x forallp),
  by unfold spec.to_prop,

  have h5: σ ⊨ vc.implies (term.unop unop.isFunc vf) (term.unop unop.isFunc f),
  from valid_env.mpr (
    assume : σ ⊨ prop.to_vc (term.unop unop.isFunc vf),
    have unop.apply unop.isFunc vf = value.true, by unfold unop.apply,
    have ⊨ value.true ≡ term.unop unop.isFunc vf, from valid.unop.mp this,
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
    have prop.to_vc (prop.term (term.unop unop.isFunc f)) = vc.term (term.unop unop.isFunc f),
    by unfold prop.to_vc,
    show σ ⊨ (prop.term (term.unop unop.isFunc f)).to_vc, from this.symm ▸ h74
  ),

  have h6: σ ⊨ vc.implies (prop.forallc x (prop.subst_env (σ₁[f↦vf]) forallp')).to_vc (prop.forallc x forallp).to_vc,
  by begin
    apply valid_env.mpr,
    assume h1,
    unfold prop.to_vc,
    rw[vc.subst_env.univ],
    apply valid.univ.mp,
    assume v: value,
    unfold prop.to_vc at h1,
    rw[vc.subst_env.univ] at h1,
    have h2, from valid.univ.mpr h1 v,
    have h3: (vc.substt x ↑v (vc.subst_env (env.without σ x) (prop.to_vc (prop.subst_env (σ₁[f↦vf]) forallp')))
            = vc.subst x v (vc.subst_env (env.without σ x) (prop.to_vc (prop.subst_env (σ₁[f↦vf]) forallp')))),
    from vc.substt_value_eq_subst,
    rw[h3] at h2,

    have : ¬ (x = f ∨ x ∈ σ₁), from not_or_distrib.mpr ⟨x_neq_f, x_not_in_σ₁⟩,
    have h61: x ∉ (σ₁[f↦vf]), from mt env.contains.inv this,
    have : (∀y, y ∈ (σ₁[f↦vf]) → ((σ₁[f↦vf]) y = (σ.without x) y)),
    from env.remove_unimportant_equivalence env_equiv h61,
    have : (∀y, y ∈ (σ₁[f↦vf]) → ((σ₁[f↦vf]) y = (σ.without x[x↦v]) y)),
    from env.equiv_of_not_contains this h61,
    have h7: (((σ.without x)[x↦v]) ⊨ vc.implies (prop.subst_env (σ₁[f↦vf]) forallp').to_vc forallp'.to_vc),
    from vc.implies.equiv_subst this,
    have h82: (((σ.without x)[x↦v]) ⊨ vc.implies (prop.implies (prop.post f x) (Q (term.app f x) ⋀ S.to_prop)).to_vc
                                                 (prop.implies (prop.post f x) S.to_prop).to_vc),
    by begin
      apply valid_env.mpr,
      assume h1,
      unfold prop.implies,
      unfold prop.implies at h1,
      unfold prop.to_vc,
      unfold prop.to_vc at h1,
      cases valid_env.or.elim h1 with h2 h2,
      apply valid_env.or₁,
      from h2,
      apply valid_env.or₂,
      from (valid_env.to_vc_and.elim h2).right
    end,
    have h8: (((σ.without x)[x↦v]) ⊨ vc.implies forallp'.to_vc forallp.to_vc),
    from vc.implies.same_left (λ_, h82),
    have h81, from valid_env.mp h8,

    have h9: (vc.subst x v (vc.subst_env (env.without σ x) (prop.to_vc forallp))
            = vc.subst_env (env.without σ x[x↦v]) (prop.to_vc forallp)),
    by unfold vc.subst_env,
    rw[h9],
    apply h81,
    have h71, from valid_env.mp h7,
    apply h71,

    have h10: (vc.subst x v (vc.subst_env (env.without σ x) (prop.to_vc (prop.subst_env (σ₁[f↦vf]) forallp')))
             = vc.subst_env (env.without σ x[x↦v]) (prop.to_vc (prop.subst_env (σ₁[f↦vf]) forallp'))),
    by unfold vc.subst_env,
    rw[h10] at h2,
    from h2
  end,
  have h7: σ ⊨ vc.implies (prop.term (term.unop unop.isFunc vf) ⋀
                            prop.forallc x (prop.subst_env (σ₁[f↦vf]) forallp')).to_vc
                          (prop.term (term.unop unop.isFunc f) ⋀ prop.forallc x forallp).to_vc,
  from vc.implies.and_intro h5 (λ_, h6),
  show σ ⊨ vc.implies (prop.subst_env (σ₁[f↦value.func f x R S e σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S))).to_vc
                      (spec.to_prop (spec.func f x R S)).to_vc,
  from h3.symm ▸ h4.symm ▸ h7

/-

lemma inlined_dominates_n_spec {σ σ₁: env} {P: prop} {Q: propctx} {f x: var} {R S: spec} {e: exp} {H: history}:
  (⊩ σ₁ : P) → (f ∉ σ₁) → (x ∉ σ₁) → (x ≠ f) → (σ ⊨ P.to_vc) → (σ f = value.func f x R S e H σ₁) →
  (⊩ (σ₁[f↦value.func f x R S e H σ₁]) : (P ⋀ f ≡ value.func f x R S e H σ₁ ⋀
                  prop.subst_env (σ₁[f↦value.func f x R S e H σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)))) →
  σ ⊨ vc.implies (prop.subst_env (σ₁[f↦value.func f x R S e H σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)))
                (spec.func f x R S) :=
  
  let vf := value.func f x R S e H σ₁ in
  let forallp' := (prop.implies R.to_prop (prop.pre f x) ⋀
                   prop.implies (prop.post f x) (Q (term.app f x) ⋀ S.to_prop)) in

  let forallp := (prop.implies R.to_prop (prop.pre f x) ⋀ prop.implies (prop.post f x) S.to_prop) in

  let P' := P ⋀ f ≡ value.func f x R S e H σ₁ ⋀
            prop.subst_env (σ₁[f↦vf]) (prop.func f x R (Q (term.app f x) ⋀ S)) in

  assume σ₁_verified: ⊩ σ₁ : P,
  assume f_not_in_σ₁: f ∉ σ₁,
  assume x_not_in_σ₁: x ∉ σ₁,
  assume x_neq_f: x ≠ f,
  assume P_valid: σ ⊨ P.to_vc,
  assume f_is_vf: σ f = value.func f x R S e H σ₁,
  assume σ₁f_verified: ⊩ (σ₁[f↦vf]) : P',

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
    from prop.subst_env.forallc_not_in this,

    show (prop.subst_env (σ₁[f↦vf]) (prop.func f x R (Q (term.app f x) ⋀ S)))
          = (term.unop unop.isFunc vf ⋀ prop.forallc x vf (prop.subst_env (σ₁[f↦vf]) forallp')),
    from h7 ▸ h8 ▸ h7 ▸ h6 ▸ h5 ▸ h3.symm ▸ h4
  ),

  have h4: spec.to_prop (spec.func f x R S) = (term.unop unop.isFunc f ⋀ prop.forallc x f forallp),
  by unfold spec.to_prop,

  have h5: σ ⊨ vc.implies (term.unop unop.isFunc vf) (term.unop unop.isFunc f),
  from vc.implies.no_quantifiers (
    assume : σ ⊨ prop.to_vc (term.unop unop.isFunc vf),
    have unop.apply unop.isFunc vf = value.true, by unfold unop.apply,
    have ⊨ value.true ≡ term.unop unop.isFunc vf, from valid.unop.mp this,
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
    have prop.to_vc (prop.term (term.unop unop.isFunc f)) = vc.term (term.unop unop.isFunc f),
    by unfold prop.to_vc,
    have h8: σ ⊨ (prop.term (term.unop unop.isFunc f)).to_vc, from this.symm ▸ h74,
    have calls_n (prop.term (term.unop unop.isFunc f)) = ∅, from set.eq_empty_of_forall_not_mem (
      assume c': calltrigger,
      assume : c' ∈ calls_n (term.unop unop.isFunc f),
      show «false», from prop.has_call_n.term.inv this
    ),
    have (prop.term (term.unop unop.isFunc f)).to_vc = (prop.term (term.unop unop.isFunc f)).to_vc,
    from instantiated_n_eq_to_vc_without_calls this,
    show σ ⊨ (prop.term (term.unop unop.isFunc f)).to_vc, from this.symm ▸ h8
  ) (
    show calls_n_subst σ (term.unop unop.isFunc f) ⊆ calls_n_subst σ (term.unop unop.isFunc vf), from (
      assume c: calltrigger,
      assume : c ∈ calls_n_subst σ (term.unop unop.isFunc f),
      @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_n (term.unop unop.isFunc f))
          (λa, a ∈ calls_n_subst σ (term.unop unop.isFunc vf)) c this (
        assume c': calltrigger,
        assume : c' ∈ calls_n (term.unop unop.isFunc f),
        show calltrigger.subst σ c' ∈ calls_n_subst σ (term.unop unop.isFunc vf),
        from absurd this prop.has_call_n.term.inv
      )
    )
  ) (
    show quantifiers_n (term.unop unop.isFunc f) = ∅, from set.eq_empty_of_forall_not_mem (
      assume q: callquantifier,
      assume : q ∈ quantifiers_n (term.unop unop.isFunc f),
      show «false», from prop.has_quantifier_n.term.inv this
    )
  ),

  have h6: σ ⊨ vc.implies (prop.forallc x vf (prop.subst_env (σ₁[f↦vf]) forallp')) (prop.forallc x f forallp),
  from vc.implies.quantifier (
    assume v: value,

    have ¬ (x = f ∨ x ∈ σ₁), from not_or_distrib.mpr ⟨x_neq_f, x_not_in_σ₁⟩,
    have h61: x ∉ (σ₁[f↦vf]), from mt env.contains.inv this,
    have (∀y, y ∈ (σ₁[f↦vf]) → ((σ₁[f↦vf]) y = (σ.without x) y)),
    from env.remove_unimportant_equivalence env_equiv h61,
    have (∀y, y ∈ (σ₁[f↦vf]) → ((σ₁[f↦vf]) y = (σ.without x[x↦v]) y)),
    from env.equiv_of_not_contains this h61,
    have h7: (σ.without ⊨ vc.implies x[x↦v]) (prop.subst_env (σ₁[f↦vf]) forallp') forallp',
    from dominates_n_equiv_subst this,
    have h82: (σ.without ⊨ vc.implies x[x↦v]) (prop.implies (prop.post f x) (Q (term.app f x) ⋀ S.to_prop))
                                 (prop.implies (prop.post f x) S.to_prop),
    from vc.implies.or_intro vc.implies.self vc.implies.of_and_right,
    have h8: (σ.without ⊨ vc.implies x[x↦v]) forallp' forallp,
    from vc.implies.same_left (λ_, h82),
    show (σ.without ⊨ vc.implies x[x↦v]) (prop.subst_env (σ₁[f↦vf]) forallp') forallp,
    from vc.implies.trans h7 h8
  ),
  have h7: σ ⊨ vc.implies (term.unop unop.isFunc vf ⋀ prop.forallc x vf (prop.subst_env (σ₁[f↦vf]) forallp'))
                       (term.unop unop.isFunc f ⋀ prop.forallc x f forallp),
  from vc.implies.and_intro h5 (λ_, h6),
  show σ ⊨ vc.implies (prop.subst_env (σ₁[f↦value.func f x R S e H σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)))
                   (spec.to_prop (spec.func f x R S)),
  from h3.symm ▸ h4.symm ▸ h7

-/

theorem preservation {s: dstack} {Q: propctx}:
   (⊩ₛ s : Q) → ∀s', (s ⟹ s') →
   ∃Q', (⊩ₛ s' : Q') ∧ (∀σ' t, σ' ⊨ vc.implies (Q' t).to_vc (Q t).to_vc) ∧ (∀v: value, FV (Q v) ⊆ FV (Q' v)) :=
  assume s_verified:  ⊩ₛ s : Q,
  begin
    induction s_verified,
    case stack.dvcgen.top σ e R P Q σ_verified fv_R R_valid e_verified {
      assume s',
      assume s_steps: ((R, σ, e) ⟹ s'),

      have R_closed: closed_subst σ R.to_prop, from (
        assume z: var,
        assume : z ∈ FV R.to_prop,
        have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
        show z ∈ σ.dom, from (free_iff_contains σ_verified).symm ▸ this
      ),

      cases s_steps,
      case dstep.tru x e {
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case dstep.fals x e {
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case dstep.num n e x {
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case dstep.closure R' S' f x e₁ e₂ {
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case dstep.unop op x y e {
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case dstep.binop op x y z e {
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case dstep.app f x y σ₂ g R₂ S₂ gx e₁ e₂ vₓ f_is_func x_is_vₓ {
        cases e_verified,
        case exp.dvcgen.app Q f_free x_free y_not_free e₂_verified func_vc { from

          have ∃σ' Q', ⊩ (σ'[f ↦ value.func g gx R₂ S₂ e₁ σ₂]) : Q',
          from env.dvcgen.inv σ_verified f_is_func,
          let ⟨σ', Q', ha1⟩ := this in

          have ∃Q₁ Q₂ Q₃,
            f ∉ σ' ∧
            g ∉ σ₂ ∧
            gx ∉ σ₂ ∧
            g ≠ gx ∧
            (⊩ σ' : Q₁) ∧
            (⊩ σ₂ : Q₂) ∧
            gx ∈ FV R₂.to_prop.to_vc ∧
            FV R₂.to_prop ⊆ FV Q₂ ∪ { g, gx } ∧
            FV S₂.to_prop ⊆ FV Q₂ ∪ { g, gx } ∧
            (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂ ⊩ e₁ : Q₃) ∧
            ⦃prop.implies (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂ ⋀ Q₃ (term.app g gx)) S₂⦄ ∧
            (Q' = (Q₁ ⋀
                ((f ≡ (value.func g gx R₂ S₂ e₁ σ₂)) ⋀
                prop.subst_env (σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂])
                (prop.func g gx R₂ (Q₃ (term.app g gx) ⋀ S₂))))),
          from env.dvcgen.func.inv ha1,

          let ⟨Q₁, Q₂, Q₃, ha2⟩ := this in
          let Q₂' := (Q₂ ⋀
                ((g ≡ (value.func g gx R₂ S₂ e₁ σ₂)) ⋀
                prop.subst_env (σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂])
                (prop.func g gx R₂ (Q₃ (term.app g gx) ⋀ S₂)))) in

          have ha3: ⊩ (σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂]) : Q₂',
          from env.dvcgen.func
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

          have ∃σ'' Q'', ⊩ (σ''[x ↦ vₓ]) : Q'',
          from env.dvcgen.inv σ_verified x_is_vₓ,
          let ⟨σ'', Q'', ha4⟩ := this in

          have gx ∉ (σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂]), from (
            assume : gx ∈ (σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂]),
            or.elim (env.contains.inv this) (
              assume : gx = g,
              show «false», from ha2.right.right.right.left this.symm
            ) (
              assume : gx ∈ σ₂,
              show «false», from ha2.right.right.left this
            )
          ),
          have ∃P₃', ⊩ (σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂][gx↦vₓ]) : Q₂' ⋀ P₃',
          from env.dvcgen.copy ha3 this ha4,
          let ⟨P₃', ha5⟩ := this in
          let P₃ := Q₂' ⋀ P₃' in

          have ha6: Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂ ⊩ e₁ : Q₃,
          from ha2.right.right.right.right.right.right.right.right.right.left,

          have ha7: FV R₂.to_prop ⊆ FV P₃, from (
            have hb1: FV P₃ = (σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂][gx↦vₓ]).dom, from (free_iff_contains ha5).symm,
            have hb2: (σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂][gx↦vₓ]).dom
                    = (σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂]).dom ∪ set.insert gx ∅, from env.dom.inv,
            have hb3: (σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂]).dom
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

          have ha8: FV (↑R₂ ⋀ P₃) = FV (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from (
            have hb1: FV P₃ = (σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂][gx↦vₓ]).dom, from (free_iff_contains ha5).symm,
            have hb2: (σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂][gx↦vₓ]).dom
                    = (σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂]).dom ∪ set.insert gx ∅, from env.dom.inv,
            have hb3: (σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂]).dom
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
                    assume x_free_in_forallp: free_in_prop x (prop.forallc gx forallp),
                    have free_in_prop x forallp,
                    from (free_in_prop.forallc.inv x_free_in_forallp).right,
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
                have x ∈ FV R₂.to_prop.to_vc,
                from this.symm ▸ ha2.right.right.right.right.right.right.left,
                have x ∈ FV R₂.to_prop,
                from set.mem_of_mem_of_subset this free_in_prop_of_free_in_to_vc,
                have free_in_prop x (spec.func g gx R₂ S₂ ⋀ R₂), from free_in_prop.and₂ this,
                show x ∈ FV (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from free_in_prop.and₂ this
              )
            ),

            have FV P₃ = FV (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from eq.trans hb4 hb5.symm,
            show FV (↑R₂ ⋀ P₃) = FV (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂),
            from eq.trans free_in_prop.and_symm (eq.trans hb9 this)
          ),

          have ha9: σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂][gx↦vₓ] ⊨ prop.to_vc (spec.to_prop R₂),
          from (
            have env_has_f: f ∈ σ,
            from env.contains_apply_equiv.right.mp (exists.intro (value.func g gx R₂ S₂ e₁ σ₂) f_is_func),
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
            have h3: σ ⊨ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).to_vc,
            from consequent_of_pre_P_call σ_verified R_closed R_valid env_has_x this func_vc,
            have (prop.and (prop.term (term.unop unop.isFunc f)) (prop.pre f x)).to_vc
              = ((prop.term (term.unop unop.isFunc f)).to_vc ⋀ (prop.pre f x).to_vc), by unfold prop.to_vc,
            have σ ⊨ ((prop.term (term.unop unop.isFunc f)).to_vc ⋀ (prop.pre f x).to_vc), from this ▸ h3,
            have h4: σ ⊨ (prop.pre f x).to_vc, from (valid_env.and.elim this).right,
            have (prop.pre f x).to_vc = vc.pre f x, by unfold prop.to_vc,
            have h5: σ ⊨ vc.pre f x, from this ▸ h4,
            have vc.subst_env σ (vc.pre f x) = vc.pre (term.subst_env σ f) (term.subst_env σ x),
            from vc.subst_env.pre,
            have h6: ⊨ vc.pre (term.subst_env σ f) (term.subst_env σ x), from this ▸ h5,
            have term.subst_env σ f = value.func g gx R₂ S₂ e₁ σ₂,
            from (term.subst_env.var.right (value.func g gx R₂ S₂ e₁ σ₂)).mp f_is_func,
            have h7: ⊨ vc.pre (value.func g gx R₂ S₂ e₁ σ₂) (term.subst_env σ x), from this ▸ h6,
            have term.subst_env σ x = vₓ, from (term.subst_env.var.right vₓ).mp x_is_vₓ,
            have ⊨ vc.pre (value.func g gx R₂ S₂ e₁ σ₂) vₓ, from this ▸ h7,
            show (σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂][gx↦vₓ] ⊨ R₂.to_prop.to_vc),
            from valid.pre.mpr this
          ),

          have ∀σ, σ ⊨ vc.implies (R₂.to_prop ⋀ P₃).to_vc (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂).to_vc, from (
            assume σ: env,

            have hb1: σ ⊨ vc.implies (R₂.to_prop ⋀ P₃).to_vc (P₃ ⋀ R₂).to_vc,
            from vc.implies.and_symm,

            have hb4: σ ⊨ vc.implies (P₃ ⋀ ↑R₂).to_vc (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂).to_vc, from (

              have (∃Q, (⊩ (σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂]) : Q) ∧ ∀σ', σ' ⊨ vc.implies P₃.to_vc Q.to_vc),
              from env_implies_rest ha5,
              let ⟨Q₂'', ⟨hb1, hb2⟩⟩ := this in
              have Q₂' = Q₂'', from env.dvcgen.inj ha3 Q₂'' hb1,
              have hb3: σ ⊨ vc.implies P₃.to_vc Q₂'.to_vc, from this.symm ▸ hb2 σ,

              have σ ⊨ vc.implies Q₂'.to_vc (Q₂ ⋀ spec.func g gx R₂ S₂).to_vc, from (
                vc.implies.same_left (
                  assume Q₂_valid: σ ⊨ Q₂.to_vc,
                  vc.implies.left_elim (
                    assume : σ ⊨ (prop.term (g ≡ value.func g gx R₂ S₂ e₁ σ₂)).to_vc,
                    have (σ g = value.func g gx R₂ S₂ e₁ σ₂), from valid_env.subst_of_eq this,
                    inlined_dominates_spec ha2.right.right.right.right.right.left
                    ha2.right.left ha2.right.right.left ha2.right.right.right.left.symm Q₂_valid this ha3
                  )
                )
              ),
              have σ ⊨ vc.implies P₃.to_vc (Q₂ ⋀ spec.func g gx R₂ S₂).to_vc,
              from vc.implies.trans hb3 this,

              have hb8: σ ⊨ vc.implies (P₃ ⋀ ↑R₂).to_vc ((Q₂ ⋀ spec.func g gx R₂ S₂) ⋀ R₂).to_vc,
              from vc.implies.same_right (λ_, this),

              have hb9: σ ⊨ vc.implies ((Q₂ ⋀ spec.func g gx R₂ S₂) ⋀ R₂).to_vc (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂).to_vc,
              from vc.implies.and_assoc.symm,

              show σ ⊨ vc.implies (P₃ ⋀ ↑R₂).to_vc (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂).to_vc,
              from vc.implies.trans hb8 hb9
            ),

            show σ ⊨ vc.implies (↑R₂ ⋀ P₃).to_vc (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂).to_vc,
            from vc.implies.trans hb1 hb4
          ),
          have ↑R₂ ⋀ P₃ ⊩ e₁ : Q₃,
          from strengthen_exp ha6 (↑R₂ ⋀ P₃) ha8 this,

          have h5: ⊩ₛ (R₂, σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂][gx↦vₓ], e₁) : P₃ ⋀ Q₃,
          from stack.dvcgen.top ha5 ha7 ha9 this,

          have h6: y ∉ σ, from (
            have y ∉ FV P, from (
              assume : y ∈ FV P,
              have y ∈ FV (R.to_prop ⋀ P), from free_in_prop.and₂ this,
              show «false», from y_not_free this
            ),
            show y ∉ σ, from mt (free_of_contains σ_verified) this
          ),

          have h7: (↑R ⋀ P ⋀ prop.call x ⋀ prop.post f x ⋀ y ≡ term.app f x ⊩ e₂ : Q), from (
            have ha1: FV (↑R ⋀ P ⋀ prop.call x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                   =  FV ((↑R ⋀ P) ⋀ prop.call x ⋀ prop.post f x ⋀ y ≡ term.app f x),
            from free_in_prop.and_assoc,

            have ∀σ, σ ⊨ vc.implies (↑R ⋀ P ⋀ prop.call x ⋀ prop.post f x ⋀ y ≡ term.app f x).to_vc
                                     ((↑R ⋀ P) ⋀ prop.call x ⋀ prop.post f x ⋀ y ≡ term.app f x).to_vc,
            from λσ, vc.implies.and_assoc,

            show (↑R ⋀ P ⋀ prop.call x ⋀ prop.post f x ⋀ y ≡ term.app f x ⊩ e₂ : Q),
            from strengthen_exp e₂_verified (↑R ⋀ P ⋀ prop.call x ⋀ prop.post f x ⋀ y ≡ term.app f x) ha1 this
          ),

          have h8: ⦃ prop.implies (↑R ⋀ P ⋀ prop.call x) (↑(term.unop unop.isFunc f) ⋀ prop.pre f x) ⦄, from (
            assume σ: env,
            have ha1: σ ⊨ vc.implies (↑R ⋀ P ⋀ prop.call x).to_vc ((↑R ⋀ P) ⋀ prop.call x).to_vc,
            from vc.implies.and_assoc,

            have FV (↑R ⋀ P ⋀ prop.call x) = FV ((↑R ⋀ P) ⋀ prop.call x),
            from free_in_prop.and_assoc,
            have ha2: FV ((↑R ⋀ P) ⋀ prop.call x) ⊆ FV (↑R ⋀ P ⋀ prop.call x),
            from set.subset_of_eq this.symm,
            strengthen_vc ha1 ha2 (func_vc σ)
          ),

          have h9: (R₂, σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂][gx↦vₓ], e₁)
              ⟹* (R₂, σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂][gx↦vₓ], e₁),
          from trans_dstep.rfl,

          have h10: ∀σ' t, (σ' ⊨ ((↑P₃ ⋀ Q₃) t).to_vc) → σ' ⊨ ((Q₂' ⋀ P₃') ⋀ Q₃ t).to_vc, from (
            assume σ': env,
            assume t: term,
            assume h10a: σ' ⊨ ((↑(Q₂' ⋀ P₃') ⋀ Q₃) t).to_vc,
            have h11: (↑(Q₂' ⋀ P₃') ⋀ Q₃) t = ((Q₂' ⋀ P₃') ⋀ Q₃ t), from propctx_apply_pq,
            show σ' ⊨ ((Q₂'⋀ P₃') ⋀ Q₃ t).to_vc,
            from @eq.subst prop (λa, σ' ⊨ a.to_vc) ((↑(Q₂' ⋀ P₃') ⋀ Q₃) t) ((Q₂' ⋀ P₃') ⋀ Q₃ t) h11 h10a
          ),

          have h11: ∀v: value, FV ((Q₂' ⋀ P₃') ⋀ Q₃ v) ⊆ FV ((↑P₃ ⋀ Q₃) v), from (
            assume v: value,
            have h11: (↑P₃ ⋀ Q₃) v = (P₃ ⋀ Q₃ v), from propctx_apply_pq,

            have FV ((Q₂'⋀ P₃') ⋀ Q₃ v) ⊆ FV (P₃ ⋀ Q₃ v),
            from set.subset.refl (FV (P₃ ⋀ Q₃ v)),
            show FV ((Q₂'⋀ P₃') ⋀ Q₃ v) ⊆ FV ((↑P₃ ⋀ Q₃) v), from h11.symm ▸ this
          ),

          have h12: ⊩ₛ dstack.cons (R₂, σ₂[g↦value.func g gx R₂ S₂ e₁ σ₂][gx↦vₓ], e₁) R σ y f x e₂
                    :  P ⋀ propctx.exis y (prop.call x ⋀ prop.post f x ⋀ y ≡ term.app f x ⋀ Q),
          from stack.dvcgen.cons h5 h6 σ_verified ha2.right.right.right.right.right.left ha5 fv_R R_valid
                                f_is_func x_is_vₓ h7 
                                ha2.right.right.right.right.right.right.right.right.right.left
                                h10 h11 h8 h9,

          have h13: ∀σ' t, σ' ⊨ vc.implies
            ((↑P ⋀ propctx.exis y (↑(prop.call x) ⋀ ↑(prop.post f x) ⋀ ↑(y ≡ term.app f x) ⋀ Q)) t).to_vc
            ((↑P ⋀ propctx.exis y (↑(prop.call x) ⋀ ↑(prop.post f x) ⋀ ↑(y ≡ term.app f x) ⋀ Q)) t).to_vc,
          from λσ' t, vc.implies.self,

          have h14: ∀v: value,
             (FV ((↑P ⋀ propctx.exis y (↑(prop.call x) ⋀ ↑(prop.post f x) ⋀ ↑(y ≡ term.app f x) ⋀ Q)) v)
           ⊆ FV ((↑P ⋀ propctx.exis y (↑(prop.call x) ⋀ ↑(prop.post f x) ⋀ ↑(y ≡ term.app f x) ⋀ Q)) v)),
          from λv, set.subset.refl
            (FV ((↑P ⋀ propctx.exis y (↑(prop.call x) ⋀ ↑(prop.post f x) ⋀ ↑(y ≡ term.app f x) ⋀ Q)) v)),
          exists.intro ( P ⋀ propctx.exis y (prop.call x ⋀ prop.post f x ⋀ y ≡ term.app f x ⋀ Q)) ⟨h12, ⟨h13, h14⟩⟩
        }
      },
      case dstep.ite_true x e₁ e₂ {
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      },
      case dstep.ite_false x e₁ e₂ {
        from exp.preservation σ_verified fv_R R_valid e_verified s_steps
      }
    },
    case stack.dvcgen.cons P P' P'' s' σ σ' f g x y fx R' R S e e' vₓ Q₂ Q₃ Q₂' s'_verified y_not_in_σ σ_verified
                          σ'_verified σ''_verified fv_R' R'_valid g_is_func x_is_v cont e'_verified Q₂'_dom Q₂'_fv
                          pre_vc steps ih {
      assume s''',
      assume s_steps: (dstack.cons s' R' σ y g x e ⟹ s'''),
      cases s_steps,
      case dstep.ctx s'' s'_steps { from
        have (∃ (Q' : propctx), (⊩ₛ s'' : Q') ∧ (∀σ' t, σ' ⊨ vc.implies (Q' t).to_vc (Q₂' t).to_vc) ∧
                                                (∀v: value, FV (Q₂' v) ⊆ FV (Q' v))),
        from ih s'' s'_steps,
        let ⟨Q', ⟨h1, ⟨h2, h3⟩⟩⟩ := this in
        have new_steps: ((R, σ'[f↦value.func f fx R S e' σ'][fx↦vₓ], e') ⟹* s''),
        from trans_dstep.trans steps s'_steps,

        have h4: ∀ (σ' : env) (t : term), (σ' ⊨ (Q' t).to_vc) → σ' ⊨ (P'' ⋀ Q₂ t).to_vc, from (
          assume σ'': env,
          assume t: term,
          have h4: σ'' ⊨ vc.implies (Q' t).to_vc (Q₂' t).to_vc, from h2 σ'' t,
          have h5: σ'' ⊨ vc.implies (Q₂' t).to_vc (P'' ⋀ Q₂ t).to_vc, from valid_env.mpr (Q₂'_dom σ'' t),
          have h6: σ'' ⊨ vc.implies (Q' t).to_vc (P'' ⋀ Q₂ t).to_vc, from vc.implies.trans h4 h5,
          valid_env.mp h6
        ),
        have h5: ∀v: value, (FV (P'' ⋀ Q₂ v) ⊆ FV (Q' v)), from (
          assume v: value,
          have h7: FV (Q₂' v) ⊆ FV (Q' v), from h3 v,
          have h8: FV (P'' ⋀ Q₂ v) ⊆ FV (Q₂' v), from Q₂'_fv v,
          show FV (P'' ⋀ Q₂ v) ⊆ FV (Q' v), from set.subset.trans h8 h7
        ),
        have h6: ⊩ₛ dstack.cons s'' R' σ y g x e
                 :  P ⋀ propctx.exis y (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃),
        from stack.dvcgen.cons h1 y_not_in_σ σ_verified σ'_verified σ''_verified fv_R' R'_valid
                              g_is_func x_is_v cont e'_verified h4 h5 pre_vc new_steps,

        have h7: ∀σ'' t, σ'' ⊨ vc.implies
          ((↑P ⋀ propctx.exis y (↑(prop.call x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) t).to_vc
          ((↑P ⋀ propctx.exis y (↑(prop.call x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) t).to_vc,
        from λσ'' t, vc.implies.self,
        have h8: ∀v: value,
           FV ((↑P ⋀ propctx.exis y (↑(prop.call x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) v)
         ⊆ FV ((↑P ⋀ propctx.exis y (↑(prop.call x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) v),
        from λv, set.subset.refl
          (FV ((↑P ⋀ propctx.exis y (↑(prop.call x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) v)),
        exists.intro ( P ⋀ propctx.exis y (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃)) ⟨h6, ⟨h7, h8⟩⟩
      },
      case dstep.return σ₁ σ₂ f₁ x₁ y₁ R'₁ R₁ S₁ e₁ vy₁ vx₁ y_is_vy₁ g_is_func₁ x_is_vx₁ { from
        have ∃P₁ Q₁, (⊩ σ₁: P₁) ∧ (FV R'₁.to_prop ⊆ FV P₁) ∧ (σ₁ ⊨ R'₁.to_prop.to_vc) ∧
                                                               (R'₁ ⋀ P₁ ⊩ exp.return y₁ : Q₁),
        from stack.dvcgen.top.inv s'_verified,
        let ⟨P₁, Q₁, ⟨σ₁_verified, ⟨h1, ⟨h2, h3⟩⟩⟩⟩ := this in
        have ∃σ' Q', ⊩ (σ'[y₁↦vy₁]) : Q', from env.dvcgen.inv σ₁_verified y_is_vy₁,
        let ⟨σ₁', Q₁', h4⟩ := this in
        have ∃P₃, (⊩ (σ[y↦vy₁]) : P ⋀ P₃), from env.dvcgen.copy σ_verified y_not_in_σ h4,
        let ⟨P₃, h5⟩ := this in

        have h6: FV R'.to_prop ⊆ FV (P ⋀ P₃), from (
          assume z: var,
          assume : z ∈ FV R'.to_prop,
          have z ∈ FV P, from set.mem_of_subset_of_mem fv_R' this,
          show z ∈ FV (P ⋀ P₃), from free_in_prop.and₁ this
        ),

        have h7: y ∉ FV R'.to_prop.to_vc, from (
          assume : y ∈ FV R'.to_prop.to_vc,
          have y ∈ FV R'.to_prop, from free_in_prop_of_free_in_to_vc this,
          have h10: y ∈ FV P, from set.mem_of_subset_of_mem fv_R' this,
          have σ.dom = FV P, from free_iff_contains σ_verified,
          have y ∈ σ.dom, from this.symm ▸ h10,
          have y ∈ σ, from this,
          show «false», from y_not_in_σ this
        ),
        have h8: (σ[y↦vy₁] ⊨ R'.to_prop.to_vc),
        from valid_with_additional_var R'_valid,

        have g_in_σ: g ∈ σ,
        from env.contains_apply_equiv.right.mp (exists.intro (value.func f fx R S e' σ') g_is_func),

        have x_in_σ: x ∈ σ,
        from env.contains_apply_equiv.right.mp (exists.intro vₓ x_is_v),

        have h9: (FV (↑R' ⋀ P ⋀ P₃)
             = FV (↑R' ⋀ P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x)), from (
          let sy: set var := set.insert y ∅ in

          have h12: (σ[y↦vy₁]).dom = FV (P ⋀ P₃), from free_iff_contains h5,
          have h13: (σ[y↦vy₁]).dom = (σ.dom ∪ sy), from env.dom.inv,
          have h14: FV (P ⋀ P₃) = (σ.dom ∪ sy), from eq.trans h12.symm h13,

          have h15: FV (↑R' ⋀ P ⋀ P₃) = (σ.dom ∪ sy),
          from set.eq_of_subset_of_subset (
            assume z: var,
            assume : z ∈ FV (↑R' ⋀ P ⋀ P₃),
            or.elim (free_in_prop.and.inv this) (
              assume : free_in_prop z R',
              have h10: z ∈ FV P, from set.mem_of_subset_of_mem fv_R' this,
              have σ.dom = FV P, from free_iff_contains σ_verified,
              have z ∈ σ.dom, from this.symm ▸ h10,
              show z ∈ σ.dom ∪ sy, from set.mem_union_left sy this
            ) (
              assume : z ∈ FV (P ⋀ P₃),
              show z ∈ (σ.dom ∪ sy), from h14 ▸ this
            )
          ) (
            assume z: var,
            assume : z ∈ σ.dom ∪ sy,
            have z ∈ FV (P ⋀ P₃), from h14.symm ▸ this,
            show z ∈ FV (↑R' ⋀ P ⋀ P₃), from free_in_prop.and₂ this
          ),

          have h18: FV (↑R' ⋀ P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x) = σ.dom ∪ sy,
          from set.eq_of_subset_of_subset (
            assume z: var,
            assume : z ∈ FV (↑R' ⋀ P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x),
            or.elim (free_in_prop.and.inv this) (
              assume : free_in_prop z R',
              have h10: z ∈ FV P, from set.mem_of_subset_of_mem fv_R' this,
              have σ.dom = FV P, from free_iff_contains σ_verified,
              have z ∈ σ.dom, from this.symm ▸ h10,
              show z ∈ σ.dom ∪ sy, from set.mem_union_left sy this
            ) (
              assume : z ∈ FV (P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x),
              or.elim (free_in_prop.and.inv this) (
                assume h10: z ∈ FV P,
                have σ.dom = FV P, from free_iff_contains σ_verified,
                have z ∈ σ.dom, from this.symm ▸ h10,
                show z ∈ σ.dom ∪ sy, from set.mem_union_left sy this
              ) (
                assume : z ∈ FV (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x),
                or.elim (free_in_prop.and.inv this) (
                  assume : z ∈ FV (prop.call x),
                  have free_in_term z x, from free_in_prop.call.inv this,
                  have z = x, from free_in_term.var.inv this,
                  have z ∈ σ, from this.symm ▸ x_in_σ,
                  show z ∈ σ.dom ∪ sy, from set.mem_union_left sy this
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
          ) (
            assume z: var,
            assume : z ∈ σ.dom ∪ sy,
            or.elim (set.mem_or_mem_of_mem_union this) (
              assume h10: z ∈ σ.dom,
              have σ.dom = FV P, from free_iff_contains σ_verified,
              have z ∈ FV P, from this ▸ h10,
              have z ∈ FV (P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x), from free_in_prop.and₁ this,
              show z ∈ FV (↑R' ⋀ P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x),
              from free_in_prop.and₂ this
            ) (
              assume : z ∈ sy,
              have h: z = y, from (set.mem_singleton_iff z y).mp this,
              have free_in_term y (term.var y), from free_in_term.var y,
              have free_in_term z y, from h.symm ▸ this,
              have free_in_term z (y ≡ term.app g x), from free_in_term.binop₁ this,
              have free_in_prop z (y ≡ term.app g x), from free_in_prop.term this,
              have z ∈ FV (prop.post g x ⋀ y ≡ term.app g x), from free_in_prop.and₂ this,
              have z ∈ FV (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x), from free_in_prop.and₂ this,
              have z ∈ FV (P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x), from free_in_prop.and₂ this,
              show z ∈ FV (↑R' ⋀ P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x),
              from free_in_prop.and₂ this
            )
          ),

          eq.trans h15 h18.symm
        ),

        have h10: ∀σ₃, (σ₃ ⊨ (P ⋀ P₃).to_vc) → (σ₃ ⊨ vc.post g x ⋀ y ≡ term.app g x), from (
          assume σ₃: env,
          assume P_P₃_valid: σ₃ ⊨ (P ⋀ P₃).to_vc,
          have P_valid: σ₃ ⊨ P.to_vc,
          from (valid_env.to_vc_and.elim P_P₃_valid).left,

          have env_equiv: (∀z, z ∈ σ → (σ z = σ₃ z)),
          from env_equiv_of_translation_valid σ_verified σ₃ P_valid,

          have env_equiv2: (∀z, z ∈ (σ[y↦vy₁]) → ((σ[y↦vy₁]) z = σ₃ z)),
          from env_equiv_of_translation_valid h5 σ₃ P_P₃_valid,

          have h21: σ₃ ⊨ P₃.to_vc,
          from (valid_env.to_vc_and.elim P_P₃_valid).right,

          have σ₃ g = (value.func f₁ x₁ R₁ S₁ e₁ σ₂),
          from eq.trans (env_equiv g g_in_σ).symm g_is_func₁,
          have h23: term.subst_env σ₃ g = value.func f₁ x₁ R₁ S₁ e₁ σ₂,
          from (term.subst_env.var.right (value.func f₁ x₁ R₁ S₁ e₁ σ₂)).mp this,

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

          have some (value.func f₁ x₁ R₁ S₁ e₁ σ₂) = some (value.func f fx R S e' σ'),
          from eq.trans g_is_func₁.symm g_is_func,
          have (value.func f₁ x₁ R₁ S₁ e₁ σ₂) = (value.func f fx R S e' σ'),
          from option.some.inj this,
          have h66: f₁ = f, from (value.func.inj this).left,
          have h67: x₁ = fx, from (value.func.inj this).right.left,
          have h68: R₁ = R, from (value.func.inj this).right.right.left,
          have h69: S₁ = S, from (value.func.inj this).right.right.right.left,
          have h70: e₁ = e', from (value.func.inj this).right.right.right.right.left,
          have h71: σ₂ = σ', from (value.func.inj this).right.right.right.right.right,

          have h49: σ₃ ⊨ vc.post g x, from (

            have ∃P₁ Q₁', (⊩ σ₁: P₁) ∧ (FV R'₁.to_prop ⊆ FV P₁) ∧ (σ₁ ⊨ R'₁.to_prop.to_vc) ∧
                          (R'₁ ⋀ P₁ ⊩ exp.return y₁: Q₁'),
            from stack.dvcgen.top.inv s'_verified,

            let ⟨P₁, Q₁', ⟨σ₁_verified, ⟨fv_R'₁, ⟨R'₁_valid, return_verified⟩⟩⟩⟩ := this in

            have h42: σ₁.dom = FV P₁, from free_iff_contains σ₁_verified,
            have y₁_in_σ₁: y₁ ∈ σ₁, from env.contains_apply_equiv.right.mp (exists.intro vy₁ y_is_vy₁),
            have h26: term.subst_env σ₁ y₁ = vy₁,
            from (term.subst_env.var.right vy₁).mp y_is_vy₁,

            have R'₁ ⋀ P₁ ⊩ exp.return y₁ : y₁ ≣ •,
            from exp.dvcgen.return (exp.dvcgen.return.inv return_verified),

            have ⊩ₛ (R'₁, σ₁, exp.return y₁) : P₁ ⋀ y₁ ≣ •,
            from stack.dvcgen.top σ₁_verified fv_R'₁ R'₁_valid this,

            have h44: Q₂' = (P₁ ⋀ y₁ ≣ •),
            from stack.dvcgen.inj s'_verified (P₁ ⋀ y₁ ≣ •) this,

            have h45b: σ₁ ⊨ P₁.to_vc, from env_translation_valid σ₁_verified,

            have h46: σ₁ ⊨ P''.to_vc, from (
              have h47: Q₂' vy₁ = (P₁.to_propctx ⋀ y₁ ≣ •) vy₁,
              from h44 ▸ rfl,

              have h48: (P₁.to_propctx ⋀ y₁ ≣ •) vy₁ = (P₁ ⋀ (y₁ ≣ •) vy₁), from propctx_apply_pq,

              have ((y₁ ≣ •):propctx) vy₁ = (y₁ ≡ vy₁),
              by {
                change (propctx.apply (propctx.term (y₁ ≣ •)) vy₁ = ↑(y₁ ≡ vy₁)),
                unfold propctx.apply,
                change (↑(termctx.apply (termctx.binop binop.eq y₁ •) vy₁) = ↑(y₁ ≡ vy₁)),
                unfold termctx.apply,
                change (↑((term.to_termctx y₁) vy₁ ≡ vy₁) = ↑(↑y₁ ≡ vy₁)),
                rw[@unchanged_of_apply_termctx_without_hole y₁ vy₁]
              },

              have h49: Q₂' vy₁ = (P₁ ⋀ y₁ ≡ vy₁), from eq.trans h47 (this ▸ h48),
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
              have prop.to_vc (prop.term (y₁ ≡ vy₁)) = vc.term (y₁ ≡ vy₁), by unfold prop.to_vc,
              have h53: σ₁ ⊨ prop.to_vc (y₁ ≡ vy₁) , from this.symm ▸ h52,
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
              have closed_subst σ₁ (prop.term (y₁ ≡ vy₁)).to_vc,
              from to_vc_closed_subst_of_closed h53b,
              have σ₁ ⊨ prop.to_vc (y₁ ≡ vy₁), from h53,
              have σ₁ ⊨ (P₁ ⋀ y₁ ≡ vy₁).to_vc,
              from valid_env.to_vc_and h45b this,
              have h54: σ₁ ⊨ (Q₂' vy₁).to_vc, from h49.symm ▸ this,

              have σ₁ ⊨ vc.implies (Q₂' vy₁).to_vc (P'' ⋀ Q₂ vy₁).to_vc, from valid_env.mpr (Q₂'_dom σ₁ vy₁),

              have h55: σ₁ ⊨ (P'' ⋀ Q₂ vy₁).to_vc,
              from valid_env.mp this h54,
              show σ₁ ⊨ P''.to_vc,
              from (valid_env.to_vc_and.elim h55).left
            ),

            have env_equiv3: (∀z, z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]) →
                                       (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ] z = σ₁ z)),
            from env_equiv_of_translation_valid σ''_verified σ₁ h46,

            have fx_is_vₓ: (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]) fx = vₓ,
            from env.apply_of_vcgen σ''_verified,
            have fx_in_σ'': fx ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.same,
            have σ₁ fx = vₓ,
            from eq.trans (env_equiv3 fx fx_in_σ'').symm fx_is_vₓ,
            have h34: term.subst_env σ₁ fx = vₓ,
            from (term.subst_env.var.right vₓ).mp this,
            have fx_in_σ₁: fx ∈ σ₁,
            from env.contains_apply_equiv.right.mp (exists.intro vₓ this),

            have (σ'[f↦value.func f fx R S e' σ']) f = value.func f fx R S e' σ',
            from exists.elim (env.rest_verified σ''_verified) (λ_, env.apply_of_vcgen),
            have f_is_vf: (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]) f = value.func f fx R S e' σ',
            from env.apply_of_rest_apply this,
            have f_in_σ'': f ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]),
            from env.contains.rest env.contains.same,
            have h35a: σ₁ f = (value.func f fx R S e' σ'),
            from eq.trans (env_equiv3 f f_in_σ'').symm f_is_vf,
            have h35: term.subst_env σ₁ f = value.func f fx R S e' σ',
            from (term.subst_env.var.right (value.func f fx R S e' σ')).mp h35a,
            have f_in_σ₁: f ∈ σ₁,
            from env.contains_apply_equiv.right.mp (exists.intro (value.func f fx R S e' σ') h35a),

            have h36: σ₁ ⊨ (P'' ⋀ Q₂ (term.app f fx)).to_vc, from (
              have h37: Q₂' (term.app f fx) = (P₁.to_propctx ⋀ y₁ ≣ •) (term.app f fx),
              from h44 ▸ rfl,

              have h38: (P₁.to_propctx ⋀ y₁ ≣ •) (term.app f fx)
                      = (P₁ ⋀ (y₁ ≣ •) (term.app f fx)), from propctx_apply_pq,

              have ((y₁ ≣ •):propctx) (term.app f fx) = (y₁ ≡ term.app f fx),
              by {
                change (propctx.apply (propctx.term (y₁ ≣ •)) (term.app f fx) = (y₁ ≡ term.app f fx)),
                unfold propctx.apply,
                change (↑(termctx.apply (termctx.binop binop.eq y₁ •) (term.app f fx)) = ↑(y₁ ≡ term.app f fx)),
                unfold termctx.apply,
                change (↑((term.to_termctx y₁) (term.app ↑f ↑fx) ≡ term.app ↑f ↑fx) = ↑(↑y₁ ≡ term.app ↑f ↑fx)),
                rw[@unchanged_of_apply_termctx_without_hole y₁ (term.app f fx)]
              },

              have h39: Q₂' (term.app f fx) = (P₁ ⋀ (y₁ ≡ term.app f fx)),
              from eq.trans h37 (this ▸ h38),

              have h40: σ₁ ⊨ y₁ ≡ term.app f fx, from (
                have (R₁, σ₂[f₁↦value.func f₁ x₁ R₁ S₁ e₁ σ₂][x₁↦vx₁], e₁)
                ⟹* (R'₁, σ₁, exp.return y₁),
                from h65.symm ▸ h66.symm ▸ h67.symm ▸ h68.symm ▸ h69.symm ▸ h70.symm ▸ h71.symm ▸ steps, 

                have h73: (σ₂[f₁↦value.func f₁ x₁ R₁ S₁ e₁ σ₂][x₁↦vx₁], e₁) ⟶* (σ₁, exp.return y₁),
                from step_of_dstep this, 

                have ⊨ vy₁ ≡ term.app (value.func f₁ x₁ R₁ S₁ e₁ σ₂) vx₁,
                from valid.app h73 y_is_vy₁,
                have ⊨ vy₁ ≡ term.app (value.func f fx R S e' σ') vₓ,
                from h65 ▸ h66 ▸ h67 ▸ h68 ▸ h69 ▸ h70 ▸ h71 ▸ this, 
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
              have prop.to_vc (prop.term (y₁ ≡ term.app f fx)) = vc.term (y₁ ≡ term.app f fx),
              by unfold prop.to_vc,
              have h41: σ₁ ⊨ prop.to_vc (y₁ ≡ term.app f fx) , from this.symm ▸ h40,
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
              have closed_subst σ₁ (prop.term (y₁ ≡ term.app f fx)).to_vc,
              from to_vc_closed_subst_of_closed h42b,
              have σ₁ ⊨ prop.to_vc (y₁ ≡ term.app f fx), from h41,
              have σ₁ ⊨ (P₁ ⋀ y₁ ≡ term.app f fx).to_vc,
              from valid_env.to_vc_and h45b this,
              have h43: σ₁ ⊨ (Q₂' (term.app f fx)).to_vc, from h39.symm ▸ this,

              have σ₁ ⊨ vc.implies (Q₂' (term.app f fx)).to_vc (P'' ⋀ Q₂ (term.app f fx)).to_vc,
              from valid_env.mpr (Q₂'_dom σ₁ (term.app f fx)),

              show σ₁ ⊨ (P'' ⋀ Q₂ (term.app f fx)).to_vc,
              from valid_env.mp this h43
            ),

            have ∃Q', (⊩ (σ'[f↦value.func f fx R S e' σ']) : Q') ∧ ∀σ', (σ' ⊨ vc.implies P''.to_vc Q'.to_vc),
            from env_implies_rest σ''_verified,

            let ⟨Q', h90⟩ := this in
            
            have ∃Q₁ Q₂ Q₃,
              f ∉ σ' ∧
              f ∉ σ' ∧
              fx ∉ σ' ∧
              f ≠ fx ∧
              (⊩ σ' : Q₁) ∧
              (⊩ σ' : Q₂) ∧
              fx ∈ FV R.to_prop.to_vc ∧
              FV R.to_prop ⊆ FV Q₂ ∪ { f, fx } ∧
              FV S.to_prop ⊆ FV Q₂ ∪ { f, fx } ∧
              (Q₂ ⋀ spec.func f fx R S ⋀ R ⊩ e' : Q₃) ∧
              ⦃prop.implies (Q₂ ⋀ spec.func f fx R S ⋀ R ⋀ Q₃ (term.app f fx)) S⦄ ∧
              (Q' = (Q₁ ⋀
                  ((f ≡ (value.func f fx R S e' σ')) ⋀
                  prop.subst_env (σ'[f↦value.func f fx R S e' σ'])
                  (prop.func f fx R (Q₃ (term.app f fx) ⋀ S))))),
            from env.dvcgen.func.inv h90.left,
            let ⟨QQ₁, QQ₂, QQ₃, ⟨f_not_in_σ', ⟨_, ⟨fx_not_in_σ', ⟨f_neq_fx, ⟨σ'_veri_QQ₁, ⟨σ'_veri_QQ₂, ⟨fx_in_R,
                                ⟨fv_R, ⟨fv_S, ⟨e'_verified_QQ₃, ⟨func_vc, Q'_is⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ := this in
            
            have h91a: QQ₁ = QQ₂, from env.dvcgen.inj σ'_veri_QQ₁ QQ₂ σ'_veri_QQ₂,
            have h91b: QQ₁ = P', from env.dvcgen.inj σ'_veri_QQ₁ P' σ'_verified,
            have h91c: QQ₂ = P', from eq.trans h91a.symm h91b,

            have P' ⋀ spec.func f fx R S ⋀ R ⊩ e' : QQ₃, from h91c ▸ e'_verified_QQ₃,
            have h91d: QQ₃ = Q₂, from exp.dvcgen.inj this Q₂ e'_verified,

            have h37: closed_subst (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]) (Q₂ (term.app f fx)), from (
              assume z: var,
              assume : z ∈ FV (Q₂ (term.app f fx)),
              have z ∈ FV (term.app f fx) ∨ z ∈ FV (P' ⋀ ↑(spec.func ↑f fx R S) ⋀ ↑R),
              from exp.post_free e'_verified (term.app f fx) this,
              or.elim this (
                assume : z ∈ FV (term.app f fx),
                or.elim (free_in_term.app.inv this) (
                  assume : free_in_term z f,
                  have z = f, from free_in_term.var.inv this,
                  have z ∈ (σ'[f↦value.func f fx R S e' σ']), from this.symm ▸ env.contains.same,
                  show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                ) (
                  assume : free_in_term z fx,
                  have z = fx, from free_in_term.var.inv this,
                  show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from this.symm ▸ env.contains.same
                )
              ) (
                assume : z ∈ FV (P' ⋀ ↑(spec.func ↑f fx R S) ⋀ ↑R),
                or.elim (free_in_prop.and.inv this) (
                  assume : z ∈ FV P',
                  have z ∈ σ'.dom, from (free_iff_contains σ'_verified).symm ▸ this,
                  have z ∈ σ', from this,
                  have z ∈ (σ'[f↦value.func f fx R S e' σ']), from env.contains.rest this,
                  show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                ) (
                  assume : free_in_prop z (↑(spec.func ↑f fx R S) ⋀ ↑R),
                  or.elim (free_in_prop.and.inv this) (
                    assume : free_in_prop z (spec.func ↑f fx R S),
                    have h: free_in_prop z (spec.func ↑f fx R S).to_prop, from this,
                    have spec.to_prop (spec.func f fx R S) = (prop.func f fx R.to_prop S.to_prop),
                    by unfold spec.to_prop,
                    have free_in_prop z (prop.func ↑f fx R S), from this ▸ h,
                    have z ∈ FV (term.var f) ∨ (z ≠ fx ∧ (z ∈ FV R.to_prop ∨ z ∈ FV S.to_prop)),
                    from free_in_prop.func.inv this,
                    or.elim this (
                      assume : free_in_term z f,
                      have z = f, from free_in_term.var.inv this,
                      have z ∈ (σ'[f↦value.func f fx R S e' σ']), from this.symm ▸ env.contains.same,
                      show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                    ) (
                      assume : z ≠ fx ∧ (z ∈ FV R.to_prop ∨ z ∈ FV S.to_prop),
                      have z_neq_fx: z ≠ fx, from this.left,
                      or.elim this.right (
                        assume : z ∈ FV R.to_prop,
                        have z ∈ FV P' ∪ { f, fx }, from h91c ▸ set.mem_of_subset_of_mem fv_R this,
                        or.elim (set.mem_or_mem_of_mem_union this) (
                          assume : z ∈ FV P',
                          have z ∈ σ'.dom, from (free_iff_contains σ'_verified).symm ▸ this,
                          have z ∈ σ', from this,
                          have z ∈ (σ'[f↦value.func f fx R S e' σ']), from env.contains.rest this,
                          show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                        ) (
                          assume : z ∈ { f, fx },
                          or.elim (set.two_elems_mem this) (
                            assume : z = f,
                            have z ∈ (σ'[f↦value.func f fx R S e' σ']), from this.symm ▸ env.contains.same,
                            show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                          ) (
                            assume : z = fx,
                            show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from absurd this z_neq_fx
                          )
                        )
                      ) (
                        assume : z ∈ FV S.to_prop,
                        have z ∈ FV P' ∪ { f, fx }, from h91c ▸ set.mem_of_subset_of_mem fv_S this,
                        or.elim (set.mem_or_mem_of_mem_union this) (
                          assume : z ∈ FV P',
                          have z ∈ σ'.dom, from (free_iff_contains σ'_verified).symm ▸ this,
                          have z ∈ σ', from this,
                          have z ∈ (σ'[f↦value.func f fx R S e' σ']), from env.contains.rest this,
                          show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                        ) (
                          assume : z ∈ { f, fx },
                          or.elim (set.two_elems_mem this) (
                            assume : z = f,
                            have z ∈ (σ'[f↦value.func f fx R S e' σ']), from this.symm ▸ env.contains.same,
                            show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                          ) (
                            assume : z = fx,
                            show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from absurd this z_neq_fx
                          )
                        )
                      )
                    )
                  ) (
                    assume : free_in_prop z R,
                    have z ∈ FV P' ∪ { f, fx }, from h91c ▸ set.mem_of_subset_of_mem fv_R this,
                    or.elim (set.mem_or_mem_of_mem_union this) (
                      assume : z ∈ FV P',
                      have z ∈ σ'.dom, from (free_iff_contains σ'_verified).symm ▸ this,
                      have z ∈ σ', from this,
                      have z ∈ (σ'[f↦value.func f fx R S e' σ']), from env.contains.rest this,
                      show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                    ) (
                      assume : z ∈ { f, fx },
                      or.elim (set.two_elems_mem this) (
                        assume : z = f,
                        have z ∈ (σ'[f↦value.func f fx R S e' σ']), from this.symm ▸ env.contains.same,
                        show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                      ) (
                        assume : z = fx,
                        show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from this.symm ▸ env.contains.same
                      )
                    )
                  )
                )
              )
            ),
            have σ₁ ⊨ (Q₂ (term.app f fx)).to_vc,
            from (valid_env.to_vc_and.elim h36).right,
            have h38: ⊨ vc.subst_env σ₁ (Q₂ (term.app f fx)).to_vc, from this,

            have closed_subst (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]) (Q₂ (term.app f fx)).to_vc,
            from to_vc_closed_subst_of_closed h37,
            have (vc.subst_env (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]) (Q₂ (term.app f fx)).to_vc
                = vc.subst_env σ₁ (Q₂ (term.app f fx)).to_vc),
            from vc.subst_env_equivalent_env env_equiv3 this,
            have h97d: ⊨ vc.subst_env (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]) (Q₂ (term.app f fx)).to_vc,
            from this.symm ▸ h38,

            have R = R'₁, from pre_preserved steps,
            have σ₁ ⊨ R.to_prop.to_vc, from this.symm ▸ R'₁_valid,
            have h98b: σ₁ ⊨ ((P'' ⋀ Q₂ (term.app f fx)) ⋀ ↑R).to_vc,
            from valid_env.to_vc_and h36 this,

            have σ₁ ⊨ vc.implies ((P'' ⋀ Q₂ (term.app f fx)) ⋀ ↑R).to_vc
                                  (P' ⋀ spec.func f fx R S ⋀ ↑R ⋀ Q₂ (term.app f fx)).to_vc, from (
              have hc1: σ₁ ⊨ vc.implies ((P'' ⋀ Q₂ (term.app f fx)) ⋀ ↑R).to_vc
                                        (↑R ⋀ P'' ⋀ Q₂ (term.app f fx)).to_vc,
              from vc.implies.and_symm,

              have hc2: σ₁ ⊨ vc.implies (↑R ⋀ P'' ⋀ Q₂ (term.app f fx)).to_vc
                                        (↑R ⋀ Q₂ (term.app f fx) ⋀ P' ⋀ ↑(spec.func f fx R S)).to_vc,
              from vc.implies.same_left (
                assume _,
                have hc1: σ₁ ⊨ vc.implies (P'' ⋀ Q₂ (term.app f fx)).to_vc
                                          (Q₂ (term.app f fx) ⋀ P'').to_vc,
                from vc.implies.and_symm,

                have hc2: σ₁ ⊨ vc.implies (Q₂ (term.app f fx) ⋀ P'').to_vc
                                          (Q₂ (term.app f fx) ⋀ P' ⋀ spec.func f fx R S).to_vc,
                from vc.implies.same_left (
                  assume _,

                  have hc1: σ₁ ⊨ vc.implies P''.to_vc Q'.to_vc,
                  from h90.right σ₁,

                  have hc2: σ₁ ⊨ vc.implies Q'.to_vc
                                            (P' ⋀ f ≡ (value.func f fx R S e' σ') ⋀
                                            prop.subst_env (σ'[f↦value.func f fx R S e' σ'])
                                                            (prop.func f fx R (Q₂ (term.app f fx) ⋀ S))).to_vc,
                  from h91b ▸ h91d ▸ (@eq.subst prop (λa, σ₁ ⊨ vc.implies Q'.to_vc a.to_vc) Q' 
                      (QQ₁ ⋀ f ≡ (value.func f fx R S e' σ') ⋀
                                                  prop.subst_env (σ'[f↦value.func f fx R S e' σ'])
                                                                (prop.func f fx R (QQ₃ (term.app f fx) ⋀ S)))
                      Q'_is (@vc.implies.self σ₁ Q'.to_vc)),

                  have hc3: σ₁ ⊨ vc.implies (P' ⋀ f ≡ (value.func f fx R S e' σ') ⋀
                                            prop.subst_env (σ'[f↦value.func f fx R S e' σ'])
                                                      (prop.func f fx R (Q₂ (term.app f fx) ⋀ S))).to_vc
                                            (P' ⋀ spec.func f fx R S).to_vc,
                  from vc.implies.same_left (λP_valid, vc.implies.left_elim (
                    assume _,
                    have ⊩ (σ'[f↦value.func f fx R S e' σ']) : (P' ⋀ f ≡ value.func f fx R S e' σ' ⋀
                            prop.subst_env (σ'[f↦value.func f fx R S e' σ'])
                                          (prop.func f fx R (Q₂ (term.app f fx) ⋀ S))),
                    from h91b ▸ h91d ▸ Q'_is ▸ h90.left,

                    show σ₁ ⊨ vc.implies (prop.subst_env (σ'[f↦value.func f fx R S e' σ'])
                                                        (prop.func f fx R (Q₂ (term.app f fx) ⋀ S))).to_vc
                                        (spec.func f fx R S).to_prop.to_vc,
                    from inlined_dominates_spec σ'_verified f_not_in_σ' fx_not_in_σ' f_neq_fx.symm
                          P_valid h35a this
                  )),

                  show σ₁ ⊨ vc.implies P''.to_vc (P' ⋀ spec.func f fx R S).to_vc,
                  from vc.implies.trans hc1 (vc.implies.trans hc2 hc3)
                ),

                show σ₁ ⊨ vc.implies (P'' ⋀ Q₂ (term.app f fx)).to_vc
                                    (Q₂ (term.app f fx) ⋀ P' ⋀ spec.func f fx R S).to_vc,
                from vc.implies.trans hc1 hc2
              ),

              have hc3: σ₁ ⊨ vc.implies (↑R ⋀ Q₂ (term.app f fx) ⋀ P' ⋀ spec.func f fx R S).to_vc
                                        ((↑R ⋀ Q₂ (term.app f fx)) ⋀ P' ⋀ spec.func f fx R S).to_vc,
              from vc.implies.and_assoc,

              have hc4: σ₁ ⊨ vc.implies ((↑R ⋀ Q₂ (term.app f fx)) ⋀ P' ⋀ spec.func f fx R S).to_vc
                                        ((P' ⋀ spec.func f fx R S) ⋀ ↑R ⋀ Q₂ (term.app f fx)).to_vc,
              from vc.implies.and_symm,

              have hc5: σ₁ ⊨ vc.implies ((P' ⋀ spec.func f fx R S) ⋀ ↑R ⋀ Q₂ (term.app f fx)).to_vc
                                        (P' ⋀ spec.func f fx R S ⋀ ↑R ⋀ Q₂ (term.app f fx)).to_vc,
              from vc.implies.and_assoc.symm,

              show σ₁ ⊨ vc.implies ((P'' ⋀ Q₂ (term.app f fx)) ⋀ ↑R).to_vc
                                  (P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)).to_vc,
              from vc.implies.trans hc1 (vc.implies.trans hc2 (vc.implies.trans hc3 (vc.implies.trans hc4 hc5)))
            ),
            have h98b: σ₁ ⊨ (P' ⋀ spec.func f fx R S ⋀ ↑R ⋀ Q₂ (term.app f fx)).to_vc,
            from valid_env.mp this h98b,

            have h98c: closed_subst (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ])
                              (prop.implies (P' ⋀ spec.func f fx R S ⋀ ↑R ⋀ Q₂ (term.app f fx)) S),
            from (
              assume z: var,
              assume : z ∈ FV (prop.implies (P' ⋀ spec.func f fx R S ⋀ ↑R ⋀ Q₂ (term.app f fx)) S),
              or.elim (free_in_prop.implies.inv this) (
                assume : z ∈ FV (P' ⋀ ↑(spec.func ↑f fx R S) ⋀ ↑R ⋀ Q₂ (term.app f fx)),
                or.elim (free_in_prop.and.inv this) (
                  assume : z ∈ FV P',
                  have z ∈ σ'.dom, from (free_iff_contains σ'_verified).symm ▸ this,
                  have z ∈ σ', from this,
                  have z ∈ (σ'[f↦value.func f fx R S e' σ']), from env.contains.rest this,
                  show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                ) (
                  assume : free_in_prop z (↑(spec.func ↑f fx R S) ⋀ ↑R ⋀ Q₂ (term.app f fx)),
                  or.elim (free_in_prop.and.inv this) (
                    assume : free_in_prop z (spec.func ↑f fx R S),
                    have h: free_in_prop z (spec.func ↑f fx R S).to_prop, from this,
                    have spec.to_prop (spec.func f fx R S) = (prop.func f fx R.to_prop S.to_prop),
                    by unfold spec.to_prop,
                    have free_in_prop z (prop.func ↑f fx R S), from this ▸ h,
                    have z ∈ FV (term.var f) ∨ (z ≠ fx ∧ (z ∈ FV R.to_prop ∨ z ∈ FV S.to_prop)),
                    from free_in_prop.func.inv this,
                    or.elim this (
                      assume : free_in_term z f,
                      have z = f, from free_in_term.var.inv this,
                      have z ∈ (σ'[f↦value.func f fx R S e' σ']), from this.symm ▸ env.contains.same,
                      show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                    ) (
                      assume : z ≠ fx ∧ (z ∈ FV R.to_prop ∨ z ∈ FV S.to_prop),
                      have z_neq_fx: z ≠ fx, from this.left,
                      or.elim this.right (
                        assume : z ∈ FV R.to_prop,
                        have z ∈ FV P' ∪ { f, fx }, from h91c ▸ set.mem_of_subset_of_mem fv_R this,
                        or.elim (set.mem_or_mem_of_mem_union this) (
                          assume : z ∈ FV P',
                          have z ∈ σ'.dom, from (free_iff_contains σ'_verified).symm ▸ this,
                          have z ∈ σ', from this,
                          have z ∈ (σ'[f↦value.func f fx R S e' σ']), from env.contains.rest this,
                          show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                        ) (
                          assume : z ∈ { f, fx },
                          or.elim (set.two_elems_mem this) (
                            assume : z = f,
                            have z ∈ (σ'[f↦value.func f fx R S e' σ']), from this.symm ▸ env.contains.same,
                            show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                          ) (
                            assume : z = fx,
                            show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from absurd this z_neq_fx
                          )
                        )
                      ) (
                        assume : z ∈ FV S.to_prop,
                        have z ∈ FV P' ∪ { f, fx }, from h91c ▸ set.mem_of_subset_of_mem fv_S this,
                        or.elim (set.mem_or_mem_of_mem_union this) (
                          assume : z ∈ FV P',
                          have z ∈ σ'.dom, from (free_iff_contains σ'_verified).symm ▸ this,
                          have z ∈ σ', from this,
                          have z ∈ (σ'[f↦value.func f fx R S e' σ']), from env.contains.rest this,
                          show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                        ) (
                          assume : z ∈ { f, fx },
                          or.elim (set.two_elems_mem this) (
                            assume : z = f,
                            have z ∈ (σ'[f↦value.func f fx R S e' σ']), from this.symm ▸ env.contains.same,
                            show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                          ) (
                            assume : z = fx,
                            show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from absurd this z_neq_fx
                          )
                        )
                      )
                    )
                  ) (
                    assume : z ∈ FV (↑R ⋀ Q₂ (term.app f fx)),
                    or.elim (free_in_prop.and.inv this) (
                      assume : free_in_prop z R,
                      have z ∈ FV P' ∪ { f, fx }, from h91c ▸ set.mem_of_subset_of_mem fv_R this,
                      or.elim (set.mem_or_mem_of_mem_union this) (
                        assume : z ∈ FV P',
                        have z ∈ σ'.dom, from (free_iff_contains σ'_verified).symm ▸ this,
                        have z ∈ σ', from this,
                        have z ∈ (σ'[f↦value.func f fx R S e' σ']), from env.contains.rest this,
                        show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                      ) (
                        assume : z ∈ { f, fx },
                        or.elim (set.two_elems_mem this) (
                          assume : z = f,
                          have z ∈ (σ'[f↦value.func f fx R S e' σ']), from this.symm ▸ env.contains.same,
                          show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                        ) (
                          assume : z = fx,
                          show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from this.symm ▸ env.contains.same
                        )
                      )
                    ) (
                      assume : z ∈ FV (Q₂ (term.app f fx)),
                      show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from h37 this
                    )
                  )
                )
              ) (
                assume : free_in_prop z S,
                have z ∈ FV P' ∪ { f, fx }, from h91c ▸ set.mem_of_subset_of_mem fv_S this,
                or.elim (set.mem_or_mem_of_mem_union this) (
                  assume : z ∈ FV P',
                  have z ∈ σ'.dom, from (free_iff_contains σ'_verified).symm ▸ this,
                  have z ∈ σ', from this,
                  have z ∈ (σ'[f↦value.func f fx R S e' σ']), from env.contains.rest this,
                  show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                ) (
                  assume : z ∈ { f, fx },
                  or.elim (set.two_elems_mem this) (
                    assume : z = f,
                    have z ∈ (σ'[f↦value.func f fx R S e' σ']), from this.symm ▸ env.contains.same,
                    show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                  ) (
                    assume : z = fx,
                    show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from this.symm ▸ env.contains.same
                  )
                )
              )
            ),
            have closed_subst σ₁ (prop.implies (P' ⋀ spec.func f fx R S ⋀ ↑R ⋀ Q₂ (term.app f fx)) S),
            from (
              assume z: var,
              assume : z ∈ FV (prop.implies (P' ⋀ spec.func f fx R S ⋀ ↑R ⋀ Q₂ (term.app f fx)) S),
              have z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from h98c this,
              have z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]).dom, from this,
              show z ∈ σ₁.dom, from set.mem_of_subset_of_mem (env.dom_subset_of_equivalent_env env_equiv3) this
            ),
            -- have closed_subst σ₁ (prop.implies (P' ⋀ spec.func f fx R S ⋀ ↑R ⋀ Q₂ (term.app f fx)) S).to_vc,
            -- from to_vc_closed_subst_of_closed this,

            have h98a: σ₁ ⊨ (prop.implies (P' ⋀ ↑(spec.func f fx R S) ⋀ ↑R ⋀ Q₂ (term.app f fx)) S).to_vc,
            from h91c ▸ h91d ▸ func_vc σ₁ (h91c.symm ▸ h91d.symm ▸ this),

            have σ₁ ⊨ (prop.implies (P' ⋀ spec.func f fx R S ⋀ ↑R ⋀ Q₂ (term.app f fx)) S).to_vc,
            from h98a, -- valid_env.to_vc_of_instantiated_n this h98a,
            have σ₁ ⊨ ((P' ⋀ spec.func f fx R S ⋀ ↑R ⋀ Q₂ (term.app f fx)).not ⋁ S.to_prop).to_vc,
            from this,
            have h98d: σ₁ ⊨ ((P' ⋀ spec.func f fx R S ⋀ ↑R ⋀ Q₂ (term.app f fx)).not.to_vc
                      ⋁ S.to_prop.to_vc),
            from valid_env.to_vc_or_elim this,
            have (P' ⋀ spec.func f fx R S ⋀ ↑R ⋀ Q₂ (term.app f fx)).not.to_vc
               = (P' ⋀ spec.func f fx R S ⋀ ↑R ⋀ Q₂ (term.app f fx)).to_vc.not,
            by unfold prop.to_vc,
            have σ₁ ⊨ ((P' ⋀ spec.func f fx R S ⋀ ↑R ⋀ Q₂ (term.app f fx)).to_vc.not ⋁ S.to_prop.to_vc),
            from this ▸ h98d,
            have σ₁ ⊨ vc.implies (P' ⋀ spec.func f fx R S ⋀ ↑R ⋀ Q₂ (term.app f fx)).to_vc S.to_prop.to_vc,
            from this,
            have σ₁ ⊨ S.to_prop.to_vc, from valid_env.mp this h98b,
            have h98z: ⊨ vc.subst_env σ₁ S.to_prop.to_vc,
            from this,

            have closed_subst (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]) S.to_prop, from (
              assume z: var,
              assume : z ∈ FV S.to_prop,
              have z ∈ FV P' ∪ { f, fx }, from h91c ▸ set.mem_of_subset_of_mem fv_S this,
              or.elim (set.mem_or_mem_of_mem_union this) (
                assume : z ∈ FV P',
                have z ∈ σ'.dom, from (free_iff_contains σ'_verified).symm ▸ this,
                have z ∈ σ', from this,
                have z ∈ (σ'[f↦value.func f fx R S e' σ']), from env.contains.rest this,
                show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
              ) (
                assume : z ∈ { f, fx },
                or.elim (set.two_elems_mem this) (
                  assume : z = f,
                  have z ∈ (σ'[f↦value.func f fx R S e' σ']), from this.symm ▸ env.contains.same,
                  show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from env.contains.rest this
                ) (
                  assume : z = fx,
                  show z ∈ (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]), from this.symm ▸ env.contains.same
                )
              )
            ),
            have closed_subst (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]) S.to_prop.to_vc,
            from to_vc_closed_subst_of_closed this,
            have (vc.subst_env (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]) S.to_prop.to_vc
                  = vc.subst_env σ₁ S.to_prop.to_vc),
            from vc.subst_env_equivalent_env env_equiv3 this,
            have h98d: ⊨ vc.subst_env (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ]) S.to_prop.to_vc,
            from this.symm ▸ h98z,
            have ⊨ vc.subst_env (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ])
                                (vc.and (Q₂ (term.app f fx)).to_vc S.to_prop.to_vc),
            from valid_env.and h97d h98d,
            have (σ'[f↦value.func f fx R S e' σ'][fx↦vₓ] ⊨ (Q₂ (term.app f fx)).to_vc ⋀
                                                                S.to_prop.to_vc),
            from this,
            have ⊨ vc.post (value.func f fx R S e' σ') vₓ,
            from valid.post.mp σ'_verified e'_verified this,
            have ⊨ vc.post (value.func f₁ x₁ R₁ S₁ e₁ σ₂) vx₁,
            from h65.symm ▸ h66.symm ▸ h67.symm ▸ h68.symm ▸ h69.symm ▸ h70.symm ▸ h71.symm ▸ this, 
            have h56: ⊨ vc.post (term.subst_env σ₃ g) (term.subst_env σ₃ x),
            from h23.symm ▸ h24.symm ▸ h25.symm ▸ this,
            have vc.subst_env σ₃ (vc.post g x) = vc.post (term.subst_env σ₃ g) (term.subst_env σ₃ x),
            from vc.subst_env.post,
            have ⊨ vc.subst_env σ₃ (vc.post g x), from this.symm ▸ h56,
            show σ₃ ⊨ vc.post g x, from this
          ),

          have h79: σ₃ ⊨ y ≡ term.app g x, from (
            have (R₁, σ₂[f₁↦value.func f₁ x₁ R₁ S₁ e₁ σ₂][x₁↦vx₁], e₁)
            ⟹* (R'₁, σ₁, exp.return y₁),
            from h65.symm ▸ h66.symm ▸ h67.symm ▸ h68.symm ▸ h69.symm ▸ h70.symm ▸ h71.symm ▸ steps, 
            have h73: (σ₂[f₁↦value.func f₁ x₁ R₁ S₁ e₁ σ₂][x₁↦vx₁], e₁) ⟶* (σ₁, exp.return y₁),
            from step_of_dstep this,

            have ⊨ vy₁ ≡ term.app (value.func f₁ x₁ R₁ S₁ e₁ σ₂) vx₁,
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

        have h10p: ∀σ₃, σ₃ ⊨ vc.implies ((P ⋀ P₃) ⋀ prop.call vx₁).to_vc
                                       ((P ⋀ P₃) ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc,
        from λσ₃, vc.implies.same_left (
          assume P_P₃_valid: σ₃ ⊨ (P ⋀ P₃).to_vc,

          have P_valid: σ₃ ⊨ P.to_vc,
          from (valid_env.to_vc_and.elim P_P₃_valid).left,

          have env_equiv: (∀z, z ∈ σ → (σ z = σ₃ z)),
          from env_equiv_of_translation_valid σ_verified σ₃ P_valid,

          have env_equiv2: (∀z, z ∈ (σ[y↦vy₁]) → ((σ[y↦vy₁]) z = σ₃ z)),
          from env_equiv_of_translation_valid h5 σ₃ P_P₃_valid,

          have h_impl: (σ₃ ⊨ (prop.call vx₁).to_vc)
                      → (σ₃ ⊨ (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc), from (
            assume : σ₃ ⊨ (prop.call vx₁).to_vc,

            have h49: σ₃ ⊨ vc.post g x ⋀ y ≡ term.app g x, from h10 σ₃ P_P₃_valid,

            have prop.to_vc (prop.post g x) = vc.post g x,
            by unfold prop.to_vc,

            have h50: σ₃ ⊨ (prop.post g x).to_vc ⋀ y ≡ term.app g x,
            from this.symm ▸ h49,

            have prop.to_vc (prop.term (y ≡ term.app g x)) = vc.term (y ≡ term.app g x),
            by unfold prop.to_vc,

            have h80: σ₃ ⊨ (prop.post g x).to_vc ⋀ prop.to_vc (y ≡ term.app g x),
            from this.symm ▸ h50,

            have prop.to_vc (prop.and (prop.post g x) (y ≡ term.app g x))
               = ((prop.post g x).to_vc ⋀ prop.to_vc (y ≡ term.app g x)),
            by unfold prop.to_vc,

            have h81: σ₃ ⊨ (prop.post g x ⋀ y ≡ term.app g x).to_vc,
            from this.symm ▸ h80,

            have prop.to_vc (prop.call x) = vc.term value.true,
            by unfold prop.to_vc,
            have h82: σ₃ ⊨ prop.to_vc (prop.call x), from this.symm ▸ valid_env.true,

            have h83: σ₃ ⊨ (prop.call x).to_vc ⋀ (prop.post g x ⋀ y ≡ term.app g x).to_vc,
            from valid_env.and h82 h81,

            have prop.to_vc (prop.and (prop.call x) (prop.post g x ⋀ y ≡ term.app g x))
               = ((prop.call x).to_vc ⋀ (prop.post g x ⋀ y ≡ term.app g x).to_vc),
            by unfold prop.to_vc,

            show σ₃ ⊨ (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc, from this.symm ▸ h83
          ),

          show σ₃ ⊨ vc.implies (prop.call vx₁).to_vc
                                (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc,
          from valid_env.mpr h_impl
        ),

        have h10n: ∀σ₃, σ₃ ⊨ vc.implies ((P ⋀ P₃) ⋀ prop.call vx₁).to_vc
                                       ((P ⋀ P₃) ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc,
        from λσ₃, vc.implies.same_left (
          assume P_P₃_valid: σ₃ ⊨ (P ⋀ P₃).to_vc,

          have P_valid: σ₃ ⊨ P.to_vc,
          from (valid_env.to_vc_and.elim P_P₃_valid).left,

          have env_equiv: (∀z, z ∈ σ → (σ z = σ₃ z)),
          from env_equiv_of_translation_valid σ_verified σ₃ P_valid,

          have env_equiv2: (∀z, z ∈ (σ[y↦vy₁]) → ((σ[y↦vy₁]) z = σ₃ z)),
          from env_equiv_of_translation_valid h5 σ₃ P_P₃_valid,

          have h_impl: (σ₃ ⊨ (prop.call vx₁).to_vc)
                      → (σ₃ ⊨ (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc), from (
            assume : σ₃ ⊨ (prop.call vx₁).to_vc,

            have h49: σ₃ ⊨ vc.post g x ⋀ y ≡ term.app g x, from h10 σ₃ P_P₃_valid,

            have prop.to_vc (prop.post g x) = vc.post g x,
            by unfold prop.to_vc,

            have h50: σ₃ ⊨ (prop.post g x).to_vc ⋀ y ≡ term.app g x,
            from this.symm ▸ h49,

            have prop.to_vc (prop.term (y ≡ term.app g x)) = vc.term (y ≡ term.app g x),
            by unfold prop.to_vc,

            have h80: σ₃ ⊨ (prop.post g x).to_vc ⋀ prop.to_vc (y ≡ term.app g x),
            from this.symm ▸ h50,

            have prop.to_vc (prop.and (prop.post g x) (y ≡ term.app g x))
               = ((prop.post g x).to_vc ⋀ prop.to_vc (y ≡ term.app g x)),
            by unfold prop.to_vc,

            have h81: σ₃ ⊨ (prop.post g x ⋀ y ≡ term.app g x).to_vc,
            from this.symm ▸ h80,

            have prop.to_vc (prop.call x) = vc.term value.true,
            by unfold prop.to_vc,
            have h82: σ₃ ⊨ prop.to_vc (prop.call x), from this.symm ▸ valid_env.true,

            have h83: σ₃ ⊨ (prop.call x).to_vc ⋀ (prop.post g x ⋀ y ≡ term.app g x).to_vc,
            from valid_env.and h82 h81,

            have prop.to_vc (prop.and (prop.call x) (prop.post g x ⋀ y ≡ term.app g x))
               = ((prop.call x).to_vc ⋀ (prop.post g x ⋀ y ≡ term.app g x).to_vc),
            by unfold prop.to_vc,

            show σ₃ ⊨ (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc, from this.symm ▸ h83
          ),

          show σ₃ ⊨ vc.implies (prop.call vx₁).to_vc
                              (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc,
          from valid_env.mpr h_impl
        ),

        have h11: ∀σ, σ ⊨ vc.implies (↑R' ⋀ P ⋀ P₃).to_vc
                                      (↑R' ⋀ P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc,
        from (
          assume σ₃: env,
          vc.implies.same_left (
            assume : σ₃ ⊨ R'.to_prop.to_vc,

            have h17: σ₃ ⊨ vc.implies (prop.call vx₁ ⋀ P ⋀ P₃).to_vc
                                      ((P ⋀ P₃) ⋀ prop.call vx₁).to_vc,
            from vc.implies.and_symm,

            have h18: σ₃ ⊨ vc.implies ((P ⋀ P₃) ⋀ prop.call vx₁).to_vc
                                    ((P ⋀ P₃) ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc,
            from h10p σ₃,

            have h19: σ₃ ⊨ vc.implies ((P ⋀ P₃) ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc
                                    ((P₃ ⋀ P) ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc,
            from vc.implies.same_right (λ_, vc.implies.and_symm),

            have h20: σ₃ ⊨ vc.implies ((P₃ ⋀ P) ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc
                                    (P₃ ⋀ P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc,
            from vc.implies.and_assoc.symm,

            have σ₃ ⊨ vc.implies (P₃ ⋀ P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc
                              ((P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x) ⋀ P₃).to_vc,
            from vc.implies.and_symm,

            have h21: σ₃ ⊨ vc.implies (P₃ ⋀ P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc
                                    (P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc,
            from vc.implies.and_elim_left this,

            have h16: σ₃ ⊨ vc.implies (prop.call vx₁ ⋀ P ⋀ P₃).to_vc
                              (P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc,
            from vc.implies.trans h17 (vc.implies.trans h18 (vc.implies.trans h19 (vc.implies.trans h20 h21))),

            have h13: σ₃ ⊨ vc.implies (P ⋀ P₃).to_vc (prop.call vx₁ ⋀ P ⋀ P₃).to_vc, by begin
              apply valid_env.mpr,
              assume h13a,

              apply valid_env.to_vc_and,
              unfold prop.to_vc,
              from valid_env.true,
              from h13a
            end,

            show σ₃ ⊨ vc.implies (P ⋀ P₃).to_vc
                                  (P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc,
            from vc.implies.trans h13 h16
          )
        ),
                       
        have h12: R' ⋀ P ⋀ P₃ ⊩ e : Q₃,
        from strengthen_exp cont (R' ⋀ P ⋀ P₃) h9 h11,

        have h13: ⊩ₛ (R', σ[y↦vy₁], e) : ↑(P ⋀ P₃) ⋀ Q₃,
        from stack.dvcgen.top h5 h6 h8 h12,

        have h14: ∀σ₃ t,
          σ₃ ⊨ vc.implies ((↑(P ⋀ P₃) ⋀ Q₃) t).to_vc
               ((↑P⋀ propctx.exis y (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t).to_vc,
        from (
          assume σ₃: env,
          assume t: term,

          have σ₃ ⊨ vc.implies ((P ⋀ P₃) ⋀ prop.call vx₁).to_vc
                            ((P ⋀ P₃) ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc,
          from h10n σ₃,

          have σ₃ ⊨ vc.implies ((P ⋀ P₃) ⋀ prop.call vx₁).to_vc
                            (((P ⋀ P₃) ⋀ prop.call x) ⋀ prop.post g x ⋀ y ≡ term.app g x).to_vc,
          from vc.implies.trans this vc.implies.and_assoc,

          have σ₃ ⊨ vc.implies ((P ⋀ P₃) ⋀ prop.call vx₁).to_vc
                            ((((P ⋀ P₃) ⋀ prop.call x) ⋀ prop.post g x) ⋀ y ≡ term.app g x).to_vc,
          from vc.implies.trans this vc.implies.and_assoc,

          have σ₃ ⊨ vc.implies (((P ⋀ P₃) ⋀ prop.call vx₁) ⋀ Q₃ t).to_vc
                            (((((P ⋀ P₃) ⋀ prop.call x) ⋀ prop.post g x) ⋀ y ≡ term.app g x) ⋀ Q₃ t).to_vc,
          from vc.implies.same_right (λ_, this),

          have σ₃ ⊨ vc.implies (((P ⋀ P₃) ⋀ prop.call vx₁) ⋀ Q₃ t).to_vc
                            ((((P ⋀ P₃) ⋀ prop.call x) ⋀ prop.post g x) ⋀ y ≡ term.app g x ⋀ Q₃ t).to_vc,

          from vc.implies.trans this vc.implies.and_assoc.symm,

          have σ₃ ⊨ vc.implies (((P ⋀ P₃) ⋀ prop.call vx₁) ⋀ Q₃ t).to_vc
                            (((P ⋀ P₃) ⋀ prop.call x) ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t).to_vc,
          from vc.implies.trans this vc.implies.and_assoc.symm,

          have σ₃ ⊨ vc.implies (((P ⋀ P₃) ⋀ prop.call vx₁) ⋀ Q₃ t).to_vc
                            ((P ⋀ P₃) ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t).to_vc,
          from vc.implies.trans this vc.implies.and_assoc.symm,

          have σ₃ ⊨ vc.implies ((P ⋀ P₃) ⋀ prop.call vx₁ ⋀ Q₃ t).to_vc
                            ((P ⋀ P₃) ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t).to_vc,
          from vc.implies.trans vc.implies.and_assoc this,

          have σ₃ ⊨ vc.implies ((P ⋀ P₃) ⋀ Q₃ t ⋀ prop.call vx₁).to_vc
                            ((P ⋀ P₃) ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t).to_vc,
          from vc.implies.trans (vc.implies.same_left (λ_, vc.implies.and_symm)) this,

          have σ₃ ⊨ vc.implies (((P ⋀ P₃) ⋀ Q₃ t) ⋀ prop.call vx₁).to_vc
                            ((P ⋀ P₃) ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t).to_vc,
          from vc.implies.trans vc.implies.and_assoc.symm this,

          have σ₃ ⊨ vc.implies (prop.call vx₁ ⋀ (P ⋀ P₃) ⋀ Q₃ t).to_vc
                            ((P ⋀ P₃) ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t).to_vc,
          from vc.implies.trans vc.implies.and_symm this,

          have σ₃ ⊨ vc.implies (prop.call vx₁ ⋀ (P ⋀ P₃) ⋀ Q₃ t).to_vc
                            ((P₃ ⋀ P) ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t).to_vc,
          from vc.implies.trans this (vc.implies.same_right (λ_, vc.implies.and_symm)),

          have σ₃ ⊨ vc.implies (prop.call vx₁ ⋀ (P ⋀ P₃) ⋀ Q₃ t).to_vc
                            (P₃ ⋀ P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t).to_vc,
          from vc.implies.trans this vc.implies.and_assoc.symm,

          have h17: σ₃ ⊨ vc.implies (prop.call vx₁ ⋀ (P ⋀ P₃) ⋀ Q₃ t).to_vc
                                 (P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t).to_vc,
          from vc.implies.and_elim_right this,

          have σ₃ ⊨ vc.implies (P ⋀ prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t).to_vc
                            (P ⋀ prop.exis y (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t)).to_vc,
          from vc.implies.same_left (λ_, vc.implies.exis),
          have h20: σ₃ ⊨ vc.implies (prop.call vx₁ ⋀ (P ⋀ P₃) ⋀ Q₃ t).to_vc
                                 (P ⋀ prop.exis y (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t)).to_vc,
          from vc.implies.trans h17 this,

          have h21a: (prop.call x).to_propctx t = prop.call x, from unchanged_of_apply_propctx_without_hole,
          have h21b: (prop.post g x).to_propctx t = prop.post g x, from unchanged_of_apply_propctx_without_hole,
          have h21c: (prop.term (y ≡ term.app g x)).to_propctx t = prop.term (y ≡ term.app g x),
          from unchanged_of_apply_propctx_without_hole,

          have (propctx.exis y (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t
              = prop.exis y (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t),
          by calc
               (propctx.exis y (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t
             = propctx.apply (propctx.exis y (↑(prop.call x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) t : rfl
         ... = prop.exis y (propctx.apply (↑(prop.call x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃) t)
                                   : by unfold propctx.apply
         ... = prop.exis y (propctx.apply (propctx.and ↑(prop.call x)
                                                       (↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) t) : rfl
         ... = prop.exis y (propctx.apply ↑(prop.call x) t ⋀
                            propctx.apply (↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃) t) : by unfold propctx.apply
         ... = prop.exis y ((prop.call x).to_propctx t ⋀
                            propctx.apply (↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃) t) : rfl
         ... = prop.exis y (prop.call x ⋀
                            propctx.apply (↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃) t)
                                  : by rw[h21a]
         ... = prop.exis y (prop.call x ⋀
                            propctx.apply (propctx.and ↑(prop.post g x) (↑(y ≡ term.app g x) ⋀ Q₃)) t) : rfl
         ... = prop.exis y (prop.call x ⋀
                            propctx.apply ↑(prop.post g x) t ⋀ propctx.apply (↑(y ≡ term.app g x) ⋀ Q₃) t)
                                   : by unfold propctx.apply
         ... = prop.exis y (prop.call x ⋀
                            (prop.post g x).to_propctx t ⋀ propctx.apply (↑(y ≡ term.app g x) ⋀ Q₃) t)
                                   : rfl
         ... = prop.exis y (prop.call x ⋀
                            prop.post g x ⋀ propctx.apply (↑(y ≡ term.app g x) ⋀ Q₃) t)
                                   : by rw[h21b]
         ... = prop.exis y (prop.call x ⋀
                            prop.post g x ⋀ propctx.apply (propctx.and ↑(prop.term (y ≡ term.app g x)) Q₃) t)
                                   : rfl
         ... = prop.exis y (prop.call x ⋀
                            prop.post g x ⋀ propctx.apply ↑(prop.term (y ≡ term.app g x)) t ⋀ propctx.apply Q₃ t)
                                   : by unfold propctx.apply
         ... = prop.exis y (prop.call x ⋀
                            prop.post g x ⋀ (prop.term (y ≡ term.app g x)).to_propctx t ⋀ propctx.apply Q₃ t)
                                   : rfl
         ... = prop.exis y (prop.call x ⋀
                            prop.post g x ⋀ prop.term (y ≡ term.app g x) ⋀ propctx.apply Q₃ t)
                                   : by rw[h21c],

          have h21: σ₃ ⊨ vc.implies (((prop.call vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t).to_vc
                    (P⋀ (propctx.exis y
                       (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t).to_vc,
          from this.symm ▸ h20,

          have ((↑P⋀ propctx.exis y
                          (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t)
             = (P⋀ (propctx.exis y
                          (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t),
          from propctx_apply_pq,

          have h22: σ₃ ⊨ vc.implies (((prop.call vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t).to_vc
                            ((↑P⋀ propctx.exis y
                               (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t).to_vc,
          from this.symm ▸ h21,

          have ((↑((prop.call vx₁)) ⋀ ↑(P ⋀ P₃) ⋀ Q₃) t)
             = (((prop.call vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t),
          from propctx_apply_hpq,

          have h23: σ₃ ⊨ vc.implies ((↑((prop.call vx₁)) ⋀ ↑(P ⋀ P₃) ⋀ Q₃) t).to_vc
                                 ((↑P⋀ propctx.exis y
                                   (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t).to_vc,
          from this.symm ▸ h22,


          have h24: σ₃ ⊨ vc.implies ((↑(P ⋀ P₃) ⋀ Q₃) t).to_vc ((↑((prop.call vx₁)) ⋀ ↑(P ⋀ P₃) ⋀ Q₃) t).to_vc, by begin
            apply valid_env.mpr,
            assume h13a,

            apply valid_env.to_vc_and,
            unfold prop.to_vc,
            from valid_env.true,
            from h13a
          end,

          show σ₃ ⊨ vc.implies ((↑(P ⋀ P₃) ⋀ Q₃) t).to_vc
             ((↑P⋀ propctx.exis y (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t).to_vc,
          from vc.implies.trans h24 h23
        ),
        have h15: ∀t,
          FV ((↑P ⋀ propctx.exis y
                       (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t)
        ⊆ FV ((↑(P ⋀ P₃) ⋀ Q₃) t), from (
          assume t: term,

          have h18: FV (P ⋀ prop.exis y (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t))
                  ⊆ σ.dom ∪ FV (Q₃ t),
          from (
            assume z: var,
            assume : z ∈ FV (P ⋀ prop.exis y (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t)),
            or.elim (free_in_prop.and.inv this) (
              assume h10: z ∈ FV P,
              have σ.dom = FV P, from free_iff_contains σ_verified,
              have z ∈ σ.dom, from this.symm ▸ h10,
              show z ∈ σ.dom ∪ FV (Q₃ t), from set.mem_union_left (FV (Q₃ t)) this
            ) (
              assume : z ∈ FV (prop.exis y (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t)),
              have z_neq_y: z ≠ y, from (free_in_prop.exis.inv this).left,
              have z ∈ FV (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t),
              from (free_in_prop.exis.inv this).right,
              or.elim (free_in_prop.and.inv this) (
                assume : z ∈ FV (prop.call x),
                have free_in_term z x, from free_in_prop.call.inv this,
                have z = x, from free_in_term.var.inv this,
                have z ∈ σ, from this.symm ▸ x_in_σ,
                show z ∈ σ.dom ∪ FV (Q₃ t), from set.mem_union_left (FV (Q₃ t)) this
              ) (
                assume : z ∈ FV (prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t),
                or.elim (free_in_prop.and.inv this) (
                  assume : z ∈ FV (prop.post g x),
                  or.elim (free_in_prop.post.inv this) (
                    assume : free_in_term z g,
                    have z = g, from free_in_term.var.inv this,
                    have z ∈ σ, from this.symm ▸ g_in_σ,
                    show z ∈ σ.dom ∪ FV (Q₃ t), from set.mem_union_left (FV (Q₃ t)) this
                  ) (
                    assume : free_in_term z x,
                    have z = x, from free_in_term.var.inv this,
                    have z ∈ σ, from this.symm ▸ x_in_σ,
                    show z ∈ σ.dom ∪ FV (Q₃ t), from set.mem_union_left (FV (Q₃ t)) this
                  )
                ) (
                  assume : free_in_prop z (y ≡ term.app g x ⋀ Q₃ t),
                  or.elim (free_in_prop.and.inv this) (
                    assume : free_in_prop z (y ≡ term.app g x),
                    have free_in_term z (y ≡ term.app g x), from free_in_prop.term.inv this,
                    or.elim (free_in_term.binop.inv this) (
                      assume : free_in_term z y,
                      have z = y, from free_in_term.var.inv this,
                      show z ∈ σ.dom ∪ FV (Q₃ t), from absurd this z_neq_y
                    ) (
                      assume : free_in_term z (term.app g x),
                      or.elim (free_in_term.app.inv this) (
                        assume : free_in_term z g,
                        have z = g, from free_in_term.var.inv this,
                        have z ∈ σ, from this.symm ▸ g_in_σ,
                        show z ∈ σ.dom ∪ FV (Q₃ t), from set.mem_union_left (FV (Q₃ t)) this
                      ) (
                        assume : free_in_term z x,
                        have z = x, from free_in_term.var.inv this,
                        have z ∈ σ, from this.symm ▸ x_in_σ,
                        show z ∈ σ.dom ∪ FV (Q₃ t), from set.mem_union_left (FV (Q₃ t)) this
                      )
                    )
                  ) (
                    assume : z ∈ FV (Q₃ t),
                    show z ∈ σ.dom ∪ FV (Q₃ t), from set.mem_union_right σ.dom this
                  )
                )
              )
            )
          ),

          have h19: σ.dom ∪ FV (Q₃ t) ⊆ FV (((prop.call vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t),
          from (
            assume z: var,
            assume : z ∈ σ.dom ∪ FV (Q₃ t),
            or.elim (set.mem_or_mem_of_mem_union this) (
              assume h10: z ∈ σ.dom,
              have σ.dom = FV P, from free_iff_contains σ_verified,
              have z ∈ FV P, from this ▸ h10,
              have z ∈ FV (P ⋀ P₃), from free_in_prop.and₁ this,
              have z ∈ FV ((P ⋀ P₃) ⋀ Q₃ t), from free_in_prop.and₁ this,
              show z ∈ FV (((prop.call vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t),
              from free_in_prop.and₂ this
            ) (
              assume : z ∈ FV (Q₃ t),
              have z ∈ FV ((P ⋀ P₃) ⋀ Q₃ t), from free_in_prop.and₂ this,
              show z ∈ FV (((prop.call vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t),
              from free_in_prop.and₂ this
            )
          ),

          have h20: FV (P ⋀ prop.exis y (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t))
                  ⊆ FV (((prop.call vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t),
          from set.subset.trans h18 h19,

          have h21a: (prop.call x).to_propctx t = prop.call x, from unchanged_of_apply_propctx_without_hole,
          have h21b: (prop.post g x).to_propctx t = prop.post g x, from unchanged_of_apply_propctx_without_hole,
          have h21c: (prop.term (y ≡ term.app g x)).to_propctx t = prop.term (y ≡ term.app g x),
          from unchanged_of_apply_propctx_without_hole,

          have (propctx.exis y (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t
              = prop.exis y (prop.call x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t),
          by calc
               (propctx.exis y (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t
             = propctx.apply (propctx.exis y (↑(prop.call x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) t : rfl
         ... = prop.exis y (propctx.apply (↑(prop.call x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃) t)
                                   : by unfold propctx.apply
         ... = prop.exis y (propctx.apply (propctx.and ↑(prop.call x)
                                                       (↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) t) : rfl
         ... = prop.exis y (propctx.apply ↑(prop.call x) t ⋀
                            propctx.apply (↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃) t) : by unfold propctx.apply
         ... = prop.exis y ((prop.call x).to_propctx t ⋀
                            propctx.apply (↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃) t) : rfl
         ... = prop.exis y (prop.call x ⋀
                            propctx.apply (↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃) t)
                                  : by rw[h21a]
         ... = prop.exis y (prop.call x ⋀
                            propctx.apply (propctx.and ↑(prop.post g x) (↑(y ≡ term.app g x) ⋀ Q₃)) t) : rfl
         ... = prop.exis y (prop.call x ⋀
                            propctx.apply ↑(prop.post g x) t ⋀ propctx.apply (↑(y ≡ term.app g x) ⋀ Q₃) t)
                                   : by unfold propctx.apply
         ... = prop.exis y (prop.call x ⋀
                            (prop.post g x).to_propctx t ⋀ propctx.apply (↑(y ≡ term.app g x) ⋀ Q₃) t)
                                   : rfl
         ... = prop.exis y (prop.call x ⋀
                            prop.post g x ⋀ propctx.apply (↑(y ≡ term.app g x) ⋀ Q₃) t)
                                   : by rw[h21b]
         ... = prop.exis y (prop.call x ⋀
                            prop.post g x ⋀ propctx.apply (propctx.and ↑(prop.term (y ≡ term.app g x)) Q₃) t)
                                   : rfl
         ... = prop.exis y (prop.call x ⋀
                            prop.post g x ⋀ propctx.apply ↑(prop.term (y ≡ term.app g x)) t ⋀ propctx.apply Q₃ t)
                                   : by unfold propctx.apply
         ... = prop.exis y (prop.call x ⋀
                            prop.post g x ⋀ (prop.term (y ≡ term.app g x)).to_propctx t ⋀ propctx.apply Q₃ t)
                                   : rfl
         ... = prop.exis y (prop.call x ⋀
                            prop.post g x ⋀ prop.term (y ≡ term.app g x) ⋀ propctx.apply Q₃ t)
                                   : by rw[h21c],

          have h21: FV (P⋀ (propctx.exis y
                        (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t)
                  ⊆ FV (((prop.call vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t),
          from this.symm ▸ h20,

          have ((↑P⋀ propctx.exis y
                          (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t)
             = (P⋀ (propctx.exis y
                          (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t),
          from propctx_apply_pq,

          have h22: FV ((↑P⋀ propctx.exis y
                               (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t) 
                  ⊆ FV (((prop.call vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t),
          from this.symm ▸ h21,

          have ((↑((prop.call vx₁)) ⋀ ↑(P ⋀ P₃) ⋀ Q₃) t)
             = (((prop.call vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t),
          from propctx_apply_hpq,

          have h23: FV ((↑P ⋀ propctx.exis y
                             (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t)
                  ⊆ FV ((↑((prop.call vx₁)) ⋀ ↑(P ⋀ P₃) ⋀ Q₃) t),
          from this.symm ▸ h22,

          have h24: FV ((↑((prop.call vx₁)) ⋀ ↑(P ⋀ P₃) ⋀ Q₃) t)
                  ⊆ FV ((↑(P ⋀ P₃) ⋀ Q₃) t), by begin
            assume z,
            assume h25,
            have h26: z ∈ FV (propctx.apply (propctx.and ↑(prop.call ↑vx₁) (↑(P⋀P₃) ⋀ Q₃)) t), from h25,
            unfold propctx.apply at h26,
            cases (free_in_prop.and.inv h26) with h27 h28,
            have h28: free_in_prop z ((prop.call ↑vx₁).to_propctx t), from h27,
            have h29: ((prop.call ↑vx₁).to_propctx t = (prop.call ↑vx₁)), from unchanged_of_apply_propctx_without_hole,
            rw[h29] at h28,
            have h30, from free_in_prop.call.inv h28,
            have h31: ¬ free_in_term z ↑vx₁, from free_in_term.value.inv,
            contradiction,

            from h28
          end,

          show FV ((↑P⋀ propctx.exis y
                       (↑(prop.call ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t) 
             ⊆ FV ((↑(P ⋀ P₃) ⋀ Q₃) t),
          from set.subset.trans h23 h24
        ),

        exists.intro (↑(P ⋀ P₃) ⋀ Q₃) ⟨h13, ⟨h14, λv, h15 v⟩⟩
      }
    }
  end
