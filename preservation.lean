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
      have h2: (σ' y = value.true), from valid_env.subst_of_eq_instantiated_p h1,
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
      have h2: (σ' y = value.false), from valid_env.subst_of_eq_instantiated_p h1,
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
      have h2: (σ' y = value.num n), from valid_env.subst_of_eq_instantiated_p h1,
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
      have h2: (σ' f = value.func g gx R S e H σ₂), from valid_env.subst_of_eq_instantiated_p h1,
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

lemma valid_with_additional_var {P: vc} {x: var} {v: value} {σ: env}:
      (σ ⊨ P) → ((σ[x↦v]) ⊨ P) :=
  assume : σ ⊨ P,
  have h1: ⊨ vc.subst_env σ P, from this,
  have closed_subst σ P, from valid_env.closed h1,
  have h2: closed (vc.subst_env σ P), from vc.closed_of_closed_subst this,
  have vc.subst x v (vc.subst_env σ P) = (vc.subst_env σ P),
  from unchanged_of_subst_nonfree_vc (h2 x),
  have h3: ⊨ vc.subst x v (vc.subst_env σ P), from this.symm ▸ h1,
  have vc.subst x v (vc.subst_env σ P) = vc.subst_env (σ[x↦v]) P,
  by unfold vc.subst_env,
  have  ⊨ vc.subst_env (σ[x↦v]) P, from this ▸ h3,
  show σ[x↦v] ⊨ P, from this

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

lemma dominates_n.apply_propctx_exis {P₁ P₂: prop} {Q: propctx} {x: var} {t: term} {σ: env}:
      dominates_n σ P₁ P₂ → dominates_n σ (P₁ ⋀ Q t) ((propctx.exis x (P₂ ⋀ Q)) t) :=
  
  assume h0: dominates_n σ P₁ P₂,
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

  have h2: dominates_n σ (prop.exis x (P₂ ⋀ propctx.apply Q t)) ((propctx.exis x (P₂ ⋀ Q)) t),
  from this ▸ dominates_n.self,
  have h3: dominates_n σ (P₁ ⋀ Q t) (P₂ ⋀ Q t),
  from dominates_n.same_right (λ_, h0),
  have h4: dominates_n σ (P₂ ⋀ Q t) (prop.exis x (P₂ ⋀ Q t)),
  from dominates_n.exis,
  show dominates_n σ (P₁ ⋀ Q t) ((propctx.exis x (P₂ ⋀ Q)) t),
  from dominates_n.trans (dominates_n.trans h3 h4) h2

lemma free_dominates_helper {H: history} {R: spec} {P P₁ P₂: prop} {Q: propctx} {x: var}:
      (∀σ, (σ ⊨ P.instantiated_p) → dominates_p σ P₁ P₂) →
      (∀σ, (σ ⊨ P.instantiated_p) → dominates_n σ P₁ P₂) →
      (FV P₁ = set.insert x ∅) → 
      (x ∈ FV P₂) → 
      (FV P₂ ⊆ FV P ∪ set.insert x ∅) → 
      (FV (↑R ⋀ ↑H ⋀ P ⋀ P₁) = FV ((↑R ⋀ ↑H ⋀ P) ⋀ P₂)) ∧
      (∀σ, dominates_p σ (↑R ⋀ ↑H ⋀ P ⋀ P₁) ((↑R ⋀ ↑H ⋀ P) ⋀ P₂)) ∧
      (∀σ t, dominates_n σ ((↑H ⋀ ↑(P ⋀ P₁) ⋀ Q) t) ((↑H ⋀ ↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) t)) ∧
      (∀v: value, FV ((↑H ⋀ ↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) v) ⊆ FV ((↑H ⋀ ↑(P ⋀ P₁) ⋀ Q) v)) :=
  assume h1: ∀σ, (σ ⊨ P.instantiated_p) → dominates_p σ P₁ P₂,
  assume h2: ∀σ, (σ ⊨ P.instantiated_p) → dominates_n σ P₁ P₂,
  assume h3a: FV P₁ = set.insert x ∅,
  assume h3b: x ∈ FV P₂,
  assume h3c: FV P₂ ⊆ FV P ∪ set.insert x ∅,

  have h4a: FV (↑R ⋀ ↑H ⋀ P ⋀ P₁) = FV (↑R ⋀ ↑H ⋀ P ⋀ P₂), from set.eq_of_subset_of_subset (
    assume z: var,
    assume : z ∈ FV (↑R ⋀ ↑H ⋀ P ⋀ P₁),
    or.elim (free_in_prop.and.inv this) (
      assume : free_in_prop z R,
      show z ∈ FV (↑R ⋀ ↑H ⋀ P ⋀ P₂), from free_in_prop.and₁ this
    ) (
      assume : z ∈ FV (↑H ⋀ P ⋀ P₁),
      or.elim (free_in_prop.and.inv this) (
        assume : free_in_prop z H,
        have z ∈ FV (↑H ⋀ P ⋀ P₂), from free_in_prop.and₁ this,
        show z ∈ FV (↑R ⋀ ↑H ⋀ P ⋀ P₂), from free_in_prop.and₂ this
      ) (
        assume : z ∈ FV (P ⋀ P₁),
        or.elim (free_in_prop.and.inv this) (
          assume : z ∈ FV P,
          have z ∈ FV (P ⋀ P₂), from free_in_prop.and₁ this,
          have z ∈ FV (↑H ⋀ P ⋀ P₂), from free_in_prop.and₂ this,
          show z ∈ FV (↑R ⋀ ↑H ⋀ P ⋀ P₂), from free_in_prop.and₂ this
        ) (
          assume : z ∈ FV P₁,
          have z ∈ set.insert x ∅, from h3a ▸ this,
          have z = x, from set.eq_of_mem_singleton this,
          have z ∈ FV P₂, from this.symm ▸ h3b,
          have z ∈ FV (P ⋀ P₂), from free_in_prop.and₂ this,
          have z ∈ FV (↑H ⋀ P ⋀ P₂), from free_in_prop.and₂ this,
          show z ∈ FV (↑R ⋀ ↑H ⋀ P ⋀ P₂), from free_in_prop.and₂ this
        )
      )
    )
  ) (
    assume z: var,
    assume : z ∈ FV (↑R ⋀ ↑H ⋀ P ⋀ P₂),
    or.elim (free_in_prop.and.inv this) (
      assume : free_in_prop z R,
      show z ∈ FV (↑R ⋀ ↑H ⋀ P ⋀ P₁), from free_in_prop.and₁ this
    ) (
      assume : z ∈ FV (↑H ⋀ P ⋀ P₂),
      or.elim (free_in_prop.and.inv this) (
        assume : free_in_prop z H,
        have z ∈ FV (↑H ⋀ P ⋀ P₁), from free_in_prop.and₁ this,
        show z ∈ FV (↑R ⋀ ↑H ⋀ P ⋀ P₁), from free_in_prop.and₂ this
      ) (
        assume : z ∈ FV (P ⋀ P₂),
        or.elim (free_in_prop.and.inv this) (
          assume : z ∈ FV P,
          have z ∈ FV (P ⋀ P₁), from free_in_prop.and₁ this,
          have z ∈ FV (↑H ⋀ P ⋀ P₁), from free_in_prop.and₂ this,
          show z ∈ FV (↑R ⋀ ↑H ⋀ P ⋀ P₁), from free_in_prop.and₂ this
        ) (
          assume : z ∈ FV P₂,
          have z ∈ FV P ∪ set.insert x ∅, from set.mem_of_subset_of_mem h3c this,
          or.elim (set.mem_or_mem_of_mem_union this) (
            assume : z ∈ FV P,
            have z ∈ FV (P ⋀ P₁), from free_in_prop.and₁ this,
            have z ∈ FV (↑H ⋀ P ⋀ P₁), from free_in_prop.and₂ this,
            show z ∈ FV (↑R ⋀ ↑H ⋀ P ⋀ P₁), from free_in_prop.and₂ this
          ) (
            assume : z ∈ set.insert x ∅,
            have z ∈ FV P₁, from h3a.symm ▸ this,
            have z ∈ FV (P ⋀ P₁), from free_in_prop.and₂ this,
            have z ∈ FV (↑H ⋀ P ⋀ P₁), from free_in_prop.and₂ this,
            show z ∈ FV (↑R ⋀ ↑H ⋀ P ⋀ P₁), from free_in_prop.and₂ this
          )
        )
      )
    )
  ),
  have h4b: FV (↑R ⋀ ↑H ⋀ P ⋀ P₂) = FV ((↑R ⋀ ↑H ⋀ P) ⋀ P₂),
  from free_in_prop.shuffle,
  have h4: FV (↑R ⋀ ↑H ⋀ P ⋀ P₁ ) = FV ((↑R ⋀ ↑H ⋀ P) ⋀ P₂),
  from eq.trans h4a h4b,

  have h5: ∀σ, dominates_p σ (↑R ⋀ ↑H ⋀ P ⋀ P₁) ((↑R ⋀ ↑H ⋀ P) ⋀ P₂), from (
    assume σ: env,
    have h5a: dominates_p σ (↑R ⋀ ↑H ⋀ P ⋀ P₁) ((↑R ⋀ ↑H ⋀ P) ⋀ P₁),
    from dominates_p.shuffle,
    have h5b: dominates_p σ ((↑R ⋀ ↑H ⋀ P) ⋀ P₁) ((↑R ⋀ ↑H ⋀ P) ⋀ P₂),
    from dominates_p.same_left (
      assume : σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_p,
      have σ ⊨ (↑H ⋀ P).instantiated_p,
      from (valid_env.and.elim (valid_env.instantiated_p_and_elim this)).right,
      have σ ⊨ P.instantiated_p,
      from (valid_env.and.elim (valid_env.instantiated_p_and_elim this)).right,
      h1 σ this
    ),
    show dominates_p σ (↑R ⋀ ↑H ⋀ P ⋀ P₁) ((↑R ⋀ ↑H ⋀ P) ⋀ P₂),
    from dominates_p.trans h5a h5b
  ),

  have h6: (∀σ t,
      dominates_n σ ((↑H ⋀ ↑(P ⋀ P₁) ⋀ Q) t) ((↑H ⋀ ↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) t)), from (
    assume σ: env,
    assume t: term,
    have h6: ((↑H ⋀ ↑(P ⋀ P₁) ⋀ Q) t) = (↑H ⋀ (P ⋀ P₁) ⋀ Q t), from propctx_apply_hpq,
    have h7: ((↑H ⋀ ↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) t)
        = (↑H ⋀ P ⋀ (propctx.exis x (↑P₂ ⋀ Q)) t), from propctx_apply_hpq,
    have dominates_n σ (↑H ⋀ (P ⋀ P₁) ⋀ Q t)
                      (↑H ⋀ P ⋀ (propctx.exis x (↑P₂ ⋀ Q)) t),
    from dominates_n.same_left (
      assume _,
      have h8a: dominates_n σ ((P ⋀ P₁) ⋀ Q t)
                              (P ⋀ P₁ ⋀ Q t),
      from dominates_n.and_assoc.symm,
      have h8b: dominates_n σ (P ⋀ P₁ ⋀ Q t)
                              (P ⋀ (propctx.exis x (↑P₂ ⋀ Q)) t),
      from dominates_n.same_left (
        assume : σ ⊨ P.instantiated_p,
        show dominates_n σ (P₁ ⋀ Q t)
                            ((propctx.exis x (↑P₂ ⋀ Q)) t),
        from dominates_n.apply_propctx_exis (h2 σ this)
      ),
      show dominates_n σ ((P ⋀ P₁) ⋀ Q t)
                          (P ⋀ (propctx.exis x (↑P₂ ⋀ Q)) t),
      from dominates_n.trans h8a h8b
    ),
    show dominates_n σ ((↑H ⋀ ↑(P ⋀ P₁) ⋀ Q) t) ((↑H ⋀ ↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) t),
    from h6.symm ▸ h7.symm ▸ this
  ),
  have h7: (∀v: value,
      FV ((↑H ⋀ ↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) v) ⊆ FV ((↑H ⋀ ↑(P ⋀ P₁) ⋀ Q) v)), from (
    assume v: value,
    have h6: ((↑H ⋀ ↑(P ⋀ P₁) ⋀ Q) v) = (↑H ⋀ (P ⋀ P₁) ⋀ Q v), from propctx_apply_hpq,
    have h7: ((↑H ⋀ ↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) v)
        = (↑H ⋀ P ⋀ (propctx.exis x (↑P₂ ⋀ Q)) v), from propctx_apply_hpq,
    have FV (↑H ⋀ P ⋀ (propctx.exis x (↑P₂ ⋀ Q)) v)
          ⊆ FV (↑H ⋀ (P ⋀ P₁) ⋀ Q v),
    from free_in_prop.sub_same_left (
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
      show FV (P ⋀ (propctx.exis x (↑P₂ ⋀ Q)) v)
          ⊆ FV ((P ⋀ P₁) ⋀ Q v),
      from set.subset.trans h9a h9b
    ),
    show FV ((↑H ⋀ ↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) v) ⊆ FV ((↑H ⋀ ↑(P ⋀ P₁) ⋀ Q) v),
    from h6.symm ▸ h7.symm ▸ this
  ),
  ⟨h4, ⟨h5, ⟨h6, h7⟩⟩⟩

lemma free_dominates_helper_eq_free {H: history} {R: spec} {P P₁ P₂: prop} {Q: propctx} {x: var}:
      (∀σ, (σ ⊨ P.instantiated_p) → dominates_p σ P₁ P₂) →
      (∀σ, (σ ⊨ P.instantiated_p) → dominates_n σ P₁ P₂) →
      (FV P₁ = set.insert x ∅) → 
      (FV P₂ = set.insert x ∅) → 
      (FV (↑R ⋀ ↑H ⋀ P ⋀ P₁) = FV ((↑R ⋀ ↑H ⋀ P) ⋀ P₂)) ∧
      (∀σ, dominates_p σ (↑R ⋀ ↑H ⋀ P ⋀ P₁) ((↑R ⋀ ↑H ⋀ P) ⋀ P₂)) ∧
      (∀σ t, dominates_n σ ((↑H ⋀ ↑(P ⋀ P₁) ⋀ Q) t) ((↑H ⋀ ↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) t)) ∧
      (∀v: value, FV ((↑H ⋀ ↑P ⋀ propctx.exis x (↑P₂ ⋀ Q)) v) ⊆ FV ((↑H ⋀ ↑(P ⋀ P₁) ⋀ Q) v)) :=
  assume h1: ∀σ, (σ ⊨ P.instantiated_p) → dominates_p σ P₁ P₂,
  assume h2: ∀σ, (σ ⊨ P.instantiated_p) → dominates_n σ P₁ P₂,
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

lemma eq_value_of_equiv_subst {σ₁ σ₂: env} {x: var} {v: value}:
      (∀z, z ∈ σ₁ → (σ₁ z = σ₂ z)) → (σ₁ x = v) → (σ₂ x = v) :=
  assume env_equiv: ∀z, z ∈ σ₁ → (σ₁ z = σ₂ z),
  assume x_is_v: σ₁ x = v,
  have x ∈ σ₁, from env.contains_apply_equiv.right.mp (exists.intro v x_is_v),
  have σ₁ x = σ₂ x, from env_equiv x this,
  show σ₂ x = v, from this ▸ x_is_v

lemma exp.preservation {R: spec} {H: history} {σ σ': env} {P: prop} {e e': exp} {Q: propctx}:
      (⊢ σ : P) → FV (spec.to_prop R) ⊆ FV P → (σ ⊨ R.to_prop.instantiated_n) → (R ⋀ H ⋀ P ⊢ e : Q) →
      ((R, H, σ, e) ⟶ (R, H, σ', e')) →
      ∃Q', (⊢ₛ (R, H, σ', e') : Q') ∧ (∀σ' t, dominates_n σ' (Q' t) ((↑H ⋀ ↑P ⋀ Q) t)) ∧
                                      (∀v: value, FV ((↑H ⋀ ↑P ⋀ Q) v) ⊆ FV (Q' v)) :=
  assume σ_verified: ⊢ σ : P,
  assume fv_R: FV (spec.to_prop R) ⊆ FV P,
  assume R_valid: (σ ⊨ R.to_prop.instantiated_n),
  assume e_verified: R ⋀ H ⋀ P ⊢ e : Q,
  assume e_steps: ((R, H, σ, e) ⟶ (R, H, σ', e')),
  begin
    cases e_verified,

    case exp.vcgen.tru x e' Q x_not_free e'_verified {
      cases e_steps,
      
      case step.tru { from
        have x ∉ σ, from (
          assume : x ∈ σ,
          have x ∈ σ.dom, from this,
          have x ∈ FV P, from (free_iff_contains σ_verified) ▸ this,
          have x ∈ FV (↑H ⋀ P), from free_in_prop.and₂ this,
          have x ∈ FV (↑R ⋀ ↑H ⋀ P), from free_in_prop.and₂ this,
          show «false», from x_not_free this
        ),
        have σ'_verified: ⊢ (σ[x↦value.true]) : P ⋀ x ≡ value.true, from env.vcgen.tru this σ_verified,
        have fv_R': FV R.to_prop ⊆ FV (P ⋀ x ≡ value.true), from set.subset.trans fv_R free_in_prop.and_left_subset,
        have R_valid': σ[x↦value.true] ⊨ R.to_prop.instantiated_n, from valid_with_additional_var R_valid,
        have h1: (∀σ, (σ ⊨ P.instantiated_p) → dominates_p σ (x ≡ value.true) (x ≡ value.true)),
        from λ_ _, dominates_p.self,
        have h2: (∀σ, (σ ⊨ P.instantiated_p) → dominates_n σ (x ≡ value.true) (x ≡ value.true)),
        from λ_ _, dominates_n.self,
        have h3: FV (prop.term (x ≡ value.true)) = set.insert x ∅, from set.eq_of_subset_of_subset (
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
        have h4: (FV (↑R ⋀ ↑H ⋀ P ⋀ (x ≡ value.true)) = FV ((↑R ⋀ ↑H ⋀ P) ⋀ (x ≡ value.true))) ∧
          (∀σ, dominates_p σ (↑R ⋀ ↑H ⋀ P ⋀ (x ≡ value.true)) ((↑R ⋀ ↑H ⋀ P) ⋀ (x ≡ value.true))) ∧
          (∀σ t, dominates_n σ ((↑H ⋀ ↑(P ⋀ (x ≡ value.true)) ⋀ Q) t)
                               ((↑H ⋀ ↑P ⋀ propctx.exis x (↑(x ≡ value.true) ⋀ Q)) t)) ∧
          (∀v: value, FV ((↑H ⋀ ↑P ⋀ propctx.exis x (↑(x ≡ value.true) ⋀ Q)) v)
                    ⊆ FV ((↑H ⋀ ↑(P ⋀ (x ≡ value.true)) ⋀ Q) v)),
        from @free_dominates_helper_eq_free H R P (x ≡ value.true) (x ≡ value.true) Q x h1 h2 h3 h3,
        have e'_verified': ↑R ⋀ H ⋀ P ⋀ x ≡ value.true ⊢ e' : Q,
        from strengthen_exp e'_verified (↑R ⋀ ↑H ⋀ P ⋀ x ≡ value.true) h4.left h4.right.left,
        have h3: ⊢ₛ (R, H, σ[x↦value.true], e') : ↑H ⋀ ↑(P ⋀ x ≡ value.true) ⋀ Q,
        from stack.vcgen.top σ'_verified fv_R' R_valid' e'_verified',
        exists.intro (↑H ⋀ ↑(P ⋀ x ≡ value.true) ⋀ Q) ⟨h3, h4.right.right⟩
      }
    },
    case exp.vcgen.fals x e' Q x_not_free e'_verified {

      cases e_steps,
      
      case step.fals { from
        have x ∉ σ, from (
          assume : x ∈ σ,
          have x ∈ σ.dom, from this,
          have x ∈ FV P, from (free_iff_contains σ_verified) ▸ this,
          have x ∈ FV (↑H ⋀ P), from free_in_prop.and₂ this,
          have x ∈ FV (↑R ⋀ ↑H ⋀ P), from free_in_prop.and₂ this,
          show «false», from x_not_free this
        ),
        have σ'_verified: ⊢ (σ[x↦value.false]) : P ⋀ x ≡ value.false, from env.vcgen.fls this σ_verified,
        have fv_R': FV R.to_prop ⊆ FV (P ⋀ x ≡ value.false), from set.subset.trans fv_R free_in_prop.and_left_subset,
        have R_valid': σ[x↦value.false] ⊨ R.to_prop.instantiated_n, from valid_with_additional_var R_valid,
        have h1: (∀σ, (σ ⊨ P.instantiated_p) → dominates_p σ (x ≡ value.false) (x ≡ value.false)),
        from λ_ _, dominates_p.self,
        have h2: (∀σ, (σ ⊨ P.instantiated_p) → dominates_n σ (x ≡ value.false) (x ≡ value.false)),
        from λ_ _, dominates_n.self,
        have h3: FV (prop.term (x ≡ value.false)) = set.insert x ∅, from set.eq_of_subset_of_subset (
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
        have h4: (FV (↑R ⋀ ↑H ⋀ P ⋀ (x ≡ value.false)) = FV ((↑R ⋀ ↑H ⋀ P) ⋀ (x ≡ value.false))) ∧
          (∀σ, dominates_p σ (↑R ⋀ ↑H ⋀ P ⋀ (x ≡ value.false)) ((↑R ⋀ ↑H ⋀ P) ⋀ (x ≡ value.false))) ∧
          (∀σ t, dominates_n σ ((↑H ⋀ ↑(P ⋀ (x ≡ value.false)) ⋀ Q) t)
                               ((↑H ⋀ ↑P ⋀ propctx.exis x (↑(x ≡ value.false) ⋀ Q)) t)) ∧
          (∀v: value, FV ((↑H ⋀ ↑P ⋀ propctx.exis x (↑(x ≡ value.false) ⋀ Q)) v)
                    ⊆ FV ((↑H ⋀ ↑(P ⋀ (x ≡ value.false)) ⋀ Q) v)),
        from @free_dominates_helper_eq_free H R P (x ≡ value.false) (x ≡ value.false) Q x h1 h2 h3 h3,
        have e'_verified': ↑R ⋀ H ⋀ P ⋀ x ≡ value.false ⊢ e' : Q,
        from strengthen_exp e'_verified (↑R ⋀ ↑H ⋀ P ⋀ x ≡ value.false) h4.left h4.right.left,
        have h3: ⊢ₛ (R, H, σ[x↦value.false], e') : ↑H ⋀ ↑(P ⋀ x ≡ value.false) ⋀ Q,
        from stack.vcgen.top σ'_verified fv_R' R_valid' e'_verified',
        exists.intro (↑H ⋀ ↑(P ⋀ x ≡ value.false) ⋀ Q) ⟨h3, h4.right.right⟩
      }
    },
    case exp.vcgen.num x n e' Q x_not_free e'_verified {

      cases e_steps,
      
      case step.num { from
        have x ∉ σ, from (
          assume : x ∈ σ,
          have x ∈ σ.dom, from this,
          have x ∈ FV P, from (free_iff_contains σ_verified) ▸ this,
          have x ∈ FV (↑H ⋀ P), from free_in_prop.and₂ this,
          have x ∈ FV (↑R ⋀ ↑H ⋀ P), from free_in_prop.and₂ this,
          show «false», from x_not_free this
        ),
        have σ'_verified: ⊢ (σ[x↦value.num n]) : P ⋀ x ≡ value.num n, from env.vcgen.num this σ_verified,
        have fv_R': FV R.to_prop ⊆ FV (P ⋀ x ≡ value.num n), from set.subset.trans fv_R free_in_prop.and_left_subset,
        have R_valid': σ[x↦value.num n] ⊨ R.to_prop.instantiated_n, from valid_with_additional_var R_valid,
        have h1: (∀σ, (σ ⊨ P.instantiated_p) → dominates_p σ (x ≡ value.num n) (x ≡ value.num n)),
        from λ_ _, dominates_p.self,
        have h2: (∀σ, (σ ⊨ P.instantiated_p) → dominates_n σ (x ≡ value.num n) (x ≡ value.num n)),
        from λ_ _, dominates_n.self,
        have h3: FV (prop.term (x ≡ value.num n)) = set.insert x ∅, from set.eq_of_subset_of_subset (
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
        have h4: (FV (↑R ⋀ ↑H ⋀ P ⋀ (x ≡ value.num n)) = FV ((↑R ⋀ ↑H ⋀ P) ⋀ (x ≡ value.num n))) ∧
          (∀σ, dominates_p σ (↑R ⋀ ↑H ⋀ P ⋀ (x ≡ value.num n)) ((↑R ⋀ ↑H ⋀ P) ⋀ (x ≡ value.num n))) ∧
          (∀σ t, dominates_n σ ((↑H ⋀ ↑(P ⋀ (x ≡ value.num n)) ⋀ Q) t)
                               ((↑H ⋀ ↑P ⋀ propctx.exis x (↑(x ≡ value.num n) ⋀ Q)) t)) ∧
          (∀v: value, FV ((↑H ⋀ ↑P ⋀ propctx.exis x (↑(x ≡ value.num n) ⋀ Q)) v)
                    ⊆ FV ((↑H ⋀ ↑(P ⋀ (x ≡ value.num n)) ⋀ Q) v)),
        from @free_dominates_helper_eq_free H R P (x ≡ value.num n) (x ≡ value.num n) Q x h1 h2 h3 h3,
        have e'_verified': ↑R ⋀ H ⋀ P ⋀ x ≡ value.num n ⊢ e' : Q,
        from strengthen_exp e'_verified (↑R ⋀ ↑H ⋀ P ⋀ x ≡ value.num n) h4.left h4.right.left,
        have h3: ⊢ₛ (R, H, σ[x↦value.num n], e') : ↑H ⋀ ↑(P ⋀ x ≡ value.num n) ⋀ Q,
        from stack.vcgen.top σ'_verified fv_R' R_valid' e'_verified',
        exists.intro (↑H ⋀ ↑(P ⋀ x ≡ value.num n) ⋀ Q) ⟨h3, h4.right.right⟩
      }
    },
    case exp.vcgen.func f x R' S' e₁ e₂ Q₁ Q₂ f_not_in x_not_in f_neq_x x_free_in_R' fv_R' fv_S' e₁_verified
                        e₂_verified func_vc {

      cases e_steps,
      
      case step.closure { from
        have f_not_in_σ: f ∉ σ, from (
          assume : f ∈ σ,
          have f ∈ σ.dom, from this,
          have f ∈ FV P, from (free_iff_contains σ_verified) ▸ this,
          have f ∈ FV (↑H ⋀ P), from free_in_prop.and₂ this,
          have f ∈ FV (↑R ⋀ ↑H ⋀ P), from free_in_prop.and₂ this,
          show «false», from f_not_in this
        ),
        have x_not_in_σ: x ∉ σ, from (
          assume : x ∈ σ,
          have x ∈ σ.dom, from this,
          have x ∈ FV P, from (free_iff_contains σ_verified) ▸ this,
          have x ∈ FV (↑H ⋀ P), from free_in_prop.and₂ this,
          have x ∈ FV (↑R ⋀ ↑H ⋀ P), from free_in_prop.and₂ this,
          show «false», from x_not_in this
        ),
        have fv_R'': FV R'.to_prop ⊆ FV P ∪ { f, x }, from (
          assume z: var,
          assume : z ∈ FV R'.to_prop,
          have z ∈ FV (prop.and ↑R (↑H⋀P)) ∪ {f, x}, from set.mem_of_subset_of_mem fv_R' this,
          or.elim (set.mem_or_mem_of_mem_union this) (
            assume : z ∈ FV (↑R ⋀ ↑H ⋀ P),
            or.elim (free_in_prop.and.inv this) (
              assume : z ∈ FV R.to_prop,
              have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
              show z ∈ FV P ∪ { f, x }, from set.mem_union_left { f, x } this
            ) (
              assume : z ∈ FV (↑H ⋀ P),
              or.elim (free_in_prop.and.inv this) (
                assume : z ∈ FV ↑H,
                show z ∈ FV P ∪ { f, x }, from absurd this (call_history_closed H z)
              ) (
                assume : z ∈ FV P,
                show z ∈ FV P ∪ { f, x }, from set.mem_union_left { f, x } this
              )
            )
          ) (
            assume : z ∈ {f, x},
            show z ∈ FV P ∪ { f, x }, from set.mem_union_right (FV P) this
          )
        ),
        have fv_S'': FV S'.to_prop ⊆ FV P ∪ { f, x }, from (
          assume z: var,
          assume : z ∈ FV S'.to_prop,
          have z ∈ FV (prop.and ↑R (↑H⋀P)) ∪ {f, x}, from set.mem_of_subset_of_mem fv_S' this,
          or.elim (set.mem_or_mem_of_mem_union this) (
            assume : z ∈ FV (↑R ⋀ ↑H ⋀ P),
            or.elim (free_in_prop.and.inv this) (
              assume : z ∈ FV R.to_prop,
              have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
              show z ∈ FV P ∪ { f, x }, from set.mem_union_left { f, x } this
            ) (
              assume : z ∈ FV (↑H ⋀ P),
              or.elim (free_in_prop.and.inv this) (
                assume : z ∈ FV ↑H,
                show z ∈ FV P ∪ { f, x }, from absurd this (call_history_closed H z)
              ) (
                assume : z ∈ FV P,
                show z ∈ FV P ∪ { f, x }, from set.mem_union_left { f, x } this
              )
            )
          ) (
            assume : z ∈ {f, x},
            show z ∈ FV P ∪ { f, x }, from set.mem_union_right (FV P) this
          )
        ),
        have e₁_verified': ↑H ⋀ P ⋀ spec.func f x R' S' ⋀ R' ⊢ e₁ : Q₁, from (
          have FV (↑H ⋀ P) = FV (↑R ⋀ ↑H ⋀ P), from set.eq_of_subset_of_subset (
            assume z: var,
            assume : z ∈ FV (↑H ⋀ P),
            show z ∈ FV (↑R ⋀ ↑H ⋀ P), from free_in_prop.and₂ this
          ) (
            assume z: var,
            assume : z ∈ FV (↑R ⋀ ↑H ⋀ P),
            or.elim (free_in_prop.and.inv this) (
              assume : z ∈ FV ↑R,
              have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
              show z ∈ FV (↑H ⋀ P), from free_in_prop.and₂ this
            ) id
          ),
          have h1: FV (↑H ⋀ P ⋀ spec.func f x R' S' ⋀ R')
                 = FV ((↑R ⋀ ↑H ⋀ P) ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R'),
          from eq.trans free_in_prop.and_assoc (free_in_prop.same_right this),
          have h2: ∀σ', dominates_p σ' (↑H ⋀ P ⋀ spec.func f x R' S' ⋀ R')
                                       ((↑R ⋀ ↑H ⋀ P) ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R'),
          from (
            assume σ': env,

            have h3: dominates_p σ' (↑H ⋀ P ⋀ spec.func f x R' S' ⋀ R')
                                    ((↑H ⋀ P) ⋀ spec.func f x R' S' ⋀ R'),
            from dominates_p.and_assoc,

            have h4: dominates_p σ' ((↑H ⋀ P) ⋀ spec.func f x R' S' ⋀ R')
                                    ((↑R ⋀ ↑H ⋀ P) ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R'),
            from dominates_p.same_right (
              assume _,

              have h3: dominates_p σ' (↑H ⋀ P)
                                      ((↑R ⋀ ↑H) ⋀ P),
              from dominates_p.same_right (
                assume P_valid: σ' ⊨ P.instantiated_p,

                have h5: (∀y, y ∈ σ → (σ y = σ' y)),
                from env_equiv_of_translation_valid σ_verified σ' P_valid,
                have h6: σ.dom ⊆ σ'.dom,
                from env.dom_subset_of_equivalent_env h5,

                have h7: closed_subst σ' R.to_prop, from (
                  assume z: var,
                  assume : z ∈ FV R.to_prop,
                  have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                  have z ∈ σ.dom, from (free_iff_contains σ_verified).symm ▸ this,
                  show z ∈ σ'.dom, from set.mem_of_subset_of_mem h6 this
                ),
                have h8: (calls_p R = ∅) ∧ (calls_n R = ∅), from no_calls_in_spec,
                have closed_subst σ R.to_prop, from (
                  assume z: var,
                  assume : z ∈ FV R.to_prop,
                  have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                  show z ∈ σ.dom, from (free_iff_contains σ_verified).symm ▸ this
                ),
                have h9: closed_subst σ R.to_prop.instantiated_n,
                from instantiated_n_closed_subst_of_closed this,
                have h10: ⊨ vc.subst_env σ R.to_prop.instantiated_n,
                from R_valid,
                have vc.subst_env σ R.to_prop.instantiated_n = vc.subst_env σ' R.to_prop.instantiated_n,
                from vc.subst_env_equivalent_env h5 h9,
                have h11: σ' ⊨ R.to_prop.instantiated_n,
                from this ▸ h10,
                show dominates_p σ' ↑H (↑R ⋀ ↑H),
                from dominates_p.and_intro_of_no_calls h7 h11 h8.left h8.right
              ),

              have h4: dominates_p σ' ((↑R ⋀ ↑H) ⋀ P)
                                      (↑R ⋀ ↑H ⋀ P),
              from dominates_p.and_assoc.symm,

              show dominates_p σ' (↑H ⋀ P)
                                  (↑R ⋀ ↑H ⋀ P),
              from dominates_p.trans h3 h4
            ),

            show dominates_p σ' (↑H ⋀ P ⋀ spec.func f x R' S' ⋀ R')
                                ((↑R ⋀ ↑H ⋀ P) ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R'),
            from dominates_p.trans h3 h4
          ),
          show (↑H ⋀ P ⋀ spec.func f x R' S' ⋀ R') ⊢ e₁ : Q₁,
          from strengthen_exp e₁_verified (↑H ⋀ P ⋀ spec.func f x R' S' ⋀ R') h1 h2
        ),
        have func_vc': ⟪prop.implies (↑H ⋀ P ⋀ spec.func f x R' S' ⋀ R' ⋀ Q₁ (term.app f x)) S'⟫, from (
          assume σ': env,
          
          have dominates_p σ' (↑H ⋀ P ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R' ⋀ Q₁ (term.app ↑f ↑x))
                              ((↑R ⋀ ↑H ⋀ P) ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R' ⋀ Q₁ (term.app ↑f ↑x)),
          from (

            have h1: dominates_p σ' (↑H ⋀ P ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R' ⋀ Q₁ (term.app ↑f ↑x))
                                ((↑H ⋀ P) ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R' ⋀ Q₁ (term.app ↑f ↑x)),
            from dominates_p.and_assoc,

            have h2: dominates_p σ' ((↑H ⋀ P) ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R' ⋀ Q₁ (term.app ↑f ↑x))
                                    ((↑R ⋀ ↑H ⋀ P) ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R' ⋀ Q₁ (term.app ↑f ↑x)),
            from dominates_p.same_right (
              assume _,

              have h3: dominates_p σ' (↑H ⋀ P)
                                      ((↑R ⋀ ↑H) ⋀ P),
              from dominates_p.same_right (
                assume P_valid: σ' ⊨ P.instantiated_p,

                have h5: (∀y, y ∈ σ → (σ y = σ' y)),
                from env_equiv_of_translation_valid σ_verified σ' P_valid,
                have h6: σ.dom ⊆ σ'.dom,
                from env.dom_subset_of_equivalent_env h5,

                have h7: closed_subst σ' R.to_prop, from (
                  assume z: var,
                  assume : z ∈ FV R.to_prop,
                  have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                  have z ∈ σ.dom, from (free_iff_contains σ_verified).symm ▸ this,
                  show z ∈ σ'.dom, from set.mem_of_subset_of_mem h6 this
                ),
                have h8: (calls_p R = ∅) ∧ (calls_n R = ∅), from no_calls_in_spec,
                have closed_subst σ R.to_prop, from (
                  assume z: var,
                  assume : z ∈ FV R.to_prop,
                  have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                  show z ∈ σ.dom, from (free_iff_contains σ_verified).symm ▸ this
                ),
                have h9: closed_subst σ R.to_prop.instantiated_n,
                from instantiated_n_closed_subst_of_closed this,
                have h10: ⊨ vc.subst_env σ R.to_prop.instantiated_n,
                from R_valid,
                have vc.subst_env σ R.to_prop.instantiated_n = vc.subst_env σ' R.to_prop.instantiated_n,
                from vc.subst_env_equivalent_env h5 h9,
                have h11: σ' ⊨ R.to_prop.instantiated_n,
                from this ▸ h10,
                show dominates_p σ' ↑H (↑R ⋀ ↑H),
                from dominates_p.and_intro_of_no_calls h7 h11 h8.left h8.right
              ),
              have h4: dominates_p σ' ((↑R ⋀ ↑H) ⋀ P)
                                      (↑R ⋀ ↑H ⋀ P),
              from dominates_p.and_assoc.symm,
              show dominates_p σ' (↑H ⋀ P)
                                  (↑R ⋀ ↑H ⋀ P),
              from dominates_p.trans h3 h4
            ),
            show dominates_p σ' (↑H ⋀ P ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R' ⋀ Q₁ (term.app ↑f ↑x))
                                ((↑R ⋀ ↑H ⋀ P) ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R' ⋀ Q₁ (term.app ↑f ↑x)),
            from dominates_p.trans h1 h2
          ),
          have dominates_n σ' (((↑R ⋀ ↑H ⋀ P) ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R' ⋀ Q₁ (term.app ↑f ↑x)).not ⋁ ↑S')
                              ((↑H ⋀ P ⋀ ↑(spec.func ↑f x R' S') ⋀ ↑R' ⋀ Q₁ (term.app ↑f ↑x)).not ⋁ ↑S'),
          from dominates_n.same_right_or (dominates_n.not this),

          show σ' ⊨ (prop.implies (↑H ⋀ P ⋀ spec.func f x R' S' ⋀ R' ⋀ Q₁ (term.app f x)) S').instantiated_n,
          from dominates_n.elim this (func_vc σ')
        ),
        let vf := value.func f x R' S' e₁ H σ in
        let P' := (↑(f ≡ vf)
                ⋀ prop.subst_env (σ[f↦vf]) (prop.func f x R' (Q₁ (term.app f x) ⋀ S'))) in
        let Q' := (prop.func f x R' (Q₁ (term.app f x) ⋀ S')) in
        have σ'_verified: ⊢ (σ[f↦vf]) : P ⋀ P',
        from env.vcgen.func f_not_in_σ f_not_in_σ x_not_in_σ f_neq_x σ_verified σ_verified
             x_free_in_R' fv_R'' fv_S'' e₁_verified' func_vc',
        have fv_R'': FV R.to_prop ⊆ FV (P ⋀ P'),
        from set.subset.trans fv_R free_in_prop.and_left_subset,
        have R_valid': σ[f↦vf] ⊨ R.to_prop.instantiated_n,
        from valid_with_additional_var R_valid,
        have h1: (∀σ', (σ' ⊨ P.instantiated_p) → dominates_p σ' P' Q'), from (
          assume σ': env,
          assume P_valid: σ' ⊨ P.instantiated_p,
          show dominates_p σ' (↑(f ≡ vf)
                ⋀ prop.subst_env (σ[f↦vf]) (prop.func f x R' (Q₁ (term.app f x) ⋀ S'))) Q',
          from dominates_p.left_elim (
            assume : σ' ⊨ prop.instantiated_p (f ≡ vf),
            have f_is_vf: σ' f = vf, from valid_env.subst_of_eq_instantiated_p this,
            have (∀y, y ∈ σ → (σ y = σ' y)),
            from env_equiv_of_translation_valid σ_verified σ' P_valid,
            have (∀y, y ∈ (σ[f↦vf]) → ((σ[f↦vf]) y = σ' y)),
            from env.equiv_of_rest_and_same this f_not_in_σ f_is_vf,
            show dominates_p σ' (prop.subst_env (σ[f↦vf]) (prop.func f x R' (Q₁ (term.app f x) ⋀ S')))
                                    (prop.func f x R' (Q₁ (term.app f x) ⋀ S')),
            from dominates_p_equiv_subst this
          )
        ),
        have h2: (∀σ', (σ' ⊨ P.instantiated_p) → dominates_n σ' P' Q'), from (
          assume σ': env,
          assume P_valid: σ' ⊨ P.instantiated_p,
          show dominates_n σ' (↑(f ≡ vf)
                ⋀ prop.subst_env (σ[f↦vf]) (prop.func f x R' (Q₁ (term.app f x) ⋀ S'))) Q',
          from dominates_n.left_elim (
            assume : σ' ⊨ prop.instantiated_p (f ≡ vf),
            have f_is_vf: σ' f = vf, from valid_env.subst_of_eq_instantiated_p this,
            have (∀y, y ∈ σ → (σ y = σ' y)),
            from env_equiv_of_translation_valid σ_verified σ' P_valid,
            have (∀y, y ∈ (σ[f↦vf]) → ((σ[f↦vf]) y = σ' y)),
            from env.equiv_of_rest_and_same this f_not_in_σ f_is_vf,
            show dominates_n σ' (prop.subst_env (σ[f↦vf]) (prop.func f x R' (Q₁ (term.app f x) ⋀ S')))
                                    (prop.func f x R' (Q₁ (term.app f x) ⋀ S')),
            from dominates_n_equiv_subst this
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
              have z ∈ FV (prop.and ↑R (↑H⋀P)) ∪ {f, x}, from set.mem_of_subset_of_mem fv_R' this,
              or.elim (set.mem_or_mem_of_mem_union this) (
                assume : z ∈ FV (↑R ⋀ ↑H ⋀ P),
                or.elim (free_in_prop.and.inv this) (
                  assume : z ∈ FV R.to_prop,
                  have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                  show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                ) (
                  assume : z ∈ FV (↑H ⋀ P),
                  or.elim (free_in_prop.and.inv this) (
                    assume : z ∈ FV ↑H,
                    show z ∈ FV P ∪ set.insert f ∅, from absurd this (call_history_closed H z)
                  ) (
                    assume : z ∈ FV P,
                    show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                  )
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
                have z ∈ FV (term.app f x) ∨ z ∈ FV ((↑R ⋀ ↑H ⋀ P) ⋀ (spec.func f x R' S') ⋀ R'),
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
                  assume : z ∈ FV ((↑R ⋀ ↑H ⋀ P) ⋀ (spec.func f x R' S') ⋀ R'),
                  or.elim (free_in_prop.and.inv this) (
                    assume : z ∈ FV (↑R ⋀ ↑H ⋀ P),
                    or.elim (free_in_prop.and.inv this) (
                      assume : z ∈ FV R.to_prop,
                      have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                      show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                    ) (
                      assume : z ∈ FV (↑H ⋀ P),
                      or.elim (free_in_prop.and.inv this) (
                        assume : z ∈ FV ↑H,
                        show z ∈ FV P ∪ set.insert f ∅, from absurd this (call_history_closed H z)
                      ) (
                        assume : z ∈ FV P,
                        show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                      )
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
                          have z ∈ FV (prop.and ↑R (↑H⋀P)) ∪ {f, x}, from set.mem_of_subset_of_mem fv_R' this,
                          or.elim (set.mem_or_mem_of_mem_union this) (
                            assume : z ∈ FV (↑R ⋀ ↑H ⋀ P),
                            or.elim (free_in_prop.and.inv this) (
                              assume : z ∈ FV R.to_prop,
                              have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                              show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                            ) (
                              assume : z ∈ FV (↑H ⋀ P),
                              or.elim (free_in_prop.and.inv this) (
                                assume : z ∈ FV ↑H,
                                show z ∈ FV P ∪ set.insert f ∅, from absurd this (call_history_closed H z)
                              ) (
                                assume : z ∈ FV P,
                                show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                              )
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
                          have z ∈ FV (prop.and ↑R (↑H⋀P)) ∪ {f, x}, from set.mem_of_subset_of_mem fv_S' this,
                          or.elim (set.mem_or_mem_of_mem_union this) (
                            assume : z ∈ FV (↑R ⋀ ↑H ⋀ P),
                            or.elim (free_in_prop.and.inv this) (
                              assume : z ∈ FV R.to_prop,
                              have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                              show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                            ) (
                              assume : z ∈ FV (↑H ⋀ P),
                              or.elim (free_in_prop.and.inv this) (
                                assume : z ∈ FV ↑H,
                                show z ∈ FV P ∪ set.insert f ∅, from absurd this (call_history_closed H z)
                              ) (
                                assume : z ∈ FV P,
                                show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                              )
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
                      have z ∈ FV (prop.and ↑R (↑H⋀P)) ∪ {f, x}, from set.mem_of_subset_of_mem fv_R' this,
                      or.elim (set.mem_or_mem_of_mem_union this) (
                        assume : z ∈ FV (↑R ⋀ ↑H ⋀ P),
                        or.elim (free_in_prop.and.inv this) (
                          assume : z ∈ FV R.to_prop,
                          have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                          show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                        ) (
                          assume : z ∈ FV (↑H ⋀ P),
                          or.elim (free_in_prop.and.inv this) (
                            assume : z ∈ FV ↑H,
                            show z ∈ FV P ∪ set.insert f ∅, from absurd this (call_history_closed H z)
                          ) (
                            assume : z ∈ FV P,
                            show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                          )
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
                have z ∈ FV (prop.and ↑R (↑H⋀P)) ∪ {f, x}, from set.mem_of_subset_of_mem fv_S' this,
                or.elim (set.mem_or_mem_of_mem_union this) (
                  assume : z ∈ FV (↑R ⋀ ↑H ⋀ P),
                  or.elim (free_in_prop.and.inv this) (
                    assume : z ∈ FV R.to_prop,
                    have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                    show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                  ) (
                    assume : z ∈ FV (↑H ⋀ P),
                    or.elim (free_in_prop.and.inv this) (
                      assume : z ∈ FV ↑H,
                      show z ∈ FV P ∪ set.insert f ∅, from absurd this (call_history_closed H z)
                    ) (
                      assume : z ∈ FV P,
                      show z ∈ FV P ∪ set.insert f ∅, from set.mem_union_left (set.insert f ∅) this
                    )
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
        have h4: (FV (↑R ⋀ ↑H ⋀ P ⋀ P') = FV ((↑R ⋀ ↑H ⋀ P) ⋀ Q')) ∧
          (∀σ, dominates_p σ (↑R ⋀ ↑H ⋀ P ⋀ P') ((↑R ⋀ ↑H ⋀ P) ⋀ Q')) ∧
          (∀σ t, dominates_n σ ((↑H ⋀ ↑(P ⋀ P') ⋀ Q₂) t) ((↑H ⋀ ↑P ⋀ propctx.exis f (↑Q' ⋀ Q₂)) t)) ∧
          (∀v: value, FV ((↑H ⋀ ↑P ⋀ propctx.exis f (↑Q' ⋀ Q₂)) v) ⊆ FV ((↑H ⋀ ↑(P ⋀ P') ⋀ Q₂) v)),
        from @free_dominates_helper H R P P' Q' Q₂ f h1 h2 h3a h3b h3c,
        have e'_verified': ↑R ⋀ H ⋀ P ⋀ P' ⊢ e' : Q₂,
        from strengthen_exp e₂_verified (↑R ⋀ ↑H ⋀ P ⋀ P') h4.left h4.right.left,
        have h3: ⊢ₛ (R, H, σ[f↦value.func f x R' S' e₁ H σ], e') : ↑H ⋀ ↑(P ⋀ P') ⋀ Q₂,
        from stack.vcgen.top σ'_verified fv_R'' R_valid' e'_verified',
        exists.intro (↑H ⋀ ↑(P ⋀ P') ⋀ Q₂) ⟨h3, h4.right.right⟩
      }
    },
    case exp.vcgen.unop op x y e' Q x_free_in_P y_not_free e'_verified vc_valid {
      cases e_steps,
      case step.unop vx vy x_is_vx vy_is_op { from
        have y_not_in_σ: y ∉ σ, from (
          assume : y ∈ σ,
          have y ∈ σ.dom, from this,
          have y ∈ FV P, from (free_iff_contains σ_verified) ▸ this,
          have y ∈ FV (↑H ⋀ P), from free_in_prop.and₂ this,
          have y ∈ FV (↑R ⋀ ↑H ⋀ P), from free_in_prop.and₂ this,
          show «false», from y_not_free this
        ),
        have σ'_verified: ⊢ (σ[y↦vy]) : P ⋀ y ≡ vy, from (
          or.elim (unop_result_not_function vy_is_op) (
            assume vy_is_true: vy = value.true,
            have σ'_verified: ⊢ (σ[y↦value.true]) : P ⋀ y ≡ value.true, from env.vcgen.tru y_not_in_σ σ_verified,
            show ⊢ (σ[y↦vy]) : P ⋀ y ≡ vy, from vy_is_true.symm ▸ σ'_verified
          ) (
            assume vy_is_false: vy = value.false,
            have σ'_verified: ⊢ (σ[y↦value.false]) : P ⋀ y ≡ value.false, from env.vcgen.fls y_not_in_σ σ_verified,
            show ⊢ (σ[y↦vy]) : P ⋀ y ≡ vy, from vy_is_false.symm ▸ σ'_verified
          )
        ),
        have fv_R': FV R.to_prop ⊆ FV (P ⋀ y ≡ vy), from set.subset.trans fv_R free_in_prop.and_left_subset,
        have R_valid': σ[y↦vy] ⊨ R.to_prop.instantiated_n, from valid_with_additional_var R_valid,
        have h1: (∀σ, (σ ⊨ P.instantiated_p) → dominates_p σ (y ≡ vy) (y ≡ term.unop op x)),
        from (
          assume σ': env,
          assume : σ' ⊨ P.instantiated_p,
          have env_equiv: (∀y, y ∈ σ → (σ y = σ' y)),
          from env_equiv_of_translation_valid σ_verified σ' this,

          have h_impl: ((σ' ⊨ prop.instantiated_p (y ≡ vy))
                      → (σ' ⊨ prop.instantiated_p (y ≡ term.unop op x))),
          from (
            assume : σ' ⊨ prop.instantiated_p (y ≡ vy),
            have y_is_vy: σ' y = some vy, from valid_env.subst_of_eq_instantiated_p this,
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
            have (prop.term (y ≡ term.unop op x)).erased_p = vc.term (y ≡ term.unop op x),
            by unfold prop.erased_p,

            have h6: σ' ⊨ (prop.term (y ≡ term.unop op x)).erased_p,
            from this.symm ▸ h5,

            have calls_p (y ≡ term.unop op x) = ∅, from set.eq_empty_of_forall_not_mem (
              assume c: calltrigger,
              assume : c ∈ calls_p (y ≡ term.unop op x),
              show «false», from prop.has_call_p.term.inv this
            ),
            have (prop.term (y ≡ term.unop op x)).instantiated_p = (prop.term (y ≡ term.unop op x)).erased_p,
            from instantiated_p_eq_erased_p_without_calls this,

            show σ' ⊨ prop.instantiated_p (y ≡ term.unop op x),
            from this.symm ▸ h6
          ),
          have h_calls: calls_p_subst σ' (y ≡ term.unop op x) ⊆ calls_p_subst σ' (y ≡ vy), from (
            assume c: calltrigger,
            assume : c ∈ calls_p_subst σ' (y ≡ term.unop op x),
            show c ∈ calls_p_subst σ' (y ≡ vy), from absurd this prop.has_call_p_subst.term.inv
          ),
          have h_quantifiers: quantifiers_p (y ≡ term.unop op x) = ∅, from set.eq_empty_of_forall_not_mem (
            assume q: callquantifier,
            assume : q ∈ quantifiers_p (y ≡ term.unop op x),
            show «false», from prop.has_quantifier_p.term.inv this
          ),
          dominates_p.no_quantifiers h_impl h_calls h_quantifiers
        ),
        have h2: (∀σ, (σ ⊨ P.instantiated_p) → dominates_n σ (y ≡ vy) (y ≡ term.unop op x)),
        from (
          assume σ': env,
          assume : σ' ⊨ P.instantiated_p,

          have env_equiv: (∀y, y ∈ σ → (σ y = σ' y)),
          from env_equiv_of_translation_valid σ_verified σ' this,

          have h_impl: ((σ' ⊨ prop.instantiated_n (y ≡ vy))
                      → (σ' ⊨ prop.instantiated_n (y ≡ term.unop op x))),
          from (
            assume : σ' ⊨ prop.instantiated_n (y ≡ vy),
            have y_is_vy: σ' y = some vy, from valid_env.subst_of_eq_instantiated_n this,
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
            have (prop.term (y ≡ term.unop op x)).erased_n = vc.term (y ≡ term.unop op x),
            by unfold prop.erased_n,

            have h6: σ' ⊨ (prop.term (y ≡ term.unop op x)).erased_n,
            from this.symm ▸ h5,

            have calls_n (y ≡ term.unop op x) = ∅, from set.eq_empty_of_forall_not_mem (
              assume c: calltrigger,
              assume : c ∈ calls_n (y ≡ term.unop op x),
              show «false», from prop.has_call_n.term.inv this
            ),
            have (prop.term (y ≡ term.unop op x)).instantiated_n = (prop.term (y ≡ term.unop op x)).erased_n,
            from instantiated_n_eq_erased_n_without_calls this,

            show σ' ⊨ prop.instantiated_n (y ≡ term.unop op x),
            from this.symm ▸ h6
          ),
          have h_calls: calls_n_subst σ' (y ≡ term.unop op x) ⊆ calls_n_subst σ' (y ≡ vy), from (
            assume c: calltrigger,
            assume : c ∈ calls_n_subst σ' (y ≡ term.unop op x),
            show c ∈ calls_n_subst σ' (y ≡ vy), from absurd this prop.has_call_n_subst.term.inv
          ),
          have h_quantifiers: quantifiers_n (y ≡ term.unop op x) = ∅, from set.eq_empty_of_forall_not_mem (
            assume q: callquantifier,
            assume : q ∈ quantifiers_n (y ≡ term.unop op x),
            show «false», from prop.has_quantifier_n.term.inv this
          ),
          dominates_n.no_quantifiers h_impl h_calls h_quantifiers
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
            have z ∈ FV (↑R ⋀ ↑H ⋀ P), from this.symm ▸ x_free_in_P,
            or.elim (free_in_prop.and.inv this) (
              assume : z ∈ FV ↑R,
              have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
              show z ∈ FV P ∪ set.insert y ∅, from set.mem_union_left (set.insert y ∅) this
            ) (
              assume : z ∈ FV (↑H ⋀ P),
              or.elim (free_in_prop.and.inv this) (
                assume : z ∈ FV ↑H,
                show z ∈ FV P ∪ set.insert y ∅, from absurd this (call_history_closed H z)
              ) (
                assume : z ∈ FV P,
                show z ∈ FV P ∪ set.insert y ∅, from set.mem_union_left (set.insert y ∅) this
              )
            )
          )
        ),
        have h4: (FV (↑R ⋀ ↑H ⋀ P ⋀ (y ≡ vy)) = FV ((↑R ⋀ ↑H ⋀ P) ⋀ (y ≡ term.unop op x))) ∧
          (∀σ, dominates_p σ (↑R ⋀ ↑H ⋀ P ⋀ (y ≡ vy)) ((↑R ⋀ ↑H ⋀ P) ⋀ (y ≡ term.unop op x))) ∧
          (∀σ t, dominates_n σ ((↑H ⋀ ↑(P ⋀ (y ≡ vy)) ⋀ Q) t)
                               ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(y ≡ term.unop op x) ⋀ Q)) t)) ∧
          (∀v: value, FV ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(y ≡ term.unop op x) ⋀ Q)) v)
                    ⊆ FV ((↑H ⋀ ↑(P ⋀ (y ≡ vy)) ⋀ Q) v)),
        from @free_dominates_helper H R P (y ≡ vy) (y ≡ term.unop op x) Q y h1 h2 h3a h3b h3c,
        have e'_verified': ↑R ⋀ H ⋀ P ⋀ y ≡ vy ⊢ e' : Q,
        from strengthen_exp e'_verified (↑R ⋀ ↑H ⋀ P ⋀ y ≡ vy) h4.left h4.right.left,
        have h3: ⊢ₛ (R, H, σ[y↦vy], e') : ↑H ⋀ ↑(P ⋀ y ≡ vy) ⋀ Q,
        from stack.vcgen.top σ'_verified fv_R' R_valid' e'_verified',
        exists.intro (↑H ⋀ ↑(P ⋀ y ≡ vy) ⋀ Q) ⟨h3, h4.right.right⟩
      }
    },
    case exp.vcgen.binop op x y z e' Q x_free_in_P y_free_in_P z_not_free e'_verified vc_valid {
      cases e_steps,
      case step.binop vx vy vz x_is_vx y_is_vy vz_is_op { from
        have z_not_in_σ: z ∉ σ, from (
          assume : z ∈ σ,
          have z ∈ σ.dom, from this,
          have z ∈ FV P, from (free_iff_contains σ_verified) ▸ this,
          have z ∈ FV (↑H ⋀ P), from free_in_prop.and₂ this,
          have z ∈ FV (↑R ⋀ ↑H ⋀ P), from free_in_prop.and₂ this,
          show «false», from z_not_free this
        ),
        have σ'_verified: ⊢ (σ[z↦vz]) : P ⋀ z ≡ vz, from (
          or.elim (binop_result_not_function vz_is_op) (
            assume vz_is_true: vz = value.true,
            have σ'_verified: ⊢ (σ[z↦value.true]) : P ⋀ z ≡ value.true, from env.vcgen.tru z_not_in_σ σ_verified,
            show ⊢ (σ[z↦vz]) : P ⋀ z ≡ vz, from vz_is_true.symm ▸ σ'_verified
          ) (
            assume : (vz = value.false) ∨ (∃n, vz = value.num n),
            or.elim this (
              assume vz_is_false: vz = value.false,
              have σ'_verified: ⊢ (σ[z↦value.false]) : P ⋀ z ≡ value.false, from env.vcgen.fls z_not_in_σ σ_verified,
              show ⊢ (σ[z↦vz]) : P ⋀ z ≡ vz, from vz_is_false.symm ▸ σ'_verified
            ) (
              assume : ∃n, vz = value.num n,
              let ⟨n, vz_is_num⟩ := this in
              have σ'_verified: ⊢ (σ[z↦value.num n]) : P ⋀ z ≡ value.num n, from env.vcgen.num z_not_in_σ σ_verified,
              show ⊢ (σ[z↦vz]) : P ⋀ z ≡ vz, from vz_is_num.symm ▸ σ'_verified
            )
          )
        ),
        have fv_R': FV R.to_prop ⊆ FV (P ⋀ z ≡ vz), from set.subset.trans fv_R free_in_prop.and_left_subset,
        have R_valid': σ[z↦vz] ⊨ R.to_prop.instantiated_n, from valid_with_additional_var R_valid,
        have h1: (∀σ, (σ ⊨ P.instantiated_p) → dominates_p σ (z ≡ vz) (z ≡ term.binop op x y)),
        from (
          assume σ': env,
          assume : σ' ⊨ P.instantiated_p,
          have env_equiv: (∀y, y ∈ σ → (σ y = σ' y)),
          from env_equiv_of_translation_valid σ_verified σ' this,

          have h_impl: ((σ' ⊨ prop.instantiated_p (z ≡ vz))
                      → (σ' ⊨ prop.instantiated_p (z ≡ term.binop op x y))),
          from (
            assume : σ' ⊨ prop.instantiated_p (z ≡ vz),
            have z_is_vz: σ' z = some vz, from valid_env.subst_of_eq_instantiated_p this,
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
            have (prop.term (z ≡ term.binop op x y)).erased_p = vc.term (z ≡ term.binop op x y),
            by unfold prop.erased_p,

            have h6: σ' ⊨ (prop.term (z ≡ term.binop op x y)).erased_p,
            from this.symm ▸ h5,

            have calls_p (z ≡ term.binop op x y) = ∅, from set.eq_empty_of_forall_not_mem (
              assume c: calltrigger,
              assume : c ∈ calls_p (z ≡ term.binop op x y),
              show «false», from prop.has_call_p.term.inv this
            ),
            have (prop.term (z ≡ term.binop op x y)).instantiated_p = (prop.term (z ≡ term.binop op x y)).erased_p,
            from instantiated_p_eq_erased_p_without_calls this,

            show σ' ⊨ prop.instantiated_p (z ≡ term.binop op x y),
            from this.symm ▸ h6
          ),
          have h_calls: calls_p_subst σ' (z ≡ term.binop op x y) ⊆ calls_p_subst σ' (z ≡ vz), from (
            assume c: calltrigger,
            assume : c ∈ calls_p_subst σ' (z ≡ term.binop op x y),
            show c ∈ calls_p_subst σ' (z ≡ vz), from absurd this prop.has_call_p_subst.term.inv
          ),
          have h_quantifiers: quantifiers_p (z ≡ term.binop op x y) = ∅, from set.eq_empty_of_forall_not_mem (
            assume q: callquantifier,
            assume : q ∈ quantifiers_p (z ≡ term.binop op x y),
            show «false», from prop.has_quantifier_p.term.inv this
          ),
          dominates_p.no_quantifiers h_impl h_calls h_quantifiers
        ),
        have h2: (∀σ, (σ ⊨ P.instantiated_p) → dominates_n σ (z ≡ vz) (z ≡ term.binop op x y)),
        from (
          assume σ': env,
          assume : σ' ⊨ P.instantiated_p,

          have env_equiv: (∀y, y ∈ σ → (σ y = σ' y)),
          from env_equiv_of_translation_valid σ_verified σ' this,

          have h_impl: ((σ' ⊨ prop.instantiated_n (z ≡ vz))
                      → (σ' ⊨ prop.instantiated_n (z ≡ term.binop op x y))),
          from (
            assume : σ' ⊨ prop.instantiated_n (z ≡ vz),
            have z_is_vz: σ' z = some vz, from valid_env.subst_of_eq_instantiated_n this,
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
            have (prop.term (z ≡ term.binop op x y)).erased_n = vc.term (z ≡ term.binop op x y),
            by unfold prop.erased_n,

            have h6: σ' ⊨ (prop.term (z ≡ term.binop op x y)).erased_n,
            from this.symm ▸ h5,

            have calls_n (z ≡ term.binop op x y) = ∅, from set.eq_empty_of_forall_not_mem (
              assume c: calltrigger,
              assume : c ∈ calls_n (z ≡ term.binop op x y),
              show «false», from prop.has_call_n.term.inv this
            ),
            have (prop.term (z ≡ term.binop op x y)).instantiated_n = (prop.term (z ≡ term.binop op x y)).erased_n,
            from instantiated_n_eq_erased_n_without_calls this,

            show σ' ⊨ prop.instantiated_n (z ≡ term.binop op x y),
            from this.symm ▸ h6
          ),
          have h_calls: calls_n_subst σ' (z ≡ term.binop op x y) ⊆ calls_n_subst σ' (z ≡ vz), from (
            assume c: calltrigger,
            assume : c ∈ calls_n_subst σ' (z ≡ term.binop op x y),
            show c ∈ calls_n_subst σ' (z ≡ vz), from absurd this prop.has_call_n_subst.term.inv
          ),
          have h_quantifiers: quantifiers_n (z ≡ term.binop op x y) = ∅, from set.eq_empty_of_forall_not_mem (
            assume q: callquantifier,
            assume : q ∈ quantifiers_n (z ≡ term.binop op x y),
            show «false», from prop.has_quantifier_n.term.inv this
          ),
          dominates_n.no_quantifiers h_impl h_calls h_quantifiers
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
              have a ∈ FV (↑R ⋀ ↑H ⋀ P), from this.symm ▸ x_free_in_P,
              or.elim (free_in_prop.and.inv this) (
                assume : a ∈ FV ↑R,
                have a ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                show a ∈ FV P ∪ set.insert z ∅, from set.mem_union_left (set.insert z ∅) this
              ) (
                assume : a ∈ FV (↑H ⋀ P),
                or.elim (free_in_prop.and.inv this) (
                  assume : a ∈ FV ↑H,
                  show a ∈ FV P ∪ set.insert z ∅, from absurd this (call_history_closed H a)
                ) (
                  assume : a ∈ FV P,
                  show a ∈ FV P ∪ set.insert z ∅, from set.mem_union_left (set.insert z ∅) this
                )
              )
            ) (
              assume : free_in_term a y,
              have a = y, from free_in_term.var.inv this,
              have a ∈ FV (↑R ⋀ ↑H ⋀ P), from this.symm ▸ y_free_in_P,
              or.elim (free_in_prop.and.inv this) (
                assume : a ∈ FV ↑R,
                have a ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                show a ∈ FV P ∪ set.insert z ∅, from set.mem_union_left (set.insert z ∅) this
              ) (
                assume : a ∈ FV (↑H ⋀ P),
                or.elim (free_in_prop.and.inv this) (
                  assume : a ∈ FV ↑H,
                  show a ∈ FV P ∪ set.insert z ∅, from absurd this (call_history_closed H a)
                ) (
                  assume : a ∈ FV P,
                  show a ∈ FV P ∪ set.insert z ∅, from set.mem_union_left (set.insert z ∅) this
                )
              )
            )
          )
        ),
        have h4: (FV (↑R ⋀ ↑H ⋀ P ⋀ (z ≡ vz)) = FV ((↑R ⋀ ↑H ⋀ P) ⋀ (z ≡ term.binop op x y))) ∧
          (∀σ, dominates_p σ (↑R ⋀ ↑H ⋀ P ⋀ (z ≡ vz)) ((↑R ⋀ ↑H ⋀ P) ⋀ (z ≡ term.binop op x y))) ∧
          (∀σ t, dominates_n σ ((↑H ⋀ ↑(P ⋀ (z ≡ vz)) ⋀ Q) t)
                               ((↑H ⋀ ↑P ⋀ propctx.exis z (↑(z ≡ term.binop op x y) ⋀ Q)) t)) ∧
          (∀v: value, FV ((↑H ⋀ ↑P ⋀ propctx.exis z (↑(z ≡ term.binop op x y) ⋀ Q)) v)
                    ⊆ FV ((↑H ⋀ ↑(P ⋀ (z ≡ vz)) ⋀ Q) v)),
        from @free_dominates_helper H R P (z ≡ vz) (z ≡ term.binop op x y) Q z h1 h2 h3a h3b h3c,
        have e'_verified': ↑R ⋀ H ⋀ P ⋀ z ≡ vz ⊢ e' : Q,
        from strengthen_exp e'_verified (↑R ⋀ ↑H ⋀ P ⋀ z ≡ vz) h4.left h4.right.left,
        have h3: ⊢ₛ (R, H, σ[z↦vz], e') : ↑H ⋀ ↑(P ⋀ z ≡ vz) ⋀ Q,
        from stack.vcgen.top σ'_verified fv_R' R_valid' e'_verified',
        exists.intro (↑H ⋀ ↑(P ⋀ z ≡ vz) ⋀ Q) ⟨h3, h4.right.right⟩
      }
    },
    case exp.vcgen.app y f x e' Q' f_free_in_P x_free_in_P _ e'_verified vc_valid {
      cases e_steps
    },
    case exp.vcgen.ite x e₂ e₁ Q₁ Q₂ x_free_in_P e₁_verified e₂_verified vc_valid {
      cases e_steps,

      case step.ite_true x_is_true { from

        have h1: FV (↑R ⋀ ↑H ⋀ P) = FV ((↑R ⋀ ↑H ⋀ P) ⋀ x), from set.eq_of_subset_of_subset (
          assume z: var,
          assume : z ∈ FV (↑R ⋀ ↑H ⋀ P),
          show z ∈ FV ((↑R ⋀ ↑H ⋀ P) ⋀ x), from free_in_prop.and₁ this
        ) (
          assume z: var,
          assume : z ∈ FV ((↑R ⋀ ↑H ⋀ P) ⋀ x),
          or.elim (free_in_prop.and.inv this) id (
            assume : free_in_prop z x,
            have free_in_term z x, from free_in_prop.term.inv this,
            have z = x, from free_in_term.var.inv this,
            show z ∈ FV (↑R ⋀ ↑H ⋀ P), from this.symm ▸ x_free_in_P
          )
        ),

        have h2: ∀σ', dominates_p σ' (↑R ⋀ ↑H ⋀ P) ((↑R ⋀ ↑H ⋀ P) ⋀ x),
        from λσ', dominates_p.and_right_intro_of_no_calls (
          assume : σ' ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_p,
          have σ' ⊨ (↑H ⋀ P).instantiated_p,
          from (valid_env.and.elim (valid_env.instantiated_p_and_elim this)).right,
          have σ' ⊨ P.instantiated_p,
          from (valid_env.and.elim (valid_env.instantiated_p_and_elim this)).right,
          have env_equiv: (∀y, y ∈ σ → (σ y = σ' y)),
          from env_equiv_of_translation_valid σ_verified σ' this,

          have h3: closed_subst σ' (prop.term x), from (
            assume z: var,
            assume : z ∈ FV (prop.term x),
            have free_in_term z x, from free_in_prop.term.inv this,
            have z = x, from free_in_term.var.inv this,
            have z ∈ FV (↑R ⋀ ↑H ⋀ P), from this.symm ▸ x_free_in_P,
            or.elim (free_in_prop.and.inv this) (
              assume : z ∈ FV ↑R,
              have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
              have z ∈ σ.dom, from (free_iff_contains σ_verified).symm ▸ this,
              have z ∈ σ'.dom, from set.mem_of_subset_of_mem (env.dom_subset_of_equivalent_env env_equiv) this,
              show z ∈ σ', from this
            ) (
              assume : z ∈ FV (↑H ⋀ P),
              or.elim (free_in_prop.and.inv this) (
                assume : z ∈ FV ↑H,
                show z ∈ σ', from absurd this (call_history_closed H z)
              ) (
                assume : z ∈ FV P,
                have z ∈ σ.dom, from (free_iff_contains σ_verified).symm ▸ this,
                have z ∈ σ'.dom, from set.mem_of_subset_of_mem (env.dom_subset_of_equivalent_env env_equiv) this,
                show z ∈ σ', from this
              )
            )
          ),

          have h4: calls_p (prop.term x) = ∅, from set.eq_empty_of_forall_not_mem (
            assume c: calltrigger,
            assume : c ∈ calls_p (prop.term x),
            show «false», from prop.has_call_p.term.inv this
          ),

          have h5: calls_n (prop.term x) = ∅, from set.eq_empty_of_forall_not_mem (
            assume c: calltrigger,
            assume : c ∈ calls_n (prop.term x),
            show «false», from prop.has_call_n.term.inv this
          ),

          have h6: σ' ⊨ (prop.term x).instantiated_n, from (
            have σ' x = some value.true, from eq_value_of_equiv_subst env_equiv x_is_true,
            have x_subst: term.subst_env σ' x = value.true, from (term.subst_env.var.right value.true).mp this,

            have ⊨ value.true, from valid.tru,
            have h7: ⊨ term.subst_env σ' x, from x_subst.symm ▸ this,
            have vc.subst_env σ' x = term.subst_env σ' x, from vc.subst_env.term,
            have ⊨ vc.subst_env σ' x, from this.symm ▸ h7,
            have h8: σ' ⊨ vc.term x, from this,
            have (prop.term x).erased_n = vc.term x, by unfold prop.erased_n,
            have h9: σ' ⊨ (prop.term x).erased_n, from this.symm ▸ h8,

            have (prop.term x).instantiated_n = (prop.term x).erased_n,
            from instantiated_n_eq_erased_n_without_calls h5,

            show σ' ⊨ (prop.term x).instantiated_n, from this.symm ▸ h9
          ),

          ⟨h3, ⟨h6, ⟨h4, h5⟩⟩⟩
        ),

        have e'_verified: ↑R ⋀ ↑H ⋀ P ⊢ e' : Q₁,
        from strengthen_exp e₁_verified (↑R ⋀ ↑H ⋀ P) h1 h2,
        have h3: ⊢ₛ (R, H, σ, e') : H ⋀ P ⋀ Q₁,
        from stack.vcgen.top σ_verified fv_R R_valid e'_verified,

        have hb1: ∀t, ((↑H ⋀ ↑P ⋀ Q₁) t) = (↑H ⋀ P ⋀ Q₁ t), from λt, propctx_apply_hpq,
        have hb2: ∀t, ((↑H ⋀ ↑P ⋀ (propctx.implies ↑x Q₁) ⋀ (propctx.implies ↑(prop.not x) Q₂)) t)
                     = (↑H ⋀ P ⋀ (propctx.and (propctx.implies ↑x Q₁) (propctx.implies ↑(prop.not x) Q₂)) t),
        from λt, propctx_apply_hpq,
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
          dominates_n σ' ((↑H ⋀ ↑P ⋀ Q₁) t)
                         ((↑H ⋀ ↑P ⋀ (propctx.implies ↑x Q₁) ⋀ (propctx.implies ↑(prop.not x) Q₂)) t), from (
          assume σ': env,
          assume t: term,

          have h5: dominates_n σ' (↑H ⋀ P ⋀ Q₁ t)
                                  (↑H ⋀ P ⋀ prop.implies x (Q₁ t) ⋀ prop.implies (prop.not x) (Q₂ t)),
          from dominates_n.same_left (λ_, dominates_n.same_left (
            assume : σ' ⊨ P.instantiated_p,
            have env_equiv: (∀y, y ∈ σ → (σ y = σ' y)),
            from env_equiv_of_translation_valid σ_verified σ' this,
            have σ' x = some value.true, from eq_value_of_equiv_subst env_equiv x_is_true,
            have x_subst: term.subst_env σ' x = value.true, from (term.subst_env.var.right value.true).mp this,

            sorry
          )),

          (hb1 t).symm ▸ (hb2 t).symm ▸ (hb5 t).symm ▸ h5
        ),

        have h5: ∀v: value,
             FV ((↑H ⋀ ↑P ⋀ propctx.and (propctx.implies ↑x Q₁) (propctx.implies ↑(prop.not x) Q₂)) v)
           ⊆ FV ((↑H ⋀ ↑P ⋀ Q₁) v), from (
          assume v: value,

          have FV (P ⋀ prop.implies x (Q₁ v) ⋀ prop.implies (prop.not x) (Q₂ v))
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
                  have z ∈ FV (↑R ⋀ ↑H ⋀ P), from this.symm ▸ x_free_in_P,
                  or.elim (free_in_prop.and.inv this) (
                    assume : z ∈ FV ↑R,
                    have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                    show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
                  ) (
                    assume : z ∈ FV (↑H ⋀ P),
                    or.elim (free_in_prop.and.inv this) (
                      assume : z ∈ FV ↑H,
                      show z ∈ FV (P ⋀ Q₁ v), from absurd this (call_history_closed H z)
                    ) (
                      assume : z ∈ FV P,
                      show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
                    )
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
                  have z ∈ FV (↑R ⋀ ↑H ⋀ P), from this.symm ▸ x_free_in_P,
                  or.elim (free_in_prop.and.inv this) (
                    assume : z ∈ FV ↑R,
                    have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                    show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
                  ) (
                    assume : z ∈ FV (↑H ⋀ P),
                    or.elim (free_in_prop.and.inv this) (
                      assume : z ∈ FV ↑H,
                      show z ∈ FV (P ⋀ Q₁ v), from absurd this (call_history_closed H z)
                    ) (
                      assume : z ∈ FV P,
                      show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
                    )
                  )
                ) (
                  assume : z ∈ FV (Q₂ v),
                  or.elim (exp.post_free e₂_verified v this) (
                    assume : z ∈ FV (term.value v),
                    show z ∈ FV (P ⋀ Q₁ v), from absurd this free_in_term.value.inv
                  ) (
                    assume : z ∈ FV ((↑R ⋀ ↑H ⋀ P) ⋀ prop.not x),
                    or.elim (free_in_prop.and.inv this) (
                      assume : z ∈ FV (↑R ⋀ ↑H ⋀ P),
                      or.elim (free_in_prop.and.inv this) (
                        assume : z ∈ FV ↑R,
                        have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                        show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
                      ) (
                        assume : z ∈ FV (↑H ⋀ P),
                        or.elim (free_in_prop.and.inv this) (
                          assume : z ∈ FV ↑H,
                          show z ∈ FV (P ⋀ Q₁ v), from absurd this (call_history_closed H z)
                        ) (
                          assume : z ∈ FV P,
                          show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
                        )
                      )
                    ) (
                      assume : z ∈ FV (prop.not x),
                      have free_in_prop z x, from free_in_prop.not.inv this,
                      have free_in_term z x, from free_in_prop.term.inv this,
                      have z = x, from free_in_term.var.inv this,
                      have z ∈ FV (↑R ⋀ ↑H ⋀ P), from this.symm ▸ x_free_in_P,
                      or.elim (free_in_prop.and.inv this) (
                        assume : z ∈ FV ↑R,
                        have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
                        show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
                      ) (
                        assume : z ∈ FV (↑H ⋀ P),
                        or.elim (free_in_prop.and.inv this) (
                          assume : z ∈ FV ↑H,
                          show z ∈ FV (P ⋀ Q₁ v), from absurd this (call_history_closed H z)
                        ) (
                          assume : z ∈ FV P,
                          show z ∈ FV (P ⋀ Q₁ v), from free_in_prop.and₁ this
                        )
                      )
                    )
                  )
                )
              )
            )
          ),
          have h6: FV (↑H ⋀ P ⋀ prop.implies x (Q₁ v) ⋀ prop.implies (prop.not x) (Q₂ v))
                 ⊆ FV (↑H ⋀ P ⋀ Q₁ v),
          from free_in_prop.sub_same_left this,
          (hb1 v).symm ▸ (hb2 v).symm ▸ (hb5 v).symm ▸ h6
        ),
        exists.intro (↑H ⋀ ↑P ⋀ Q₁) ⟨h3, ⟨h4, h5⟩⟩
      },

      case step.ite_false {
        admit
      }
    },
    case exp.vcgen.return x x_free_in_P {
      cases e_steps
    }
  end

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
    from prop.subst_env.forallc_not_in this,

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
    assume v: value,

    have ¬ (x = f ∨ x ∈ σ₁), from not_or_distrib.mpr ⟨x_neq_f, x_not_in_σ₁⟩,
    have h61: x ∉ (σ₁[f↦vf]), from mt env.contains.inv this,
    have (∀y, y ∈ (σ₁[f↦vf]) → ((σ₁[f↦vf]) y = (σ.without x) y)),
    from env.remove_unimportant_equivalence env_equiv h61,
    have (∀y, y ∈ (σ₁[f↦vf]) → ((σ₁[f↦vf]) y = (σ.without x[x↦v]) y)),
    from env.equiv_of_not_contains this h61,
    have h7: dominates_p (σ.without x[x↦v]) (prop.subst_env (σ₁[f↦vf]) forallp') forallp',
    from dominates_p_equiv_subst this,
    have h82: dominates_p (σ.without x[x↦v]) (prop.implies (prop.post f x) (Q (term.app f x) ⋀ S.to_prop))
                                 (prop.implies (prop.post f x) S.to_prop),
    from dominates_p.or_intro dominates_p.self dominates_p.of_and_right,
    have h8: dominates_p (σ.without x[x↦v]) forallp' forallp,
    from dominates_p.same_left (λ_, h82),
    show dominates_p (σ.without x[x↦v]) (prop.subst_env (σ₁[f↦vf]) forallp') forallp,
    from dominates_p.trans h7 h8
  ),
  have h7: dominates_p σ (term.unop unop.isFunc vf ⋀ prop.forallc x vf (prop.subst_env (σ₁[f↦vf]) forallp'))
                       (term.unop unop.isFunc f ⋀ prop.forallc x f forallp),
  from dominates_p.and_intro h5 (λ_, h6),
  show dominates_p σ (prop.subst_env (σ₁[f↦value.func f x R S e H σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)))
                   (spec.to_prop (spec.func f x R S)),
  from h3.symm ▸ h4.symm ▸ h7

lemma inlined_dominates_n_spec {σ σ₁: env} {P: prop} {Q: propctx} {f x: var} {R S: spec} {e: exp} {H: history}:
  (⊢ σ₁ : P) → (f ∉ σ₁) → (x ∉ σ₁) → (x ≠ f) → (σ ⊨ P.instantiated_p) → (σ f = value.func f x R S e H σ₁) →
  (⊢ (σ₁[f↦value.func f x R S e H σ₁]) : (P ⋀ f ≡ value.func f x R S e H σ₁ ⋀
                  prop.subst_env (σ₁[f↦value.func f x R S e H σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)))) →
  dominates_n σ (prop.subst_env (σ₁[f↦value.func f x R S e H σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)))
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
    from prop.subst_env.forallc_not_in this,

    show (prop.subst_env (σ₁[f↦vf]) (prop.func f x R (Q (term.app f x) ⋀ S)))
          = (term.unop unop.isFunc vf ⋀ prop.forallc x vf (prop.subst_env (σ₁[f↦vf]) forallp')),
    from h7 ▸ h8 ▸ h7 ▸ h6 ▸ h5 ▸ h3.symm ▸ h4
  ),

  have h4: spec.to_prop (spec.func f x R S) = (term.unop unop.isFunc f ⋀ prop.forallc x f forallp),
  by unfold spec.to_prop,

  have h5: dominates_n σ (term.unop unop.isFunc vf) (term.unop unop.isFunc f),
  from dominates_n.no_quantifiers (
    assume : σ ⊨ prop.instantiated_n (term.unop unop.isFunc vf),
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
    have prop.erased_n (prop.term (term.unop unop.isFunc f)) = vc.term (term.unop unop.isFunc f),
    by unfold prop.erased_n,
    have h8: σ ⊨ (prop.term (term.unop unop.isFunc f)).erased_n, from this.symm ▸ h74,
    have calls_n (prop.term (term.unop unop.isFunc f)) = ∅, from set.eq_empty_of_forall_not_mem (
      assume c': calltrigger,
      assume : c' ∈ calls_n (term.unop unop.isFunc f),
      show «false», from prop.has_call_n.term.inv this
    ),
    have (prop.term (term.unop unop.isFunc f)).instantiated_n = (prop.term (term.unop unop.isFunc f)).erased_n,
    from instantiated_n_eq_erased_n_without_calls this,
    show σ ⊨ (prop.term (term.unop unop.isFunc f)).instantiated_n, from this.symm ▸ h8
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

  have h6: dominates_n σ (prop.forallc x vf (prop.subst_env (σ₁[f↦vf]) forallp')) (prop.forallc x f forallp),
  from dominates_n.quantifier (
    assume v: value,

    have ¬ (x = f ∨ x ∈ σ₁), from not_or_distrib.mpr ⟨x_neq_f, x_not_in_σ₁⟩,
    have h61: x ∉ (σ₁[f↦vf]), from mt env.contains.inv this,
    have (∀y, y ∈ (σ₁[f↦vf]) → ((σ₁[f↦vf]) y = (σ.without x) y)),
    from env.remove_unimportant_equivalence env_equiv h61,
    have (∀y, y ∈ (σ₁[f↦vf]) → ((σ₁[f↦vf]) y = (σ.without x[x↦v]) y)),
    from env.equiv_of_not_contains this h61,
    have h7: dominates_n (σ.without x[x↦v]) (prop.subst_env (σ₁[f↦vf]) forallp') forallp',
    from dominates_n_equiv_subst this,
    have h82: dominates_n (σ.without x[x↦v]) (prop.implies (prop.post f x) (Q (term.app f x) ⋀ S.to_prop))
                                 (prop.implies (prop.post f x) S.to_prop),
    from dominates_n.or_intro dominates_n.self dominates_n.of_and_right,
    have h8: dominates_n (σ.without x[x↦v]) forallp' forallp,
    from dominates_n.same_left (λ_, h82),
    show dominates_n (σ.without x[x↦v]) (prop.subst_env (σ₁[f↦vf]) forallp') forallp,
    from dominates_n.trans h7 h8
  ),
  have h7: dominates_n σ (term.unop unop.isFunc vf ⋀ prop.forallc x vf (prop.subst_env (σ₁[f↦vf]) forallp'))
                       (term.unop unop.isFunc f ⋀ prop.forallc x f forallp),
  from dominates_n.and_intro h5 (λ_, h6),
  show dominates_n σ (prop.subst_env (σ₁[f↦value.func f x R S e H σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)))
                   (spec.to_prop (spec.func f x R S)),
  from h3.symm ▸ h4.symm ▸ h7

theorem preservation {s: stack} {Q: propctx}:
   (⊢ₛ s : Q) → ∀s', (s ⟶ s') →
   ∃Q', (⊢ₛ s' : Q') ∧ (∀σ' t, dominates_n σ' (Q' t) (Q t)) ∧ (∀v: value, FV (Q v) ⊆ FV (Q' v)) :=
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
            gx ∈ FV R₂.to_prop.instantiated_p ∧
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
                  have x ∈ FV R₂.to_prop.instantiated_p,
                  from this.symm ▸ ha2.right.right.right.right.right.right.left,
                  have x ∈ FV R₂.to_prop,
                  from free_of_instantiated_p_free this,
                  have free_in_prop x (spec.func g gx R₂ S₂ ⋀ R₂), from free_in_prop.and₂ this,
                  show x ∈ FV (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from free_in_prop.and₂ this
                )
              ),

              have FV P₃ = FV (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from eq.trans hb4 hb5.symm,
              show FV (P₃ ⋀ ↑R₂) = FV (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from eq.trans hb9 this
            ),
            show FV (↑R₂ ⋀ ↑H₂ ⋀ P₃) = FV (↑H₂ ⋀ Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), by calc
                  FV (↑R₂ ⋀ ↑H₂ ⋀ P₃) = FV ((↑H₂ ⋀ P₃) ⋀ ↑R₂) : free_in_prop.and_symm
                            ... = FV (↑H₂ ⋀ P₃ ⋀ ↑R₂) : free_in_prop.and_assoc.symm
                            ... = FV ((P₃ ⋀ ↑R₂) ⋀ ↑H₂) : free_in_prop.and_symm
                            ... = FV ((Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂) ⋀ ↑H₂) : free_in_prop.same_right ha8
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
                    have (σ g = value.func g gx R₂ S₂ e₁ H₂ σ₂), from valid_env.subst_of_eq_instantiated_p this,
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
              from free_in_prop.and_assoc,

              have haa2: FV (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                       = FV ((↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑R),
              from free_in_prop.and_symm,

              have haa3: FV ((↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑R)
                       = FV (((↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑ R),
              from free_in_prop.same_right haa1,

              have haa4: FV (((↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑R)
                       = FV (↑R ⋀ (↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from free_in_prop.and_symm,
              
              have haa5: FV (↑R ⋀ (↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                       = FV ((↑R ⋀ (↑H ⋀ P)) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from free_in_prop.and_assoc,
              
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

          have h10: ∀σ' t, dominates_n σ' ((↑H₂ ⋀ ↑P₃ ⋀ Q₃) t) (↑H₂ ⋀ (Q₂'⋀P₃') ⋀ Q₃ t), from (
            assume σ': env,
            assume t: term,
            have h11: (↑H₂ ⋀ ↑P₃ ⋀ Q₃) t = (↑H₂ ⋀ P₃ ⋀ Q₃ t), from propctx_apply_hpq,

            have dominates_n σ' (↑H₂ ⋀ P₃ ⋀ Q₃ t) (↑H₂ ⋀ (Q₂'⋀ P₃') ⋀ Q₃ t),
            from dominates_n.self,
            show dominates_n σ' ((↑H₂ ⋀ ↑P₃ ⋀ Q₃) t) (↑H₂ ⋀ (Q₂'⋀ P₃') ⋀ Q₃ t), from h11.symm ▸ this
          ),

          have h11: ∀v: value, FV (↑H₂ ⋀ (Q₂'⋀P₃') ⋀ Q₃ v) ⊆ FV ((↑H₂ ⋀ ↑P₃ ⋀ Q₃) v), from (
            assume v: value,
            have h11: (↑H₂ ⋀ ↑P₃ ⋀ Q₃) v = (↑H₂ ⋀ P₃ ⋀ Q₃ v), from propctx_apply_hpq,

            have FV (↑H₂ ⋀ (Q₂'⋀ P₃') ⋀ Q₃ v) ⊆ FV (↑H₂ ⋀ P₃ ⋀ Q₃ v),
            from set.subset.refl (FV (↑H₂ ⋀ P₃ ⋀ Q₃ v)),
            show FV (↑H₂ ⋀ (Q₂'⋀ P₃') ⋀ Q₃ v) ⊆ FV ((↑H₂ ⋀ ↑P₃ ⋀ Q₃) v), from h11.symm ▸ this
          ),

          have h12: ⊢ₛ ((R₂, H₂, σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂][gx↦vₓ], e₁) · [R, H, σ, letapp y = f[x] in e₂])
                    : H ⋀ P ⋀ propctx.exis y (prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⋀ Q),
          from stack.vcgen.cons h5 h6 σ_verified ha2.right.right.right.right.right.left ha5 fv_R R_valid
                                f_is_func x_is_vₓ h7 
                                ha2.right.right.right.right.right.right.right.right.right.left
                                h10 h11 h8 h9,

          have h13: ∀σ' t, dominates_n σ'
            ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call f x) ⋀ ↑(prop.post f x) ⋀ ↑(y ≡ term.app f x) ⋀ Q)) t)
            ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call f x) ⋀ ↑(prop.post f x) ⋀ ↑(y ≡ term.app f x) ⋀ Q)) t),
          from λσ' t, dominates_n.self,

          have h14: ∀v: value,
             (FV ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call f x) ⋀ ↑(prop.post f x) ⋀ ↑(y ≡ term.app f x) ⋀ Q)) v)
           ⊆ FV ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call f x) ⋀ ↑(prop.post f x) ⋀ ↑(y ≡ term.app f x) ⋀ Q)) v)),
          from λv, set.subset.refl
            (FV ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call f x) ⋀ ↑(prop.post f x) ⋀ ↑(y ≡ term.app f x) ⋀ Q)) v)),
          exists.intro (H ⋀ P ⋀ propctx.exis y (prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⋀ Q)) ⟨h12, ⟨h13, h14⟩⟩
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
                          σ'_verified σ''_verified fv_R' R'_valid g_is_func x_is_v cont e'_verified Q₂'_dom Q₂'_fv
                          pre_vc steps ih {
      assume s''',
      assume s_steps: ((s' · [R', H, σ, letapp y = g[x] in e]) ⟶ s'''),
      cases s_steps,
      case step.ctx s'' s'_steps { from
        have (∃ (Q' : propctx), (⊢ₛ s'' : Q') ∧ (∀σ' t, dominates_n σ' (Q' t) (Q₂' t)) ∧
                                                (∀v: value, FV (Q₂' v) ⊆ FV (Q' v))),
        from ih s'' s'_steps,
        let ⟨Q', ⟨h1, ⟨h2, h3⟩⟩⟩ := this in
        have new_steps: ((R, H', σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ], e') ⟶* s''),
        from trans_step.trans steps s'_steps,

        have h4: ∀ (σ' : env) (t : term), dominates_n σ' (Q' t) (↑H' ⋀ P'' ⋀ Q₂ t), from (
          assume σ'': env,
          assume t: term,
          have h4: dominates_n σ'' (Q' t) (Q₂' t), from h2 σ'' t,
          have h5: dominates_n σ'' (Q₂' t) (↑H' ⋀ P'' ⋀ Q₂ t), from Q₂'_dom σ'' t,
          show dominates_n σ'' (Q' t) (↑H' ⋀ P'' ⋀ Q₂ t), from dominates_n.trans h4 h5
        ),
        have h5: ∀v: value, (FV (↑H' ⋀ P'' ⋀ Q₂ v) ⊆ FV (Q' v)), from (
          assume v: value,
          have h7: FV (Q₂' v) ⊆ FV (Q' v), from h3 v,
          have h8: FV (↑H' ⋀ P'' ⋀ Q₂ v) ⊆ FV (Q₂' v), from Q₂'_fv v,
          show FV (↑H' ⋀ P'' ⋀ Q₂ v) ⊆ FV (Q' v), from set.subset.trans h8 h7
        ),
        have h6: ⊢ₛ (s'' · [R', H, σ, letapp y = g[x] in e])
                 : H ⋀ P ⋀ propctx.exis y (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃),
        from stack.vcgen.cons h1 y_not_in_σ σ_verified σ'_verified σ''_verified fv_R' R'_valid
                              g_is_func x_is_v cont e'_verified h4 h5 pre_vc new_steps,

        have h7: ∀σ'' t, dominates_n σ''
          ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call g x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) t)
          ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call g x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) t),
        from λσ'' t, dominates_n.self,
        have h8: ∀v: value,
           FV ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call g x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) v)
         ⊆ FV ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call g x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) v),
        from λv, set.subset.refl
          (FV ((↑H ⋀ ↑P ⋀ propctx.exis y (↑(prop.call g x) ⋀ ↑(prop.post g x) ⋀ ↑(y ≡ term.app g x) ⋀ Q₃)) v)),
        exists.intro (H ⋀ P ⋀ propctx.exis y (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃)) ⟨h6, ⟨h7, h8⟩⟩
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

              have dominates_n σ₁ (Q₂' vy₁) (H'⋀ P'' ⋀ Q₂ vy₁), from Q₂'_dom σ₁ vy₁,

              have h55: σ₁ ⊨ (↑H'⋀ P'' ⋀ Q₂ vy₁).instantiated_n,
              from dominates_n.elim this h54,

              have h56: FV (↑H'⋀ P'' ⋀ Q₂ vy₁) ⊆ FV (Q₂' vy₁), from Q₂'_fv vy₁,

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
            have h35a: σ₁ f = (value.func f fx R S e' H' σ'),
            from eq.trans (env_equiv3 f f_in_σ'').symm f_is_vf,
            have h35: term.subst_env σ₁ f = value.func f fx R S e' H' σ',
            from (term.subst_env.var.right (value.func f fx R S e' H' σ')).mp h35a,
            have f_in_σ₁: f ∈ σ₁,
            from env.contains_apply_equiv.right.mp (exists.intro (value.func f fx R S e' H' σ') h35a),

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
              from Q₂'_dom σ₁ (term.app f fx),

              show σ₁ ⊨ (↑H'⋀ P'' ⋀ Q₂ (term.app f fx)).instantiated_n,
              from dominates_n.elim this h43
            ),

            have ∃Q', (⊢ (σ'[f↦value.func f fx R S e' H' σ']) : Q') ∧ ∀σ', (dominates_n σ' P'' Q'),
            from env_dominates_n_rest σ''_verified,

            let ⟨Q', h90⟩ := this in
            
            have ∃Q₁ Q₂ Q₃,
              f ∉ σ' ∧
              f ∉ σ' ∧
              fx ∉ σ' ∧
              f ≠ fx ∧
              (⊢ σ' : Q₁) ∧
              (⊢ σ' : Q₂) ∧
              fx ∈ FV R.to_prop.instantiated_p ∧
              FV R.to_prop ⊆ FV Q₂ ∪ { f, fx } ∧
              FV S.to_prop ⊆ FV Q₂ ∪ { f, fx } ∧
              (H' ⋀ Q₂ ⋀ spec.func f fx R S ⋀ R ⊢ e' : Q₃) ∧
              ⟪prop.implies (H' ⋀ Q₂ ⋀ spec.func f fx R S ⋀ R ⋀ Q₃ (term.app f fx)) S⟫ ∧
              (Q' = (Q₁ ⋀
                  ((f ≡ (value.func f fx R S e' H' σ')) ⋀
                  prop.subst_env (σ'[f↦value.func f fx R S e' H' σ'])
                  (prop.func f fx R (Q₃ (term.app f fx) ⋀ S))))),
            from env.vcgen.func.inv h90.left,
            let ⟨QQ₁, QQ₂, QQ₃, ⟨f_not_in_σ', ⟨_, ⟨fx_not_in_σ', ⟨f_neq_fx, ⟨σ'_veri_QQ₁, ⟨σ'_veri_QQ₂, ⟨fx_in_R,
                                ⟨fv_R, ⟨fv_S, ⟨e'_verified_QQ₃, ⟨func_vc, Q'_is⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ := this in
            
            have h91a: QQ₁ = QQ₂, from env.vcgen.inj σ'_veri_QQ₁ QQ₂ σ'_veri_QQ₂,
            have h91b: QQ₁ = P', from env.vcgen.inj σ'_veri_QQ₁ P' σ'_verified,
            have h91c: QQ₂ = P', from eq.trans h91a.symm h91b,

            have H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⊢ e' : QQ₃, from h91c ▸ e'_verified_QQ₃,
            have h91d: QQ₃ = Q₂, from exp.vcgen.inj this Q₂ e'_verified,

            have h37: closed_subst (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]) (Q₂ (term.app f fx)), from (
              assume z: var,
              assume : z ∈ FV (Q₂ (term.app f fx)),
              have z ∈ FV (term.app f fx) ∨ z ∈ FV (↑H' ⋀ P' ⋀ ↑(spec.func ↑f fx R S) ⋀ ↑R),
              from exp.post_free e'_verified (term.app f fx) this,
              or.elim this (
                assume : z ∈ FV (term.app f fx),
                or.elim (free_in_term.app.inv this) (
                  assume : free_in_term z f,
                  have z = f, from free_in_term.var.inv this,
                  have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from this.symm ▸ env.contains.same,
                  show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
                ) (
                  assume : free_in_term z fx,
                  have z = fx, from free_in_term.var.inv this,
                  show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from this.symm ▸ env.contains.same
                )
              ) (
                assume : z ∈ FV (↑H' ⋀ P' ⋀ ↑(spec.func ↑f fx R S) ⋀ ↑R),
                or.elim (free_in_prop.and.inv this) (
                  assume : free_in_prop z H',
                  show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from absurd this (call_history_closed H' z)
                ) (
                  assume : z ∈ FV (P' ⋀ ↑(spec.func ↑f fx R S) ⋀ ↑R),
                  or.elim (free_in_prop.and.inv this) (
                    assume : z ∈ FV P',
                    have z ∈ σ'.dom, from (free_iff_contains σ'_verified).symm ▸ this,
                    have z ∈ σ', from this,
                    have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from env.contains.rest this,
                    show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
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
                        have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from this.symm ▸ env.contains.same,
                        show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
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
                            have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from env.contains.rest this,
                            show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
                          ) (
                            assume : z ∈ { f, fx },
                            or.elim (set.two_elems_mem this) (
                              assume : z = f,
                              have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from this.symm ▸ env.contains.same,
                              show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
                            ) (
                              assume : z = fx,
                              show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from absurd this z_neq_fx
                            )
                          )
                        ) (
                          assume : z ∈ FV S.to_prop,
                          have z ∈ FV P' ∪ { f, fx }, from h91c ▸ set.mem_of_subset_of_mem fv_S this,
                          or.elim (set.mem_or_mem_of_mem_union this) (
                            assume : z ∈ FV P',
                            have z ∈ σ'.dom, from (free_iff_contains σ'_verified).symm ▸ this,
                            have z ∈ σ', from this,
                            have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from env.contains.rest this,
                            show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
                          ) (
                            assume : z ∈ { f, fx },
                            or.elim (set.two_elems_mem this) (
                              assume : z = f,
                              have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from this.symm ▸ env.contains.same,
                              show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
                            ) (
                              assume : z = fx,
                              show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from absurd this z_neq_fx
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
                        have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from env.contains.rest this,
                        show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
                      ) (
                        assume : z ∈ { f, fx },
                        or.elim (set.two_elems_mem this) (
                          assume : z = f,
                          have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from this.symm ▸ env.contains.same,
                          show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
                        ) (
                          assume : z = fx,
                          show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from this.symm ▸ env.contains.same
                        )
                      )
                    )
                  )
                )
              )
            ),
            have h37a: closed_subst σ₁ ↑H', from (
              assume z: var,
              assume : z ∈ FV ↑H',
              show z ∈ σ₁.dom, from absurd this (call_history_closed H' z)
            ),
            have h37b: closed_subst σ₁ P'', from (
              assume z: var,
              assume : z ∈ FV P'',
              have z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]).dom,
              from (free_iff_contains σ''_verified).symm ▸ this,
              show z ∈ σ₁.dom, from set.mem_of_subset_of_mem (env.dom_subset_of_equivalent_env env_equiv3) this
            ),
            have h37c: closed_subst σ₁ (Q₂ (term.app f fx)), from (
              assume z: var,
              assume : z ∈ FV (Q₂ (term.app f fx)),
              have z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from h37 this,
              have z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]).dom, from this,
              show z ∈ σ₁.dom, from set.mem_of_subset_of_mem (env.dom_subset_of_equivalent_env env_equiv3) this
            ),
            have closed_subst σ₁ (P'' ⋀ Q₂ (term.app f fx)),
            from prop.closed_subst.and h37b h37c,
            have closed_subst σ₁ (↑H'⋀ P'' ⋀ Q₂ (term.app f fx)),
            from prop.closed_subst.and h37a this,
            have closed_subst σ₁ (↑H'⋀ P'' ⋀ Q₂ (term.app f fx)).instantiated_p,
            from instantiated_p_closed_subst_of_closed this,
            have σ₁ ⊨ (↑H'⋀ P'' ⋀ Q₂ (term.app f fx)).instantiated_p,
            from valid_env.instantiated_p_of_instantiated_n this h36,
            have σ₁ ⊨ (P'' ⋀ Q₂ (term.app f fx)).instantiated_p,
            from (valid_env.and.elim (valid_env.instantiated_p_and_elim this)).right,
            have σ₁ ⊨ (Q₂ (term.app f fx)).instantiated_p,
            from (valid_env.and.elim (valid_env.instantiated_p_and_elim this)).right,
            have h38: ⊨ vc.subst_env σ₁ (Q₂ (term.app f fx)).instantiated_p, from this,

            have closed_subst (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]) (Q₂ (term.app f fx)).instantiated_p,
            from instantiated_p_closed_subst_of_closed h37,
            have (vc.subst_env (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]) (Q₂ (term.app f fx)).instantiated_p
                = vc.subst_env σ₁ (Q₂ (term.app f fx)).instantiated_p),
            from vc.subst_env_equivalent_env env_equiv3 this,
            have h97d: ⊨ vc.subst_env (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]) (Q₂ (term.app f fx)).instantiated_p,
            from this.symm ▸ h38,

            have h98a: σ₁ ⊨ (prop.implies (↑H' ⋀ P' ⋀ ↑(spec.func f fx R S) ⋀ ↑R ⋀ Q₂ (term.app f fx))
                                           S).instantiated_n,
            from h91c ▸ h91d ▸ func_vc σ₁,

            have R = R'₁, from pre_preserved steps,
            have σ₁ ⊨ R.to_prop.instantiated_n, from this.symm ▸ R'₁_valid,
            have h98b: σ₁ ⊨ ((↑H'⋀ P'' ⋀ Q₂ (term.app f fx)) ⋀ ↑R).instantiated_n,
            from valid_env.instantiated_n_and (valid_env.and h36 this),

            have dominates_n σ₁ ((↑H'⋀ P'' ⋀ Q₂ (term.app f fx)) ⋀ ↑R)
                                (↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)), from (
              have hc1: dominates_n σ₁ ((↑H'⋀ P'' ⋀ Q₂ (term.app f fx)) ⋀ ↑R)
                                       (↑H'⋀ (P'' ⋀ Q₂ (term.app f fx)) ⋀ ↑R),
              from dominates_n.and_assoc.symm,

              have hc2: dominates_n σ₁ (↑H'⋀ (P'' ⋀ Q₂ (term.app f fx)) ⋀ ↑R)
                                       (↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)),
              from dominates_n.same_left (
                assume _,

                have hc1: dominates_n σ₁ ((P'' ⋀ Q₂ (term.app f fx)) ⋀ ↑R)
                                         (↑R ⋀ P'' ⋀ Q₂ (term.app f fx)),
                from dominates_n.and_symm,

                have hc2: dominates_n σ₁ (↑R ⋀ P'' ⋀ Q₂ (term.app f fx))
                                         (↑R ⋀ Q₂ (term.app f fx) ⋀ P' ⋀ spec.func f fx R S),
                from dominates_n.same_left (
                  assume _,
                  have hc1: dominates_n σ₁ (P'' ⋀ Q₂ (term.app f fx))
                                           (Q₂ (term.app f fx) ⋀ P''),
                  from dominates_n.and_symm,

                  have hc2: dominates_n σ₁ (Q₂ (term.app f fx) ⋀ P'')
                                           (Q₂ (term.app f fx) ⋀ P' ⋀ spec.func f fx R S),
                  from dominates_n.same_left (
                    assume _,

                    have hc1: dominates_n σ₁ P'' Q',
                    from h90.right σ₁,

                    have hc2: dominates_n σ₁ Q'
                                             (P' ⋀ f ≡ (value.func f fx R S e' H' σ') ⋀
                                              prop.subst_env (σ'[f↦value.func f fx R S e' H' σ'])
                                                             (prop.func f fx R (Q₂ (term.app f fx) ⋀ S))),
                    from h91b ▸ h91d ▸ (@eq.subst prop (λa, dominates_n σ₁ Q' a) Q' 
                        (QQ₁ ⋀ f ≡ (value.func f fx R S e' H' σ') ⋀
                                                    prop.subst_env (σ'[f↦value.func f fx R S e' H' σ'])
                                                                  (prop.func f fx R (QQ₃ (term.app f fx) ⋀ S)))
                        Q'_is (@dominates_n.self Q' σ₁)),

                    have hc3: dominates_n σ₁ (P' ⋀ f ≡ (value.func f fx R S e' H' σ') ⋀
                                              prop.subst_env (σ'[f↦value.func f fx R S e' H' σ'])
                                                        (prop.func f fx R (Q₂ (term.app f fx) ⋀ S)))
                                             (P' ⋀ spec.func f fx R S),
                    from dominates_n.same_left (λP_valid, dominates_n.left_elim (
                      assume _,
                      have ⊢ (σ'[f↦value.func f fx R S e' H' σ']) : (P' ⋀ f ≡ value.func f fx R S e' H' σ' ⋀
                              prop.subst_env (σ'[f↦value.func f fx R S e' H' σ'])
                                            (prop.func f fx R (Q₂ (term.app f fx) ⋀ S))),
                      from h91b ▸ h91d ▸ Q'_is ▸ h90.left,

                      show dominates_n σ₁ (prop.subst_env (σ'[f↦value.func f fx R S e' H' σ'])
                                                          (prop.func f fx R (Q₂ (term.app f fx) ⋀ S)))
                                          (spec.func f fx R S),
                      from inlined_dominates_n_spec σ'_verified f_not_in_σ' fx_not_in_σ' f_neq_fx.symm
                           P_valid h35a this
                    )),

                    show dominates_n σ₁ P'' (P' ⋀ spec.func f fx R S),
                    from dominates_n.trans hc1 (dominates_n.trans hc2 hc3)
                  ),

                  show dominates_n σ₁ (P'' ⋀ Q₂ (term.app f fx))
                                      (Q₂ (term.app f fx) ⋀ P' ⋀ spec.func f fx R S),
                  from dominates_n.trans hc1 hc2
                ),

                have hc3: dominates_n σ₁ (R ⋀ Q₂ (term.app f fx) ⋀ P' ⋀ spec.func f fx R S)
                                         ((R ⋀ Q₂ (term.app f fx)) ⋀ P' ⋀ spec.func f fx R S),
                from dominates_n.and_assoc,

                have hc4: dominates_n σ₁ ((R ⋀ Q₂ (term.app f fx)) ⋀ P' ⋀ spec.func f fx R S)
                                         ((P' ⋀ spec.func f fx R S) ⋀ R ⋀ Q₂ (term.app f fx)),
                from dominates_n.and_symm,

                have hc5: dominates_n σ₁ ((P' ⋀ spec.func f fx R S) ⋀ R ⋀ Q₂ (term.app f fx))
                                         (P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)),
                from dominates_n.and_assoc.symm,

                show dominates_n σ₁ ((P'' ⋀ Q₂ (term.app f fx)) ⋀ ↑R)
                                    (P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)),
                from dominates_n.trans hc1 (dominates_n.trans hc2 (dominates_n.trans hc3 (dominates_n.trans hc4 hc5)))
              ),

              show dominates_n σ₁ ((↑H'⋀ P'' ⋀ Q₂ (term.app f fx)) ⋀ ↑R)
                                  (↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)),
              from dominates_n.trans hc1 hc2
            ),
            have h98b: σ₁ ⊨ (↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)).instantiated_n,
            from dominates_n.elim this h98b,

            have h98c: closed_subst (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ])
                              (prop.implies (↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)) S),
            from (
              assume z: var,
              assume : z ∈ FV (prop.implies (↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)) S),
              or.elim (free_in_prop.implies.inv this) (
                assume : z ∈ FV (↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)),
                or.elim (free_in_prop.and.inv this) (
                  assume : free_in_prop z H',
                  show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from absurd this (call_history_closed H' z)
                ) (
                  assume : z ∈ FV (P' ⋀ ↑(spec.func ↑f fx R S) ⋀ ↑R ⋀ Q₂ (term.app f fx)),
                  or.elim (free_in_prop.and.inv this) (
                    assume : z ∈ FV P',
                    have z ∈ σ'.dom, from (free_iff_contains σ'_verified).symm ▸ this,
                    have z ∈ σ', from this,
                    have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from env.contains.rest this,
                    show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
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
                        have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from this.symm ▸ env.contains.same,
                        show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
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
                            have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from env.contains.rest this,
                            show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
                          ) (
                            assume : z ∈ { f, fx },
                            or.elim (set.two_elems_mem this) (
                              assume : z = f,
                              have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from this.symm ▸ env.contains.same,
                              show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
                            ) (
                              assume : z = fx,
                              show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from absurd this z_neq_fx
                            )
                          )
                        ) (
                          assume : z ∈ FV S.to_prop,
                          have z ∈ FV P' ∪ { f, fx }, from h91c ▸ set.mem_of_subset_of_mem fv_S this,
                          or.elim (set.mem_or_mem_of_mem_union this) (
                            assume : z ∈ FV P',
                            have z ∈ σ'.dom, from (free_iff_contains σ'_verified).symm ▸ this,
                            have z ∈ σ', from this,
                            have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from env.contains.rest this,
                            show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
                          ) (
                            assume : z ∈ { f, fx },
                            or.elim (set.two_elems_mem this) (
                              assume : z = f,
                              have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from this.symm ▸ env.contains.same,
                              show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
                            ) (
                              assume : z = fx,
                              show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from absurd this z_neq_fx
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
                          have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from env.contains.rest this,
                          show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
                        ) (
                          assume : z ∈ { f, fx },
                          or.elim (set.two_elems_mem this) (
                            assume : z = f,
                            have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from this.symm ▸ env.contains.same,
                            show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
                          ) (
                            assume : z = fx,
                            show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from this.symm ▸ env.contains.same
                          )
                        )
                      ) (
                        assume : z ∈ FV (Q₂ (term.app f fx)),
                        show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from h37 this
                      )
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
                  have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from env.contains.rest this,
                  show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
                ) (
                  assume : z ∈ { f, fx },
                  or.elim (set.two_elems_mem this) (
                    assume : z = f,
                    have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from this.symm ▸ env.contains.same,
                    show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
                  ) (
                    assume : z = fx,
                    show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from this.symm ▸ env.contains.same
                  )
                )
              )
            ),
            have closed_subst σ₁ (prop.implies (↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)) S),
            from (
              assume z: var,
              assume : z ∈ FV (prop.implies (↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)) S),
              have z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from h98c this,
              have z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]).dom, from this,
              show z ∈ σ₁.dom, from set.mem_of_subset_of_mem (env.dom_subset_of_equivalent_env env_equiv3) this
            ),
            have closed_subst σ₁ (prop.implies (↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx))
                                                S).instantiated_p,
            from instantiated_p_closed_subst_of_closed this,

            have σ₁ ⊨ (prop.implies (↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)) S).instantiated_p,
            from valid_env.instantiated_p_of_instantiated_n this h98a,
            have σ₁ ⊨ ((↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)).not ⋁ S.to_prop).instantiated_p,
            from this,
            have h98d: σ₁ ⊨ ((↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)).not.instantiated_p
                      ⋁ S.to_prop.instantiated_p),
            from valid_env.instantiated_p_or_elim this,
            have (↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)).not.instantiated_p
               = (↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)).instantiated_n.not,
            from not_dist_instantiated_p,
            have σ₁ ⊨ ((↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)).instantiated_n.not
                        ⋁ S.to_prop.instantiated_p),
            from this ▸ h98d,
            have σ₁ ⊨ vc.implies (↑H' ⋀ P' ⋀ spec.func f fx R S ⋀ R ⋀ Q₂ (term.app f fx)).instantiated_n
                                  S.to_prop.instantiated_p,
            from this,
            have σ₁ ⊨ S.to_prop.instantiated_p, from valid_env.mp this h98b,
            have h98z: ⊨ vc.subst_env σ₁ S.to_prop.instantiated_p,
            from this,

            have closed_subst (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]) S.to_prop, from (
              assume z: var,
              assume : z ∈ FV S.to_prop,
              have z ∈ FV P' ∪ { f, fx }, from h91c ▸ set.mem_of_subset_of_mem fv_S this,
              or.elim (set.mem_or_mem_of_mem_union this) (
                assume : z ∈ FV P',
                have z ∈ σ'.dom, from (free_iff_contains σ'_verified).symm ▸ this,
                have z ∈ σ', from this,
                have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from env.contains.rest this,
                show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
              ) (
                assume : z ∈ { f, fx },
                or.elim (set.two_elems_mem this) (
                  assume : z = f,
                  have z ∈ (σ'[f↦value.func f fx R S e' H' σ']), from this.symm ▸ env.contains.same,
                  show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from env.contains.rest this
                ) (
                  assume : z = fx,
                  show z ∈ (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]), from this.symm ▸ env.contains.same
                )
              )
            ),
            have closed_subst (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]) S.to_prop.instantiated_p,
            from instantiated_p_closed_subst_of_closed this,
            have (vc.subst_env (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]) S.to_prop.instantiated_p
                  = vc.subst_env σ₁ S.to_prop.instantiated_p),
            from vc.subst_env_equivalent_env env_equiv3 this,
            have h98d: ⊨ vc.subst_env (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ]) S.to_prop.instantiated_p,
            from this.symm ▸ h98z,
            have ⊨ vc.subst_env (σ'[f↦value.func f fx R S e' H' σ'][fx↦vₓ])
                                (vc.and (Q₂ (term.app f fx)).instantiated_p S.to_prop.instantiated_p),
            from valid_env.and h97d h98d,
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
        have h15: ∀t,
          FV ((↑H ⋀ ↑P ⋀ propctx.exis y
                       (↑(prop.call ↑g ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t)
        ⊆ FV ((↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ ↑(P ⋀ P₃) ⋀ Q₃) t), from (
          assume t: term,

          have h18: FV (↑H ⋀ P ⋀ prop.exis y (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t))
                  ⊆ σ.dom ∪ FV (Q₃ t),
          from (
            assume z: var,
            assume : z ∈ FV (↑H ⋀ P ⋀ prop.exis y (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t)),
            or.elim (free_in_prop.and.inv this) (
              assume : z ∈ FV ↑H,
              show z ∈ σ.dom ∪ FV (Q₃ t), from absurd this (call_history_closed H z)
            ) (
              assume : z ∈ FV (P ⋀ prop.exis y (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t)),
              or.elim (free_in_prop.and.inv this) (
                assume h10: z ∈ FV P,
                have σ.dom = FV P, from free_iff_contains σ_verified,
                have z ∈ σ.dom, from this.symm ▸ h10,
                show z ∈ σ.dom ∪ FV (Q₃ t), from set.mem_union_left (FV (Q₃ t)) this
              ) (
                assume : z ∈ FV (prop.exis y (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t)),
                have z_neq_y: z ≠ y, from (free_in_prop.exis.inv this).left,
                have z ∈ FV (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t),
                from (free_in_prop.exis.inv this).right,
                or.elim (free_in_prop.and.inv this) (
                  assume : z ∈ FV (prop.call g x),
                  or.elim (free_in_prop.call.inv this) (
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
            )
          ),

          have h19: σ.dom ∪ FV (Q₃ t) ⊆ FV ((↑H ⋀ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t),
          from (
            assume z: var,
            assume : z ∈ σ.dom ∪ FV (Q₃ t),
            or.elim (set.mem_or_mem_of_mem_union this) (
              assume h10: z ∈ σ.dom,
              have σ.dom = FV P, from free_iff_contains σ_verified,
              have z ∈ FV P, from this ▸ h10,
              have z ∈ FV (P ⋀ P₃), from free_in_prop.and₁ this,
              have z ∈ FV ((P ⋀ P₃) ⋀ Q₃ t), from free_in_prop.and₁ this,
              show z ∈ FV ((↑H ⋀ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t),
              from free_in_prop.and₂ this
            ) (
              assume : z ∈ FV (Q₃ t),
              have z ∈ FV ((P ⋀ P₃) ⋀ Q₃ t), from free_in_prop.and₂ this,
              show z ∈ FV ((↑H ⋀ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t),
              from free_in_prop.and₂ this
            )
          ),

          have h20: FV (↑H ⋀ P ⋀ prop.exis y (prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⋀ Q₃ t))
                  ⊆ FV ((↑H ⋀ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t),
          from set.subset.trans h18 h19,

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

          have h21: FV (↑H ⋀ P⋀ (propctx.exis y
                        (↑(prop.call ↑g ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t)
                  ⊆ FV ((↑H ⋀ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t),
          from this.symm ▸ h20,

          have ((↑H ⋀ ↑P⋀ propctx.exis y
                          (↑(prop.call ↑g ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t)
             = (↑H ⋀ P⋀ (propctx.exis y
                          (↑(prop.call ↑g ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t),
          from propctx_apply_hpq,

          have h22: FV ((↑H ⋀ ↑P⋀ propctx.exis y
                               (↑(prop.call ↑g ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t) 
                  ⊆ FV ((↑H ⋀ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t),
          from this.symm ▸ h21,

          have ((↑(↑H ⋀ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) ⋀ ↑(P ⋀ P₃) ⋀ Q₃) t)
             = ((↑H ⋀ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) ⋀ (P ⋀ P₃) ⋀ Q₃ t),
          from propctx_apply_hpq,

          have h23: FV ((↑H ⋀ ↑P ⋀ propctx.exis y
                             (↑(prop.call ↑g ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t)
                  ⊆ FV ((↑(↑H ⋀ (prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁)) ⋀ ↑(P ⋀ P₃) ⋀ Q₃) t),
          from this.symm ▸ h22,

          have calls_to_prop (H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁)
             = (calls_to_prop H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁),
          by unfold calls_to_prop,
          have ↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) = (↑H ⋀ prop.call (value.func f₁ x₁ R₁ S₁ e₁ H₂ σ₂) vx₁),
          from this,

          show FV ((↑H ⋀ ↑P⋀ propctx.exis y
                       (↑(prop.call ↑g ↑x) ⋀ ↑(prop.post ↑g ↑x) ⋀ ↑(↑y ≡ term.app ↑g ↑x) ⋀ Q₃)) t) 
             ⊆ FV ((↑(H·call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ ↑(P ⋀ P₃) ⋀ Q₃) t),
          from this.symm ▸ h23
        ),

        exists.intro (↑(H · call f₁ x₁ R₁ S₁ e₁ H₂ σ₂ vx₁) ⋀ ↑(P ⋀ P₃) ⋀ Q₃) ⟨h13, ⟨h14, λv, h15 v⟩⟩
      }
    }
  end
