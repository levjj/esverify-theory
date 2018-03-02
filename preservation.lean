import .syntax .notations .logic .evaluation .vcgen .bindings

lemma no_calls_in_spec {f: term} {x: var} {R S: spec}: calls_p (spec.func f x R S) = ∅ :=
  set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_p (spec.func f x R S),
    or.elim (prop.has_call_p.and.inv this) (
      assume : c ∈ calls_p (term.unop unop.isFunc f),
      show «false», from prop.has_call_p.term.inv this
    ) (
      assume h2,
      show «false», from prop.has_call_p.forallc.inv h2
    )
  )

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

lemma dominates_self: ∀ {P: prop} {σ: env}, dominates σ P P
| P σ :=
  have h_impl: σ ⊨ vc.implies P.instantiated_p P.instantiated_p, from valid_env.mpr id,
  have h_calls: calls_p_subst σ P ⊆ calls_p_subst σ P, from set.subset.refl (calls_p_subst σ P),
  have h_quantifiers_p:
    (∀(t': term) (x: var) (Q₁: prop) (h: callquantifier.mk t' x Q₁ ∈ quantifiers_p P),
                          have Q₁.size < P.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers_p P ∧
                          (∀v: value, dominates' Q₁ Q₂ (σ[x↦v]))), from (
    assume (t₁: term) (x:var) (Q₁: prop),
    assume h: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p P,
    have Q₁.size < P.size, from quantifiers_smaller_than_prop.left h,
    have (∀v: value, dominates' Q₁ Q₁ (σ[x↦v])), from (
      assume v: value,
      dominates_self
    ),
    exists.intro t₁ (exists.intro Q₁ ⟨h, this⟩)
  ),
  show dominates σ P P, from dominates_of h_impl h_calls h_quantifiers_p

lemma dominates_and_left {P P' Q: prop} {σ: env}:
      dominates σ P' P → dominates σ (P' ⋀ Q) (P ⋀ Q) :=
  assume h1: dominates σ P' P,
  show dominates σ (P' ⋀ Q) (P ⋀ Q), from dominates_of_pre (
    assume h2: σ ⊨ (P' ⋀ Q).instantiated_p,

    have σ ⊨ vc.implies (P' ⋀ Q).instantiated_p (P ⋀ Q).instantiated_p,
    from valid_env.strengthen_and_with_dominating_instantiations h1,
    have h_impl: σ ⊨ (P ⋀ Q).instantiated_p, from valid_env.mp this h2,

    have σ ⊨ P'.instantiated_p, from (valid_env.and.elim (valid_env.instantiated_p_and_elim h2)).left,

    have h3:
      (σ ⊨ P.instantiated_p) ∧
      (calls_p_subst σ P ⊆ calls_p_subst σ P') ∧
      (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers_p P),
                            have Q'.size < P.size, from quantifiers_smaller_than_prop.left h,
      ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers_p P' ∧
                            (∀v: value, dominates' Q' Q (σ[x↦v]))),
    from dominates.elim h1 this,

    have calls_p_subst σ P ⊆ calls_p_subst σ P', from h3.right.left,
    have h_calls: calls_p_subst σ (P ⋀ Q) ⊆ calls_p_subst σ (P' ⋀ Q), from same_calls_p_and_left this,
    have h_quantifiers_p:
      (∀(t': term) (x: var) (Q₁: prop) (h: callquantifier.mk t' x Q₁ ∈ quantifiers_p (P ⋀ Q)),
                            have Q₁.size < (P ⋀ Q).size, from quantifiers_smaller_than_prop.left h,
      ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers_p (P' ⋀ Q) ∧
                            (∀v: value, dominates' Q₁ Q₂ (σ[x↦v]))), from (

      assume (t₁: term) (x:var) (Q₁: prop),
      assume : callquantifier.mk t₁ x Q₁ ∈ quantifiers_p (P ⋀ Q),
      or.elim (prop.has_quantifier_p.and.inv this) (
        assume : callquantifier.mk t₁ x Q₁ ∈ quantifiers_p P,
        have ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers_p P' ∧
                            (∀v: value, dominates' Q₁ Q₂ (σ[x↦v])),
        from h3.right.right t₁ x Q₁ this,
        let ⟨t₂, Q₂, ⟨call_t₂_Q₂_in_P', Q₂_impl_Q₁⟩⟩ := this in
        have callquantifier.mk t₂ x Q₂ ∈ quantifiers_p (P' ⋀ Q), from prop.has_quantifier_p.and₁ call_t₂_Q₂_in_P',
        show ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers_p (P' ⋀ Q) ∧
                                    (∀v: value, dominates' Q₁ Q₂ (σ[x↦v])),
        from exists.intro t₂ (exists.intro Q₂ ⟨this, Q₂_impl_Q₁⟩)
      ) (
        assume : callquantifier.mk t₁ x Q₁ ∈ quantifiers_p Q,
        have h1: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p (P' ⋀ Q), from prop.has_quantifier_p.and₂ this,
        have h2: ∀v: value, dominates' Q₁ Q₁ (σ[x↦v]), from (
          assume v: value,
          show dominates' Q₁ Q₁ (σ[x↦v]), from dominates_self
        ),
        show ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers_p (P' ⋀ Q) ∧
                                    (∀v: value, dominates' Q₁ Q₂ (σ[x↦v])),
        from exists.intro t₁ (exists.intro Q₁ ⟨h1, h2⟩)
      )
    ),
    ⟨h_impl, ⟨h_calls, h_quantifiers_p⟩⟩
  )

lemma dominates_and_symm {P₁ P₂: prop} {σ: env}:
      dominates σ (P₁ ⋀ P₂) (P₂ ⋀ P₁) :=

  have h_impl: σ ⊨ vc.implies (P₁ ⋀ P₂).instantiated_p (P₂ ⋀ P₁).instantiated_p,
  from valid_env.mpr valid_env.and_symm_with_instantiations,

  have h1: calls_p_subst σ (P₁ ⋀ P₂) = (calltrigger.subst σ) '' calls_p (P₁ ⋀ P₂), by unfold calls_p_subst,
  have calls_p (P₁ ⋀ P₂) = calls_p (P₂ ⋀ P₁), from prop.has_call_p.and.symm,
  have h2: calls_p_subst σ (P₁ ⋀ P₂) = (calltrigger.subst σ) '' calls_p (P₂ ⋀ P₁),
  from this ▸ h1,
  have calls_p_subst σ (P₂ ⋀ P₁) = (calltrigger.subst σ) '' calls_p (P₂ ⋀ P₁), by unfold calls_p_subst,
  have calls_p_subst σ (P₂ ⋀ P₁) = calls_p_subst σ (P₁ ⋀ P₂), from eq.trans this h2.symm,
  have h_calls: calls_p_subst σ (P₂ ⋀ P₁) ⊆ calls_p_subst σ (P₁ ⋀ P₂), from set.subset_of_eq this,

  have h_quantifiers_p:
    (∀(t₁: term) (x: var) (Q₁: prop) (h: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p (P₂ ⋀ P₁)),
                          have Q₁.size < (P₂ ⋀ P₁).size, from quantifiers_smaller_than_prop.left h,
    ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers_p (P₁ ⋀ P₂) ∧
                          (∀v: value, dominates' Q₁ Q₂ (σ[x↦v]))), from (

    assume (t₁: term) (x:var) (Q₁: prop),
    assume t₁_Q₁_in_c: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p (P₂ ⋀ P₁),
    have quantifiers_p (P₂ ⋀ P₁) = quantifiers_p (P₁ ⋀ P₂), from prop.has_quantifier_p.and.symm,
    have t₁_Q₁_in: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p (P₁ ⋀ P₂), from this ▸ t₁_Q₁_in_c,
    have (∀v: value, dominates' Q₁ Q₁ (σ[x↦v])), from (
      assume v: value,
      dominates_self
    ),

    show ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers_p (P₁ ⋀ P₂) ∧
                                  (∀v: value, dominates' Q₁ Q₂ (σ[x↦v])),
    from exists.intro t₁ (exists.intro Q₁ ⟨t₁_Q₁_in, this⟩)
  ),

  show dominates σ (P₁ ⋀ P₂) (P₂ ⋀ P₁), from dominates_of h_impl h_calls h_quantifiers_p

lemma dominates_and_comm {P₁ P₂ P₃: prop} {σ: env}:
      dominates σ (P₁ ⋀ P₂ ⋀ P₃) ((P₁ ⋀ P₂) ⋀ P₃) :=

  have h_impl: σ ⊨ vc.implies (P₁ ⋀ P₂ ⋀ P₃).instantiated_p ((P₁ ⋀ P₂) ⋀ P₃).instantiated_p,
  from valid_env.mpr valid_env.and_comm_with_instantiations.mp,

  have h1: calls_p_subst σ (P₁ ⋀ P₂ ⋀ P₃) = (calltrigger.subst σ) '' calls_p (P₁ ⋀ P₂ ⋀ P₃), by unfold calls_p_subst,
  have calls_p (P₁ ⋀ P₂ ⋀ P₃) = calls_p ((P₁ ⋀ P₂) ⋀ P₃), from prop.has_call_p.and.comm,
  have h2: calls_p_subst σ (P₁ ⋀ P₂ ⋀ P₃) = (calltrigger.subst σ) '' calls_p ((P₁ ⋀ P₂) ⋀ P₃),
  from this ▸ h1,
  have calls_p_subst σ ((P₁ ⋀ P₂) ⋀ P₃) = (calltrigger.subst σ) '' calls_p ((P₁ ⋀ P₂) ⋀ P₃), by unfold calls_p_subst,
  have calls_p_subst σ ((P₁ ⋀ P₂) ⋀ P₃) = calls_p_subst σ (P₁ ⋀ P₂ ⋀ P₃), from eq.trans this h2.symm,
  have h_calls: calls_p_subst σ ((P₁ ⋀ P₂) ⋀ P₃) ⊆ calls_p_subst σ (P₁ ⋀ P₂ ⋀ P₃), from set.subset_of_eq this,

  have h_quantifiers_p:
    (∀(t₁: term) (x: var) (Q₁: prop) (h: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p ((P₁ ⋀ P₂) ⋀ P₃)),
                          have Q₁.size < ((P₁ ⋀ P₂) ⋀ P₃).size, from quantifiers_smaller_than_prop.left h,
    ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers_p (P₁ ⋀ P₂ ⋀ P₃) ∧
                          (∀v: value, dominates' Q₁ Q₂ (σ[x↦v]))), from (

    assume (t₁: term) (x:var) (Q₁: prop),
    assume t₁_Q₁_in_c: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p ((P₁ ⋀ P₂) ⋀ P₃),
    have quantifiers_p ((P₁ ⋀ P₂) ⋀ P₃) = quantifiers_p (P₁ ⋀ P₂ ⋀ P₃), from prop.has_quantifier_p.and.comm.symm,
    have t₁_Q₁_in: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p (P₁ ⋀ P₂ ⋀ P₃), from this ▸ t₁_Q₁_in_c,
    have (∀v: value, dominates' Q₁ Q₁ (σ[x↦v])), from (
      assume v: value,
      dominates_self
    ),

    show ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers_p (P₁ ⋀ P₂ ⋀ P₃) ∧
                                  (∀v: value, dominates' Q₁ Q₂ (σ[x↦v])),
    from exists.intro t₁ (exists.intro Q₁ ⟨t₁_Q₁_in, this⟩)
  ),

  show dominates σ (P₁ ⋀ P₂ ⋀ P₃) ((P₁ ⋀ P₂) ⋀ P₃), from dominates_of h_impl h_calls h_quantifiers_p

lemma dominates_and_rcomm {P₁ P₂ P₃: prop} {σ: env}:
      dominates σ ((P₁ ⋀ P₂) ⋀ P₃) (P₁ ⋀ P₂ ⋀ P₃) :=

  have h_impl: σ ⊨ vc.implies ((P₁ ⋀ P₂) ⋀ P₃).instantiated_p (P₁ ⋀ P₂ ⋀ P₃).instantiated_p,
  from valid_env.mpr valid_env.and_comm_with_instantiations.mpr,

  have h1: calls_p_subst σ (P₁ ⋀ P₂ ⋀ P₃) = (calltrigger.subst σ) '' calls_p (P₁ ⋀ P₂ ⋀ P₃), by unfold calls_p_subst,
  have calls_p (P₁ ⋀ P₂ ⋀ P₃) = calls_p ((P₁ ⋀ P₂) ⋀ P₃), from prop.has_call_p.and.comm,
  have h2: calls_p_subst σ (P₁ ⋀ P₂ ⋀ P₃) = (calltrigger.subst σ) '' calls_p ((P₁ ⋀ P₂) ⋀ P₃),
  from this ▸ h1,
  have calls_p_subst σ ((P₁ ⋀ P₂) ⋀ P₃) = (calltrigger.subst σ) '' calls_p ((P₁ ⋀ P₂) ⋀ P₃), by unfold calls_p_subst,
  have calls_p_subst σ ((P₁ ⋀ P₂) ⋀ P₃) = calls_p_subst σ (P₁ ⋀ P₂ ⋀ P₃), from eq.trans this h2.symm,
  have h_calls: calls_p_subst σ (P₁ ⋀ P₂ ⋀ P₃) ⊆ calls_p_subst σ ((P₁ ⋀ P₂) ⋀ P₃), from set.subset_of_eq this.symm,

  have h_quantifiers_p:
    (∀(t₁: term) (x: var) (Q₁: prop) (h: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p (P₁ ⋀ P₂ ⋀ P₃)),
                          have Q₁.size < (P₁ ⋀ P₂ ⋀ P₃).size, from quantifiers_smaller_than_prop.left h,
    ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers_p ((P₁ ⋀ P₂) ⋀ P₃) ∧
                          (∀v: value, dominates' Q₁ Q₂ (σ[x↦v]))), from (

    assume (t₁: term) (x:var) (Q₁: prop),
    assume t₁_Q₁_in_c: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p (P₁ ⋀ P₂ ⋀ P₃),
    have quantifiers_p (P₁ ⋀ P₂ ⋀ P₃) = quantifiers_p ((P₁ ⋀ P₂) ⋀ P₃), from prop.has_quantifier_p.and.comm,
    have t₁_Q₁_in: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p ((P₁ ⋀ P₂) ⋀ P₃), from this ▸ t₁_Q₁_in_c,
    have (∀v: value, dominates' Q₁ Q₁ (σ[x↦v])), from (
      assume v: value,
      dominates_self
    ),

    show ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers_p ((P₁ ⋀ P₂) ⋀ P₃) ∧
                                  (∀v: value, dominates' Q₁ Q₂ (σ[x↦v])),
    from exists.intro t₁ (exists.intro Q₁ ⟨t₁_Q₁_in, this⟩)
  ),

  show dominates σ ((P₁ ⋀ P₂) ⋀ P₃) (P₁ ⋀ P₂ ⋀ P₃), from dominates_of h_impl h_calls h_quantifiers_p

lemma dominates.trans: ∀ {P₁ P₂ P₃: prop} {σ: env},
      dominates σ P₁ P₂ → dominates σ P₂ P₃ → dominates σ P₁ P₃
| P₁ P₂ P₃ σ :=

  assume h1: dominates σ P₁ P₂,
  assume h2: dominates σ P₂ P₃,
  show dominates σ P₁ P₃, from dominates_of_pre (
    assume : σ ⊨ P₁.instantiated_p,

    have h3:
      ((σ ⊨ P₂.instantiated_p) ∧
      (calls_p_subst σ P₂ ⊆ calls_p_subst σ P₁) ∧
      (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers_p P₂),
                            have Q'.size < P₂.size, from quantifiers_smaller_than_prop.left h,
      ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers_p P₁ ∧
                            (∀v: value, dominates' Q' Q (σ[x↦v])))),
    from dominates.elim h1 this,

    have h4:
      ((σ ⊨ P₃.instantiated_p) ∧
      (calls_p_subst σ P₃ ⊆ calls_p_subst σ P₂) ∧
      (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers_p P₃),
                            have Q'.size < P₃.size, from quantifiers_smaller_than_prop.left h,
      ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers_p P₂ ∧
                            (∀v: value, dominates' Q' Q (σ[x↦v])))),
    from dominates.elim h2 h3.left,

    have h_impl: (σ ⊨ P₃.instantiated_p), from h4.left,

    have h_calls: calls_p_subst σ P₃ ⊆ calls_p_subst σ P₁, from set.subset.trans h4.right.left h3.right.left,

    have h_quantifiers_p:
      (∀(t₃: term) (x: var) (Q₃: prop) (h: callquantifier.mk t₃ x Q₃ ∈ quantifiers_p P₃),
                            have Q₃.size < P₃.size, from quantifiers_smaller_than_prop.left h,
      ∃(t₁: term) (Q₁: prop), callquantifier.mk t₁ x Q₁ ∈ quantifiers_p P₁ ∧
                            (∀v: value, dominates' Q₃ Q₁ (σ[x↦v]))), from (

      assume (t₃: term) (x:var) (Q₃: prop),
      assume h5: callquantifier.mk t₃ x Q₃ ∈ quantifiers_p P₃,
      have ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers_p P₂ ∧
                            (∀v: value, dominates' Q₃ Q₂ (σ[x↦v])),
      from h4.right.right t₃ x Q₃ h5,
      let ⟨t₂, Q₂, ⟨t₂_Q₂_in_P₂, Q₃_dom_Q₂⟩⟩ := this in
      have ∃(t₁: term) (Q₁: prop), callquantifier.mk t₁ x Q₁ ∈ quantifiers_p P₁ ∧
                            (∀v: value, dominates' Q₂ Q₁ (σ[x↦v])),
      from h3.right.right t₂ x Q₂ t₂_Q₂_in_P₂,
      let ⟨t₁, Q₁, ⟨t₁_Q₁_in_P₁, Q₂_dom_Q₁⟩⟩ := this in
      have Q₃_dom_Q₁: (∀v: value, dominates' Q₃ Q₁ (σ[x↦v])), from (
        assume v: value,
        have h6: dominates (σ[x↦v]) Q₁ Q₂, from Q₂_dom_Q₁ v,
        have h7: dominates (σ[x↦v]) Q₂ Q₃, from Q₃_dom_Q₂ v,
        have Q₁.size < P₁.size, from quantifiers_smaller_than_prop.left t₁_Q₁_in_P₁,
        show dominates (σ[x↦v]) Q₁ Q₃, from dominates.trans h6 h7
      ),

      show ∃(t₁: term) (Q₁: prop), callquantifier.mk t₁ x Q₁ ∈ quantifiers_p P₁ ∧
                                  (∀v: value, dominates' Q₃ Q₁ (σ[x↦v])),
      from exists.intro t₁ (exists.intro Q₁ ⟨t₁_Q₁_in_P₁, Q₃_dom_Q₁⟩)
    ),
    ⟨h_impl, ⟨h_calls, h_quantifiers_p⟩⟩
  )

lemma dominates_of_and₁ {P₁ P₂: prop} {σ: env}:
      dominates σ (P₁ ⋀ P₂) P₁ :=

  have h_impl: σ ⊨ vc.implies (P₁ ⋀ P₂).instantiated_p P₁.instantiated_p, from valid_env.mpr (
    assume : σ ⊨ (P₁ ⋀ P₂).instantiated_p,
    show σ ⊨ P₁.instantiated_p,
    from (valid_env.and.elim (valid_env.instantiated_p_and_elim this)).left
  ),

  have h_calls: calls_p_subst σ P₁ ⊆ calls_p_subst σ (P₁ ⋀ P₂), from (
    assume c: calltrigger,
    assume : c ∈ calls_p_subst σ P₁,
    show c ∈ calls_p_subst σ (P₁ ⋀ P₂), from prop.has_call_p_subst.and₁ this
  ),

  have h_quantifiers_p:
    (∀(t₁: term) (x: var) (Q₁: prop) (h: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p P₁),
                          have Q₁.size < P₁.size, from quantifiers_smaller_than_prop.left h,
    ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers_p (P₁ ⋀ P₂) ∧
                          (∀v: value, dominates' Q₁ Q₂ (σ[x↦v]))), from (

    assume (t₁: term) (x:var) (Q₁: prop),
    assume : callquantifier.mk t₁ x Q₁ ∈ quantifiers_p P₁,
    have t₁_Q₁_in: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p (P₁ ⋀ P₂), from prop.has_quantifier_p.and₁ this,
    have (∀v: value, dominates' Q₁ Q₁ (σ[x↦v])), from (
      assume v: value,
      dominates_self
    ),

    show ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers_p (P₁ ⋀ P₂) ∧
                                  (∀v: value, dominates' Q₁ Q₂ (σ[x↦v])),
    from exists.intro t₁ (exists.intro Q₁ ⟨t₁_Q₁_in, this⟩)
  ),

  show dominates σ (P₁ ⋀ P₂) P₁, from dominates_of h_impl h_calls h_quantifiers_p

lemma dominates_of_and₂ {P₁ P₂: prop} {σ: env}: dominates σ (P₁ ⋀ P₂) P₂ :=
  have h1: dominates σ (P₁ ⋀ P₂) (P₂ ⋀ P₁), from dominates_and_symm,
  have h2: dominates σ (P₂ ⋀ P₁) P₂, from dominates_of_and₁,
  show dominates σ (P₁ ⋀ P₂) P₂, from dominates.trans h1 h2

lemma dominates_not_not: ∀ {P: prop} {σ: env}, dominates σ P.not.not P
| P σ :=
  have h_impl: σ ⊨ vc.implies P.not.not.instantiated_p P.instantiated_p, from valid_env.mpr (
    assume h1: σ ⊨ P.not.not.instantiated_p,
    have P.not.not.instantiated_p = P.not.instantiated_n.not, from not_dist_instantiated_p,
    have h2: σ ⊨ P.not.instantiated_n.not, from this ▸ h1,
    have P.not.instantiated_n = P.instantiated_p.not, from not_dist_instantiated_n,
    have σ ⊨ P.instantiated_p.not.not, from this ▸ h2,
    show σ ⊨ P.instantiated_p, from valid_env.neg_neg.mp this
  ),
  have h_calls: calls_p_subst σ P ⊆ calls_p_subst σ P.not.not, from (
    assume c: calltrigger,
    assume : c ∈ calls_p_subst σ P,
    have c ∈ calls_n_subst σ P.not, from prop.has_call_p_subst.not this,
    show c ∈ calls_p_subst σ P.not.not, from prop.has_call_n_subst.not this
  ),
  have h_quantifiers_p:
    (∀(t': term) (x: var) (Q₁: prop) (h: callquantifier.mk t' x Q₁ ∈ quantifiers_p P),
                          have Q₁.size < P.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers_p P.not.not ∧
                          (∀v: value, dominates' Q₁ Q₂ (σ[x↦v]))), from (
    assume (t₁: term) (x:var) (Q₁: prop),
    assume h: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p P,
    have callquantifier.mk t₁ x Q₁ ∈ quantifiers_n P.not, from prop.has_quantifier_n.not h,
    have h2: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p P.not.not, from prop.has_quantifier_p.not this,
    have Q₁.size < P.size, from quantifiers_smaller_than_prop.left h,
    have (∀v: value, dominates' Q₁ Q₁ (σ[x↦v])), from (
      assume v: value,
      dominates_self
    ),
    exists.intro t₁ (exists.intro Q₁ ⟨h2, this⟩)
  ),
  show dominates σ P.not.not P, from dominates_of h_impl h_calls h_quantifiers_p

lemma dominates_of_not_not: ∀ {P: prop} {σ: env}, dominates σ P P.not.not
| P σ :=
  have h_impl: σ ⊨ vc.implies P.instantiated_p P.not.not.instantiated_p, from valid_env.mpr (
    assume : σ ⊨ P.instantiated_p,
    have h1: σ ⊨ P.instantiated_p.not.not, from valid_env.neg_neg.mpr this,
    have P.not.instantiated_n = P.instantiated_p.not, from not_dist_instantiated_n,
    have h2: σ ⊨ P.not.instantiated_n.not, from this.symm ▸ h1,
    have P.not.not.instantiated_p = P.not.instantiated_n.not, from not_dist_instantiated_p,
    show σ ⊨ P.not.not.instantiated_p, from this.symm ▸ h2
  ),
  have h_calls: calls_p_subst σ P.not.not ⊆ calls_p_subst σ P, from (
    assume c: calltrigger,
    assume : c ∈ calls_p_subst σ P.not.not,
    have c ∈ calls_n_subst σ P.not, from prop.has_call_p_subst.not.inv this,
    show c ∈ calls_p_subst σ P, from prop.has_call_n_subst.not.inv this
  ),
  have h_quantifiers_p:
    (∀(t': term) (x: var) (Q₁: prop) (h: callquantifier.mk t' x Q₁ ∈ quantifiers_p P.not.not),
                          have Q₁.size < P.not.not.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers_p P ∧
                          (∀v: value, dominates' Q₁ Q₂ (σ[x↦v]))), from (
    assume (t₁: term) (x:var) (Q₁: prop),
    assume h: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p P.not.not,
    have callquantifier.mk t₁ x Q₁ ∈ quantifiers_n P.not, from prop.has_quantifier_p.not.inv h,
    have h2: callquantifier.mk t₁ x Q₁ ∈ quantifiers_p P, from prop.has_quantifier_n.not.inv this,
    have Q₁.size < P.size, from quantifiers_smaller_than_prop.left h2,
    have (∀v: value, dominates' Q₁ Q₁ (σ[x↦v])), from (
      assume v: value,
      dominates_self
    ),
    exists.intro t₁ (exists.intro Q₁ ⟨h2, this⟩)
  ),
  show dominates σ P P.not.not, from dominates_of h_impl h_calls h_quantifiers_p

lemma dominates_true (σ: env) (P: prop): dominates σ P value.true :=
  have h_impl: σ ⊨ vc.implies P.instantiated_p (prop.term value.true).instantiated_p, from valid_env.mpr (
    assume : σ ⊨ P.instantiated_p,
    have h1: σ ⊨ value.true, from valid_env.true,
    have (prop.term value.true).erased_n = vc.term value.true, by unfold prop.erased_n,
    have σ ⊨ (prop.term value.true).erased_n, from this ▸ h1,
    have σ ⊨ (prop.term value.true).instantiated_n, from valid_env.instantiated_n_of_erased_n this,
    show σ ⊨ (prop.term value.true).instantiated_p, from valid_env.instantiated_p_of_instantiated_n this
  ),
  have h_calls: calls_p_subst σ value.true ⊆ calls_p_subst σ P, from (
    assume c: calltrigger,
    assume : c ∈ calls_p_subst σ value.true,
    show c ∈ calls_p_subst σ P, from absurd this prop.has_call_p_subst.term.inv
  ),
  have h_quantifiers_p:
    (∀(t': term) (x: var) (Q₁: prop) (h: callquantifier.mk t' x Q₁ ∈ quantifiers_p value.true),
    ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers_p P ∧
                          (∀v: value, dominates' Q₁ Q₂ (σ[x↦v]))), from (
    assume (t₁: term) (x:var) (Q₁: prop),
    assume : callquantifier.mk t₁ x Q₁ ∈ quantifiers_p value.true,
    show ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers_p P ∧
                                (∀v: value, dominates' Q₁ Q₂ (σ[x↦v])),
    from absurd this prop.has_quantifier_p.term.inv
  ),
  show dominates σ P value.true, from dominates_of h_impl h_calls h_quantifiers_p

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

lemma env_dominates_rest {P: prop} {σ: env} {x: var} {v: value}:
      (⊢ (σ[x↦v]) : P) → (∃Q, (⊢ σ : Q) ∧ ∀σ', dominates σ' P Q) :=
  assume σ_verified: ⊢ (σ[x↦v]) : P,
  begin
    cases σ_verified,
    case env.vcgen.tru Q _ σ_verified { from
      have ∀σ', dominates σ' (prop.and Q (x ≡ value.true)) Q, from (
        assume σ': env,
        have h_impl: σ' ⊨ vc.implies (Q ⋀ x ≡ value.true).instantiated_p Q.instantiated_p, from valid_env.mpr (
          assume h2: σ' ⊨ (Q ⋀ (x ≡ value.true)).instantiated_p,
          have no_instantiations (x ≡ value.true), from no_instantiations.term,
          have (Q ⋀ (x ≡ value.true)).instantiated_p = (Q.instantiated_p ⋀ prop.erased_p (x ≡ value.true)),
          from and_dist_of_no_instantiations_p this,
          have σ' ⊨ (Q.instantiated_p ⋀ prop.erased_p (x ≡ value.true)), from this ▸ h2,
          show σ' ⊨ Q.instantiated_p, from (valid_env.and.elim this).left
        ),
        have h_calls: calls_p_subst σ' Q ⊆ calls_p_subst σ' (Q ⋀ x ≡ value.true), from (
          assume c: calltrigger,
          assume : c ∈ calls_p_subst σ' Q,
          show c ∈ calls_p_subst σ' (Q ⋀ x ≡ value.true), from prop.has_call_p_subst.and₁ this
        ),
        have h_quantifiers_p:
          (∀(t': term) (y: var) (Q₁: prop) (h: callquantifier.mk t' y Q₁ ∈ quantifiers_p Q),
                                have Q₁.size < Q.size, from quantifiers_smaller_than_prop.left h,
          ∃(t: term) (Q₂: prop), callquantifier.mk t y Q₂ ∈ quantifiers_p (Q ⋀ x ≡ value.true) ∧
                                (∀v: value, dominates' Q₁ Q₂ (σ'[y↦v]))), from (
          assume (t₁: term) (y:var) (Q₁: prop),
          assume h: callquantifier.mk t₁ y Q₁ ∈ quantifiers_p Q,
          have h2: callquantifier.mk t₁ y Q₁ ∈ quantifiers_p (Q ⋀ x ≡ value.true), from prop.has_quantifier_p.and₁ h,
          have Q₁.size < (Q ⋀ x ≡ value.true).size, from quantifiers_smaller_than_prop.left h2,
          have (∀v: value, dominates' Q₁ Q₁ (σ'[y↦v])), from (
            assume v: value,
            dominates_self
          ),
          exists.intro t₁ (exists.intro Q₁ ⟨h2, this⟩)
        ),
        show dominates σ' (Q ⋀ x ≡ value.true) Q, from dominates_of h_impl h_calls h_quantifiers_p
      ),
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ ∀σ', dominates σ' (prop.and Q (x ≡ value.true)) Q_1,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.fls Q _ σ_verified { from
      have ∀σ', dominates σ' (prop.and Q (x ≡ value.false)) Q, from (
        assume σ': env,
        have h_impl: σ' ⊨ vc.implies (Q ⋀ x ≡ value.false).instantiated_p Q.instantiated_p, from valid_env.mpr (
          assume h2: σ' ⊨ (Q ⋀ (x ≡ value.false)).instantiated_p,
          have no_instantiations (x ≡ value.false), from no_instantiations.term,
          have (Q ⋀ (x ≡ value.false)).instantiated_p = (Q.instantiated_p ⋀ prop.erased_p (x ≡ value.false)),
          from and_dist_of_no_instantiations_p this,
          have σ' ⊨ (Q.instantiated_p ⋀ prop.erased_p (x ≡ value.false)), from this ▸ h2,
          show σ' ⊨ Q.instantiated_p, from (valid_env.and.elim this).left
        ),
        have h_calls: calls_p_subst σ' Q ⊆ calls_p_subst σ' (Q ⋀ x ≡ value.false), from (
          assume c: calltrigger,
          assume : c ∈ calls_p_subst σ' Q,
          show c ∈ calls_p_subst σ' (Q ⋀ x ≡ value.false), from prop.has_call_p_subst.and₁ this
        ),
        have h_quantifiers_p:
          (∀(t': term) (y: var) (Q₁: prop) (h: callquantifier.mk t' y Q₁ ∈ quantifiers_p Q),
                                have Q₁.size < Q.size, from quantifiers_smaller_than_prop.left h,
          ∃(t: term) (Q₂: prop), callquantifier.mk t y Q₂ ∈ quantifiers_p (Q ⋀ x ≡ value.false) ∧
                                (∀v: value, dominates' Q₁ Q₂ (σ'[y↦v]))), from (
          assume (t₁: term) (y:var) (Q₁: prop),
          assume h: callquantifier.mk t₁ y Q₁ ∈ quantifiers_p Q,
          have h2: callquantifier.mk t₁ y Q₁ ∈ quantifiers_p (Q ⋀ x ≡ value.false), from prop.has_quantifier_p.and₁ h,
          have Q₁.size < (Q ⋀ x ≡ value.false).size, from quantifiers_smaller_than_prop.left h2,
          have (∀v: value, dominates' Q₁ Q₁ (σ'[y↦v])), from (
            assume v: value,
            dominates_self
          ),
          exists.intro t₁ (exists.intro Q₁ ⟨h2, this⟩)
        ),
        show dominates σ' (Q ⋀ x ≡ value.false) Q, from dominates_of h_impl h_calls h_quantifiers_p
      ),
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ ∀σ', dominates σ' (prop.and Q (x ≡ value.false)) Q_1,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.num n Q _ σ_verified { from
      have ∀σ', dominates σ' (prop.and Q (x ≡ value.num n)) Q, from (
        assume σ': env,
        have h_impl: σ' ⊨ vc.implies (Q ⋀ x ≡ value.num n).instantiated_p Q.instantiated_p, from valid_env.mpr (
          assume h2: σ' ⊨ (Q ⋀ (x ≡ value.num n)).instantiated_p,
          have no_instantiations (x ≡ value.num n), from no_instantiations.term,
          have (Q ⋀ (x ≡ value.num n)).instantiated_p = (Q.instantiated_p ⋀ prop.erased_p (x ≡ value.num n)),
          from and_dist_of_no_instantiations_p this,
          have σ' ⊨ (Q.instantiated_p ⋀ prop.erased_p (x ≡ value.num n)), from this ▸ h2,
          show σ' ⊨ Q.instantiated_p, from (valid_env.and.elim this).left
        ),
        have h_calls: calls_p_subst σ' Q ⊆ calls_p_subst σ' (Q ⋀ x ≡ value.num n), from (
          assume c: calltrigger,
          assume : c ∈ calls_p_subst σ' Q,
          show c ∈ calls_p_subst σ' (Q ⋀ x ≡ value.num n), from prop.has_call_p_subst.and₁ this
        ),
        have h_quantifiers_p:
          (∀(t': term) (y: var) (Q₁: prop) (h: callquantifier.mk t' y Q₁ ∈ quantifiers_p Q),
                                have Q₁.size < Q.size, from quantifiers_smaller_than_prop.left h,
          ∃(t: term) (Q₂: prop), callquantifier.mk t y Q₂ ∈ quantifiers_p (Q ⋀ x ≡ value.num n) ∧
                                (∀v: value, dominates' Q₁ Q₂ (σ'[y↦v]))), from (
          assume (t₁: term) (y:var) (Q₁: prop),
          assume h: callquantifier.mk t₁ y Q₁ ∈ quantifiers_p Q,
          have h2: callquantifier.mk t₁ y Q₁ ∈ quantifiers_p (Q ⋀ x ≡ value.num n), from prop.has_quantifier_p.and₁ h,
          have Q₁.size < (Q ⋀ x ≡ value.num n).size, from quantifiers_smaller_than_prop.left h2,
          have (∀v: value, dominates' Q₁ Q₁ (σ'[y↦v])), from (
            assume v: value,
            dominates_self
          ),
          exists.intro t₁ (exists.intro Q₁ ⟨h2, this⟩)
        ),
        show dominates σ' (Q ⋀ x ≡ value.num n) Q, from dominates_of h_impl h_calls h_quantifiers_p
      ),
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ ∀σ', dominates σ' (prop.and Q (x ≡ value.num n)) Q_1,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.func σ₂ f fx R S H e Q Q₂ Q₃ x_not_in_σ f_not_in_σ₂
         fx_not_in_σ₂ f_neq_fx σ_verified σ₂_verified fx_in_R fv_R fv_S e_verified func_vc { from
      let funcp := prop.subst_env (σ₂[f↦value.func f fx R S e H σ₂])
                                  (prop.func f fx R (Q₃ (term.app f fx) ⋀ S)) in
      have ∀σ', dominates σ' (Q ⋀ x ≡ value.func f fx R S e H σ₂ ⋀ funcp) Q, from (
        assume σ': env,
        have h_impl: σ' ⊨ vc.implies (Q ⋀ x ≡ value.func f fx R S e H σ₂ ⋀ funcp).instantiated_p Q.instantiated_p,
        from valid_env.mpr (
          assume : σ' ⊨ (Q ⋀ x ≡ value.func f fx R S e H σ₂ ⋀ funcp).instantiated_p,
          have σ' ⊨ Q.instantiated_p ⋀ (↑(x ≡ value.func f fx R S e H σ₂) ⋀ funcp).instantiated_p,
          from valid_env.instantiated_p_and_elim this,
          show σ' ⊨ Q.instantiated_p, from (valid_env.and.elim this).left
        ),
        have h_calls: calls_p_subst σ' Q ⊆ calls_p_subst σ' (Q ⋀ x ≡ value.func f fx R S e H σ₂ ⋀ funcp), from (
          assume c: calltrigger,
          assume : c ∈ calls_p_subst σ' Q,
          show c ∈ calls_p_subst σ' (Q ⋀ x ≡ value.func f fx R S e H σ₂ ⋀ funcp), from prop.has_call_p_subst.and₁ this
        ),
        have h_quantifiers_p:
          (∀(t': term) (y: var) (Q₁: prop) (h: callquantifier.mk t' y Q₁ ∈ quantifiers_p Q),
                                have Q₁.size < Q.size, from quantifiers_smaller_than_prop.left h,
          ∃(t: term) (Q₂: prop), callquantifier.mk t y Q₂ ∈ quantifiers_p (Q ⋀ x ≡ value.func f fx R S e H σ₂ ⋀ funcp) ∧
                                (∀v: value, dominates' Q₁ Q₂ (σ'[y↦v]))), from (
          assume (t₁: term) (y:var) (Q₁: prop),
          assume h: callquantifier.mk t₁ y Q₁ ∈ quantifiers_p Q,
          have h2: callquantifier.mk t₁ y Q₁ ∈ quantifiers_p (Q ⋀ x ≡ value.func f fx R S e H σ₂ ⋀ funcp),
          from prop.has_quantifier_p.and₁ h,
          have Q₁.size < (Q ⋀ x ≡ value.func f fx R S e H σ₂ ⋀ funcp).size, from quantifiers_smaller_than_prop.left h2,
          have (∀v: value, dominates' Q₁ Q₁ (σ'[y↦v])), from (
            assume v: value,
            dominates_self
          ),
          exists.intro t₁ (exists.intro Q₁ ⟨h2, this⟩)
        ),
        show dominates σ' (Q ⋀ x ≡ value.func f fx R S e H σ₂ ⋀ funcp) Q, from dominates_of h_impl h_calls h_quantifiers_p
      ),
      show ∃Q_1, (⊢ σ : Q_1) ∧ ∀σ', dominates σ' (prop.and Q ((x ≡ (value.func f fx R S e H σ₂)) ⋀ funcp)) Q_1,
      from exists.intro Q ⟨σ_verified, this⟩
    }
  end

lemma strengthen_impl_with_dominating_instantiations {σ: env} {P P' Q: prop}:
  dominates σ P' P → σ ⊨ vc.implies (prop.implies P Q).instantiated_n (prop.implies P' Q).instantiated_n :=
  assume P'_dominates_P: dominates σ P' P,
  show σ ⊨ vc.implies (prop.implies P Q).instantiated_n (prop.implies P' Q).instantiated_n, from valid_env.mpr (
    assume : σ ⊨ (P.not ⋁ Q).instantiated_n,
    have h1: σ ⊨ (P.not ⋁ Q).instantiated_n.not.not, from valid_env.neg_neg.mpr this,
    have (P.not ⋁ Q).not.instantiated_p = (P.not ⋁ Q).instantiated_n.not, from not_dist_instantiated_p,
    have h2: σ ⊨ (P.not ⋁ Q).not.instantiated_p.not, from this.symm ▸ h1,
    have h3: σ ⊨ vc.implies (P'.not ⋁ Q).not.instantiated_p (P.not ⋁ Q).not.instantiated_p, from valid_env.mpr (
      assume : σ ⊨ (P'.not ⋁ Q).not.instantiated_p,
      have h4: σ ⊨ (P'.not.not ⋀ Q.not).instantiated_p, from valid_env.or_not_dist_with_instantiations.mp this,
      have dominates σ P'.not.not P', from dominates_not_not,
      have σ ⊨ vc.implies (P'.not.not ⋀ Q.not).instantiated_p (P' ⋀ Q.not).instantiated_p,
      from valid_env.strengthen_and_with_dominating_instantiations this,
      have h5: σ ⊨ (P' ⋀ Q.not).instantiated_p, from valid_env.mp this h4,
      have σ ⊨ vc.implies (P' ⋀ Q.not).instantiated_p (P ⋀ Q.not).instantiated_p,
      from valid_env.strengthen_and_with_dominating_instantiations P'_dominates_P,
      have h6: σ ⊨ (P ⋀ Q.not).instantiated_p, from valid_env.mp this h5,
      have dominates σ P P.not.not, from dominates_of_not_not,
      have σ ⊨ vc.implies (P ⋀ Q.not).instantiated_p (P.not.not ⋀ Q.not).instantiated_p,
      from valid_env.strengthen_and_with_dominating_instantiations this,
      have σ ⊨ (P.not.not ⋀ Q.not).instantiated_p, from valid_env.mp this h6,
      show σ ⊨ (P.not ⋁ Q).not.instantiated_p, from valid_env.or_not_dist_with_instantiations.mpr this
    ),
    have h9: σ ⊨ (P'.not ⋁ Q).not.instantiated_p.not, from valid_env.mt h3 h2,
    have (P'.not ⋁ Q).not.instantiated_p = (P'.not ⋁ Q).instantiated_n.not, from not_dist_instantiated_p,
    have σ ⊨ (P'.not ⋁ Q).instantiated_n.not.not, from this ▸ h9,
    show σ ⊨ (P'.not ⋁ Q).instantiated_n, from valid_env.neg_neg.mp this
  )

lemma dominates_shuffle {P Q R S: prop} {σ: env}:
      (σ ⊨ (P ⋀ Q ⋀ R ⋀ S).instantiated_p) → (σ ⊨ ((P ⋀ Q ⋀ R) ⋀ S).instantiated_p) :=
  assume : σ ⊨ (P ⋀ Q ⋀ R ⋀ S).instantiated_p,
  have h1: σ ⊨ ((Q ⋀ R ⋀ S) ⋀ P).instantiated_p, from valid_env.and_symm_with_instantiations this,
  have dominates σ (Q ⋀ R ⋀ S) ((Q ⋀ R) ⋀ S), from dominates_and_comm,
  have σ ⊨ (((Q ⋀ R) ⋀ S) ⋀ P).instantiated_p,
  from valid_env.mp (valid_env.strengthen_and_with_dominating_instantiations this) h1,
  have σ ⊨ (P ⋀ ((Q ⋀ R) ⋀ S)).instantiated_p, from valid_env.and_symm_with_instantiations this,
  show σ ⊨ ((P ⋀ Q ⋀ R) ⋀ S).instantiated_p, from valid_env.and_comm_with_instantiations.mp this

lemma strengthen_vc {P P' Q S: prop} {σ: env}:
  dominates σ P' P → (σ ⊨ (prop.implies (P ⋀ Q) S).instantiated_n) → σ ⊨ (prop.implies (P' ⋀ Q) S).instantiated_n :=
  assume : dominates σ P' P,
  have dominates σ (P' ⋀ Q) (P ⋀ Q), from dominates_and_left this,
  valid_env.mp (strengthen_impl_with_dominating_instantiations this)

lemma strengthen_exp {P: prop} {Q: propctx} {e: exp}:
      (P ⊢ e : Q) → ∀P': prop, (FV P' = FV P) → (∀σ, dominates σ P' P) → (P' ⊢ e: Q) :=
  assume e_verified: (P ⊢ e : Q),
  begin
    induction e_verified,
    case exp.vcgen.tru x P e' Q x_not_free_in_P e'_verified ih { from (
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_P: (∀σ, dominates σ P' P),

      have h1: FV (P' ⋀ (x ≡ value.true)) = FV (P ⋀ (x ≡ value.true)),
      from same_free_and_left free_P'_P,
      have h2: (∀σ, dominates σ (P' ⋀ (x ≡ value.true)) (P ⋀ (x ≡ value.true))),
      from (λσ, dominates_and_left (P'_dominates_P σ)),
      have e'_verified': P' ⋀ (x ≡ value.true) ⊢ e': Q, from ih (P' ⋀ (x ≡ value.true)) h1 h2,
      have x_not_free_in_P': x ∉ FV P', from free_P'_P.symm ▸ x_not_free_in_P,
      show P' ⊢ lett x = true in e' : propctx.exis x ((x ≡ value.true) ⋀ Q),
      from exp.vcgen.tru x_not_free_in_P' e'_verified'
    )},
    case exp.vcgen.fals x P e' Q x_not_free_in_P e'_verified ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_P: (∀σ, dominates σ P' P),

      have h1: FV (P' ⋀ (x ≡ value.false)) = FV (P ⋀ (x ≡ value.false)),
      from same_free_and_left free_P'_P,
      have h2: (∀σ, dominates σ (P' ⋀ (x ≡ value.false)) (P ⋀ (x ≡ value.false))),
      from (λσ, dominates_and_left (P'_dominates_P σ)),
      have e'_verified': P' ⋀ (x ≡ value.false) ⊢ e': Q, from ih (P' ⋀ (x ≡ value.false)) h1 h2,
      have x_not_free_in_P': x ∉ FV P', from free_P'_P.symm ▸ x_not_free_in_P,
      show P' ⊢ letf x = false in e' : propctx.exis x ((x ≡ value.false) ⋀ Q),
      from exp.vcgen.fals x_not_free_in_P' e'_verified'
    },
    case exp.vcgen.num x n P e' Q x_not_free_in_P e'_verified ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_P: (∀σ, dominates σ P' P),

      have h1: FV (P' ⋀ (x ≡ value.num n)) = FV (P ⋀ (x ≡ value.num n)),
      from same_free_and_left free_P'_P,
      have h2: (∀σ, dominates σ (P' ⋀ (x ≡ value.num n)) (P ⋀ (x ≡ value.num n))),
      from (λσ, dominates_and_left (P'_dominates_P σ)),
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
      from (λσ, dominates_and_left (P'_dominates_P σ)),
      have e₁_verified': P' ⋀ (spec.func f x R S) ⋀ R ⊢ e₁ : Q₁,
      from ih₁ (P' ⋀ (spec.func f x R S) ⋀ R) h1 h2,

      have h3: FV (P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)))
             = FV (P ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S))),
      from same_free_and_left free_P'_P,
      have h4: (∀σ, dominates σ (P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)))
                                (P ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)))),
      from (λσ, dominates_and_left (P'_dominates_P σ)),
      have e₂_verified': P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)) ⊢ e₂ : Q₂,
      from ih₂ (P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S))) h3 h4,

      have func_vc': ∀ (σ : env),
             σ ⊨ prop.instantiated_n (prop.implies (P' ⋀ ↑(spec.func ↑f x R S) ⋀ R ⋀ Q₁ (term.app ↑f ↑x)) ↑S),
      from (λσ, strengthen_vc (P'_dominates_P σ) (func_vc σ)),

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
      from (λσ, dominates_and_left (P'_dominates_P σ)),
      have e'_verified': P' ⋀ y ≡ term.unop op x ⊢ e' : Q',
      from ih (P' ⋀ y ≡ term.unop op x) h1 h2,

      have vc_valid': ∀ (σ : env),
             σ ⊨ prop.instantiated_n (prop.implies P' (prop.pre₁ op x)),
      from (λσ, valid_env.mp (strengthen_impl_with_dominating_instantiations (P'_dominates_P σ)) (vc_valid σ)),

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
      from (λσ, dominates_and_left (P'_dominates_P σ)),
      have e'_verified': P' ⋀ z ≡ term.binop op x y ⊢ e' : Q',
      from ih (P' ⋀ z ≡ term.binop op x y) h1 h2,

      have vc_valid': ∀ (σ : env),
             σ ⊨ prop.instantiated_n (prop.implies P' (prop.pre₂ op x y)),
      from (λσ, valid_env.mp (strengthen_impl_with_dominating_instantiations (P'_dominates_P σ)) (vc_valid σ)),

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
      from (λσ, dominates_and_left (P'_dominates_P σ)),

      have e'_verified': P' ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⊢ e' : Q',
      from ih (P' ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) h1 h2,

      have vc_valid': ∀ (σ : env),
             σ ⊨ prop.instantiated_n (prop.implies (P' ⋀ prop.call f x) (term.unop unop.isFunc f ⋀ prop.pre f x)),
      from (λσ, strengthen_vc (P'_dominates_P σ) (vc_valid σ)),

      show P' ⊢ letapp y = f [x] in e' : propctx.exis y (prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⋀ Q'),
      from exp.vcgen.app f_free_in_P' x_free_in_P' y_not_free_in_P' e'_verified' vc_valid'
    },
    case exp.vcgen.ite x e₂ e₁ P Q₁ Q₂ x_free_in_P e₁_verified e₂_verified vc_valid ih₁ ih₂ { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_P: (∀σ, dominates σ P' P),

      have x_free_in_P': x ∈ FV P', from free_P'_P.symm ▸ x_free_in_P,

      have h1: FV (P' ⋀ x) = FV (P ⋀ x), from same_free_and_left free_P'_P,
      have h2: (∀σ, dominates σ (P' ⋀ x) (P ⋀ x)), from (λσ, dominates_and_left (P'_dominates_P σ)),
      have e₁_verified': P' ⋀ x ⊢ e₁ : Q₁, from ih₁ (P' ⋀ x) h1 h2,

      have h1: FV (P' ⋀ term.unop unop.not x) = FV (P ⋀ term.unop unop.not x), from same_free_and_left free_P'_P,
      have h2: (∀σ, dominates σ (P' ⋀ term.unop unop.not x) (P ⋀ term.unop unop.not x)),
      from (λσ, dominates_and_left (P'_dominates_P σ)),
      have e₂_verified': P' ⋀ term.unop unop.not x ⊢ e₂ : Q₂, from ih₂ (P' ⋀ term.unop unop.not x) h1 h2,

      have vc_valid': ∀ (σ : env),
             σ ⊨ prop.instantiated_n (prop.implies P' (term.unop unop.isBool x)),
      from (λσ, valid_env.mp (strengthen_impl_with_dominating_instantiations (P'_dominates_P σ)) (vc_valid σ)),

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
      have h1: σ' ⊨ prop.instantiated_p (y ≡ value.true),
      from (valid_env.and.elim (valid_env.instantiated_p_and_elim P_valid)).right,

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

    }
  end

lemma exp.preservation {R: spec} {H: history} {σ σ': env} {P: prop} {e e': exp} {Q: propctx}:
      (⊢ σ : P) → FV (spec.to_prop R) ⊆ FV P → (σ ⊨ R.to_prop.instantiated_n) → (R ⋀ H ⋀ P ⊢ e : Q) →
      ((R, H, σ, e) ⟶ (R, H, σ', e')) → ⊢ₛ (R, H, σ', e') :=
  sorry

lemma inlined_dominates_spec {σ σ₁: env} {P: prop} {Q: propctx} {f x: var} {R S: spec} {e: exp} {H: history}:
  (⊢ σ₁ : P) → (⊢ (σ₁[f↦value.func f x R S e H σ₁]) : (P ⋀ f ≡ value.func f x R S e H σ₁ ⋀
                  prop.subst_env (σ₁[f↦value.func f x R S e H σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)))) →
  dominates σ (P ⋀ f ≡ value.func f x R S e H σ₁ ⋀
               prop.subst_env (σ₁[f↦value.func f x R S e H σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)))
              (P ⋀ spec.func f x R S) :=
  
  let forallp' := (prop.implies R.to_prop (prop.pre f x) ⋀
                   prop.implies (prop.post f x) (Q (term.app f x) ⋀ S.to_prop)) in

  let forallp := (prop.implies R.to_prop (prop.pre f x) ⋀ prop.implies (prop.post f x) S.to_prop) in

  let P' := P ⋀ f ≡ value.func f x R S e H σ₁ ⋀
            prop.subst_env (σ₁[f↦value.func f x R S e H σ₁]) (prop.func f x R (Q (term.app f x) ⋀ S)) in

  assume σ₁_verified: ⊢ σ₁ : P,
  assume σ₁f_verified: ⊢ (σ₁[f↦value.func f x R S e H σ₁]) : P',

  dominates_of_pre (
    assume : σ ⊨ P'.instantiated_p,

    have σ ⊨ P.instantiated_p, from (valid_env.and.elim (valid_env.instantiated_p_and_elim this)).left,
    have h0: σ ⊨ P.erased_p, from valid_env.erased_p_of_instantiated_p this,

    have h1: calls_p P = ∅, from no_calls_in_env_translation σ₁_verified,
    have h2: calls_p (spec.func f x R S) = ∅, from no_calls_in_spec,
    have calls_p (P ⋀ spec.func f x R S) = calls_p P ∪ calls_p (spec.func f x R S),
    from prop.has_call_p.and_union,
    have calls_p (P ⋀ spec.func f x R S) = ∅ ∪ calls_p (spec.func f x R S), from h1 ▸ this,
    have calls_p (P ⋀ spec.func f x R S) = ∅ ∪ ∅,
    from @eq.subst (set calltrigger) (λa, calls_p (P ⋀ spec.func f x R S) = ∅ ∪ a)
                   (calls_p (spec.func f x R S)) ∅ h2 this,
    have calls_p (P ⋀ spec.func f x R S) = ∅, from eq.trans this (set.empty_union ∅),
    have h4: (P ⋀ spec.func f x R S).instantiated_p = (P ⋀ spec.func f x R S).erased_p,
    from instantiated_p_eq_erased_p_without_calls this,


    have h5: σ ⊨ term.unop unop.isFunc f, from sorry,
    have prop.erased_p (prop.term (term.unop unop.isFunc f)) = vc.term (term.unop unop.isFunc f),
    by unfold prop.erased_p,
    have h6: σ ⊨ (prop.term (term.unop unop.isFunc f)).erased_p, from this.symm ▸ h5,

    have h7: σ ⊨ value.true, from valid_env.true,
    have prop.erased_p (prop.forallc x f forallp) = vc.term value.true, by unfold prop.erased_p,
    have σ ⊨ (prop.forallc x f forallp).erased_p, from this.symm ▸ h7,

    have h8: σ ⊨ ((prop.term (term.unop unop.isFunc f)).erased_p ⋀ (prop.forallc x f forallp).erased_p),
    from valid_env.and h6 this,
    have prop.erased_p (prop.and (prop.term (term.unop unop.isFunc f)) (prop.forallc x f forallp))
       = ((prop.term (term.unop unop.isFunc f)).erased_p ⋀ (prop.forallc x f forallp).erased_p),
    by unfold prop.erased_p,
    have σ ⊨ (prop.term (term.unop unop.isFunc f) ⋀ prop.forallc x f forallp).erased_p, from this.symm ▸ h8,
    have σ ⊨ (prop.func f x R S).erased_p, from this,

    have h9: σ ⊨ P.erased_p ⋀ (prop.func f x R S).erased_p, from valid_env.and h0 this,
    have prop.erased_p (prop.and P (prop.func f x R S)) = (P.erased_p ⋀ (prop.func f x R S).erased_p),
    by unfold prop.erased_p,
    have σ ⊨ prop.erased_p (P ⋀ spec.func f x R S), from this.symm ▸ h9,
    have h_impl: σ ⊨ (P ⋀ spec.func f x R S).instantiated_p, from h4.symm ▸ this,

    have h_calls: calls_p_subst σ (P ⋀ spec.func f x R S)
                ⊆ calls_p_subst σ P', from sorry,

    have h_quantifiers_p:
      (∀(t₃: term) (y: var) (Q₃: prop) (h: callquantifier.mk t₃ y Q₃ ∈ quantifiers_p (P ⋀ spec.func f x R S)),
                            have Q₃.size < (P ⋀ spec.func f x R S).size, from quantifiers_smaller_than_prop.left h,
      ∃(t₁: term) (Q₁: prop), callquantifier.mk t₁ y Q₁ ∈ quantifiers_p P' ∧
                            (∀v: value, dominates' Q₃ Q₁ (σ[y↦v]))), from (

      assume (t₃: term) (y:var) (Q₃: prop),
      assume h5: callquantifier.mk t₃ y Q₃ ∈ quantifiers_p (P ⋀ spec.func f x R S),

      -- have ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers_p P₂ ∧
      --                       (∀v: value, dominates' Q₃ Q₂ (σ[x↦v])),
      -- from h4.right.right t₃ x Q₃ h5,
      -- let ⟨t₂, Q₂, ⟨t₂_Q₂_in_P₂, Q₃_dom_Q₂⟩⟩ := this in
      -- have ∃(t₁: term) (Q₁: prop), callquantifier.mk t₁ x Q₁ ∈ quantifiers_p P₁ ∧
      --                       (∀v: value, dominates' Q₂ Q₁ (σ[x↦v])),
      -- from h3.right.right t₂ x Q₂ t₂_Q₂_in_P₂,
      -- let ⟨t₁, Q₁, ⟨t₁_Q₁_in_P₁, Q₂_dom_Q₁⟩⟩ := this in
      -- have Q₃_dom_Q₁: (∀v: value, dominates' Q₃ Q₁ (σ[x↦v])), from (
      --   assume v: value,
      --   have h6: dominates (σ[x↦v]) Q₁ Q₂, from Q₂_dom_Q₁ v,
      --   have h7: dominates (σ[x↦v]) Q₂ Q₃, from Q₃_dom_Q₂ v,
      --   have Q₁.size < P₁.size, from quantifiers_smaller_than_prop.left t₁_Q₁_in_P₁,
      --   show dominates (σ[x↦v]) Q₁ Q₃, from dominates.trans h6 h7
      -- ),

      show ∃(t₁: term) (Q₁: prop), callquantifier.mk t₁ y Q₁ ∈ quantifiers_p P' ∧
                                  (∀v: value, dominates' Q₃ Q₁ (σ[y↦v])),
      from sorry
      -- from exists.intro t₁ (exists.intro Q₁ ⟨t₁_Q₁_in_P₁, Q₃_dom_Q₁⟩)
    ),
    ⟨h_impl, ⟨h_calls, h_quantifiers_p⟩⟩
  )

theorem preservation {s s': stack}: (⊢ₛ s) → (s ⟶ s') → (⊢ₛ s') :=
  assume s_verified:  ⊢ₛ s,
  assume s_steps: s ⟶ s',
  begin
    cases s_verified,
    case stack.vcgen.top σ e P Q H R σ_verified fv_R R_valid e_verified {
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
                    assume : x ∈ FV (prop.func g gx R₂ S₂ ⋀ R₂),
                    or.elim (free_in_prop.and.inv this) (
                      assume : x ∈ FV (prop.func g gx R₂ S₂),
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
                      have x ∈ FV (prop.func g gx R₂ S₂), from free_in_prop.and₁ this,
                      have x ∈ FV (prop.func g gx R₂ S₂ ⋀ R₂), from free_in_prop.and₁ this,
                      show x ∈ FV (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from free_in_prop.and₂ this
                    )
                  ) (
                    assume : x ∈ set.insert gx ∅,
                    have x = gx, from (set.mem_singleton_iff x gx).mp this,
                    have x ∈ FV R₂.to_prop,
                    from this.symm ▸ ha2.right.right.right.right.right.right.left,
                    have x ∈ FV (prop.func g gx R₂ S₂ ⋀ R₂), from free_in_prop.and₂ this,
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
              have h1: no_instantiations (term.unop unop.isFunc f), from no_instantiations.term,
              have h2: no_instantiations (prop.pre f x), from no_instantiations.pre,
              have no_instantiations (↑(term.unop unop.isFunc f) ⋀ prop.pre f x), from no_instantiations.and h1 h2,
              have h3: σ ⊨ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased_n,
              from consequent_of_H_P_call σ_verified R_valid func_vc this,
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
              from dominates_and_symm,

              have hb2: dominates σ ((H₂ ⋀ P₃) ⋀ R₂) (H₂ ⋀ P₃ ⋀ R₂),
              from dominates_and_rcomm,

              have hb3: dominates σ (↑H₂ ⋀ P₃ ⋀ ↑R₂) ((P₃ ⋀ ↑R₂) ⋀ H₂),
              from dominates_and_symm,

              have hb4: dominates σ (P₃ ⋀ ↑R₂) (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂), from (

                have (∃Q, (⊢ (σ₂[g↦value.func g gx R₂ S₂ e₁ H₂ σ₂]) : Q) ∧ ∀σ', dominates σ' P₃ Q),
                from env_dominates_rest ha5,
                let ⟨Q₂'', ⟨hb1, hb2⟩⟩ := this in
                have Q₂' = Q₂'', from env.vcgen.inj ha3 Q₂'' hb1,
                have hb3: dominates σ P₃ Q₂', from this.symm ▸ hb2 σ,

                have dominates σ Q₂' (Q₂ ⋀ spec.func g gx R₂ S₂),
                from inlined_dominates_spec ha2.right.right.right.right.right.left ha3,
                have dominates σ P₃ (Q₂ ⋀ spec.func g gx R₂ S₂),
                from dominates.trans hb3 this,

                have hb8: dominates σ (P₃ ⋀ ↑R₂) ((Q₂ ⋀ spec.func g gx R₂ S₂) ⋀ R₂),
                from dominates_and_left this,

                have hb9: dominates σ ((Q₂ ⋀ spec.func g gx R₂ S₂) ⋀ R₂) (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂),
                from dominates_and_rcomm,

                show dominates σ (P₃ ⋀ ↑R₂) (Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂),
                from dominates.trans hb8 hb9
              ),

              have hb5: dominates σ ((P₃ ⋀ ↑R₂) ⋀ H₂) ((Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂) ⋀ H₂),
              from dominates_and_left hb4,

              have hb6: dominates σ ((Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂) ⋀ H₂) (↑H₂ ⋀ Q₂ ⋀ spec.func g gx R₂ S₂ ⋀ R₂),
              from dominates_and_symm,

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
              from dominates_and_comm,

              have haa2: dominates σ (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                                     ((↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑R),
              from dominates_and_symm,

              have haa3: dominates σ ((↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑R)
                                     (((↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑ R),
              from dominates_and_left haa1,

              have haa4: dominates σ (((↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ⋀ ↑R)
                                     (↑R ⋀ (↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from dominates_and_symm,
              
              have haa5: dominates σ (↑R ⋀ (↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                                     ((↑R ⋀ (↑H ⋀ P)) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from dominates_and_comm,
              
              show dominates σ (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                               ((↑R ⋀ (↑H ⋀ P)) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from dominates.trans (dominates.trans (dominates.trans haa2 haa3) haa4) haa5
            ),
            show (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⊢ e₂ : Q),
            from strengthen_exp e₂_verified (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ha1 this
          ),

          have h8: ⟪ prop.implies (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x) (↑(term.unop unop.isFunc f) ⋀ prop.pre f x) ⟫, from (
            assume σ: env,
            have ha0: σ ⊨ (((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).not
                          ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated_n,
            from func_vc σ,

            have ha1: no_instantiations (term.unop unop.isFunc f), from no_instantiations.term,
            have ha2: no_instantiations (prop.pre f x), from no_instantiations.pre,
            have ha3: no_instantiations (↑(term.unop unop.isFunc f) ⋀ prop.pre f x), from no_instantiations.and ha1 ha2,
            have (((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).not ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated_n
               = (((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).not.instantiated_n
                      ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased_n),
            from or_dist_of_no_instantiations_n ha3,
            have σ ⊨ (((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).not.instantiated_n ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased_n),
            from this ▸ ha0,
            or.elim (valid_env.or.elim this) (
              assume ha4: σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).not.instantiated_n,
              have ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).not.instantiated_n
                 = ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_p.not,
              from not_dist_instantiated_n,
              have σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_p.not, from this ▸ ha4,
              have ha5: σ ⊨ (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x).instantiated_p.not, from valid_env.mt (valid_env.mpr (
                assume : σ ⊨ (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x).instantiated_p,
                show σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_p,
                from dominates_shuffle this
              )) this,
              have (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x).not.instantiated_n = (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x).instantiated_p.not,
              from not_dist_instantiated_n,
              have σ ⊨ (↑R ⋀ ↑H ⋀ P ⋀ prop.call f x).not.instantiated_n, from this.symm ▸ ha5,

              have ha6: σ ⊨ ((↑R ⋀ ↑H ⋀ P ⋀ prop.call f x).not.instantiated_n ⋁
                        (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased_n),
              from valid_env.or₁ this,

              have ((↑R ⋀ ↑H ⋀ P ⋀ prop.call f x).not ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated_n
                = ((↑R ⋀ ↑H ⋀ P ⋀ prop.call f x).not.instantiated_n ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased_n),
              from or_dist_of_no_instantiations_n ha3,

              have σ ⊨ ((↑R ⋀ ↑H ⋀ P ⋀ prop.call f x).not ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated_n,
              from this.symm ▸ ha6,
              show σ ⊨ (prop.implies (R ⋀ H ⋀ P ⋀ prop.call f x)
                                      (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated_n,
              from this
            ) (
              assume : σ ⊨ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased_n,
              have ha4: σ ⊨ ((↑R ⋀ ↑H ⋀ P ⋀ prop.call f x).not.instantiated_n ⋁
                        (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased_n),
              from valid_env.or₂ this,

              have ((↑R ⋀ ↑H ⋀ P ⋀ prop.call f x).not ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated_n
                = ((↑R ⋀ ↑H ⋀ P ⋀ prop.call f x).not.instantiated_n ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased_n),
              from or_dist_of_no_instantiations_n ha3,

              have σ ⊨ ((↑R ⋀ ↑H ⋀ P ⋀ prop.call f x).not ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated_n,
              from this.symm ▸ ha4,
              show σ ⊨ (prop.implies (R ⋀ H ⋀ P ⋀ prop.call f x)
                                     (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated_n,
              from this
            )
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
    case stack.vcgen.cons {-- H P s' σ σ' f g x y fx R S e vₓ Q s'_verified _ g_is_func x_is_v _ cont _ _ ih {
      cases s_steps,
      admit,
      admit
    }
  end
