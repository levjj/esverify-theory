import .syntax .notations .logic .evaluation .vcgen .bindings

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

lemma same_calls_and_left {P P' Q: prop} {σ: env}:
      calls_env σ P' = calls_env σ P → (calls_env σ (P' ⋀ Q) = calls_env σ (P ⋀ Q)) :=
  assume calls_P'_P: calls_env σ P' = calls_env σ P,
  set.eq_of_subset_of_subset (
    assume c: calltrigger,
    assume : c ∈ calls_env σ (P' ⋀ Q),
    or.elim (prop.has_call_env.and.inv this) (
      assume : c ∈ calls_env σ P',
      have c ∈ calls_env σ P, from calls_P'_P ▸ this,
      show c ∈ calls_env σ (P ⋀ Q), from prop.has_call_env.and₁ this
    )
    (
      assume : c ∈ calls_env σ Q,
      show c ∈ calls_env σ (P ⋀ Q), from prop.has_call_env.and₂ this
    )
  )
  (
    assume c: calltrigger,
    assume : c ∈ calls_env σ (P ⋀ Q),
    or.elim (prop.has_call_env.and.inv this) (
      assume : c ∈ calls_env σ P,
      have c ∈ calls_env σ P', from calls_P'_P.symm ▸ this,
      show c ∈ calls_env σ (P' ⋀ Q), from prop.has_call_env.and₁ this
    )
    (
      assume : c ∈ calls_env σ Q,
      show c ∈ calls_env σ (P' ⋀ Q), from prop.has_call_env.and₂ this
    )
  )

lemma dominates_self: ∀ {P: prop} {σ: env}, dominates σ P P
| P σ :=
  have h_impl: σ ⊨ vc.implies P.instantiated_n P.instantiated_n, from valid_env.mpr id,
  have h_calls: calls_env σ P = calls_env σ P, from rfl,
  have h_quantifiers:
    (∀(t': term) (x: var) (Q₁: prop) (h: callquantifier.mk t' x Q₁ ∈ quantifiers P),
                          have Q₁.size < P.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers P ∧
                          (∀v: value, dominates' Q₁ Q₂ (σ[x↦v]))), from (
    assume (t₁: term) (x:var) (Q₁: prop),
    assume h: callquantifier.mk t₁ x Q₁ ∈ quantifiers P,
    have Q₁.size < P.size, from quantifiers_smaller_than_prop.left h,
    have (∀v: value, dominates' Q₁ Q₁ (σ[x↦v])), from (
      assume v: value,
      dominates_self
    ),
    exists.intro t₁ (exists.intro Q₁ ⟨h, this⟩)
  ),
  show dominates σ P P, from dominates_of h_impl h_calls h_quantifiers

lemma dominates_and_left {P P' Q: prop} {σ: env}:
      dominates σ P' P → dominates σ (P' ⋀ Q) (P ⋀ Q) :=
  assume h1: dominates σ P' P,
  have dominates' P P' σ, from h1,
  have h2:
    ((σ ⊨ vc.implies P'.instantiated_n P.instantiated_n) ∧
    (calls_env σ P' = calls_env σ P) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P),
                          have Q'.size < P.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers P' ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v])))),
  by { unfold1 dominates' at this, from this },

  have calls_env σ P' = calls_env σ P, from h2.right.left,
  have h_calls: calls_env σ (P' ⋀ Q) = calls_env σ (P ⋀ Q), from same_calls_and_left this,
  have h_quantifiers:
    (∀(t': term) (x: var) (Q₁: prop) (h: callquantifier.mk t' x Q₁ ∈ quantifiers (P ⋀ Q)),
                          have Q₁.size < (P ⋀ Q).size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers (P' ⋀ Q) ∧
                          (∀v: value, dominates' Q₁ Q₂ (σ[x↦v]))), from (

    assume (t₁: term) (x:var) (Q₁: prop),
    assume : callquantifier.mk t₁ x Q₁ ∈ quantifiers (P ⋀ Q),
    or.elim (prop.has_quantifier.and.inv this) (
      assume : callquantifier.mk t₁ x Q₁ ∈ quantifiers P,
      have ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers P' ∧
                          (∀v: value, dominates' Q₁ Q₂ (σ[x↦v])),
      from h2.right.right t₁ x Q₁ this,
      let ⟨t₂, Q₂, ⟨call_t₂_Q₂_in_P', Q₂_impl_Q₁⟩⟩ := this in
      have callquantifier.mk t₂ x Q₂ ∈ quantifiers (P' ⋀ Q), from prop.has_quantifier.and₁ call_t₂_Q₂_in_P',
      show ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers (P' ⋀ Q) ∧
                                   (∀v: value, dominates' Q₁ Q₂ (σ[x↦v])),
      from exists.intro t₂ (exists.intro Q₂ ⟨this, Q₂_impl_Q₁⟩)
    ) (
      assume : callquantifier.mk t₁ x Q₁ ∈ quantifiers Q,
      have h1: callquantifier.mk t₁ x Q₁ ∈ quantifiers (P' ⋀ Q), from prop.has_quantifier.and₂ this,
      have h2: ∀v: value, dominates' Q₁ Q₁ (σ[x↦v]), from (
        assume v: value,
        show dominates' Q₁ Q₁ (σ[x↦v]), from dominates_self
      ),
      show ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers (P' ⋀ Q) ∧
                                   (∀v: value, dominates' Q₁ Q₂ (σ[x↦v])),
      from exists.intro t₁ (exists.intro Q₁ ⟨h1, h2⟩)
    )
  ),

  have σ ⊨ vc.implies P'.instantiated_n P.instantiated_n, from h2.left,
  have h_impl: σ ⊨ vc.implies (P' ⋀ Q).instantiated_n (P ⋀ Q).instantiated_n,
  from valid_env.strengthen_and_with_dominating_instantiations h1,
  show dominates σ (P' ⋀ Q) (P ⋀ Q), from dominates_of h_impl h_calls h_quantifiers

lemma dominates_and_symm {P₁ P₂: prop} {σ: env}:
      dominates σ (P₁ ⋀ P₂) (P₂ ⋀ P₁) :=

  have h_impl: σ ⊨ vc.implies (P₁ ⋀ P₂).instantiated_n (P₂ ⋀ P₁).instantiated_n,
  from valid_env.mpr valid_env.and_symm_with_instantiations,

  have h1: calls_env σ (P₁ ⋀ P₂) = (calltrigger.subst σ) '' calls (P₁ ⋀ P₂), by unfold calls_env,
  have calls (P₁ ⋀ P₂) = calls (P₂ ⋀ P₁), from prop.has_call.and.symm,
  have h2: calls_env σ (P₁ ⋀ P₂) = (calltrigger.subst σ) '' calls (P₂ ⋀ P₁),
  from this ▸ h1,
  have calls_env σ (P₂ ⋀ P₁) = (calltrigger.subst σ) '' calls (P₂ ⋀ P₁), by unfold calls_env,
  have h_calls: calls_env σ (P₁ ⋀ P₂) = calls_env σ (P₂ ⋀ P₁), from eq.trans h2 this.symm,

  have h_quantifiers:
    (∀(t₁: term) (x: var) (Q₁: prop) (h: callquantifier.mk t₁ x Q₁ ∈ quantifiers (P₂ ⋀ P₁)),
                          have Q₁.size < (P₂ ⋀ P₁).size, from quantifiers_smaller_than_prop.left h,
    ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers (P₁ ⋀ P₂) ∧
                          (∀v: value, dominates' Q₁ Q₂ (σ[x↦v]))), from (

    assume (t₁: term) (x:var) (Q₁: prop),
    assume t₁_Q₁_in_c: callquantifier.mk t₁ x Q₁ ∈ quantifiers (P₂ ⋀ P₁),
    have quantifiers (P₂ ⋀ P₁) = quantifiers (P₁ ⋀ P₂), from prop.has_quantifier.and.symm.symm,
    have t₁_Q₁_in: callquantifier.mk t₁ x Q₁ ∈ quantifiers (P₁ ⋀ P₂), from this ▸ t₁_Q₁_in_c,
    have (∀v: value, dominates' Q₁ Q₁ (σ[x↦v])), from (
      assume v: value,
      dominates_self
    ),

    show ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers (P₁ ⋀ P₂) ∧
                                  (∀v: value, dominates' Q₁ Q₂ (σ[x↦v])),
    from exists.intro t₁ (exists.intro Q₁ ⟨t₁_Q₁_in, this⟩)
  ),

  show dominates σ (P₁ ⋀ P₂) (P₂ ⋀ P₁), from dominates_of h_impl h_calls h_quantifiers

lemma dominates_and_comm {P₁ P₂ P₃: prop} {σ: env}:
      dominates σ (P₁ ⋀ P₂ ⋀ P₃) ((P₁ ⋀ P₂) ⋀ P₃) :=

  have h_impl: σ ⊨ vc.implies (P₁ ⋀ P₂ ⋀ P₃).instantiated_n ((P₁ ⋀ P₂) ⋀ P₃).instantiated_n,
  from valid_env.mpr valid_env.and_comm_with_instantiations.mp,

  have h1: calls_env σ (P₁ ⋀ P₂ ⋀ P₃) = (calltrigger.subst σ) '' calls (P₁ ⋀ P₂ ⋀ P₃), by unfold calls_env,
  have calls (P₁ ⋀ P₂ ⋀ P₃) = calls ((P₁ ⋀ P₂) ⋀ P₃), from prop.has_call.and.comm,
  have h2: calls_env σ (P₁ ⋀ P₂ ⋀ P₃) = (calltrigger.subst σ) '' calls ((P₁ ⋀ P₂) ⋀ P₃),
  from this ▸ h1,
  have calls_env σ ((P₁ ⋀ P₂) ⋀ P₃) = (calltrigger.subst σ) '' calls ((P₁ ⋀ P₂) ⋀ P₃), by unfold calls_env,
  have h_calls: calls_env σ (P₁ ⋀ P₂ ⋀ P₃) = calls_env σ ((P₁ ⋀ P₂) ⋀ P₃), from eq.trans h2 this.symm,

  have h_quantifiers:
    (∀(t₁: term) (x: var) (Q₁: prop) (h: callquantifier.mk t₁ x Q₁ ∈ quantifiers ((P₁ ⋀ P₂) ⋀ P₃)),
                          have Q₁.size < ((P₁ ⋀ P₂) ⋀ P₃).size, from quantifiers_smaller_than_prop.left h,
    ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers (P₁ ⋀ P₂ ⋀ P₃) ∧
                          (∀v: value, dominates' Q₁ Q₂ (σ[x↦v]))), from (

    assume (t₁: term) (x:var) (Q₁: prop),
    assume t₁_Q₁_in_c: callquantifier.mk t₁ x Q₁ ∈ quantifiers ((P₁ ⋀ P₂) ⋀ P₃),
    have quantifiers ((P₁ ⋀ P₂) ⋀ P₃) = quantifiers (P₁ ⋀ P₂ ⋀ P₃), from prop.has_quantifier.and.comm.symm,
    have t₁_Q₁_in: callquantifier.mk t₁ x Q₁ ∈ quantifiers (P₁ ⋀ P₂ ⋀ P₃), from this ▸ t₁_Q₁_in_c,
    have (∀v: value, dominates' Q₁ Q₁ (σ[x↦v])), from (
      assume v: value,
      dominates_self
    ),

    show ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers (P₁ ⋀ P₂ ⋀ P₃) ∧
                                  (∀v: value, dominates' Q₁ Q₂ (σ[x↦v])),
    from exists.intro t₁ (exists.intro Q₁ ⟨t₁_Q₁_in, this⟩)
  ),

  show dominates σ (P₁ ⋀ P₂ ⋀ P₃) ((P₁ ⋀ P₂) ⋀ P₃), from dominates_of h_impl h_calls h_quantifiers

lemma dominates.trans: ∀ {P₁ P₂ P₃: prop} {σ: env},
      dominates σ P₁ P₂ → dominates σ P₂ P₃ → dominates σ P₁ P₃
| P₁ P₂ P₃ σ :=
  assume h1: dominates σ P₁ P₂,
  have dominates' P₂ P₁ σ, from h1,
  have h2:
    ((σ ⊨ vc.implies P₁.instantiated_n P₂.instantiated_n) ∧
    (calls_env σ P₁ = calls_env σ P₂) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P₂),
                          have Q'.size < P₂.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers P₁ ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v])))),
  by { unfold1 dominates' at this, from this },

  assume h3: dominates σ P₂ P₃,
  have dominates' P₃ P₂ σ, from h3,
  have h4:
    ((σ ⊨ vc.implies P₂.instantiated_n P₃.instantiated_n) ∧
    (calls_env σ P₂ = calls_env σ P₃) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P₃),
                          have Q'.size < P₃.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers P₂ ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v])))),
  by { unfold1 dominates' at this, from this },


  have h_impl: σ ⊨ vc.implies P₁.instantiated_n P₃.instantiated_n,
  from valid_env.implies.trans h2.left h4.left,

  have h_calls: calls_env σ P₁ = calls_env σ P₃, from eq.trans h2.right.left h4.right.left,

  have h_quantifiers:
    (∀(t₃: term) (x: var) (Q₃: prop) (h: callquantifier.mk t₃ x Q₃ ∈ quantifiers P₃),
                          have Q₃.size < P₃.size, from quantifiers_smaller_than_prop.left h,
    ∃(t₁: term) (Q₁: prop), callquantifier.mk t₁ x Q₁ ∈ quantifiers P₁ ∧
                          (∀v: value, dominates' Q₃ Q₁ (σ[x↦v]))), from (

    assume (t₃: term) (x:var) (Q₃: prop),
    assume h5: callquantifier.mk t₃ x Q₃ ∈ quantifiers P₃,
    have ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers P₂ ∧
                          (∀v: value, dominates' Q₃ Q₂ (σ[x↦v])),
    from h4.right.right t₃ x Q₃ h5,
    let ⟨t₂, Q₂, ⟨t₂_Q₂_in_P₂, Q₃_dom_Q₂⟩⟩ := this in
    have ∃(t₁: term) (Q₁: prop), callquantifier.mk t₁ x Q₁ ∈ quantifiers P₁ ∧
                          (∀v: value, dominates' Q₂ Q₁ (σ[x↦v])),
    from h2.right.right t₂ x Q₂ t₂_Q₂_in_P₂,
    let ⟨t₁, Q₁, ⟨t₁_Q₁_in_P₁, Q₂_dom_Q₁⟩⟩ := this in
    have Q₃_dom_Q₁: (∀v: value, dominates' Q₃ Q₁ (σ[x↦v])), from (
      assume v: value,
      have h6: dominates (σ[x↦v]) Q₁ Q₂, from Q₂_dom_Q₁ v,
      have h7: dominates (σ[x↦v]) Q₂ Q₃, from Q₃_dom_Q₂ v,
      have Q₁.size < P₁.size, from quantifiers_smaller_than_prop.left t₁_Q₁_in_P₁,
      show dominates (σ[x↦v]) Q₁ Q₃, from dominates.trans h6 h7
    ),

    show ∃(t₁: term) (Q₁: prop), callquantifier.mk t₁ x Q₁ ∈ quantifiers P₁ ∧
                                 (∀v: value, dominates' Q₃ Q₁ (σ[x↦v])),
    from exists.intro t₁ (exists.intro Q₁ ⟨t₁_Q₁_in_P₁, Q₃_dom_Q₁⟩)
  ),
  show dominates σ P₁ P₃, from dominates_of h_impl h_calls h_quantifiers

lemma dominates_not_not: ∀ {P: prop} {σ: env}, dominates σ P.not.not P
| P σ :=
  have h_impl: σ ⊨ vc.implies P.not.not.instantiated_n P.instantiated_n, from valid_env.mpr (
    assume h1: σ ⊨ P.not.not.instantiated_n,
    have P.not.not.instantiated_n = P.not.instantiated.not, from not_dist_instantiated_n,
    have h2: σ ⊨ P.not.instantiated.not, from this ▸ h1,
    have P.not.instantiated = P.instantiated_n.not, from not_dist_instantiated,
    have σ ⊨ P.instantiated_n.not.not, from this ▸ h2,
    show σ ⊨ P.instantiated_n, from valid_env.neg_neg.mp this
  ),
  have h_calls: calls_env σ P.not.not = calls_env σ P, from set.eq_of_subset_of_subset (
    assume c: calltrigger,
    assume : c ∈ calls_env σ P.not.not,
    have c ∈ calls_n_env σ P.not, from prop.has_call_env.not.inv this,
    show c ∈ calls_env σ P, from prop.has_call_n_env.not.inv this
  )
  (
    assume c: calltrigger,
    assume : c ∈ calls_env σ P,
    have c ∈ calls_n_env σ P.not, from prop.has_call_env.not this,
    show c ∈ calls_env σ P.not.not, from prop.has_call_n_env.not this
  ),
  have h_quantifiers:
    (∀(t': term) (x: var) (Q₁: prop) (h: callquantifier.mk t' x Q₁ ∈ quantifiers P),
                          have Q₁.size < P.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers P.not.not ∧
                          (∀v: value, dominates' Q₁ Q₂ (σ[x↦v]))), from (
    assume (t₁: term) (x:var) (Q₁: prop),
    assume h: callquantifier.mk t₁ x Q₁ ∈ quantifiers P,
    have callquantifier.mk t₁ x Q₁ ∈ quantifiers_n P.not, from prop.has_quantifier_n.not h,
    have h2: callquantifier.mk t₁ x Q₁ ∈ quantifiers P.not.not, from prop.has_quantifier.not this,
    have Q₁.size < P.size, from quantifiers_smaller_than_prop.left h,
    have (∀v: value, dominates' Q₁ Q₁ (σ[x↦v])), from (
      assume v: value,
      dominates_self
    ),
    exists.intro t₁ (exists.intro Q₁ ⟨h2, this⟩)
  ),
  show dominates σ P.not.not P, from dominates_of h_impl h_calls h_quantifiers

lemma dominates_of_not_not: ∀ {P: prop} {σ: env}, dominates σ P P.not.not
| P σ :=
  have h_impl: σ ⊨ vc.implies P.instantiated_n P.not.not.instantiated_n, from valid_env.mpr (
    assume : σ ⊨ P.instantiated_n,
    have h1: σ ⊨ P.instantiated_n.not.not, from valid_env.neg_neg.mpr this,
    have P.not.instantiated = P.instantiated_n.not, from not_dist_instantiated,
    have h2: σ ⊨ P.not.instantiated.not, from this.symm ▸ h1,
    have P.not.not.instantiated_n = P.not.instantiated.not, from not_dist_instantiated_n,
    show σ ⊨ P.not.not.instantiated_n, from this.symm ▸ h2
  ),
  have h_calls: calls_env σ P = calls_env σ P.not.not, from set.eq_of_subset_of_subset (
    assume c: calltrigger,
    assume : c ∈ calls_env σ P,
    have c ∈ calls_n_env σ P.not, from prop.has_call_env.not this,
    show c ∈ calls_env σ P.not.not, from prop.has_call_n_env.not this
  )
  (
    assume c: calltrigger,
    assume : c ∈ calls_env σ P.not.not,
    have c ∈ calls_n_env σ P.not, from prop.has_call_env.not.inv this,
    show c ∈ calls_env σ P, from prop.has_call_n_env.not.inv this
  ),
  have h_quantifiers:
    (∀(t': term) (x: var) (Q₁: prop) (h: callquantifier.mk t' x Q₁ ∈ quantifiers P.not.not),
                          have Q₁.size < P.not.not.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers P ∧
                          (∀v: value, dominates' Q₁ Q₂ (σ[x↦v]))), from (
    assume (t₁: term) (x:var) (Q₁: prop),
    assume h: callquantifier.mk t₁ x Q₁ ∈ quantifiers P.not.not,
    have callquantifier.mk t₁ x Q₁ ∈ quantifiers_n P.not, from prop.has_quantifier.not.inv h,
    have h2: callquantifier.mk t₁ x Q₁ ∈ quantifiers P, from prop.has_quantifier_n.not.inv this,
    have Q₁.size < P.size, from quantifiers_smaller_than_prop.left h2,
    have (∀v: value, dominates' Q₁ Q₁ (σ[x↦v])), from (
      assume v: value,
      dominates_self
    ),
    exists.intro t₁ (exists.intro Q₁ ⟨h2, this⟩)
  ),
  show dominates σ P P.not.not, from dominates_of h_impl h_calls h_quantifiers

lemma strengthen_impl_with_dominating_instantiations {σ: env} {P P' Q: prop}:
  dominates σ P' P → σ ⊨ vc.implies (prop.implies P Q).instantiated (prop.implies P' Q).instantiated :=
  assume P'_dominates_P: dominates σ P' P,
  show σ ⊨ vc.implies (prop.implies P Q).instantiated (prop.implies P' Q).instantiated, from valid_env.mpr (
    assume : σ ⊨ (P.not ⋁ Q).instantiated,
    have h1: σ ⊨ (P.not ⋁ Q).instantiated.not.not, from valid_env.neg_neg.mpr this,
    have (P.not ⋁ Q).not.instantiated_n = (P.not ⋁ Q).instantiated.not, from not_dist_instantiated_n,
    have h2: σ ⊨ (P.not ⋁ Q).not.instantiated_n.not, from this.symm ▸ h1,
    have h3: σ ⊨ vc.implies (P'.not ⋁ Q).not.instantiated_n (P.not ⋁ Q).not.instantiated_n, from valid_env.mpr (
      assume : σ ⊨ (P'.not ⋁ Q).not.instantiated_n,
      have h4: σ ⊨ (P'.not.not ⋀ Q.not).instantiated_n, from valid_env.or_not_dist_with_instantiations.mp this,
      have dominates σ P'.not.not P', from dominates_not_not,
      have σ ⊨ vc.implies (P'.not.not ⋀ Q.not).instantiated_n (P' ⋀ Q.not).instantiated_n,
      from valid_env.strengthen_and_with_dominating_instantiations this,
      have h5: σ ⊨ (P' ⋀ Q.not).instantiated_n, from valid_env.mp this h4,
      have σ ⊨ vc.implies (P' ⋀ Q.not).instantiated_n (P ⋀ Q.not).instantiated_n,
      from valid_env.strengthen_and_with_dominating_instantiations P'_dominates_P,
      have h6: σ ⊨ (P ⋀ Q.not).instantiated_n, from valid_env.mp this h5,
      have dominates σ P P.not.not, from dominates_of_not_not,
      have σ ⊨ vc.implies (P ⋀ Q.not).instantiated_n (P.not.not ⋀ Q.not).instantiated_n,
      from valid_env.strengthen_and_with_dominating_instantiations this,
      have σ ⊨ (P.not.not ⋀ Q.not).instantiated_n, from valid_env.mp this h6,
      show σ ⊨ (P.not ⋁ Q).not.instantiated_n, from valid_env.or_not_dist_with_instantiations.mpr this
    ),
    have h9: σ ⊨ (P'.not ⋁ Q).not.instantiated_n.not, from valid_env.mt h3 h2,
    have (P'.not ⋁ Q).not.instantiated_n = (P'.not ⋁ Q).instantiated.not, from not_dist_instantiated_n,
    have σ ⊨ (P'.not ⋁ Q).instantiated.not.not, from this ▸ h9,
    show σ ⊨ (P'.not ⋁ Q).instantiated, from valid_env.neg_neg.mp this
  )

lemma strengthen_vc {P P' Q S: prop} {σ: env}:
  dominates σ P' P → (σ ⊨ (prop.implies (P ⋀ Q) S).instantiated) → σ ⊨ (prop.implies (P' ⋀ Q) S).instantiated :=
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
             σ ⊨ prop.instantiated (prop.implies (P' ⋀ ↑(spec.func ↑f x R S) ⋀ R ⋀ Q₁ (term.app ↑f ↑x)) ↑S),
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
             σ ⊨ prop.instantiated (prop.implies P' (prop.pre₁ op x)),
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
             σ ⊨ prop.instantiated (prop.implies P' (prop.pre₂ op x y)),
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
             σ ⊨ prop.instantiated (prop.implies (P' ⋀ prop.call f x) (term.unop unop.isFunc f ⋀ prop.pre f x)),
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
             σ ⊨ prop.instantiated (prop.implies P' (term.unop unop.isBool x)),
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

lemma exp.preservation {H: history} {σ σ': env} {P P': prop} {e e': exp} {Q Q': propctx}:
      (⊢ σ : P) → (H ⋀ P ⊢ e : Q) → ((H, σ, e) ⟶ (H, σ', e')) → (⊢ σ' : P') ∧ (H ⋀ P' ⊢ e' : Q') :=
  sorry

theorem preservation {s s': stack}: (⊢ₛ s) → (s ⟶ s') → (⊢ₛ s') :=
  assume s_verified:  ⊢ₛ s,
  assume s_steps: s ⟶ s',
  begin
    cases s_verified,
    case stack.vcgen.top σ e H Q P σ_verified e_verified {
      cases s_steps,
      case step.tru x e { from
        have (⊢ (σ[x↦value.true]) : P) ∧ (H ⋀ P ⊢ e : Q), from exp.preservation σ_verified e_verified s_steps,
        show ⊢ₛ (H, σ[x↦value.true], e), from stack.vcgen.top this.left this.right
      },
      case step.fals x e { from
        have (⊢ (σ[x↦value.false]) : P) ∧ (H ⋀ P ⊢ e : Q), from exp.preservation σ_verified e_verified s_steps,
        show ⊢ₛ (H, σ[x↦value.false], e), from stack.vcgen.top this.left this.right
      },
      case step.num n e x { from
        have (⊢ (σ[x↦value.num n]) : P) ∧ (H ⋀ P ⊢ e : Q), from exp.preservation σ_verified e_verified s_steps,
        show ⊢ₛ (H, σ[x↦value.num n], e), from stack.vcgen.top this.left this.right
      },
      case step.closure R S f x e₁ e₂ { from
        have (⊢ (σ[f↦value.func f x R S e₁ H σ]) : P) ∧ (H ⋀ P ⊢ e₂ : Q), from exp.preservation σ_verified e_verified s_steps,
        show ⊢ₛ (H, σ[f↦value.func f x R S e₁ H σ], e₂), from stack.vcgen.top this.left this.right,
      },
      case step.unop op x y e { from
        have (⊢ (σ[y↦v]) : P) ∧ (H ⋀ P ⊢ e : Q), from exp.preservation σ_verified e_verified s_steps,
        show ⊢ₛ (H, σ[y↦v], e), from stack.vcgen.top this.left this.right
      },
      case step.binop op x y z e { from
        have (⊢ (σ[z↦v]) : P) ∧ (H ⋀ P ⊢ e : Q), from exp.preservation σ_verified e_verified s_steps,
        show ⊢ₛ (H, σ[z↦v], e), from stack.vcgen.top this.left this.right
      },
      case step.app f x y S H₂ g σ₂ R gx e₁ e₂ vₓ f_is_func x_is_vₓ {
        cases e_verified,
        case exp.vcgen.app Q f_free x_free y_not_free e₂_verified func_vc { from

          have h5: ⊢ₛ (H₂, σ₂[g↦value.func g gx R S e₁ H₂ σ₂][gx↦vₓ], e₁), from (

            have ∃σ' Q', ⊢ (σ'[f ↦ value.func g gx R S e₁ H₂ σ₂]) : Q',
            from env.vcgen.inv σ_verified f_is_func,
            let ⟨σ', Q', ha1⟩ := this in

            have ∃Q₁ Q₂ Q₃,
              f ∉ σ' ∧
              g ∉ σ₂ ∧
              gx ∉ σ₂ ∧
              g ≠ gx ∧
              (⊢ σ' : Q₁) ∧
              (⊢ σ₂ : Q₂) ∧
              gx ∈ FV R.to_prop ∧
              FV R.to_prop ⊆ FV Q₂ ∪ { g, gx } ∧
              FV S.to_prop ⊆ FV Q₂ ∪ { g, gx } ∧
              (H₂ ⋀ Q₂ ⋀ spec.func g gx R S ⋀ R ⊢ e₁ : Q₃) ∧
              ⟪prop.implies (H₂ ⋀ Q₂ ⋀ spec.func g gx R S ⋀ R ⋀ Q₃ (term.app g gx)) S⟫ ∧
              (Q' = (Q₁ ⋀
                  ((f ≡ (value.func g gx R S e₁ H₂ σ₂)) ⋀
                  prop.subst_env (σ₂[g↦value.func g gx R S e₁ H₂ σ₂])
                  (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))))),
            from env.vcgen.func.inv ha1,

            let ⟨Q₁, Q₂, Q₃, ha2⟩ := this in
            let Q₂' := (Q₂ ⋀
                  ((g ≡ (value.func g gx R S e₁ H₂ σ₂)) ⋀
                  prop.subst_env (σ₂[g↦value.func g gx R S e₁ H₂ σ₂])
                  (prop.func g gx R (Q₃ (term.app g gx) ⋀ S)))) in

            have ha3: ⊢ (σ₂[g↦value.func g gx R S e₁ H₂ σ₂]) : Q₂',
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

            have gx ∉ (σ₂[g↦value.func g gx R S e₁ H₂ σ₂]), from (
              assume : gx ∈ (σ₂[g↦value.func g gx R S e₁ H₂ σ₂]),
              or.elim (env.contains.inv this) (
                assume : gx = g,
                show «false», from ha2.right.right.right.left this.symm
              ) (
                assume : gx ∈ σ₂,
                show «false», from ha2.right.right.left this
              )
            ),
            have ∃P₃, ⊢ (σ₂[g↦value.func g gx R S e₁ H₂ σ₂][gx↦vₓ]) : P₃,
            from env.vcgen.copy ha3 this ha4,
            let ⟨P₃, ha5⟩ := this in

            have ha6: H₂ ⋀ Q₂ ⋀ spec.func g gx R S ⋀ R ⊢ e₁ : Q₃,
            from ha2.right.right.right.right.right.right.right.right.right.left,

            have ha7: FV (↑H₂ ⋀ P₃) = FV (↑H₂ ⋀ Q₂ ⋀ spec.func g gx R S ⋀ R), from (
              have ha8: FV P₃ = FV (Q₂ ⋀ spec.func g gx R S ⋀ R), from (
                have hb1: FV P₃ = (σ₂[g↦value.func g gx R S e₁ H₂ σ₂][gx↦vₓ]).dom, from (free_iff_contains ha5).symm,
                have hb2: (σ₂[g↦value.func g gx R S e₁ H₂ σ₂][gx↦vₓ]).dom
                        = (σ₂[g↦value.func g gx R S e₁ H₂ σ₂]).dom ∪ set.insert gx ∅, from env.dom.inv,
                have hb3: (σ₂[g↦value.func g gx R S e₁ H₂ σ₂]).dom
                        = σ₂.dom ∪ set.insert g ∅, from env.dom.inv,
                have hb4: FV P₃ = σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅, from eq.trans hb1 (hb3 ▸ hb2),

                let forallp := (prop.implies R.to_prop (prop.pre g gx)
                              ⋀ prop.implies (prop.post g gx) S.to_prop) in

                have hb5: FV (Q₂ ⋀ spec.func g gx R S ⋀ R) = σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅,
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

                  assume : x ∈ FV (Q₂ ⋀ spec.func g gx R S ⋀ R),

                  or.elim (free_in_prop.and.inv this) (
                    assume hb2: x ∈ FV Q₂,
                    have FV Q₂ = σ₂.dom, from (free_iff_contains ha2.right.right.right.right.right.left).symm,
                    have x ∈ σ₂.dom, from this ▸ hb2,
                    have x ∈ σ₂.dom ∪ set.insert g ∅, from set.mem_union_left (set.insert g ∅) this,
                    show x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅,
                    from set.mem_union_left (set.insert gx ∅) this
                  ) (
                    assume : x ∈ FV (prop.func g gx R S ⋀ R),
                    or.elim (free_in_prop.and.inv this) (
                      assume : x ∈ FV (prop.func g gx R S),
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
                            assume : free_in_prop x (prop.implies R.to_prop (prop.pre g gx)),
                            or.elim (free_in_prop.implies.inv this) (
                              assume : x ∈ FV R.to_prop,
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
                            assume : free_in_prop x (prop.implies (prop.post g gx) S.to_prop),
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
                              assume : free_in_prop x S.to_prop,
                              have x ∈ FV Q₂ ∪ {g, gx},
                              from set.mem_of_mem_of_subset this
                                   ha2.right.right.right.right.right.right.right.right.left,
                              show x ∈ σ₂.dom ∪ set.insert g ∅ ∪ set.insert gx ∅, from hb6 this
                            )
                          )
                        )
                      ) 
                    ) (
                      assume : x ∈ FV R.to_prop,
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
                      show x ∈ FV (Q₂ ⋀ spec.func g gx R S ⋀ R), from free_in_prop.and₁ this
                    ) (
                      assume : x ∈ set.insert g ∅,
                      have x = g, from (set.mem_singleton_iff x g).mp this,
                      have free_in_term x g, from this ▸ free_in_term.var x,
                      have free_in_term x (term.unop unop.isFunc g), from free_in_term.unop this,
                      have free_in_prop x (term.unop unop.isFunc g), from free_in_prop.term this,
                      have x ∈ FV (prop.func g gx R S), from free_in_prop.and₁ this,
                      have x ∈ FV (prop.func g gx R S ⋀ R), from free_in_prop.and₁ this,
                      show x ∈ FV (Q₂ ⋀ spec.func g gx R S ⋀ R), from free_in_prop.and₂ this
                    )
                  ) (
                    assume : x ∈ set.insert gx ∅,
                    have x = gx, from (set.mem_singleton_iff x gx).mp this,
                    have x ∈ FV R.to_prop,
                    from this.symm ▸ ha2.right.right.right.right.right.right.left,
                    have x ∈ FV (prop.func g gx R S ⋀ R), from free_in_prop.and₂ this,
                    show x ∈ FV (Q₂ ⋀ spec.func g gx R S ⋀ R), from free_in_prop.and₂ this
                  )
                ),

                show FV P₃ = FV (Q₂ ⋀ spec.func g gx R S ⋀ R), from eq.trans hb4 hb5.symm
              ),
              show FV (↑H₂ ⋀ P₃) = FV (↑H₂ ⋀ Q₂ ⋀ spec.func g gx R S ⋀ R), by calc
                   FV (↑H₂ ⋀ P₃) = FV (P₃ ⋀ ↑H₂) : free_in_prop.and_symm
                             ... = FV ((Q₂ ⋀ spec.func g gx R S ⋀ R) ⋀ ↑H₂) : same_free_and_left ha8
                             ... = FV (↑H₂ ⋀ Q₂ ⋀ spec.func g gx R S ⋀ R) : free_in_prop.and_symm
            ),

            have ∀σ, dominates σ (H₂ ⋀ P₃) (H₂ ⋀ Q₂ ⋀ spec.func g gx R S ⋀ R), from (
              assume σ: env,

              have hb1: dominates σ P₃ (Q₂ ⋀ spec.func g gx R S ⋀ R), from (
                sorry
              ),

              have hb2: dominates σ (↑H₂ ⋀ P₃) (P₃ ⋀ ↑H₂), from dominates_and_symm,
              have dominates σ (P₃ ⋀ ↑H₂) ((Q₂ ⋀ spec.func g gx R S ⋀ R) ⋀ ↑H₂),
              from dominates_and_left hb1,
              have hb3: dominates σ (↑H₂ ⋀ P₃) ((Q₂ ⋀ spec.func g gx R S ⋀ R) ⋀ ↑H₂),
              from dominates.trans hb2 this,
              have dominates σ ((Q₂ ⋀ spec.func g gx R S ⋀ R) ⋀ ↑H₂) (↑H₂ ⋀ Q₂ ⋀ spec.func g gx R S ⋀ R),
              from dominates_and_symm,
              show dominates σ (H₂ ⋀ P₃) (H₂ ⋀ Q₂ ⋀ spec.func g gx R S ⋀ R),
              from dominates.trans hb3 this
            ),
            have ha9: H₂ ⋀ P₃ ⊢ e₁ : Q₃,
            from strengthen_exp ha6 (H₂ ⋀ P₃) ha7 this,

            show ⊢ₛ (H₂, σ₂[g↦value.func g gx R S e₁ H₂ σ₂][gx↦vₓ], e₁),
            from stack.vcgen.top ha5 ha9
          ),

          have h6: y ∉ σ, from (
            have y ∉ FV P, from (
              assume : y ∈ FV P,
              have y ∈ FV (↑H ⋀ P), from free_in_prop.and₂ this,
              show «false», from y_not_free this
            ),
            show y ∉ σ, from mt (free_of_contains σ_verified) this
          ),

          have h7: (H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⊢ e₂ : Q), from (
            have ha1: FV (↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                   =  FV ((↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x), from free_in_prop.and_comm,
            have ∀σ, dominates σ (↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                             ((↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x), from (
              assume σ: env,
              show dominates σ (↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                               ((↑H ⋀ P) ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
              from dominates_and_comm
            ),
            show (↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⊢ e₂ : Q),
            from strengthen_exp e₂_verified (↑H ⋀ P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) ha1 this
          ),

          have h8: ⟪ prop.implies (↑H ⋀ P ⋀ prop.call f x) (↑(term.unop unop.isFunc f) ⋀ prop.pre f x) ⟫, from (
            assume σ: env,
            have ha0: σ ⊨ (((↑H ⋀ P) ⋀ prop.call f x).not ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated,
            from func_vc σ,

            have ha1: no_instantiations (term.unop unop.isFunc f), from no_instantiations.term,
            have ha2: no_instantiations (prop.pre f x), from no_instantiations.pre,
            have ha3: no_instantiations (↑(term.unop unop.isFunc f) ⋀ prop.pre f x), from no_instantiations.and ha1 ha2,
            have (((↑H ⋀ P) ⋀ prop.call f x).not ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated
               = (((↑H ⋀ P) ⋀ prop.call f x).not.instantiated ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased),
            from or_dist_of_no_instantiations ha3,
            have σ ⊨ (((↑H ⋀ P) ⋀ prop.call f x).not.instantiated ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased),
            from this ▸ ha0,
            or.elim (valid_env.or.elim this) (
              assume ha4: σ ⊨ ((↑H ⋀ P) ⋀ prop.call f x).not.instantiated,
              have ((↑H ⋀ P) ⋀ prop.call f x).not.instantiated = ((↑H ⋀ P) ⋀ prop.call f x).instantiated_n.not,
              from not_dist_instantiated,
              have σ ⊨ ((↑H ⋀ P) ⋀ prop.call f x).instantiated_n.not, from this ▸ ha4,
              have ha5: σ ⊨ (↑H ⋀ P ⋀ prop.call f x).instantiated_n.not, from valid_env.mt (valid_env.mpr (
                assume : σ ⊨ (↑H ⋀ P ⋀ prop.call f x).instantiated_n,
                show σ ⊨ ((↑H ⋀ P) ⋀ prop.call f x).instantiated_n, from valid_env.and_comm_with_instantiations.mp this
              )) this,
              have (↑H ⋀ P ⋀ prop.call f x).not.instantiated = (↑H ⋀ P ⋀ prop.call f x).instantiated_n.not,
              from not_dist_instantiated,
              have σ ⊨ (↑H ⋀ P ⋀ prop.call f x).not.instantiated, from this.symm ▸ ha5,

              have ha6: σ ⊨ ((↑H ⋀ P ⋀ prop.call f x).not.instantiated ⋁
                        (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased),
              from valid_env.or₁ this,

              have ((↑H ⋀ P ⋀ prop.call f x).not ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated
                = ((↑H ⋀ P ⋀ prop.call f x).not.instantiated ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased),
              from or_dist_of_no_instantiations ha3,

              have σ ⊨ ((↑H ⋀ P ⋀ prop.call f x).not ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated,
              from this.symm ▸ ha6,
              show σ ⊨ (prop.implies (H ⋀ P ⋀ prop.call f x) (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated,
              from this
            ) (
              assume : σ ⊨ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased,
              have ha4: σ ⊨ ((↑H ⋀ P ⋀ prop.call f x).not.instantiated ⋁
                        (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased),
              from valid_env.or₂ this,

              have ((↑H ⋀ P ⋀ prop.call f x).not ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated
                = ((↑H ⋀ P ⋀ prop.call f x).not.instantiated ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased),
              from or_dist_of_no_instantiations ha3,

              have σ ⊨ ((↑H ⋀ P ⋀ prop.call f x).not ⋁ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated,
              from this.symm ▸ ha4,
              show σ ⊨ (prop.implies (H ⋀ P ⋀ prop.call f x) (↑(term.unop unop.isFunc f) ⋀ prop.pre f x)).instantiated,
              from this
            )
          ),

          have h9: (H₂, σ₂[g↦value.func g gx R S e₁ H₂ σ₂][gx↦vₓ], e₁)
              ⟶* (H₂, σ₂[g↦value.func g gx R S e₁ H₂ σ₂][gx↦vₓ], e₁),
          from trans_step.rfl,

          show ⊢ₛ ((H₂, σ₂[g↦value.func g gx R S e₁ H₂ σ₂][gx↦vₓ], e₁) · [H, σ, let y = f[x] in e₂]),
          from stack.vcgen.cons h5 σ_verified f_is_func x_is_vₓ h6 h7 h8 h9
        }
      },
      case step.ite_true x e₁ e₂ { from
        have (⊢ σ : P) ∧ (H ⋀ P ⊢ e₂ : Q), from exp.preservation σ_verified e_verified s_steps,
        show ⊢ₛ (H, σ, e₂), from stack.vcgen.top this.left this.right
      },
      case step.ite_false x e₁ e₂ { from
        have (⊢ σ : P) ∧ (H ⋀ P ⊢ e₁ : Q), from exp.preservation σ_verified e_verified s_steps,
        show ⊢ₛ (H, σ, e₁), from stack.vcgen.top this.left this.right
      }
    },
    case stack.vcgen.cons {-- H P s' σ σ' f g x y fx R S e vₓ Q s'_verified _ g_is_func x_is_v _ cont _ _ ih {
      cases s_steps,
      admit,
      admit
    }
  end
