import .syntax .notations .logic .evaluation .vcgen

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
  have h3: 
    ((σ ⊨ vc.implies P.instantiated_n P.instantiated_n) ∧
    (calls_env σ P = calls_env σ P) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P),
                          have Q'.size < P.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers P ∧
                          (∀v: value, dominates' Q' Q₂ (σ[x↦v])))),
  from ⟨h_impl, ⟨h_calls, h_quantifiers⟩⟩,
  have
    dominates' P P σ = (
    ((σ ⊨ vc.implies P.instantiated_n P.instantiated_n) ∧
    (calls_env σ P = calls_env σ P) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P),
                          have Q'.size < P.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers P ∧
                          (∀v: value, dominates' Q' Q₂ (σ[x↦v]))))),
  by unfold1 dominates',
  have dominates' P P σ, from this.symm ▸ h3,
  show dominates σ P P, from this

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

  have h3: 
    ((σ ⊨ vc.implies (P' ⋀ Q).instantiated_n (P ⋀ Q).instantiated_n) ∧
    (calls_env σ (P' ⋀ Q) = calls_env σ (P ⋀ Q)) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers (P ⋀ Q)),
                          have Q'.size < (P ⋀ Q).size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers (P' ⋀ Q) ∧
                          (∀v: value, dominates' Q' Q₂ (σ[x↦v])))),
  from ⟨h_impl, ⟨h_calls, h_quantifiers⟩⟩,
  have
    dominates' (P ⋀ Q) (P' ⋀ Q) σ = (
    ((σ ⊨ vc.implies (P' ⋀ Q).instantiated_n (P ⋀ Q).instantiated_n) ∧
    (calls_env σ (P' ⋀ Q) = calls_env σ (P ⋀ Q)) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers (P ⋀ Q)),
                          have Q'.size < (P ⋀ Q).size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers (P' ⋀ Q) ∧
                          (∀v: value, dominates' Q' Q₂ (σ[x↦v]))))),
  by unfold1 dominates',
  have dominates' (P ⋀ Q) (P' ⋀ Q) σ, from this.symm ▸ h3,
  show dominates σ (P' ⋀ Q) (P ⋀ Q), from this

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
  have h3: 
    ((σ ⊨ vc.implies P.not.not.instantiated_n P.instantiated_n) ∧
    (calls_env σ P.not.not = calls_env σ P) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P),
                          have Q'.size < P.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers P.not.not ∧
                          (∀v: value, dominates' Q' Q₂ (σ[x↦v])))),
  from ⟨h_impl, ⟨h_calls, h_quantifiers⟩⟩,
  have
    dominates' P P.not.not σ = (
    ((σ ⊨ vc.implies P.not.not.instantiated_n P.instantiated_n) ∧
    (calls_env σ P.not.not = calls_env σ P) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P),
                          have Q'.size < P.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers P.not.not ∧
                          (∀v: value, dominates' Q' Q₂ (σ[x↦v]))))),
  by unfold1 dominates',
  have dominates' P P.not.not σ, from this.symm ▸ h3,
  show dominates σ P.not.not P, from this

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
  have h3: 
    ((σ ⊨ vc.implies P.instantiated_n P.not.not.instantiated_n) ∧
    (calls_env σ P = calls_env σ P.not.not) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P.not.not),
                          have Q'.size < P.not.not.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers P ∧
                          (∀v: value, dominates' Q' Q₂ (σ[x↦v])))),
  from ⟨h_impl, ⟨h_calls, h_quantifiers⟩⟩,
  have
    dominates' P.not.not P σ = (
    ((σ ⊨ vc.implies P.instantiated_n P.not.not.instantiated_n) ∧
    (calls_env σ P = calls_env σ P.not.not) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P.not.not),
                          have Q'.size < P.not.not.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q₂: prop), callquantifier.mk t x Q₂ ∈ quantifiers P ∧
                          (∀v: value, dominates' Q' Q₂ (σ[x↦v]))))),
  by unfold1 dominates',
  have dominates' P.not.not P σ, from this.symm ▸ h3,
  show dominates σ P P.not.not, from this

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
      have h4: σ ⊨ (P'.not.not ⋀ Q.not).instantiated_n, from valid_env.and_not_dist_with_instantiations.mp this,
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
      show σ ⊨ (P.not ⋁ Q).not.instantiated_n, from valid_env.and_not_dist_with_instantiations.mpr this
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
    case exp.vcgen.func f x R S e₁ e₂ P Q₁ Q₂ f_not_free_in_P x_not_free_in_P f_neq_x fv_R fv_S
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
      from exp.vcgen.func f_not_free_in_P' x_not_free_in_P' f_neq_x fv_R' fv_S' e₁_verified'
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

theorem preservation {H: callhistory} {h: historyitem} {s s': stack}: (H ⊢ₛ s) → (s ⟶ h, s') → (h :: H ⊢ₛ s') :=
  sorry
