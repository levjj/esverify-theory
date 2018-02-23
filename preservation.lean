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
    or.elim (has_call_env.and.inv this) (
      assume : c ∈ calls_env σ P',
      have c ∈ calls_env σ P, from calls_P'_P ▸ this,
      show c ∈ calls_env σ (P ⋀ Q), from has_call_env.and₁ this
    )
    (
      assume : c ∈ calls_env σ Q,
      show c ∈ calls_env σ (P ⋀ Q), from has_call_env.and₂ this
    )
  )
  (
    assume c: calltrigger,
    assume : c ∈ calls_env σ (P ⋀ Q),
    or.elim (has_call_env.and.inv this) (
      assume : c ∈ calls_env σ P,
      have c ∈ calls_env σ P', from calls_P'_P.symm ▸ this,
      show c ∈ calls_env σ (P' ⋀ Q), from has_call_env.and₁ this
    )
    (
      assume : c ∈ calls_env σ Q,
      show c ∈ calls_env σ (P' ⋀ Q), from has_call_env.and₂ this
    )
  )

lemma same_quantifiers_and_left {P P' Q: prop} {σ: env}:
      qualifiers_dominate σ P' P → qualifiers_dominate σ (P' ⋀ Q) (P ⋀ Q) :=
  assume P'_dominates_P: qualifiers_dominate σ P' P,
  assume (t₁: term) (x:var) (Q₁: prop),
  assume : callquantifier.mk t₁ x Q₁ ∈ quantifiers (P ⋀ Q),
  or.elim (has_quantifier.and.inv this) (
    assume : callquantifier.mk t₁ x Q₁ ∈ quantifiers P,
    have ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers P' ∧
        ∀v: value, σ[x↦v] ⊨ vc.implies Q₂.instantiated Q₁.instantiated,
    from P'_dominates_P t₁ x Q₁ this,
    let ⟨t₂, Q₂, ⟨call_t₂_Q₂_in_P', Q₂_impl_Q₁⟩⟩ := this in
    have callquantifier.mk t₂ x Q₂ ∈ quantifiers (P' ⋀ Q), from has_quantifier.and₁ call_t₂_Q₂_in_P',
    show ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers (P' ⋀ Q) ∧
        ∀v: value, σ[x↦v] ⊨ vc.implies Q₂.instantiated Q₁.instantiated,
    from exists.intro t₂ (exists.intro Q₂ ⟨this, Q₂_impl_Q₁⟩)
  ) (
    assume : callquantifier.mk t₁ x Q₁ ∈ quantifiers Q,
    have h1: callquantifier.mk t₁ x Q₁ ∈ quantifiers (P' ⋀ Q), from has_quantifier.and₂ this,
    have h2: ∀v: value, σ[x↦v] ⊨ vc.implies Q₁.instantiated Q₁.instantiated, from (
      assume v: value,
      show σ[x↦v] ⊨ vc.implies Q₁.instantiated Q₁.instantiated, from valid_env.mpr id
    ),
    show ∃(t₂: term) (Q₂: prop), callquantifier.mk t₂ x Q₂ ∈ quantifiers (P' ⋀ Q) ∧
        ∀v: value, σ[x↦v] ⊨ vc.implies Q₂.instantiated Q₁.instantiated,
    from exists.intro t₁ (exists.intro Q₁ ⟨h1, h2⟩)
  )

lemma dominates_and_left {P P' Q: prop}:
      (∀σ, dominates σ P' P) → (∀σ, dominates σ (P' ⋀ Q) (P ⋀ Q)) :=
  assume h: ∀σ, dominates σ P' P,
  assume σ: env,
  have calls_env σ P' = calls_env σ P, from (h σ).left,
  have h_calls: calls_env σ (P' ⋀ Q) = calls_env σ (P ⋀ Q), from same_calls_and_left this,
  have qualifiers_dominate σ P' P, from (h σ).right.left,
  have h_quantifiers: qualifiers_dominate σ (P' ⋀ Q) (P ⋀ Q), from same_quantifiers_and_left this,
  have σ ⊨ vc.implies P'.instantiated_n P.instantiated_n, from (h σ).right.right,
  have h_impl: σ ⊨ vc.implies (P' ⋀ Q).instantiated_n (P ⋀ Q).instantiated_n,
  from valid_env.strengthen_and_with_dominating_instantiations (h σ),
  ⟨h_calls, ⟨h_quantifiers, h_impl⟩⟩

lemma strengthen_pre_exp {P: prop} {Q: propctx} {e: exp}:
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
      from dominates_and_left P'_dominates_P,
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
      from dominates_and_left P'_dominates_P,
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
      from dominates_and_left P'_dominates_P,
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
      from dominates_and_left P'_dominates_P,
      have e₁_verified': P' ⋀ (spec.func f x R S) ⋀ R ⊢ e₁ : Q₁,
      from ih₁ (P' ⋀ (spec.func f x R S) ⋀ R) h1 h2,

      have h3: FV (P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)))
             = FV (P ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S))),
      from same_free_and_left free_P'_P,
      have h4: (∀σ, dominates σ (P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)))
                                (P ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)))),
      from dominates_and_left P'_dominates_P,
      have e₂_verified': P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)) ⊢ e₂ : Q₂,
      from ih₂ (P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S))) h3 h4,

      have func_vc': ∀ (σ : env),
             σ ⊨ prop.instantiated (prop.implies (P' ⋀ ↑(spec.func ↑f x R S) ⋀ R ⋀ Q₁ (term.app ↑f ↑x)) ↑S),
      from (
        assume σ: env,

        have dominates σ (prop.or (P' ⋀ ↑(spec.func ↑f x R S) ⋀ R ⋀ Q₁ (term.app ↑f ↑x)).not
        
         ↑S).instantiated,


        show σ ⊨ (prop.or (P' ⋀ ↑(spec.func ↑f x R S) ⋀ R ⋀ Q₁ (term.app ↑f ↑x)).not ↑S).instantiated,
        from sorry
      ),

      show P' ⊢ letf f[x] req R ens S {e₁} in e₂ : propctx.exis f (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S) ⋀ Q₂),
      from exp.vcgen.func f_not_free_in_P' x_not_free_in_P' f_neq_x fv_R' fv_S' e₁_verified'
           e₂_verified' func_vc'
    },
    case exp.vcgen.unop op x y e' Q' x_free_in_P _ e'_verified vc_valid { from
    },
    case exp.vcgen.binop op x y z e' Q' x_free_in_P y_free_in_P _ e'_verified vc_valid { from
    },
    case exp.vcgen.app y f x e' Q' f_free_in_P x_free_in_P _ e'_verified vc_valid { from
    },
    case exp.vcgen.ite x e₂ e₁ Q₁ Q₂ x_free_in_P _ _ vc_valid { from
    },
    case exp.vcgen.return x x_free_in_P { from
    }
  end

theorem preservation {H: callhistory} {h: historyitem} {s s': stack}: (H ⊢ₛ s) → (s ⟶ h, s') → (h :: H ⊢ₛ s') :=
  sorry
