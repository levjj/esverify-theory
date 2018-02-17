import .syntax .notations .logic .evaluation .vcgen

lemma not_free_of_subset {P P': prop} {x: var}: FV P' ⊆ FV P → x ∉ FV P → x ∉ FV P' :=
  assume free_P'_P: FV P' ⊆ FV P,
  assume x_not_free_in_P: x ∉ FV P,
  have x ∈ FV P' → x ∈ FV P, from set.mem_of_subset_of_mem free_P'_P,
  have x ∉ FV P → x ∉ FV P', from mt this,
  show x ∉ FV P', from this x_not_free_in_P

lemma strengthen_and_left {σ: env} {P P' Q: prop}:
      no_instantiations Q →
      σ ⊨ vc.implies P'.instantiated_n P.instantiated_n →
      σ ⊨ vc.implies (P' && Q).instantiated_n (P && Q).instantiated_n :=
  assume no_instantiations_in_Q: no_instantiations Q,
  assume strengthen_P'_P: σ ⊨ vc.implies P'.instantiated_n P.instantiated_n,
  valid_env.mpr (
    assume h1: σ ⊨ (P' && Q).instantiated_n,
    have (P' && Q).instantiated_n = P'.instantiated_n && Q.erased,
    from and_dist_of_no_instantiations_n no_instantiations_in_Q,
    have h2: σ ⊨ (P'.instantiated_n && Q.erased), from this ▸ h1,
    have σ ⊨ P'.instantiated_n, from (valid_env.and.elim h2).left,
    have h3: σ ⊨ P.instantiated_n, from valid_env.mp strengthen_P'_P this,
    have h4: σ ⊨ Q.erased, from (valid_env.and.elim h2).right,
    have h5: σ ⊨ (P.instantiated_n && Q.erased), from valid_env.and h3 h4,
    have (P && Q).instantiated_n = P.instantiated_n && Q.erased,
    from and_dist_of_no_instantiations_n no_instantiations_in_Q,
    show σ ⊨ (P && Q).instantiated_n, from this.symm ▸ h5
  )

lemma free_and_left {P P' Q: prop}:
      FV P' ⊆ FV P →
      FV (P' && Q) ⊆ FV (P && Q) :=
  assume free_P'_P: FV P' ⊆ FV P,
  assume x,
  assume : x ∈ FV (P' && Q),
  or.elim (free_in_prop.and.inv this) (
    assume : x ∈ FV P',
    have x ∈ FV P, from set.mem_of_subset_of_mem free_P'_P this,
    show x ∈ FV (P && Q), from free_in_prop.and₁ this
  ) (
    assume : x ∈ FV Q,
    show x ∈ FV (P && Q), from free_in_prop.and₂ this
  )

lemma same_calls_P_and_t {P: prop} {t: term}: (calls (P && t) = calls P) :=
  sorry

lemma same_quantifiers_P_and_t {P: prop} {t: term}: (quantifiers (P && t) = quantifiers P) :=
  sorry

lemma strengthen_P_and_t {P: prop} {t: term} {σ: env}: σ ⊨ vc.implies (P && t).instantiated_n P.instantiated_n :=
  sorry

lemma strengthen_pre_exp {P: prop} {Q: propctx} {e: exp}:
  (P ⊢ e : Q) →
  ∀P': prop, FV P' ⊆ FV P → (calls P' = calls P) → (quantifiers P' = quantifiers P) →
       (∀σ, σ ⊨ vc.implies P'.instantiated_n P.instantiated_n) →
       (P' ⊢ e: Q) :=
  assume e_verified: (P ⊢ e : Q),
  begin
    induction e_verified,
    case exp.vcgen.tru x P e' Q x_not_free_in_P e'_verified ih { from (
      assume P': prop,
      assume free_P'_P: FV P' ⊆ FV P,
      assume strengthen_P'_P: (∀σ, σ ⊨ vc.implies P'.instantiated_n P.instantiated_n),
      have h1: FV (P' && (x ≡ value.true)) ⊆ FV (P && (x ≡ value.true)),
      from free_and_left free_P'_P,
      have x_not_free_in_P': x ∉ FV P', from not_free_of_subset free_P'_P x_not_free_in_P,
      have no_instantiations (x ≡ value.true), from no_instantiations.term,
      have h2: ∀σ, σ ⊨ vc.implies (P' && (x ≡ value.true)).instantiated_n (P && (x ≡ value.true)).instantiated_n,
      from (assume σ, strengthen_and_left this (strengthen_P'_P σ)),
      have e'_verified': P' && (x ≡ value.true) ⊢ e': Q,
      from ih (P' && (x ≡ value.true)) h1 h2,
      show P' ⊢ lett x = true in e' : propctx.exis x ((x ≡ value.true) && Q),
      from exp.vcgen.tru x_not_free_in_P' e'_verified'
    )},
    case exp.vcgen.fals x e' { from
    },
    case exp.vcgen.num x n e' { from
    },
    case exp.vcgen.func f x R S e₁ e₂ { from
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

theorem preservation {s s': stack}: (⊢ₛ s) → (s ⟶ s') → ⊢ₛ s'
:= sorry
