import .syntax .notations .logic .evaluation .vcgen

lemma same_free_and_left {P P' Q: prop}: FV P' = FV P → (FV (P' && Q) = FV (P && Q)) :=
  assume free_P'_P: FV P' = FV P,
  set.eq_of_subset_of_subset (
    assume x,
    assume : x ∈ FV (P' && Q),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P',
      have x ∈ FV P, from free_P'_P ▸ this,
      show x ∈ FV (P && Q), from free_in_prop.and₁ this
    ) (
      assume : x ∈ FV Q,
      show x ∈ FV (P && Q), from free_in_prop.and₂ this
    )
  ) (
    assume x,
    assume : x ∈ FV (P && Q),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P,
      have x ∈ FV P', from free_P'_P.symm ▸ this,
      show x ∈ FV (P' && Q), from free_in_prop.and₁ this
    ) (
      assume : x ∈ FV Q,
      show x ∈ FV (P' && Q), from free_in_prop.and₂ this
    )
  )

lemma same_calls_and_left {P P' Q: prop}: calls P' = calls P → (calls (P' && Q) = calls (P && Q)) :=
  assume calls_P'_P: calls P' = calls P,
  set.eq_of_subset_of_subset (
    assume c: calltrigger,
    assume : c ∈ calls (P' && Q),
    or.elim (has_call.and.inv this) (
      assume : c ∈ calls P',
      have c ∈ calls P, from calls_P'_P ▸ this,
      show c ∈ calls (P && Q), from has_call.and₁ this
    )
    (
      assume : c ∈ calls Q,
      show c ∈ calls (P && Q), from has_call.and₂ this
    )
  )
  (
    assume c: calltrigger,
    assume : c ∈ calls (P && Q),
    or.elim (has_call.and.inv this) (
      assume : c ∈ calls P,
      have c ∈ calls P', from calls_P'_P.symm ▸ this,
      show c ∈ calls (P' && Q), from has_call.and₁ this
    )
    (
      assume : c ∈ calls Q,
      show c ∈ calls (P' && Q), from has_call.and₂ this
    )
  )

lemma same_quantifiers_and_left {P P' Q: prop}: quantifiers P' = quantifiers P → (quantifiers (P' && Q) = quantifiers (P && Q)) :=
  assume quantifiers_P'_P: quantifiers P' = quantifiers P,
  set.eq_of_subset_of_subset (
    assume c: callquantifier,
    assume : c ∈ quantifiers (P' && Q),
    or.elim (has_quantifier.and.inv this) (
      assume : c ∈ quantifiers P',
      have c ∈ quantifiers P, from quantifiers_P'_P ▸ this,
      show c ∈ quantifiers (P && Q), from has_quantifier.and₁ this
    )
    (
      assume : c ∈ quantifiers Q,
      show c ∈ quantifiers (P && Q), from has_quantifier.and₂ this
    )
  )
  (
    assume c: callquantifier,
    assume : c ∈ quantifiers (P && Q),
    or.elim (has_quantifier.and.inv this) (
      assume : c ∈ quantifiers P,
      have c ∈ quantifiers P', from quantifiers_P'_P.symm ▸ this,
      show c ∈ quantifiers (P' && Q), from has_quantifier.and₁ this
    )
    (
      assume : c ∈ quantifiers Q,
      show c ∈ quantifiers (P' && Q), from has_quantifier.and₂ this
    )
  )

lemma strengthen_pre_exp {P: prop} {Q: propctx} {e: exp}:
  (P ⊢ e : Q) →
  ∀P': prop, (FV P' = FV P) → (calls P' = calls P) → (quantifiers P' = quantifiers P) →
       (∀σ, σ ⊨ vc.implies P'.instantiated_n P.instantiated_n) →
       (P' ⊢ e: Q) :=
  assume e_verified: (P ⊢ e : Q),
  begin
    induction e_verified,
    case exp.vcgen.tru x P e' Q x_not_free_in_P e'_verified ih { from (
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume calls_P'_P: calls P' = calls P,
      assume quantifiers_P'_P: quantifiers P' = quantifiers P,
      assume strengthen_P'_P: (∀σ, σ ⊨ vc.implies P'.instantiated_n P.instantiated_n),
      have h1: FV (P' && (x ≡ value.true)) = FV (P && (x ≡ value.true)),
      from same_free_and_left free_P'_P,
      have h2: calls (P' && (x ≡ value.true)) = calls (P && (x ≡ value.true)),
      from same_calls_and_left calls_P'_P,
      have h3: quantifiers (P' && (x ≡ value.true)) = quantifiers (P && (x ≡ value.true)),
      from same_quantifiers_and_left quantifiers_P'_P,
      have h4: ∀σ, σ ⊨ vc.implies (P' && (x ≡ value.true)).instantiated_n (P && (x ≡ value.true)).instantiated_n,
      from (assume σ, valid_env.strengthen_without_instantiations calls_P'_P quantifiers_P'_P (strengthen_P'_P σ)),
      have e'_verified': P' && (x ≡ value.true) ⊢ e': Q,
      from ih (P' && (x ≡ value.true)) h1 h2 h3 h4,
      have x_not_free_in_P': x ∉ FV P', from free_P'_P.symm ▸ x_not_free_in_P,
      show P' ⊢ lett x = true in e' : propctx.exis x ((x ≡ value.true) && Q),
      from exp.vcgen.tru x_not_free_in_P' e'_verified'
    )},
    case exp.vcgen.fals x P e' Q x_not_free_in_P e'_verified ih { from

    },
    case exp.vcgen.num x n P e' Q x_not_free_in_P e'_verified ih { from

    },
    case exp.vcgen.func f x R S e₁ e₂ P Q₁ Q₂ f_not_free_in_P fv_R fv_S e₁_verified e₂_verified func_vc ih₁ ih₂ { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume calls_P'_P: calls P' = calls P,
      assume quantifiers_P'_P: quantifiers P' = quantifiers P,
      assume strengthen_P'_P: (∀σ, σ ⊨ vc.implies P'.instantiated_n P.instantiated_n),


      have f_not_free_in_P': f ∉ FV P', from free_P'_P.symm ▸ f_not_free_in_P,
      have fv_R': FV R.to_prop ⊆ FV P' ∪ { f, x }, from free_P'_P.symm ▸ fv_R,
      have fv_S': FV S.to_prop ⊆ FV P' ∪ { f, x }, from free_P'_P.symm ▸ fv_S,
      show P' ⊢ letf f[x] req R ens S {e₁} in e₂ : propctx.exis f (spec.func f x R S && Q₂),
      from exp.vcgen.func f_not_free_in_P' fv_R' fv_S' 
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
