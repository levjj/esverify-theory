import .definitions3 .logic

lemma strengthen_and_with_dominating_instantiations {σ: env} {P P' Q: prop}:
  (σ ⊨ vc.implies P.to_vc P'.to_vc) → (σ ⊨ (P ⋀ Q).to_vc) → σ ⊨ (P' ⋀ Q).to_vc :=
  begin
    assume h1: σ ⊨ vc.implies P.to_vc P'.to_vc,
    assume h2: σ ⊨ (P ⋀ Q).to_vc,
    apply valid_env.to_vc_and,
    have h3, from (valid_env.to_vc_and.elim h2).left,
    from valid_env.mp h1 h3,
    from (valid_env.to_vc_and.elim h2).right
  end

lemma strengthen_impl_with_dominating_instantiations {σ: env} {P P' Q: prop}:
  (σ ⊨ vc.implies P'.to_vc P.to_vc) → (σ ⊨ (prop.implies P Q).to_vc) → (σ ⊨ (prop.implies P' Q).to_vc) :=
  begin
    assume h1,
    assume h2,
    apply valid_env.to_vc_implies.mpr,
    apply valid_env.mpr,
    assume h3,
    have h4, from valid_env.mp h1 h3,
    have h5, from valid_env.to_vc_implies.mp h2,
    from valid_env.mp h5 h4
  end

lemma strengthen_vc {P P' Q S: prop} {σ: env}:
  (σ ⊨ vc.implies P'.to_vc P.to_vc) →
  (σ ⊨ (prop.implies (P ⋀ Q) S).to_vc) → σ ⊨ (prop.implies (P' ⋀ Q) S).to_vc :=
  begin
    assume h1,
    apply strengthen_impl_with_dominating_instantiations,
    apply valid_env.mpr,
    from strengthen_and_with_dominating_instantiations h1
  end

lemma strengthen_exp {P: prop} {Q: propctx} {e: exp}:
      (P ⊩ e : Q) → ∀P': prop, (FV P' = FV P) → (∀σ, σ ⊨ vc.implies P'.to_vc P.to_vc) → (P' ⊩ e: Q) :=
  assume e_verified: (P ⊩ e : Q),
  begin
    induction e_verified,
    case exp.dvcgen.tru x P e' Q x_not_free_in_P e'_verified ih { from (
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, σ ⊨ vc.implies P'.to_vc P.to_vc),

      have h1: FV (P' ⋀ x ≡ value.true) = FV (P ⋀ x ≡ value.true),
      from free_in_prop.same_right free_P'_P,
      have h2: (∀σ, σ ⊨ vc.implies (P' ⋀ x ≡ value.true).to_vc (P ⋀ x ≡ value.true).to_vc),
      from λσ, dominates_p.same_right (λ_, P'_dominates_p_P σ),
      have e'_verified': P' ⋀ x ≡ value.true ⊢ e': Q, from ih (P' ⋀ x ≡ value.true) h1 h2,
      have x_not_free_in_P': x ∉ FV P', from free_P'_P.symm ▸ x_not_free_in_P,
      show P' ⊢ lett x = true in e' : propctx.exis x (x ≡ value.true ⋀ Q),
      from exp.dvcgen.tru x_not_free_in_P' e'_verified'
    )},
    case exp.vcgen.fals x P e' Q x_not_free_in_P e'_verified ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, dominates_p σ P' P),

      have h1: FV (P' ⋀ (x ≡ value.false)) = FV (P ⋀ x ≡ value.false),
      from free_in_prop.same_right free_P'_P,
      have h2: (∀σ, dominates_p σ (P' ⋀ x ≡ value.false) (P ⋀ x ≡ value.false)),
      from λσ, dominates_p.same_right (λ_, P'_dominates_p_P σ),
      have e'_verified': P' ⋀ x ≡ value.false ⊢ e': Q, from ih (P' ⋀ x ≡ value.false) h1 h2,
      have x_not_free_in_P': x ∉ FV P', from free_P'_P.symm ▸ x_not_free_in_P,
      show P' ⊢ letf x = false in e' : propctx.exis x ((x ≡ value.false) ⋀ Q),
      from exp.vcgen.fals x_not_free_in_P' e'_verified'
    },
    case exp.vcgen.num x n P e' Q x_not_free_in_P e'_verified ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, dominates_p σ P' P),

      have h1: FV (P' ⋀ x ≡ value.num n) = FV (P ⋀ x ≡ value.num n),
      from free_in_prop.same_right free_P'_P,
      have h2: (∀σ, dominates_p σ (P' ⋀ x ≡ value.num n) (P ⋀ x ≡ value.num n)),
      from λσ, dominates_p.same_right (λ_, P'_dominates_p_P σ),
      have e'_verified': P' ⋀ (x ≡ value.num n) ⊢ e': Q, from ih (P' ⋀ (x ≡ value.num n)) h1 h2,
      have x_not_free_in_P': x ∉ FV P', from free_P'_P.symm ▸ x_not_free_in_P,
      show P' ⊢ letn x = n in e' : propctx.exis x ((x ≡ value.num n) ⋀ Q),
      from exp.vcgen.num x_not_free_in_P' e'_verified'
    },
    case exp.vcgen.func f x R S e₁ e₂ P Q₁ Q₂ f_not_free_in_P x_not_free_in_P f_neq_x x_free_in_R fv_R fv_S
                        e₁_verified e₂_verified func_vc ih₁ ih₂ { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, dominates_p σ P' P),

      have f_not_free_in_P': f ∉ FV P', from free_P'_P.symm ▸ f_not_free_in_P,
      have x_not_free_in_P': x ∉ FV P', from free_P'_P.symm ▸ x_not_free_in_P,
      have fv_R': FV R.to_prop ⊆ FV P' ∪ { f, x }, from free_P'_P.symm ▸ fv_R,
      have fv_S': FV S.to_prop ⊆ FV P' ∪ { f, x }, from free_P'_P.symm ▸ fv_S,

      have h1: FV (P' ⋀ ((spec.func f x R S) ⋀ R)) = FV (P ⋀ ((spec.func f x R S) ⋀ R)),
      from free_in_prop.same_right free_P'_P,
      have h2: (∀σ, dominates_p σ (P' ⋀ (spec.func f x R S) ⋀ R) (P ⋀ (spec.func f x R S) ⋀ R)),
      from λσ, dominates_p.same_right (λ_, P'_dominates_p_P σ),
      have e₁_verified': P' ⋀ (spec.func f x R S) ⋀ R ⊢ e₁ : Q₁,
      from ih₁ (P' ⋀ (spec.func f x R S) ⋀ R) h1 h2,

      have h3: FV (P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)))
             = FV (P ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S))),
      from free_in_prop.same_right free_P'_P,

      have h5: (∀σ, dominates_p σ (P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)))
                      (P ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)))),
      from (λσ, dominates_p.same_right (λ_, P'_dominates_p_P σ)),

      have e₂_verified': P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)) ⊢ e₂ : Q₂,
      from ih₂ (P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S))) h3 h5,

      have func_vc': ∀ (σ : env),
             σ ⊨ prop.instantiated_n (prop.implies (P' ⋀ ↑(spec.func ↑f x R S) ⋀ R ⋀ Q₁ (term.app ↑f ↑x)) ↑S),
      from (λσ, strengthen_vc (P'_dominates_p_P σ) (set.subset_of_eq free_P'_P) (func_vc σ)),

      show P' ⊢ letf f[x] req R ens S {e₁} in e₂ : propctx.exis f (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S) ⋀ Q₂),
      from exp.vcgen.func f_not_free_in_P' x_not_free_in_P' f_neq_x x_free_in_R fv_R' fv_S' e₁_verified'
           e₂_verified' func_vc'
    },
    case exp.vcgen.unop op x y P e' Q' x_free_in_P y_not_free_in_P e'_verified vc_valid ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, dominates_p σ P' P),

      have x_free_in_P': x ∈ FV P', from free_P'_P.symm ▸ x_free_in_P,
      have y_not_free_in_P': y ∉ FV P', from free_P'_P.symm ▸ y_not_free_in_P,

      have h1: FV (P' ⋀ y ≡ term.unop op x) = FV (P ⋀ y ≡ term.unop op x),
      from free_in_prop.same_right free_P'_P,
      have h2: (∀σ, dominates_p σ (P' ⋀ y ≡ term.unop op x) (P ⋀ y ≡ term.unop op x)),
      from (λσ, dominates_p.same_right (λ_, P'_dominates_p_P σ)),
      have e'_verified': P' ⋀ y ≡ term.unop op x ⊢ e' : Q',
      from ih (P' ⋀ y ≡ term.unop op x) h1 h2,

      have FV P' ⊆ FV P, from set.subset_of_eq free_P'_P,
      have vc_valid': ∀ (σ : env), σ ⊨ prop.instantiated_n (prop.implies P' (prop.pre₁ op x)),
      from (λσ, strengthen_impl_with_dominating_instantiations (P'_dominates_p_P σ) this (vc_valid σ)),

      show P' ⊢ letop y = op [x] in e' : propctx.exis y (y ≡ term.unop op x ⋀ Q'),
      from exp.vcgen.unop x_free_in_P' y_not_free_in_P' e'_verified' vc_valid'
    },
    case exp.vcgen.binop op x y z e' P Q' x_free_in_P y_free_in_P z_not_free_in_P e'_verified vc_valid ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, dominates_p σ P' P),

      have x_free_in_P': x ∈ FV P', from free_P'_P.symm ▸ x_free_in_P,
      have y_free_in_P': y ∈ FV P', from free_P'_P.symm ▸ y_free_in_P,
      have z_not_free_in_P': z ∉ FV P', from free_P'_P.symm ▸ z_not_free_in_P,

      have h1: FV (P' ⋀ z ≡ term.binop op x y) = FV (P ⋀ z ≡ term.binop op x y),
      from free_in_prop.same_right free_P'_P,
      have h2: (∀σ, dominates_p σ (P' ⋀ z ≡ term.binop op x y) (P ⋀ z ≡ term.binop op x y)),
      from (λσ, dominates_p.same_right (λ_, P'_dominates_p_P σ)),
      have e'_verified': P' ⋀ z ≡ term.binop op x y ⊢ e' : Q',
      from ih (P' ⋀ z ≡ term.binop op x y) h1 h2,

      have FV P' ⊆ FV P, from set.subset_of_eq free_P'_P,
      have vc_valid': ∀ (σ : env), σ ⊨ prop.instantiated_n (prop.implies P' (prop.pre₂ op x y)),
      from (λσ, strengthen_impl_with_dominating_instantiations (P'_dominates_p_P σ) this (vc_valid σ)),

      show P' ⊢ letop2 z = op [x, y] in e' : propctx.exis z (z ≡ term.binop op x y ⋀ Q'),
      from exp.vcgen.binop x_free_in_P' y_free_in_P' z_not_free_in_P' e'_verified' vc_valid'
    },
    case exp.vcgen.app y f x e' P Q' f_free_in_P x_free_in_P y_not_free_in_P e'_verified vc_valid ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, dominates_p σ P' P),

      have f_free_in_P': f ∈ FV P', from free_P'_P.symm ▸ f_free_in_P,
      have x_free_in_P': x ∈ FV P', from free_P'_P.symm ▸ x_free_in_P,
      have y_not_free_in_P': y ∉ FV P', from free_P'_P.symm ▸ y_not_free_in_P,

      have h1: FV (P' ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
             = FV (P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x),
      from free_in_prop.same_right free_P'_P,

      have h2: (∀σ, dominates_p σ (P' ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)
                                (P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x)),
      from (λσ, dominates_p.same_right (λ_, P'_dominates_p_P σ)),

      have e'_verified': P' ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⊢ e' : Q',
      from ih (P' ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x) h1 h2,

      have vc_valid': ∀ (σ : env),
             σ ⊨ prop.instantiated_n (prop.implies (P' ⋀ prop.call f x) (term.unop unop.isFunc f ⋀ prop.pre f x)),
      from (λσ, strengthen_vc (P'_dominates_p_P σ) (set.subset_of_eq free_P'_P) (vc_valid σ)),

      show P' ⊢ letapp y = f [x] in e' : propctx.exis y (prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⋀ Q'),
      from exp.vcgen.app f_free_in_P' x_free_in_P' y_not_free_in_P' e'_verified' vc_valid'
    },
    case exp.vcgen.ite x e₂ e₁ P Q₁ Q₂ x_free_in_P e₁_verified e₂_verified vc_valid ih₁ ih₂ { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, dominates_p σ P' P),

      have x_free_in_P': x ∈ FV P', from free_P'_P.symm ▸ x_free_in_P,

      have h1: FV (P' ⋀ x) = FV (P ⋀ x), from free_in_prop.same_right free_P'_P,
      have h2: (∀σ, dominates_p σ (P' ⋀ x) (P ⋀ x)), from (λσ, dominates_p.same_right (λ_, P'_dominates_p_P σ)),
      have e₁_verified': P' ⋀ x ⊢ e₁ : Q₁, from ih₁ (P' ⋀ x) h1 h2,

      have h1: FV (P' ⋀ prop.not x) = FV (P ⋀ prop.not x), from free_in_prop.same_right free_P'_P,
      have h2: (∀σ, dominates_p σ (P' ⋀ prop.not x) (P ⋀ prop.not x)),
      from (λσ, dominates_p.same_right (λ_, P'_dominates_p_P σ)),
      have e₂_verified': P' ⋀ prop.not x ⊢ e₂ : Q₂, from ih₂ (P' ⋀ prop.not x) h1 h2,

      have FV P' ⊆ FV P, from set.subset_of_eq free_P'_P,
      have vc_valid': ∀ (σ : env),
             σ ⊨ prop.instantiated_n (prop.implies P' (term.unop unop.isBool x)),
      from (λσ, strengthen_impl_with_dominating_instantiations (P'_dominates_p_P σ) this (vc_valid σ)),

      show P' ⊢ exp.ite x e₁ e₂ : propctx.implies x Q₁ ⋀ propctx.implies (prop.not x) Q₂,
      from exp.vcgen.ite x_free_in_P' e₁_verified' e₂_verified' vc_valid'
    },
    case exp.vcgen.return x P x_free_in_P { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, dominates_p σ P' P),

      have x_free_in_P': x ∈ FV P', from free_P'_P.symm ▸ x_free_in_P,

      show P' ⊢ exp.return x : (x ≣ •), from exp.vcgen.return x_free_in_P'
    }
  end
