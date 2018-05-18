import .definitions3 .logic

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

lemma strengthen_vc {P P' Q: prop} {σ: env}:
  (σ ⊨ vc.implies P'.to_vc P.to_vc) → (FV P ⊆ FV P') →
  (closed_subst σ (prop.implies P Q) → σ ⊨ (prop.implies P Q).to_vc) →
  (closed_subst σ (prop.implies P' Q) → σ ⊨ (prop.implies P' Q).to_vc) :=
  begin
    assume h1,
    assume h2,
    assume h3,
    assume h4,
    apply @strengthen_impl_with_dominating_instantiations σ P P' Q,
    from h1,

    have h5: closed_subst σ (prop.implies P Q), by begin
      assume x,
      assume h6,
      cases free_in_prop.implies.inv h6 with h7 h8,
      have h9: x ∈ FV P, from h7,
      have h10, from set.mem_of_mem_of_subset h9 h2,
      have h12: free_in_prop x (prop.implies P' Q), from free_in_prop.implies₁ h10,
      from h4 h12,

      have h12: free_in_prop x (prop.implies P' Q), from free_in_prop.implies₂ h8,
      from h4 h12
    end,
    from h3 h5
  end

lemma strengthen_vc_with_q {P P' Q S: prop} {σ: env}:
  (σ ⊨ vc.implies P'.to_vc P.to_vc) → (FV P ⊆ FV P') →
  (closed_subst σ (prop.implies (P ⋀ Q) S) → σ ⊨ (prop.implies (P ⋀ Q) S).to_vc) →
  (closed_subst σ (prop.implies (P' ⋀ Q) S) → σ ⊨ (prop.implies (P' ⋀ Q) S).to_vc) :=
  begin
    assume h1,
    assume h2,
    assume h3,
    assume h4,
    apply @strengthen_impl_with_dominating_instantiations σ (P ⋀ Q) (P' ⋀ Q) S,
    from vc.implies.same_right (λ_, h1),
    have h5: closed_subst σ (prop.implies (P⋀Q) S), by begin
      assume x,
      assume h6,
      cases free_in_prop.implies.inv h6 with h7 h8,
      cases free_in_prop.and.inv h7 with h8 h9,
      have h9: x ∈ FV P, from h8,
      have h10, from set.mem_of_mem_of_subset h9 h2,
      have h11: free_in_prop x (P' ⋀ Q), from free_in_prop.and₁ h10,
      have h12: free_in_prop x (prop.implies (P' ⋀ Q) S), from free_in_prop.implies₁ h11,
      from h4 h12,


      have h11: free_in_prop x (P' ⋀ Q), from free_in_prop.and₂ h9,
      have h12: free_in_prop x (prop.implies (P' ⋀ Q) S), from free_in_prop.implies₁ h11,
      from h4 h12,

      have h12: free_in_prop x (prop.implies (P' ⋀ Q) S), from free_in_prop.implies₂ h8,
      from h4 h12
    end,
    from h3 h5
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
      from λσ, vc.implies.same_right (λ_, P'_dominates_p_P σ),
      have e'_verified': P' ⋀ x ≡ value.true ⊩ e': Q, from ih (P' ⋀ x ≡ value.true) h1 h2,
      have x_not_free_in_P': x ∉ FV P', from free_P'_P.symm ▸ x_not_free_in_P,
      show P' ⊩ lett x = true in e' : propctx.exis x (x ≡ value.true ⋀ Q),
      from exp.dvcgen.tru x_not_free_in_P' e'_verified'
    )},
    case exp.dvcgen.fals x P e' Q x_not_free_in_P e'_verified ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, σ ⊨ vc.implies P'.to_vc P.to_vc),

      have h1: FV (P' ⋀ (x ≡ value.false)) = FV (P ⋀ x ≡ value.false),
      from free_in_prop.same_right free_P'_P,
      have h2: (∀σ, σ ⊨ vc.implies (P' ⋀ x ≡ value.false).to_vc (P ⋀ x ≡ value.false).to_vc),
      from λσ, vc.implies.same_right (λ_, P'_dominates_p_P σ),
      have e'_verified': P' ⋀ x ≡ value.false ⊩ e': Q, from ih (P' ⋀ x ≡ value.false) h1 h2,
      have x_not_free_in_P': x ∉ FV P', from free_P'_P.symm ▸ x_not_free_in_P,
      show P' ⊩ letf x = false in e' : propctx.exis x ((x ≡ value.false) ⋀ Q),
      from exp.dvcgen.fals x_not_free_in_P' e'_verified'
    },
    case exp.dvcgen.num x n P e' Q x_not_free_in_P e'_verified ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, σ ⊨ vc.implies P'.to_vc P.to_vc),

      have h1: FV (P' ⋀ x ≡ value.num n) = FV (P ⋀ x ≡ value.num n),
      from free_in_prop.same_right free_P'_P,
      have h2: (∀σ, σ ⊨ vc.implies (P' ⋀ x ≡ value.num n).to_vc (P ⋀ x ≡ value.num n).to_vc),
      from λσ, vc.implies.same_right (λ_, P'_dominates_p_P σ),
      have e'_verified': P' ⋀ (x ≡ value.num n) ⊩ e': Q, from ih (P' ⋀ (x ≡ value.num n)) h1 h2,
      have x_not_free_in_P': x ∉ FV P', from free_P'_P.symm ▸ x_not_free_in_P,
      show P' ⊩ letn x = n in e' : propctx.exis x ((x ≡ value.num n) ⋀ Q),
      from exp.dvcgen.num x_not_free_in_P' e'_verified'
    },
    case exp.dvcgen.func f x R S e₁ e₂ P Q₁ Q₂ f_not_free_in_P x_not_free_in_P f_neq_x x_free_in_R fv_R fv_S
                        e₁_verified e₂_verified func_vc ih₁ ih₂ { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, σ ⊨ vc.implies P'.to_vc P.to_vc),

      have f_not_free_in_P': f ∉ FV P', from free_P'_P.symm ▸ f_not_free_in_P,
      have x_not_free_in_P': x ∉ FV P', from free_P'_P.symm ▸ x_not_free_in_P,
      have fv_R': FV R.to_prop ⊆ FV P' ∪ { f, x }, from free_P'_P.symm ▸ fv_R,
      have fv_S': FV S.to_prop ⊆ FV P' ∪ { f, x }, from free_P'_P.symm ▸ fv_S,

      have h1: FV (P' ⋀ ((spec.func f x R S) ⋀ R)) = FV (P ⋀ ((spec.func f x R S) ⋀ R)),
      from free_in_prop.same_right free_P'_P,
      have h2: (∀σ, σ ⊨ vc.implies (P' ⋀ (spec.func f x R S) ⋀ R).to_vc (P ⋀ (spec.func f x R S) ⋀ R).to_vc),
      from λσ, vc.implies.same_right (λ_, P'_dominates_p_P σ),
      have e₁_verified': P' ⋀ (spec.func f x R S) ⋀ R ⊩ e₁ : Q₁,
      from ih₁ (P' ⋀ (spec.func f x R S) ⋀ R) h1 h2,

      have h3: FV (P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)))
             = FV (P ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S))),
      from free_in_prop.same_right free_P'_P,

      have h5: (∀σ, σ ⊨ vc.implies (P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S))).to_vc
                      (P ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S))).to_vc),
      from (λσ, vc.implies.same_right (λ_, P'_dominates_p_P σ)),

      have e₂_verified': P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S)) ⊩ e₂ : Q₂,
      from ih₂ (P' ⋀ (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S))) h3 h5,

      have func_vc': ∀ (σ : env),
            closed_subst σ (prop.implies (P'⋀↑(spec.func ↑f x R S) ⋀ R ⋀ Q₁ (term.app ↑f ↑x)) ↑S) →
             σ ⊨ (prop.implies (P' ⋀ ↑(spec.func ↑f x R S) ⋀ R ⋀ Q₁ (term.app ↑f ↑x)) ↑S).to_vc,
      from (λσ, strengthen_vc_with_q (P'_dominates_p_P σ) (set.subset_of_eq free_P'_P.symm) (func_vc σ)),

      show P' ⊩ letf f[x] req R ens S {e₁} in e₂ : propctx.exis f (prop.func f x R (Q₁ (term.app ↑f ↑x) ⋀ ↑S) ⋀ Q₂),
      from exp.dvcgen.func f_not_free_in_P' x_not_free_in_P' f_neq_x x_free_in_R fv_R' fv_S' e₁_verified'
           e₂_verified' func_vc'
    },
    case exp.dvcgen.unop op x y P e' Q' x_free_in_P y_not_free_in_P e'_verified vc_valid ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, σ ⊨ vc.implies P'.to_vc P.to_vc),

      have x_free_in_P': x ∈ FV P', from free_P'_P.symm ▸ x_free_in_P,
      have y_not_free_in_P': y ∉ FV P', from free_P'_P.symm ▸ y_not_free_in_P,

      have h1: FV (P' ⋀ y ≡ term.unop op x) = FV (P ⋀ y ≡ term.unop op x),
      from free_in_prop.same_right free_P'_P,
      have h2: (∀σ, σ ⊨ vc.implies (P' ⋀ y ≡ term.unop op x).to_vc (P ⋀ y ≡ term.unop op x).to_vc),
      from (λσ, vc.implies.same_right (λ_, P'_dominates_p_P σ)),
      have e'_verified': P' ⋀ y ≡ term.unop op x ⊩ e' : Q',
      from ih (P' ⋀ y ≡ term.unop op x) h1 h2,

      have FV P ⊆ FV P', from set.subset_of_eq free_P'_P.symm,
      have vc_valid': ∀ (σ : env),
           closed_subst σ (prop.implies P' (prop.pre₁ op x)) → σ ⊨ (prop.implies P' (prop.pre₁ op x)).to_vc,
      from (λσ, strengthen_vc (P'_dominates_p_P σ) this (vc_valid σ)),

      show P' ⊩ letop y = op [x] in e' : propctx.exis y (y ≡ term.unop op x ⋀ Q'),
      from exp.dvcgen.unop x_free_in_P' y_not_free_in_P' e'_verified' vc_valid'
    },
    case exp.dvcgen.binop op x y z e' P Q' x_free_in_P y_free_in_P z_not_free_in_P e'_verified vc_valid ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, σ ⊨ vc.implies P'.to_vc P.to_vc),

      have x_free_in_P': x ∈ FV P', from free_P'_P.symm ▸ x_free_in_P,
      have y_free_in_P': y ∈ FV P', from free_P'_P.symm ▸ y_free_in_P,
      have z_not_free_in_P': z ∉ FV P', from free_P'_P.symm ▸ z_not_free_in_P,

      have h1: FV (P' ⋀ z ≡ term.binop op x y) = FV (P ⋀ z ≡ term.binop op x y),
      from free_in_prop.same_right free_P'_P,
      have h2: (∀σ, σ ⊨ vc.implies (P' ⋀ z ≡ term.binop op x y).to_vc (P ⋀ z ≡ term.binop op x y).to_vc),
      from (λσ, vc.implies.same_right (λ_, P'_dominates_p_P σ)),
      have e'_verified': P' ⋀ z ≡ term.binop op x y ⊩ e' : Q',
      from ih (P' ⋀ z ≡ term.binop op x y) h1 h2,

      have FV P ⊆ FV P', from set.subset_of_eq free_P'_P.symm,
      have vc_valid': ∀ (σ : env),
        closed_subst σ (prop.implies P' (prop.pre₂ op x y)) →
        σ ⊨ (prop.implies P' (prop.pre₂ op x y)).to_vc,
      from (λσ, strengthen_vc (P'_dominates_p_P σ) this (vc_valid σ)),

      show P' ⊩ letop2 z = op [x, y] in e' : propctx.exis z (z ≡ term.binop op x y ⋀ Q'),
      from exp.dvcgen.binop x_free_in_P' y_free_in_P' z_not_free_in_P' e'_verified' vc_valid'
    },
    case exp.dvcgen.app y f x e' P Q' f_free_in_P x_free_in_P y_not_free_in_P e'_verified vc_valid ih { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, σ ⊨ vc.implies P'.to_vc P.to_vc),

      have f_free_in_P': f ∈ FV P', from free_P'_P.symm ▸ f_free_in_P,
      have x_free_in_P': x ∈ FV P', from free_P'_P.symm ▸ x_free_in_P,
      have y_not_free_in_P': y ∉ FV P', from free_P'_P.symm ▸ y_not_free_in_P,

      have h1: FV (P' ⋀ prop.call x ⋀ prop.post f x ⋀ y ≡ term.app f x)
             = FV (P ⋀ prop.call x ⋀ prop.post f x ⋀ y ≡ term.app f x),
      from free_in_prop.same_right free_P'_P,

      have h2: (∀σ, σ ⊨ vc.implies (P' ⋀ prop.call x ⋀ prop.post f x ⋀ y ≡ term.app f x).to_vc
                                (P ⋀ prop.call x ⋀ prop.post f x ⋀ y ≡ term.app f x).to_vc),
      from (λσ, vc.implies.same_right (λ_, P'_dominates_p_P σ)),

      have e'_verified': P' ⋀ prop.call x ⋀ prop.post f x ⋀ y ≡ term.app f x ⊩ e' : Q',
      from ih (P' ⋀ prop.call x ⋀ prop.post f x ⋀ y ≡ term.app f x) h1 h2,

      have vc_valid': ∀ (σ : env),
           closed_subst σ (prop.implies (P' ⋀ prop.call x) (term.unop unop.isFunc f ⋀ prop.pre f x)) →
           σ ⊨ (prop.implies (P' ⋀ prop.call x) (term.unop unop.isFunc f ⋀ prop.pre f x)).to_vc,
      from (λσ, strengthen_vc_with_q (P'_dominates_p_P σ) (set.subset_of_eq free_P'_P.symm) (vc_valid σ)),

      show P' ⊩ letapp y = f [x] in e' : propctx.exis y (prop.call x ⋀ prop.post f x ⋀ y ≡ term.app f x ⋀ Q'),
      from exp.dvcgen.app f_free_in_P' x_free_in_P' y_not_free_in_P' e'_verified' vc_valid'
    },
    case exp.dvcgen.ite x e₂ e₁ P Q₁ Q₂ x_free_in_P e₁_verified e₂_verified vc_valid ih₁ ih₂ { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, σ ⊨ vc.implies P'.to_vc P.to_vc),

      have x_free_in_P': x ∈ FV P', from free_P'_P.symm ▸ x_free_in_P,

      have h1: FV (P' ⋀ x) = FV (P ⋀ x), from free_in_prop.same_right free_P'_P,
      have h2: (∀σ, σ ⊨ vc.implies (P' ⋀ x).to_vc (P ⋀ x).to_vc),
      from (λσ, vc.implies.same_right (λ_, P'_dominates_p_P σ)),
      have e₁_verified': P' ⋀ x ⊩ e₁ : Q₁, from ih₁ (P' ⋀ x) h1 h2,

      have h1: FV (P' ⋀ prop.not x) = FV (P ⋀ prop.not x), from free_in_prop.same_right free_P'_P,
      have h2: (∀σ, σ ⊨ vc.implies (P' ⋀ prop.not x).to_vc (P ⋀ prop.not x).to_vc),
      from (λσ, vc.implies.same_right (λ_, P'_dominates_p_P σ)),
      have e₂_verified': P' ⋀ prop.not x ⊩ e₂ : Q₂, from ih₂ (P' ⋀ prop.not x) h1 h2,

      have FV P ⊆ FV P', from set.subset_of_eq free_P'_P.symm,
      have vc_valid': ∀ (σ : env),
           closed_subst σ (prop.implies P' (term.unop unop.isBool x)) →
           σ ⊨ (prop.implies P' (term.unop unop.isBool x)).to_vc,
      from (λσ, strengthen_vc (P'_dominates_p_P σ) this (vc_valid σ)),

      show P' ⊩ exp.ite x e₁ e₂ : propctx.implies x Q₁ ⋀ propctx.implies (prop.not x) Q₂,
      from exp.dvcgen.ite x_free_in_P' e₁_verified' e₂_verified' vc_valid'
    },
    case exp.dvcgen.return x P x_free_in_P { from
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, σ ⊨ vc.implies P'.to_vc P.to_vc),

      have x_free_in_P': x ∈ FV P', from free_P'_P.symm ▸ x_free_in_P,

      show P' ⊩ exp.return x : (x ≣ •), from exp.dvcgen.return x_free_in_P'
    }
  end
