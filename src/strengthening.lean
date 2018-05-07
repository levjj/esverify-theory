/-
import .definitions2

lemma strengthen_and_with_dominating_instantiations {σ: env} {P P' Q: prop}:
  dominates_p σ P P' → (σ ⊨ (P ⋀ Q).instantiated_p) → σ ⊨ (P' ⋀ Q).instantiated_p :=
  assume h1: dominates_p σ P P',
  assume h2: (σ ⊨ (P ⋀ Q).instantiated_p),
  have dominates_p σ (P ⋀ Q) (P' ⋀ Q), from dominates_p.same_right (λ_, h1),
  dominates_p.elim this h2

lemma strengthen_impl_with_dominating_instantiations {σ: env} {P P' Q: prop}:
  dominates_p σ P' P → FV P' ⊆ FV P → (σ ⊨ (prop.implies P Q).instantiated_n) → (σ ⊨ (prop.implies P' Q).instantiated_n) :=
  assume P'_dominates_P: dominates_p σ P' P,
  assume fv_P'_P: FV P' ⊆ FV P,
  assume h0: σ ⊨ (P.not ⋁ Q).instantiated_n,
  have h11: closed_subst σ (P'.not ⋁ Q).not.instantiated_p, from (
    assume x: var,
    assume h12: x ∈ FV (P'.not ⋁ Q).not.instantiated_p,
    have (P'.not ⋁ Q).not.instantiated_p = (P'.not ⋁ Q).instantiated_n.not, from not_dist_instantiated_p,
    have x ∈ FV (P'.not ⋁ Q).instantiated_n.not, from this ▸ h12,
    have h13: x ∈ FV (P'.not ⋁ Q).instantiated_n, from free_in_vc.not.inv this,
    have FV P'.not ⊆ FV P.not, from (
      assume y: var,
      assume : y ∈ FV P'.not,
      have y ∈ FV P', from free_in_prop.not.inv this,
      have y ∈ FV P, from set.mem_of_subset_of_mem fv_P'_P this,
      show y ∈ FV P.not, from free_in_prop.not this
    ),
    have FV (P'.not ⋁ Q).instantiated_n ⊆ FV (P.not ⋁ Q).instantiated_n,
    from free_in_prop.strengthen_or_with_instantiations this,
    have x ∈ FV (P.not ⋁ Q).instantiated_n, from set.mem_of_subset_of_mem this h13,
    show x ∈ σ.dom,
    from set.mem_of_subset_of_mem (valid_env.closed h0) this
  ),
  have h12: σ ⊨ (P.not ⋁ Q).instantiated_n.not.not, from valid_env.not_not.mpr h0,
  have (P.not ⋁ Q).not.instantiated_p = (P.not ⋁ Q).instantiated_n.not, from not_dist_instantiated_p,
  have σ ⊨ (P.not ⋁ Q).not.instantiated_p.not, from this.symm ▸ h12,
  have h2: ¬ σ ⊨ (P.not ⋁ Q).not.instantiated_p, from valid_env.not.mpr this,

  have h3: (σ ⊨ (P'.not ⋁ Q).not.instantiated_p) → (σ ⊨ (P.not ⋁ Q).not.instantiated_p), from (
    assume : σ ⊨ (P'.not ⋁ Q).not.instantiated_p,
    have h4: σ ⊨ (P'.not.not ⋀ Q.not).instantiated_p, from valid_env.or_not_dist_with_instantiations.mp this,

    have h41: σ ⊨ P'.not.not.instantiated_p, from (valid_env.and.elim (valid_env.instantiated_p_and_elim h4)).left,
    have h42: P'.not.not.instantiated_p = P'.not.instantiated_n.not, from not_dist_instantiated_p,
    have h43: P'.not.instantiated_n = P'.instantiated_p.not, from not_dist_instantiated_n,
    have σ ⊨ P'.instantiated_p.not.not, from h43 ▸ h42 ▸ h41,
    have σ ⊨ P'.instantiated_p, from valid_env.not_not.mp this,
    have dominates_p σ P'.not.not P', from dominates_p.not_not,
    have h5: σ ⊨ (P' ⋀ Q.not).instantiated_p, from strengthen_and_with_dominating_instantiations this h4,
    have h6: σ ⊨ (P ⋀ Q.not).instantiated_p, from strengthen_and_with_dominating_instantiations P'_dominates_P h5,

    have dominates_p σ P P.not.not, from dominates_p.of_not_not,
    have σ ⊨ (P.not.not ⋀ Q.not).instantiated_p, from strengthen_and_with_dominating_instantiations this h6,
    show σ ⊨ (P.not ⋁ Q).not.instantiated_p, from valid_env.or_not_dist_with_instantiations.mpr this
  ),

  have ¬ σ ⊨ (P'.not ⋁ Q).not.instantiated_p, from mt h3 h2,
  have h9: σ ⊨ (P'.not ⋁ Q).not.instantiated_p.not, from valid_env.not.mp h11 this,
  have (P'.not ⋁ Q).not.instantiated_p = (P'.not ⋁ Q).instantiated_n.not, from not_dist_instantiated_p,
  have σ ⊨ (P'.not ⋁ Q).instantiated_n.not.not, from this ▸ h9,
  show σ ⊨ (P'.not ⋁ Q).instantiated_n, from valid_env.not_not.mp this

lemma strengthen_vc {P P' Q S: prop} {σ: env}:
  dominates_p σ P' P → FV P' ⊆ FV P →
  (σ ⊨ (prop.implies (P ⋀ Q) S).instantiated_n) → σ ⊨ (prop.implies (P' ⋀ Q) S).instantiated_n :=
  assume : dominates_p σ P' P,
  assume fv_P'_P: FV P' ⊆ FV P,
  have h1: dominates_p σ (P' ⋀ Q) (P ⋀ Q), from dominates_p.same_right (λ_, this),
  have h2: FV (P' ⋀ Q) ⊆ FV (P ⋀ Q), from (
    assume x: var,
    assume : x ∈ FV (P' ⋀ Q),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P',
      have x ∈ FV P, from set.mem_of_subset_of_mem fv_P'_P this,
      show x ∈ FV (P ⋀ Q), from free_in_prop.and₁ this
    ) (
      assume : x ∈ FV Q,
      show x ∈ FV (P ⋀ Q), from free_in_prop.and₂ this
    )
  ),
  strengthen_impl_with_dominating_instantiations h1 h2

lemma strengthen_exp {P: prop} {Q: propctx} {e: exp}:
      (P ⊢ e : Q) → ∀P': prop, (FV P' = FV P) → (∀σ, dominates_p σ P' P) → (P' ⊢ e: Q) :=
  assume e_verified: (P ⊢ e : Q),
  begin
    induction e_verified,
    case exp.vcgen.tru x P e' Q x_not_free_in_P e'_verified ih { from (
      assume P': prop,
      assume free_P'_P: FV P' = FV P,
      assume P'_dominates_p_P: (∀σ, dominates_p σ P' P),

      have h1: FV (P' ⋀ x ≡ value.true) = FV (P ⋀ x ≡ value.true),
      from free_in_prop.same_right free_P'_P,
      have h2: (∀σ, dominates_p σ (P' ⋀ x ≡ value.true) (P ⋀ x ≡ value.true)),
      from λσ, dominates_p.same_right (λ_, P'_dominates_p_P σ),
      have e'_verified': P' ⋀ x ≡ value.true ⊢ e': Q, from ih (P' ⋀ x ≡ value.true) h1 h2,
      have x_not_free_in_P': x ∉ FV P', from free_P'_P.symm ▸ x_not_free_in_P,
      show P' ⊢ lett x = true in e' : propctx.exis x (x ≡ value.true ⋀ Q),
      from exp.vcgen.tru x_not_free_in_P' e'_verified'
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

-/