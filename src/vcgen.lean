import .definitions3 .qi

lemma exp.vcgen.extension {P: prop} {e: exp} {Q: propctx}: (P ⊢ e : Q) → (P ⊩ e : Q) :=
  begin

    assume e_verified: P ⊢ e : Q,

    induction e_verified,

    case exp.vcgen.tru P y e' Q y_not_in_P e'_verified ih {
      apply exp.dvcgen.tru,
      from y_not_in_P,
      from ih
    },

    case exp.vcgen.fals P y e' Q y_not_in_P e'_verified ih {
      apply exp.dvcgen.fals,
      from y_not_in_P,
      from ih
    },

    case exp.vcgen.num P y n e' Q y_not_in_P e'_verified ih {
      apply exp.dvcgen.num,
      from y_not_in_P,
      from ih
    },

    case exp.vcgen.func P f fx R S e₁ e₂ Q₁ Q₂ f_not_in_P fx_not_in_P f_neq_fx fx_in_R fv_R fv_S
                        e₁_verified e₂_verified func_vc ih₁ ih₂ {
      apply exp.dvcgen.func,
      from f_not_in_P,
      from fx_not_in_P,
      from f_neq_fx,
      from fx_in_R,
      from fv_R,
      from fv_S,
      from ih₁,
      from ih₂,
      from vc_valid_from_inst_valid func_vc
    },

    case exp.vcgen.unop op P e' x₁ y Q x_free_in_P y_not_in_P e'_verified vc_valid ih {
      apply exp.dvcgen.unop,
      from x_free_in_P,
      from y_not_in_P,
      from ih,
      from vc_valid_from_inst_valid vc_valid
    },

    case exp.vcgen.binop op P e' x₁ x₂ y Q x₁_free_in_P x₂_free_in_P y_not_in_P e'_verified vc_valid ih {
      apply exp.dvcgen.binop,
      from x₁_free_in_P,
      from x₂_free_in_P,
      from y_not_in_P,
      from ih,
      from vc_valid_from_inst_valid vc_valid
    },

    case exp.vcgen.app P y f e' x₁ Q f_free_in_P x₁_free_in_P y_not_in_P e'_verified vc_valid ih {
      apply exp.dvcgen.app,
      from f_free_in_P,
      from x₁_free_in_P,
      from y_not_in_P,
      from ih,
      from vc_valid_from_inst_valid vc_valid
    },

    case exp.vcgen.ite P e₁ e₂ y Q₁ Q₂ y_free_in_P e₁_verified e₂_verified vc_valid ih₁ ih₂ {
      apply exp.dvcgen.ite,
      from y_free_in_P,
      from ih₁,
      from ih₂,
      from vc_valid_from_inst_valid vc_valid
    },

    case exp.vcgen.return P y y_free_in_P {
      apply exp.dvcgen.return,
      from y_free_in_P
    }
  end

lemma exp.dvcgen.return.inv {P: prop} {x: var} {Q: propctx}: (P ⊩ exp.return x : Q) → x ∈ FV P :=
  assume return_verified: P ⊩ exp.return x : Q,
  begin
    cases return_verified,
    case exp.dvcgen.return x_free {
      show x ∈ FV P, from x_free
    }
  end

lemma stack.dvcgen.top.inv {R: spec} {σ: env} {e: exp} {Q: propctx}:
  (⊩ₛ (R, σ, e) : Q) →
  ∃P Q₂, (⊩ σ: P) ∧ (FV R.to_prop ⊆ FV P) ∧ (σ ⊨ R.to_prop.to_vc) ∧ (R ⋀ P ⊩ e: Q₂) :=
  assume top_verified: ⊩ₛ (R, σ, e) : Q,
  begin
    cases top_verified,
    case stack.dvcgen.top P Q env_verified fv_R R_valid e_verified {
      show ∃P Q₂, (⊩ σ: P) ∧ (FV R.to_prop ⊆ FV P) ∧ (σ ⊨ R.to_prop.to_vc) ∧ (R ⋀ P ⊩ e: Q₂),
      from exists.intro P (exists.intro Q ⟨env_verified, ⟨fv_R, ⟨R_valid, e_verified⟩⟩⟩) 
    }
  end

lemma env.dvcgen.inv {σ: env} {P: prop} {x: var} {v: value}:
      (⊩ σ : P) → (σ x = v) → ∃σ' Q', ⊩ (σ'[x↦v]) : Q' :=
  assume env_verified: ⊩ σ : P,
  assume σ_x_is_v: σ x = v,
  show ∃σ' Q', ⊩ (σ'[x↦v]) : Q', by begin
    induction env_verified,
    case env.dvcgen.empty { from
      have env.apply env.empty x = none, by unfold env.apply,
      have some v = none, from eq.trans σ_x_is_v.symm this,
      show ∃σ' Q', ⊩ (σ'[x↦v]) : Q', from false.elim (option.no_confusion this)
    },
    case env.dvcgen.tru σ' y Q y_not_in_σ' σ'_verified ih { from
      have env.apply (σ'[y↦value.true]) x = v, from σ_x_is_v,
      have h1: (if y = x ∧ option.is_none (σ'.apply x) then ↑value.true else σ'.apply x) = v,
      by { unfold env.apply at this, from this },
      if h2: y = x ∧ option.is_none (σ'.apply x) then (
        have (↑value.true) = ↑v, by { simp[h2] at h1, from h1 },
        have v_is_true: v = value.true, from (option.some.inj this).symm,
        have x_not_in_σ': x ∉ σ', from h2.left ▸ y_not_in_σ',
        have ⊩ (σ'[x↦value.true]) : Q ⋀ x ≡ value.true, from env.dvcgen.tru x_not_in_σ' σ'_verified,
        have ⊩ (σ'[x↦v]) : Q ⋀ x ≡ value.true, from v_is_true.symm ▸ this,
        show ∃σ' Q', ⊩ (σ'[x↦v]) : Q',
        from exists.intro σ' (exists.intro (Q ⋀ x ≡ value.true) this)
      ) else (
        have (σ'.apply x) = v, by { simp[h2] at h1, from h1 },
        show ∃σ' Q', ⊩ (σ'[x↦v]) : Q', from ih this
      )
    },
    case env.dvcgen.fls σ' y Q y_not_in_σ' σ'_verified ih { from
      have env.apply (σ'[y↦value.false]) x = v, from σ_x_is_v,
      have h1: (if y = x ∧ option.is_none (σ'.apply x) then ↑value.false else σ'.apply x) = v,
      by { unfold env.apply at this, from this },
      if h2: y = x ∧ option.is_none (σ'.apply x) then (
        have (↑value.false) = ↑v, by { simp[h2] at h1, from h1 },
        have v_is_false: v = value.false, from (option.some.inj this).symm,
        have x_not_in_σ': x ∉ σ', from h2.left ▸ y_not_in_σ',
        have ⊩ (σ'[x↦value.false]) : Q ⋀ x ≡ value.false, from env.dvcgen.fls x_not_in_σ' σ'_verified,
        have ⊩ (σ'[x↦v]) : Q ⋀ x ≡ value.false, from v_is_false.symm ▸ this,
        show ∃σ' Q', ⊩ (σ'[x↦v]) : Q',
        from exists.intro σ' (exists.intro (Q ⋀ x ≡ value.false) this)
      ) else (
        have (σ'.apply x) = v, by { simp[h2] at h1, from h1 },
        show ∃σ' Q', ⊩ (σ'[x↦v]) : Q', from ih this
      )
    },
    case env.dvcgen.num n σ' y Q y_not_in_σ' σ'_verified ih { from
      have env.apply (σ'[y↦value.num n]) x = v, from σ_x_is_v,
      have h1: (if y = x ∧ option.is_none (σ'.apply x) then ↑(value.num n) else σ'.apply x) = v,
      by { unfold env.apply at this, from this },
      if h2: y = x ∧ option.is_none (σ'.apply x) then (
        have ↑(value.num n) = ↑v, by { simp[h2] at h1, from h1 },
        have v_is_num: v = value.num n, from (option.some.inj this).symm,
        have x_not_in_σ': x ∉ σ', from h2.left ▸ y_not_in_σ',
        have ⊩ (σ'[x↦value.num n]) : Q ⋀ x ≡ value.num n, from env.dvcgen.num x_not_in_σ' σ'_verified,
        have ⊩ (σ'[x↦v]) : Q ⋀ x ≡ value.num n, from v_is_num.symm ▸ this,
        show ∃σ' Q', ⊩ (σ'[x↦v]) : Q',
        from exists.intro σ' (exists.intro (Q ⋀ x ≡ value.num n) this)
      ) else (
        have (σ'.apply x) = v, by { simp[h2] at h1, from h1 },
        show ∃σ' Q', ⊩ (σ'[x↦v]) : Q', from ih this
      )
    },
    case env.dvcgen.func f σ₂ σ₁ g gx R S e Q₁ Q₂ Q₃ f_not_in_σ₁ g_not_in_σ₂ gx_not_in_σ₂ g_neq_gx
                        σ₁_verified σ₂_verified x_free_in_R fv_R fv_S e_verified func_vc ih₁ ih₂ { from
      have env.apply (σ₁[f↦value.func g gx R S e σ₂]) x = v, from σ_x_is_v,
      have h1: (if f = x ∧ option.is_none (σ₁.apply x) then ↑(value.func g gx R S e σ₂) else σ₁.apply x) = v,
      by { unfold env.apply at this, from this },
      if h2: f = x ∧ option.is_none (σ₁.apply x) then (
        have ↑(value.func g gx R S e σ₂) = ↑v, by { simp[h2] at h1, from h1 },
        have v_is_num: v = value.func g gx R S e σ₂, from (option.some.inj this).symm,
        have x_not_in_σ₁: x ∉ σ₁, from h2.left ▸ f_not_in_σ₁,
        have ⊩ (σ₁[x↦value.func g gx R S e σ₂]) :
                  (Q₁
                  ⋀ x ≡ value.func g gx R S e σ₂
                  ⋀ prop.subst_env (σ₂[g↦value.func g gx R S e σ₂]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
        from env.dvcgen.func x_not_in_σ₁ g_not_in_σ₂ gx_not_in_σ₂ g_neq_gx
                             σ₁_verified σ₂_verified x_free_in_R fv_R fv_S e_verified func_vc,
        have ⊩ (σ₁[x↦v]) :
                  (Q₁
                  ⋀ x ≡ value.func g gx R S e σ₂
                  ⋀ prop.subst_env (σ₂[g↦value.func g gx R S e σ₂]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
        from v_is_num.symm ▸ this,
        show ∃σ₁ Q', ⊩ (σ₁[x↦v]) : Q',
        from exists.intro σ₁ (exists.intro (Q₁
                  ⋀ x ≡ value.func g gx R S e σ₂
                  ⋀ prop.subst_env (σ₂[g↦value.func g gx R S e σ₂]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))) this)
      ) else (
        have (σ₁.apply x) = v, by { simp[h2] at h1, from h1 },
        show ∃σ₁ Q₁, ⊩ (σ₁[x↦v]) : Q₁, from ih₁ this
      )
    }
  end

lemma env.dvcgen.tru.inv {σ: env} {x: var} {Q: prop}:
    (⊩ (σ[x ↦ value.true]) : Q ⋀ x ≡ value.true) → x ∉ σ ∧ (⊩ σ : Q) :=
  assume h: ⊩ (σ[x ↦ value.true]) : Q ⋀ x ≡ value.true,
  begin
    cases h,
    case env.dvcgen.tru h1 h2 { from ⟨h1, h2⟩ }
  end

lemma env.dvcgen.fls.inv {σ: env} {x: var} {Q: prop}:
    (⊩ (σ[x ↦ value.false]) : Q ⋀ x ≡ value.false) → x ∉ σ ∧ (⊩ σ : Q) :=
  assume h: ⊩ (σ[x ↦ value.false]) : Q ⋀ x ≡ value.false,
  begin
    cases h,
    case env.dvcgen.fls h1 h2 { from ⟨h1, h2⟩ }
  end

lemma env.dvcgen.num.inv {σ: env} {x: var} {n: ℕ} {Q: prop}:
    (⊩ (σ[x ↦ value.num n]) : Q ⋀ x ≡ value.num n) → x ∉ σ ∧ (⊩ σ : Q) :=
  assume h: ⊩ (σ[x ↦ value.num n]) : Q ⋀ x ≡ value.num n,
  begin
    cases h,
    case env.dvcgen.num h1 h2 { from ⟨h1, h2⟩ }
  end

lemma env.dvcgen.func.inv {σ₁ σ₂: env} {f g x: var} {R S: spec} {e: exp} {Q: prop}:
      (⊩ (σ₁[f ↦ value.func g x R S e σ₂]) : Q) →
      ∃Q₁ Q₂ Q₃,
      f ∉ σ₁ ∧
      g ∉ σ₂ ∧
      x ∉ σ₂ ∧
      g ≠ x ∧
      (⊩ σ₁ : Q₁) ∧
      (⊩ σ₂ : Q₂) ∧
      x ∈ FV R.to_prop.to_vc ∧
      FV R.to_prop ⊆ FV Q₂ ∪ { g, x } ∧
      FV S.to_prop ⊆ FV Q₂ ∪ { g, x } ∧
      (Q₂ ⋀ spec.func g x R S ⋀ R ⊩ e : Q₃) ∧
      ⦃ prop.implies (Q₂ ⋀ spec.func g x R S ⋀ R ⋀ Q₃ (term.app g x)) S ⦄ ∧
      (Q = (Q₁ ⋀
           ((f ≡ (value.func g x R S e σ₂)) ⋀
           prop.subst_env (σ₂[g↦value.func g x R S e σ₂])
           (prop.func g x R (Q₃ (term.app g ↑x) ⋀ S))))) :=
  assume h : ⊩ (σ₁[f ↦ value.func g x R S e σ₂]) : Q,
  begin
    cases h,
    case env.dvcgen.func Q₁ Q₂ Q₃ f_not_in_σ₁ g_not_in_σ₂ x_not_in_σ₂ g_neq_x
                        σ₁_verified σ₂_verified x_free_in_R fv_R fv_S e_verified func_vc {
      from ⟨Q₁, ⟨Q₂, ⟨Q₃,
           ⟨f_not_in_σ₁, ⟨g_not_in_σ₂, ⟨x_not_in_σ₂, ⟨g_neq_x, ⟨σ₁_verified,
           ⟨σ₂_verified, ⟨x_free_in_R, ⟨fv_R, ⟨fv_S, ⟨e_verified, ⟨func_vc, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
    }
  end

lemma env.dvcgen.copy {σ₁ σ₂: env} {P₁ P₂} {x y: var} {v: value}:
      (⊩ σ₁ : P₁) → (y ∉ σ₁) → (⊩ (σ₂[x↦v]) : P₂) → ∃P₃, (⊩ (σ₁[y↦v]) : P₁ ⋀ P₃) :=
  assume σ₁_verified: ⊩ σ₁ : P₁,
  assume y_not_in_σ₁: y ∉ σ₁,
  assume σ₂_xv_verified: ⊩ (σ₂[x↦v]) : P₂,
  show ∃P₃, (⊩ (σ₁[y↦v]) : P₁ ⋀ P₃), by begin
    cases σ₂_xv_verified,
    case env.dvcgen.tru { from
      have ⊩ (σ₁[y↦value.true]) : P₁ ⋀ y ≡ value.true,
      from env.dvcgen.tru y_not_in_σ₁ σ₁_verified,
      show ∃P₃, ⊩ (σ₁[y↦value.true]) : P₁ ⋀ P₃, from exists.intro (y ≡ value.true) this
    },
    case env.dvcgen.fls { from
      have ⊩ (σ₁[y↦value.false]) : P₁ ⋀ y ≡ value.false,
      from env.dvcgen.fls y_not_in_σ₁ σ₁_verified,
      show ∃P₃, ⊩ (σ₁[y↦value.false]) : P₁ ⋀ P₃, from exists.intro (y ≡ value.false) this
    },
    case env.dvcgen.num n { from
      have ⊩ (σ₁[y↦value.num n]) : P₁ ⋀ y ≡ value.num n,
      from env.dvcgen.num y_not_in_σ₁ σ₁_verified,
      show ∃P₃, ⊩ (σ₁[y↦value.num n]) : P₁ ⋀ P₃, from exists.intro (y ≡ value.num n) this
    },
    case env.dvcgen.func σ₃ f fx R S e Q₃ Q₄ Q₂ x_not_in_σ₂ f_not_in_σ₃ fx_not_in_σ₃
                        f_neq_fx σ₂_verified σ₃_verified x_free_in_R fv_R fv_S e_verified func_vc { from
      have ⊩ (σ₁[y↦value.func f fx R S e σ₃]) : (P₁
        ⋀ y ≡ value.func f fx R S e σ₃
        ⋀ prop.subst_env (σ₃[f↦value.func f fx R S e σ₃]) (prop.func f fx R (Q₃ (term.app f fx) ⋀ S))),
      from env.dvcgen.func y_not_in_σ₁ f_not_in_σ₃ fx_not_in_σ₃
                        f_neq_fx σ₁_verified σ₃_verified x_free_in_R fv_R fv_S e_verified func_vc,
      show ∃P₃, ⊩ (σ₁[y↦value.func f fx R S e σ₃]) : P₁ ⋀ P₃,
      from exists.intro (
        y ≡ value.func f fx R S e σ₃
       ⋀ prop.subst_env (σ₃[f↦value.func f fx R S e σ₃]) (prop.func f fx R (Q₃ (term.app f fx) ⋀ S)))
      this
    }
  end

lemma exp.dvcgen.inj {P: prop} {Q: propctx} {e: exp}: (P ⊩ e : Q) → ∀Q', (P ⊩ e : Q') → (Q = Q') :=
  assume h1: P ⊩ e : Q,
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

lemma env.dvcgen.inj {P: prop} {σ: env}: (⊩ σ : P) → ∀Q, (⊩ σ : Q) → (P = Q) :=
  assume h1: ⊩ σ : P,
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
    have : (Q₃ = Q₃_1), from exp.dvcgen.inj a_9 Q₃_1 a_20,
    rw[this],
    refl
  end

lemma stack.dvcgen.inj {s: dstack} {Q₁: propctx}: (⊩ₛ s : Q₁) → ∀Q₂, (⊩ₛ s : Q₂) → (Q₁ = Q₂) :=
  assume h1: ⊩ₛ s : Q₁,
  have ∀s' Q₂, (s = s') → (⊩ₛ s' : Q₂) → (Q₁ = Q₂), by begin
    cases h1,

    intros s' Q₂ h2 h3,
    cases h3,

    injection h2,
    have h4: (R = R_1), from h_1,
    have h6: (σ = σ_1), from h_2,
    have h7: (e = e_1), from h_3,
    have h8: (P = P_1), from env.dvcgen.inj a P_1 (h6.symm ▸ a_4),
    have : ↑R ⋀ P ⊩ e : Q_1, from h4.symm ▸ h7.symm ▸ h8.symm ▸ a_7,
    have h9: (Q = Q_1), from exp.dvcgen.inj a_3 Q_1 this,
    rw[←h8],
    rw[←h9],

    contradiction,

    intros s' Q₂ h2 h3,
    cases h3,

    contradiction,

    injection h2,

    have h4: (P₁ = P₁_1), from env.dvcgen.inj a_2 P₁_1 (h_3.symm ▸ a_17),
    rw[h4.symm] at a_24,
    rw[h_4.symm] at a_24,
    rw[h_5.symm] at a_24,
    rw[h_7.symm] at a_24,
    rw[h_6.symm] at a_24,
    rw[h_2.symm] at a_24,
    have h5: (Q₁_1 = Q₁), from exp.dvcgen.inj a_9 Q₁ a_24,
    rw[←h4],
    rw[←h_5],
    rw[←h_6],
    rw[←h_4],
    rw[h5]
  end,
  show ∀Q₂, (⊩ₛ s : Q₂) → (Q₁ = Q₂),
  from λQ₂ h1, (this s Q₂) rfl h1
