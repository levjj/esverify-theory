import .syntax .notations .evaluation .freevars .substitution

reserve infix `⊢`:10

inductive exp.vcgen : prop → exp → propctx → Prop
notation P `⊢` e `:` Q : 10 := exp.vcgen P e Q

| tru {P: prop} {x: var} {e: exp} {Q: propctx}:
    x ∉ FV P →
    (P ⋀ x ≡ value.true ⊢ e : Q) →
    (P ⊢ lett x = true in e : propctx.exis x (x ≡ value.true ⋀ Q))

| fals {P: prop} {x: var} {e: exp} {Q: propctx}:
    x ∉ FV P →
    (P ⋀ x ≡ value.false ⊢ e : Q) →
    (P ⊢ letf x = false in e : propctx.exis x (x ≡ value.false ⋀ Q))

| num {P: prop} {x: var} {n: ℕ} {e: exp} {Q: propctx}:
    x ∉ FV P →
    (P ⋀ x ≡ value.num n ⊢ e : Q) →
    (P ⊢ letn x = n in e : propctx.exis x (x ≡ value.num n ⋀ Q))

| func {P: prop} {f x: var} {R S: spec} {e₁ e₂: exp} {Q₁ Q₂: propctx}:
    f ∉ FV P →
    x ∉ FV P →
    f ≠ x →
    FV R.to_prop ⊆ FV P ∪ { f, x } →
    FV S.to_prop ⊆ FV P ∪ { f, x } →
    (P ⋀ spec.func f x R S ⋀ R ⊢ e₁ : Q₁) →
    (P ⋀ prop.func f x R (Q₁ (term.app f x) ⋀ S) ⊢ e₂ : Q₂) →
    ⟪prop.implies (P ⋀ spec.func f x R S ⋀ R ⋀ Q₁ (term.app f x)) S⟫ →
    (P ⊢ letf f[x] req R ens S {e₁} in e₂ : propctx.exis f (prop.func f x R (Q₁ (term.app f x) ⋀ S) ⋀ Q₂))

| unop {P: prop} {op: unop} {e: exp} {x y: var} {Q: propctx}:
    x ∈ FV P →
    y ∉ FV P →
    (P ⋀ y ≡ term.unop op x ⊢ e : Q) →
    ⟪ prop.implies P (prop.pre₁ op x) ⟫ →
    (P ⊢ letop y = op [x] in e : propctx.exis y (y ≡ term.unop op x ⋀ Q))

| binop {P: prop} {op: binop} {e: exp} {x y z: var} {Q: propctx}:
    x ∈ FV P →
    y ∈ FV P →
    z ∉ FV P →
    (P ⋀ z ≡ term.binop op x y ⊢ e : Q) →
    ⟪ prop.implies P (prop.pre₂ op x y) ⟫ →
    (P ⊢ letop2 z = op [x, y] in e : propctx.exis z (z ≡ term.binop op x y ⋀ Q))

| app {P: prop} {e: exp} {y f x: var} {Q: propctx}:
    f ∈ FV P →
    x ∈ FV P →
    y ∉ FV P →
    (P ⋀ prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⊢ e : Q) →
    ⟪ prop.implies (P ⋀ prop.call f x) (term.unop unop.isFunc f ⋀ prop.pre f x) ⟫ →
    (P ⊢ letapp y = f [x] in e : propctx.exis y (prop.call f x ⋀ prop.post f x ⋀ y ≡ term.app f x ⋀ Q))

| ite {P: prop} {e₁ e₂: exp} {x: var} {Q₁ Q₂: propctx}:
    x ∈ FV P →
    (P ⋀ x ⊢ e₁ : Q₁) →
    (P ⋀ term.unop unop.not x ⊢ e₂ : Q₂) →
    ⟪ prop.implies P (term.unop unop.isBool x) ⟫ →
    (P ⊢ exp.ite x e₁ e₂ : propctx.implies x Q₁ ⋀ propctx.implies (term.unop unop.not x) Q₂)

| return {P: prop} {x: var}:
    x ∈ FV P →
    (P ⊢ exp.return x : x ≣ •)

notation P `⊢` e `:` Q : 10 := exp.vcgen P e Q

inductive env.vcgen : env → prop → Prop
notation `⊢` σ `:` Q : 10 := env.vcgen σ Q

| empty:
    ⊢ env.empty : value.true

| tru {σ: env} {x: var} {Q: prop}:
    x ∉ σ →
    (⊢ σ : Q) →
    (⊢ (σ[x ↦ value.true]) : Q ⋀ x ≡ value.true)

| fls {σ: env} {x: var} {Q: prop}:
    x ∉ σ →
    (⊢ σ : Q) →
    (⊢ (σ[x ↦ value.false]) : Q ⋀ x ≡ value.false)

| num {n: ℤ} {σ: env} {x: var} {Q: prop}:
    x ∉ σ →
    (⊢ σ : Q) →
    (⊢ (σ[x ↦ value.num n]) : Q ⋀ x ≡ value.num n)

| func {σ₁ σ₂: env} {f g x: var} {R S: spec} {e: exp} {Q₁ Q₂: prop} {Q₃: propctx}:
    f ∉ σ₁ →
    g ∉ σ₂ →
    x ∉ σ₂ →
    g ≠ x →
    (⊢ σ₁ : Q₁) →
    (⊢ σ₂ : Q₂) →
    FV R.to_prop ⊆ FV Q₂ ∪ { g, x } →
    FV S.to_prop ⊆ FV Q₂ ∪ { g, x } →
    (Q₂ ⋀ spec.func g x R S ⋀ R ⊢ e : Q₃) →
    ⟪prop.implies (Q₂ ⋀ spec.func g x R S ⋀ R ⋀ Q₃ (term.app g x)) S⟫ →
    (⊢ (σ₁[f ↦ value.func g x R S e σ₂]) :
      (Q₁
       ⋀ f ≡ value.func g x R S e σ₂
       ⋀ prop.subst_env (σ₂[g↦value.func g x R S e σ₂]) (prop.func g x R (Q₃ (term.app g x) ⋀ S))))

notation `⊢` σ `:` Q : 10 := env.vcgen σ Q

inductive stack.vcgen : callhistory → stack → Prop
notation H `⊢ₛ` s : 10 := stack.vcgen H s

| top {H: callhistory} {P: prop} {σ: env} {e: exp} {Q: propctx}:
    (⊢ σ : P) →
    (H ⋀ P ⊢ e : Q) →
    (H ⊢ₛ (σ, e))

| cons {H: callhistory} {P: prop} {s: stack} {σ₁ σ₂: env}
       {f fx g x y: var} {R S: spec} {e₁ e₂: exp} {v: value} {Q: propctx}:
    (H ⊢ₛ s) →
    (⊢ σ₁ : P) →
    (σ₁ g = value.func f fx R S e₂ σ₂) →
    (σ₁ x = v) →
    y ∉ σ₁ →
    (H ⋀ P ⋀ prop.call g x ⋀ prop.post g x ⋀ y ≡ term.app g x ⊢ e₁ : Q) →
    ⟪ prop.implies (H ⋀ P ⋀ prop.call g x) (term.unop unop.isFunc g ⋀ prop.pre g x) ⟫ →
    ((σ₂[f↦value.func f fx R S e₂ σ₂][fx↦v], e₂) ⟶* s) →
    (H ⊢ₛ (s · [σ₁, let y = g[x] in e₁]))

notation H `⊢ₛ` s : 10 := stack.vcgen H s

-- lemmas

lemma exp.vcgen.return.inv {P: prop} {x: var} {Q: propctx}: (P ⊢ exp.return x : Q) → x ∈ FV P :=
  assume return_verified: P ⊢ exp.return x : Q,
  begin
    cases return_verified,
    case exp.vcgen.return x_free {
      show x ∈ FV P, from x_free
    }
  end

lemma stack.vcgen.top.inv {H: callhistory} {σ: env} {e: exp}: (H ⊢ₛ (σ, e)) → ∃P Q, (⊢ σ: P) ∧ (H ⋀ P ⊢ e: Q) :=
  assume top_verified: H ⊢ₛ (σ, e),
  begin
    cases top_verified,
    case stack.vcgen.top P Q env_verified e_verified {
      show ∃P Q, (⊢ σ: P) ∧ (H ⋀ P ⊢ e: Q), from exists.intro P (exists.intro Q ⟨env_verified, e_verified⟩)
    }
  end

lemma env.vcgen.inv {σ: env} {P: prop} {x: var} {v: value}:
      (⊢ σ : P) → (σ x = v) → ∃σ' Q', ⊢ (σ'[x↦v]) : Q' :=
  assume env_verified: ⊢ σ : P,
  assume σ_x_is_v: σ x = v,
  show ∃σ' Q', ⊢ (σ'[x↦v]) : Q', by begin
    induction env_verified,
    case env.vcgen.empty { from
      have env.apply env.empty x = none, by unfold env.apply,
      have some v = none, from eq.trans σ_x_is_v.symm this,
      show ∃σ' Q', ⊢ (σ'[x↦v]) : Q', from false.elim (option.no_confusion this)
    },
    case env.vcgen.tru σ' y Q y_not_in_σ' σ'_verified ih { from
      have env.apply (σ'[y↦value.true]) x = v, from σ_x_is_v,
      have h1: (if y = x ∧ option.is_none (σ'.apply x) then ↑value.true else σ'.apply x) = v,
      by { unfold env.apply at this, from this },
      if h2: y = x ∧ option.is_none (σ'.apply x) then (
        have (↑value.true) = ↑v, by { simp[h2] at h1, from h1 },
        have v_is_true: v = value.true, from (option.some.inj this).symm,
        have x_not_in_σ': x ∉ σ', from h2.left ▸ y_not_in_σ',
        have ⊢ (σ'[x↦value.true]) : Q ⋀ x ≡ value.true, from env.vcgen.tru x_not_in_σ' σ'_verified,
        have ⊢ (σ'[x↦v]) : Q ⋀ x ≡ value.true, from v_is_true.symm ▸ this,
        show ∃σ' Q', ⊢ (σ'[x↦v]) : Q',
        from exists.intro σ' (exists.intro (Q ⋀ x ≡ value.true) this)
      ) else (
        have (σ'.apply x) = v, by { simp[h2] at h1, from h1 },
        show ∃σ' Q', ⊢ (σ'[x↦v]) : Q', from ih this
      )
    },
    case env.vcgen.fls σ' y Q y_not_in_σ' σ'_verified ih { from
      have env.apply (σ'[y↦value.false]) x = v, from σ_x_is_v,
      have h1: (if y = x ∧ option.is_none (σ'.apply x) then ↑value.false else σ'.apply x) = v,
      by { unfold env.apply at this, from this },
      if h2: y = x ∧ option.is_none (σ'.apply x) then (
        have (↑value.false) = ↑v, by { simp[h2] at h1, from h1 },
        have v_is_false: v = value.false, from (option.some.inj this).symm,
        have x_not_in_σ': x ∉ σ', from h2.left ▸ y_not_in_σ',
        have ⊢ (σ'[x↦value.false]) : Q ⋀ x ≡ value.false, from env.vcgen.fls x_not_in_σ' σ'_verified,
        have ⊢ (σ'[x↦v]) : Q ⋀ x ≡ value.false, from v_is_false.symm ▸ this,
        show ∃σ' Q', ⊢ (σ'[x↦v]) : Q',
        from exists.intro σ' (exists.intro (Q ⋀ x ≡ value.false) this)
      ) else (
        have (σ'.apply x) = v, by { simp[h2] at h1, from h1 },
        show ∃σ' Q', ⊢ (σ'[x↦v]) : Q', from ih this
      )
    },
    case env.vcgen.num n σ' y Q y_not_in_σ' σ'_verified ih { from
      have env.apply (σ'[y↦value.num n]) x = v, from σ_x_is_v,
      have h1: (if y = x ∧ option.is_none (σ'.apply x) then ↑(value.num n) else σ'.apply x) = v,
      by { unfold env.apply at this, from this },
      if h2: y = x ∧ option.is_none (σ'.apply x) then (
        have ↑(value.num n) = ↑v, by { simp[h2] at h1, from h1 },
        have v_is_num: v = value.num n, from (option.some.inj this).symm,
        have x_not_in_σ': x ∉ σ', from h2.left ▸ y_not_in_σ',
        have ⊢ (σ'[x↦value.num n]) : Q ⋀ x ≡ value.num n, from env.vcgen.num x_not_in_σ' σ'_verified,
        have ⊢ (σ'[x↦v]) : Q ⋀ x ≡ value.num n, from v_is_num.symm ▸ this,
        show ∃σ' Q', ⊢ (σ'[x↦v]) : Q',
        from exists.intro σ' (exists.intro (Q ⋀ x ≡ value.num n) this)
      ) else (
        have (σ'.apply x) = v, by { simp[h2] at h1, from h1 },
        show ∃σ' Q', ⊢ (σ'[x↦v]) : Q', from ih this
      )
    },
    case env.vcgen.func f σ₂ σ₁ g gx R S e Q₁ Q₂ Q₃ f_not_in_σ₁ g_not_in_σ₂ gx_not_in_σ₂ g_neq_gx
                        σ₁_verified σ₂_verified fv_R fv_S e_verified func_vc ih₁ ih₂ { from
      have env.apply (σ₁[f↦value.func g gx R S e σ₂]) x = v, from σ_x_is_v,
      have h1: (if f = x ∧ option.is_none (σ₁.apply x) then ↑(value.func g gx R S e σ₂) else σ₁.apply x) = v,
      by { unfold env.apply at this, from this },
      if h2: f = x ∧ option.is_none (σ₁.apply x) then (
        have ↑(value.func g gx R S e σ₂) = ↑v, by { simp[h2] at h1, from h1 },
        have v_is_num: v = value.func g gx R S e σ₂, from (option.some.inj this).symm,
        have x_not_in_σ₁: x ∉ σ₁, from h2.left ▸ f_not_in_σ₁,
        have ⊢ (σ₁[x↦value.func g gx R S e σ₂]) :
                  (Q₁
                  ⋀ x ≡ value.func g gx R S e σ₂
                  ⋀ prop.subst_env (σ₂[g↦value.func g gx R S e σ₂]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
        from env.vcgen.func x_not_in_σ₁ g_not_in_σ₂ gx_not_in_σ₂ g_neq_gx
                            σ₁_verified σ₂_verified fv_R fv_S e_verified func_vc,
        have ⊢ (σ₁[x↦v]) :
                  (Q₁
                  ⋀ x ≡ value.func g gx R S e σ₂
                  ⋀ prop.subst_env (σ₂[g↦value.func g gx R S e σ₂]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
        from v_is_num.symm ▸ this,
        show ∃σ₁ Q', ⊢ (σ₁[x↦v]) : Q',
        from exists.intro σ₁ (exists.intro (Q₁
                  ⋀ x ≡ value.func g gx R S e σ₂
                  ⋀ prop.subst_env (σ₂[g↦value.func g gx R S e σ₂]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))) this)
      ) else (
        have (σ₁.apply x) = v, by { simp[h2] at h1, from h1 },
        show ∃σ₁ Q₁, ⊢ (σ₁[x↦v]) : Q₁, from ih₁ this
      )
    }
  end

lemma env.vcgen.tru.inv {σ: env} {x: var} {Q: prop}:
    (⊢ (σ[x ↦ value.true]) : Q ⋀ x ≡ value.true) → x ∉ σ ∧ (⊢ σ : Q) :=
  assume h: ⊢ (σ[x ↦ value.true]) : Q ⋀ x ≡ value.true,
  begin
    cases h,
    case env.vcgen.tru h1 h2 { from ⟨h1, h2⟩ }
  end

lemma env.vcgen.fls.inv {σ: env} {x: var} {Q: prop}:
    (⊢ (σ[x ↦ value.false]) : Q ⋀ x ≡ value.false) → x ∉ σ ∧ (⊢ σ : Q) :=
  assume h: ⊢ (σ[x ↦ value.false]) : Q ⋀ x ≡ value.false,
  begin
    cases h,
    case env.vcgen.fls h1 h2 { from ⟨h1, h2⟩ }
  end

lemma env.vcgen.num.inv {σ: env} {x: var} {n: ℕ} {Q: prop}:
    (⊢ (σ[x ↦ value.num n]) : Q ⋀ x ≡ value.num n) → x ∉ σ ∧ (⊢ σ : Q) :=
  assume h: ⊢ (σ[x ↦ value.num n]) : Q ⋀ x ≡ value.num n,
  begin
    cases h,
    case env.vcgen.num h1 h2 { from ⟨h1, h2⟩ }
  end

lemma env.vcgen.func.inv {σ₁ σ₂: env} {f g x: var} {R S: spec} {e: exp} {Q: prop}:
      (⊢ (σ₁[f ↦ value.func g x R S e σ₂]) : Q) →
      ∃Q₁ Q₂ Q₃,
      f ∉ σ₁ ∧
      g ∉ σ₂ ∧
      x ∉ σ₂ ∧
      g ≠ x ∧
      (⊢ σ₁ : Q₁) ∧
      (⊢ σ₂ : Q₂) ∧
      FV R.to_prop ⊆ FV Q₂ ∪ { g, x } ∧
      FV S.to_prop ⊆ FV Q₂ ∪ { g, x } ∧
      (Q₂ ⋀ spec.func g x R S ⋀ R ⊢ e : Q₃) ∧
      ⟪prop.implies (Q₂ ⋀ spec.func g x R S ⋀ R ⋀ Q₃ (term.app g x)) S⟫ ∧
      (Q = (Q₁ ⋀
           ((f ≡ (value.func g x R S e σ₂)) ⋀
           prop.subst_env (σ₂[g↦value.func g x R S e σ₂])
           (prop.func g x R (Q₃ (term.app g ↑x) ⋀ S))))) :=
  assume h : ⊢ (σ₁[f ↦ value.func g x R S e σ₂]) : Q,
  begin
    cases h,
    case env.vcgen.func Q₁ Q₂ Q₃ f_not_in_σ₁ g_not_in_σ₂ x_not_in_σ₂ g_neq_x
                        σ₁_verified σ₂_verified fv_R fv_S e_verified func_vc {
      from ⟨Q₁, ⟨Q₂, ⟨Q₃,
           ⟨f_not_in_σ₁, ⟨g_not_in_σ₂, ⟨x_not_in_σ₂, ⟨g_neq_x, ⟨σ₁_verified,
           ⟨σ₂_verified, ⟨fv_R, ⟨fv_S, ⟨e_verified, ⟨func_vc, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
    }
  end

lemma env.vcgen.copy {σ₁ σ₂: env} {P₁ P₂} {x y: var} {v: value}:
      (⊢ σ₁ : P₁) → (y ∉ σ₁) → (⊢ (σ₂[x↦v]) : P₂) → ∃P₃, (⊢ (σ₁[y↦v]) : P₃) :=
  assume σ₁_verified: ⊢ σ₁ : P₁,
  assume y_not_in_σ₁: y ∉ σ₁,
  assume σ₂_xv_verified: ⊢ (σ₂[x↦v]) : P₂,
  show ∃P₃, (⊢ (σ₁[y↦v]) : P₃), by begin
    cases σ₂_xv_verified,
    case env.vcgen.tru { from
      have ⊢ (σ₁[y↦value.true]) : P₁ ⋀ y ≡ value.true,
      from env.vcgen.tru y_not_in_σ₁ σ₁_verified,
      show ∃P₃, ⊢ (σ₁[y↦value.true]) : P₃, from exists.intro (P₁ ⋀ y ≡ value.true) this
    },
    case env.vcgen.fls { from
      have ⊢ (σ₁[y↦value.false]) : P₁ ⋀ y ≡ value.false,
      from env.vcgen.fls y_not_in_σ₁ σ₁_verified,
      show ∃P₃, ⊢ (σ₁[y↦value.false]) : P₃, from exists.intro (P₁ ⋀ y ≡ value.false) this
    },
    case env.vcgen.num n { from
      have ⊢ (σ₁[y↦value.num n]) : P₁ ⋀ y ≡ value.num n,
      from env.vcgen.num y_not_in_σ₁ σ₁_verified,
      show ∃P₃, ⊢ (σ₁[y↦value.num n]) : P₃, from exists.intro (P₁ ⋀ y ≡ value.num n) this
    },
    case env.vcgen.func σ₃ f fx R S e Q₃ Q₄ Q₂ x_not_in_σ₂ f_not_in_σ₃ fx_not_in_σ₃
                        f_neq_fx σ₂_verified σ₃_verified fv_R fv_S e_verified func_vc { from
      have ⊢ (σ₁[y↦value.func f fx R S e σ₃]) : (P₁
        ⋀ y ≡ value.func f fx R S e σ₃
        ⋀ prop.subst_env (σ₃[f↦value.func f fx R S e σ₃]) (prop.func f fx R (Q₃ (term.app f fx) ⋀ S))),
      from env.vcgen.func y_not_in_σ₁ f_not_in_σ₃ fx_not_in_σ₃
                        f_neq_fx σ₁_verified σ₃_verified fv_R fv_S e_verified func_vc,
      show ∃P₃, ⊢ (σ₁[y↦value.func f fx R S e σ₃]) : P₃,
      from exists.intro (P₁
       ⋀ y ≡ value.func f fx R S e σ₃
       ⋀ prop.subst_env (σ₃[f↦value.func f fx R S e σ₃]) (prop.func f fx R (Q₃ (term.app f fx) ⋀ S)))
      this
    }
  end