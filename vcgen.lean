import .syntax .notations .evaluation .logic

reserve infix `⊢`:10

inductive exp.vcgen : prop → exp → propctx → Prop
notation P `⊢` e `:` Q : 10 := exp.vcgen P e Q

| tru {P: prop} {x: var} {e: exp} {Q: propctx}:
    x ∉ FV P →
    (P && (x ≡ value.true) ⊢ e : Q) →
    (P ⊢ lett x = true in e : propctx.exis x ((x ≡ value.true) && Q))

| fals {P: prop} {x: var} {e: exp} {Q: propctx}:
    x ∉ FV P →
    (P && (x ≡ value.false) ⊢ e : Q) →
    (P ⊢ letf x = false in e : propctx.exis x ((x ≡ value.false) && Q))

| num {P: prop} {x: var} {n: ℕ} {e: exp} {Q: propctx}:
    x ∉ FV P →
    (P && (x ≡ value.num n) ⊢ e : Q) →
    (P ⊢ letn x = n in e : propctx.exis x ((x ≡ value.num n) && Q))

| func {P: prop} {f x: var} {R S: spec} {e₁ e₂: exp} {Q₁ Q₂: propctx}:
    f ∉ FV P →
    x ∉ FV P →
    FV R.to_prop ⊆ FV P →
    FV S.to_prop ⊆ FV P →
    (P && spec.func f x R S && R ⊢ e₂ : Q₂) →
    ⟪prop.implies (P && spec.func f x R S && R && Q₂ (term.app f x)) S⟫ →
    (P ⊢ letf f[x] req R ens S {e₁} in e₂ :
         propctx.exis f (spec.func f x R S && Q₁))

| unop {P: prop} {op: unop} {e: exp} {x y: var} {Q: propctx}:
    x ∈ FV P →
    y ∉ FV P →
    (P && (y ≡ term.unop op x) ⊢ e : Q) →
    ⟪ prop.implies P (prop.pre₁ op x) ⟫ →
    (P ⊢ letop y = op [x] in e : propctx.exis y ((y ≡ term.unop op x) && Q))

| binop {P: prop} {op: binop} {e: exp} {x y z: var} {Q: propctx}:
    x ∈ FV P →
    y ∈ FV P →
    z ∉ FV P →
    (P && (z ≡ term.binop op x y) ⊢ e : Q) →
    ⟪ prop.implies P (prop.pre₂ op x y) ⟫ →
    (P ⊢ letop2 y = op [x, y] in e : propctx.exis y ((z ≡ term.binop op x y) && Q))

| app {P: prop} {e: exp} {y f x: var} {Q: propctx}:
    f ∈ FV P →
    x ∈ FV P →
    y ∉ FV P →
    (P && prop.call f x && (y ≡ term.app f x) && prop.post f x ⊢ e : Q) →
    ⟪ prop.implies (P && prop.call f x) (term.unop unop.isFunc f && prop.pre f x) ⟫ →
    (P ⊢ letapp y = f [x] in e : propctx.exis y (prop.call f x && (y ≡ term.app f x) && prop.post f x && Q))

| ite {P: prop} {e₁ e₂: exp} {x: var} {Q₁ Q₂: propctx}:
    x ∈ FV P →
    (P && x ⊢ e₁ : Q₁) →
    (P && term.unop unop.not x ⊢ e₂ : Q₂) →
    ⟪ prop.implies P (term.unop unop.isBool x) ⟫ →
    (P ⊢ exp.ite x e₁ e₂ : (propctx.implies x Q₁ && propctx.implies (term.unop unop.not x) Q₂))

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
    (⊢ (σ[x ↦ value.true]) : (Q && (x ≡ value.true)))

| fls {σ: env} {x: var} {Q: prop}:
    x ∉ σ →
    (⊢ σ : Q) →
    (⊢ (σ[x ↦ value.false]) : (Q && (x ≡ value.false)))

| num {n: ℤ} {σ: env} {x: var} {Q: prop}:
    x ∉ σ →
    (⊢ σ : Q) →
    (⊢ (σ[x ↦ value.num n]) : (Q && (x ≡ value.num n)))

| func {σ₁ σ₂: env} {f g x: var} {R S: spec} {e: exp} {Q₁ Q₂: prop} {Q₃: propctx}:
    f ∉ σ₁ →
    (⊢ σ₁ : Q₁) →
    (⊢ σ₂ : Q₂) →
    FV R.to_prop ⊆ FV Q₂ ∪ { g, x } →
    FV S.to_prop ⊆ FV Q₂ ∪ { g, x } →
    (Q₂ && spec.func g x R S && R ⊢ e : Q₃) →
    ⟪prop.implies (Q₂ && spec.func g x R S && R && Q₃ (term.app g x)) S⟫ →
    (⊢ (σ₁[f ↦ value.func g x R S e σ₂]) :
      (Q₁ &&
       spec.func f x (spec.subst_env (σ₂[g↦value.func g x R S e σ₂]) R)
                     (spec.subst_env (σ₂[g↦value.func g x R S e σ₂]) S) &&
       (f ≡ value.func g x R S e σ₂)))

notation `⊢` σ `:` Q : 10 := env.vcgen σ Q

inductive stack.vcgen : list call → stack → Prop
notation H `⊩` s : 10 := stack.vcgen H s

| top {H: list call} {P: prop} {σ: env} {e: exp} {Q: propctx}:
    (⊢ σ : P) →
    (H && P ⊢ e : Q) →
    (H ⊩ (σ, e))

| cons {H: list call} {P: prop} {s: stack} {σ σ': env} {f g x y z: var} {R S: spec} {e: exp} {v: value} {Q: propctx}:
    (H ⊩ s) →
    (⊢ σ : P) →
    (σ f = value.func g z R S e σ') →
    (σ x = v) →
    ((σ[g↦value.func g z R S e σ'][z↦v], e) ⟶* s) →
    (H && P ⊢ letapp y = f[x] in e : Q) →
    (H ⊩ (s · [σ, let y = f[x] in e]))

notation P `⊩` s : 10 := stack.vcgen P s