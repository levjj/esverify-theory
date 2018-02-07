import .syntax .etc .props

reserve infix `⊢`:10

inductive exp.vcgen : prop → exp → propctx → Prop
notation P `⊢` e `:` Q : 10 := exp.vcgen P e Q

| tru {P: prop} {x: var} {e: exp} {Q: propctx}:
    x ∉ FV P →
    (P & x ≡ term.true ⊢ e : Q) →
    (P ⊢ lett x = true in e : propctx.exist x (x ≡ term.true & Q))

| fals {P: prop} {x: var} {e: exp} {Q: propctx}:
    x ∉ FV P →
    (P & x ≡ term.false ⊢ e : Q) →
    (P ⊢ letf x = false in e : propctx.exist x (x ≡ term.false & Q))

| num {P: prop} {x: var} {n: ℕ} {e: exp} {Q: propctx}:
    x ∉ FV P →
    (P & x ≡ term.num n ⊢ e : Q) →
    (P ⊢ letn x = n in e : propctx.exist x (x ≡ term.num n & Q))

| func {P: prop} {f x: var} {R S: spec} {e₁ e₂: exp} {Q₁ Q₂: propctx}:
    f ∉ FV P →
    x ∉ FV P →
    (P & spec.func f x R S & R ⊢ e₂ : Q₂) →
    ⟪ prop.implies (P & (spec.func f x R S) & R)
                   (Q₂ (term.app f x)) ⟫ →
    (P ⊢ letf f[x] req R ens S {e₁} in e₂ :
         propctx.exist f (spec.func f x R S & Q₁))

| unop {P: prop} {op: unop} {e: exp} {x y: var} {Q: propctx}:
    x ∈ FV P →
    y ∉ FV P →
    (P & y ≡ term.unop op x ⊢ e : Q) →
    ⟪ prop.implies P (prop.pre₁ op x) ⟫ →
    (P ⊢ letop y = op [x] in e : propctx.exist y (y ≡ term.unop op x & Q))

| binop {P: prop} {op: binop} {e: exp} {x y z: var} {Q: propctx}:
    x ∈ FV P →
    y ∈ FV P →
    z ∉ FV P →
    (P & z ≡ term.binop op x y ⊢ e : Q) →
    ⟪ prop.implies P (prop.pre₂ op x y) ⟫ →
    (P ⊢ letop2 y = op [x, y] in e : propctx.exist y (z ≡ term.binop op x y & Q))

| app {P: prop} {e: exp} {y f x: var} {Q: propctx}:
    f ∈ FV P →
    x ∈ FV P →
    y ∉ FV P →
    (P & prop.call f x & y ≡ term.app f x & prop.post f x ⊢ e : Q) →
    ⟪ prop.implies (P & prop.call f x) (term.unop unop.isFunc f & prop.pre f x) ⟫ →
    (P ⊢ letapp y = f [x] in e : propctx.exist y (prop.call f x & y ≡ term.app f x & prop.post f x & Q))

| ite {P: prop} {e₁ e₂: exp} {x: var} {Q₁ Q₂: propctx}:
    x ∈ FV P →
    (P & x ⊢ e₁ : Q₁) →
    (P & term.unop unop.not x ⊢ e₂ : Q₂) →
    ⟪ prop.implies P (term.unop unop.isBool x) ⟫ →
    (P ⊢ exp.ite x e₁ e₂ : (propctx.implies x Q₁ & propctx.implies (term.unop unop.not x) Q₂))

| return {P: prop} {op: unop} {e: exp} {x: var}:
    x ∈ FV P →
    (P ⊢ exp.return x : x ≣ •)

notation P `⊢` e `:` Q : 10 := exp.vcgen P e Q

inductive env.vcgen : env → prop → Prop
notation `⊢` σ `:` Q : 10 := env.vcgen σ Q

| empty:
    ⊢ env.empty : term.true

| tru {σ: env} {x: var} {Q: prop}:
    (⊢ σ : Q) →
    (⊢ (σ[x ↦ value.true]) : (Q & x ≡ term.true))

| fls {σ: env} {x: var} {Q: prop}:
    (⊢ σ : Q) →
    (⊢ (σ[x ↦ value.false]) : (Q & x ≡ term.false))

| num {σ: env} {x: var} {n: ℤ} {Q: prop}:
    (⊢ σ : Q) →
    (⊢ (σ[x ↦ value.num n]) : (Q & x ≡ term.num n))

| func {σ₁ σ₂: env} {f x: var} {R S: spec} {e: exp} {Q₁ Q₂: prop} {Q₃: propctx}:
    (⊢ σ₁ : Q₁) →
    (⊢ σ₂ : Q₂) →
    (Q₂ & spec.func f x R S & R ⊢ e : Q₃) →
    ⟪ prop.implies (Q₂ & (spec.func f x R S) & R)
                   (Q₃ (term.app f x)) ⟫ →
    (⊢ (σ₁[x ↦ value.func f x R S e σ₂]) : (Q₁ & spec.func f x R S))

notation `⊢` σ `:` Q : 10 := env.vcgen σ Q

inductive stack.vcgen : prop → stack → Prop
notation P `⊩` s : 10 := stack.vcgen P s

| top {P₁ P₂: prop} {σ: env} {e: exp} {Q: propctx}:
    (⊢ σ : P₂) →
    (P₁ & P₂ ⊢ e : Q) →
    (P₁ ⊩ (σ, e))

| cons {P₁ P₂: prop} {s: stack} {σ: env} {f x y: var} {e: exp} {Q: propctx}:
    (P₁ ⊩ s) →
    (⊢ σ : P₂) →
    (P₁ & P₂ ⊢ letapp y = f[x] in e : Q) →
    (P₁ ⊩ (s · [σ, let y = f[x] in e]))

notation P `⊩` s : 10 := stack.vcgen P s