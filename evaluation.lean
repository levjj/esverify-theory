import .syntax .etc

def unop.apply: unop → value → option value
| unop.not value.true                  := value.false
| unop.not value.false                 := value.true
| unop.isInt (value.num _)             := value.true
| unop.isInt _                         := value.false
| unop.isBool value.true               := value.true
| unop.isBool value.false              := value.true
| unop.isBool _                        := value.false
| unop.isFunc (value.func _ _ _ _ _ _) := value.true
| unop.isFunc _                        := value.false
| _ _                                  := none

instance : has_coe_to_fun unop := ⟨λ _, value → option value, unop.apply⟩

def binop.apply: binop → value → value → option value
| binop.plus (value.num n₁) (value.num n₂)  := value.num (n₁ + n₂)
| binop.minus (value.num n₁) (value.num n₂) := value.num (n₁ - n₂)
| binop.times (value.num n₁) (value.num n₂) := value.num (n₁ * n₂)
| binop.div (value.num n₁) (value.num n₂)   := value.num (n₁ / n₂)
| binop.and value.true value.true           := value.true
| binop.and value.true value.false          := value.false
| binop.and value.false value.true          := value.false
| binop.and value.false value.false         := value.false
| binop.or value.true value.true            := value.true
| binop.or value.true value.false           := value.true
| binop.or value.false value.true           := value.true
| binop.or value.false value.false          := value.false
| binop.eq (value.num n₁) (value.num n₂)    := if n₁ = n₂ then value.true else value.false
| binop.eq value.true value.true            := value.true
| binop.eq value.true value.false           := value.false
| binop.eq value.false value.true           := value.false
| binop.eq value.false value.false          := value.true
| binop.lt (value.num n₁) (value.num n₂)    := if n₁ < n₂ then value.true else value.false
| _ _ _                                     := none

instance : has_coe_to_fun binop := ⟨λ _, value → value → option value, binop.apply⟩

inductive step : stack → option call → stack → Prop
notation s₁ `⟶` c `,` s₂:100 := step s₁ c s₂

| ctx {s s': stack} {c: option call} {σ: env} {y f x: var} {e: exp}:
    (s ⟶ c, s') →
    (s · [σ, let y = f[x] in e] ⟶ c, (s' · [σ, let y = f[x] in e]))

| tru {σ: env} {x: var} {e: exp}:
    (σ, lett x = true in e) ⟶ none, (σ[x↦value.true], e)

| fals {σ: env} {x: var} {e: exp}:
    (σ, letf x = false in e) ⟶ none, (σ[x↦value.false], e)

| num {σ: env} {x: var} {e: exp} {n: ℤ}:
    (σ, letn x = n in e) ⟶ none, (σ[x↦value.num n], e)

| closure {σ: env} {R S: spec} {f x: var} {e₁ e₂: exp}:
    (σ, letf f[x] req R ens S {e₁} in e₂) ⟶ none,
    (σ[f↦value.func f x R S e₁ σ], e₂)

| unop {op: unop} {σ: env} {x y: var} {e: exp} {v₁ v: value}:
    (σ x = v₁) →
    (op v₁ = v) →
    ((σ, letop y = op [x] in e) ⟶ none, (σ[y↦v], e))

| binop {op: binop} {σ: env} {x y z: var} {e: exp} {v₁ v₂ v: value}:
    (σ x = v₁) →
    (σ y = v₂) →
    (op v₁ v₂ = v) →
    ((σ, letop2 z = op [x, y] in e) ⟶ none, (σ[z↦v], e))

| app {σ σ': env} {R S: spec} {f g x y z: var} {e e': exp} {v: value}:
    (σ f = value.func g z R S e σ') →
    (σ x = v) →
    ((σ, letapp y = f[x] in e') ⟶ none,
    ((σ[g↦value.func g z R S e σ'][z↦v], e) · [σ, let y = f[x] in e']))

| return {σ₁ σ₂ σ₃: env} {f x y z: var} {R S: spec} {e e': exp} {v vₓ: value}:
    (σ₁ z = v) →
    (σ₂ f = value.func f x R S e σ₃) →
    (σ₂ x = vₓ) →
    ((σ₁, exp.return z) · [σ₂, let y = f[x] in e'] ⟶ some ⟨f, x, R, S, e, σ₃, vₓ, v⟩, (σ₂[y↦v], e'))

| ite_true {σ: env} {e₁ e₂: exp} {x: var}:
    (σ x = value.true) →
    ((σ, exp.ite x e₁ e₂) ⟶ none, (σ, e₁))

| ite_false {σ: env} {e₁ e₂: exp} {x: var}:
    (σ x = value.false) →
    ((σ, exp.ite x e₁ e₂) ⟶ none, (σ, e₂))

notation s₁ `⟶` c `,` s₂:100 := step s₁ c s₂

inductive trans_step : stack → stack → Prop
notation s `⟶*` s':100 := trans_step s s'
| rfl {s: stack}                    : s ⟶* s
| trans {s s' s'': stack} {c: call} : (s ⟶ c, s') → (s' ⟶* s'') → (s ⟶* s'')

notation s `⟶*` s':100 := trans_step s s'
