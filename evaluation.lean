import .syntax .notations

def unop.apply: unop → value → option value
| unop.not value.true                    := value.false
| unop.not value.false                   := value.true
| unop.isInt (value.num _)               := value.true
| unop.isInt _                           := value.false
| unop.isBool value.true                 := value.true
| unop.isBool value.false                := value.true
| unop.isBool _                          := value.false
| unop.isFunc (value.func _ _ _ _ _ _ _) := value.true
| unop.isFunc _                          := value.false
| _ _                                    := none

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
| binop.eq v₁ v₂                            := if v₁ = v₂ then value.true else value.false
| binop.lt (value.num n₁) (value.num n₂)    := if n₁ < n₂ then value.true else value.false
| _ _ _                                     := none


inductive step : stack → stack → Prop
notation s₁ `⟶` s₂:100 := step s₁ s₂

| ctx {s s': stack} {R: spec} {H: history} {σ: env} {y f x: var} {e: exp}:
    (s ⟶ s') →
    (s · [R, H, σ, letapp y = f[x] in e] ⟶ (s' · [R, H, σ, letapp y = f[x] in e]))

| tru {R: spec} {H: history} {σ: env} {x: var} {e: exp}:
    (R, H, σ, lett x = true in e) ⟶ (R, H, σ[x↦value.true], e)

| fals {R: spec} {H: history} {σ: env} {x: var} {e: exp}:
    (R, H, σ, letf x = false in e) ⟶ (R, H, σ[x↦value.false], e)

| num {R: spec} {H: history} {σ: env} {x: var} {e: exp} {n: ℤ}:
    (R, H, σ, letn x = n in e) ⟶ (R, H, σ[x↦value.num n], e)

| closure {H: history} {σ: env} {R' R S: spec} {f x: var} {e₁ e₂: exp}:
    (R', H, σ, letf f[x] req R ens S {e₁} in e₂) ⟶ 
    (R', H, σ[f↦value.func f x R S e₁ H σ], e₂)

| unop {R: spec} {H: history} {op: unop} {σ: env} {x y: var} {e: exp} {v₁ v: value}:
    (σ x = v₁) →
    (unop.apply op v₁ = v) →
    ((R, H, σ, letop y = op [x] in e) ⟶ (R, H, σ[y↦v], e))

| binop {R: spec} {H: history} {op: binop} {σ: env} {x y z: var} {e: exp} {v₁ v₂ v: value}:
    (σ x = v₁) →
    (σ y = v₂) →
    (binop.apply op v₁ v₂ = v) →
    ((R, H, σ, letop2 z = op [x, y] in e) ⟶ (R, H, σ[z↦v], e))

| app {H H': history} {σ σ': env} {R' R S: spec} {f g x y z: var} {e e': exp} {v: value}:
    (σ f = value.func g z R S e H' σ') →
    (σ x = v) →
    ((R', H, σ, letapp y = f[x] in e') ⟶
    ((R, H', σ'[g↦value.func g z R S e H' σ'][z↦v], e) · [R', H, σ, letapp y = f[x] in e']))

| return {H₁ H₂ H₃: history} {σ₁ σ₂ σ₃: env} {f g gx x y z: var} {R₁ R₂ R S: spec} {e e': exp} {v vₓ: value}:
    (σ₁ z = v) →
    (σ₂ f = value.func g gx R S e H₃ σ₃) →
    (σ₂ x = vₓ) →
    ((R₁, H₁, σ₁, exp.return z) · [R₂, H₂, σ₂, letapp y = f[x] in e'] ⟶
    (R₂, H₂ · call g gx R S e H₃ σ₃ vₓ, σ₂[y↦v], e'))

| ite_true {R: spec} {H: history} {σ: env} {e₁ e₂: exp} {x: var}:
    (σ x = value.true) →
    ((R, H, σ, exp.ite x e₁ e₂) ⟶ (R, H, σ, e₁))

| ite_false {R: spec} {H: history} {σ: env} {e₁ e₂: exp} {x: var}:
    (σ x = value.false) →
    ((R, H, σ, exp.ite x e₁ e₂) ⟶ (R, H, σ, e₂))

notation s₁ `⟶` s₂:100 := step s₁ s₂

inductive trans_step : stack → stack → Prop
notation s `⟶*` s':100 := trans_step s s'
| rfl {s: stack}          : s ⟶* s
| trans {s s' s'': stack} : (s ⟶* s') → (s' ⟶ s'') → (s ⟶* s'')

notation s `⟶*` s':100 := trans_step s s'

-- lemmas

lemma binop.eq_of_equal_values {v: value}: binop.apply binop.eq v v = value.true :=
  have binop.apply binop.eq v v = (if v = v then value.true else value.false), by unfold binop.apply,
  show binop.apply binop.eq v v = value.true, by simp[this]

lemma unop.isFunc.inv {v: value}: unop.apply unop.isFunc v = value.true → 
      ∃ (f x: var) (R S: spec) (e: exp) (H: history) (σ: env), v = value.func f x R S e H σ :=
  assume isFunc_is_true: unop.apply unop.isFunc v = value.true,
  begin
    cases v with n f x R S e H σ,

    show ∃ (f x: var) (R S: spec) (e: exp) (H: history) (σ: env), value.true = value.func f x R S e H σ, from (
      have h1: (unop.apply unop.isFunc value.true = value.true), from isFunc_is_true,
      have h2: (unop.apply unop.isFunc value.true = value.false), by unfold unop.apply,
      have some value.true = some value.false, from eq.trans h1.symm h2,
      have value.true = value.false, from option.some.inj this,
      false.elim (value._mut_.no_confusion this)
    ),

    show ∃ (f x: var) (R S: spec) (e: exp) (H: history) (σ: env), value.false = value.func f x R S e H σ, from (
      have h1: (unop.apply unop.isFunc value.false = value.true), from isFunc_is_true,
      have h2: (unop.apply unop.isFunc value.false = value.false), by unfold unop.apply,
      have some value.true = some value.false, from eq.trans h1.symm h2,
      have value.true = value.false, from option.some.inj this,
      false.elim (value._mut_.no_confusion this)
    ),

    show ∃ (f x: var) (R S: spec) (e: exp) (H: history) (σ: env), value.num n = value.func f x R S e H σ, from (
      have h1: (unop.apply unop.isFunc (value.num n) = value.true), from isFunc_is_true,
      have h2: (unop.apply unop.isFunc (value.num n) = value.false), by unfold unop.apply,
      have some value.true = some value.false, from eq.trans h1.symm h2,
      have value.true = value.false, from option.some.inj this,
      false.elim (value._mut_.no_confusion this)
    ),

    show ∃ (f_1 x_1: var) (R_1 S_1: spec) (e_1: exp) (H_1: history) (σ_1: env),
        value.func f x R S e H σ = value.func f_1 x_1 R_1 S_1 e_1 H_1 σ_1, from (
      exists.intro f (exists.intro x (exists.intro R (exists.intro S
                     (exists.intro e (exists.intro H (exists.intro σ rfl))))))
    )
  end

lemma unop.isBool.inv {v: value}: unop.apply unop.isBool v = value.true → (v = value.true) ∨ (v = value.false) :=
  assume isBool_is_true: unop.apply unop.isBool v = value.true,
  begin
    cases v with n f x R S e H σ,

    show ((value.true = value.true) ∨ (value.true = value.false)), from (
      or.inl rfl
    ),

    show ((value.false = value.true) ∨ (value.false = value.false)), from (
      or.inr rfl
    ),

    show (value.num n = value.true ∨ (value.num n = value.false)), from (
      have h1: unop.apply unop.isBool (value.num n) = ↑value.true, from isBool_is_true,
      have h2: (unop.apply unop.isBool (value.num n) = value.false), by unfold unop.apply,
      have some value.true = some value.false, from eq.trans h1.symm h2,
      have value.true = value.false, from option.some.inj this,
      false.elim (value._mut_.no_confusion this)
    ),

    show (value.func f x R S e H σ = value.true ∨ (value.func f x R S e H σ = value.false)), from (
      have h1: unop.apply unop.isBool (value.func f x R S e H σ) = ↑value.true, from isBool_is_true,
      have h2: (unop.apply unop.isBool (value.func f x R S e H σ) = value.false), by unfold unop.apply,
      have some value.true = some value.false, from eq.trans h1.symm h2,
      have value.true = value.false, from option.some.inj this,
      false.elim (value._mut_.no_confusion this)
    )
  end

lemma binop.eq.inv {v₁ v₂: value}: binop.apply binop.eq v₁ v₂ = value.true → (v₁ = v₂) :=
  assume eq_is_true: binop.apply binop.eq v₁ v₂ = value.true,
  begin
    by_cases (v₁ = v₂),
    from h,
    unfold binop.apply at eq_is_true,
    simp[h] at eq_is_true,
    have h2, from option.some.inj eq_is_true,
    contradiction
  end
