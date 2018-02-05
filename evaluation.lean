import .syntax .etc

def unop.apply: unop → value → option value
| unop.not value.true                := value.false
| unop.not value.false               := value.true
| unop.isInt (value.num _)           := value.true
| unop.isInt _                       := value.false
| unop.isBool value.true             := value.true
| unop.isBool value.false            := value.true
| unop.isBool _                      := value.false
| unop.isFunc (value.func _ _ _ _ _) := value.true
| unop.isFunc _                      := value.false
| _ _                                := none

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

mutual inductive value.substituted, term.substituted, spec.substituted, exp.substituted

with value.substituted : value → var → value → value → Prop

| num {x: var} {v: value} {n: ℤ} :
    value.substituted (value.num n) x v (value.num n)

| true {x: var} {v: value} :
    value.substituted value.true x v value.true

| false {x: var} {v: value} :
    value.substituted value.false x v value.false

| func_f_same {v: value} {f x: var} {R S: spec} {e: exp} :
    value.substituted (value.func f x R S e) f v (value.func f x R S e)

| func_x_same {v: value} {f x: var} {R S: spec} {e: exp} :
    value.substituted (value.func f x R S e) x v (value.func f x R S e)

| func {f x y: var} {R R' S S': spec} {e e': exp} {v: value} :
    (x ≠ f) →
    (x ≠ y) →
    exp.substituted e x v e' →
    spec.substituted R x v R' →
    spec.substituted S x v S' →
    value.substituted (value.func f y R S e) x v (value.func f y R' S' e')

with term.substituted : term → var → value → term → Prop

| value {x: var} {v v₁ v₁': value} :
    value.substituted v₁ x v v₁' →
    term.substituted v₁ x v v₁'

| same_var {x: var} {v: value} :
    term.substituted (term.var x) x v v

| diff_var {x y: var} {v: value}:
    (x ≠ y) →
    term.substituted (term.var y) x v (term.var y)

| unop {x: var} {v: value} {op: unop} {t t': term}:
    term.substituted t x v t' →
    term.substituted (term.unop op t) x v (term.unop op t')

| binop {x: var} {v: value} {op: binop} {t₁ t₁' t₂ t₂': term}:
    term.substituted t₁ x v t₁' →
    term.substituted t₂ x v t₂' →
    term.substituted (term.binop op t₁ t₂) x v (term.binop op t₁' t₂')

| app {x: var} {v: value} {t₁ t₁' t₂ t₂': term}:
    term.substituted t₁ x v t₁' →
    term.substituted t₂ x v t₂' →
    term.substituted (term.app t₁ t₂) x v (term.app t₁' t₂')

with spec.substituted : spec → var → value → spec → Prop

| term {x: var} {v: value} {t t': term} :
    term.substituted t x v t' →
    spec.substituted (spec.term t) x v (spec.term t')

| not {x: var} {v: value} {R R': spec} :
    spec.substituted R x v R' →
    spec.substituted (spec.not R) x v (spec.not R')

| and {x: var} {v: value} {R R' S S': spec} :
    spec.substituted R x v R' →
    spec.substituted S x v S' →
    spec.substituted (spec.and R S) x v (spec.and R' S')

| or {x: var} {v: value} {R R' S S': spec} :
    spec.substituted R x v R' →
    spec.substituted S x v S' →
    spec.substituted (spec.or R S) x v (spec.or R' S')

| func_x_same {x: var} {v: value} {R S: spec} {t t': term} :
    term.substituted t x v t' →
    spec.substituted (spec.func t x R S) x v (spec.func t' x R S)

| func {x y: var} {v: value} {R R' S S': spec} {t t': term} :
    (x ≠ y) →
    term.substituted t x v t' →
    spec.substituted R x v R' →
    spec.substituted S x v S' →
    spec.substituted (spec.func t y R S) x v (spec.func t' y R' S')

with exp.substituted : exp → var → value → exp → Prop

| value {x: var} {v v₁ v₁': value} :
    value.substituted v₁ x v v₁' →
    exp.substituted v₁ x v v₁'

| same_var {x: var} {v: value} :
    exp.substituted (exp.var x) x v v

| diff_var {x y: var} {v: value} :
    (x ≠ y) →
    exp.substituted (exp.var y) x v (exp.var y)

| unop {x: var} {v: value} {op: unop} {e e': exp}:
    exp.substituted e x v e' →
    exp.substituted (exp.unop op e) x v (exp.unop op e')

| binop {x: var} {v: value} {op: binop} {e₁ e₁' e₂ e₂': exp}:
    exp.substituted e₁ x v e₁' →
    exp.substituted e₂ x v e₂' →
    exp.substituted (exp.binop op e₁ e₂) x v (exp.binop op e₁' e₂')

| app {x: var} {v: value} {e₁ e₁' e₂ e₂': exp}:
    exp.substituted e₁ x v e₁' →
    exp.substituted e₂ x v e₂' →
    exp.substituted (exp.app e₁ e₂) x v (exp.app e₁' e₂')

inductive step : exp → exp → Prop
notation e₁ `⟶` e₂:100 := step e₁ e₂

| unop_ctx {op: unop} {e e': exp} :
    (e ⟶ e') →
    (exp.unop op e ⟶ exp.unop op e')

| unop {op: unop} {v v': value} :
    (op v = some v') →
    (exp.unop op v ⟶ v')

| binop_left {op: binop} {e₁ e₁' e₂: exp}:
    (e₁ ⟶ e₁') →
    (exp.binop op e₁ e₂ ⟶ exp.binop op e₁' e₂)

| binop_right {op: binop} {v₁: value} {e₂ e₂': exp}:
    (e₂ ⟶ e₂') →
    (exp.binop op v₁ e₂ ⟶ exp.binop op v₁ e₂')

| binop {op: binop} {v₁ v₂ v': value} :
    (op v₁ v₂ = some v') →
    (exp.binop op v₁ v₂ ⟶ v')

| app_left {e₁ e₁' e₂: exp}:
    (e₁ ⟶ e₁') →
    (exp.app e₁ e₂ ⟶ exp.app e₁' e₂)

| app_right {v₁: value} {e₂ e₂': exp}:
    (e₂ ⟶ e₂') →
    (exp.app  v₁ e₂ ⟶ exp.app v₁ e₂')

| app {f x: var} {R S: spec} {e e': exp} {v: value}:
    (e.substituted x v e') →
    (exp.app (value.func f x R S e) v ⟶ e')

| ite {e1 e1' e2 e3: exp}:
    (e1 ⟶ e1') →
    (exp.ite e1 e2 e3 ⟶ exp.ite e1' e2 e3)

| ite_true {e2 e3: exp}:
    exp.ite value.true e2 e3 ⟶ e2

| ite_false {e2 e3: exp}:
    exp.ite value.false e2 e3 ⟶ e3

notation e1 `⟶` e2:100 := step e1 e2

inductive trans_step : exp → exp → Prop
notation e `⟶*` e':100 := trans_step e e'
| rfl {e: exp}:          e ⟶* e
| trans {e e' e'': exp}: (e ⟶ e') → (e' ⟶* e'') → (e ⟶* e'')

notation e `⟶*` e':100 := trans_step e e'
