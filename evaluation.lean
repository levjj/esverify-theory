import .syntax

def δ: unop → value → option value
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

def δ₂: binop → value → value → option value
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
| _ _ _ := none

mutual inductive value.substituted, term.substituted, spec.substituted, exp.substituted

with value.substituted : var → value → value → value → Prop

| num {x: var} {v: value} {n: ℤ} :
    value.substituted x v (value.num n) (value.num n)

| true {x: var} {v: value} :
    value.substituted x v value.true value.true

| false {x: var} {v: value} :
    value.substituted x v value.false value.false

| func_f_same {v: value} {f x: var} {R S: spec} {e: exp} :
    value.substituted f v (value.func f x R S e) (value.func f x R S e)

| func_x_same {v: value} {f x: var} {R S: spec} {e: exp} :
    value.substituted x v (value.func f x R S e) (value.func f x R S e)

| func {f x y: var} {R R' S S': spec} {e e': exp} {v: value} :
    (x ≠ f) →
    (x ≠ y) →
    exp.substituted x v e e' →
    spec.substituted x v R R' →
    spec.substituted x v S S' →
    value.substituted x v (value.func f y R S e) (value.func f y R' S' e')

with term.substituted : var → value → term → term → Prop

| value {x: var} {v v₁ v₁': value} :
    value.substituted x v v₁ v₁' →
    term.substituted x v v₁ v₁'

| same_var {x: var} {v: value} :
    term.substituted x v (term.var x) v

| diff_var {x y: var} {v: value}:
    (x ≠ y) →
    term.substituted x v (term.var y) (term.var y)

| unop {x: var} {v: value} {op: unop} {t t': term}:
    term.substituted x v t t' →
    term.substituted x v (term.unop op t) (term.unop op t')

| binop {x: var} {v: value} {op: binop} {t₁ t₁' t₂ t₂': term}:
    term.substituted x v t₁ t₁' →
    term.substituted x v t₂ t₂' →
    term.substituted x v (term.binop op t₁ t₂) (term.binop op t₁' t₂')

| app {x: var} {v: value} {t₁ t₁' t₂ t₂': term}:
    term.substituted x v t₁ t₁' →
    term.substituted x v t₂ t₂' →
    term.substituted x v (term.app t₁ t₂) (term.app t₁' t₂')

with spec.substituted : var → value → spec → spec → Prop

| term {x: var} {v: value} {t t': term} :
    term.substituted x v t t' →
    spec.substituted x v (spec.term t) (spec.term t')

| not {x: var} {v: value} {R R': spec} :
    spec.substituted x v R R' →
    spec.substituted x v (spec.not R) (spec.not R')

| and {x: var} {v: value} {R R' S S': spec} :
    spec.substituted x v R R' →
    spec.substituted x v S S' →
    spec.substituted x v (spec.and R S) (spec.and R' S')

| or {x: var} {v: value} {R R' S S': spec} :
    spec.substituted x v R R' →
    spec.substituted x v S S' →
    spec.substituted x v (spec.or R S) (spec.or R' S')

| func_x_same {x: var} {v: value} {R S: spec} {t t': term} :
    term.substituted x v t t' →
    spec.substituted x v (spec.func t x R S) (spec.func t' x R S)

| func {x y: var} {v: value} {R R' S S': spec} {t t': term} :
    (x ≠ y) →
    term.substituted x v t t' →
    spec.substituted x v R R' →
    spec.substituted x v S S' →
    spec.substituted x v (spec.func t y R S) (spec.func t' y R' S')

with exp.substituted : var → value → exp → exp → Prop

| value {x: var} {v v₁ v₁': value} :
    value.substituted x v v₁ v₁' →
    exp.substituted x v v₁ v₁'

| same_var {x: var} {v: value} :
    exp.substituted x v (exp.var x) v

| diff_var {x y: var} {v: value} :
    (x ≠ y) →
    exp.substituted x v (exp.var y) (exp.var y)

| unop {x: var} {v: value} {op: unop} {e e': exp}:
    exp.substituted x v e e' →
    exp.substituted x v (exp.unop op e) (exp.unop op e')

| binop {x: var} {v: value} {op: binop} {e₁ e₁' e₂ e₂': exp}:
    exp.substituted x v e₁ e₁' →
    exp.substituted x v e₂ e₂' →
    exp.substituted x v (exp.binop op e₁ e₂) (exp.binop op e₁' e₂')

| app {x: var} {v: value} {e₁ e₁' e₂ e₂': exp}:
    exp.substituted x v e₁ e₁' →
    exp.substituted x v e₂ e₂' →
    exp.substituted x v (exp.app e₁ e₂) (exp.app e₁' e₂')

inductive step : exp → exp → Prop
notation e₁ `⟶` e₂:100 := step e₁ e₂

| unop_ctx {op: unop} {e e': exp} :
    (e ⟶ e') →
    (exp.unop op e ⟶ exp.unop op e')

| unop {op: unop} {v v': value} :
    (δ op v = some v') →
    (exp.unop op v ⟶ v')

| binop_left {op: binop} {e₁ e₁' e₂: exp}:
    (e₁ ⟶ e₁') →
    (exp.binop op e₁ e₂ ⟶ exp.binop op e₁' e₂)

| binop_right {op: binop} {v₁: value} {e₂ e₂': exp}:
    (e₂ ⟶ e₂') →
    (exp.binop op v₁ e₂ ⟶ exp.binop op v₁ e₂')

| binop {op: binop} {v₁ v₂ v': value} :
    (δ₂ op v₁ v₂ = some v') →
    (exp.binop op v₁ v₂ ⟶ v')

| app_left {e₁ e₁' e₂: exp}:
    (e₁ ⟶ e₁') →
    (exp.app e₁ e₂ ⟶ exp.app e₁' e₂)

| app_right {v₁: value} {e₂ e₂': exp}:
    (e₂ ⟶ e₂') →
    (exp.app  v₁ e₂ ⟶ exp.app v₁ e₂')

| app {f x: var} {R S: spec} {e e': exp} {v: value}:
    (exp.substituted x v e e') →
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
