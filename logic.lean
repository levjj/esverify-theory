import .syntax .etc .props

-- instantiation

constant prop.instantiated: prop → qfprop → Prop

-- substitution

inductive term.substituted (x: var) (v: value): term → term → Prop

| value {v': value} :
    term.substituted v' v'

| same_var:
    term.substituted x v

| diff_var {y: var}:
    (x ≠ y) →
    term.substituted y y

| unop {op: unop} {t t': term}:
    term.substituted t t' →
    term.substituted (term.unop op t) (term.unop op t')

| binop {op: binop} {t₁ t₂ t₁' t₂': term}:
    term.substituted t₁ t₁' →
    term.substituted t₂ t₂' →
    term.substituted (term.binop op t₁ t₂) (term.binop op t₁' t₂')

| app {t₁ t₂ t₁' t₂': term}:
    term.substituted t₁ t₁' →
    term.substituted t₂ t₂' →
    term.substituted (term.app t₁ t₂) (term.app t₁' t₂')

inductive spec.substituted (x: var) (v: value): spec → spec → Prop

| term {t t': term} :
    term.substituted x v t t' →
    spec.substituted (spec.term t) (spec.term t')

| not {R R': spec} :
    spec.substituted R R' →
    spec.substituted (spec.not R) (spec.not R')

| and {R S R' S': spec} :
    spec.substituted R R' →
    spec.substituted S S' →
    spec.substituted (spec.and R S) (spec.and R' S')

| or {R S R' S': spec} :
    spec.substituted R R' →
    spec.substituted S S' →
    spec.substituted (spec.or R S) (spec.or R' S')

| func_same {R S: spec} {t t': term} :
    term.substituted x v t t' →
    spec.substituted (spec.func t x R S) (spec.func t' x R S)

| func {y: var} {R S R' S': spec} {t t': term} :
    (x ≠ y) →
    term.substituted x v t t' →
    spec.substituted R R' →
    spec.substituted S S' →
    spec.substituted (spec.func t y R S) (spec.func t' y R' S')

inductive spec.substituted_env: env → spec → spec → Prop

| empty {R: spec}:
    spec.substituted_env env.empty R R

| cons {σ: env} {x: var} {v: value} {R R' R'': spec} :
    spec.substituted x v R R' →
    spec.substituted_env σ R' R'' →
    spec.substituted_env (σ[x↦v]) R R''

inductive qfprop.substituted (x: var) (v: value): qfprop → qfprop → Prop

| term {t t': term} :
    term.substituted x v t t' →
    qfprop.substituted (qfprop.term t) (qfprop.term t')

| not {P P': qfprop} :
    qfprop.substituted P P' →
    qfprop.substituted (qfprop.not P) (qfprop.not P')

| and {P Q P' Q': qfprop} :
    qfprop.substituted P P' →
    qfprop.substituted Q Q' →
    qfprop.substituted (qfprop.and P Q) (qfprop.and P' Q')

| or {P Q P' Q': qfprop} :
    qfprop.substituted P P' →
    qfprop.substituted Q Q' →
    qfprop.substituted (qfprop.or P Q) (qfprop.or P' Q')

| pre {t₁ t₂ t₁' t₂': term}:
    term.substituted x v t₁ t₁' →
    term.substituted x v t₂ t₂' →
    qfprop.substituted (qfprop.pre t₁ t₂) (qfprop.pre t₁' t₂')

| pre₁ {op: unop} {t t': term} :
    term.substituted x v t t' →
    qfprop.substituted (qfprop.pre₁ op t) (qfprop.pre₁ op t')

| pre₂ {op: binop} {t₁ t₂ t₁' t₂': term}:
    term.substituted x v t₁ t₁' →
    term.substituted x v t₂ t₂' →
    qfprop.substituted (qfprop.pre₂ op t₁ t₂) (qfprop.pre₂ op t₁' t₂')

| post {t₁ t₂ t₁' t₂': term}:
    term.substituted x v t₁ t₁' →
    term.substituted x v t₂ t₂' →
    qfprop.substituted (qfprop.post t₁ t₂) (qfprop.post t₁' t₂')

inductive qfprop.substituted_env: env → qfprop → qfprop → Prop

| empty {P: qfprop}:
    qfprop.substituted_env env.empty P P

| cons {σ: env} {x: var} {v: value} {P P' P'': qfprop} :
    qfprop.substituted x v P P' →
    qfprop.substituted_env σ P' P'' →
    qfprop.substituted_env (σ[x↦v]) P P''

-- validity

inductive valid : qfprop → Prop
notation `⊨` p: 100 := valid p

| tru: ⊨ value.true

| eq {t: term}: ⊨ term.binop binop.eq t t

| and {q p: qfprop}: ⊨ p → ⊨ q → ⊨ (p & q)

| orl {q p: qfprop}: ⊨ p → ⊨ (qfprop.or p q)

| orr {q p: qfprop}: ⊨ q → ⊨ (qfprop.or p q)

| mp {q p: qfprop}: ⊨ qfprop.implies p q → ⊨ p → ⊨ q

notation `⊨` p: 100 := valid p

@[reducible]
def VC(P: prop) := ∀ (σ: env) (P' P'': qfprop), (prop.instantiated P P') → (qfprop.substituted_env σ P' P'') → ⊨ P''

notation `⟪` P `⟫`: 100 := VC P