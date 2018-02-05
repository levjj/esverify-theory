import .syntax .etc .props

reserve infix `⊢`:10

inductive vcgen : prop → exp → propctx → Prop
notation p `⊢` e `:` q : 10 := vcgen p e q

| num {n: ℤ} {P: prop} :
    (P ⊢ value.num n : • ≣ value.num n)

| true {P: prop} :
    (P ⊢ value.true : • ≣ value.true)

| false {P: prop} :
    (P ⊢ value.false : • ≣ value.false)

| var {P: prop} {x: var} :
    (P ⊢ exp.var x : term.var r ≡ term.var x)

| unop {P Q: prop} {op: unop} {e: exp} {x r: var} :
    (P ⊢ x, e : Q) →
    ⟪ prop.implies (prop.and P Q) (prop.pre₁ op (term.var x)) ⟫ →
    (P ⊢ r, exp.unop op e : prop.exis x (prop.and Q (term.var r ≡ term.unop op (term.var x))))

| unop {P: prop} {Q: propctx} {op: unop} {e: exp} {x: var} :
    (P ⊢ e : Q) →
    ⟪ prop.univ x (prop.implies (prop.and P (Q x)) (prop.pre₁ op (term.var x))) ⟫ →
    (P ⊢ exp.unop op e : propctx.exis x (propctx.and (Q x) (• ≣ term.unop op (term.var x))))

notation p `⊢` r `,` e `:` q : 10 := vcgen p r e q