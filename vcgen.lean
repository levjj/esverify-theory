import .props

reserve infix `⊢`:10

inductive vcgen : prop → var → exp → prop → Prop
notation p `⊢` r `,` e `:` q : 10 := vcgen p r e q

  | num {n: ℤ} {P: prop} {r: var} :
      (P ⊢ r, value.num n : term.var r ≡ value.num n)

  | true {P: prop} {r: var} :
      (P ⊢ r, value.true : term.var r ≡ value.true)

  | false {P: prop} {r: var} :
      (P ⊢ r, value.false : term.var r ≡ value.false)

  | var {P: prop} {x r: var} :
      (P ⊢ r, exp.var x : term.var r ≡ term.var x)

  | unop {P Q: prop} {op: unop} {e: exp} {x r: var} :
      (P ⊢ x, e : Q) →
      ⟪ prop.implies (prop.and P Q) (prop.pre₁ op (term.var x)) ⟫ →
      (P ⊢ r, exp.unop op e : prop.exis x (prop.and Q (term.var r ≡ term.unop op (term.var x))))

notation p `⊢` r `,` e `:` q : 10 := vcgen p r e q