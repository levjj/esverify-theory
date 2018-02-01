def var := name

inductive unop
| not    : unop
| isInt  : unop
| isBool : unop
| isFunc : unop

inductive binop
| plus  : binop
| minus : binop
| times : binop
| div   : binop
| and   : binop
| or    : binop
| eq    : binop
| lt    : binop

mutual inductive value, term, spec, exp

with value: Type
| num   : ℤ → value
| true  : value
| false : value
| func  : var → var → spec → spec → exp → value

with term: Type
| value : value → term
| var   : var → term
| unop  : unop → term → term
| binop : binop → term → term → term
| app   : term → term → term

with spec: Type
| term : term → spec
| not  : spec → spec
| and  : spec → spec → spec
| or   : spec → spec → spec
| func : term → var → spec → spec → spec

with exp: Type
| value : value → exp
| var   : var → exp
| unop  : unop → exp → exp
| binop : binop → exp → exp → exp
| app   : exp → exp → exp
| ite   : exp → exp → exp → exp

notation t₁ `≡` t₂ := term.binop binop.eq t₁ t₂

instance : has_coe value exp := ⟨exp.value⟩
instance : has_coe value term := ⟨term.value⟩
