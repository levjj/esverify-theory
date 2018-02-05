@[reducible]
def var := ℕ

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

inductive prop
| term : term → prop
| not  : prop → prop
| and  : prop → prop → prop
| or   : prop → prop → prop
| pre  : term → term → prop
| pre₁ : unop → term → prop
| pre₂ : binop → term → term → prop
| post : term → term → prop
| call : term → term → prop
| forallc : var → term → prop → prop
| univ    : var → prop → prop
| exis : var → prop → prop

inductive termctx
| hole  : termctx
| value : value → termctx
| var   : var → termctx
| unop  : unop → termctx → termctx
| binop : binop → termctx → termctx → termctx
| app   : termctx → termctx → termctx

inductive propctx
| term    : termctx → propctx
| not     : propctx → propctx
| and     : propctx → propctx → propctx
| or      : propctx → propctx → propctx
| pre     : termctx → termctx → propctx
| pre₁    : unop → termctx → propctx
| pre₂    : binop → termctx → termctx → propctx
| post    : termctx → termctx → propctx
| call    : termctx → termctx → propctx
| forallc : var → termctx → propctx → propctx
| univ    : var → propctx → propctx
| exis    : var → propctx → propctx
