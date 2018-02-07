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

inductive term
| true  : term
| false : term
| num   : ℤ → term
| var   : var → term
| unop  : unop → term → term
| binop : binop → term → term → term
| app   : term → term → term

inductive spec
| term : term → spec
| not  : spec → spec
| and  : spec → spec → spec
| or   : spec → spec → spec
| func : term → var → spec → spec → spec

mutual inductive value, env, exp

with value: Type
| true  : value
| false : value
| num   : ℤ → value
| func  : var → var → spec → spec → exp → env → value

with env: Type
| empty : env
| cons  : var → value → env → env -- [x: v, env]

with exp: Type
| true   : var → exp → exp                           -- let x = true in e
| false  : var → exp → exp                           -- let x = false in e
| num    : var → ℤ → exp → exp                       -- let x = n in e
| func   : var → var → spec → spec → exp → exp → exp -- let f(x) R S = e in e
| unop   : var → unop → var → exp → exp              -- let y = op x in e
| binop  : var → binop → var → var → exp → exp       -- let z = x op y in e
| app    : var → var → var → exp → exp               -- let z = x(y) in e
| ite    : var → exp → exp → exp                     -- if x then e else e
| return : var → exp                                 -- return x

inductive stack
| top  : env → exp → stack -- (σ, e)
| cons : stack → env → var → var → var → exp → stack -- κ · (σ, let y = f(x) in e)

structure call := (f: var) (x: var) (y: var) -- f(x)=y

inductive prop
| term    : term → prop
| not     : prop → prop
| and     : prop → prop → prop
| or      : prop → prop → prop
| pre     : term → term → prop
| pre₁    : unop → term → prop
| pre₂    : binop → term → term → prop
| post    : term → term → prop
| call    : term → term → prop
| forallc : var → term → prop → prop
| exist   : var → prop → prop

inductive termctx
| hole  : termctx
| true  : termctx
| false : termctx
| num   : ℤ → termctx
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
| exist   : var → propctx → propctx
