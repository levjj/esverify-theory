-- x ∈ VariableNames
@[reducible]
def var := ℕ

-- ⊗ ∈ UnaryOperators
inductive unop
| not    : unop
| isInt  : unop
| isBool : unop
| isFunc : unop

-- ⊕ ∈ BinaryOperators
inductive binop
| plus  : binop
| minus : binop
| times : binop
| div   : binop
| and   : binop
| or    : binop
| eq    : binop
| lt    : binop

mutual inductive value, exp, term, spec, env

-- v ∈ Values := true | false | n | <func f(x) R S {e}, σ>
with value: Type
| true  : value
| false : value
| num   : ℤ → value
| func  : var → var → spec → spec → exp → env → value

-- e ∈ Expressions := ...
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

-- A ∈ LogicalTerms := v | x | ⊗A | A⊕A | A(A)
with term: Type
| value : value → term
| var   : var → term
| unop  : unop → term → term
| binop : binop → term → term → term
| app   : term → term → term

-- R,S ∈ Specs := A | ¬ R | R ∧ S | R ∨ S | spec A(x) req R ens S
with spec: Type
| term : term → spec
| not  : spec → spec
| and  : spec → spec → spec
| or   : spec → spec → spec
| func : term → var → spec → spec → spec

-- σ ∈ Environments := • | σ[x ↦ v]
with env: Type
| empty : env
| cons  : var → value → env → env

-- s ∈ Stacks := (σ, e) | s · (σ, let y = f(x) in e)
inductive stack
| top  : env → exp → stack
| cons : stack → env → var → var → var → exp → stack

-- h ∈ HistoryItem := call((func f(x) R S e σ), v)
inductive historyitem
| nop  : historyitem
| call : var → var → spec → spec → exp → env → value → historyitem

-- H ∈ CallHistories := ∅ | h • H
@[reducible]
def callhistory := list historyitem

-- P,Q ∈ Propositions := A | ¬ P | P ∧ Q | P ∨ Q | pre(A, A) | pre(⊗, A) | pre(⊕, A, A)
--                     | post(A, A) | call(A, A) | ∀x. {call(A, x)} ⇒ P | ∃x. P
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
| exis    : var → prop → prop

-- A[•] ∈ TermContexts := • | v | x | ⊗ A[•] | A[•] ⊕ A[•] | A[•] ( A[•] )
inductive termctx
| hole  : termctx
| value : value → termctx
| var   : var → termctx
| unop  : unop → termctx → termctx
| binop : binop → termctx → termctx → termctx
| app   : termctx → termctx → termctx

-- P[•], Q[•] ∈ PropositionsContexts := A[•] | ¬ P[•] | P[•] ∧ Q[•] | P[•] ∨ Q[•]
--             | pre(A[•], A[•]) | pre(⊗, A[•]) | pre(⊕, A[•], A[•]) | post(A[•], A[•])
--             | call(A[•], A[•]) | ∀x. {call(A[•], x)} ⇒ P[•] | ∃x. P[•]
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
| exis    : var → propctx → propctx

-- call(f, x) ∈ CallTriggers
structure calltrigger := (f: term) (x: term)

-- (∀x {call(f, x)} ⇒ P) ∈ CallQuantifiers
structure callquantifier := (f: term) (x: var) (P: prop)

-- P,Q ∈ VerificationCondition := ...
inductive vc: Type
| term    : term → vc
| not     : vc → vc
| and     : vc → vc → vc
| or      : vc → vc → vc
| pre     : term → term → vc
| pre₁    : unop → term → vc
| pre₂    : binop → term → term → vc
| post    : term → term → vc
| univ    : var → vc → vc