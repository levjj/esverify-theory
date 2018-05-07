-- first part of definitions

import .syntax .sizeof .eqdec

--  #######################################
--  ### MINOR DEFINITIONS AND NOTATIONS ###
--  #######################################

-- P → Q

@[reducible]
def spec.implies(P Q: spec): spec := spec.or (spec.not P) Q

@[reducible]
def prop.implies(P Q: prop): prop := prop.or (prop.not P) Q

@[reducible]
def propctx.implies(P Q: propctx): propctx := propctx.or (propctx.not P) Q

@[reducible]
def vc.implies(P Q: vc): vc := vc.or (vc.not P) Q

-- P ↔ Q

@[reducible]
def spec.iff(P Q: spec): spec := spec.and (spec.implies P Q) (spec.implies Q P)

@[reducible]
def prop.iff(P Q: prop): prop := prop.and (prop.implies P Q) (prop.implies Q P)

@[reducible]
def propctx.iff(P Q: propctx): propctx := propctx.and (propctx.implies P Q) (propctx.implies Q P)

@[reducible]
def vc.iff(P Q: vc): vc := vc.and (vc.implies P Q) (vc.implies Q P)

-- P ⋀ Q
class has_and (α : Type) := (and : α → α → α) 
instance : has_and spec := ⟨spec.and⟩
instance : has_and prop := ⟨prop.and⟩
instance : has_and propctx := ⟨propctx.and⟩
instance : has_and vc := ⟨vc.and⟩
infixr `⋀`:35 := has_and.and

-- P ⋁ Q

class has_or (α : Type) := (or : α → α → α) 
instance : has_or spec := ⟨spec.or⟩
instance : has_or prop := ⟨prop.or⟩
instance : has_or propctx := ⟨propctx.or⟩
instance : has_or vc := ⟨vc.or⟩
infixr `⋁`:30 := has_or.or

-- use • as hole
notation `•` := termctx.hole

-- simple coercions
instance value_to_term : has_coe value term := ⟨term.value⟩
instance var_to_term : has_coe var term := ⟨term.var⟩
instance term_to_prop : has_coe term prop := ⟨prop.term⟩
instance termctx_to_propctx : has_coe termctx propctx := ⟨propctx.term⟩
instance term_to_vc : has_coe term vc := ⟨vc.term⟩

-- use (t ≡ t)/(t ≣ t) to construct equality comparison
infix ≡ := term.binop binop.eq
infix `≣`:50 := termctx.binop binop.eq

-- syntax for let expressions
notation `lett` x `=`:1 `true` `in` e := exp.true x e
notation `letf` x `=`:1 `false` `in` e := exp.false x e
notation `letn` x `=`:1 n`in` e := exp.num x n e
notation `letf` f `[`:1 x `]` `req` R `ens` S `{`:1 e `}`:1 `in` e' := exp.func f x R S e e'
notation `letop` y `=`:1 op `[`:1 x `]`:1 `in` e := exp.unop y op x e
notation `letop2` z `=`:1 op `[`:1 x `,` y `]`:1 `in` e := exp.binop z op x y e
notation `letapp` y `=`:1 f `[`:1 x `]`:1 `in` e := exp.app y f x e

-- σ[x ↦ v]
notation e `[` x `↦` v `]` := env.cons e x v

-- (σ, e) : stack
instance : has_coe (spec × env × exp) stack := ⟨λe, stack.top e.1 e.2.1 e.2.2⟩

-- κ · [σ, let y = f [ x ] in e]
notation st `·` `[` R `,` env `,` `letapp` y `=`:1 f `[` x `]` `in` e `]` := stack.cons st R env y f x e

-- env lookup as function application

def env.apply: env → var → option value
| env.empty _ := none
| (σ[x↦v]) y :=
  have σ.sizeof < (σ[x↦v]).sizeof, from sizeof_env_rest,
  if x = y ∧ option.is_none (σ.apply y) then v else σ.apply y

using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ e, e.1.sizeof)⟩],
  dec_tac := tactic.assumption
}

instance : has_coe_to_fun env := ⟨λ _, var → option value, env.apply⟩

def env.rest: env → env
| env.empty := env.empty
| (σ[x↦v])  := σ

-- x ∈ σ

inductive env.contains: env → var → Prop
| same {e: env} {x: var} {v: value} : env.contains (e[x↦v]) x 
| rest {e: env} {x y: var} {v: value} : env.contains e x → env.contains (e[y↦v]) x

instance : has_mem var env := ⟨λx σ, σ.contains x⟩ 

-- dom(σ)

def env.dom (σ: env): set var := λx, x ∈ σ

-- spec to prop coercion

@[reducible]
def prop.func (f: term) (x: var) (P: prop) (Q: prop): prop := 
  term.unop unop.isFunc f ⋀
  prop.forallc x (prop.implies P (prop.pre f x) ⋀
                  prop.implies (prop.post f x) Q)

def spec.to_prop : spec → prop
| (spec.term t)       := prop.term t
| (spec.not S)        :=
    have S.sizeof < S.not.sizeof, from sizeof_spec_not,
    prop.not S.to_prop
| (spec.and R S)      :=
    have R.sizeof < (R ⋀ S).sizeof, from sizeof_spec_and₁,
    have S.sizeof < (R ⋀ S).sizeof, from sizeof_spec_and₂,
    R.to_prop ⋀ S.to_prop
| (spec.or R S)       :=
    have R.sizeof < (R ⋁ S).sizeof, from sizeof_spec_or₁,
    have S.sizeof < (R ⋁ S).sizeof, from sizeof_spec_or₂,
    R.to_prop ⋁ S.to_prop
| (spec.func f x R S) :=
    have R.sizeof < (spec.func f x R S).sizeof, from sizeof_spec_func_R,
    have S.sizeof < (spec.func f x R S).sizeof, from sizeof_spec_func_S,
    prop.func f x R.to_prop S.to_prop

using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ e, e.sizeof)⟩],
  dec_tac := tactic.assumption
}

instance spec_to_prop : has_coe spec prop := ⟨spec.to_prop⟩

-- term to termctx coercion

def term.to_termctx : term → termctx
| (term.value v)        := termctx.value v
| (term.var x)          := termctx.var x
| (term.unop op t)      := termctx.unop op t.to_termctx
| (term.binop op t₁ t₂) := termctx.binop op t₁.to_termctx t₂.to_termctx
| (term.app t₁ t₂)      := termctx.app t₁.to_termctx t₂.to_termctx

instance term_to_termctx : has_coe term termctx := ⟨term.to_termctx⟩

-- term to termctx coercion

def prop.to_propctx : prop → propctx
| (prop.term t)        := propctx.term t
| (prop.not P)         := propctx.not P.to_propctx
| (prop.and P₁ P₂)     := P₁.to_propctx ⋀ P₂.to_propctx
| (prop.or P₁ P₂)      := P₁.to_propctx ⋁ P₂.to_propctx
| (prop.pre t₁ t₂)     := propctx.pre t₁ t₂
| (prop.pre₁ op t)     := propctx.pre₁ op t
| (prop.pre₂ op t₁ t₂) := propctx.pre₂ op t₁ t₂
| (prop.post t₁ t₂)    := propctx.post t₁ t₂
| (prop.call t)        := propctx.call t
| (prop.forallc x P)   := propctx.forallc x P.to_propctx
| (prop.exis x P)      := propctx.exis x P.to_propctx

instance prop_to_propctx : has_coe prop propctx := ⟨prop.to_propctx⟩

-- termctx substituttion as function application

def termctx.apply: termctx → term → term
| •                        t := t
| (termctx.value v)        _ := term.value v
| (termctx.var x)          _ := term.var x
| (termctx.unop op t₁)     t := term.unop op (t₁.apply t)
| (termctx.binop op t₁ t₂) t := term.binop op (t₁.apply t) (t₂.apply t)
| (termctx.app t₁ t₂)      t := term.app (t₁.apply t) (t₂.apply t)

instance : has_coe_to_fun termctx := ⟨λ _, term → term, termctx.apply⟩

-- propctx substituttion as function application

def propctx.apply: propctx → term → prop
| (propctx.term t₁) t       := t₁ t
| (propctx.not P) t         := prop.not (P.apply t)
| (propctx.and P₁ P₂) t     := P₁.apply t ⋀ P₂.apply t
| (propctx.or P₁ P₂) t      := P₁.apply t ⋁ P₂.apply t
| (propctx.pre t₁ t₂) t     := prop.pre (t₁ t) (t₂ t)
| (propctx.pre₁ op t₁) t    := prop.pre₁ op (t₁ t)
| (propctx.pre₂ op t₁ t₂) t := prop.pre₂ op (t₁ t) (t₂ t)
| (propctx.post t₁ t₂) t    := prop.post (t₁ t) (t₂ t)
| (propctx.call t₁) t       := prop.call (t₁ t)
| (propctx.forallc x P) t   := prop.forallc x (P.apply t)
| (propctx.exis x P) t      := prop.exis x (P.apply t)

instance : has_coe_to_fun propctx := ⟨λ _, term → prop, propctx.apply⟩

-- stack precondition projection

def stack.pre: stack → spec
| (stack.top R _ _) := R
| (stack.cons _ R _ _ _ _ _) := R

--  #############################
--  ### VARIABLE SUBSTITUTION ###
--  #############################

-- free variables in terms, propositions and vcs

inductive free_in_term (x: var) : term → Prop
| var                              : free_in_term x
| unop {t: term} {op: unop}        : free_in_term t → free_in_term (term.unop op t)
| binop₁ {t₁ t₂: term} {op: binop} : free_in_term t₁ → free_in_term (term.binop op t₁ t₂)
| binop₂ {t₁ t₂: term} {op: binop} : free_in_term t₂ → free_in_term (term.binop op t₁ t₂)
| app₁ {t₁ t₂: term}               : free_in_term t₁ → free_in_term (term.app t₁ t₂)
| app₂ {t₁ t₂: term}               : free_in_term t₂ → free_in_term (term.app t₁ t₂)

inductive free_in_prop (x: var) : prop → Prop
| term {t: term}                   : free_in_term x t  → free_in_prop t
| not {p: prop}                    : free_in_prop p    → free_in_prop (prop.not p)
| and₁ {p₁ p₂: prop}               : free_in_prop p₁   → free_in_prop (prop.and p₁ p₂)
| and₂ {p₁ p₂: prop}               : free_in_prop p₂   → free_in_prop (prop.and p₁ p₂)
| or₁ {p₁ p₂: prop}                : free_in_prop p₁   → free_in_prop (prop.or p₁ p₂)
| or₂ {p₁ p₂: prop}                : free_in_prop p₂   → free_in_prop (prop.or p₁ p₂)
| pre₁ {t₁ t₂: term}               : free_in_term x t₁ → free_in_prop (prop.pre t₁ t₂)
| pre₂ {t₁ t₂: term}               : free_in_term x t₂ → free_in_prop (prop.pre t₁ t₂)
| preop {t: term} {op: unop}       : free_in_term x t  → free_in_prop (prop.pre₁ op t)
| preop₁ {t₁ t₂: term} {op: binop} : free_in_term x t₁ → free_in_prop (prop.pre₂ op t₁ t₂)
| preop₂ {t₁ t₂: term} {op: binop} : free_in_term x t₂ → free_in_prop (prop.pre₂ op t₁ t₂)
| post₁ {t₁ t₂: term}              : free_in_term x t₁ → free_in_prop (prop.post t₁ t₂)
| post₂ {t₁ t₂: term}              : free_in_term x t₂ → free_in_prop (prop.post t₁ t₂)
| call {t: term}                   : free_in_term x t → free_in_prop (prop.call t)
| forallc {y: var} {p: prop}       : (x ≠ y) → free_in_prop p → free_in_prop (prop.forallc y p)
| exis {y: var} {p: prop}          : (x ≠ y) → free_in_prop p → free_in_prop (prop.exis y p)

inductive free_in_vc (x: var) : vc → Prop
| term {t: term}                        : free_in_term x t  → free_in_vc t
| not {P: vc}                           : free_in_vc P      → free_in_vc (vc.not P)
| and₁ {P₁ P₂: vc}                      : free_in_vc P₁     → free_in_vc (vc.and P₁ P₂)
| and₂ {P₁ P₂: vc}                      : free_in_vc P₂     → free_in_vc (vc.and P₁ P₂)
| or₁ {P₁ P₂: vc}                       : free_in_vc P₁     → free_in_vc (vc.or P₁ P₂)
| or₂ {P₁ P₂: vc}                       : free_in_vc P₂     → free_in_vc (vc.or P₁ P₂)
| pre₁ {t₁ t₂: term}                    : free_in_term x t₁ → free_in_vc (vc.pre t₁ t₂)
| pre₂ {t₁ t₂: term}                    : free_in_term x t₂ → free_in_vc (vc.pre t₁ t₂)
| preop {t: term} {op: unop}            : free_in_term x t  → free_in_vc (vc.pre₁ op t)
| preop₁ {t₁ t₂: term} {op: binop}      : free_in_term x t₁ → free_in_vc (vc.pre₂ op t₁ t₂)
| preop₂ {t₁ t₂: term} {op: binop}      : free_in_term x t₂ → free_in_vc (vc.pre₂ op t₁ t₂)
| post₁ {t₁ t₂: term}                   : free_in_term x t₁ → free_in_vc (vc.post t₁ t₂)
| post₂ {t₁ t₂: term}                   : free_in_term x t₂ → free_in_vc (vc.post t₁ t₂)
| univ {y: var} {P: vc}                 : (x ≠ y) → free_in_vc P → free_in_vc (vc.univ y P)

-- notation x ∈ FV t/P

inductive freevars
| term: term → freevars
| prop: prop → freevars
| vc:   vc   → freevars

class has_fv (α: Type) := (fv : α → freevars)
instance : has_fv term := ⟨freevars.term⟩
instance : has_fv prop := ⟨freevars.prop⟩
instance : has_fv vc   := ⟨freevars.vc⟩

def freevars.to_set: freevars → set var
| (freevars.term t) := λx, free_in_term x t
| (freevars.prop P) := λx, free_in_prop x P
| (freevars.vc P)   := λx, free_in_vc x P

@[reducible]
def FV {α: Type} [h: has_fv α] (a: α): set var := (has_fv.fv a).to_set

@[reducible]
def closed {α: Type} [h: has_fv α] (a: α): Prop := ∀x, x ∉ FV a

-- fresh variables (not used in the provided term/prop)

def term.fresh_var : term → var
| (term.value v)        := 0
| (term.var x)          := x + 1
| (term.unop op t)      := t.fresh_var
| (term.binop op t₁ t₂) := max t₁.fresh_var t₂.fresh_var
| (term.app t₁ t₂)      := max t₁.fresh_var t₂.fresh_var

def prop.fresh_var : prop → var
| (prop.term t)        := t.fresh_var
| (prop.not P)         := P.fresh_var
| (prop.and P₁ P₂)     := max P₁.fresh_var P₂.fresh_var
| (prop.or P₁ P₂)      := max P₁.fresh_var P₂.fresh_var
| (prop.pre t₁ t₂)     := max t₁.fresh_var t₂.fresh_var
| (prop.pre₁ op t)     := t.fresh_var
| (prop.pre₂ op t₁ t₂) := max t₁.fresh_var t₂.fresh_var
| (prop.post t₁ t₂)    := max t₁.fresh_var t₂.fresh_var
| (prop.call t)        := t.fresh_var
| (prop.forallc x P)   := max (x + 1) P.fresh_var
| (prop.exis x P)      := max (x + 1) P.fresh_var

-- substituation in terms, propositions and vcs

def term.subst (x: var) (v: value): term → term
| (term.value v')       := v'
| (term.var y)          := if x = y then v else y
| (term.unop op t)      := term.unop op t.subst
| (term.binop op t₁ t₂) := term.binop op t₁.subst t₂.subst
| (term.app t₁ t₂)      := term.app t₁.subst t₂.subst

def term.subst_env: env → term → term
| env.empty t := t
| (σ[x↦v]) t :=
    have σ.sizeof < (σ[x ↦ v]).sizeof, from sizeof_env_rest,
    term.subst x v (term.subst_env σ t)

using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ e, e.1.sizeof)⟩],
  dec_tac := tactic.assumption
}

def prop.subst (x: var) (v: value): prop → prop
| (prop.term t)        := term.subst x v t
| (prop.not P)         := P.subst.not
| (prop.and P Q)       := P.subst ⋀ Q.subst
| (prop.or P Q)        := P.subst ⋁ Q.subst
| (prop.pre t₁ t₂)     := prop.pre (term.subst x v t₁) (term.subst x v t₂)
| (prop.pre₁ op t)     := prop.pre₁ op (term.subst x v t)
| (prop.pre₂ op t₁ t₂) := prop.pre₂ op (term.subst x v t₁) (term.subst x v t₂)
| (prop.call t)        := prop.call (term.subst x v t)
| (prop.post t₁ t₂)    := prop.post (term.subst x v t₁) (term.subst x v t₂)
| (prop.forallc y P)   := prop.forallc y (if x = y then P else P.subst)
| (prop.exis y P)      := prop.exis y (if x = y then P else P.subst)

def prop.subst_env: env → prop → prop
| env.empty P := P
| (σ[x↦v]) P :=
    have σ.sizeof < (σ[x ↦ v]).sizeof, from sizeof_env_rest,
    prop.subst x v (prop.subst_env σ P)

using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ e, e.1.sizeof)⟩],
  dec_tac := tactic.assumption
}

def vc.subst (x: var) (v: value): vc → vc
| (vc.term t)        := term.subst x v t
| (vc.not P)         := vc.not P.subst
| (vc.and P Q)       := P.subst ⋀ Q.subst
| (vc.or P Q)        := P.subst ⋁ Q.subst
| (vc.pre t₁ t₂)     := vc.pre (term.subst x v t₁) (term.subst x v t₂)
| (vc.pre₁ op t)     := vc.pre₁ op (term.subst x v t)
| (vc.pre₂ op t₁ t₂) := vc.pre₂ op (term.subst x v t₁) (term.subst x v t₂)
| (vc.post t₁ t₂)    := vc.post (term.subst x v t₁) (term.subst x v t₂)
| (vc.univ y P)      := vc.univ y (if x = y then P else P.subst)

def vc.subst_env: env → vc → vc
| env.empty P := P
| (σ[x↦v]) P :=
    have σ.sizeof < (σ[x ↦ v]).sizeof, from sizeof_env_rest,
    vc.subst x v (vc.subst_env σ P)

using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ e, e.1.sizeof)⟩],
  dec_tac := tactic.assumption
}

-- σ ∖ { x }

def env.without: env → var → env
| env.empty y := env.empty
| (σ[x↦v]) y := have σ.sizeof < (σ[x ↦ v]).sizeof, from sizeof_env_rest,
                if x = y then env.without σ y else ((env.without σ y)[x↦v])

using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ e, e.1.sizeof)⟩],
  dec_tac := tactic.assumption
}

-- closed under substitution

@[reducible]
def closed_subst {α: Type} [h: has_fv α] (σ: env) (a: α): Prop := FV a ⊆ σ.dom

-- renaming

def term.rename (x y: var): term → term
| (term.value v')       := v'
| (term.var z)          := if x = z then y else z
| (term.unop op t)      := term.unop op t.rename
| (term.binop op t₁ t₂) := term.binop op t₁.rename t₂.rename
| (term.app t₁ t₂)      := term.app t₁.rename t₂.rename

def prop.rename (x y: var): prop → prop
| (prop.term t)        := term.rename x y t
| (prop.not P)         := P.rename.not
| (prop.and P Q)       := P.rename ⋀ Q.rename
| (prop.or P Q)        := P.rename ⋁ Q.rename
| (prop.pre t₁ t₂)     := prop.pre (term.rename x y t₁) (term.rename x y t₂)
| (prop.pre₁ op t)     := prop.pre₁ op (term.rename x y t)
| (prop.pre₂ op t₁ t₂) := prop.pre₂ op (term.rename x y t₁) (term.rename x y t₂)
| (prop.call t)        := prop.call (term.rename x y t)
| (prop.post t₁ t₂)    := prop.post (term.rename x y t₁) (term.rename x y t₂)
| (prop.forallc z P)   := prop.forallc z (if x = z then P else P.rename)
| (prop.exis z P)      := prop.exis z (if x = z then P else P.rename)

-- subst term

def term.substt (x: var) (t: term): term → term
| (term.value v')       := v'
| (term.var y)          := if x = y then t else y
| (term.unop op t)      := term.unop op t.substt
| (term.binop op t₁ t₂) := term.binop op t₁.substt t₂.substt
| (term.app t₁ t₂)      := term.app t₁.substt t₂.substt

def prop.substt (x: var) (t: term): prop → prop
| (prop.term t₁)       := term.substt x t t₁
| (prop.not P)         := P.substt.not
| (prop.and P Q)       := P.substt ⋀ Q.substt
| (prop.or P Q)        := P.substt ⋁ Q.substt
| (prop.pre t₁ t₂)     := prop.pre (term.substt x t t₁) (term.substt x t t₂)
| (prop.pre₁ op t₁)    := prop.pre₁ op (term.substt x t t₁)
| (prop.pre₂ op t₁ t₂) := prop.pre₂ op (term.substt x t t₁) (term.substt x t t₂)
| (prop.call t₁)       := prop.call (term.substt x t t₁)
| (prop.post t₁ t₂)    := prop.post (term.substt x t t₁) (term.substt x t t₂)
| (prop.forallc y P)   := prop.forallc y (if x = y then P else P.substt)
| (prop.exis y P)      := prop.exis y (if x = y then P else P.substt)

--  ################################
--  ### QUANTIFIER INSTANTIATION ###
--  ################################

-- simple conversion of propositions to verification conditions
-- (no quantifier instantiation)

def prop.to_vc: prop → vc
| (prop.term t)        := vc.term t
| (prop.not P)         := vc.not P.to_vc
| (prop.and P₁ P₂)     := P₁.to_vc ⋀ P₂.to_vc
| (prop.or P₁ P₂)      := P₁.to_vc ⋁ P₂.to_vc
| (prop.pre t₁ t₂)     := vc.pre t₁ t₂
| (prop.pre₁ op t)     := vc.pre₁ op t
| (prop.pre₂ op t₁ t₂) := vc.pre₂ op t₁ t₂
| (prop.post t₁ t₂)    := vc.post t₁ t₂
| (prop.call _)        := vc.term value.true
| (prop.forallc x P)   := vc.univ x P.to_vc
| (prop.exis x P)      := have P.sizeof < (prop.exis x P).sizeof, from sizeof_prop_exis,
                          vc.not (vc.univ x (vc.not P.to_vc))

-- lift_p(P) / lift_n(P) lifts quantifiers in either positive or negative position
-- to become a top-level quantifier by using a fresh (unbound) variable

mutual def prop.lift_p, prop.lift_n

with prop.lift_p: prop → var → option prop
| (prop.term t) y        := none
| (prop.not P) y         := have P.sizeof < P.not.sizeof, from sizeof_prop_not,
                            prop.not <$> P.lift_n y
| (prop.and P₁ P₂) y     := have P₁.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₁,
                            have P₂.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₂,
                            match P₁.lift_p y with
                            | some P₁' := some (P₁' ⋀ P₂)
                            | none := (λP₂', P₁ ⋀ P₂') <$> P₂.lift_p y
                            end
| (prop.or P₁ P₂) y      := have P₁.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₁,
                            have P₂.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₂,
                            match P₁.lift_p y with
                            | some P₁' := some (P₁' ⋁ P₂)
                            | none := (λP₂', P₁ ⋁ P₂') <$> P₂.lift_p y
                            end
| (prop.pre t₁ t₂) y     := none
| (prop.pre₁ op t) y     := none
| (prop.pre₂ op t₁ t₂) y := none
| (prop.post t₁ t₂) y    := none
| (prop.call t) y        := none
| (prop.forallc x P) y   := some (prop.implies (prop.call y) (P.rename x y)) 
| (prop.exis x P) y      := none

with prop.lift_n: prop → var → option prop
| (prop.term t) y        := none
| (prop.not P) y         := have P.sizeof < P.not.sizeof, from sizeof_prop_not,
                            prop.not <$> P.lift_p y
| (prop.and P₁ P₂) y     := have P₁.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₁,
                            have P₂.sizeof < (P₁ ⋀ P₂).sizeof, from sizeof_prop_and₂,
                            match P₁.lift_n y with
                            | some P₁' := some (P₁' ⋀ P₂)
                            | none := (λP₂', P₁ ⋀ P₂') <$> P₂.lift_n y
                            end
| (prop.or P₁ P₂) y      := have P₁.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₁,
                            have P₂.sizeof < (P₁ ⋁ P₂).sizeof, from sizeof_prop_or₂,
                            match P₁.lift_n y with
                            | some P₁' := some (P₁' ⋁ P₂)
                            | none := (λP₂', P₁ ⋁ P₂') <$> P₂.lift_n y
                            end
| (prop.pre t₁ t₂) y     := none
| (prop.pre₁ op t) y     := none
| (prop.pre₂ op t₁ t₂) y := none
| (prop.post t₁ t₂) y    := none
| (prop.call t) y        := none
| (prop.forallc x P) y   := none
| (prop.exis x P) y      := some (P.rename x y)

using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf $ λ s,
  match s with
  | psum.inl a := a.1.sizeof
  | psum.inr a := a.1.sizeof
  end⟩],
  dec_tac := tactic.assumption
}

-- remaining definitions need some additional lemmas in qiaux.lean to prove termination
-- definitions continue in definitions2.lean
