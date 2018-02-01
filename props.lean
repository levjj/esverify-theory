import .syntax

inductive prop
| term : term → prop
| not  : prop → prop
| and  : prop → prop → prop
| or   : prop → prop → prop
| pre  : term → term → prop
| pre₁ : unop → term → prop
| pre₂ : binop → term → prop
| post : term → term → prop
| call : term → term → prop
| univ : var → term → prop → prop
| exis : var → prop → prop

def prop.implies(p q: prop): prop :=
  prop.or (prop.not p) q

inductive valid : prop → Prop
notation `⟪` p `⟫`: 100 := valid p
| to_prop {p: prop}: valid p

notation `⟪` p `⟫`: 100 := valid p

instance term_to_prop_coe: has_coe term prop := ⟨prop.term⟩

inductive termctx
| hole  : termctx
| value : value → termctx
| var   : var → termctx
| unop  : unop → termctx → termctx
| binop : binop → termctx → termctx → termctx
| app   : termctx → termctx → termctx

inductive propctx
| term : termctx → propctx
| not  : propctx → propctx
| and  : propctx → propctx → propctx
| or   : propctx → propctx → propctx
| pre  : termctx → termctx → propctx
| pre₁ : unop → termctx → propctx
| pre₂ : binop → termctx → propctx
| post : termctx → termctx → propctx
| call : termctx → termctx → propctx
| univ : var → termctx → propctx → propctx
| exis : var → propctx → propctx

def termctx.apply: termctx → var → term
| termctx.hole                 x := term.var x
| (termctx.value v) _ := v
| (termctx.var x) _ := term.var x
| (termctx.unop op t) x := term.unop op (termctx.apply t x)
| (termctx.binop op t₁ t₂) x := term.binop op (termctx.apply t₁ x) (termctx.apply t₂ x)
| (termctx.app t₁ t₂) x := term.app (termctx.apply t₁ x) (termctx.apply t₂ x)

instance : has_coe_to_fun termctx := ⟨λ _, var → term, termctx.apply⟩

def propctx.apply: propctx → var → prop
| (propctx.term t) x := t x
| (propctx.not p) x := prop.not (propctx.apply p x)
| (propctx.and p₁ p₂) x := prop.and (propctx.apply p₁ x) (propctx.apply p₂ x)
| (propctx.or p₁ p₂) x := prop.or (propctx.apply p₁ x) (propctx.apply p₂ x)
| (propctx.pre p₁ p₂) x := prop.or (propctx.apply p₁ x) (propctx.apply p₂ x)

instance : has_coe_to_fun termctx := ⟨λ _, var → term, termctx.apply⟩

