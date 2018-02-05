import .syntax

-- p → q: prop

def prop.implies(p q: prop): prop := prop.or (prop.not p) q

-- use • as hole

notation `•` := termctx.hole

-- simple coersions

instance : has_coe value exp := ⟨exp.value⟩
instance : has_coe value term := ⟨term.value⟩
instance : has_coe term prop := ⟨prop.term⟩
instance : has_coe termctx propctx := ⟨propctx.term⟩

-- use (t ≡ t)/(t ≣ t) to construct equality comparison

infix ≡ := term.binop binop.eq
infix `≣`:50 := termctx.binop binop.eq

-- term to termctx coersion

def term.to_termctx : term → termctx
| (term.value v) := termctx.value v
| (term.var x) := termctx.var x
| (term.unop op t) := termctx.unop op t.to_termctx
| (term.binop op t₁ t₂) := termctx.binop op t₁.to_termctx t₂.to_termctx
| (term.app t₁ t₂) := termctx.app t₁.to_termctx t₂.to_termctx

instance term_to_termctx : has_coe term termctx := ⟨term.to_termctx⟩

-- term to termctx coersion

def prop.to_propctx : prop → propctx
| (prop.term t) := propctx.term t
| (prop.not p) := propctx.not p.to_propctx
| (prop.and p₁ p₂) := propctx.and p₁.to_propctx p₂.to_propctx
| (prop.or p₁ p₂) := propctx.or p₁.to_propctx p₂.to_propctx
| (prop.pre t₁ t₂) := propctx.pre t₁ t₂
| (prop.pre₁ op t) := propctx.pre₁ op t
| (prop.pre₂ op t₁ t₂) := propctx.pre₂ op t₁ t₂
| (prop.post t₁ t₂) := propctx.post t₁ t₂
| (prop.call t₁ t₂) := propctx.call t₁ t₂
| (prop.forallc x t p) := propctx.forallc x t p.to_propctx
| (prop.univ x p) := propctx.univ x p.to_propctx
| (prop.exis x p) := propctx.exis x p.to_propctx

instance prop_to_propctx : has_coe prop propctx := ⟨prop.to_propctx⟩

-- termctx substituttion as function application

def termctx.apply: termctx → var → term
| •                        x := term.var x
| (termctx.value v)        _ := v
| (termctx.var x)          _ := term.var x
| (termctx.unop op t)      x := term.unop op (t.apply x)
| (termctx.binop op t₁ t₂) x := term.binop op (t₁.apply x) (t₂.apply x)
| (termctx.app t₁ t₂)      x := term.app (t₁.apply x) (t₂.apply x)

instance : has_coe_to_fun termctx := ⟨λ _, var → term, termctx.apply⟩

-- propctx substituttion as function application

def propctx.apply: propctx → var → prop
| (propctx.term t) x := t x
| (propctx.not p) x := prop.not (p.apply x)
| (propctx.and p₁ p₂) x := prop.and (p₁.apply x) (p₂.apply x)
| (propctx.or p₁ p₂) x := prop.or (p₁.apply x) (p₂.apply x)
| (propctx.pre t₁ t₂) x := prop.or (t₁ x) (t₂ x)
| (propctx.pre₁ op t) x := prop.pre₁ op (t x)
| (propctx.pre₂ op t₁ t₂) x := prop.pre₂ op (t₁ x) (t₂ x)
| (propctx.post t₁ t₂) x := prop.post (t₁ x) (t₂ x)
| (propctx.call t₁ t₂) x := prop.call (t₁ x) (t₂ x)
| (propctx.forallc x t p) y := prop.forallc x (t y) (p.apply y)
| (propctx.univ x p) y := prop.univ x (p.apply y)
| (propctx.exis x p) y := prop.exis x (p.apply y)

instance : has_coe_to_fun propctx := ⟨λ _, var → prop, propctx.apply⟩
