import .syntax .etc

-- free variables

inductive free_in_term (x: var) : term → Prop
| freevar                          : free_in_term x
| unop {t: term} {op: unop}        : free_in_term t → free_in_term (term.unop op t)
| binop₁ {t₁ t₂: term} {op: binop} : free_in_term t₁ → free_in_term (term.binop op t₁ t₂)
| binop₂ {t₁ t₂: term} {op: binop} : free_in_term t₂ → free_in_term (term.binop op t₁ t₂)
| app₁ {t₁ t₂: term}               : free_in_term t₁ → free_in_term (term.app t₁ t₂)
| app₂ {t₁ t₂: term}               : free_in_term t₂ → free_in_term (term.app t₁ t₂)

inductive free_in_prop (x: var) : prop → Prop
| term {t: term}                        : free_in_term x t → free_in_prop t
| not {p: prop}                         : free_in_prop p → free_in_prop (prop.not p)
| and₁ {p₁ p₂: prop}                    : free_in_prop p₁ → free_in_prop (prop.and p₁ p₂)
| and₂ {p₁ p₂: prop}                    : free_in_prop p₂ → free_in_prop (prop.and p₁ p₂)
| or₁ {p₁ p₂: prop}                     : free_in_prop p₁ → free_in_prop (prop.or p₁ p₂)
| or₂ {p₁ p₂: prop}                     : free_in_prop p₂ → free_in_prop (prop.or p₁ p₂)
| pre₁ {t₁ t₂: term}                    : free_in_term x t₁ → free_in_prop (prop.pre t₁ t₂)
| pre₂ {t₁ t₂: term}                    : free_in_term x t₂ → free_in_prop (prop.pre t₁ t₂)
| preop {t: term} {op: unop}            : free_in_term x t → free_in_prop (prop.pre₁ op t)
| preop₁ {t₁ t₂: term} {op: binop}      : free_in_term x t₁ → free_in_prop (prop.pre₂ op t₁ t₂)
| preop₂ {t₁ t₂: term} {op: binop}      : free_in_term x t₂ → free_in_prop (prop.pre₂ op t₁ t₂)
| post₁ {t₁ t₂: term}                   : free_in_term x t₁ → free_in_prop (prop.post t₁ t₂)
| post₂ {t₁ t₂: term}                   : free_in_term x t₂ → free_in_prop (prop.post t₁ t₂)
| call₁ {t₁ t₂: term}                   : free_in_term x t₁ → free_in_prop (prop.call t₁ t₂)
| call₂ {t₁ t₂: term}                   : free_in_term x t₂ → free_in_prop (prop.call t₁ t₂)
| forallc₁ {y: var} {t: term} {p: prop} : (x ≠ y) → free_in_term x t → free_in_prop (prop.forallc y t p)
| forallc₂ {y: var} {t: term} {p: prop} : (x ≠ y) → free_in_prop p → free_in_prop (prop.forallc y t p)
| exist {y: var} {p: prop}              : (x ≠ y) → free_in_prop p → free_in_prop (prop.exist y p)

-- notation x ∈ FV p

structure freevars := (p: prop)
instance : has_mem var freevars := ⟨λx fv, free_in_prop x fv.p⟩ 
def FV(p: prop): freevars := freevars.mk p

-- validity

inductive valid : prop → Prop
notation `⟪` p `⟫`: 100 := valid p
| to_prop {p: prop}: valid p

notation `⟪` p `⟫`: 100 := valid p
