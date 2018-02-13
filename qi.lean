-- quantifier instantiation

import .syntax .notations

constant prop.instantiated: prop → vc

constant prop.instantiated_n: prop → vc

mutual def prop.erased, prop.erased_n

with prop.erased: prop → vc
| (prop.term t)        := vc.term t
| (prop.not P)         := have h: P.size + 1 < P.size + 2, from lt_of_add_one,
                          have P.size + 2 = 2 + P.size, from add_comm P.size 2,
                          have P.size + 1 < 2 + P.size, from this ▸ h,
                          vc.not P.erased_n
| (prop.and P₁ P₂)     := have P₁.size < (P₁ && P₂).size, from lt_of_add.left,
                          have P₂.size < (P₁ && P₂).size, from lt_of_add.right,
                          P₁.erased && P₂.erased
| (prop.or P₁ P₂)      := have P₁.size < (P₁ || P₂).size, from lt_of_add.left,
                          have P₂.size < (P₁ || P₂).size, from lt_of_add.right,
                          P₁.erased || P₂.erased
| (prop.pre t₁ t₂)     := vc.pre t₁ t₂
| (prop.pre₁ op t)     := vc.pre₁ op t
| (prop.pre₂ op t₁ t₂) := vc.pre₂ op t₁ t₂
| (prop.post t₁ t₂)    := vc.post t₁ t₂
| (prop.call _ _)      := vc.term value.true
| (prop.forallc x t P) := have P.size < (prop.forallc x t P).size, from lt_of_add_one,
                          vc.univ x P.erased
| (prop.exis x P)      := vc.term value.false -- TODO: look into this

with prop.erased_n: prop → vc
| (prop.term t)        := vc.term t
| (prop.not P)         := have h: P.size + 1 < P.size + 2, from lt_of_add_one,
                          have P.size + 2 = 2 + P.size, from add_comm P.size 2,
                          have P.size + 1 < 2 + P.size, from this ▸ h,
                          vc.not P.erased
| (prop.and P₁ P₂)     := have P₁.size < (P₁ && P₂).size, from lt_of_add.left,
                          have P₂.size < (P₁ && P₂).size, from lt_of_add.right,
                          P₁.erased_n && P₂.erased_n
| (prop.or P₁ P₂)      := have P₁.size < (P₁ || P₂).size, from lt_of_add.left,
                          have P₂.size < (P₁ || P₂ ).size, from lt_of_add.right,
                          P₁.erased_n || P₂.erased_n
| (prop.pre t₁ t₂)     := vc.pre t₁ t₂
| (prop.pre₁ op t)     := vc.pre₁ op t
| (prop.pre₂ op t₁ t₂) := vc.pre₂ op t₁ t₂
| (prop.post t₁ t₂)    := vc.post t₁ t₂
| (prop.call _ _)      := vc.term value.true
| (prop.forallc x t P) := vc.term value.true
| (prop.exis x P)      := have P.size < P.size + 1, from lt_of_add_one,
                          vc.not (vc.univ x (vc.not P.erased_n))

 -- propositions without quantifiers or call triggers do not participate in instantiations
inductive no_instantiations: prop -> Prop
| term {t: term}                 : no_instantiations t
| not {P: prop}                  : no_instantiations P → no_instantiations (prop.not P)
| and {P₁ P₂: prop}              : no_instantiations P₁ → no_instantiations (prop.and P₁ P₂)
| or {P₁ P₂: prop}               : no_instantiations P₂ → no_instantiations (prop.or P₁ P₂)
| pre {t₁ t₂: term}              : no_instantiations (prop.pre t₁ t₂)
| pre₁ {t: term} {op: unop}      : no_instantiations (prop.pre₁ op t)
| pre₂ {t₁ t₂: term} {op: binop} : no_instantiations (prop.pre₂ op t₁ t₂)
| post {t₁ t₂: term}             : no_instantiations (prop.post t₁ t₂)

-- axioms about instantiation

axiom not_dist_instantiated {P: prop}:
  P.not.instantiated = P.instantiated_n.not

axiom and_dist_of_no_instantiations {P Q: prop}:
  no_instantiations Q → ((P && Q).instantiated = P.instantiated && Q.erased)

axiom or_dist_of_no_instantiations {P Q: prop}:
  no_instantiations Q → ((P || Q).instantiated = P.instantiated || Q.erased)
