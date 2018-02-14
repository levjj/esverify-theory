-- quantifier instantiation

import .syntax .notations .freevars

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
| (prop.exis x P)      := have P.size < P.size + 1, from lt_of_add_one,
                          vc.not (vc.univ x (vc.not P.erased))

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

lemma free_of_erased_free {x: var} {P: prop}: (x ∈ FV P.erased ∨ x ∈ FV P.erased_n) → x ∈ FV P :=
  assume x_free_in_erased_or_erased_n: x ∈ FV P.erased ∨ x ∈ FV P.erased_n,
  begin
    induction P,
    case prop.term t { from (
      or.elim x_free_in_erased_or_erased_n
      (
        assume x_free_in_t: free_in_vc x (prop.term t).erased,
        have (prop.term t).erased = vc.term t, by unfold prop.erased,
        have free_in_vc x (vc.term t), from this ▸ x_free_in_t,
        have free_in_term x t, from free_in_vc.term.inv this,
        show free_in_prop x (prop.term t), from free_in_prop.term this
      ) (
        assume x_free_in_t: free_in_vc x (prop.term t).erased_n,
        have (prop.term t).erased_n = vc.term t, by unfold prop.erased_n,
        have free_in_vc x (vc.term t), from this ▸ x_free_in_t,
        have free_in_term x t, from free_in_vc.term.inv this,
        show free_in_prop x (prop.term t), from free_in_prop.term this
      )
    )},
    case prop.not P₁ ih { from (
      or.elim x_free_in_erased_or_erased_n
      (
        assume x_free: x ∈ FV (prop.not P₁).erased,
        have (prop.not P₁).erased = vc.not P₁.erased_n, by unfold prop.erased,
        have x ∈ FV (vc.not P₁.erased_n), from this ▸ x_free,
        have x ∈ FV P₁.erased_n, from free_in_vc.not.inv this,
        have x ∈ FV P₁, from ih (or.inr this),
        show x ∈ FV P₁.not, from free_in_prop.not this
      ) (
        assume x_free: x ∈ FV (prop.not P₁).erased_n,
        have (prop.not P₁).erased_n = vc.not P₁.erased, by unfold prop.erased_n,
        have x ∈ FV (vc.not P₁.erased), from this ▸ x_free,
        have x ∈ FV P₁.erased, from free_in_vc.not.inv this,
        have x ∈ FV P₁, from ih (or.inl this),
        show x ∈ FV P₁.not, from free_in_prop.not this
      )
    )},
    case prop.and P₁ P₂ P₁_ih P₂_ih { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free: x ∈ FV (P₁ && P₂).erased,
        have (prop.and P₁ P₂).erased = P₁.erased && P₂.erased, by unfold prop.erased,
        have x ∈ FV (P₁.erased && P₂.erased), from this ▸ x_free,
        have x ∈ FV P₁.erased ∨ x ∈ FV P₂.erased, from free_in_vc.and.inv this,
        or.elim this (
          assume : x ∈ FV P₁.erased,
          have x ∈ FV P₁, from P₁_ih (or.inl this),
          show x ∈ FV (P₁ && P₂), from free_in_prop.and₁ this
        ) (
          assume : x ∈ FV P₂.erased,
          have x ∈ FV P₂, from P₂_ih (or.inl this),
          show x ∈ FV (P₁ && P₂), from free_in_prop.and₂ this
        )
      ) (
        assume x_free: x ∈ FV (P₁ && P₂).erased_n,
        have (prop.and P₁ P₂).erased_n = P₁.erased_n && P₂.erased_n, by unfold prop.erased_n,
        have x ∈ FV (P₁.erased_n && P₂.erased_n), from this ▸ x_free,
        have x ∈ FV P₁.erased_n ∨ x ∈ FV P₂.erased_n, from free_in_vc.and.inv this,
        or.elim this (
          assume : x ∈ FV P₁.erased_n,
          have x ∈ FV P₁, from P₁_ih (or.inr this),
          show x ∈ FV (P₁ && P₂), from free_in_prop.and₁ this
        ) (
          assume : x ∈ FV P₂.erased_n,
          have x ∈ FV P₂, from P₂_ih (or.inr this),
          show x ∈ FV (P₁ && P₂), from free_in_prop.and₂ this
        )
      )
    )},
    case prop.or P₁ P₂ P₁_ih P₂_ih { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free: x ∈ FV (P₁ || P₂).erased,
        have (prop.or P₁ P₂).erased = P₁.erased || P₂.erased, by unfold prop.erased,
        have x ∈ FV (P₁.erased || P₂.erased), from this ▸ x_free,
        have x ∈ FV P₁.erased ∨ x ∈ FV P₂.erased, from free_in_vc.or.inv this,
        or.elim this (
          assume : x ∈ FV P₁.erased,
          have x ∈ FV P₁, from P₁_ih (or.inl this),
          show x ∈ FV (P₁ || P₂), from free_in_prop.or₁ this
        ) (
          assume : x ∈ FV P₂.erased,
          have x ∈ FV P₂, from P₂_ih (or.inl this),
          show x ∈ FV (P₁ || P₂), from free_in_prop.or₂ this
        )
      ) (
        assume x_free: x ∈ FV (P₁ || P₂).erased_n,
        have (prop.or P₁ P₂).erased_n = P₁.erased_n || P₂.erased_n, by unfold prop.erased_n,
        have x ∈ FV (P₁.erased_n || P₂.erased_n), from this ▸ x_free,
        have x ∈ FV P₁.erased_n ∨ x ∈ FV P₂.erased_n, from free_in_vc.or.inv this,
        or.elim this (
          assume : x ∈ FV P₁.erased_n,
          have x ∈ FV P₁, from P₁_ih (or.inr this),
          show x ∈ FV (P₁ || P₂), from free_in_prop.or₁ this
        ) (
          assume : x ∈ FV P₂.erased_n,
          have x ∈ FV P₂, from P₂_ih (or.inr this),
          show x ∈ FV (P₁ || P₂), from free_in_prop.or₂ this
        )
      )
    )},
    case prop.pre t₁ t₂ { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free: x ∈ FV (prop.pre t₁ t₂).erased,
        have (prop.pre t₁ t₂).erased = vc.pre t₁ t₂, by unfold prop.erased,
        have x ∈ FV (vc.pre t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.pre.inv this,
        or.elim this (
          assume : x ∈ FV t₁,
          show free_in_prop x (prop.pre t₁ t₂), from free_in_prop.pre₁ this
        ) (
          assume : x ∈ FV t₂,
          show free_in_prop x (prop.pre t₁ t₂), from free_in_prop.pre₂ this
        )
      ) (
        assume x_free: x ∈ FV (prop.pre t₁ t₂).erased_n,
        have (prop.pre t₁ t₂).erased_n = vc.pre t₁ t₂, by unfold prop.erased_n,
        have x ∈ FV (vc.pre t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.pre.inv this,
        or.elim this (
          assume : x ∈ FV t₁,
          show free_in_prop x (prop.pre t₁ t₂), from free_in_prop.pre₁ this
        ) (
          assume : x ∈ FV t₂,
          show free_in_prop x (prop.pre t₁ t₂), from free_in_prop.pre₂ this
        )
      )
    )},
    case prop.pre₁ op t { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free_in_t: free_in_vc x (prop.pre₁ op t).erased,
        have (prop.pre₁ op t).erased = vc.pre₁ op t, by unfold prop.erased,
        have free_in_vc x (vc.pre₁ op t), from this ▸ x_free_in_t,
        have free_in_term x t, from free_in_vc.pre₁.inv this,
        show free_in_prop x (prop.pre₁ op t), from free_in_prop.preop this
      ) (
        assume x_free_in_t: free_in_vc x (prop.pre₁ op t).erased_n,
        have (prop.pre₁ op t).erased_n = vc.pre₁ op t, by unfold prop.erased_n,
        have free_in_vc x (vc.pre₁ op t), from this ▸ x_free_in_t,
        have free_in_term x t, from free_in_vc.pre₁.inv this,
        show free_in_prop x (prop.pre₁ op t), from free_in_prop.preop this
      )
    )},
    case prop.pre₂ op t₁ t₂ { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free: x ∈ FV (prop.pre₂ op t₁ t₂).erased,
        have (prop.pre₂ op t₁ t₂).erased = vc.pre₂ op t₁ t₂, by unfold prop.erased,
        have x ∈ FV (vc.pre₂ op t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.pre₂.inv this,
        or.elim this (
          assume : x ∈ FV t₁,
          show free_in_prop x (prop.pre₂ op t₁ t₂), from free_in_prop.preop₁ this
        ) (
          assume : x ∈ FV t₂,
          show free_in_prop x (prop.pre₂ op t₁ t₂), from free_in_prop.preop₂ this
        )
      ) (
        assume x_free: x ∈ FV (prop.pre₂ op t₁ t₂).erased_n,
        have (prop.pre₂ op t₁ t₂).erased_n = vc.pre₂ op t₁ t₂, by unfold prop.erased_n,
        have x ∈ FV (vc.pre₂ op t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.pre₂.inv this,
        or.elim this (
          assume : x ∈ FV t₁,
          show free_in_prop x (prop.pre₂ op t₁ t₂), from free_in_prop.preop₁ this
        ) (
          assume : x ∈ FV t₂,
          show free_in_prop x (prop.pre₂ op t₁ t₂), from free_in_prop.preop₂ this
        )
      )
    )},
    case prop.post t₁ t₂ { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free: x ∈ FV (prop.post t₁ t₂).erased,
        have (prop.post t₁ t₂).erased = vc.post t₁ t₂, by unfold prop.erased,
        have x ∈ FV (vc.post t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.post.inv this,
        or.elim this (
          assume : x ∈ FV t₁,

          show free_in_prop x (prop.post t₁ t₂), from free_in_prop.post₁ this
        ) (
          assume : x ∈ FV t₂,

          show free_in_prop x (prop.post t₁ t₂), from free_in_prop.post₂ this
        )
      ) (
        assume x_free: x ∈ FV (prop.post t₁ t₂).erased_n,
        have (prop.post t₁ t₂).erased_n = vc.post t₁ t₂, by unfold prop.erased_n,
        have x ∈ FV (vc.post t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.post.inv this,
        or.elim this (
          assume : x ∈ FV t₁,

          show free_in_prop x (prop.post t₁ t₂), from free_in_prop.post₁ this
        ) (
          assume : x ∈ FV t₂,

          show free_in_prop x (prop.post t₁ t₂), from free_in_prop.post₂ this
        )
      )
    )},
    case prop.call t₁ t₂ { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free: x ∈ FV (prop.call t₁ t₂).erased,
        have (prop.call t₁ t₂).erased = vc.term value.true, by unfold prop.erased,
        have x ∈ FV (vc.term value.true), from this ▸ x_free,
        have x ∈ FV (term.value value.true), from free_in_vc.term.inv this,
        absurd this (free_in_term.value.inv)
      ) (
        assume x_free: x ∈ FV (prop.call t₁ t₂).erased_n,
        have (prop.call t₁ t₂).erased_n = vc.term value.true, by unfold prop.erased_n,
        have x ∈ FV (vc.term value.true), from this ▸ x_free,
        have x ∈ FV (term.value value.true), from free_in_vc.term.inv this,
        absurd this (free_in_term.value.inv)
      )
    )},
    case prop.forallc y t P₁ ih { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free: x ∈ FV (prop.forallc y t P₁).erased,
        have (prop.forallc y t P₁).erased = vc.univ y P₁.erased, by unfold prop.erased,
        have x ∈ FV (vc.univ y P₁.erased), from this ▸ x_free,
        have h2: (x ≠ y) ∧ free_in_vc x P₁.erased, from free_in_vc.univ.inv this,
        have x ∈ FV P₁, from ih (or.inl h2.right),
        show x ∈ FV (prop.forallc y t P₁), from free_in_prop.forallc₂ h2.left this
      ) (
        assume x_free: x ∈ FV (prop.forallc y t P₁).erased_n,
        have (prop.forallc y t P₁).erased_n = vc.term value.true, by unfold prop.erased_n,
        have x ∈ FV (vc.term value.true), from this ▸ x_free,
        have x ∈ FV (term.value value.true), from free_in_vc.term.inv this,
        absurd this (free_in_term.value.inv)
      )
    )},
    case prop.exis y P₁ ih { from (
      or.elim x_free_in_erased_or_erased_n (
        assume x_free: x ∈ FV (prop.exis y P₁).erased,
        have (prop.exis y P₁).erased = vc.not (vc.univ y (vc.not P₁.erased)), by unfold prop.erased,
        have x ∈ FV (vc.not (vc.univ y (vc.not P₁.erased))), from this ▸ x_free,
        have x ∈ FV (vc.univ y (vc.not P₁.erased)), from free_in_vc.not.inv this,
        have h2: (x ≠ y) ∧ free_in_vc x (vc.not P₁.erased), from free_in_vc.univ.inv this,
        have h3: x ∈ FV P₁.erased, from free_in_vc.not.inv h2.right,
        have x ∈ FV P₁, from ih (or.inl h3),
        show x ∈ FV (prop.exis y P₁), from free_in_prop.exis h2.left this
      )
      (
        assume x_free: x ∈ FV (prop.exis y P₁).erased_n,
        have (prop.exis y P₁).erased_n = vc.not (vc.univ y (vc.not P₁.erased_n)), by unfold prop.erased_n,
        have x ∈ FV (vc.not (vc.univ y (vc.not P₁.erased_n))), from this ▸ x_free,
        have x ∈ FV (vc.univ y (vc.not P₁.erased_n)), from free_in_vc.not.inv this,
        have h2: (x ≠ y) ∧ free_in_vc x (vc.not P₁.erased_n), from free_in_vc.univ.inv this,
        have h3: x ∈ FV P₁.erased_n, from free_in_vc.not.inv h2.right,
        have x ∈ FV P₁, from ih (or.inr h3),
        show x ∈ FV (prop.exis y P₁), from free_in_prop.exis h2.left this
      )
    )}
  end
