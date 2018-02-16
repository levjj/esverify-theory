import .syntax .notations

-- free variables

inductive free_in_term (x: var) : term → Prop
| var                              : free_in_term x
| unop {t: term} {op: unop}        : free_in_term t → free_in_term (term.unop op t)
| binop₁ {t₁ t₂: term} {op: binop} : free_in_term t₁ → free_in_term (term.binop op t₁ t₂)
| binop₂ {t₁ t₂: term} {op: binop} : free_in_term t₂ → free_in_term (term.binop op t₁ t₂)
| app₁ {t₁ t₂: term}               : free_in_term t₁ → free_in_term (term.app t₁ t₂)
| app₂ {t₁ t₂: term}               : free_in_term t₂ → free_in_term (term.app t₁ t₂)

inductive free_in_prop (x: var) : prop → Prop
| term {t: term}                        : free_in_term x t  → free_in_prop t
| not {p: prop}                         : free_in_prop p    → free_in_prop (prop.not p)
| and₁ {p₁ p₂: prop}                    : free_in_prop p₁   → free_in_prop (prop.and p₁ p₂)
| and₂ {p₁ p₂: prop}                    : free_in_prop p₂   → free_in_prop (prop.and p₁ p₂)
| or₁ {p₁ p₂: prop}                     : free_in_prop p₁   → free_in_prop (prop.or p₁ p₂)
| or₂ {p₁ p₂: prop}                     : free_in_prop p₂   → free_in_prop (prop.or p₁ p₂)
| pre₁ {t₁ t₂: term}                    : free_in_term x t₁ → free_in_prop (prop.pre t₁ t₂)
| pre₂ {t₁ t₂: term}                    : free_in_term x t₂ → free_in_prop (prop.pre t₁ t₂)
| preop {t: term} {op: unop}            : free_in_term x t  → free_in_prop (prop.pre₁ op t)
| preop₁ {t₁ t₂: term} {op: binop}      : free_in_term x t₁ → free_in_prop (prop.pre₂ op t₁ t₂)
| preop₂ {t₁ t₂: term} {op: binop}      : free_in_term x t₂ → free_in_prop (prop.pre₂ op t₁ t₂)
| post₁ {t₁ t₂: term}                   : free_in_term x t₁ → free_in_prop (prop.post t₁ t₂)
| post₂ {t₁ t₂: term}                   : free_in_term x t₂ → free_in_prop (prop.post t₁ t₂)
| call₁ {t₁ t₂: term}                   : free_in_term x t₁ → free_in_prop (prop.call t₁ t₂)
| call₂ {t₁ t₂: term}                   : free_in_term x t₂ → free_in_prop (prop.call t₁ t₂)
| forallc₁ {y: var} {t: term} {p: prop} : (x ≠ y) → free_in_term x t → free_in_prop (prop.forallc y t p)
| forallc₂ {y: var} {t: term} {p: prop} : (x ≠ y) → free_in_prop p → free_in_prop (prop.forallc y t p)
| exis {y: var} {p: prop}               : (x ≠ y) → free_in_prop p → free_in_prop (prop.exis y p)

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

-- notation x ∈ FV t/p

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

def FV {α: Type} [h: has_fv α] (a: α): set var := (has_fv.fv a).to_set

-- helper lemmas

lemma free_in_term.value.inv {x: var} {v: value}: ¬ free_in_term x v :=
  assume x_free_in_v: free_in_term x v,
  show «false», by cases x_free_in_v

lemma free_in_term.var.inv {x y: var}: free_in_term x y → (x = y) :=
  assume x_free_in_y: free_in_term x y,
  begin
    cases x_free_in_y,
    case free_in_term.var { exact rfl }
  end

lemma free_in_term.unop.inv {x: var} {op: unop} {t: term}: free_in_term x (term.unop op t) → free_in_term x t :=
  assume x_free_in_unop: free_in_term x (term.unop op t),
  begin
    cases x_free_in_unop,
    case free_in_term.unop x_free_in_t { from x_free_in_t }
  end

lemma free_in_term.binop.inv {x: var} {op: binop} {t₁ t₂: term}:
                              free_in_term x (term.binop op t₁ t₂) → free_in_term x t₁ ∨ free_in_term x t₂ :=
  assume x_free_in_binop: free_in_term x (term.binop op t₁ t₂),
  begin
    cases x_free_in_binop,
    case free_in_term.binop₁ x_free_in_t₁ { from or.inl x_free_in_t₁ },
    case free_in_term.binop₂ x_free_in_t₂ { from or.inr x_free_in_t₂ }
  end

lemma free_in_term.app.inv {x: var} {t₁ t₂: term}:
                           free_in_term x (term.app t₁ t₂) → free_in_term x t₁ ∨ free_in_term x t₂ :=
  assume x_free_in_app: free_in_term x (term.app t₁ t₂),
  begin
    cases x_free_in_app,
    case free_in_term.app₁ x_free_in_t₁ { from or.inl x_free_in_t₁ },
    case free_in_term.app₂ x_free_in_t₂ { from or.inr x_free_in_t₂ }
  end

lemma free_in_prop.term.inv {t: term} {x: var}: free_in_prop x t → free_in_term x t :=
  assume x_free_in_t: free_in_prop x t,
  begin
    cases x_free_in_t,
    case free_in_prop.term free_in_t { from free_in_t }
  end

lemma free_in_prop.not.inv {P: prop} {x: var}: free_in_prop x P.not → free_in_prop x P :=
  assume x_free_in_not: free_in_prop x P.not,
  begin
    cases x_free_in_not,
    case free_in_prop.not free_in_P { from free_in_P }
  end

lemma free_in_prop.and.inv {P₁ P₂: prop} {x: var}: free_in_prop x (P₁ && P₂) → free_in_prop x P₁ ∨ free_in_prop x P₂ :=
  assume x_free_in_and: free_in_prop x (P₁ && P₂),
  begin
    cases x_free_in_and,
    case free_in_prop.and₁ free_in_P₁ {
      show free_in_prop x P₁ ∨ free_in_prop x P₂, from or.inl free_in_P₁
    },
    case free_in_prop.and₂ free_in_P₂ {
      show free_in_prop x P₁ ∨ free_in_prop x P₂, from or.inr free_in_P₂
    }
  end

lemma free_in_prop.or.inv {P₁ P₂: prop} {x: var}: free_in_prop x (P₁ || P₂) → free_in_prop x P₁ ∨ free_in_prop x P₂ :=
  assume x_free_in_or: free_in_prop x (P₁ || P₂),
  begin
    cases x_free_in_or,
    case free_in_prop.or₁ free_in_P₁ {
      show free_in_prop x P₁ ∨ free_in_prop x P₂, from or.inl free_in_P₁
    },
    case free_in_prop.or₂ free_in_P₂ {
      show free_in_prop x P₁ ∨ free_in_prop x P₂, from or.inr free_in_P₂
    }
  end

lemma free_in_prop.pre.inv {t₁ t₂: term} {x: var}:
      free_in_prop x (prop.pre t₁ t₂) → free_in_term x t₁ ∨ free_in_term x t₂ :=
  assume x_free_in_pre: free_in_prop x (prop.pre t₁ t₂),
  begin
    cases x_free_in_pre,
    case free_in_prop.pre₁ free_in_t₁ { from or.inl free_in_t₁ },
    case free_in_prop.pre₂ free_in_t₂ { from or.inr free_in_t₂ } 
  end

lemma free_in_prop.post.inv {t₁ t₂: term} {x: var}:
      free_in_prop x (prop.post t₁ t₂) → free_in_term x t₁ ∨ free_in_term x t₂ :=
  assume x_free_in_post: free_in_prop x (prop.post t₁ t₂),
  begin
    cases x_free_in_post,
    case free_in_prop.post₁ free_in_t₁ { from or.inl free_in_t₁ },
    case free_in_prop.post₂ free_in_t₂ { from or.inr free_in_t₂ } 
  end

lemma free_in_prop.forallc.inv {P: prop} {t: term} {x fx: var}:
      free_in_prop x (prop.forallc fx t P) → (x ≠ fx) ∧ (free_in_term x t ∨ free_in_prop x P) :=
  assume x_free_in_forallc: free_in_prop x (prop.forallc fx t P),
  begin
    cases x_free_in_forallc,
    case free_in_prop.forallc₁ x_neq_fx free_in_t {
      from ⟨x_neq_fx, or.inl free_in_t⟩ 
    },
    case free_in_prop.forallc₂ x_neq_fx free_in_P {
      from ⟨x_neq_fx, or.inr free_in_P⟩ 
    }
  end

lemma free_in_prop.implies.inv {P₁ P₂: prop} {x: var}: free_in_prop x (prop.implies P₁ P₂) → free_in_prop x P₁ ∨ free_in_prop x P₂ :=
  assume x_free_in_implies: free_in_prop x (prop.or P₁.not P₂),
  begin
    cases x_free_in_implies,
    case free_in_prop.or₁ x_free_in_not_P₁ {
      cases x_free_in_not_P₁,
      case free_in_prop.not free_in_P₁ {
        show free_in_prop x P₁ ∨ free_in_prop x P₂, from or.inl free_in_P₁
      }
    },
    case free_in_prop.or₂ free_in_P₂ {
      show free_in_prop x P₁ ∨ free_in_prop x P₂, from or.inr free_in_P₂
    }
  end

lemma free_in_vc.term.inv {t: term} {x: var}: free_in_vc x t → free_in_term x t :=
  assume x_free_in_t: free_in_vc x t,
  begin
    cases x_free_in_t,
    case free_in_vc.term free_in_t { from free_in_t }
  end

lemma free_in_vc.not.inv {P: vc} {x: var}: free_in_vc x P.not → free_in_vc x P :=
  assume x_free_in_not: free_in_vc x P.not,
  begin
    cases x_free_in_not,
    case free_in_vc.not free_in_P { from free_in_P }
  end

lemma free_in_vc.and.inv {P₁ P₂: vc} {x: var}: free_in_vc x (P₁ && P₂) → free_in_vc x P₁ ∨ free_in_vc x P₂ :=
  assume x_free_in_and: free_in_vc x (P₁ && P₂),
  begin
    cases x_free_in_and,
    case free_in_vc.and₁ free_in_P₁ {
      show free_in_vc x P₁ ∨ free_in_vc x P₂, from or.inl free_in_P₁
    },
    case free_in_vc.and₂ free_in_P₂ {
      show free_in_vc x P₁ ∨ free_in_vc x P₂, from or.inr free_in_P₂
    }
  end

lemma free_in_vc.or.inv {P₁ P₂: vc} {x: var}: free_in_vc x (P₁ || P₂) → free_in_vc x P₁ ∨ free_in_vc x P₂ :=
  assume x_free_in_or: free_in_vc x (P₁ || P₂),
  begin
    cases x_free_in_or,
    case free_in_vc.or₁ free_in_P₁ {
      show free_in_vc x P₁ ∨ free_in_vc x P₂, from or.inl free_in_P₁
    },
    case free_in_vc.or₂ free_in_P₂ {
      show free_in_vc x P₁ ∨ free_in_vc x P₂, from or.inr free_in_P₂
    }
  end

lemma free_in_vc.pre.inv {t₁ t₂: term} {x: var}:
      free_in_vc x (vc.pre t₁ t₂) → free_in_term x t₁ ∨ free_in_term x t₂ :=
  assume x_free_in_pre: free_in_vc x (vc.pre t₁ t₂),
  begin
    cases x_free_in_pre,
    case free_in_vc.pre₁ free_in_t₁ { from or.inl free_in_t₁ },
    case free_in_vc.pre₂ free_in_t₂ { from or.inr free_in_t₂ } 
  end

lemma free_in_vc.pre₁.inv {t: term} {op: unop} {x: var}:
      free_in_vc x (vc.pre₁ op t) → free_in_term x t :=
  assume x_free_in_pre: free_in_vc x (vc.pre₁ op t),
  begin
    cases x_free_in_pre,
    case free_in_vc.preop free_in_t { from free_in_t }
  end

lemma free_in_vc.pre₂.inv {t₁ t₂: term} {op: binop} {x: var}:
      free_in_vc x (vc.pre₂ op t₁ t₂) → free_in_term x t₁ ∨ free_in_term x t₂ :=
  assume x_free_in_pre: free_in_vc x (vc.pre₂ op t₁ t₂),
  begin
    cases x_free_in_pre,
    case free_in_vc.preop₁ free_in_t₁ { from or.inl free_in_t₁ },
    case free_in_vc.preop₂ free_in_t₂ { from or.inr free_in_t₂ } 
  end

lemma free_in_vc.post.inv {t₁ t₂: term} {x: var}:
      free_in_vc x (vc.post t₁ t₂) → free_in_term x t₁ ∨ free_in_term x t₂ :=
  assume x_free_in_post: free_in_vc x (vc.post t₁ t₂),
  begin
    cases x_free_in_post,
    case free_in_vc.post₁ free_in_t₁ { from or.inl free_in_t₁ },
    case free_in_vc.post₂ free_in_t₂ { from or.inr free_in_t₂ } 
  end

lemma free_in_vc.univ.inv {P: vc} {x y: var}:
      free_in_vc x (vc.univ y P) → (x ≠ y) ∧ free_in_vc x P :=
  assume x_free: free_in_vc x (vc.univ y P),
  begin
    cases x_free,
    case free_in_vc.univ x_neq_y free_in_P {
      from ⟨x_neq_y, free_in_P⟩ 
    }
  end

lemma free_in_vc.univ.same.inv {P: vc} {x: var}: ¬ free_in_vc x (vc.univ x P) :=
  assume x_free: free_in_vc x (vc.univ x P),
  begin
    cases x_free,
    case free_in_vc.univ x_neq_y free_in_P {
      contradiction
    }
  end

lemma call_history_closed (H: callhistory) (x: var): ¬ free_in_prop x (calls_to_prop H) :=
  list.rec_on H
  ( -- empty history
    assume x_free: free_in_prop x (calls_to_prop list.nil),
    have calls_to_prop list.nil = value.true, from rfl,
    have x_free_in_true: free_in_prop x value.true, from this ▸ x_free,
    show «false», by begin
      cases x_free_in_true,
      case free_in_prop.term x_free_in_term {
        cases x_free_in_term
      }
    end
  )
  ( -- hist :: rest
    assume h: historyitem,
    assume rest: callhistory,
    assume ih: ¬ free_in_prop x (calls_to_prop rest),
    historyitem.cases_on h
    ( -- <nop> :: rest
      have h2: ¬ free_in_prop x (calls_to_prop rest), from ih,
      have calls_to_prop (historyitem.nop :: rest) = calls_to_prop rest, by unfold calls_to_prop,
      show ¬ free_in_prop x (historyitem.nop :: rest), from this.symm ▸ h2
    )
    ( -- <call> :: rest
      assume f x' R S e σ vₓ,
      assume x_free: free_in_prop x (calls_to_prop (call f x' R S e σ vₓ :: rest)),
      have calls_to_prop (call f x' R S e σ vₓ :: rest) =
        (prop.call (value.func f x' R S e σ) vₓ && calls_to_prop rest), by unfold calls_to_prop,
      have x_free_in_prop: free_in_prop x (
        prop.call (value.func f x' R S e σ) vₓ &&
        calls_to_prop rest), from this ▸ x_free,
      have x_not_free_in_vₓ: ¬ free_in_term x vₓ, from (
        assume x_free_in_vₓ: free_in_term x vₓ,
        show «false», by cases x_free_in_vₓ
      ),
      have x_not_free_in_f: ¬ free_in_term x (value.func f x' R S e σ), from (
        assume x_free_in_f: free_in_term x (value.func f x' R S e σ),
        show «false», by cases x_free_in_f
      ),
      have
        free_in_prop x (calls_to_prop rest) ∨
        free_in_prop x (prop.call (value.func f x' R S e σ) vₓ),
      from (free_in_prop.and.inv x_free_in_prop).symm,
      or.elim this ih (
        assume x_free_in_call: free_in_prop x (prop.call (value.func f x' R S e σ) vₓ),
        show «false», by begin
          cases x_free_in_call,
          case free_in_prop.call₁ x_free_in_f {
            show «false», from x_not_free_in_f x_free_in_f
          },
          case free_in_prop.call₂ x_free_in_vₓ {
            show «false», from x_not_free_in_vₓ x_free_in_vₓ
          }
        end
      )
    )
  )

lemma env.contains.same.inv {σ: env} {x y: var} {v: value}: x ∉ (σ[y↦v]) → ¬ (x = y ∨ x ∈ σ) :=
  assume x_not_in: x ∉ (σ[y↦v]),
  assume : (x = y ∨ x ∈ σ),
  this.elim (
    assume x_is_y: x = y,
    have x ∈ (σ[x↦v]), from env.contains.same,
    have x ∈ (σ[y↦v]), from @eq.subst var (λa, x ∈ (σ[a↦v])) x y x_is_y this,
    show «false», from x_not_in this
  ) (
    assume : x ∈ σ,
    have x ∈ (σ[y↦v]), from env.contains.rest this,
    show «false», from x_not_in this
  )

lemma env.contains_apply_equiv {σ: env} {x: var}:
  ((σ x = none) ↔ (x ∉ σ)) ∧ ((∃v, σ x = some v) ↔ (x ∈ σ)) :=
begin
  induction σ with y v' σ' ih,
  show ((env.empty x = none) ↔ (x ∉ env.empty)) ∧ ((∃v, env.empty x = some v) ↔ (x ∈ env.empty)), by begin
    split,
    show (env.empty x = none) ↔ (x ∉ env.empty), by begin
      split,
      show (env.empty x = none) → (x ∉ env.empty), by begin
        assume : (env.empty x = none),
        by_contradiction h,
        cases h
      end,
      show (x ∉ env.empty) → (env.empty x = none), by begin
        assume : (x ∉ env.empty),
        have : (env.apply env.empty x = none), by unfold env.apply,
        show (env.empty x = none), from this
      end
    end,
    show (∃v, env.empty x = some v) ↔ (x ∈ env.empty), by begin
      split,
      show (∃v, env.empty x = some v) → (x ∈ env.empty), from (
        assume : (∃v, env.empty x = some v),
        let (⟨v, h0⟩) := this in
        have h1: env.apply env.empty x = some v, from h0,
        have h2: env.apply env.empty x = none, by unfold env.apply,
        have some v = none, from eq.trans h1.symm h2,
        show (x ∈ env.empty), by contradiction
      ),
      show (x ∈ env.empty) → (∃v,env.empty x = some v), by begin
        assume h: x ∈ env.empty,
        cases h
      end
    end
  end,
  show (((σ'[y↦v']) x = none) ↔ (x ∉ (σ'[y↦v']))) ∧ ((∃v, (σ'[y↦v']) x = some v) ↔ (x ∈ (σ'[y↦v']))), by begin
    split,
    show (((σ'[y↦v']) x = none) ↔ (x ∉ (σ'[y↦v']))), by begin
      split,
      show (((σ'[y↦v']) x = none) → (x ∉ (σ'[y↦v']))), by begin
        assume h: ((σ'[y↦v']) x = none),
        have h2: (env.apply (σ'[y↦v']) x = (if y = x ∧ option.is_none (σ'.apply x) then v' else σ'.apply x)),
        by unfold env.apply,
        have h3: ((if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = none),
        from eq.trans h2.symm h,
        have h4: (σ'.apply x = none), by begin
          by_cases (y = x ∧ option.is_none (σ'.apply x)),
          show (σ'.apply x = none), by begin
            have : ((if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = ↑v'),
            by simp[h],
            have : (none = ↑v'), from eq.trans h3.symm this,
            contradiction
          end,
          show (σ'.apply x = none), by begin
            have : ((if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = σ'.apply x),
            by simp[h],
            show (σ'.apply x = none), from eq.trans this.symm h3
          end
        end,
        have : x ∉ σ', from ih.left.mp h4,
        have h5: ¬ (x = y), by begin
          by_contradiction,
          have h6: (option.is_none (σ'.apply x) = tt), from (is_none.inv (σ'.apply x)).mpr h4,
          have : (y = x ∧ option.is_none (σ'.apply x)), from ⟨a.symm, h6⟩,
          have : ((if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = ↑v'),
          by simp[this],
          have : (none = ↑v'), from eq.trans h3.symm this,
          contradiction
        end,
        by_contradiction a,
        cases a,
        case env.contains.same x_is_x {
          contradiction
        },
        case env.contains.rest x_is_x {
          contradiction
        }
      end,
      show (x ∉ (σ'[y↦v'])) → (((σ'[y↦v']) x = none)), by begin
        assume : (x ∉ (σ'[y↦v'])),
        have h7: ¬ (x = y ∨ x ∈ σ'), from env.contains.same.inv this,
        have : x ≠ y, from (not_or_distrib.mp h7).left,
        have h8: y ≠ x, from ne.symm this,
        have h9: x ∉ σ', from (not_or_distrib.mp h7).right,
        have h10: (σ'.apply x = none), from ih.left.mpr h9,
        have h11: (env.apply (σ'[y↦v']) x = (if y = x ∧ option.is_none (σ'.apply x) then v' else σ'.apply x)),
        by unfold env.apply,
        have h12: ((if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = σ'.apply x),
        by simp[h8],
        show ((σ'[y↦v']) x = none), from eq.trans (eq.trans h11 h12) h10
      end
    end,
    show ((∃v, (σ'[y↦v']) x = some v) ↔ (x ∈ (σ'[y↦v']))), by begin
      split,
      show ((∃v, (σ'[y↦v']) x = some v) → (x ∈ (σ'[y↦v']))), from (
        assume : (∃v, (σ'[y↦v']) x = some v),
        let ⟨v, h13⟩ := this in begin
        have h14: (env.apply (σ'[y↦v']) x = (if y = x ∧ option.is_none (σ'.apply x) then v' else σ'.apply x)),
        by unfold env.apply,
        by_cases (y = x ∧ option.is_none (σ'.apply x)) with h15,
        show (x ∈ (σ'[y↦v'])), by begin
          have x_is_y: (y = x), from h15.left,
          have : (x ∈ (σ'[x↦v'])), from env.contains.same,
          show x ∈ (σ'[y↦v']), from @eq.subst var (λa, x ∈ (σ'[a↦v'])) x y x_is_y.symm this
        end,
        show (x ∈ (σ'[y↦v'])), by begin
          have : ((if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = σ'.apply x),
          by simp[h15],
          have : (σ'.apply x = v), from eq.trans (eq.trans this.symm h14.symm) h13,
          have : x ∈ σ', from ih.right.mp (exists.intro v this),
          show x ∈ (σ'[y↦v']), from env.contains.rest this
        end
      end),
      show (x ∈ (σ'[y↦v'])) → (∃v, (σ'[y↦v']) x = some v), by begin
        assume h16: (x ∈ (σ'[y↦v'])),
        have h17: (env.apply (σ'[y↦v']) x = (if y = x ∧ option.is_none (σ'.apply x) then v' else σ'.apply x)),
        by unfold env.apply,
        cases h16,
        case env.contains.same {
          by_cases (x = x ∧ option.is_none (σ'.apply x)),
          show (∃v, (σ'[x↦v']) x = some v), by begin
            have : ((if x = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = v'),
            by { simp[h] },
            show (∃v, (σ'[x↦v']) x = some v), from exists.intro v' (eq.trans h17 this)
          end,
          show (∃v, (σ'[x↦v']) x = some v), by begin
            have h19: ¬option.is_none (σ'.apply x), by begin
              by_contradiction h18,
              have : (x = x ∧ option.is_none (σ'.apply x)), from ⟨rfl, h18⟩,
              exact h this
            end,
            have : ∃v, (σ'.apply x) = some v, from not_is_none.rinv.mpr h19,
            cases this with v h20,
            have : ((if x = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = σ'.apply x),
            by { simp[h], simp[h19] },
            show (∃v, (σ'[x↦v']) x = some v), from exists.intro v (eq.trans (eq.trans h17 this) h20)
          end
        },
        case env.contains.rest h27 {
          have : (∃v, σ'.apply x = some v), from ih.right.mpr h27,
          cases this with v h28,
          have : ¬ (option.is_none (σ'.apply x)), from not_is_none.rinv.mp (exists.intro v h28),
          have : ((if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = σ'.apply x),
          by simp[this],
          show (∃v, (σ'[y↦v']) x = some v), from exists.intro v (eq.trans (eq.trans h17 this) h28)
        }
      end
    end
  end
end
