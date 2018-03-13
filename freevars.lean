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

@[reducible]
def FV {α: Type} [h: has_fv α] (a: α): set var := (has_fv.fv a).to_set

@[reducible]
def closed {α: Type} [h: has_fv α] (a: α): Prop := ∀x, x ∉ FV a

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

lemma free_in_prop.and.inv {P₁ P₂: prop} {x: var}: free_in_prop x (P₁ ⋀ P₂) → free_in_prop x P₁ ∨ free_in_prop x P₂ :=
  assume x_free_in_and: free_in_prop x (P₁ ⋀ P₂),
  begin
    cases x_free_in_and,
    case free_in_prop.and₁ free_in_P₁ {
      show free_in_prop x P₁ ∨ free_in_prop x P₂, from or.inl free_in_P₁
    },
    case free_in_prop.and₂ free_in_P₂ {
      show free_in_prop x P₁ ∨ free_in_prop x P₂, from or.inr free_in_P₂
    }
  end

lemma free_in_prop.or.inv {P₁ P₂: prop} {x: var}: free_in_prop x (P₁ ⋁ P₂) → free_in_prop x P₁ ∨ free_in_prop x P₂ :=
  assume x_free_in_or: free_in_prop x (P₁ ⋁ P₂),
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

lemma free_in_prop.pre₁.inv {t: term} {op: unop} {x: var}:
      free_in_prop x (prop.pre₁ op t) → free_in_term x t :=
  assume x_free_in_pre: free_in_prop x (prop.pre₁ op t),
  begin
    cases x_free_in_pre,
    case free_in_prop.preop free_in_t { from free_in_t }
  end

lemma free_in_prop.pre₂.inv {t₁ t₂: term} {op: binop} {x: var}:
      free_in_prop x (prop.pre₂ op t₁ t₂) → free_in_term x t₁ ∨ free_in_term x t₂ :=
  assume x_free_in_pre: free_in_prop x (prop.pre₂ op t₁ t₂),
  begin
    cases x_free_in_pre,
    case free_in_prop.preop₁ free_in_t₁ { from or.inl free_in_t₁ },
    case free_in_prop.preop₂ free_in_t₂ { from or.inr free_in_t₂ } 
  end

lemma free_in_prop.post.inv {t₁ t₂: term} {x: var}:
      free_in_prop x (prop.post t₁ t₂) → free_in_term x t₁ ∨ free_in_term x t₂ :=
  assume x_free_in_post: free_in_prop x (prop.post t₁ t₂),
  begin
    cases x_free_in_post,
    case free_in_prop.post₁ free_in_t₁ { from or.inl free_in_t₁ },
    case free_in_prop.post₂ free_in_t₂ { from or.inr free_in_t₂ } 
  end

lemma free_in_prop.call.inv {t₁ t₂: term} {x: var}:
      free_in_prop x (prop.call t₁ t₂) → free_in_term x t₁ ∨ free_in_term x t₂ :=
  assume x_free_in_call: free_in_prop x (prop.call t₁ t₂),
  begin
    cases x_free_in_call,
    case free_in_prop.call₁ free_in_t₁ { from or.inl free_in_t₁ },
    case free_in_prop.call₂ free_in_t₂ { from or.inr free_in_t₂ } 
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

lemma free_in_prop.exis.inv {P: prop} {x fx: var}:
      free_in_prop x (prop.exis fx P) → (x ≠ fx) ∧ (free_in_prop x P) :=
  assume x_free_in_exis: free_in_prop x (prop.exis fx P),
  begin
    cases x_free_in_exis,
    case free_in_prop.exis x_neq_fx free_in_P {
      from ⟨x_neq_fx, free_in_P⟩ 
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

lemma free_in_prop.func.inv {P₁ P₂: prop} {t: term} {x y: var}:
      free_in_prop x (prop.func t y P₁ P₂) → free_in_term x t ∨ (x ≠ y ∧ (free_in_prop x P₁ ∨ free_in_prop x P₂)) :=
  assume : free_in_prop x (prop.func t y P₁ P₂),
  have free_in_prop x (term.unop unop.isFunc t ⋀
                      (prop.forallc y t (prop.implies P₁ (prop.pre t y)
                                      ⋀ prop.implies (prop.post t y) P₂))), from this,
  begin
    cases this,
    case free_in_prop.and₁ x_free_in_unopfunc {
      cases x_free_in_unopfunc,
      case free_in_prop.term x_free_in_unopfuncterm {
        cases x_free_in_unopfuncterm,
        case free_in_term.unop x_free_in_func {
          left,
          from x_free_in_func
        }
      }
    },
    case free_in_prop.and₂ x_free_in_forallc {
      cases x_free_in_forallc,
      case free_in_prop.forallc₁ x_neq_y x_free_in_t {
        left,
        from x_free_in_t
      },
      case free_in_prop.forallc₂ x_neq_y x_free_in_forallp {
        cases x_free_in_forallp,
        case free_in_prop.and₁ x_free_Rpre {
          cases x_free_Rpre,
          case free_in_prop.or₁ x_free_in_Pnot {
            cases x_free_in_Pnot,
            case free_in_prop.not x_free_in_P₁ {
              right,
              split,
              from x_neq_y,
              left,
              from x_free_in_P₁
            }
          },
          case free_in_prop.or₂ x_free_in_pre {
            cases x_free_in_pre,
            case free_in_prop.pre₁ x_free_in_t {
              left,
              from x_free_in_t
            },
            case free_in_prop.pre₂ x_free_in_y {
              cases x_free_in_y,
              case free_in_term.var {
                contradiction
              }
            }
          }
        },
        case free_in_prop.and₂ x_free_postS {
          cases x_free_postS,
          case free_in_prop.or₁ x_free_in_postnot {
            cases x_free_in_postnot,
            case free_in_prop.not x_free_in_post {
              cases x_free_in_post,
              case free_in_prop.post₁ x_free_in_t {
                left,
                from x_free_in_t
              },
              case free_in_prop.post₂ x_free_in_y {
                cases x_free_in_y,
                case free_in_term.var {
                  contradiction
                }
              }
            }
          },
          case free_in_prop.or₂ x_free_in_S {
            right,
            split,
            from x_neq_y,
            right,
            from x_free_in_S
          }
        }
      }
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

lemma free_in_vc.and.inv {P₁ P₂: vc} {x: var}: free_in_vc x (P₁ ⋀ P₂) → free_in_vc x P₁ ∨ free_in_vc x P₂ :=
  assume x_free_in_and: free_in_vc x (P₁ ⋀ P₂),
  begin
    cases x_free_in_and,
    case free_in_vc.and₁ free_in_P₁ {
      show free_in_vc x P₁ ∨ free_in_vc x P₂, from or.inl free_in_P₁
    },
    case free_in_vc.and₂ free_in_P₂ {
      show free_in_vc x P₁ ∨ free_in_vc x P₂, from or.inr free_in_P₂
    }
  end

lemma free_in_vc.or.inv {P₁ P₂: vc} {x: var}: free_in_vc x (P₁ ⋁ P₂) → free_in_vc x P₁ ∨ free_in_vc x P₂ :=
  assume x_free_in_or: free_in_vc x (P₁ ⋁ P₂),
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

lemma call_history_closed (H: history): closed (calls_to_prop H) :=
  begin
    intro x,
    induction H with H₁ f y R S e H₂ σ v ih₁ ih₂,

    show ¬free_in_prop x (calls_to_prop history.empty), from (
      assume x_free: free_in_prop x (calls_to_prop history.empty),
      have calls_to_prop history.empty = value.true, from rfl,
      have x_free_in_true: free_in_prop x value.true, from this ▸ x_free,
      show «false», by begin
        cases x_free_in_true,
        case free_in_prop.term x_free_in_term {
          cases x_free_in_term
        }
      end
    ),

    show ¬free_in_prop x (calls_to_prop (H₁ · call f y R S e H₂ σ v)), from (
      assume x_free: free_in_prop x (calls_to_prop (H₁ · call f y R S e H₂ σ v)),
      have calls_to_prop (H₁ · call f y R S e H₂ σ v) =
        (calls_to_prop H₁ ⋀ prop.call (value.func f y R S e H₂ σ) v), by unfold calls_to_prop,
      have x_free_in_prop: free_in_prop x (calls_to_prop H₁ ⋀
        prop.call (value.func f y R S e H₂ σ) v), from this ▸ x_free,
      have x_not_free_in_v: ¬ free_in_term x v, from (
        assume x_free_in_v: free_in_term x v,
        show «false», by cases x_free_in_v
      ),
      have x_not_free_in_f: ¬ free_in_term x (value.func f y R S e H₂ σ), from (
        assume x_free_in_f: free_in_term x (value.func f y R S e H₂ σ),
        show «false», by cases x_free_in_f
      ),
      have
        free_in_prop x (calls_to_prop H₁) ∨
        free_in_prop x (prop.call (value.func f y R S e H₂ σ) v),
      from (free_in_prop.and.inv x_free_in_prop),
      or.elim this ih₁ (
        assume x_free_in_call: free_in_prop x (prop.call (value.func f y R S e H₂ σ) v),
        show «false», by begin
          cases x_free_in_call,
          case free_in_prop.call₁ x_free_in_f {
            show «false», from x_not_free_in_f x_free_in_f
          },
          case free_in_prop.call₂ x_free_in_v {
            show «false», from x_not_free_in_v x_free_in_v
          }
        end
      )
    )
  end

lemma env.contains.inv {σ: env} {x y: var} {v: value}: x ∈ (σ[y↦v]) → (x = y ∨ x ∈ σ) :=
  assume x_in: x ∈ (σ[y↦v]),
  show x = y ∨ x ∈ σ, by { cases x_in, left, refl, right, from a }

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
  induction σ with σ' y v' ih,
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
          have h6: (option.is_none (σ'.apply x) = tt), from option.is_none.inv.mp h4,
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
            have : ((option.is_some (σ'.apply x)):Prop), from option.some_iff_not_none.mpr h19,
            have : ∃v, (σ'.apply x) = some v, from option.is_some_iff_exists.mp this,
            cases this with v h20,
            have : ((if x = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = σ'.apply x),
            by { simp[h], simp[h19] },
            show (∃v, (σ'[x↦v']) x = some v), from exists.intro v (eq.trans (eq.trans h17 this) h20)
          end
        },
        case env.contains.rest h27 {
          have : (∃v, σ'.apply x = some v), from ih.right.mpr h27,
          cases this with v h28,
          have : ¬ (option.is_none (σ'.apply x)),
          from option.some_iff_not_none.mp (option.is_some_iff_exists.mpr (exists.intro v h28)),
          have : ((if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = σ'.apply x),
          by simp[this],
          show (∃v, (σ'[y↦v']) x = some v), from exists.intro v (eq.trans (eq.trans h17 this) h28)
        }
      end
    end
  end
end

instance {σ: env} {x: var} : decidable (env.contains σ x) :=
  let r := env.apply σ x in
  have h: r = env.apply σ x, from rfl,
  @option.rec_on value (λa, (r = a) → decidable (env.contains σ x)) r
  (
    assume : r = none,
    have env.apply σ x = none, from eq.trans h this,
    have ¬ (x ∈ σ), from env.contains_apply_equiv.left.mp this,
    is_false this
  ) (
    assume v: value,
    assume : r = some v,
    have env.apply σ x = some v, from eq.trans h this,
    have ∃v, env.apply σ x = some v, from exists.intro v this,
    have x ∈ σ, from env.contains_apply_equiv.right.mp this,
    is_true this
  ) rfl

lemma free_in_termctx.hole.inv {x: var} {t: term}:
      x ∈ FV (• t) → x ∈ FV t :=
  assume x_free_in_t: x ∈ FV (• t),
  have (termctx.apply • t) = t, by unfold termctx.apply,
  show x ∈ FV t, from this ▸ x_free_in_t

lemma free_in_termctx.binop.inv {x: var} {op: binop} {t₁ t₂: termctx} {t': term}:
      x ∈ FV ((termctx.binop op t₁ t₂) t') → x ∈ FV (t₁ t') ∨ x ∈ FV (t₂ t') :=
  assume x_free_in_t: x ∈ FV ((termctx.binop op t₁ t₂) t'),
  have (termctx.apply (termctx.binop op t₁ t₂) t') = term.binop op (t₁.apply t') (t₂.apply t'),
  by unfold termctx.apply,
  have x ∈ FV (term.binop op (t₁.apply t') (t₂.apply t')), from this ▸ x_free_in_t,
  show x ∈ FV (t₁ t') ∨ x ∈ FV (t₂ t'), from free_in_term.binop.inv this

lemma free_in_termctx.term.inv {x: var} {t t': term}:
      x ∈ FV (t.to_termctx t') → x ∈ FV t :=
  assume x_free_in_t: x ∈ FV (t.to_termctx t'),
  begin
    induction t with v y unop t₁ ih₁ binop t₂ t₃ ih₂ ih₃ t₄ t₅ ih₄ ih₅,

    show x ∈ FV (term.value v), from (
      have term.to_termctx (term.value v) = (termctx.value v), by unfold term.to_termctx,
      have h: x ∈ FV ((termctx.value v) t'), from this ▸ x_free_in_t,
      have termctx.apply (termctx.value v) t' = (term.value v), by unfold termctx.apply,
      show x ∈ FV (term.value v), from this.symm ▸ h
    ),

    show x ∈ FV (term.var y), from (
      have term.to_termctx (term.var y) = termctx.var y, by unfold term.to_termctx,
      have h: x ∈ FV ((termctx.var y) t'), from this ▸ x_free_in_t,
      have termctx.apply (termctx.var y) t' = term.var y, by unfold termctx.apply,
      show x ∈ FV (term.var y), from this.symm ▸ h
    ),

    show x ∈ FV (term.unop unop t₁), from (
      have term.to_termctx (term.unop unop t₁) = termctx.unop unop t₁.to_termctx, by unfold term.to_termctx,
      have h: x ∈ FV ((termctx.unop unop t₁.to_termctx) t'), from this ▸ x_free_in_t,
      have termctx.apply (termctx.unop unop t₁.to_termctx) t' = term.unop unop (t₁.to_termctx.apply t'),
      by unfold termctx.apply,
      have x ∈ FV (term.unop unop (t₁.to_termctx.apply t')), from this ▸ h,
      have x ∈ FV (t₁.to_termctx.apply t'), from free_in_term.unop.inv this,
      have x ∈ FV t₁, from ih₁ this,
      show x ∈ FV (term.unop unop t₁), from free_in_term.unop this
    ),

    show x ∈ FV (term.binop binop t₂ t₃), from (
      have term.to_termctx (term.binop binop t₂ t₃) = termctx.binop binop t₂.to_termctx t₃.to_termctx,
      by unfold term.to_termctx,
      have h: x ∈ FV ((termctx.binop binop t₂.to_termctx t₃.to_termctx) t'), from this ▸ x_free_in_t,
      have termctx.apply (termctx.binop binop t₂.to_termctx t₃.to_termctx) t'
         = term.binop binop (t₂.to_termctx.apply t') (t₃.to_termctx.apply t'),
      by unfold termctx.apply,
      have x ∈ FV (term.binop binop (t₂.to_termctx.apply t') (t₃.to_termctx.apply t')), from this ▸ h,
      have x ∈ FV (t₂.to_termctx.apply t') ∨ x ∈ FV (t₃.to_termctx.apply t'), from free_in_term.binop.inv this,
      or.elim this (
        assume : x ∈ FV (t₂.to_termctx.apply t'),
        have x ∈ FV t₂, from ih₂ this,
        show x ∈ FV (term.binop binop t₂ t₃), from free_in_term.binop₁ this
      ) (
        assume : x ∈ FV (t₃.to_termctx.apply t'),
        have x ∈ FV t₃, from ih₃ this,
        show x ∈ FV (term.binop binop t₂ t₃), from free_in_term.binop₂ this
      )
    ),

    show x ∈ FV (term.app t₄ t₅), from (
      have term.to_termctx (term.app t₄ t₅) = termctx.app t₄.to_termctx t₅.to_termctx,
      by unfold term.to_termctx,
      have h: x ∈ FV ((termctx.app t₄.to_termctx t₅.to_termctx) t'), from this ▸ x_free_in_t,
      have termctx.apply (termctx.app t₄.to_termctx t₅.to_termctx) t'
         = term.app (t₄.to_termctx.apply t') (t₅.to_termctx.apply t'),
      by unfold termctx.apply,
      have x ∈ FV (term.app (t₄.to_termctx.apply t') (t₅.to_termctx.apply t')), from this ▸ h,
      have x ∈ FV (t₄.to_termctx.apply t') ∨ x ∈ FV (t₅.to_termctx.apply t'), from free_in_term.app.inv this,
      or.elim this (
        assume : x ∈ FV (t₄.to_termctx.apply t'),
        have x ∈ FV t₄, from ih₄ this,
        show x ∈ FV (term.app t₄ t₅), from free_in_term.app₁ this
      ) (
        assume : x ∈ FV (t₅.to_termctx.apply t'),
        have x ∈ FV t₅, from ih₅ this,
        show x ∈ FV (term.app t₄ t₅), from free_in_term.app₂ this
      )
    )
  end

lemma free_in_propctx.prop.inv {x: var} {P: prop} {t': term}:
      x ∈ FV (P.to_propctx t') → x ∈ FV P :=
  assume x_free_in_P: x ∈ FV (P.to_propctx t'),
  begin
    induction P,
    case prop.term t { from (
      have prop.to_propctx (prop.term t) = (propctx.term t), by unfold prop.to_propctx,
      have h: x ∈ FV ((propctx.term t) t'), from this ▸ x_free_in_P,
      have propctx.apply (propctx.term t.to_termctx) t' = t.to_termctx t', by unfold propctx.apply,
      have x ∈ FV (prop.term (t.to_termctx t')), from this.symm ▸ h,
      have x ∈ FV (t.to_termctx t'), from free_in_prop.term.inv this,
      have x ∈ FV t, from free_in_termctx.term.inv this,
      show x ∈ FV (prop.term t), from free_in_prop.term this
    )},
    case prop.not P₁ ih { from (
      have prop.to_propctx (prop.not P₁) = (propctx.not P₁.to_propctx), by unfold prop.to_propctx,
      have h: x ∈ FV ((propctx.not P₁.to_propctx) t'), from this ▸ x_free_in_P,
      have propctx.apply (propctx.not P₁.to_propctx) t' = prop.not (P₁.to_propctx.apply t'), by unfold propctx.apply,
      have x ∈ FV (prop.not (P₁.to_propctx.apply t')), from this.symm ▸ h,
      have x ∈ FV (P₁.to_propctx.apply t'), from free_in_prop.not.inv this,
      have x ∈ FV P₁, from ih this,
      show x ∈ FV P₁.not, from free_in_prop.not this
    )},
    case prop.and P₁ P₂ ih₁ ih₂ { from (
      have prop.to_propctx (prop.and P₁ P₂) = (P₁.to_propctx ⋀ P₂.to_propctx), by unfold prop.to_propctx,
      have h: x ∈ FV ((P₁.to_propctx ⋀ P₂.to_propctx) t'), from this ▸ x_free_in_P,
      have propctx.apply (propctx.and P₁.to_propctx P₂.to_propctx) t'
         = (P₁.to_propctx.apply t' ⋀ P₂.to_propctx.apply t'), by unfold propctx.apply,
      have x ∈ FV ((P₁.to_propctx.apply t') ⋀ (P₂.to_propctx.apply t')), from this.symm ▸ h,
      have x ∈ FV (P₁.to_propctx.apply t') ∨ x ∈ FV (P₂.to_propctx.apply t'), from free_in_prop.and.inv this,
      or.elim this (
        assume : x ∈ FV (P₁.to_propctx.apply t'),
        have x ∈ FV P₁, from ih₁ this,
        show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₁ this
      ) (
        assume : x ∈ FV (P₂.to_propctx.apply t'),
        have x ∈ FV P₂, from ih₂ this,
        show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₂ this
      )
    )},
    case prop.or P₁ P₂ ih₁ ih₂ { from (
      have prop.to_propctx (prop.or P₁ P₂) = (P₁.to_propctx ⋁ P₂.to_propctx), by unfold prop.to_propctx,
      have h: x ∈ FV ((P₁.to_propctx ⋁ P₂.to_propctx) t'), from this ▸ x_free_in_P,
      have propctx.apply (propctx.or P₁.to_propctx P₂.to_propctx) t'
         = (P₁.to_propctx.apply t' ⋁ P₂.to_propctx.apply t'), by unfold propctx.apply,
      have x ∈ FV ((P₁.to_propctx.apply t') ⋁ (P₂.to_propctx.apply t')), from this.symm ▸ h,
      have x ∈ FV (P₁.to_propctx.apply t') ∨ x ∈ FV (P₂.to_propctx.apply t'), from free_in_prop.or.inv this,
      or.elim this (
        assume : x ∈ FV (P₁.to_propctx.apply t'),
        have x ∈ FV P₁, from ih₁ this,
        show x ∈ FV (P₁ ⋁ P₂), from free_in_prop.or₁ this
      ) (
        assume : x ∈ FV (P₂.to_propctx.apply t'),
        have x ∈ FV P₂, from ih₂ this,
        show x ∈ FV (P₁ ⋁ P₂), from free_in_prop.or₂ this
      )
    )},
    case prop.pre t₁ t₂ { from (
      have prop.to_propctx (prop.pre t₁ t₂) = propctx.pre t₁ t₂, by unfold prop.to_propctx,
      have h: x ∈ FV ((propctx.pre t₁ t₂) t'), from this ▸ x_free_in_P,
      have propctx.apply (propctx.pre t₁.to_termctx t₂.to_termctx) t' = prop.pre (t₁.to_termctx t') (t₂.to_termctx t'),
      by unfold propctx.apply,
      have x ∈ FV (prop.pre (t₁.to_termctx t') (t₂.to_termctx t')), from this.symm ▸ h,
      have x ∈ FV (t₁.to_termctx t') ∨ x ∈ FV (t₂.to_termctx t'), from free_in_prop.pre.inv this,
      or.elim this (
        assume : x ∈ FV (t₁.to_termctx t'),
        have x ∈ FV t₁, from free_in_termctx.term.inv this,
        show x ∈ FV (prop.pre t₁ t₂), from free_in_prop.pre₁ this
      ) (
        assume : x ∈ FV (t₂.to_termctx t'),
        have x ∈ FV t₂, from free_in_termctx.term.inv this,
        show x ∈ FV (prop.pre t₁ t₂), from free_in_prop.pre₂ this
      )
    )},
    case prop.pre₁ op t { from (
      have prop.to_propctx (prop.pre₁ op t) = propctx.pre₁ op t, by unfold prop.to_propctx,
      have h: x ∈ FV ((propctx.pre₁ op t) t'), from this ▸ x_free_in_P,
      have propctx.apply (propctx.pre₁ op t.to_termctx) t' = prop.pre₁ op (t.to_termctx t'),
      by unfold propctx.apply,
      have x ∈ FV (prop.pre₁ op (t.to_termctx t')), from this.symm ▸ h,
      have x ∈ FV (t.to_termctx t'), from free_in_prop.pre₁.inv this,
      have x ∈ FV t, from free_in_termctx.term.inv this,
      show x ∈ FV (prop.pre₁ op t), from free_in_prop.preop this
    )},
    case prop.pre₂ op t₁ t₂ { from (
      have prop.to_propctx (prop.pre₂ op t₁ t₂) = propctx.pre₂ op t₁ t₂, by unfold prop.to_propctx,
      have h: x ∈ FV ((propctx.pre₂ op t₁ t₂) t'), from this ▸ x_free_in_P,
      have propctx.apply (propctx.pre₂ op t₁.to_termctx t₂.to_termctx) t'
         = prop.pre₂ op (t₁.to_termctx t') (t₂.to_termctx t'),
      by unfold propctx.apply,
      have x ∈ FV (prop.pre₂ op (t₁.to_termctx t') (t₂.to_termctx t')), from this.symm ▸ h,
      have x ∈ FV (t₁.to_termctx t') ∨ x ∈ FV (t₂.to_termctx t'), from free_in_prop.pre₂.inv this,
      or.elim this (
        assume : x ∈ FV (t₁.to_termctx t'),
        have x ∈ FV t₁, from free_in_termctx.term.inv this,
        show x ∈ FV (prop.pre₂ op t₁ t₂), from free_in_prop.preop₁ this
      ) (
        assume : x ∈ FV (t₂.to_termctx t'),
        have x ∈ FV t₂, from free_in_termctx.term.inv this,
        show x ∈ FV (prop.pre₂ op t₁ t₂), from free_in_prop.preop₂ this
      )
    )},
    case prop.post t₁ t₂ { from (
      have prop.to_propctx (prop.post t₁ t₂) = propctx.post t₁ t₂, by unfold prop.to_propctx,
      have h: x ∈ FV ((propctx.post t₁ t₂) t'), from this ▸ x_free_in_P,
      have propctx.apply (propctx.post t₁.to_termctx t₂.to_termctx) t' = prop.post (t₁.to_termctx t') (t₂.to_termctx t'),
      by unfold propctx.apply,
      have x ∈ FV (prop.post (t₁.to_termctx t') (t₂.to_termctx t')), from this.symm ▸ h,
      have x ∈ FV (t₁.to_termctx t') ∨ x ∈ FV (t₂.to_termctx t'), from free_in_prop.post.inv this,
      or.elim this (
        assume : x ∈ FV (t₁.to_termctx t'),
        have x ∈ FV t₁, from free_in_termctx.term.inv this,
        show x ∈ FV (prop.post t₁ t₂), from free_in_prop.post₁ this
      ) (
        assume : x ∈ FV (t₂.to_termctx t'),
        have x ∈ FV t₂, from free_in_termctx.term.inv this,
        show x ∈ FV (prop.post t₁ t₂), from free_in_prop.post₂ this
      )
    )},
    case prop.call t₁ t₂ { from (
      have prop.to_propctx (prop.call t₁ t₂) = propctx.call t₁ t₂, by unfold prop.to_propctx,
      have h: x ∈ FV ((propctx.call t₁ t₂) t'), from this ▸ x_free_in_P,
      have propctx.apply (propctx.call t₁.to_termctx t₂.to_termctx) t' = prop.call (t₁.to_termctx t') (t₂.to_termctx t'),
      by unfold propctx.apply,
      have x ∈ FV (prop.call (t₁.to_termctx t') (t₂.to_termctx t')), from this.symm ▸ h,
      have x ∈ FV (t₁.to_termctx t') ∨ x ∈ FV (t₂.to_termctx t'), from free_in_prop.call.inv this,
      or.elim this (
        assume : x ∈ FV (t₁.to_termctx t'),
        have x ∈ FV t₁, from free_in_termctx.term.inv this,
        show x ∈ FV (prop.call t₁ t₂), from free_in_prop.call₁ this
      ) (
        assume : x ∈ FV (t₂.to_termctx t'),
        have x ∈ FV t₂, from free_in_termctx.term.inv this,
        show x ∈ FV (prop.call t₁ t₂), from free_in_prop.call₂ this
      )
    )},
    case prop.forallc y t P₁ ih { from (
      have prop.to_propctx (prop.forallc y t P₁) = propctx.forallc y t P₁.to_propctx, by unfold prop.to_propctx,
      have h: x ∈ FV ((propctx.forallc y t.to_termctx P₁.to_propctx) t'), from this ▸ x_free_in_P,
      have propctx.apply (propctx.forallc y t.to_termctx P₁.to_propctx) t'
         = prop.forallc y (t.to_termctx t') (P₁.to_propctx.apply t'), by unfold propctx.apply,
      have x ∈ FV (prop.forallc y (t.to_termctx t') (P₁.to_propctx.apply t')), from this.symm ▸ h,
      have x_neq_y: x ≠ y, from (free_in_prop.forallc.inv this).left,
      have x ∈ FV (t.to_termctx t') ∨ x ∈ FV (P₁.to_propctx.apply t'), from (free_in_prop.forallc.inv this).right,
      or.elim this (
        assume : x ∈ FV (t.to_termctx t'),
        have x ∈ FV t, from free_in_termctx.term.inv this,
        show x ∈ FV (prop.forallc y t P₁), from free_in_prop.forallc₁ x_neq_y this
      ) (
        assume : x ∈ FV (P₁.to_propctx.apply t'),
        have x ∈ FV P₁, from ih this,
        show x ∈ FV (prop.forallc y t P₁), from free_in_prop.forallc₂ x_neq_y this
      )
    )},
    case prop.exis y P₁ ih { from (
      have prop.to_propctx (prop.exis y P₁) = (propctx.exis y P₁.to_propctx), by unfold prop.to_propctx,
      have h: x ∈ FV ((propctx.exis y P₁.to_propctx) t'), from this ▸ x_free_in_P,
      have propctx.apply (propctx.exis y P₁.to_propctx) t' = prop.exis y (P₁.to_propctx.apply t'), by unfold propctx.apply,
      have x ∈ FV (prop.exis y (P₁.to_propctx.apply t')), from this.symm ▸ h,
      have x_neq_y: x ≠ y, from (free_in_prop.exis.inv this).left,
      have x ∈ FV (P₁.to_propctx.apply t'), from (free_in_prop.exis.inv this).right,
      have x ∈ FV P₁, from ih this,
      show x ∈ FV (prop.exis y P₁), from free_in_prop.exis x_neq_y this
    )}
  end

lemma free_in_propctx.term.inv {x: var} {t: termctx} {t': term}:
      x ∈ FV ((propctx.term t) t') → x ∈ FV (t t') :=
  assume x_free_in_t: x ∈ FV (propctx.apply (propctx.term t) t'),
  have (propctx.apply (propctx.term t) t') = t t', by unfold propctx.apply,
  have x ∈ FV (prop.term (t t')), from this ▸ x_free_in_t,
  show x ∈ FV (t t'), from free_in_prop.term.inv this

lemma free_in_propctx.not.inv {x: var} {Q: propctx} {t: term}:
      x ∈ FV (Q.not t) → x ∈ FV (Q t) :=
  assume x_free_in_Qn: x ∈ FV (Q.not t),
  have (propctx.apply (propctx.not Q) t) = prop.not (Q.apply t), by unfold propctx.apply,
  have x ∈ FV (prop.not (Q.apply t)), from this ▸ x_free_in_Qn,
  show x ∈ FV (Q t), from free_in_prop.not.inv this

lemma free_in_propctx.and.inv {x: var} {Q₁ Q₂: propctx} {t: term}:
      x ∈ FV ((Q₁ ⋀ Q₂) t) → x ∈ FV (Q₁ t) ∨ x ∈ FV (Q₂ t) :=
  assume x_free_in_Q12: x ∈ FV ((Q₁ ⋀ Q₂) t),
  have (propctx.apply (propctx.and Q₁ Q₂) t) = (Q₁.apply t ⋀ Q₂.apply t), by unfold propctx.apply,
  have x ∈ FV (Q₁.apply t ⋀ Q₂.apply t), from this ▸ x_free_in_Q12,
  show x ∈ FV (Q₁ t) ∨ x ∈ FV (Q₂ t), from free_in_prop.and.inv this

lemma free_in_propctx.or.inv {x: var} {Q₁ Q₂: propctx} {t: term}:
      x ∈ FV ((Q₁ ⋁ Q₂) t) → x ∈ FV (Q₁ t) ∨ x ∈ FV (Q₂ t) :=
  assume x_free_in_Q12: x ∈ FV ((Q₁ ⋁ Q₂) t),
  have (propctx.apply (propctx.or Q₁ Q₂) t) = (Q₁.apply t ⋁ Q₂.apply t), by unfold propctx.apply,
  have x ∈ FV (Q₁.apply t ⋁ Q₂.apply t), from this ▸ x_free_in_Q12,
  show x ∈ FV (Q₁ t) ∨ x ∈ FV (Q₂ t), from free_in_prop.or.inv this

lemma free_in_propctx.implies.inv {x: var} {Q₁ Q₂: propctx} {t: term}:
      x ∈ FV ((propctx.implies Q₁ Q₂) t) → x ∈ FV (Q₁ t) ∨ x ∈ FV (Q₂ t) :=
  assume : x ∈ FV ((propctx.implies Q₁ Q₂) t),
  have x ∈ FV (Q₁.not t) ∨ x ∈ FV (Q₂ t), from free_in_propctx.or.inv this,
  or.elim this (
    assume : x ∈ FV (Q₁.not t),
    have x ∈ FV (Q₁ t), from free_in_propctx.not.inv this,
    show x ∈ FV (Q₁ t) ∨ x ∈ FV (Q₂ t), from or.inl this
  ) (
    assume : x ∈ FV (Q₂ t),
    show x ∈ FV (Q₁ t) ∨ x ∈ FV (Q₂ t), from or.inr this
  )

lemma free_in_propctx.exis.inv {x fx: var} {Q: propctx} {t: term}:
      x ∈ FV ((propctx.exis fx Q) t) → x ≠ fx ∧ x ∈ FV (Q t) :=
  assume x_free_in_eQt: x ∈ FV ((propctx.exis fx Q) t),
  have (propctx.apply (propctx.exis fx Q) t) = prop.exis fx (Q.apply t), by unfold propctx.apply,
  have x ∈ FV (prop.exis fx (Q.apply t)), from this ▸ x_free_in_eQt,
  show x ≠ fx ∧ x ∈ FV (Q t), from free_in_prop.exis.inv this

lemma free_in_prop.and_elim {P₁ P₂: prop}:
      FV (P₁ ⋀ P₂) = FV P₁ ∪ FV P₂ :=
  set.eq_of_subset_of_subset (
    assume x: var,
    assume : x ∈ FV (P₁ ⋀ P₂),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P₁,
      show x ∈ FV P₁ ∪ FV P₂, from set.mem_union_left (FV P₂) this
    ) (
      assume : x ∈ FV P₂,
      show x ∈ FV P₁ ∪ FV P₂, from set.mem_union_right (FV P₁) this
    )
  ) (
    assume x: var,
    assume : x ∈ FV P₁ ∪ FV P₂,
    or.elim (set.mem_or_mem_of_mem_union this) (
      assume : x ∈ FV P₁,
      show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₁ this
    ) (
      assume : x ∈ FV P₂,
      show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₂ this
    )
  )

lemma free_in_prop.and_comm {P₁ P₂ P₃: prop}:
      FV (P₁ ⋀ P₂ ⋀ P₃) = FV ((P₁ ⋀ P₂) ⋀ P₃) :=
  set.eq_of_subset_of_subset (
    assume x: var,
    assume : x ∈ FV (P₁ ⋀ P₂ ⋀ P₃),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P₁,
      have x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₁ this,
      show x ∈ FV ((P₁ ⋀ P₂) ⋀ P₃), from free_in_prop.and₁ this
    ) (
      assume : x ∈ FV (P₂ ⋀ P₃),
      or.elim (free_in_prop.and.inv this) (
        assume : x ∈ FV P₂,
        have x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₂ this,
        show x ∈ FV ((P₁ ⋀ P₂) ⋀ P₃), from free_in_prop.and₁ this
      ) (
        assume : x ∈ FV P₃,
        show x ∈ FV ((P₁ ⋀ P₂) ⋀ P₃), from free_in_prop.and₂ this
      )
    )
  ) (
    assume x: var,
    assume : x ∈ FV ((P₁ ⋀ P₂) ⋀ P₃),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV (P₁ ⋀ P₂),
      or.elim (free_in_prop.and.inv this) (
        assume : x ∈ FV P₁,
        show x ∈ FV (P₁ ⋀ P₂ ⋀ P₃), from free_in_prop.and₁ this
      ) (
        assume : x ∈ FV P₂,
        have x ∈ FV (P₂ ⋀ P₃), from free_in_prop.and₁ this,
        show x ∈ FV (P₁ ⋀ P₂ ⋀ P₃), from free_in_prop.and₂ this
      )
    ) (
      assume : x ∈ FV P₃,
      have x ∈ FV (P₂ ⋀ P₃), from free_in_prop.and₂ this,
      show x ∈ FV (P₁ ⋀ P₂ ⋀ P₃), from free_in_prop.and₂ this
    )
  )

lemma free_in_prop.and_symm {P₁ P₂: prop}:
      FV (P₁ ⋀ P₂) = FV (P₂ ⋀ P₁) :=
  set.eq_of_subset_of_subset (
    assume x: var,
    assume : x ∈ FV (P₁ ⋀ P₂),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P₁,
      show x ∈ FV (P₂ ⋀ P₁), from free_in_prop.and₂ this
    ) (
      assume : x ∈ FV P₂,
      show x ∈ FV (P₂ ⋀ P₁), from free_in_prop.and₁ this
    )
  ) (
    assume x: var,
    assume : x ∈ FV (P₂ ⋀ P₁),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P₂,
      show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₂ this
    ) (
      assume : x ∈ FV P₁,
      show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₁ this
    )
  )

lemma prop.closed.and {P Q: prop}: closed P → closed Q → closed (P ⋀ Q) :=
  assume P_closed: closed P,
  assume Q_closed: closed Q,
  show closed (P ⋀ Q), from (
    assume x: var,
    assume : x ∈ FV (P ⋀ Q),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P,
      show «false», from P_closed x this
    ) (
      assume : x ∈ FV Q,
      show «false», from Q_closed x this
    )
  )

lemma prop.closed.or {P Q: prop}: closed P → closed Q → closed (P ⋁ Q) :=
  assume P_closed: closed P,
  assume Q_closed: closed Q,
  show closed (P ⋁ Q), from (
    assume x: var,
    assume : x ∈ FV (P ⋁ Q),
    or.elim (free_in_prop.or.inv this) (
      assume : x ∈ FV P,
      show «false», from P_closed x this
    ) (
      assume : x ∈ FV Q,
      show «false», from Q_closed x this
    )
  )

lemma prop.closed.not {P: prop}: closed P → closed P.not :=
  assume P_closed: closed P,
  show closed P.not, from (
    assume x: var,
    assume : x ∈ FV P.not,
    have x ∈ FV P, from free_in_prop.not.inv this,
    show «false», from P_closed x this
  )

lemma prop.closed.implies {P Q: prop}: closed P → closed Q → closed (prop.implies P Q) :=
  assume P_closed: closed P,
  have P_not_closed: closed P.not, from prop.closed.not P_closed,
  assume Q_closed: closed Q,
  show closed (P.not ⋁ Q), from prop.closed.or P_not_closed Q_closed

lemma prop.closed.and.inv {P Q: prop}: closed (P ⋀ Q) → (closed P ∧ closed Q) :=
  assume P_and_Q_closed: closed (P ⋀ Q),
  have P_closed: closed P, from (
    assume x: var,
    assume : x ∈ FV P,
    have x ∈ FV (P ⋀ Q), from free_in_prop.and₁ this,
    show «false», from P_and_Q_closed x this
  ),
  have Q_closed: closed Q, from (
    assume x: var,
    assume : x ∈ FV Q,
    have x ∈ FV (P ⋀ Q), from free_in_prop.and₂ this,
    show «false», from P_and_Q_closed x this
  ),
  ⟨P_closed, Q_closed⟩

lemma prop.closed.or.inv {P Q: prop}: closed (P ⋁ Q) → (closed P ∧ closed Q) :=
  assume P_or_Q_closed: closed (P ⋁ Q),
  have P_closed: closed P, from (
    assume x: var,
    assume : x ∈ FV P,
    have x ∈ FV (P ⋁ Q), from free_in_prop.or₁ this,
    show «false», from P_or_Q_closed x this
  ),
  have Q_closed: closed Q, from (
    assume x: var,
    assume : x ∈ FV Q,
    have x ∈ FV (P ⋁ Q), from free_in_prop.or₂ this,
    show «false», from P_or_Q_closed x this
  ),
  ⟨P_closed, Q_closed⟩

lemma prop.closed.not.inv {P: prop}: closed P.not → closed P :=
  assume P_not_closed: closed P.not,
  show closed P, from (
    assume x: var,
    assume : x ∈ FV P,
    have x ∈ FV P.not, from free_in_prop.not this,
    show «false», from P_not_closed x this
  )

lemma prop.closed.implies.inv {P Q: prop}: closed (prop.implies P Q) → closed P ∧ closed Q :=
  assume P_not_or_Q_closed: closed (P.not ⋁ Q),
  have P_not_closed: closed P.not, from (prop.closed.or.inv P_not_or_Q_closed).left,
  have P_closed: closed P, from prop.closed.not.inv P_not_closed,
  have Q_closed: closed Q, from (prop.closed.or.inv P_not_or_Q_closed).right,
  ⟨P_closed, Q_closed⟩

lemma vc.closed.and {P Q: vc}: closed P → closed Q → closed (P ⋀ Q) :=
  assume P_closed: closed P,
  assume Q_closed: closed Q,
  show closed (P ⋀ Q), from (
    assume x: var,
    assume : x ∈ FV (P ⋀ Q),
    or.elim (free_in_vc.and.inv this) (
      assume : x ∈ FV P,
      show «false», from P_closed x this
    ) (
      assume : x ∈ FV Q,
      show «false», from Q_closed x this
    )
  )

lemma vc.closed.or {P Q: vc}: closed P → closed Q → closed (P ⋁ Q) :=
  assume P_closed: closed P,
  assume Q_closed: closed Q,
  show closed (P ⋁ Q), from (
    assume x: var,
    assume : x ∈ FV (P ⋁ Q),
    or.elim (free_in_vc.or.inv this) (
      assume : x ∈ FV P,
      show «false», from P_closed x this
    ) (
      assume : x ∈ FV Q,
      show «false», from Q_closed x this
    )
  )

lemma vc.closed.not {P: vc}: closed P → closed P.not :=
  assume P_closed: closed P,
  show closed P.not, from (
    assume x: var,
    assume : x ∈ FV P.not,
    have x ∈ FV P, from free_in_vc.not.inv this,
    show «false», from P_closed x this
  )

lemma vc.closed.implies {P Q: vc}: closed P → closed Q → closed (vc.implies P Q) :=
  assume P_closed: closed P,
  have P_not_closed: closed P.not, from vc.closed.not P_closed,
  assume Q_closed: closed Q,
  show closed (P.not ⋁ Q), from vc.closed.or P_not_closed Q_closed

lemma vc.closed.term.inv {t: term}: closed (vc.term t) → closed t :=
  assume h: closed (vc.term t),
  assume x: var,
  assume : x ∈ FV t,
  have x ∈ FV (vc.term t), from free_in_vc.term this,
  show «false», from h x this

lemma vc.closed.and.inv {P Q: vc}: closed (P ⋀ Q) → (closed P ∧ closed Q) :=
  assume P_and_Q_closed: closed (P ⋀ Q),
  have P_closed: closed P, from (
    assume x: var,
    assume : x ∈ FV P,
    have x ∈ FV (P ⋀ Q), from free_in_vc.and₁ this,
    show «false», from P_and_Q_closed x this
  ),
  have Q_closed: closed Q, from (
    assume x: var,
    assume : x ∈ FV Q,
    have x ∈ FV (P ⋀ Q), from free_in_vc.and₂ this,
    show «false», from P_and_Q_closed x this
  ),
  ⟨P_closed, Q_closed⟩

lemma vc.closed.or.inv {P Q: vc}: closed (P ⋁ Q) → (closed P ∧ closed Q) :=
  assume P_or_Q_closed: closed (P ⋁ Q),
  have P_closed: closed P, from (
    assume x: var,
    assume : x ∈ FV P,
    have x ∈ FV (P ⋁ Q), from free_in_vc.or₁ this,
    show «false», from P_or_Q_closed x this
  ),
  have Q_closed: closed Q, from (
    assume x: var,
    assume : x ∈ FV Q,
    have x ∈ FV (P ⋁ Q), from free_in_vc.or₂ this,
    show «false», from P_or_Q_closed x this
  ),
  ⟨P_closed, Q_closed⟩

lemma vc.closed.not.inv {P: vc}: closed P.not → closed P :=
  assume P_not_closed: closed P.not,
  show closed P, from (
    assume x: var,
    assume : x ∈ FV P,
    have x ∈ FV P.not, from free_in_vc.not this,
    show «false», from P_not_closed x this
  )

lemma vc.closed.implies.inv {P Q: vc}: closed (vc.implies P Q) → closed P ∧ closed Q :=
  assume P_not_or_Q_closed: closed (P.not ⋁ Q),
  have P_not_closed: closed P.not, from (vc.closed.or.inv P_not_or_Q_closed).left,
  have P_closed: closed P, from vc.closed.not.inv P_not_closed,
  have Q_closed: closed Q, from (vc.closed.or.inv P_not_or_Q_closed).right,
  ⟨P_closed, Q_closed⟩

lemma same_free_and_left {P P' Q: prop}: FV P' = FV P → (FV (P' ⋀ Q) = FV (P ⋀ Q)) :=
  assume free_P'_P: FV P' = FV P,
  set.eq_of_subset_of_subset (
    assume x,
    assume : x ∈ FV (P' ⋀ Q),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P',
      have x ∈ FV P, from free_P'_P ▸ this,
      show x ∈ FV (P ⋀ Q), from free_in_prop.and₁ this
    ) (
      assume : x ∈ FV Q,
      show x ∈ FV (P ⋀ Q), from free_in_prop.and₂ this
    )
  ) (
    assume x,
    assume : x ∈ FV (P ⋀ Q),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P,
      have x ∈ FV P', from free_P'_P.symm ▸ this,
      show x ∈ FV (P' ⋀ Q), from free_in_prop.and₁ this
    ) (
      assume : x ∈ FV Q,
      show x ∈ FV (P' ⋀ Q), from free_in_prop.and₂ this
    )
  )

lemma free_in_left {P Q: prop}: FV P ⊆ FV (P ⋀ Q) :=
  assume x: var,
  assume : x ∈ FV P,
  show x ∈ FV (P ⋀ Q), from free_in_prop.and₁ this