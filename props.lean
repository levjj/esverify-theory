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

-- helper lemmas

lemma free_in_term.freevar.inv {x y: var}: free_in_term x y → (x = y) :=
  assume x_free_in_y: free_in_term x y,
  begin
    cases x_free_in_y,
    case free_in_term.freevar a b c { exact rfl }
  end

lemma free_in_prop.and.inv {P₁ P₂: prop} {x: var}: free_in_prop x (P₁ & P₂) → free_in_prop x P₁ ∨ free_in_prop x P₂ :=
  assume x_free_in_and: free_in_prop x (P₁ & P₂),
  begin
    cases x_free_in_and,
    case free_in_prop.and₁ free_in_P₁ {
      show free_in_prop x P₁ ∨ free_in_prop x P₂, from or.inl free_in_P₁
    },
    case free_in_prop.and₂ free_in_P₂ {
      show free_in_prop x P₁ ∨ free_in_prop x P₂, from or.inr free_in_P₂
    }
  end

lemma call_history_closed (H: list call) (x: var): ¬ free_in_prop x (calls_to_prop H) :=
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
  ( -- <call> :: rest
    assume ⟨f, x', R, S, e, σ, vₓ, v⟩,
    assume rest: list call,
    assume ih: ¬ free_in_prop x (calls_to_prop rest),
    assume x_free: free_in_prop x (calls_to_prop (⟨f, x', R, S, e, σ, vₓ, v⟩ :: rest)),
    have calls_to_prop (⟨f, x', R, S, e, σ, vₓ, v⟩ :: rest) =
      (prop.call (value.func f x' R S e σ) vₓ &
      prop.post (value.func f x' R S e σ) vₓ &
      term.app (value.func f x' R S e σ) vₓ ≡ v &
      calls_to_prop rest), from rfl,
    have x_free_in_prop: free_in_prop x (
      prop.call (value.func f x' R S e σ) vₓ &
      prop.post (value.func f x' R S e σ) vₓ &
      term.app (value.func f x' R S e σ) vₓ ≡ v &
      calls_to_prop rest), from this ▸ x_free,
    have x_not_free_in_v: ¬ free_in_term x v, from (
      assume x_free_in_v: free_in_term x v,
      show «false», by cases x_free_in_v
    ),
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
      free_in_prop x (prop.call (value.func f x' R S e σ) vₓ &
        prop.post (value.func f x' R S e σ) vₓ &
        term.app (value.func f x' R S e σ) vₓ ≡ v),
    from (free_in_prop.and.inv x_free_in_prop).symm,
    or.elim this ih (
      assume x_free_in_call: free_in_prop x (
        prop.call (value.func f x' R S e σ) vₓ &
        prop.post (value.func f x' R S e σ) vₓ &
        term.app (value.func f x' R S e σ) vₓ ≡ v),
      have
        free_in_prop x (term.app (value.func f x' R S e σ) vₓ ≡ v) ∨
        free_in_prop x (prop.call (value.func f x' R S e σ) vₓ &
          prop.post (value.func f x' R S e σ) vₓ),
      from (free_in_prop.and.inv x_free_in_call).symm,
      or.elim this (
        assume x_free_in_eq_app: free_in_prop x (term.app (value.func f x' R S e σ) vₓ ≡ v),
        show «false», by begin
          cases x_free_in_eq_app,
          case free_in_prop.term x_free_in_term {
            cases x_free_in_term,
            case free_in_term.binop₁ x_free_in_app {
              cases x_free_in_app,
              case free_in_term.app₁ x_free_in_f {
                show «false», from x_not_free_in_f x_free_in_f
              },
              case free_in_term.app₂ x_free_in_vₓ {
                show «false», from x_not_free_in_vₓ x_free_in_vₓ
              }
            },
            case free_in_term.binop₂ x_free_in_v {
              show «false», from x_not_free_in_v x_free_in_v
            }
          }
        end
      )
      (
        assume x_free_in_call_or_func: free_in_prop x (
          prop.call (value.func f x' R S e σ) vₓ &
          prop.post (value.func f x' R S e σ) vₓ),
        have
          free_in_prop x (prop.call (value.func f x' R S e σ) vₓ) ∨
          free_in_prop x (prop.post (value.func f x' R S e σ) vₓ),
        from free_in_prop.and.inv x_free_in_call_or_func,
        or.elim this
        (
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
        (
          assume x_free_in_post: free_in_prop x (prop.post (value.func f x' R S e σ) vₓ),
          show «false», by begin
            cases x_free_in_post,
            case free_in_prop.post₁ x_free_in_f {
              show «false», from x_not_free_in_f x_free_in_f
            },
            case free_in_prop.post₂ x_free_in_vₓ {
              show «false», from x_not_free_in_vₓ x_free_in_vₓ
            }
          end
        )
      )
    )
  )

-- validity

inductive valid : prop → Prop
notation `⟪` p `⟫`: 100 := valid p
| to_prop {p: prop}: valid p

notation `⟪` p `⟫`: 100 := valid p
