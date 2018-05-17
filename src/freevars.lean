-- lemmas about free variables and environments

import .definitions3

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

lemma free_in_prop.call.inv {t: term} {x: var}:
      free_in_prop x (prop.call t) → free_in_term x t :=
  assume x_free_in_call: free_in_prop x (prop.call t),
  begin
    cases x_free_in_call,
    case free_in_prop.call free_in_t { from free_in_t }
  end

lemma free_in_prop.forallc.inv {P: prop} {x fx: var}:
      free_in_prop x (prop.forallc fx P) → (x ≠ fx) ∧ free_in_prop x P :=
  assume x_free_in_forallc: free_in_prop x (prop.forallc fx P),
  begin
    cases x_free_in_forallc,
    case free_in_prop.forallc x_neq_fx free_in_P {
      from ⟨x_neq_fx, free_in_P⟩ 
    }
  end

lemma free_in_prop.forallc.same.inv {P: prop} {x: var}: ¬ free_in_prop x (prop.forallc x P) :=
  assume x_free: free_in_prop x (prop.forallc x P),
  begin
    cases x_free,
    case free_in_prop.forallc x_neq_y free_in_P {
      contradiction
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
                      (prop.forallc y (prop.implies P₁ (prop.pre t y) ⋀
                                       prop.implies (prop.post t y) P₂))),
  from this,
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
      case free_in_prop.forallc x_neq_y x_free_in_forallp {
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
    case prop.call t { from (
      have prop.to_propctx (prop.call t) = propctx.call t, by unfold prop.to_propctx,
      have h: x ∈ FV ((propctx.call t) t'), from this ▸ x_free_in_P,
      have propctx.apply (propctx.call t.to_termctx) t' = prop.call (t.to_termctx t'),
      by unfold propctx.apply,
      have x ∈ FV (prop.call (t.to_termctx t')), from this.symm ▸ h,
      have x ∈ FV (t.to_termctx t'), from free_in_prop.call.inv this,
      have x ∈ FV t, from free_in_termctx.term.inv this,
      show x ∈ FV (prop.call t), from free_in_prop.call this
    )},
    case prop.forallc y P₁ ih { from (
      have prop.to_propctx (prop.forallc y P₁) = propctx.forallc y P₁.to_propctx, by unfold prop.to_propctx,
      have h: x ∈ FV ((propctx.forallc y P₁.to_propctx) t'), from this ▸ x_free_in_P,
      have propctx.apply (propctx.forallc y P₁.to_propctx) t'
         = prop.forallc y (P₁.to_propctx.apply t'), by unfold propctx.apply,
      have x ∈ FV (prop.forallc y (P₁.to_propctx.apply t')), from this.symm ▸ h,
      have x_neq_y: x ≠ y, from (free_in_prop.forallc.inv this).left,
      have x ∈ FV (P₁.to_propctx.apply t'), from (free_in_prop.forallc.inv this).right,
      have x ∈ FV P₁, from ih this,
      show x ∈ FV (prop.forallc y P₁), from free_in_prop.forallc x_neq_y this
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

lemma free_in_prop.and_left_subset {P₁ P₂: prop}: FV P₁ ⊆ FV (P₁ ⋀ P₂) :=
  assume x: var,
  assume : x ∈ FV P₁,
  show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₁ this

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

lemma free_in_prop.and_assoc {P₁ P₂ P₃: prop}:
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

lemma free_in_prop.same_left {P₁ P₂ P₃: prop}:
      (FV P₂ = FV P₃) → (FV (P₁ ⋀ P₂) = FV (P₁ ⋀ P₃)) :=
  assume h1: FV P₂ = FV P₃,
  set.eq_of_subset_of_subset (
    assume x: var,
    assume : x ∈ FV (P₁ ⋀ P₂),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P₁,
      show x ∈ FV (P₁ ⋀ P₃), from free_in_prop.and₁ this
    ) (
      assume : x ∈ FV P₂,
      have x ∈ FV P₃, from h1 ▸ this,
      show x ∈ FV (P₁ ⋀ P₃), from free_in_prop.and₂ this
    )
  ) (
    assume x: var,
    assume : x ∈ FV (P₁ ⋀ P₃),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P₁,
      show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₁ this
    ) (
      assume : x ∈ FV P₃,
      have x ∈ FV P₂, from h1.symm ▸ this,
      show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₂ this
    )
  )

lemma free_in_prop.same_right {P₁ P₂ P₃: prop}:
      (FV P₁ = FV P₂) → (FV (P₁ ⋀ P₃) = FV (P₂ ⋀ P₃)) :=
  assume h1: FV P₁ = FV P₂,
  set.eq_of_subset_of_subset (
    assume x: var,
    assume : x ∈ FV (P₁ ⋀ P₃),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P₁,
      have x ∈ FV P₂, from h1 ▸ this,
      show x ∈ FV (P₂ ⋀ P₃), from free_in_prop.and₁ this
    ) (
      assume : x ∈ FV P₃,
      show x ∈ FV (P₂ ⋀ P₃), from free_in_prop.and₂ this
    )
  ) (
    assume x: var,
    assume : x ∈ FV (P₂ ⋀ P₃),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P₂,
      have x ∈ FV P₁, from h1.symm ▸ this,
      show x ∈ FV (P₁ ⋀ P₃), from free_in_prop.and₁ this
    ) (
      assume : x ∈ FV P₃,
      show x ∈ FV (P₁ ⋀ P₃), from free_in_prop.and₂ this
    )
  )

lemma free_in_prop.shuffle {P Q R S: prop}:
      FV (P ⋀ Q ⋀ R ⋀ S) = FV ((P ⋀ Q ⋀ R) ⋀ S):=
  have h1: FV (P ⋀ Q ⋀ R ⋀ S) = FV ((Q ⋀ R ⋀ S) ⋀ P), from free_in_prop.and_symm,
  have h2: FV ((Q ⋀ R ⋀ S) ⋀ P) = FV (((Q ⋀ R) ⋀ S) ⋀ P),
  from free_in_prop.same_right free_in_prop.and_assoc,
  have h3: FV (((Q ⋀ R) ⋀ S) ⋀ P) = FV ((Q ⋀ R) ⋀ S ⋀ P), from free_in_prop.and_assoc.symm,
  have h4: FV ((Q ⋀ R) ⋀ S ⋀ P) = FV ((S ⋀ P) ⋀ Q ⋀ R), from free_in_prop.and_symm,
  have h5: FV ((S ⋀ P) ⋀ Q ⋀ R) = FV (S ⋀ P ⋀ Q ⋀ R), from free_in_prop.and_assoc.symm,
  have h6: FV (S ⋀ P ⋀ Q ⋀ R) = FV ((P ⋀ Q ⋀ R) ⋀ S), from free_in_prop.and_symm,
  show FV (P ⋀ Q ⋀ R ⋀ S) = FV ((P ⋀ Q ⋀ R) ⋀ S),
  from eq.trans h1 (eq.trans h2 (eq.trans h3 (eq.trans h4 (eq.trans h5 h6))))

lemma free_in_prop.sub_same_left {P₁ P₂ P₃: prop}:
      (FV P₂ ⊆ FV P₃) → (FV (P₁ ⋀ P₂) ⊆ FV (P₁ ⋀ P₃)) :=
  assume h1: FV P₂ ⊆ FV P₃,
  assume x: var,
  assume : x ∈ FV (P₁ ⋀ P₂),
  or.elim (free_in_prop.and.inv this) (
    assume : x ∈ FV P₁,
    show x ∈ FV (P₁ ⋀ P₃), from free_in_prop.and₁ this
  ) (
    assume : x ∈ FV P₂,
    have x ∈ FV P₃, from set.mem_of_subset_of_mem h1 this,
    show x ∈ FV (P₁ ⋀ P₃), from free_in_prop.and₂ this
  )

lemma free_in_prop.sub_same_right {P₁ P₂ P₃: prop}:
      (FV P₁ ⊆ FV P₂) → (FV (P₁ ⋀ P₃) ⊆ FV (P₂ ⋀ P₃)) :=
  assume h1: FV P₁ ⊆ FV P₂,
  assume x: var,
  assume : x ∈ FV (P₁ ⋀ P₃),
  or.elim (free_in_prop.and.inv this) (
    assume : x ∈ FV P₁,
    have x ∈ FV P₂, from set.mem_of_subset_of_mem h1 this,
    show x ∈ FV (P₂ ⋀ P₃), from free_in_prop.and₁ this
  ) (
    assume : x ∈ FV P₃,
    show x ∈ FV (P₂ ⋀ P₃), from free_in_prop.and₂ this
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

lemma free_in_prop_of_free_in_to_vc {P: prop}: FV P.to_vc ⊆ FV P :=
  begin
    assume x: var,
    assume x_free: x ∈ FV P.to_vc,
    induction P,
    case prop.term t {
      unfold prop.to_vc at x_free,
      apply free_in_prop.term,
      from free_in_vc.term.inv x_free
    },
    case prop.not P₁ ih {
      unfold prop.to_vc at x_free,
      apply free_in_prop.not,
      have h1, from free_in_vc.not.inv x_free,
      from ih h1
    },
    case prop.and P₁ P₂ P₁_ih P₂_ih {
      unfold prop.to_vc at x_free,
      cases (free_in_vc.and.inv x_free),

      apply free_in_prop.and₁,
      from P₁_ih a,

      apply free_in_prop.and₂,
      from P₂_ih a
    },
    case prop.or P₁ P₂ P₁_ih P₂_ih {
      unfold prop.to_vc at x_free,
      cases (free_in_vc.or.inv x_free),

      apply free_in_prop.or₁,
      from P₁_ih a,

      apply free_in_prop.or₂,
      from P₂_ih a
    },
    case prop.pre t₁ t₂ {
      unfold prop.to_vc at x_free,
      cases (free_in_vc.pre.inv x_free),

      apply free_in_prop.pre₁,
      from a,

      apply free_in_prop.pre₂,
      from a
    },
    case prop.pre₁ op t {
      unfold prop.to_vc at x_free,
      apply free_in_prop.preop,
      from free_in_vc.pre₁.inv x_free
    },
    case prop.pre₂ op t₁ t₂ {
      unfold prop.to_vc at x_free,
      cases (free_in_vc.pre₂.inv x_free),

      apply free_in_prop.preop₁,
      from a,

      apply free_in_prop.preop₂,
      from a
    },
    case prop.call t {
      unfold prop.to_vc at x_free,
      have h2, from free_in_vc.term.inv x_free,
      show x ∈ FV (prop.call t), from absurd h2 free_in_term.value.inv
    },
    case prop.post t₁ t₂ {
      unfold prop.to_vc at x_free,
      cases (free_in_vc.post.inv x_free),

      apply free_in_prop.post₁,
      from a,

      apply free_in_prop.post₂,
      from a
    },
    case prop.forallc y P₁ P₁_ih {
      unfold prop.to_vc at x_free,
      have h1, from free_in_vc.univ.inv x_free,
      apply free_in_prop.forallc,
      from h1.left,
      from P₁_ih h1.right
    },
    case prop.exis y P₁ P₁_ih {
      unfold prop.to_vc at x_free,
      have h1, from free_in_vc.not.inv x_free,
      have h2, from free_in_vc.univ.inv h1,
      apply free_in_prop.exis,
      from h2.left,
      have h3, from free_in_vc.not.inv h2.right,
      from P₁_ih h3
    }
  end

lemma free_in_prop_of_free_in_erased {P: prop}:
      FV P.erased_p ⊆ FV P ∧ FV P.erased_n ⊆ FV P :=
  begin
    induction P,

    case prop.term t {
      split,

      assume x: var,
      assume x_free: x ∈ FV (prop.term t).erased_p,
      unfold prop.erased_p at x_free,
      apply free_in_prop.term,
      from free_in_vc.term.inv x_free,

      assume x: var,
      assume x_free: x ∈ FV (prop.term t).erased_n,
      unfold prop.erased_n at x_free,
      apply free_in_prop.term,
      from free_in_vc.term.inv x_free
    },
    case prop.not P₁ ih {
      split,

      assume x: var,
      assume x_free: x ∈ FV P₁.not.erased_p,
      unfold prop.erased_p at x_free,
      apply free_in_prop.not,
      have h1, from free_in_vc.not.inv x_free,
      from ih.right h1,

      assume x: var,
      assume x_free: x ∈ FV P₁.not.erased_n,
      unfold prop.erased_n at x_free,
      apply free_in_prop.not,
      have h1, from free_in_vc.not.inv x_free,
      from ih.left h1
    },
    case prop.and P₁ P₂ P₁_ih P₂_ih {
      split,

      assume x: var,
      assume x_free: x ∈ FV (P₁ ⋀ P₂).erased_p,
      unfold prop.erased_p at x_free,
      cases (free_in_vc.and.inv x_free),
      apply free_in_prop.and₁,
      from P₁_ih.left a,
      apply free_in_prop.and₂,
      from P₂_ih.left a,

      assume x: var,
      assume x_free: x ∈ FV (P₁ ⋀ P₂).erased_n,
      unfold prop.erased_n at x_free,
      cases (free_in_vc.and.inv x_free),
      apply free_in_prop.and₁,
      from P₁_ih.right a,
      apply free_in_prop.and₂,
      from P₂_ih.right a
    },
    case prop.or P₁ P₂ P₁_ih P₂_ih {
      split,

      assume x: var,
      assume x_free: x ∈ FV (P₁ ⋁ P₂).erased_p,
      unfold prop.erased_p at x_free,
      cases (free_in_vc.or.inv x_free),
      apply free_in_prop.or₁,
      from P₁_ih.left a,
      apply free_in_prop.or₂,
      from P₂_ih.left a,

      assume x: var,
      assume x_free: x ∈ FV (P₁ ⋁ P₂).erased_n,
      unfold prop.erased_n at x_free,
      cases (free_in_vc.or.inv x_free),
      apply free_in_prop.or₁,
      from P₁_ih.right a,
      apply free_in_prop.or₂,
      from P₂_ih.right a
    },
    case prop.pre t₁ t₂ {
      split,

      assume x: var,
      assume x_free: x ∈ FV (prop.pre t₁ t₂).erased_p,
      unfold prop.erased_p at x_free,
      cases (free_in_vc.pre.inv x_free),

      apply free_in_prop.pre₁,
      from a,

      apply free_in_prop.pre₂,
      from a,

      assume x: var,
      assume x_free: x ∈ FV (prop.pre t₁ t₂).erased_n,
      unfold prop.erased_n at x_free,
      cases (free_in_vc.pre.inv x_free),

      apply free_in_prop.pre₁,
      from a,

      apply free_in_prop.pre₂,
      from a
    },
    case prop.pre₁ op t {
      split,

      assume x: var,
      assume x_free: x ∈ FV (prop.pre₁ op t).erased_p,
      unfold prop.erased_p at x_free,
      apply free_in_prop.preop,
      from free_in_vc.pre₁.inv x_free,

      assume x: var,
      assume x_free: x ∈ FV (prop.pre₁ op t).erased_n,
      unfold prop.erased_n at x_free,
      apply free_in_prop.preop,
      from free_in_vc.pre₁.inv x_free
    },
    case prop.pre₂ op t₁ t₂ {
      split,

      assume x: var,
      assume x_free: x ∈ FV (prop.pre₂ op t₁ t₂).erased_p,
      unfold prop.erased_p at x_free,
      cases (free_in_vc.pre₂.inv x_free),

      apply free_in_prop.preop₁,
      from a,

      apply free_in_prop.preop₂,
      from a,

      assume x: var,
      assume x_free: x ∈ FV (prop.pre₂ op t₁ t₂).erased_n,
      unfold prop.erased_n at x_free,
      cases (free_in_vc.pre₂.inv x_free),

      apply free_in_prop.preop₁,
      from a,

      apply free_in_prop.preop₂,
      from a
    },
    case prop.call t {
      split,

      assume x: var,
      assume x_free: x ∈ FV (prop.call t).erased_p,
      unfold prop.erased_p at x_free,
      have h2, from free_in_vc.term.inv x_free,
      show x ∈ FV (prop.call t), from absurd h2 free_in_term.value.inv,

      assume x: var,
      assume x_free: x ∈ FV (prop.call t).erased_n,
      unfold prop.erased_n at x_free,
      have h2, from free_in_vc.term.inv x_free,
      show x ∈ FV (prop.call t), from absurd h2 free_in_term.value.inv
    },
    case prop.post t₁ t₂ {
      split,

      assume x: var,
      assume x_free: x ∈ FV (prop.post t₁ t₂).erased_p,
      unfold prop.erased_p at x_free,
      cases (free_in_vc.post.inv x_free),

      apply free_in_prop.post₁,
      from a,

      apply free_in_prop.post₂,
      from a,

      assume x: var,
      assume x_free: x ∈ FV (prop.post t₁ t₂).erased_n,
      unfold prop.erased_n at x_free,
      cases (free_in_vc.post.inv x_free),

      apply free_in_prop.post₁,
      from a,

      apply free_in_prop.post₂,
      from a
    },
    case prop.forallc y P₁ P₁_ih {
      split,

      assume x: var,
      assume x_free: x ∈ FV (prop.forallc y P₁).erased_p,
      unfold prop.erased_p at x_free,
      have h2, from free_in_vc.term.inv x_free,
      show x ∈ FV (prop.forallc y P₁), from absurd h2 free_in_term.value.inv,

      assume x: var,
      assume x_free: x ∈ FV (prop.forallc y P₁).erased_n,
      unfold prop.erased_n at x_free,
      have h1, from free_in_vc.univ.inv x_free,
      apply free_in_prop.forallc,
      from h1.left,
      from P₁_ih.right h1.right
    },
    case prop.exis y P₁ P₁_ih {
      split,

      assume x: var,
      assume x_free: x ∈ FV (prop.exis y P₁).erased_p,
      unfold prop.erased_p at x_free,
      have h1, from free_in_vc.not.inv x_free,
      have h2, from free_in_vc.univ.inv h1,
      apply free_in_prop.exis,
      from h2.left,
      have h3, from free_in_vc.not.inv h2.right,
      from P₁_ih.left h3,

      assume x: var,
      assume x_free: x ∈ FV (prop.exis y P₁).erased_n,
      unfold prop.erased_n at x_free,
      have h1, from free_in_vc.not.inv x_free,
      have h2, from free_in_vc.univ.inv h1,
      apply free_in_prop.exis,
      from h2.left,
      have h3, from free_in_vc.not.inv h2.right,
      from P₁_ih.right h3
    }
  end

lemma free_in_instantiate_to_vc_of_free_in_to_vc {P: prop} {t: calltrigger}:
      FV P.to_vc ⊆ FV (P.instantiate_with_p t).to_vc ∧
      FV P.to_vc ⊆ FV (P.instantiate_with_n t).to_vc :=
  begin
    induction P,

    case prop.term t {
      split,

      unfold prop.instantiate_with_p,
      from set.subset.refl (FV (prop.to_vc (prop.term t))),

      unfold prop.instantiate_with_n,
      from set.subset.refl (FV (prop.to_vc (prop.term t)))
    },
    case prop.not P₁ ih {
      split,

      unfold prop.instantiate_with_p,
      unfold prop.to_vc,

      assume x: var,
      assume x_free: x ∈ FV (vc.not (prop.to_vc P₁)),
      apply free_in_vc.not,
      have h1, from free_in_vc.not.inv x_free,
      change (x ∈ FV (prop.to_vc (prop.instantiate_with_n P₁ t))),
      from set.mem_of_mem_of_subset h1 ih.right,

      unfold prop.instantiate_with_n,
      unfold prop.to_vc,

      assume x: var,
      assume x_free: x ∈ FV (vc.not (prop.to_vc P₁)),
      apply free_in_vc.not,
      have h1, from free_in_vc.not.inv x_free,
      change (x ∈ FV (prop.to_vc (prop.instantiate_with_p P₁ t))),
      from set.mem_of_mem_of_subset h1 ih.left
    },
    case prop.and P₁ P₂ P₁_ih P₂_ih {
      split,

      assume x: var,
      assume x_free: x ∈ FV (P₁ ⋀ P₂).to_vc,
      unfold prop.to_vc at x_free,
      unfold prop.instantiate_with_p,
      change (x ∈ FV (prop.to_vc (prop.and (prop.instantiate_with_p P₁ t) (prop.instantiate_with_p P₂ t)))),
      unfold prop.to_vc,
      cases (free_in_vc.and.inv x_free),
      apply free_in_vc.and₁,
      from P₁_ih.left a,
      apply free_in_vc.and₂,
      from P₂_ih.left a,

      assume x: var,
      assume x_free: x ∈ FV (P₁ ⋀ P₂).to_vc,
      unfold prop.to_vc at x_free,
      unfold prop.instantiate_with_n,
      change (x ∈ FV (prop.to_vc (prop.and (prop.instantiate_with_n P₁ t) (prop.instantiate_with_n P₂ t)))),
      unfold prop.to_vc,
      cases (free_in_vc.and.inv x_free),
      apply free_in_vc.and₁,
      from P₁_ih.right a,
      apply free_in_vc.and₂,
      from P₂_ih.right a
    },
    case prop.or P₁ P₂ P₁_ih P₂_ih {
      split,

      assume x: var,
      assume x_free: x ∈ FV (P₁ ⋁ P₂).to_vc,
      unfold prop.to_vc at x_free,
      unfold prop.instantiate_with_p,
      change (x ∈ FV (prop.to_vc (prop.or (prop.instantiate_with_p P₁ t) (prop.instantiate_with_p P₂ t)))),
      unfold prop.to_vc,
      cases (free_in_vc.or.inv x_free),
      apply free_in_vc.or₁,
      from P₁_ih.left a,
      apply free_in_vc.or₂,
      from P₂_ih.left a,

      assume x: var,
      assume x_free: x ∈ FV (P₁ ⋁ P₂).to_vc,
      unfold prop.to_vc at x_free,
      unfold prop.instantiate_with_n,
      change (x ∈ FV (prop.to_vc (prop.or (prop.instantiate_with_n P₁ t) (prop.instantiate_with_n P₂ t)))),
      unfold prop.to_vc,
      cases (free_in_vc.or.inv x_free),
      apply free_in_vc.or₁,
      from P₁_ih.right a,
      apply free_in_vc.or₂,
      from P₂_ih.right a
    },
    case prop.pre t₁ t₂ {
      split,

      unfold prop.instantiate_with_p,
      from set.subset.refl (FV (prop.to_vc (prop.pre t₁ t₂))),

      unfold prop.instantiate_with_n,
      from set.subset.refl (FV (prop.to_vc (prop.pre t₁ t₂)))
    },
    case prop.pre₁ op t {
      split,

      unfold prop.instantiate_with_p,
      from set.subset.refl (FV (prop.to_vc (prop.pre₁ op t))),

      unfold prop.instantiate_with_n,
      from set.subset.refl (FV (prop.to_vc (prop.pre₁ op t)))
    },
    case prop.pre₂ op t₁ t₂ {
      split,

      unfold prop.instantiate_with_p,
      from set.subset.refl (FV (prop.to_vc (prop.pre₂ op t₁ t₂))),

      unfold prop.instantiate_with_n,
      from set.subset.refl (FV (prop.to_vc (prop.pre₂ op t₁ t₂)))
    },
    case prop.call t {
      split,

      unfold prop.instantiate_with_p,
      from set.subset.refl (FV (prop.to_vc (prop.call t))),

      unfold prop.instantiate_with_n,
      from set.subset.refl (FV (prop.to_vc (prop.call t)))
    },
    case prop.post t₁ t₂ {
      split,

      unfold prop.instantiate_with_p,
      from set.subset.refl (FV (prop.to_vc (prop.post t₁ t₂))),

      unfold prop.instantiate_with_n,
      from set.subset.refl (FV (prop.to_vc (prop.post t₁ t₂)))
    },
    case prop.forallc y P₁ P₁_ih {
      split,

      unfold prop.instantiate_with_p,
      assume x: var,
      assume x_free: x ∈ FV (prop.to_vc (prop.forallc y P₁)),
      change x ∈ FV (prop.to_vc (prop.and (prop.forallc y P₁) (prop.substt y (t.x) P₁))),
      unfold1 prop.to_vc,
      apply free_in_vc.and₁,
      from x_free,

      unfold prop.instantiate_with_n,
      from set.subset.refl (FV (prop.to_vc (prop.forallc y P₁)))
    },
    case prop.exis y P₁ P₁_ih {
      split,

      unfold prop.instantiate_with_p,
      from set.subset.refl (FV (prop.to_vc (prop.exis y P₁))),

      unfold prop.instantiate_with_n,
      from set.subset.refl (FV (prop.to_vc (prop.exis y P₁)))
    }
  end

lemma free_in_instantiate_with_of_free_in_prop {P: prop} {t: calltrigger}:
      FV P ⊆ FV (P.instantiate_with_p t) ∧
      FV P ⊆ FV (P.instantiate_with_n t) :=
  begin
    induction P,

    case prop.term t {
      split,

      unfold prop.instantiate_with_p,
      from set.subset.refl (FV (prop.term t)),

      unfold prop.instantiate_with_n,
      from set.subset.refl (FV (prop.term t))
    },
    case prop.not P₁ ih {
      split,

      unfold prop.instantiate_with_p,

      assume x: var,
      assume x_free: x ∈ FV (prop.not P₁),
      apply free_in_prop.not,
      have h1, from free_in_prop.not.inv x_free,
      change (x ∈ FV (prop.instantiate_with_n P₁ t)),
      from set.mem_of_mem_of_subset h1 ih.right,

      unfold prop.instantiate_with_n,

      assume x: var,
      assume x_free: x ∈ FV (prop.not P₁),
      apply free_in_prop.not,
      have h1, from free_in_prop.not.inv x_free,
      change (x ∈ FV (prop.instantiate_with_p P₁ t)),
      from set.mem_of_mem_of_subset h1 ih.left
    },
    case prop.and P₁ P₂ P₁_ih P₂_ih {
      split,

      assume x: var,
      assume x_free: x ∈ FV (P₁ ⋀ P₂),
      unfold prop.instantiate_with_p,
      cases (free_in_prop.and.inv x_free),
      apply free_in_prop.and₁,
      from P₁_ih.left a,
      apply free_in_prop.and₂,
      from P₂_ih.left a,

      assume x: var,
      assume x_free: x ∈ FV (P₁ ⋀ P₂),
      unfold prop.instantiate_with_n,
      cases (free_in_prop.and.inv x_free),
      apply free_in_prop.and₁,
      from P₁_ih.right a,
      apply free_in_prop.and₂,
      from P₂_ih.right a
    },
    case prop.or P₁ P₂ P₁_ih P₂_ih {
      split,

      assume x: var,
      assume x_free: x ∈ FV (P₁ ⋁ P₂),
      unfold prop.instantiate_with_p,
      cases (free_in_prop.or.inv x_free),
      apply free_in_prop.or₁,
      from P₁_ih.left a,
      apply free_in_prop.or₂,
      from P₂_ih.left a,

      assume x: var,
      assume x_free: x ∈ FV (P₁ ⋁ P₂),
      unfold prop.instantiate_with_n,
      cases (free_in_prop.or.inv x_free),
      apply free_in_prop.or₁,
      from P₁_ih.right a,
      apply free_in_prop.or₂,
      from P₂_ih.right a
    },
    case prop.pre t₁ t₂ {
      split,

      unfold prop.instantiate_with_p,
      from set.subset.refl (FV (prop.pre t₁ t₂)),

      unfold prop.instantiate_with_n,
      from set.subset.refl (FV (prop.pre t₁ t₂))
    },
    case prop.pre₁ op t {
      split,

      unfold prop.instantiate_with_p,
      from set.subset.refl (FV (prop.pre₁ op t)),

      unfold prop.instantiate_with_n,
      from set.subset.refl (FV (prop.pre₁ op t))
    },
    case prop.pre₂ op t₁ t₂ {
      split,

      unfold prop.instantiate_with_p,
      from set.subset.refl (FV (prop.pre₂ op t₁ t₂)),

      unfold prop.instantiate_with_n,
      from set.subset.refl (FV (prop.pre₂ op t₁ t₂))
    },
    case prop.call t {
      split,

      unfold prop.instantiate_with_p,
      from set.subset.refl (FV (prop.call t)),

      unfold prop.instantiate_with_n,
      from set.subset.refl (FV (prop.call t))
    },
    case prop.post t₁ t₂ {
      split,

      unfold prop.instantiate_with_p,
      from set.subset.refl (FV (prop.post t₁ t₂)),

      unfold prop.instantiate_with_n,
      from set.subset.refl (FV (prop.post t₁ t₂))
    },
    case prop.forallc y P₁ P₁_ih {
      split,

      unfold prop.instantiate_with_p,

      assume x: var,
      assume x_free: x ∈ FV (prop.forallc y P₁),
      apply free_in_prop.and₁,
      from x_free,

      unfold prop.instantiate_with_n,
      from set.subset.refl (FV (prop.forallc y P₁))
    },
    case prop.exis y P₁ P₁_ih {
      split,

      unfold prop.instantiate_with_p,
      from set.subset.refl (FV (prop.exis y P₁)),

      unfold prop.instantiate_with_n,
      from set.subset.refl (FV (prop.exis y P₁))
    }
  end

instance {x: var} {t: term}: decidable (free_in_term x t) :=
  begin
    induction t with v y unop t₁ ih₁ binop t₂ t₃ ih₂ ih₃ t₄ t₅ ih₄ ih₅,

    show decidable (free_in_term x (term.value v)), by begin
      from is_false (free_in_term.value.inv)
    end,

    show decidable (free_in_term x (term.var y)), by begin
      by_cases (x = y)  with h1,

      rw[h1],
      from is_true (free_in_term.var y),
      apply is_false, 
      assume h2,
      have h3, from free_in_term.var.inv h2,
      contradiction
    end,

    show decidable (free_in_term x (term.unop unop t₁)), by begin
      by_cases (free_in_term x t₁) with h1,
      from is_true (free_in_term.unop h1),
      apply is_false,
      assume h2,
      have h3, from free_in_term.unop.inv h2,
      contradiction
    end,

    show decidable (free_in_term x (term.binop binop t₂ t₃)), by begin
      by_cases (free_in_term x t₂) with h1,
      from is_true (free_in_term.binop₁ h1),

      by_cases (free_in_term x t₃) with h2,
      from is_true (free_in_term.binop₂ h2),
      apply is_false,
      assume h3,
      have h4, from free_in_term.binop.inv h3,
      cases h4 with h5 h6,
      contradiction,
      contradiction
    end,

    show decidable (free_in_term x (term.app t₄ t₅)), by begin
      by_cases (free_in_term x t₄) with h1,
      from is_true (free_in_term.app₁ h1),

      by_cases (free_in_term x t₅) with h2,
      from is_true (free_in_term.app₂ h2),
      apply is_false,
      assume h3,
      have h4, from free_in_term.app.inv h3,
      cases h4 with h5 h6,
      contradiction,
      contradiction
    end
  end

instance {x: var} {P: vc}: decidable (free_in_vc x P) :=
  begin
    induction P,
    case vc.term t {
      by_cases (free_in_term x t) with h1,
      from is_true (free_in_vc.term h1),
      apply is_false,
      assume h2,
      have h3, from free_in_vc.term.inv h2,
      contradiction
    },
    case vc.not P₁ ih {
      by_cases (free_in_vc x P₁) with h1,
      from is_true (free_in_vc.not h1),
      apply is_false,
      assume h2,
      have h3, from free_in_vc.not.inv h2,
      contradiction
    },
    case vc.and P₁ P₂ P₁_ih P₂_ih {
      by_cases (free_in_vc x P₁) with h1,
      from is_true (free_in_vc.and₁ h1),

      by_cases (free_in_vc x P₂) with h2,
      from is_true (free_in_vc.and₂ h2),
      apply is_false,
      assume h3,
      have h4, from free_in_vc.and.inv h3,
      cases h4 with h5 h6,
      contradiction,
      contradiction
    },
    case vc.or P₁ P₂ P₁_ih P₂_ih {
      by_cases (free_in_vc x P₁) with h1,
      from is_true (free_in_vc.or₁ h1),

      by_cases (free_in_vc x P₂) with h2,
      from is_true (free_in_vc.or₂ h2),
      apply is_false,
      assume h3,
      have h4, from free_in_vc.or.inv h3,
      cases h4 with h5 h6,
      contradiction,
      contradiction
    },
    case vc.pre t₁ t₂ {
      by_cases (free_in_term x t₁) with h1,
      from is_true (free_in_vc.pre₁ h1),

      by_cases (free_in_term x t₂) with h2,
      from is_true (free_in_vc.pre₂ h2),
      apply is_false,
      assume h3,
      have h4, from free_in_vc.pre.inv h3,
      cases h4 with h5 h6,
      contradiction,
      contradiction
    },
    case vc.pre₁ op t {
      by_cases (free_in_term x t) with h1,
      from is_true (free_in_vc.preop h1),
      apply is_false,
      assume h2,
      have h3, from free_in_vc.pre₁.inv h2,
      contradiction
    },
    case vc.pre₂ op t₁ t₂ {
      by_cases (free_in_term x t₁) with h1,
      from is_true (free_in_vc.preop₁ h1),

      by_cases (free_in_term x t₂) with h2,
      from is_true (free_in_vc.preop₂ h2),
      apply is_false,
      assume h3,
      have h4, from free_in_vc.pre₂.inv h3,
      cases h4 with h5 h6,
      contradiction,
      contradiction
    },
    case vc.post t₁ t₂ {
      by_cases (free_in_term x t₁) with h1,
      from is_true (free_in_vc.post₁ h1),

      by_cases (free_in_term x t₂) with h2,
      from is_true (free_in_vc.post₂ h2),
      apply is_false,
      assume h3,
      have h4, from free_in_vc.post.inv h3,
      cases h4 with h5 h6,
      contradiction,
      contradiction
    },
    case vc.univ y P' P'_ih {
      by_cases (x = y) with h1,
      rw[h1],
      apply is_false,
      assume h2,
      have h3, from free_in_vc.univ.inv h2,
      from h3.left rfl,

      by_cases (free_in_vc x P') with h2,
      from is_true (free_in_vc.univ h1 h2),
      apply is_false,
      assume h3,
      have h4, from free_in_vc.univ.inv h3,
      from h2 h4.right
    }
  end

lemma term.fresh_var_is_not_free {t: term}: ∀y, y ≥ t.fresh_var → y ∉ FV t :=
  begin
    induction t with v z unop t₁ t₁_ih binop t₂ t₃ t₂_ih t₃_ih t₄ t₅ t₄_ih t₅_ih,

    show ∀y : var, y ≥ term.fresh_var (term.value v) → y ∉ FV (term.value v), by begin
      assume y,
      assume h1,
      from free_in_term.value.inv
    end,

    show ∀y: var, y ≥ term.fresh_var (term.var z) → y ∉ FV (term.var z), by begin
      assume y,
      assume h1,
      assume h2,
      have h3: (y = z), from free_in_term.var.inv h2,
      rw[h3] at h1,
      unfold term.fresh_var at h1,
      have h3: z < z + 1, from lt_of_add_one,
      have h4, from not_lt_of_ge h1,
      contradiction
    end,

    show ∀y: var, y ≥ term.fresh_var (term.unop unop t₁) → y ∉ FV (term.unop unop t₁), by begin
      assume y,
      assume h1,
      assume h2,
      have h3, from free_in_term.unop.inv h2,
      unfold term.fresh_var at h1,
      from t₁_ih y h1 h3
    end,

    show ∀y: var, y ≥ term.fresh_var (term.binop binop t₂ t₃) → y ∉ FV (term.binop binop t₂ t₃), by begin
      assume y,
      assume h1,
      assume h2,
      unfold term.fresh_var at h1,
      cases (free_in_term.binop.inv h2) with h3 h3,

      have h4: (term.fresh_var t₂ ≤ max (term.fresh_var t₂) (term.fresh_var t₃)),
      from le_max_left (term.fresh_var t₂) (term.fresh_var t₃),
      have h5, from ge_trans h1 h4,
      from t₂_ih y h5 h3,

      have h4: (term.fresh_var t₃ ≤ max (term.fresh_var t₂) (term.fresh_var t₃)),
      from le_max_right (term.fresh_var t₂) (term.fresh_var t₃),
      have h5, from ge_trans h1 h4,
      from t₃_ih y h5 h3
    end,

    show ∀y: var, y ≥ term.fresh_var (term.app t₄ t₅) → y ∉ FV (term.app t₄ t₅), by begin
      assume y,
      assume h1,
      assume h2,
      unfold term.fresh_var at h1,
      cases (free_in_term.app.inv h2) with h3 h3,

      have h4: (term.fresh_var t₄ ≤ max (term.fresh_var t₄) (term.fresh_var t₅)),
      from le_max_left (term.fresh_var t₄) (term.fresh_var t₅),
      have h5, from ge_trans h1 h4,
      from t₄_ih y h5 h3,

      have h4: (term.fresh_var t₅ ≤ max (term.fresh_var t₄) (term.fresh_var t₅)),
      from le_max_right (term.fresh_var t₄) (term.fresh_var t₅),
      have h5, from ge_trans h1 h4,
      from t₅_ih y h5 h3
    end
  end

lemma prop.fresh_var_is_unused {P: prop}: ∀x, x ≥ P.fresh_var → ¬ prop.uses_var x P :=
  begin
    induction P,

    case prop.term t {
      assume y,
      assume h1,
      assume h2,
      cases h2 with _ h3,
      unfold prop.fresh_var at h1,
      from term.fresh_var_is_not_free y h1 h3
    },

    case prop.not P₁ P₁_ih {
      assume y,
      assume h1,
      assume h2,
      cases h2 with _ _ _ h3,
      unfold prop.fresh_var at h1,
      from P₁_ih y h1 h3
    },

    case prop.and P₁ P₂ P₁_ih P₂_ih {
      assume y,
      assume h1,
      assume h2,
      unfold prop.fresh_var at h1,
      cases h2 with _ _ _ _ _ _ h3 _ _ h3,

      have h4: (prop.fresh_var P₁ ≤ max (prop.fresh_var P₁) (prop.fresh_var P₂)),
      from le_max_left (prop.fresh_var P₁) (prop.fresh_var P₂),
      have h5, from ge_trans h1 h4,
      from P₁_ih y h5 h3,

      have h4: (prop.fresh_var P₂ ≤ max (prop.fresh_var P₁) (prop.fresh_var P₂)),
      from le_max_right (prop.fresh_var P₁) (prop.fresh_var P₂),
      have h5, from ge_trans h1 h4,
      from P₂_ih y h5 h3
    },

    case prop.or P₁ P₂ P₁_ih P₂_ih {
      assume y,
      assume h1,
      assume h2,
      unfold prop.fresh_var at h1,
      cases h2 with _ _ _ _ _ _ _ _ _ _ _ _ h3 _ _ h3,

      have h4: (prop.fresh_var P₁ ≤ max (prop.fresh_var P₁) (prop.fresh_var P₂)),
      from le_max_left (prop.fresh_var P₁) (prop.fresh_var P₂),
      have h5, from ge_trans h1 h4,
      from P₁_ih y h5 h3,

      have h4: (prop.fresh_var P₂ ≤ max (prop.fresh_var P₁) (prop.fresh_var P₂)),
      from le_max_right (prop.fresh_var P₁) (prop.fresh_var P₂),
      have h5, from ge_trans h1 h4,
      from P₂_ih y h5 h3
    },

    case prop.pre t₁ t₂ {
      assume y,
      assume h1,
      assume h2,
      unfold prop.fresh_var at h1,
      cases h2 with _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h3 _ _ h3,

      have h4: (term.fresh_var t₁ ≤ max (term.fresh_var t₁) (term.fresh_var t₂)),
      from le_max_left (term.fresh_var t₁) (term.fresh_var t₂),
      have h5, from ge_trans h1 h4,
      from term.fresh_var_is_not_free y h5 h3,

      have h4: (term.fresh_var t₂ ≤ max (term.fresh_var t₁) (term.fresh_var t₂)),
      from le_max_right (term.fresh_var t₁) (term.fresh_var t₂),
      have h5, from ge_trans h1 h4,
      from term.fresh_var_is_not_free y h5 h3
    },

    case prop.pre₁ op t {
      assume y,
      assume h1,
      assume h2,
      cases h2,
      unfold prop.fresh_var at h1,
      from term.fresh_var_is_not_free y h1 a
    },

    case prop.pre₂ op t₁ t₂ {
      assume y,
      assume h1,
      assume h2,
      unfold prop.fresh_var at h1,
      cases h2,

      have h4: (term.fresh_var t₁ ≤ max (term.fresh_var t₁) (term.fresh_var t₂)),
      from le_max_left (term.fresh_var t₁) (term.fresh_var t₂),
      have h5, from ge_trans h1 h4,
      from term.fresh_var_is_not_free y h5 a,

      have h4: (term.fresh_var t₂ ≤ max (term.fresh_var t₁) (term.fresh_var t₂)),
      from le_max_right (term.fresh_var t₁) (term.fresh_var t₂),
      have h5, from ge_trans h1 h4,
      from term.fresh_var_is_not_free y h5 a
    },

    case prop.call t {
      assume y,
      assume h1,
      assume h2,
      cases h2,
      unfold prop.fresh_var at h1,
      from term.fresh_var_is_not_free y h1 a
    },

    case prop.post t₁ t₂ {
      assume y,
      assume h1,
      assume h2,
      unfold prop.fresh_var at h1,
      cases h2,

      have h4: (term.fresh_var t₁ ≤ max (term.fresh_var t₁) (term.fresh_var t₂)),
      from le_max_left (term.fresh_var t₁) (term.fresh_var t₂),
      have h5, from ge_trans h1 h4,
      from term.fresh_var_is_not_free y h5 a,

      have h4: (term.fresh_var t₂ ≤ max (term.fresh_var t₁) (term.fresh_var t₂)),
      from le_max_right (term.fresh_var t₁) (term.fresh_var t₂),
      have h5, from ge_trans h1 h4,
      from term.fresh_var_is_not_free y h5 a
    },

    case prop.forallc z P₁ P₁_ih {
      assume y,
      assume h1,
      assume h2,
      unfold prop.fresh_var at h1,
      cases h2,
      
      have h4: (prop.fresh_var P₁ ≤ max (z + 1) (prop.fresh_var P₁)),
      from le_max_right (z + 1) (prop.fresh_var P₁),
      have h5, from ge_trans h1 h4,
      from P₁_ih y h5 a,

      have h4: (z + 1 ≤ max (z + 1) (prop.fresh_var P₁)),
      from le_max_left (z + 1) (prop.fresh_var P₁),
      have h5, from ge_trans h1 h4,
      have h3: z < z + 1, from lt_of_add_one,
      have h4, from not_lt_of_ge h1,
      contradiction
    },

    case prop.exis z P₁ P₁_ih {
      assume y,
      assume h1,
      assume h2,
      unfold prop.fresh_var at h1,
      cases h2,
      
      have h4: (prop.fresh_var P₁ ≤ max (z + 1) (prop.fresh_var P₁)),
      from le_max_right (z + 1) (prop.fresh_var P₁),
      have h5, from ge_trans h1 h4,
      from P₁_ih y h5 a,

      have h4: (z + 1 ≤ max (z + 1) (prop.fresh_var P₁)),
      from le_max_left (z + 1) (prop.fresh_var P₁),
      have h5, from ge_trans h1 h4,
      have h3: z < z + 1, from lt_of_add_one,
      have h4, from not_lt_of_ge h1,
      contradiction
    }
  end

lemma vc.uses_var_of_free {x: var} {P: vc}: x ∈ FV P → vc.uses_var x P :=
  begin
    assume h1,
    induction P,
    case vc.term t {
      from vc.uses_var.term (free_in_vc.term.inv h1)
    },
    case vc.not P₁ P₁_ih {
      from vc.uses_var.not (P₁_ih (free_in_vc.not.inv h1))
    },
    case vc.and P₁ P₂ P₁_ih P₂_ih {
      cases (free_in_vc.and.inv h1) with h2 h3,

      from vc.uses_var.and₁ (P₁_ih h2),
      from vc.uses_var.and₂ (P₂_ih h3)
    },
    case vc.or P₁ P₂ P₁_ih P₂_ih {
      cases (free_in_vc.or.inv h1) with h2 h3,

      from vc.uses_var.or₁ (P₁_ih h2),
      from vc.uses_var.or₂ (P₂_ih h3)
    },
    case vc.pre t₁ t₂ {
      cases (free_in_vc.pre.inv h1) with h2 h3,

      from vc.uses_var.pre₁ h2,
      from vc.uses_var.pre₂ h3
    },
    case vc.pre₁ op t {
      from vc.uses_var.preop (free_in_vc.pre₁.inv h1)
    },
    case vc.pre₂ op t₁ t₂ {
      cases (free_in_vc.pre₂.inv h1) with h2 h3,

      from vc.uses_var.preop₁ h2,
      from vc.uses_var.preop₂ h3
    },
    case vc.post t₁ t₂ {
      cases (free_in_vc.post.inv h1) with h2 h3,

      from vc.uses_var.post₁ h2,
      from vc.uses_var.post₂ h3
    },
    case vc.univ y P' P'_ih {
      have h2, from free_in_vc.univ.inv h1,
      from vc.uses_var.univ (P'_ih h2.right)
    }
  end

lemma vc.uses_var.term.inv {t: term} {x: var}: vc.uses_var x t → x ∈ FV t :=
  assume x_free_in_not: vc.uses_var x t,
  begin
    cases x_free_in_not,
    case vc.uses_var.term free_in_P { from free_in_P }
  end

lemma vc.uses_var.not.inv {P: vc} {x: var}: vc.uses_var x P.not → vc.uses_var x P :=
  assume x_free_in_not: vc.uses_var x P.not,
  begin
    cases x_free_in_not,
    case vc.uses_var.not free_in_P { from free_in_P }
  end

lemma vc.uses_var.and.inv {P₁ P₂: vc} {x: var}: vc.uses_var x (P₁ ⋀ P₂) → vc.uses_var x P₁ ∨ vc.uses_var x P₂ :=
  assume x_free_in_and: vc.uses_var x (P₁ ⋀ P₂),
  begin
    cases x_free_in_and,
    case vc.uses_var.and₁ free_in_P₁ {
      show vc.uses_var x P₁ ∨ vc.uses_var x P₂, from or.inl free_in_P₁
    },
    case vc.uses_var.and₂ free_in_P₂ {
      show vc.uses_var x P₁ ∨ vc.uses_var x P₂, from or.inr free_in_P₂
    }
  end

lemma vc.uses_var.or.inv {P₁ P₂: vc} {x: var}: vc.uses_var x (P₁ ⋁ P₂) → vc.uses_var x P₁ ∨ vc.uses_var x P₂ :=
  assume x_free_in_or: vc.uses_var x (P₁ ⋁ P₂),
  begin
    cases x_free_in_or,
    case vc.uses_var.or₁ free_in_P₁ {
      show vc.uses_var x P₁ ∨ vc.uses_var x P₂, from or.inl free_in_P₁
    },
    case vc.uses_var.or₂ free_in_P₂ {
      show vc.uses_var x P₁ ∨ vc.uses_var x P₂, from or.inr free_in_P₂
    }
  end

lemma vc.uses_var.univ.inv {P: vc} {x y: var}: vc.uses_var x (vc.univ y P) → (x = y) ∨ vc.uses_var x P :=
  assume x_free_in_univ: vc.uses_var x (vc.univ y P),
  begin
    cases x_free_in_univ,
    case vc.uses_var.univ h1 {
      from or.inr h1
    },
    case vc.uses_var.quantified h1 {
      from or.inl rfl
    }
  end

lemma prop_uses_var_of_to_vc_uses_var {x: var} {P: prop}: vc.uses_var x P.to_vc → prop.uses_var x P :=
  begin
    assume h1,

    induction P,

    case prop.term t {
      unfold prop.to_vc at h1,
      cases h1,
      from prop.uses_var.term a
    },

    case prop.not P₁ P₁_ih {
      unfold prop.to_vc at h1,
      have h2, from vc.uses_var.not.inv h1,
      apply prop.uses_var.not,
      from P₁_ih h2
    },

    case prop.and P₁ P₂ P₁_ih P₂_ih {
      unfold prop.to_vc at h1,
      cases vc.uses_var.and.inv h1 with h2 h3,
      apply prop.uses_var.and₁,
      from P₁_ih h2,
      apply prop.uses_var.and₂,
      from P₂_ih h3
    },

    case prop.or P₁ P₂ P₁_ih P₂_ih {
      unfold prop.to_vc at h1,
      cases vc.uses_var.or.inv h1 with h2 h3,
      apply prop.uses_var.or₁,
      from P₁_ih h2,
      apply prop.uses_var.or₂,
      from P₂_ih h3
    },

    case prop.pre t₁ t₂ {
      unfold prop.to_vc at h1,
      cases h1,
      from prop.uses_var.pre₁ a,
      from prop.uses_var.pre₂ a
    },

    case prop.pre₁ op t {
      unfold prop.to_vc at h1,
      cases h1,
      from prop.uses_var.preop a
    },

    case prop.pre₂ op t₁ t₂ {
      unfold prop.to_vc at h1,
      cases h1,
      from prop.uses_var.preop₁ a,
      from prop.uses_var.preop₂ a
    },

    case prop.call t {
      unfold prop.to_vc at h1,
      have h2, from vc.uses_var.term.inv h1,
      have h3: ¬ free_in_term x value.true, from free_in_term.value.inv,
      contradiction
    },

    case prop.post t₁ t₂ {
      unfold prop.to_vc at h1,
      cases h1,
      from prop.uses_var.post₁ a,
      from prop.uses_var.post₂ a
    },

    case prop.forallc z P₁ P₁_ih {
      unfold prop.to_vc at h1,
      cases vc.uses_var.univ.inv h1 with h2 h3,

      rw[h2],
      from prop.uses_var.uquantified z,

      apply prop.uses_var.forallc,
      from P₁_ih h3
    },

    case prop.exis z P₁ P₁_ih {
      unfold prop.to_vc at h1,
      have h2, from vc.uses_var.not.inv h1,
      cases vc.uses_var.univ.inv h2 with h3 h4,

      rw[h3],
      from prop.uses_var.equantified z,

      apply prop.uses_var.exis,
      have h5, from vc.uses_var.not.inv h4,
      from P₁_ih h5
    }
  end
