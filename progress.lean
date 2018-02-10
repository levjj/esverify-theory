import .syntax .etc .evaluation .props .vcgen

@[reducible]
def is_return(s: stack): Prop := ∃(σ: env) (x: var), s = (σ, exp.return x)

lemma exp.vcgen.return.inv {P: prop} {x: var} {Q: propctx}: (P ⊢ exp.return x : Q) → x ∈ FV P :=
  assume return_verified: P ⊢ exp.return x : Q,
  begin
    cases return_verified,
    case exp.vcgen.return x_free {
      show x ∈ FV P, from x_free
    }
  end

lemma stack.vcgen.top.inv {H: list call} {σ: env} {e: exp}: (H ⊩ (σ, e)) → ∃P Q, (⊢ σ: P) ∧ (H & P ⊢ e: Q) :=
  assume top_verified: H ⊩ (σ, e),
  begin
    cases top_verified,
    case stack.vcgen.top P Q env_verified e_verified {
      show ∃P Q, (⊢ σ: P) ∧ (H & P ⊢ e: Q), from exists.intro P (exists.intro Q ⟨env_verified, e_verified⟩)
    }
  end

lemma not_free_of_subst_env {P: prop} {R: spec} {σ: env} {x: var}:
       (⊢ σ : P) → free_in_prop x P → ¬ (free_in_prop x (spec.subst_env σ R)) :=
  sorry

lemma val_of_free_in_nonempty_env {P: prop} {σ: env} {x y: var} {v: value}:
                                  (⊢ σ : P) → (x ≠ y → ∃v', σ y = some v') →
                                  ∃v', σ[x↦v] y = some v' :=
  assume env_verified: ⊢ σ : P,
  assume ih: x ≠ y → ∃v', σ y = some v',
  if x_eq_y: x = y then (
    have h: σ[x↦v].apply x = (if x = x then ↑v else σ.apply x), by unfold env.apply,
    have (if x = x then ↑v else σ.apply x) = ↑v, by simp *,
    have σ[x↦v].apply x = ↑v, from this ▸ h,
    have σ[x↦v].apply y = some v, from x_eq_y ▸ this,
    show ∃v', σ[x↦v] y = some v', from exists.intro v this
  ) else (
    have ∃v', σ y = some v', from ih x_eq_y,
    let ⟨v', σ_has_y⟩ := this in
    have h: σ[x↦v].apply y = (if x = y then ↑v else σ.apply y), by unfold env.apply,
    have (if x = y then ↑v else σ.apply y) = σ.apply y, by simp *,
    have σ[x↦v].apply y = σ.apply y, from this ▸ h,
    have σ[x↦v].apply y = some v', from eq.trans this σ_has_y,
    show ∃v', σ[x↦v] y = some v', from exists.intro v' this
  )

lemma val_of_free_in_env {P: prop} {σ: env} {x: var}: (⊢ σ : P) → x ∈ FV P → ∃v, σ x = some v :=
  assume env_verified: ⊢ σ: P,
  assume x_free_in_P: x ∈ FV P,
  begin
    induction env_verified,
    case env.vcgen.empty {
      cases x_free_in_P,
      case free_in_prop.term x_free_in_true {
        cases x_free_in_true
      }
    },
    case env.vcgen.tru σ' x' Q σ'_verified ih { from
      val_of_free_in_nonempty_env σ'_verified (
        assume x'_is_not_x: x' ≠ x,
        have free_in_prop x Q ∨ free_in_prop x (x' ≡ value.true), from free_in_prop.and.inv x_free_in_P,
        or.elim this.symm
        (
          assume x_free_in_true: free_in_prop x (x' ≡ value.true),
          show ∃v, σ' x = some v, by begin
            cases x_free_in_true,
            case free_in_prop.term x_free_in_eq {
              cases x_free_in_eq,
              case free_in_term.binop₁ free_in_x' {
                have x'_is_x: (x' = x), from (free_in_term.var.inv free_in_x').symm,
                contradiction
              },
              case free_in_term.binop₂ free_in_true {
                cases free_in_true
              }
            }
          end
        )
        (
          assume x_free_in_Q: free_in_prop x Q,
          show ∃v, σ' x = some v, from ih x_free_in_Q
        )
      )
    },
    case env.vcgen.fls σ' x' Q σ'_verified ih { from
      val_of_free_in_nonempty_env σ'_verified (
        assume x'_is_not_x: x' ≠ x,
        have free_in_prop x Q ∨ free_in_prop x (x' ≡ value.false), from free_in_prop.and.inv x_free_in_P,
        or.elim this.symm
        (
          assume x_free_in_false: free_in_prop x (x' ≡ value.false),
          show ∃v, σ' x = some v, by begin
            cases x_free_in_false,
            case free_in_prop.term x_free_in_eq {
              cases x_free_in_eq,
              case free_in_term.binop₁ free_in_x' {
                have x'_is_x: (x' = x), from (free_in_term.var.inv free_in_x').symm,
                contradiction
              },
              case free_in_term.binop₂ free_in_false {
                cases free_in_false
              }
            }
          end
        )
        (
          assume x_free_in_Q: free_in_prop x Q,
          show ∃v, σ' x = some v, from ih x_free_in_Q
        )
      )
    },
    case env.vcgen.num n σ' x' Q σ'_verified ih { from
      val_of_free_in_nonempty_env σ'_verified (
        assume x'_is_not_x: x' ≠ x,
        have free_in_prop x Q ∨ free_in_prop x (x' ≡ value.num n), from free_in_prop.and.inv x_free_in_P,
        or.elim this.symm
        (
          assume x_free_in_num: free_in_prop x (x' ≡ value.num n),
          show ∃v, σ' x = some v, by begin
            cases x_free_in_num,
            case free_in_prop.term x_free_in_eq {
              cases x_free_in_eq,
              case free_in_term.binop₁ free_in_x' {
                have x'_is_x: (x' = x), from (free_in_term.freevar.inv free_in_x').symm,
                contradiction
              },
              case free_in_term.binop₂ free_in_num {
                cases free_in_num
              }
            }
          end
        )
        (
          assume x_free_in_Q: free_in_prop x Q,
          show ∃v, σ' x = some v, from ih x_free_in_Q
        )
      )
    },
    case env.vcgen.func σ₁ σ₂ f g fx R S e Q₁ Q₂ Q₃ σ₁_verified σ₂_verified R_fv S_fv func_verified S_valid { from
      val_of_free_in_nonempty_env σ₁_verified (
        assume f_is_not_x: f ≠ x,
        let R': spec := spec.subst_env (σ₂[g↦value.func g fx R S e σ₂]) R in
        let S': spec := spec.subst_env (σ₂[g↦value.func g fx R S e σ₂]) S in
        let fspec: prop := spec.func f fx R' S' in
        have free_in_prop x (Q₁ & fspec) ∨ free_in_prop x (f ≡ value.func g fx R S e σ₂),
        from free_in_prop.and.inv x_free_in_P,
        or.elim this
        (
          assume : free_in_prop x (Q₁ & fspec),
          have free_in_prop x Q₁ ∨ free_in_prop x fspec, from free_in_prop.and.inv this,
          or.elim this
          (
            assume : free_in_prop x Q₁,
            show ∃v, σ₁ x = some v, from ih_1 this
          )
          (
            assume : free_in_prop x fspec,
            have 
              free_in_prop x (term.unop unop.isFunc f) ∨
              free_in_prop x (prop.forallc fx f (prop.implies R'.to_prop (prop.pre f fx)
                              & prop.implies (R'.to_prop & prop.post f fx) S'.to_prop)),
            from free_in_prop.and.inv this,
            or.elim this
            (
              assume x_free_in_unopp: free_in_prop x (term.unop unop.isFunc f),
              show ∃v, σ₁ x = some v, by begin
                cases x_free_in_unopp,
                case free_in_prop.term x_free_in_unop {
                  cases x_free_in_unop,
                  case free_in_term.unop free_in_f {
                    have : (f = x), from (free_in_term.freevar.inv free_in_f).symm,
                    contradiction
                  }
                }
              end
            )
            (
              assume : free_in_prop x (prop.forallc fx f (prop.implies R'.to_prop (prop.pre f fx)
                                     & prop.implies (R'.to_prop & prop.post f fx) S'.to_prop)),
              show ∃v, σ₁ x = some v, by begin
                cases this,
                case free_in_prop.forallc₁ x_not_fx x_free_in_f {
                  have : (f = x), from (free_in_term.freevar.inv x_free_in_f).symm,
                  contradiction
                },
                case free_in_prop.forallc₂ x_not_fx x_free_in_p { from
                  have free_in_prop x (prop.implies R'.to_prop (prop.pre f fx))
                     ∨ free_in_prop x (prop.implies (R'.to_prop & prop.post f fx) S'.to_prop),
                  from free_in_prop.and.inv x_free_in_p,
                  or.elim this
                  (
                    assume : free_in_prop x (prop.implies R'.to_prop (prop.pre f fx)),
                    have free_in_prop x (prop.or R'.to_prop.not (prop.pre f fx)), from this,
                    have free_in_prop x R'.to_prop.not ∨ free_in_prop x (prop.pre f fx),
                    from free_in_prop.or.inv this,
                    or.elim this
                    (
                      assume : free_in_prop x R'.to_prop.not,
                      have free_in_prop x R'.to_prop, from free_in_prop.not.inv this,

                      show ∃v, σ₁ x = some v, from sorry
                    )
                    (
                      assume x_free_in_pre: free_in_prop x (prop.pre f fx),
                      show ∃v, σ₁ x = some v, by begin
                        cases x_free_in_pre,
                        case free_in_prop.pre₁ x_free_in_f {
                          have : (f = x), from (free_in_term.freevar.inv x_free_in_f).symm,
                          contradiction
                        },
                        case free_in_prop.pre₂ x_free_in_fx {
                          have : (x = fx), from (free_in_term.freevar.inv x_free_in_fx),
                          contradiction
                        }
                      end
                    )
                  )
                  (
                    assume : free_in_prop x (prop.implies (R'.to_prop & prop.post f fx) S'.to_prop),
                    have free_in_prop x (prop.or (R'.to_prop & prop.post f fx).not S'.to_prop), from this,
                    show ∃v, σ₁ x = some v, from sorry
                  )
                }
              end
            )
          )
        )
        (
          assume x_free_in_func: free_in_prop x (f ≡ value.func g fx R S e σ₂),
          show ∃v, σ₁ x = some v, by begin
            cases x_free_in_func,
            case free_in_prop.term x_free_in_eq {
              cases x_free_in_eq,
              case free_in_term.binop₁ free_in_f {
                have f_is_x: (f = x), from (free_in_term.freevar.inv free_in_f).symm,
                contradiction
              },
              case free_in_term.binop₂ free_in_func {
                cases free_in_func
              }
            }
          end
        )
      )
    }
  end

lemma exp.progress{H: list call} {P: prop} {Q: propctx} {e: exp} {σ: env}:
                  ⟪H⟫ → (⊢ σ: P) → (H & P ⊢ e: Q) → is_return (σ, e) ∨ ∃c s', (σ, e) ⟶ c, s'
:=
  assume h_valid: ⟪H⟫,
  assume env_verified: (⊢ σ : P),
  assume e_verified: (H & P ⊢ e : Q),
  show is_return (σ, e) ∨ ∃c s', (σ, e) ⟶ c, s', from begin
    cases e_verified,
    case exp.vcgen.tru x e' { from
      let s: stack := (σ, lett x = true in e') in
      have s ⟶ none, (σ[x↦value.true], e'), from step.tru,
      have ∃c s', s ⟶ c, s', from exists.intro none (exists.intro (σ[x↦value.true], e') this),
      show is_return s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },
    case exp.vcgen.fals x e' { from
      let s: stack := (σ, letf x = false in e') in
      have s ⟶ none, (σ[x↦value.false], e'), from step.fals,
      have ∃c s', s ⟶ c, s', from exists.intro none (exists.intro (σ[x↦value.false], e') this),
      show is_return s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },
    case exp.vcgen.num x n e' { from
      let s: stack := (σ, letn x = n in e') in
      have s ⟶ none, (σ[x↦value.num n], e'), from step.num,
      have ∃c s', s ⟶ c, s', from exists.intro none (exists.intro (σ[x↦value.num n], e') this),
      show is_return s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },
    case exp.vcgen.func f x R S e₁ e₂ { from
      let s: stack := (σ, letf f[x] req R ens S {e₁} in e₂) in
      have s ⟶ none, (σ[f↦value.func f x R S e₁ σ], e₂), from step.closure,
      have ∃c s', s ⟶ c, s', from exists.intro none (exists.intro (σ[f↦value.func f x R S e₁ σ], e₂) this),
      show is_return s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },
    case exp.vcgen.unop op x y e' Q' x_free_in_P _ e'_verified pre_valid { from
      let s: stack := (σ, letop y = op[x] in e') in
      have free_in_prop x H ∨ free_in_prop x P, from free_in_prop.and.inv x_free_in_P,
      have x ∈ FV P, from or.elim this.symm id (
        assume : free_in_prop x H,
        show free_in_prop x P, from absurd this (call_history_closed H x)
      ),
      have ∃v, σ x = some v, from val_of_free_in_env env_verified this,
      let ⟨v, env_has_x⟩ := this in


      have s ⟶ none, (σ[y↦v], e'), from step.unop,
      have ∃c s', s ⟶ c, s', from exists.intro none (exists.intro (σ[y↦v], e') this),
      show is_return s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },


    case exp.vcgen.return a x { from
      let s: stack := (σ, exp.return x) in
      have s_is_return: s = (σ, exp.return x), from rfl,
      have is_return_s: is_return s = (∃(σ': env) (x': var), s = (σ', exp.return x')), by unfold is_return,
      have (∃(σ': env) (x': var), s = (σ', exp.return x')), from exists.intro σ (exists.intro x s_is_return),
      have is_return s, from is_return_s ▸ this,
      show is_return s ∨ ∃c s', s ⟶ c, s', from or.inl this
    }
  end

theorem progress(H: list call) (s: stack): ⟪H⟫ → (H ⊩ s) → is_return s ∨ ∃c s', s ⟶ c, s'
:=
  assume h_valid: ⟪H⟫,
  assume s_verified: H ⊩ s,
  stack.vcgen.rec_on s_verified
  ( -- top
    assume (H: list call) (P: prop) (σ: env) (e: exp) (Q: propctx),
    assume env_verified: (⊢ σ : P),
    assume e_verified: (H & P ⊢ e : Q),
    show is_return (σ, e) ∨ ∃c s', (σ, e) ⟶ c, s', from exp.progress h_valid env_verified e_verified
  )
  ( -- cons
    assume (H: list call) (P: prop) (s': stack) (σ σ': env) (f g x y gx: var) (R S: spec) (e: exp) (vₓ: value) (Q: propctx),
    assume s'_verified: H ⊩ s',
    assume env_verified: ⊢ σ : P,
    assume f_is_func: σ f = value.func g gx R S e σ',
    assume x_is_v: σ x = vₓ,
    assume _,
    assume cont_verified: H & P ⊢ letapp y = f[x] in e : Q,
    assume ih: is_return s' ∨ ∃c s'', s' ⟶ c, s'',
    let s := (s' · [σ, let y = f[x] in e]) in
    have s_cons: s = (s' · [σ, let y = f[x] in e]), from rfl,
    ih.elim
    ( -- step return
      assume s'_is_return: is_return s',
      let ⟨σ₂, z, s'_return⟩ := s'_is_return in
      have s_return_cons: s = ((σ₂, exp.return z) · [σ, let y = f[x] in e]), from s'_return ▸ s_cons,
      have H ⊩ (σ₂, exp.return z), from s'_return ▸ s'_verified,
      have ∃P' Q', (⊢ σ₂: P') ∧ (H & P' ⊢ exp.return z: Q'), from stack.vcgen.top.inv this,
      let ⟨P', Q', ⟨env2_verified, return_verified⟩⟩ := this in
      have z ∈ FV (↑H & P'), from exp.vcgen.return.inv return_verified,
      have free_in_prop z H ∨ free_in_prop z P', from free_in_prop.and.inv this,
      have z ∈ FV P', from or.elim this.symm id (
        assume : free_in_prop z H,
        show free_in_prop z P', from absurd this (call_history_closed H z)
      ),
      have ∃v, σ₂ z = some v, from val_of_free_in_env env2_verified this,
      let ⟨v, env2_has_z⟩ := this in
      have s ⟶ some ⟨g, gx, R, S, e, σ', vₓ, v⟩, (σ[y↦v], e),
      from s_return_cons.symm ▸ (step.return env2_has_z f_is_func x_is_v),
      have ∃s', s ⟶ some ⟨g, gx, R, S, e, σ', vₓ, v⟩, s', from exists.intro (σ[y↦v], e) this,
      have ∃c s', s ⟶ c, s', from exists.intro (some ⟨g, gx, R, S, e, σ', vₓ, v⟩) this,
      show is_return s ∨ ∃c s', s ⟶ c, s', from or.inr this
    )
    ( -- step ctx
      assume s'_can_step: ∃c s'', s' ⟶ c, s'',
      let ⟨c, s'', s'_steps⟩ := s'_can_step in
      have s ⟶ c, (s'' · [σ, let y = f[x] in e]), from step.ctx s'_steps,
      have ∃s', s ⟶ c, s', from exists.intro (s'' · [σ, let y = f[x] in e]) this,
      have ∃c s', s ⟶ c, s', from exists.intro c this,
      show is_return s ∨ ∃c s', s ⟶ c, s', from or.inr this
    )
  )