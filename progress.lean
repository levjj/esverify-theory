import .syntax .etc .evaluation .props .vcgen

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
                have x'_is_x: (x' = x), from (free_in_term.freevar.inv free_in_x').symm,
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
                have x'_is_x: (x' = x), from (free_in_term.freevar.inv free_in_x').symm,
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
    case env.vcgen.func σ₁ σ₂ f g fx R S e Q₁ Q₂ Q₃ σ₁_verified σ₂_verified func_verified _ ih₁ ih₂ { from
      val_of_free_in_nonempty_env σ₁_verified (
        assume f_is_not_x: f ≠ x,
        have free_in_prop x (Q₁ & spec.func f fx R S) ∨ free_in_prop x (f ≡ value.func g fx R S e σ₂),
        from free_in_prop.and.inv x_free_in_P,
        or.elim this
        (
          assume x_free_in_Q₁_or_spec: free_in_prop x (Q₁ & spec.func f fx R S),
          have free_in_prop x Q₁ ∨ free_in_prop x (spec.func f fx R S),
          from free_in_prop.and.inv x_free_in_Q₁_or_spec,
          or.elim this
          (
            assume x_free_in_Q₁: free_in_prop x Q₁,
            show ∃v, σ₁ x = some v, from ih₁ x_free_in_Q₁
          )
          (
            assume x_free_in_spec: free_in_prop x (spec.func f fx R S),
            show ∃v, σ₁ x = some v, by begin
              admit
            end
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

theorem progress(H: list call) (s: stack): (H ⊩ s) → is_return s ∨ ∃c s', s ⟶ c, s'
:=
  assume s_verified: H ⊩ s,
  stack.vcgen.rec_on s_verified
  ( -- top
    assume (P₁ P₂: prop) (σ: env) (e: exp) (Q: propctx),
    assume env_verified: (⊢ σ : P₂),
    assume e_verified: (P₁ & P₂ ⊢ e : Q),
    let s := (σ, e) in
    show is_return s ∨ ∃c s', s ⟶ c, s', from sorry
  )
  ( -- cons
    assume (P₁ P₂: prop) (s': stack) (σ σ': env) (f g x y z: var) (R S: spec) (e: exp) (v: value) (Q: propctx),
    assume s'_verified: P₁ ⊩ s',
    assume env_verified: ⊢ σ : P₂,
    assume _,
    assume _,
    assume _,
    assume cont_verified: P₁ & P₂ ⊢ letapp y = f[x] in e : Q,
    assume ih: is_return s' ∨ ∃c s'', s' ⟶ c, s'',
    let s := (s' · [σ, let y = f[x] in e]) in
    have s_cons: s = (s' · [σ, let y = f[x] in e]), from rfl,
    ih.elim
    (
      assume s'_is_return: is_return s',
      let ⟨σ₂, z, s'_return⟩ := s'_is_return in
      have s_return_cons: s = ((σ₂, exp.return z) · [σ, let y = f[x] in e]), from s'_return ▸ s_cons,
      have P₁ ⊩ (σ₂, exp.return z), from s'_return ▸ s'_verified,
      have ∃P₂' Q', (⊢ σ₂: P₂') ∧ (P₁ & P₂' ⊢ exp.return z: Q'), from stack.vcgen.top.inv this,
      let ⟨P₂', Q', ⟨env2_verified, return_verified⟩⟩ := this in
      have z ∈ FV (P₁ & P₂'), from exp.vcgen.return.inv return_verified,

      have v: value, from sorry,
      have σ₂ z = v, from sorry,

      have s ⟶ some ⟨f, x, y⟩, (σ[y↦v], e), from s_return_cons.symm ▸ step.return this,
      have ∃s', s ⟶ some ⟨f, x, y⟩, s', from exists.intro (σ[y↦v], e) this,
      have ∃c s', s ⟶ c, s', from exists.intro (some ⟨f, x, y⟩) this,
      show is_return s ∨ ∃c s', s ⟶ c, s', from or.inr this
    )
    (
      assume s'_can_step: ∃c s'', s' ⟶ c, s'',
      let ⟨c, s'', s'_steps⟩ := s'_can_step in
      have s ⟶ c, (s'' · [σ, let y = f[x] in e]), from step.ctx s'_steps,
      have ∃s', s ⟶ c, s', from exists.intro (s'' · [σ, let y = f[x] in e]) this,
      have ∃c s', s ⟶ c, s', from exists.intro c this,
      show is_return s ∨ ∃c s', s ⟶ c, s', from or.inr this
    )
  )