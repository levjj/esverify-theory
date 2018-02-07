import .syntax .etc .evaluation .props .vcgen

def is_return(s: stack): Prop := ∃(σ: env) (x: var), s = (σ, exp.return x)

theorem progress(P: prop) (s: stack): ⟪P⟫ ∧ (P ⊩ s) → is_return s ∨ ∃c s', s ⟶ c, s' :=
  assume ⟨P_valid, s_verified⟩,
  stack.vcgen.rec_on s_verified
  ( -- top
    assume P₁ P₂: prop,
    assume σ: env,
    assume e: exp,
    assume Q: propctx,
    assume env_verified: (⊢ σ : P₂),
    assume e_verified: (P₁ & P₂ ⊢ e : Q),
    let s := (σ, e) in
    show is_return s ∨ ∃c s', s ⟶ c, s', from sorry
  )
  ( -- cons
    assume P₁ P₂: prop,
    assume s': stack,
    assume σ: env,
    assume f x y: var,
    assume e: exp,
    assume Q: propctx,
    assume s'_verified: P₁ ⊩ s',
    assume env_verified: ⊢ σ : P₂,
    assume cont_verified: P₁ & P₂ ⊢ letapp y = f[x] in e : Q,
    assume ih: is_return s' ∨ ∃c s'', s' ⟶ c, s'',
    let s := (s' · [σ, let y = f[x] in e]) in
    have s_cons: s = (s' · [σ, let y = f[x] in e]), from rfl,
    ih.elim
    (
      assume s'_is_return: is_return s',
      let ⟨σ₂, z, s'_return⟩ := s'_is_return in
      have s = ((σ₂, exp.return z) · [σ, let y = f[x] in e]), from s'_return ▸ s_cons,
      have s ⟶ some ⟨f, x, y⟩, (σ[y↦v], e)), from step.return sorry,
      have s ⟶ c, (s'' · [σ, let y = f[x] in e]), from step.ctx s'_steps,
      have ∃s', s ⟶ c, s', from exists.intro (s'' · [σ, let y = f[x] in e]) this,
      have ∃c s', s ⟶ c, s', from exists.intro c this,
      show is_return s ∨ ∃c s', s ⟶ c, s', from sorry
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