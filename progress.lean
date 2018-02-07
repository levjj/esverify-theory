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

lemma stack.vcgen.top.inv {P: prop} {σ: env} {e: exp}: (P ⊩ (σ, e)) → ∃P₂ Q, (⊢ σ: P₂) ∧ (P & P₂ ⊢ e: Q) :=
  assume top_verified: P ⊩ (σ, e),
  begin
    cases top_verified,
    case stack.vcgen.top P₂ Q env_verified e_verified { from
      have (⊢ σ: P₂) ∧ (P & P₂ ⊢ e: Q), from ⟨env_verified, e_verified⟩,
      show ∃P₂ Q, (⊢ σ: P₂) ∧ (P & P₂ ⊢ e: Q), from exists.intro P₂ $ exists.intro Q this
    }
  end

theorem progress(P: prop) (s: stack): ⟪P⟫ ∧ (P ⊩ s) → is_return s ∨ ∃c s', s ⟶ c, s'
:=
  assume ⟨P_valid, s_verified⟩,
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