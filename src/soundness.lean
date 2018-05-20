import .definitions3 .progress .preservation

lemma true_true_freevars: FV (prop.term value.true ⋀ prop.term value.true) = FV (prop.term value.true) :=
  have h1: FV (prop.term value.true ⋀ prop.term value.true) = ∅, from set.eq_empty_of_forall_not_mem (
    assume x: var,
    assume : x ∈ FV (prop.term value.true ⋀ prop.term value.true),
    have x ∈ FV (prop.term value.true) ∨ x ∈ FV (prop.term value.true), from free_in_prop.and.inv this,
    or.elim this (
      assume : x ∈ FV (prop.term value.true),
      have x ∈ FV (term.value value.true), from free_in_prop.term.inv this,
      show «false», from free_in_term.value.inv this
    ) (
      assume : x ∈ FV (prop.term value.true),
      have x ∈ FV (term.value value.true), from free_in_prop.term.inv this,
      show «false», from free_in_term.value.inv this
    )
  ),
  have h2: FV (prop.term value.true) = ∅, from set.eq_empty_of_forall_not_mem (
    assume x: var,
    assume : x ∈ FV (prop.term value.true),
    have x ∈ FV (term.value value.true), from free_in_prop.term.inv this,
    show «false», from free_in_term.value.inv this
  ),
  show FV (prop.term value.true ⋀ prop.term value.true) = FV (prop.term value.true), from eq.trans h1 h2.symm

lemma true_true_implies_true {σ: env}:
      σ ⊨ vc.implies (prop.term value.true ⋀ prop.term value.true).to_vc (prop.term value.true).to_vc :=
  begin
    apply valid_env.mpr,
    assume h1,
    unfold prop.to_vc,
    from valid_env.true
  end

lemma true_spec_freevars: FV (spec.to_prop (spec.term value.true)) ⊆ FV (prop.term value.true) :=
  begin
    assume x,
    assume h1,
    unfold spec.to_prop at h1,
    have h2, from free_in_prop.term.inv h1,
    have h3: ¬ free_in_term x ↑value.true, from free_in_term.value.inv,
    contradiction
  end

lemma true_spec_valid: env.empty ⊨ prop.to_vc (spec.to_prop (spec.term ↑value.true)) :=
  begin
    unfold vc.subst_env,
    unfold spec.to_prop,
    unfold prop.to_vc,
    from valid.tru
  end

lemma dsoundness {s s': dstack} {Q: propctx}: (s ⟹* s') → (⊩ₛ s: Q) → (is_dvalue s' ∨ ∃s'', s' ⟹ s'') :=
  begin
    have : ∀{s s': dstack} {Q: propctx}, (s ⟹* s') → (⊩ₛ s: Q) → (∃Q': propctx, ⊩ₛ s' : Q'), by begin
      assume s s' Q steps_to_s',
      induction steps_to_s',
      case trans_dstep.rfl s₁ {
        assume s₁_verified,
        existsi Q,
        from s₁_verified
      },
      case trans_dstep.trans s₁ s₂ s₃ s₁_steps_to_s₂ s₂_steps_to_s₃ ih {
        assume s₁_verified,
        cases ih s₁_verified with Q₂ h1,
        cases preservation h1 s₃ s₂_steps_to_s₃ with Q₃ h2,
        from exists.intro Q₃ h2.left
      }
    end,
    assume h1 h2,
    cases this h1 h2 with Q' h3,
    from progress h3
  end

lemma soundness_source_programs {e: exp} {s: stack} {Q: propctx}:
  (value.true ⊢ e: Q) → ((env.empty, e) ⟶* s) → (is_value s ∨ ∃s', s ⟶ s') :=
  assume : value.true ⊢ e: Q,
  have value.true ⊩ e: Q, from exp.vcgen.extension this,
  have value.true ⋀ value.true ⊩ e : Q,
  from strengthen_exp this (value.true ⋀ value.true) true_true_freevars (λσ, true_true_implies_true),
  have h1: ⊩ₛ (spec.term value.true, env.empty, e) : value.true ⋀ Q,
  from stack.dvcgen.top env.dvcgen.empty true_spec_freevars true_spec_valid this,
  assume : (env.empty, e) ⟶* s,
  have ∃d', ((spec.term value.true, env.empty, e) ⟹* d') ∧ stack_equiv_dstack s d',
  from dstep_of_step_trans this (spec.term value.true, env.empty, e) stack_equiv_dstack.top,
  let ⟨d', h2⟩ := this in
  have is_dvalue d' ∨ ∃d'', d' ⟹ d'', from dsoundness h2.left h1,
  show is_value s ∨ ∃s', s ⟶ s', from value_or_step_of_dvalue_or_dstep h2.right this
