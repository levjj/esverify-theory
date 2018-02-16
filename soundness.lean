import data.set

import .syntax .notations .logic .evaluation .vcgen .progress .preservation

lemma trivial_precondition:
  ∀σ, σ ⊨ vc.implies (prop.instantiated_n (value.true && value.true)) (prop.instantiated_n (value.true)) :=
  assume σ: env,
  show σ ⊨ vc.implies (prop.instantiated_n (value.true && value.true)) (prop.instantiated_n (value.true)),
  from valid_env.mpr (
    assume _,
    have h: σ ⊨ value.true, from valid_env.true,
    have prop.erased (prop.term value.true) = vc.term value.true, by unfold prop.erased,
    have σ ⊨ (prop.erased (value.true)), from this.symm ▸ h,
    have σ ⊨ (prop.instantiated (value.true)), from valid_env.instantiated_of_erased this,
    show σ ⊨ (prop.instantiated_n (value.true)), from valid_env.instantiated_n_of_instantiated this
  )

lemma trivial_freevars: FV (prop.term value.true && prop.term value.true) ⊆ FV (prop.term value.true) :=
  assume x: var,
  assume : x ∈ FV (prop.term value.true && prop.term value.true),
  have x ∈ FV (prop.term value.true) ∨ x ∈ FV (prop.term value.true), from free_in_prop.and.inv this,
  or.elim this (
    assume : x ∈ FV (prop.term value.true),
    have x ∈ FV (term.value value.true), from free_in_prop.term.inv this,
    show x ∈ FV (prop.term value.true), from absurd this free_in_term.value.inv
  ) (
    assume : x ∈ FV (prop.term value.true),
    have x ∈ FV (term.value value.true), from free_in_prop.term.inv this,
    show x ∈ FV (prop.term value.true), from absurd this free_in_term.value.inv
  )

lemma soundness {s s': stack}: (s ⟶* s') → ∀H, (H ⊩ s) → (is_value s' ∨ ∃h s'', s' ⟶ h, s'') :=
  assume steps_to_s': s ⟶* s',
  begin
    induction steps_to_s',
    case trans_step.rfl s₁ {
      assume H,
      assume s₁_verified ,
      show is_value s₁ ∨ ∃h s', s₁ ⟶ h, s', from progress H s₁ s₁_verified
    },
    case trans_step.trans s₁ s₂ s₃ h s₁_steps_to_s₂ s₂_steps_to_s₃ ih {
      assume H,
      assume s₁_verified ,
      have : (h :: H ⊩ s₂), from preservation s₁_verified s₁_steps_to_s₂,
      show is_value s₃ ∨ ∃h s', s₃ ⟶ h, s', from ih (h::H) this
    }
  end

theorem soundness_source_programs {e: exp} {s: stack} {Q: propctx}:
  (value.true ⊢ e: Q) → ((env.empty, e) ⟶* s) → (is_value s ∨ ∃h s', s ⟶ h, s') :=

  assume initial_verified: value.true ⊢ e: Q,
  assume steps_to_s: (env.empty, e) ⟶* s,
  have (prop.term value.true && prop.term value.true) ⊢ e: Q,
  from strengthen_pre_exp initial_verified trivial_freevars trivial_precondition,
  have list.nil ⊩ (env.empty, e), from stack.vcgen.top env.vcgen.empty this,
  show is_value s ∨ ∃h s', s ⟶ h, s', from soundness steps_to_s list.nil this
