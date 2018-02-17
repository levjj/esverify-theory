import data.set

import .syntax .notations .logic .evaluation .vcgen .progress .preservation

theorem soundness {e: exp} {s: stack} {Q: propctx}:
  (value.true ⊢ e: Q) → ((env.empty, e) ⟶* s) → (is_value s ∨ ∃s', s ⟶ s') :=

  assume initial_verified: value.true ⊢ e: Q,
  assume steps_to_s: (env.empty, e) ⟶* s,
  have h: ⊢ₛ (env.empty, e), from stack.vcgen.top env.vcgen.empty initial_verified,
  begin
    induction steps_to_s,
    case trans_step.rfl s₁ {
      show is_value s₁ ∨ ∃s', s₁ ⟶ s', from progress h
    },
    case trans_step.trans s₁ s₂ s₃ s₁_steps_to_s₂ s₂_steps_to_s₃ ih {
      have : ⊢ₛ s₂, from preservation h s₁_steps_to_s₂,
      show is_value s₃ ∨ ∃s', s₃ ⟶ s', from ih this
    }
  end
