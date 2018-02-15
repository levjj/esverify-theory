import .syntax .notations .logic .evaluation .vcgen .progress .preservation

theorem soundness {e: exp} {s: stack}:
  (list.nil ⊩ (env.empty, e)) → ((env.empty, e) ⟶* s) → (is_value s ∨ ∃s' h, s ⟶ h, s') :=
  assume initial_verified: (list.nil ⊩ (env.empty, e)),
  assume stepped_to_s: ((env.empty, e) ⟶* s),
  begin
    induction stepped_to_s,
    case trans_step.rfl s_initial {
      let H: list call := list.nil,
      have H_valid: ⟪H⟫, from empty_history_valid,
      show is_value s_initial ∨ ∃s' h, s_initial ⟶ h, s', from progress H H_valid initial_verified
    },
    case trans_step.trans a b c d e f {

    }
  end