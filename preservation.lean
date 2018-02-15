import .syntax .notations .logic .evaluation .vcgen

theorem preservation {H: list call} {h: call} {s s': stack}:
  (H ⊩ s) → (s ⟶ h, s') → (h :: H ⊩ s') ∧ ⟪[h]⟫
:= sorry
