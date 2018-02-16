import .syntax .notations .logic .evaluation .vcgen

lemma strengthen_pre_exp {P P': prop} {Q: propctx} {e: exp}:
  (P ⊢ e : Q) → FV P' ⊆ FV P → (∀σ, σ ⊨ vc.implies P'.instantiated_n P.instantiated_n) → (P' ⊢ e: Q) :=
  sorry

theorem preservation {H: callhistory} {h: historyitem} {s s': stack}:
  (H ⊩ s) → (s ⟶ h, s') → (h :: H ⊩ s')
:= sorry
