import .definitions2 .qi .soundness

-- This theorem states that any proposition `P` that is valid with instantiations `⟪ P ⟫` 
-- is also a valid proposition without quantifier instantiation `⦃ P ⦄`:
theorem vc_valid_without_instantiations (P: prop):
  ⟪ P ⟫ → ⦃ P ⦄

  := @vc_valid_from_inst_valid P -- actual proof in qi.lean


-- This theorem states that a verified source program `e` does not get stuck,
-- i.e. its evaluation always results either in a value or in a runtime stack `s` that can be
-- further evaluated. The proof internally uses lemmas for progress and preservation.
theorem verification_safety (e: exp) (s: stack) (Q: propctx):
  (value.true ⊢ e: Q) → ((env.empty, e) ⟶* s) → (is_value s ∨ ∃s', s ⟶ s')
  
  := @soundness_source_programs e s Q -- actual proof in soundness.lean
