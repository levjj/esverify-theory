import data.set

import .syntax .notations .logic .evaluation .vcgen .progress .preservation

lemma trivial_freevars: FV (prop.term value.true ⋀ prop.term value.true) = FV (prop.term value.true) :=
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

lemma trivial_precondition:
  ∀σ, σ ⊨ vc.implies (prop.instantiated_n (value.true ⋀ value.true)) (prop.instantiated_n (value.true)) :=
  assume σ: env,
  show σ ⊨ vc.implies (prop.instantiated_n (value.true ⋀ value.true)) (prop.instantiated_n (value.true)),
  from valid_env.mpr (
    assume _,
    have h: σ ⊨ value.true, from valid_env.true,
    have prop.erased (prop.term value.true) = vc.term value.true, by unfold prop.erased,
    have σ ⊨ (prop.erased (value.true)), from this.symm ▸ h,
    have σ ⊨ (prop.instantiated (value.true)), from valid_env.instantiated_of_erased this,
    show σ ⊨ (prop.instantiated_n (value.true)), from valid_env.instantiated_n_of_instantiated this
  )

lemma trivial_calls: calls (prop.term value.true ⋀ prop.term value.true) = calls (prop.term value.true) :=
  have h1: calls (prop.term value.true ⋀ prop.term value.true) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls (prop.term value.true ⋀ prop.term value.true),
    have c ∈ calls (prop.term value.true) ∨ c ∈ calls (prop.term value.true), from prop.has_call.and.inv this,
    or.elim this (
      assume : c ∈ calls (prop.term value.true),
      show «false», from prop.has_call.term.inv this
    ) (
      assume : c ∈ calls (prop.term value.true),
      show «false», from prop.has_call.term.inv this
    )
  ),
  have h2: calls (prop.term value.true) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls (prop.term value.true),
    show «false», from prop.has_call.term.inv this
  ),
  show calls (prop.term value.true ⋀ prop.term value.true) = calls (prop.term value.true), from eq.trans h1 h2.symm

lemma trivial_dominates {σ: env}: dominates σ (prop.term value.true ⋀ prop.term value.true) (prop.term value.true) :=
  let P:prop := prop.term value.true ⋀ prop.term value.true in
  let P':prop := prop.term value.true in

  have h_impl: σ ⊨ vc.implies P.instantiated_n P'.instantiated_n, from trivial_precondition σ,

  have calls_env σ P = (calltrigger.subst σ) '' calls (prop.term value.true ⋀ prop.term value.true), from rfl,
  have h1: calls_env σ P = (calltrigger.subst σ) '' calls (prop.term value.true), from trivial_calls ▸ this,
  have h2: calls_env σ P' = (calltrigger.subst σ) '' calls (prop.term value.true), from rfl,
  have h_calls: calls_env σ P = calls_env σ P', from eq.trans h1 h2.symm,

  have h_quantifiers:
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v]))), from (
    assume (t': term) (x:var) (Q': prop),
    assume h3: callquantifier.mk t' x Q' ∈ quantifiers P',
    have h4: callquantifier.mk t' x Q' ∉ quantifiers P', from prop.has_quantifier.term.inv,
    absurd h3 h4
  ),

  have h3: 
    ((σ ⊨ vc.implies P.instantiated_n P'.instantiated_n) ∧
    (calls_env σ P = calls_env σ P') ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v])))),
  from ⟨h_impl, ⟨h_calls, h_quantifiers⟩⟩,
  have
    dominates' P' P σ = (
    ((σ ⊨ vc.implies P.instantiated_n P'.instantiated_n) ∧
    (calls_env σ P = calls_env σ P') ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v]))))),
  by unfold1 dominates',
  have dominates' P' P σ, from this.symm ▸ h3,
  show dominates σ P P', from this

lemma soundness {s s': stack}: (s ⟶* s') → ∀H, (H ⊢ₛ s) → (is_value s' ∨ ∃h s'', s' ⟶ h, s'') :=
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
      have : (h :: H ⊢ₛ s₂), from preservation s₁_verified s₁_steps_to_s₂,
      show is_value s₃ ∨ ∃h s', s₃ ⟶ h, s', from ih (h::H) this
    }
  end

theorem soundness_source_programs {e: exp} {s: stack} {Q: propctx}:
  (value.true ⊢ e: Q) → ((env.empty, e) ⟶* s) → (is_value s ∨ ∃h s', s ⟶ h, s') :=

  assume initial_verified: value.true ⊢ e: Q,
  assume steps_to_s: (env.empty, e) ⟶* s,
  have (prop.term value.true ⋀ prop.term value.true) ⊢ e: Q,
  from strengthen_exp initial_verified (prop.term value.true ⋀ prop.term value.true)
       trivial_freevars (λσ, trivial_dominates),
  have list.nil ⊢ₛ (env.empty, e), from stack.vcgen.top env.vcgen.empty this,
  show is_value s ∨ ∃h s', s ⟶ h, s', from soundness steps_to_s list.nil this
