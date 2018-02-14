import .syntax .notations .evaluation .substitution .qi

-- validity

constant valid : vc → Prop
notation `⊨` p: 100 := valid p
notation σ `⊨` p: 100 := valid (vc.subst_env σ p)
@[reducible]
def VC(P: prop) := ∀ (σ: env), σ ⊨ P.instantiated
notation `⟪` P `⟫`: 100 := VC P

-- axioms

axiom valid.tru:
  ⊨ value.true

axiom valid.unop {op: unop} {vₓ v: value}:
  unop.apply op vₓ = some v
  ↔
  ⊨ (term.unop op vₓ ≡ v)

axiom valid.binop {op: binop} {v₁ v₂ v: value}:
  binop.apply op v₁ v₂ = some v
  ↔
  ⊨ (term.binop op v₁ v₂ ≡ v)

axiom valid.app {vₓ v: value} {σ σ': env} {f x y: var} {R S: spec} {e: exp}:
  (σ[x↦vₓ], e) ⟶* (σ', exp.return y) ∧
  (σ' y = some v)
  ↔
  ⊨ (term.app (value.func f x R S e σ) vₓ ≡ v)

axiom valid.and {P Q: vc}:
  ⊨ P ∧
  ⊨ Q
  ↔
  ⊨ (P && Q)

axiom valid.or {P Q: vc}:
  (⊨ P ∨ ⊨ Q)
  ↔
  ⊨ (P || Q)

axiom valid.mp  {P Q: vc}:
  (⊨ P → ⊨ Q)
  ↔
  ⊨ vc.implies P Q

axiom valid.pre {vₓ: value} {σ: env} {f x y: var} {R S: spec} {e: exp}:
  ⊨ vc.subst_env (σ[x↦vₓ][f↦value.func f x R S e σ]) R.to_prop.instantiated
  ↔
  ⊨ vc.pre (value.func f x R S e σ) vₓ

axiom valid.pre₁ {vₓ v: value} {op: unop}:
  (∃v, unop.apply op vₓ = some v)
  ↔
  ⊨ vc.pre₁ op vₓ

axiom valid.pre₂ {v₁ v₂ v: value} {op: binop}:
  (∃v, binop.apply op v₁ v₂ = v)
  ↔
  ⊨ vc.pre₂ op v₁ v₂

axiom valid.post {vₓ: value} {σ σ': env} {f x y: var} {R S: spec} {e: exp}:
  (σ[x↦vₓ], e) ⟶* (σ', exp.return y) ∧
  ⊨ vc.subst_env (σ[x↦vₓ][f↦value.func f x R S e σ]) (spec.implies R S).to_prop.instantiated
  ↔
  ⊨ vc.post (value.func f x R S e σ) vₓ

axiom valid.univ {x: var} {P: vc}:
  (∀v, ⊨ vc.subst x v P)
  ↔
  ⊨ vc.univ x P

axiom valid.subst {t₁ t₂: term} (Q: propctx):
  ⊨ (t₁ ≡ t₂) →
  ⊨ (Q t₁).instantiated →
  ⊨ (Q t₂).instantiated

axiom valid.eq.symm {t₁ t₂: term}:
  ⊨ (t₁ ≡ t₂) →
  ⊨ (t₂ ≡ t₁)

axiom instantiated_of_erased {P: prop}:
  ⊨ P.erased →
  ⊨ P.instantiated

axiom instantiated_n_of_instantiated {P: prop}:
  ⊨ P.instantiated →
  ⊨ P.instantiated_n

axiom erased_n_of_instantiated_n {P: prop}:
  ⊨ P.instantiated_n → ⊨ P.erased_n

axiom instantiated_and {P Q: prop}:
  ⊨ (P.instantiated && Q.instantiated) → ⊨ (P && Q).instantiated

axiom instantiated_or {P Q: prop}:
  ⊨ (P.instantiated || Q.instantiated) → ⊨ (P || Q).instantiated

-- lemmas

lemma valid.refl {v: value}: ⊨ (v ≡ v) :=
  have binop.apply binop.eq v v = @ite (v = v)
                                  (classical.prop_decidable (v = v))
                                  value value.true value.false, by unfold binop.apply,
  have binop.apply binop.eq v v = value.true, by simp[this],
  have ⊨ ((v ≡ v) ≡ value.true), from valid.binop.mp this,
  have h: ⊨ (value.true ≡ (v ≡ v)), from valid.eq.symm this,
  have h2: ⊨ vc.term value.true, from valid.tru,
  let Q:propctx := propctx.term • in
  have h3: Q value.true = value.true, by refl,
  have (prop.term value.true).erased = vc.term value.true, by unfold prop.erased,
  have (Q value.true).erased = vc.term value.true, from h3 ▸ this,
  have ⊨ (Q value.true).erased, from this ▸ h2,
  have ⊨ (Q value.true).instantiated, from instantiated_of_erased this,
  have ⊨ (Q (v ≡ v)).instantiated, from valid.subst Q h this,
  have ⊨ (Q (v ≡ v)).instantiated_n, from instantiated_n_of_instantiated this,
  have h7: ⊨ (Q (v ≡ v)).erased_n, from erased_n_of_instantiated_n this,
  have Q (v ≡ v) = prop.term (v ≡ v), by refl,
  have h8: ⊨ (prop.term (v ≡ v)).erased_n, from this ▸ h7,
  have (prop.term (v ≡ v)).erased = vc.term (v ≡ v), by unfold prop.erased,
  show ⊨ (v ≡ v), from this ▸ h8

lemma valid_env.and {σ: env} {P Q: vc}: σ ⊨ P → σ ⊨ Q → σ ⊨ (P && Q) :=
  assume p_valid: ⊨ vc.subst_env σ P,
  assume q_valid: ⊨ vc.subst_env σ Q,
  have vc.subst_env σ (P && Q) = (vc.subst_env σ P && vc.subst_env σ Q), from vc.subst_env.and,
  show σ ⊨ (P && Q), from this.symm ▸ valid.and.mp ⟨p_valid, q_valid⟩

lemma valid_env.mp {σ: env} {P Q: vc}: σ ⊨ vc.implies P Q → σ ⊨ P → σ ⊨ Q :=
  assume impl: σ ⊨ (vc.implies P Q),
  assume p: σ ⊨ P,
  have vc.subst_env σ (vc.implies P Q) = (vc.subst_env σ P.not || vc.subst_env σ Q), from vc.subst_env.or,
  have h: ⊨ (vc.subst_env σ P.not || vc.subst_env σ Q), from this ▸ impl,
  have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  have ⊨ ((vc.subst_env σ P).not || vc.subst_env σ Q), from this ▸ h,
  have ⊨ vc.implies (vc.subst_env σ P) (vc.subst_env σ Q), from this,
  show σ ⊨ Q, from valid.mp.mpr this p
