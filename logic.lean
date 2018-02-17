import .syntax .notations .evaluation .substitution .qi

-- validity is axiomatized instead of specified

constant valid : vc → Prop
notation `⊨` p: 100 := valid p
notation σ `⊨` p: 100 := valid (vc.subst_env σ p)

-- notation ⟪ P ⟫

@[reducible]
def VC(P: prop) := ∀ (σ: env), σ ⊨ P.instantiated
notation `⟪` P `⟫`: 100 := VC P

-- simple axioms for logical reasoning

axiom valid.tru:
  ⊨ value.true

axiom valid.and {P Q: vc}:
  (⊨ P ∧ ⊨ Q)
  ↔
  ⊨ (P && Q)

axiom valid.or {P Q: vc}:
  (⊨ P ∨ ⊨ Q)
  ↔
  ⊨ (P || Q)

axiom valid.implies  {P Q: vc}:
  (⊨ P → ⊨ Q)
  ↔
  ⊨ vc.implies P Q

axiom valid.univ {x: var} {P: vc}:
  (∀v, ⊨ vc.subst x v P)
  ↔
  ⊨ vc.univ x P

-- axioms for equality

-- a term is valid if it equals true
axiom valid.eq.true {t: term}:
  ⊨ t
  ↔
  ⊨ (t ≡ value.true)

-- unary and binary operators are decidable, so equalities with operators are decidable
axiom valid.eq.unop {op: unop} {vₓ v: value}:
  unop.apply op vₓ = some v
  ↔
  ⊨ (term.unop op vₓ ≡ v)

axiom valid.eq.binop {op: binop} {v₁ v₂ v: value}:
  binop.apply op v₁ v₂ = some v
  ↔
  ⊨ (term.binop op v₁ v₂ ≡ v)

-- The following equality axiom is non-standard and makes validity undecidable.
-- It is only used in the preservation proof of e-return and in no other lemmas.
-- The logic treats `f(x)` uninterpreted, so there is no way to derive it naturally.
-- However, given a complete evaluation derivation of a function call, we can add the
-- equality `f(x)=y` as new axiom for closed values f, x, y and the resulting set
-- of axioms is still sound due to deterministic evaluation.
axiom valid.eq.app {vₓ v: value} {σ σ': env} {f x y: var} {R S: spec} {e: exp}:
  (σ[x↦vₓ], e) ⟶* (σ', exp.return y) ∧
  (σ' y = some v)
  →
  ⊨ (term.app (value.func f x R S e σ) vₓ ≡ v)

-- can write pre₁ and pre₂ to check domain of operators

axiom valid.pre₁ {vₓ: value} {op: unop}:
  option.is_some (unop.apply op vₓ)
  ↔
  ⊨ vc.pre₁ op vₓ

axiom valid.pre₂ {v₁ v₂: value} {op: binop}:
  option.is_some (binop.apply op v₁ v₂)
  ↔
  ⊨ vc.pre₂ op v₁ v₂

-- can write pre and post to extract pre- and postcondition of function values

axiom valid.pre {vₓ: value} {σ: env} {f x: var} {R S: spec} {e: exp}:
  ⊨ vc.subst_env (σ[x↦vₓ][f↦value.func f x R S e σ]) R.to_prop.instantiated
  ↔
  ⊨ vc.pre (value.func f x R S e σ) vₓ

axiom valid.post {vₓ: value} {σ σ': env} {f x y: var} {R S: spec} {e: exp}:
  ⊨ vc.subst_env (σ[x↦vₓ][f↦value.func f x R S e σ]) S.to_prop.instantiated
  ↔
  ⊨ vc.post (value.func f x R S e σ) vₓ

-- axioms about instantiations

--  inst(P)   ⇒   inst_n(P)
--         ⇘    ⇗  
--     ⇑      P      ⇓
--         ⇗    ⇘ 
-- erased(P)     erased_n(P)

axiom valid_env.instantiated_of_erased {σ: env} {P: prop}:
  σ ⊨ P.erased →
  σ ⊨ P.instantiated

axiom valid_env.instantiated_n_of_instantiated {σ: env} {P: prop}:
  σ ⊨ P.instantiated →
  σ ⊨ P.instantiated_n

axiom valid_env.erased_n_of_instantiated_n {σ: env} {P: prop}:
  σ ⊨ P.instantiated_n →
  σ ⊨ P.erased_n

-- if a conjunction or disjunciton is valid without cross-instantiations
-- then it remains valid, as potential new instantiations are in negative positions
axiom valid_env.instantiated_and {σ: env} {P Q: prop}:
  σ ⊨ (P.instantiated && Q.instantiated) →
  σ ⊨ (P && Q).instantiated

axiom valid_env.instantiated_or {σ: env} {P Q: prop}:
  σ ⊨ (P.instantiated || Q.instantiated) →
  σ ⊨ (P || Q).instantiated

-- if P and P' have the exact same triggers and quantifiers, then
-- any instantiation with an arbitrary propostion Q are also the same,
-- so if (P') implies (P) without cross-instantiations,
-- then (P' ∧ Q) implies (P ∧ Q) without cross-instantiations
axiom valid_env.strengthen_without_instantiations {σ: env} {P P' Q: prop}:
  (calls P = calls P') →
  (quantifiers P = quantifiers P') →
  σ ⊨ vc.implies P'.instantiated_n P.instantiated_n →
  σ ⊨ vc.implies (P' && Q).instantiated_n (P && Q).instantiated_n

-- lemmas

lemma instantiated_of_erased {P: prop}: ⊨ P.erased → ⊨ P.instantiated :=
  assume h: ⊨ P.erased,
  have P.erased = vc.subst_env env.empty P.erased, by unfold vc.subst_env,
  have env.empty ⊨ P.erased, from this ▸ h,
  have h2: env.empty ⊨ P.instantiated, from valid_env.instantiated_of_erased this,
  have  vc.subst_env env.empty P.instantiated = P.instantiated, by unfold vc.subst_env,
  show ⊨ P.instantiated, from this ▸ h2

lemma instantiated_n_of_instantiated {P: prop}: ⊨ P.instantiated → ⊨ P.instantiated_n :=
  assume h: ⊨ P.instantiated,
  have P.instantiated = vc.subst_env env.empty P.instantiated, by unfold vc.subst_env,
  have env.empty ⊨ P.instantiated, from this ▸ h,
  have h2: env.empty ⊨ P.instantiated_n, from valid_env.instantiated_n_of_instantiated this,
  have  vc.subst_env env.empty P.instantiated_n = P.instantiated_n, by unfold vc.subst_env,
  show ⊨ P.instantiated_n, from this ▸ h2

lemma erased_n_of_instantiated_n {P: prop}: ⊨ P.instantiated_n → ⊨ P.erased_n :=
  assume h: ⊨ P.instantiated_n,
  have P.instantiated_n = vc.subst_env env.empty P.instantiated_n, by unfold vc.subst_env,
  have env.empty ⊨ P.instantiated_n, from this ▸ h,
  have h2: env.empty ⊨ P.erased_n, from valid_env.erased_n_of_instantiated_n this,
  have vc.subst_env env.empty P.erased_n = P.erased_n, by unfold vc.subst_env,
  show ⊨ P.erased_n, from this ▸ h2

lemma valid.refl {v: value}: ⊨ (v ≡ v) :=
  have binop.apply binop.eq v v = @ite (v = v)
                                  (classical.prop_decidable (v = v))
                                  value value.true value.false, by unfold binop.apply,
  have binop.apply binop.eq v v = value.true, by simp[this],
  have ⊨ ((v ≡ v) ≡ value.true), from valid.eq.binop.mp this,
  show ⊨ (v ≡ v), from valid.eq.true.mpr this

lemma valid_env.true {σ: env}: σ ⊨ value.true :=
  have h1: ⊨ value.true, from valid.tru,
  have term.subst_env σ value.true = value.true, from term.subst_env.value,
  have h2: ⊨ term.subst_env σ value.true, from this.symm ▸ h1,
  have vc.subst_env σ value.true = vc.term (term.subst_env σ value.true), from vc.subst_env.term,
  show σ ⊨ value.true, from this.symm ▸ h2

lemma valid_env.and {σ: env} {P Q: vc}: σ ⊨ P → σ ⊨ Q → σ ⊨ (P && Q) :=
  assume p_valid: ⊨ vc.subst_env σ P,
  assume q_valid: ⊨ vc.subst_env σ Q,
  have vc.subst_env σ (P && Q) = (vc.subst_env σ P && vc.subst_env σ Q), from vc.subst_env.and,
  show σ ⊨ (P && Q), from this.symm ▸ valid.and.mp ⟨p_valid, q_valid⟩

lemma valid_env.and.elim {σ: env} {P Q: vc}: σ ⊨ (P && Q) → σ ⊨ P ∧ σ ⊨ Q :=
  assume p_and_q_valid: ⊨ vc.subst_env σ (P && Q),
  have vc.subst_env σ (P && Q) = (vc.subst_env σ P && vc.subst_env σ Q), from vc.subst_env.and,
  have ⊨ (vc.subst_env σ P && vc.subst_env σ Q), from this ▸ p_and_q_valid,
  show σ ⊨ P ∧ σ ⊨ Q, from valid.and.mpr this

lemma valid_env.mp {σ: env} {P Q: vc}: σ ⊨ vc.implies P Q → σ ⊨ P → σ ⊨ Q :=
  assume impl: σ ⊨ (vc.implies P Q),
  assume p: σ ⊨ P,
  have vc.subst_env σ (vc.implies P Q) = (vc.subst_env σ P.not || vc.subst_env σ Q), from vc.subst_env.or,
  have h: ⊨ (vc.subst_env σ P.not || vc.subst_env σ Q), from this ▸ impl,
  have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  have ⊨ ((vc.subst_env σ P).not || vc.subst_env σ Q), from this ▸ h,
  have ⊨ vc.implies (vc.subst_env σ P) (vc.subst_env σ Q), from this,
  show σ ⊨ Q, from valid.implies.mpr this p

lemma valid_env.mpr {σ: env} {P Q: vc}: (σ ⊨ P → σ ⊨ Q) → σ ⊨ vc.implies P Q :=
  assume : (σ ⊨ P → σ ⊨ Q),
  have ⊨ vc.implies (vc.subst_env σ P) (vc.subst_env σ Q), from valid.implies.mp this,
  have h1: ⊨ vc.or (vc.subst_env σ P).not (vc.subst_env σ Q), from this,
  have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  have h2: ⊨ vc.or (vc.subst_env σ P.not) (vc.subst_env σ Q), from this.symm ▸ h1,
  have vc.subst_env σ (P.not || Q) = vc.subst_env σ P.not || vc.subst_env σ Q,
  from vc.subst_env.or,
  have ⊨ vc.subst_env σ (P.not || Q), from this.symm ▸ h2,
  show σ ⊨ vc.implies P Q, from this
