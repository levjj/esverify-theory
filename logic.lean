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

axiom valid.pre₁ {vₓ: value} {op: unop}:
  (∃v, unop.apply op vₓ = some v)
  ↔
  ⊨ vc.pre₁ op vₓ

axiom valid.pre₂ {v₁ v₂: value} {op: binop}:
  (∃v, binop.apply op v₁ v₂ = some v)
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

axiom valid.eq.true {t: term}:
  ⊨ (t ≡ value.true)
  ↔
  ⊨ t

axiom instantiated_of_erased {σ: env} {P: prop}:
  σ ⊨ P.erased →
  σ ⊨ P.instantiated

axiom instantiated_n_of_instantiated {σ: env} {P: prop}:
  σ ⊨ P.instantiated →
  σ ⊨ P.instantiated_n

axiom erased_n_of_instantiated_n {σ: env} {P: prop}:
  σ ⊨ P.instantiated_n →
  σ ⊨ P.erased_n

axiom instantiated_and {σ: env} {P Q: prop}:
  σ ⊨ (P.instantiated && Q.instantiated) →
  σ ⊨ (P && Q).instantiated

axiom instantiated_or {σ: env} {P Q: prop}:
  σ ⊨ (P.instantiated || Q.instantiated) →
  σ ⊨ (P || Q).instantiated

-- lemmas

lemma instantiated_of_erased_no_env {P: prop}: ⊨ P.erased → ⊨ P.instantiated :=
  assume h: ⊨ P.erased,
  have P.erased = vc.subst_env env.empty P.erased, by unfold vc.subst_env,
  have env.empty ⊨ P.erased, from this ▸ h,
  have h2: env.empty ⊨ P.instantiated, from instantiated_of_erased this,
  have  vc.subst_env env.empty P.instantiated = P.instantiated, by unfold vc.subst_env,
  show ⊨ P.instantiated, from this ▸ h2

lemma instantiated_n_of_instantiated_no_env {P: prop}: ⊨ P.instantiated → ⊨ P.instantiated_n :=
  assume h: ⊨ P.instantiated,
  have P.instantiated = vc.subst_env env.empty P.instantiated, by unfold vc.subst_env,
  have env.empty ⊨ P.instantiated, from this ▸ h,
  have h2: env.empty ⊨ P.instantiated_n, from instantiated_n_of_instantiated this,
  have  vc.subst_env env.empty P.instantiated_n = P.instantiated_n, by unfold vc.subst_env,
  show ⊨ P.instantiated_n, from this ▸ h2

lemma erased_n_of_instantiated_n_no_env {P: prop}: ⊨ P.instantiated_n → ⊨ P.erased_n :=
  assume h: ⊨ P.instantiated_n,
  have P.instantiated_n = vc.subst_env env.empty P.instantiated_n, by unfold vc.subst_env,
  have env.empty ⊨ P.instantiated_n, from this ▸ h,
  have h2: env.empty ⊨ P.erased_n, from erased_n_of_instantiated_n this,
  have vc.subst_env env.empty P.erased_n = P.erased_n, by unfold vc.subst_env,
  show ⊨ P.erased_n, from this ▸ h2

lemma valid.refl {v: value}: ⊨ (v ≡ v) :=
  have binop.apply binop.eq v v = @ite (v = v)
                                  (classical.prop_decidable (v = v))
                                  value value.true value.false, by unfold binop.apply,
  have binop.apply binop.eq v v = value.true, by simp[this],
  have ⊨ ((v ≡ v) ≡ value.true), from valid.binop.mp this,
  show ⊨ (v ≡ v), from valid.eq.true.mp this

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

lemma empty_history_valid: ⟪calls_to_prop list.nil⟫ :=
  assume σ: env,
  have h1: ⊨ value.true, from valid.tru,
  have (prop.term value.true).erased = vc.term value.true, by unfold prop.erased,
  have ⊨ (prop.term value.true).erased, from this ▸ h1,
  have ⊨ (prop.term value.true).instantiated, from instantiated_of_erased_no_env this,


  
  have term.subst_env σ value.true = value.true, from term.subst_env.value,
  have ⊨ term.subst_env σ value.true, from this.symm ▸ h1,
  have vc.subst_env σ value.true = vc.term (term.subst_env σ value.true), from vc.subst_env.term,
  have \si⊨ term.subst_env σ value.true, from this.symm ▸ h1,




  have calls_to_prop list.nil = value.true, by unfold calls_to_prop,
  have h1: ⊨ prop.term (calls_to_prop list.nil), from valid.tru,


  show σ ⊨ (calls_to_prop list.nil).instantiated, from sorry
