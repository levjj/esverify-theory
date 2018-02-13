import .syntax .notations .evaluation .substitution .qi

-- validity

inductive valid : vc → Prop
notation `⊨` p: 100 := valid p

| tru:
  ⊨ value.true

| unop {op: unop} {vₓ v: value}:
  unop.apply op vₓ = some v →
  ⊨ term.binop binop.eq (term.unop op vₓ) v

| binop {op: binop} {v₁ v₂ v: value}:
  binop.apply op v₁ v₂ = some v →
  ⊨ term.binop binop.eq (term.binop op v₁ v₂) v

| app {vₓ v: value} {σ σ': env} {f x y: var} {R S: spec} {e: exp}:
  (σ[x↦vₓ], e) ⟶* (σ', exp.return y) →
  (σ' y = some v) →
  ⊨ term.binop binop.eq (term.app (value.func f x R S e σ) vₓ) v

| and {P Q: vc}:
  ⊨ P →
  ⊨ Q →
  ⊨ (P && Q)

| orl {P Q: vc}:
  ⊨ P →
  ⊨ (P || Q)

| orr {P Q: vc}:
  ⊨ Q →
  ⊨ (P || Q)

| pre {vₓ: value} {σ: env} {f x y: var} {R S: spec} {e: exp}:
  ⊨ vc.subst_env (σ[x↦vₓ][f↦value.func f x R S e σ]) R.to_prop.instantiated →
  ⊨ vc.pre (value.func f x R S e σ) vₓ

| pre₁ {vₓ v: value} {op: unop}:
  (∃v, unop.apply op vₓ = some v) →
  ⊨ vc.pre₁ op vₓ

| pre₂ {v₁ v₂ v: value} {op: binop}:
  (∃v, binop.apply op v₁ v₂ = v) →
  ⊨ vc.pre₂ op v₁ v₂

| post {vₓ: value} {σ σ': env} {f x y: var} {R S: spec} {e: exp}:
  (σ[x↦vₓ], e) ⟶* (σ', exp.return y) →
  ⊨ vc.subst_env (σ[x↦vₓ][f↦value.func f x R S e σ]) (spec.implies R S).to_prop.instantiated →
  ⊨ vc.post (value.func f x R S e σ) vₓ

| univ {x: var} {P: vc}:
  (∀v, ⊨ vc.subst x v P) →
  ⊨ vc.univ x P

notation `⊨` p: 100 := valid p
notation σ `⊨` p: 100 := valid (vc.subst_env σ p)

axiom valid.mp  {P Q: vc}: ⊨ vc.implies P Q → ⊨ P → ⊨ Q

axiom valid.subst {t₁ t₂: term} (Q: propctx): ⊨ (t₁ ≡ t₂) → ⊨ (Q t₁).instantiated → ⊨ (Q t₂).instantiated

-- notation ⟪ P ⟫

@[reducible]
def VC(P: prop) := ∀ (σ: env), σ ⊨ P.instantiated

notation `⟪` P `⟫`: 100 := VC P

axiom instantiated_of_erased {σ: env} {P: prop}:
  σ ⊨ P.erased → σ ⊨ P.instantiated
axiom instantiated_n_of_instantiated {σ: env} {P: prop}:
  σ ⊨ P.instantiated → σ ⊨ P.instantiated_n
axiom erased_n_of_instantiated_n {σ: env} {P: prop}:
  σ ⊨ P.instantiated_n → σ ⊨ P.erased_n
axiom instantiated_and {σ: env} {P Q: prop}:
  σ ⊨ P.instantiated → σ ⊨ Q.instantiated → σ ⊨ (P && Q).instantiated
axiom instantiated_or {σ: env} {P Q: prop}:
  σ ⊨ P.instantiated → σ ⊨ Q.instantiated → σ ⊨ (P || Q).instantiated

-- lemmas

lemma valid.refl {v: value}: ⊨ (v ≡ v) :=
  have binop.apply binop.eq v v = @ite (v = v)
                                  (classical.prop_decidable (v = v))
                                  value value.true value.false, by unfold binop.apply,
  have binop.apply binop.eq v v = value.true, by simp[this],
  have h: ⊨ ((v ≡ v) ≡ value.true), from valid.binop this,
  have ⊨ value.true, from valid.tru,
  let Q:propctx := propctx.term termctx.hole in
  show ⊨ (v ≡ v), from valid.subst Q h this

lemma valid_env.and {σ: env} {P Q: vc}: σ ⊨ P → σ ⊨ Q → σ ⊨ (P && Q) :=
  assume p_valid: valid (vc.subst_env σ P),
  assume q_valid: valid (vc.subst_env σ Q),
  have vc.subst_env σ (P && Q) = (vc.subst_env σ P && vc.subst_env σ Q), from vc.subst_env.and,
  show σ ⊨ (P && Q), from this.symm ▸ valid.and p_valid q_valid

lemma valid.mp_env {σ: env} {P Q: vc}: σ ⊨ vc.implies P Q → σ ⊨ P → σ ⊨ Q :=
  assume impl: σ ⊨ (vc.implies P Q),
  assume p: σ ⊨ P,
  have vc.subst_env σ (vc.implies P Q) = (vc.subst_env σ P.not || vc.subst_env σ Q), from vc.subst_env.or,
  have h: ⊨ (vc.subst_env σ P.not || vc.subst_env σ Q), from this ▸ impl,
  have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  have ⊨ ((vc.subst_env σ P).not || vc.subst_env σ Q), from this ▸ h,
  have ⊨ vc.implies (vc.subst_env σ P) (vc.subst_env σ Q), from this,
  show σ ⊨ Q, from valid.mp this p

lemma valid.pre₁.inv {vₓ: value} {op: unop}: ⊨ vc.pre₁ op vₓ → (∃v, unop.apply op vₓ = some v) :=
  assume pre_valid: ⊨ vc.pre₁ op vₓ,
  show (∃v, unop.apply op vₓ = some v), by begin
    cases pre_valid,
    case valid.pre₁ v exist_v { exact exist_v }
  end
