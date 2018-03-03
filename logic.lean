import .syntax .notations .evaluation .substitution .qi .vcgen .bindings

-- simple axioms for logical reasoning

axiom valid.tru:
  ⊨ value.true

axiom valid.and {P Q: vc}:
  (⊨ P) ∧ (⊨ Q)
  ↔
  ⊨ P ⋀ Q

axiom valid.or.left {P Q: vc}:
  (⊨ P) → 
  closed Q →
  ⊨ P ⋁ Q

axiom valid.or.right {P Q: vc}:
  closed P →
  (⊨ Q) → 
  ⊨ P ⋁ Q

axiom valid.or.elim {P Q: vc}:
  (⊨ P ⋁ Q)
  →
  (⊨ P) ∨ (⊨ Q)

axiom valid.not.term {t: term}:
  (⊨ term.unop unop.not t)
  ↔
  ⊨ vc.not t

-- no contradictions
axiom valid.contradiction {P: vc}:
  ¬ (⊨ P ⋀ P.not)

-- law of excluded middle
axiom valid.em {P: vc}:
  closed P →
  (⊨ P ⋁ P.not)

-- a term is valid if it equals true
axiom valid.eq.true {t: term}:
  ⊨ t
  ↔
  ⊨ t ≡ value.true

axiom valid.univ {x: var} {P: vc}:
  (∀v, ⊨ vc.subst x v P)
  ↔
  ⊨ vc.univ x P

-- unary and binary operators are decidable, so equalities with operators are decidable
axiom valid.unop {op: unop} {vₓ v: value}:
  unop.apply op vₓ = some v
  ↔
  ⊨ term.unop op vₓ ≡ v

axiom valid.binop {op: binop} {v₁ v₂ v: value}:
  binop.apply op v₁ v₂ = some v
  ↔
  ⊨ term.binop op v₁ v₂ ≡ v

-- The following equality axiom is non-standard and makes validity undecidable.
-- It is only used in the preservation proof of e-return and in no other lemmas.
-- The logic treats `f(x)` uninterpreted, so there is no way to derive it naturally.
-- However, given a complete evaluation derivation of a function call, we can add the
-- equality `f(x)=y` as new axiom for closed values f, x, y and the resulting set
-- of axioms is still sound due to deterministic evaluation.
axiom valid.app {vₓ v: value} {σ σ': env} {H H': history} {f x y: var} {R S: spec} {e: exp}:
  (R, H, σ[x↦vₓ], e) ⟶* (R, H', σ', exp.return y) ∧
  (σ' y = some v)
  →
  ⊨ term.app (value.func f x R S e H σ) vₓ ≡ v

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

axiom valid.pre.mp {vₓ: value} {σ: env} {f x: var} {R S: spec} {e: exp} {H: history}:
  (σ[f↦value.func f x R S e H σ][x↦vₓ] ⊨ R.to_prop.instantiated_p)
  →
  ⊨ vc.pre (value.func f x R S e H σ) vₓ

axiom valid.pre.mpr {vₓ: value} {σ: env} {f x: var} {R S: spec} {e: exp} {H: history}:
  (⊨ vc.pre (value.func f x R S e H σ) vₓ)
  →
  (σ[f↦value.func f x R S e H σ][x↦vₓ] ⊨ R.to_prop.instantiated_n)

axiom valid.post {vₓ: value} {σ: env} {Q: prop} {Q₂: propctx} {f x: var} {R S: spec} {e: exp} {H: history}:
  (⊢ σ : Q) →
  (H ⋀ Q ⋀ spec.func f x R S ⋀ R ⊢ e : Q₂) →
  (⊨ vc.post (value.func f x R S e H σ) vₓ)
  →
  (σ[f↦value.func f x R S e H σ][x↦vₓ] ⊨ (Q₂ (term.app f x) ⋀ S.to_prop).instantiated_n)

-- only closed VCs can be validated
axiom valid.closed {P: vc}:
  (⊨ P) → closed P

-- lemmas

lemma valid.false.elim {P: vc}: closed P → (⊨ vc.implies value.false P) :=
  assume P_closed: closed P,
  have h1: ⊨ value.true, from valid.tru,
  have unop.apply unop.not value.false = value.true, by unfold unop.apply,
  have ⊨ term.unop unop.not value.false ≡ value.true, from valid.unop.mp this,
  have ⊨ term.unop unop.not value.false, from valid.eq.true.mpr this,
  have ⊨ vc.not value.false, from valid.not.term.mp this,
  have ⊨ vc.not value.false ⋁ P, from valid.or.left this P_closed,
  show ⊨ vc.implies value.false P, from this

lemma valid.implies.mp {P Q: vc}: closed P → closed Q → ((⊨ P) → (⊨ Q)) → ⊨ vc.implies P Q :=
  assume P_closed: closed P,
  assume Q_closed: closed Q,
  assume h1: (⊨ P) → (⊨ Q),
  have ⊨ P ⋁ P.not, from valid.em P_closed,
  or.elim (valid.or.elim this) (
    assume : ⊨ P,
    have ⊨ Q, from h1 this,
    show ⊨ P.not ⋁ Q, from valid.or.right (vc.closed.not P_closed) this
  ) (
    assume : ⊨ P.not,
    show ⊨ P.not ⋁ Q, from valid.or.left this Q_closed
  )

lemma valid.implies.mpr {P Q: vc}: (⊨ vc.implies P Q) → (⊨ P) → (⊨ Q) :=
  assume h1: (⊨ P.not ⋁ Q),
  assume h2: (⊨ P),
  or.elim (valid.or.elim h1) (
    assume : ⊨ P.not,
    have ⊨ P ⋀ P.not, from valid.and.mp ⟨h2, this⟩,
    show ⊨ Q, from false.elim (valid.contradiction this)
  ) id

lemma valid.not.mp {P: vc}: closed P → (¬ ⊨ P) → ⊨ P.not :=
  assume P_closed: closed P,
  assume h1: ¬ (⊨ P),
  have ⊨ P ⋁ P.not, from valid.em P_closed,
  or.elim (valid.or.elim this) (
    assume : ⊨ P,
    show ⊨ P.not, from absurd this h1
  ) id

lemma valid.not.mpr {P: vc}: (⊨ P.not) → ¬ ⊨ P :=
  assume h2: ⊨ P.not,
  assume h3: ⊨ P,
  have ⊨ (P ⋀ P.not), from valid.and.mp ⟨h3, h2⟩,
  show «false», from valid.contradiction this

lemma valid.neg_neg {P: vc}: (⊨ P.not.not) ↔ ⊨ P :=
  iff.intro (
    assume : ⊨ P.not.not,
    have P_not_closed: closed P.not, from vc.closed.not.inv (valid.closed this),
    have P_closed: closed P, from vc.closed.not.inv P_not_closed,
    have h1: ¬ ⊨ P.not, from valid.not.mpr this,
    have h2: ¬ ¬ ⊨ P, from (
      assume : ¬ ⊨ P,
      have ⊨ P.not, from valid.not.mp P_closed this,
      show «false», from h1 this
    ),
    show ⊨ P, from classical.by_contradiction (
      assume : ¬ ⊨ P,
      show «false», from h2 this
    )
  ) (
    assume h1: ⊨ P,
    have h2: ¬ ⊨ P.not, from (
      assume : ⊨ P.not,
      have ¬ ⊨ P, from valid.not.mpr this,
      show «false», from this h1
    ),
    show ⊨ P.not.not, from valid.not.mp (vc.closed.not (valid.closed h1)) h2
  )

lemma valid.mt {P Q: vc}: (⊨ vc.implies P Q) → (⊨ Q.not) → ⊨ P.not :=
  assume h1: ⊨ vc.implies P Q,
  have P_closed: closed P, from (vc.closed.implies.inv (valid.closed h1)).left,
  assume : ⊨ Q.not,
  have h2: ¬ ⊨ Q, from valid.not.mpr this,
  have ¬ ⊨ P, from (
    assume : ⊨ P,
    have ⊨ Q, from valid.implies.mpr h1 this,
    show «false», from h2 this
  ),
  show ⊨ P.not, from valid.not.mp P_closed this

lemma valid.refl {v: value}: ⊨ (v ≡ v) :=
  have binop.apply binop.eq v v = value.true, from binop.eq_of_equal_values,
  have ⊨ ((v ≡ v) ≡ value.true), from valid.binop.mp this,
  show ⊨ (v ≡ v), from valid.eq.true.mpr this

lemma valid.implies.trans {P₁ P₂ P₃: vc}:
      (⊨ vc.implies P₁ P₂) → (⊨ vc.implies P₂ P₃) → ⊨ vc.implies P₁ P₃ :=
  assume h1: ⊨ vc.implies P₁ P₂,
  have P₁_closed: closed P₁, from (vc.closed.implies.inv (valid.closed h1)).left,
  assume h2: ⊨ vc.implies P₂ P₃,
  have P₃_closed: closed P₃, from (vc.closed.implies.inv (valid.closed h2)).right,
  show ⊨ vc.implies P₁ P₃, from valid.implies.mp P₁_closed P₃_closed (
    assume : ⊨ P₁,
    have ⊨ P₂, from valid.implies.mpr h1 this,
    show ⊨ P₃, from valid.implies.mpr h2 this
  )

lemma valid_env.closed {σ: env} {P: vc}: (σ ⊨ P) → closed_subst σ P :=
  assume : σ ⊨ P,
  have ⊨ vc.subst_env σ P, from this,
  have closed (vc.subst_env σ P), from valid.closed this,
  show closed_subst σ P, from vc.closed_subst_of_closed this

lemma valid_env.true {σ: env}: σ ⊨ value.true :=
  have h1: ⊨ value.true, from valid.tru,
  have term.subst_env σ value.true = value.true, from term.subst_env.value,
  have h2: ⊨ term.subst_env σ value.true, from this.symm ▸ h1,
  have vc.subst_env σ value.true = vc.term (term.subst_env σ value.true), from vc.subst_env.term,
  show σ ⊨ value.true, from this.symm ▸ h2

lemma valid_env.mt {σ: env} {P Q: vc}: (σ ⊨ vc.implies P Q) → (σ ⊨ Q.not) → σ ⊨ P.not :=
  assume h1: σ ⊨ vc.implies P Q,
  have vc.subst_env σ (vc.implies P Q) = vc.implies (vc.subst_env σ P) (vc.subst_env σ Q),
  from vc.subst_env.implies,
  have h2: ⊨ vc.implies (vc.subst_env σ P) (vc.subst_env σ Q), from this ▸ h1,
  assume h3: σ ⊨ Q.not,
  have vc.subst_env σ Q.not = (vc.subst_env σ Q).not, from vc.subst_env.not,
  have h4: ⊨ (vc.subst_env σ Q).not, from this ▸ h3,
  have h5: ⊨ (vc.subst_env σ P).not, from valid.mt h2 h4,
  have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  show σ ⊨ P.not, from this.symm ▸ h5

lemma valid_env.eq.true {σ: env} {t: term}: σ ⊨ t ↔ σ ⊨ (t ≡ value.true) :=
  iff.intro (
    assume t_valid: ⊨ vc.subst_env σ t,
    have vc.subst_env σ t = vc.term (term.subst_env σ t), from vc.subst_env.term,
    have ⊨ vc.term (term.subst_env σ t), from this ▸ t_valid,
    have h: ⊨ vc.term ((term.subst_env σ t) ≡ value.true), from valid.eq.true.mp this,
    have term.subst_env σ value.true = value.true, from term.subst_env.value,
    have h2: ⊨ vc.term ((term.subst_env σ t) ≡ (term.subst_env σ value.true)),
    from this.symm ▸ h,
    have (term.subst_env σ (t ≡ value.true)) = ((term.subst_env σ t) ≡ (term.subst_env σ value.true)),
    from term.subst_env.binop,
    have h3: ⊨ term.subst_env σ (t ≡ value.true),
    from this.symm ▸ h2,
    have vc.subst_env σ (t ≡ value.true) = vc.term (term.subst_env σ (t ≡ value.true)), from vc.subst_env.term,
    show σ ⊨ (t ≡ value.true), from this.symm ▸ h3
  ) (
    assume t_valid: ⊨ vc.subst_env σ (t ≡ value.true),
    have vc.subst_env σ (t ≡ value.true) = vc.term (term.subst_env σ (t ≡ value.true)), from vc.subst_env.term,
    have h: ⊨ vc.term (term.subst_env σ (t ≡ value.true)),
    from this ▸ t_valid,
    have (term.subst_env σ (t ≡ value.true)) = ((term.subst_env σ t) ≡ (term.subst_env σ value.true)),
    from term.subst_env.binop,
    have h2: ⊨ vc.term ((term.subst_env σ t) ≡ (term.subst_env σ value.true)),
    from this ▸ h,
    have term.subst_env σ value.true = value.true, from term.subst_env.value,
    have ⊨ vc.term ((term.subst_env σ t) ≡ value.true), from this ▸ h2,
    have h3: ⊨ vc.term (term.subst_env σ t), from valid.eq.true.mpr this,
    have vc.subst_env σ t = vc.term (term.subst_env σ t), from vc.subst_env.term,
    show ⊨ vc.subst_env σ t, from this.symm ▸ h3
  )

lemma valid_env.neg_neg {σ: env} {P: vc}: (σ ⊨ P.not.not) ↔ σ ⊨ P :=
  iff.intro (
    assume h1: σ ⊨ P.not.not,
    have vc.subst_env σ P.not.not = (vc.subst_env σ P.not).not, from vc.subst_env.not,
    have h2: ⊨ (vc.subst_env σ P.not).not, from this ▸ h1,
    have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
    have  ⊨ (vc.subst_env σ P).not.not, from this ▸ h2,
    show σ ⊨ P, from valid.neg_neg.mp this
  ) (
    assume : σ ⊨ P,
    have h1: ⊨ (vc.subst_env σ P).not.not, from valid.neg_neg.mpr this,
    have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
    have h2: ⊨ (vc.subst_env σ P.not).not, from this.symm ▸ h1,
    have vc.subst_env σ P.not.not = (vc.subst_env σ P.not).not, from vc.subst_env.not,
    show σ ⊨ P.not.not, from this.symm ▸ h2
  )

lemma valid_env.and {σ: env} {P Q: vc}: (σ ⊨ P) → (σ ⊨ Q) → σ ⊨ (P ⋀ Q) :=
  assume p_valid: ⊨ vc.subst_env σ P,
  assume q_valid: ⊨ vc.subst_env σ Q,
  have vc.subst_env σ (P ⋀ Q) = (vc.subst_env σ P ⋀ vc.subst_env σ Q), from vc.subst_env.and,
  show σ ⊨ (P ⋀ Q), from this.symm ▸ valid.and.mp ⟨p_valid, q_valid⟩

lemma valid_env.and.elim {σ: env} {P Q: vc}: (σ ⊨ P ⋀ Q) → (σ ⊨ P) ∧ σ ⊨ Q :=
  assume p_and_q_valid: ⊨ vc.subst_env σ (P ⋀ Q),
  have vc.subst_env σ (P ⋀ Q) = (vc.subst_env σ P ⋀ vc.subst_env σ Q), from vc.subst_env.and,
  have ⊨ (vc.subst_env σ P ⋀ vc.subst_env σ Q), from this ▸ p_and_q_valid,
  show (σ ⊨ P) ∧ (σ ⊨ Q), from valid.and.mpr this

lemma valid_env.or₁ {σ: env} {P Q: vc}: (σ ⊨ P) → closed_subst σ Q → σ ⊨ (P ⋁ Q) :=
  assume h1: ⊨ vc.subst_env σ P,
  assume : closed_subst σ Q,
  have h2: closed (vc.subst_env σ Q), from vc.closed_of_closed_subst this,
  have h: ⊨ vc.subst_env σ P ⋁ vc.subst_env σ Q, from valid.or.left h1 h2,
  have vc.subst_env σ (P ⋁ Q) = (vc.subst_env σ P ⋁ vc.subst_env σ Q), from vc.subst_env.or,
  show σ ⊨ (P ⋁ Q), from this.symm ▸ h

lemma valid_env.or₂ {σ: env} {P Q: vc}: closed_subst σ P → (σ ⊨ Q) → σ ⊨ (P ⋁ Q) :=
  assume : closed_subst σ P,
  have h1: closed (vc.subst_env σ P), from vc.closed_of_closed_subst this,
  assume h2: ⊨ vc.subst_env σ Q,
  have h: ⊨ vc.subst_env σ P ⋁ vc.subst_env σ Q, from valid.or.right h1 h2,
  have vc.subst_env σ (P ⋁ Q) = (vc.subst_env σ P ⋁ vc.subst_env σ Q), from vc.subst_env.or,
  show σ ⊨ (P ⋁ Q), from this.symm ▸ h

lemma valid_env.or.elim {σ: env} {P Q: vc}: (σ ⊨ P ⋁ Q) → (σ ⊨ P) ∨ σ ⊨ Q :=
  assume p_or_q_valid: ⊨ vc.subst_env σ (P ⋁ Q),
  have vc.subst_env σ (P ⋁ Q) = (vc.subst_env σ P ⋁ vc.subst_env σ Q), from vc.subst_env.or,
  have ⊨ (vc.subst_env σ P ⋁ vc.subst_env σ Q), from this ▸ p_or_q_valid,
  show (σ ⊨ P) ∨ (σ ⊨ Q), from valid.or.elim this

lemma valid_env.not.mp {σ: env} {P: vc}: closed_subst σ P → ¬ (σ ⊨ P) → (σ ⊨ P.not) :=
  assume P_closed: closed_subst σ P,
  assume h1: ¬ (σ ⊨ P),
  have h2: vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  have ¬ ⊨ (vc.subst_env σ P), from h2 ▸ h1,
  have ⊨ (vc.subst_env σ P).not, from valid.not.mp (vc.closed_of_closed_subst P_closed) this,
  show σ ⊨ P.not, from h2.symm ▸ this

lemma valid_env.not.mpr {σ: env} {P: vc}: (σ ⊨ P.not) → ¬ (σ ⊨ P) :=
  assume h1: σ ⊨ P.not,
  have h2: vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  have ⊨ (vc.subst_env σ P).not, from h2 ▸ h1,
  have ¬ ⊨ (vc.subst_env σ P), from valid.not.mpr this,
  show ¬ (σ ⊨ P), from h2.symm ▸ this

lemma valid_env.mp {σ: env} {P Q: vc}: (σ ⊨ vc.implies P Q) → (σ ⊨ P) → σ ⊨ Q :=
  assume impl: σ ⊨ (vc.implies P Q),
  assume p: σ ⊨ P,
  have vc.subst_env σ (vc.implies P Q) = (vc.subst_env σ P.not ⋁ vc.subst_env σ Q), from vc.subst_env.or,
  have h: ⊨ (vc.subst_env σ P.not ⋁ vc.subst_env σ Q), from this ▸ impl,
  have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  have ⊨ ((vc.subst_env σ P).not ⋁ vc.subst_env σ Q), from this ▸ h,
  have ⊨ vc.implies (vc.subst_env σ P) (vc.subst_env σ Q), from this,
  show σ ⊨ Q, from valid.implies.mpr this p

lemma valid_env.mpr {σ: env} {P Q: vc}:
      closed_subst σ P → closed_subst σ Q → ((σ ⊨ P) → (σ ⊨ Q)) → σ ⊨ vc.implies P Q :=
  assume : closed_subst σ P,
  have P_closed: closed (vc.subst_env σ P), from vc.closed_of_closed_subst this,
  assume : closed_subst σ Q,
  have Q_closed: closed (vc.subst_env σ Q), from vc.closed_of_closed_subst this,
  assume : ((σ ⊨ P) → σ ⊨ Q),
  have ⊨ vc.implies (vc.subst_env σ P) (vc.subst_env σ Q), from valid.implies.mp P_closed Q_closed this,
  have h1: ⊨ vc.or (vc.subst_env σ P).not (vc.subst_env σ Q), from this,
  have vc.subst_env σ P.not = (vc.subst_env σ P).not, from vc.subst_env.not,
  have h2: ⊨ vc.or (vc.subst_env σ P.not) (vc.subst_env σ Q), from this.symm ▸ h1,
  have vc.subst_env σ (P.not ⋁ Q) = (vc.subst_env σ P.not ⋁ vc.subst_env σ Q),
  from vc.subst_env.or,
  have ⊨ vc.subst_env σ (P.not ⋁ Q), from this.symm ▸ h2,
  show σ ⊨ vc.implies P Q, from this

lemma valid_env.implies.trans {σ: env} {P₁ P₂ P₃: vc}:
      (σ ⊨ vc.implies P₁ P₂) → (σ ⊨ vc.implies P₂ P₃) → σ ⊨ vc.implies P₁ P₃ :=
  assume h1: σ ⊨ vc.implies P₁ P₂,
  have P₁_closed: closed_subst σ P₁, from (vc.closed_subst.implies.inv (valid_env.closed h1)).left,
  assume h2: σ ⊨ vc.implies P₂ P₃,
  have P₃_closed: closed_subst σ P₃, from (vc.closed_subst.implies.inv (valid_env.closed h2)).right,
  show σ ⊨ vc.implies P₁ P₃, from valid_env.mpr P₁_closed P₃_closed (
    assume : σ ⊨ P₁,
    have σ ⊨ P₂, from valid_env.mp h1 this,
    show σ ⊨ P₃, from valid_env.mp h2 this
  )

lemma valid_env.subst_of_eq_instantiated {σ: env} {x: var} {v: value}:
      (σ ⊨ prop.instantiated_p (x ≡ v)) → (σ x = v) :=
  assume : σ ⊨ prop.instantiated_p (x ≡ v),
  have h1: σ ⊨ prop.erased_p (x ≡ v), from valid_env.erased_p_of_instantiated_p this,
  have prop.erased_p (prop.term (x ≡ v)) = vc.term (x ≡ v),
  by unfold prop.erased_p,
  have σ ⊨ vc.term (x ≡ v), from this.symm ▸ h1,
  have h2: ⊨ vc.subst_env σ (vc.term (x ≡ v)), from this,
  have vc.subst_env σ (vc.term (x ≡ v)) = vc.term (term.subst_env σ (x ≡ v)),
  from vc.subst_env.term,
  have h3: ⊨ vc.term (term.subst_env σ (x ≡ v)), from this ▸ h2,
  have term.subst_env σ (x ≡ v) = (term.subst_env σ x ≡ term.subst_env σ v),
  from term.subst_env.binop,
  have h4: ⊨ (term.subst_env σ x ≡ term.subst_env σ v), from this ▸ h3,
  have term.subst_env σ v = v, from term.subst_env.value,
  have h5: ⊨ (term.subst_env σ x ≡ v), from this ▸ h4,
  have x ∈ σ, from by_contradiction (
    assume : x ∉ σ,
    have σ x = none, from env.contains_apply_equiv.left.mpr this,
    have term.subst_env σ x = x, from term.subst_env.var.left.mp this,
    have ⊨ (x ≡ v), from this ▸ h5,
    have closed (vc.term (x ≡ v)), from valid.closed this,
    have h6: closed (x ≡ v), from vc.closed.term.inv this,
    have x ∈ FV (term.var x), from free_in_term.var x,
    have x ∈ FV (x ≡ v), from free_in_term.binop₁ this,
    show «false», from h6 x this
  ),
  have ∃v', σ x = some v', from env.contains_apply_equiv.right.mpr this,
  let ⟨v', h6⟩ := this in
  have term.subst_env σ x = v', from (term.subst_env.var.right v').mp h6,
  have ⊨ (v' ≡ v), from this ▸ h5,
  have ⊨ (v' ≡ v) ≡ value.true, from valid.eq.true.mp this,
  have binop.apply binop.eq v' v = some value.true, from valid.binop.mpr this,
  have v' = v, from binop.eq.inv this,
  show σ x = some v, from h6.symm ▸ (some.inj.inv this)

lemma history_valid {H: history}: ⟪calls_to_prop H⟫ :=
  assume σ: env,
  begin
    induction H with H₁ f y R S e H₂ σ₂ v ih₁ ih₂,

    show σ ⊨ (calls_to_prop history.empty).instantiated_n, from (
      have h1: σ ⊨ value.true, from valid_env.true,
      have (prop.term value.true).erased_n = vc.term value.true, by unfold prop.erased_n,
      have σ ⊨ (prop.term value.true).erased_n, from this ▸ h1,
      have h2: σ ⊨ (prop.term value.true).instantiated_n, from valid_env.instantiated_n_of_erased_n this,
      have calls_to_prop history.empty = value.true, by unfold calls_to_prop,
      show σ ⊨ (calls_to_prop history.empty).instantiated_n, from this ▸ h2
    ),

    show σ ⊨ prop.instantiated_n (calls_to_prop (H₁ · call f y R S e H₂ σ₂ v)), from (
      have h1: σ ⊨ (calls_to_prop H₁).instantiated_n, from ih₁,
      have h2: σ ⊨ value.true, from valid_env.true,
      have (prop.call (value.func f y R S e H₂ σ₂) v).erased_n = vc.term value.true, by unfold prop.erased_n,
      have σ ⊨ (prop.call (value.func f y R S e H₂ σ₂) v).erased_n, from this ▸ h2,
      have h3: σ ⊨ (prop.call (value.func f y R S e H₂ σ₂) v).instantiated_n,
      from valid_env.instantiated_n_of_erased_n this,
      have σ ⊨ ((calls_to_prop H₁).instantiated_n ⋀ (prop.call (value.func f y R S e H₂ σ₂) v).instantiated_n),
      from valid_env.and h1 h3,
      have h4: σ ⊨ (calls_to_prop H₁ ⋀ prop.call (value.func f y R S e H₂ σ₂) v).instantiated_n,
      from valid_env.instantiated_n_and this,
      have calls_to_prop (H₁ · call f y R S e H₂ σ₂ v)
        = (calls_to_prop H₁ ⋀ prop.call (value.func f y R S e H₂ σ₂) v),
      by unfold calls_to_prop,
      show σ ⊨ (calls_to_prop (H₁ · call f y R S e H₂ σ₂ v)).instantiated_n, from this ▸ h4
    )
  end

lemma val_of_free_in_env {P: prop} {σ: env} {x: var}: (⊢ σ : P) → x ∈ FV P → ∃v, σ x = some v :=
  assume env_verified: ⊢ σ: P,
  assume x_free_in_P: x ∈ FV P,
  have x ∈ σ, from contains_of_free env_verified x_free_in_P,
  show ∃v, σ x = some v, from env.contains_apply_equiv.right.mpr this

lemma val_of_free_in_hist_env {R: spec} {H: history} {σ: env} {P: prop} {x: var}:
                              (⊢ σ : P) → FV R.to_prop ⊆ FV P → x ∈ FV (R.to_prop ⋀ ↑H ⋀ P) → ∃v, σ x = some v :=
  assume σ_verified: ⊢ σ : P,
  assume fv_R: FV R.to_prop ⊆ FV P,
  assume x_free_in_R_H_P: x ∈ FV (R.to_prop ⋀ ↑H ⋀ P),
  have FV (R.to_prop ⋀ ↑H ⋀ P) = FV ((R.to_prop ⋀ ↑H) ⋀ P), from free_in_prop.and_comm,
  have x ∈ FV ((R.to_prop ⋀ ↑H) ⋀ P), from this ▸ x_free_in_R_H_P,
  have free_in_prop x (R.to_prop ⋀ ↑H) ∨ free_in_prop x P, from free_in_prop.and.inv this,
  have x ∈ FV P, from or.elim this.symm id (
    assume : free_in_prop x (R.to_prop ⋀ ↑H),
    or.elim (free_in_prop.and.inv this) (
      assume : free_in_prop x R.to_prop,
      show x ∈ FV P, from set.mem_of_mem_of_subset this fv_R
    ) (
      assume : free_in_prop x H,
      show free_in_prop x P, from absurd this (call_history_closed H x)
    )
  ),
  show ∃v, σ x = some v, from val_of_free_in_env σ_verified this

lemma simple_equality_valid {σ: env} {x: var} {v: value}:
  x ∉ σ → (σ[x↦v]) ⊨ (prop.term (x ≡ v)).erased_n :=
  assume x_not_free_in_σ: x ∉ σ,
  have σ.apply x = none, from env.contains_apply_equiv.left.mpr x_not_free_in_σ,
  have h1: term.subst_env σ x = x, from term.subst_env.var.left.mp this,
  have (term.subst_env (σ[x↦v]) x = term.subst x v (term.subst_env σ x)),
  by unfold term.subst_env,
  have h2: term.subst_env (σ[x↦v]) x = term.subst x v x,
  from @eq.subst term (λa, term.subst_env (σ[x↦v]) x = term.subst x v a) (term.subst_env σ x) x h1 this,
  have term.subst x v (term.var x) = (if x = x then v else x), by unfold term.subst,
  have term.subst x v (term.var x) = v, by simp[this],
  have h3: term.subst_env (σ[x↦v]) x = v, from eq.trans h2 this,
  have h4: term.subst_env (σ[x↦v]) v = v, from term.subst_env.value,
  have term.subst_env (σ[x↦v]) (x ≡ v) = (term.subst_env (σ[x↦v]) x ≡ term.subst_env (σ[x↦v]) v),
  from term.subst_env.binop,
  have term.subst_env (σ[x↦v]) (x ≡ v) = (v ≡ term.subst_env (σ[x↦v]) v),
  from @eq.subst term (λa, term.subst_env (σ[x↦v]) (x ≡ v) = (a ≡ term.subst_env (σ[x↦v]) v))
                      (term.subst_env (σ[x↦v]) x) v h3 this,
  have h5: term.subst_env (σ[x↦v]) (x ≡ v) = (v ≡ v),
  from @eq.subst term (λa, term.subst_env (σ[x↦v]) (x ≡ v) = (v ≡ a))
                      (term.subst_env (σ[x↦v]) v) v h4 this,
  have h6: vc.term (term.subst_env (σ[x↦v]) (x ≡ v)) = vc.term (v ≡ v), by simp[h5],
  have vc.subst_env (σ[x↦v]) (x ≡ v) = vc.term (term.subst_env (σ[x↦v]) (x ≡ v)), from vc.subst_env.term,
  have h7: vc.subst_env (σ[x↦v]) (vc.term (x ≡ v)) = vc.term (v ≡ v), from eq.trans this h6,
  have prop.erased_n (prop.term (x ≡ v)) = vc.term (x ≡ v), by unfold prop.erased_n,
  have h8: vc.subst_env (σ[x↦v]) (prop.term (x ≡ v)).erased_n = vc.term (v ≡ v), from this.symm ▸ h7,
  have ⊨ vc.term (v ≡ v), from valid.refl,
  show (σ[x↦v]) ⊨ prop.erased_n (x ≡ v), from h8.symm ▸ this

lemma simple_equality_env_valid {P: prop} {σ: env} {x: var} {v: value}:
                                   (⊢ σ: P) → x ∉ σ → (σ ⊨ P.instantiated_n) → ((σ[x↦v]) ⊨ P.instantiated_n)
                                                             ∧ ((σ[x↦v]) ⊨ (prop.term (x ≡ v)).instantiated_n) :=
  assume σ_verified: ⊢ σ: P,
  assume x_not_free_in_σ: x ∉ σ,
  assume ih: σ ⊨ P.instantiated_n,
  have σ.apply x = none, from env.contains_apply_equiv.left.mpr x_not_free_in_σ,
  have h1: ⊨ vc.subst_env σ P.instantiated_n, from ih,
  have x_not_in_P: x ∉ FV (vc.subst_env σ P.instantiated_n), from (
    assume : x ∈ FV (vc.subst_env σ P.instantiated_n),
    have x ∈ FV P.instantiated_n, from free_in_vc.subst_env this,
    have x ∈ FV P.erased_n, from free_in_erased_n_of_free_in_instantiated_n this,
    have x ∈ FV P, from free_of_erased_n_free (or.inl this),
    have ∃v, σ x = some v, from val_of_free_in_env σ_verified this,
    have x ∈ σ, from env.contains_apply_equiv.right.mp this,
    show «false», from x_not_free_in_σ this
  ),
  have vc.subst x v (vc.subst_env σ P.instantiated_n) = vc.subst_env σ P.instantiated_n,
  from unchanged_of_subst_nonfree_vc x_not_in_P,
  have h2: ⊨ vc.subst x v (vc.subst_env σ P.instantiated_n),
  from @eq.subst vc (λa, ⊨ a) (vc.subst_env σ P.instantiated_n)
          (vc.subst x v (vc.subst_env σ P.instantiated_n)) this.symm h1,
  have vc.subst x v (vc.subst_env σ P.instantiated_n)
      = vc.subst_env (σ[x↦v]) P.instantiated_n, by unfold vc.subst_env, 
  have h3: ⊨ vc.subst_env (σ[x↦v]) P.instantiated_n, from this ▸ h2,
  have (σ[x↦v]) ⊨ (prop.term (x ≡ v)).erased_n,
  from simple_equality_valid x_not_free_in_σ,
  have (σ[x↦v]) ⊨ (prop.term (x ≡ v)).instantiated_n, from valid_env.instantiated_n_of_erased_n this,
  ⟨h3, this⟩

lemma simple_equality_env_inst_valid {P: prop} {σ: env} {x: var} {v: value}:
                                   (⊢ σ: P) → x ∉ σ → (σ ⊨ P.instantiated_n) → (σ[x↦v]) ⊨ (P ⋀ x ≡ v).instantiated_n :=
  assume σ_verified: ⊢ σ: P,
  assume x_not_free_in_σ: x ∉ σ,
  assume ih: σ ⊨ P.instantiated_n,
  have ((σ[x↦v]) ⊨ P.instantiated_n) ∧ ((σ[x↦v]) ⊨ (prop.term (x ≡ v)).instantiated_n),
  from simple_equality_env_valid σ_verified x_not_free_in_σ ih,
  have (σ[x↦v]) ⊨ (P.instantiated_n ⋀ (prop.term (x ≡ v)).instantiated_n),
  from valid_env.and this.left this.right,
  show (σ[x↦v]) ⊨ prop.instantiated_n (P ⋀ (x ≡ v)), from valid_env.instantiated_n_and this

lemma env_translation_instantiated_n_valid {P: prop} {σ: env}: (⊢ σ: P) → σ ⊨ P.instantiated_n :=
  assume env_verified: (⊢ σ : P),
  begin
    induction env_verified,
    case env.vcgen.empty {
      show env.empty ⊨ prop.instantiated_n (value.true), from (
        have h: prop.erased_n (prop.term ↑value.true) = vc.term ↑value.true, by unfold prop.erased_n,
        have env.empty ⊨ value.true, from valid.tru,
        have env.empty ⊨ prop.erased_n (value.true), from h ▸ this,
        show env.empty ⊨ prop.instantiated_n (value.true), from valid_env.instantiated_n_of_erased_n this
      )
    },
    case env.vcgen.tru σ' x' Q x_not_free_in_σ' σ'_verified ih {
      show (σ'[x'↦value.true]) ⊨ prop.instantiated_n (Q ⋀ (x' ≡ value.true)),
      from simple_equality_env_inst_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.vcgen.fls σ' x' Q x_not_free_in_σ' σ'_verified ih {
      show (σ'[x'↦value.false]) ⊨ prop.instantiated_n (Q ⋀ (x' ≡ value.false)),
      from simple_equality_env_inst_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.vcgen.num n σ' x' Q x_not_free_in_σ' σ'_verified ih {
      show (σ'[x'↦value.num n]) ⊨ prop.instantiated_n (Q ⋀ (x' ≡ value.num n)),
      from simple_equality_env_inst_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.vcgen.func σ₁ σ₂ f g gx R S e H Q₁ Q₂ Q₃
      f_not_free_in_σ₁ g_not_free_in_σ₂ gx_not_free_in_σ₂ g_neq_gx σ₁_verified σ₂_verified gx_free_in_R R_fv S_fv func_verified
      S_valid ih₁ ih₂ { from (
      let vf := value.func g gx R S e H σ₂ in
      have h1: ((σ₁[f↦vf]) ⊨ Q₁.instantiated_n) ∧ ((σ₁[f↦vf]) ⊨ (prop.term (f ≡ vf)).instantiated_n),
      from simple_equality_env_valid σ₁_verified f_not_free_in_σ₁ ih₁,

      have g_subst: term.subst_env (σ₂[g↦vf]) g = vf, from (
        have h1: term.subst g vf g = vf, from term.subst.var.same,
        have σ₂ g = none, from env.contains_apply_equiv.left.mpr g_not_free_in_σ₂,
        have term.subst_env σ₂ g = g, from term.subst_env.var.left.mp this,
        have h2: term.subst g vf (term.subst_env σ₂ g) = vf, from this.symm ▸ h1,
        have term.subst_env (σ₂[g↦vf]) g = term.subst g vf (term.subst_env σ₂ g), by unfold term.subst_env,
        show term.subst_env (σ₂[g↦vf]) g = vf, from eq.trans this h2
      ),

      have h2: ⊨ prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from (
        have unop.apply unop.isFunc vf = value.true, by unfold unop.apply,
        have ⊨ (term.unop unop.isFunc vf ≡ value.true), from valid.unop.mp this,
        have ⊨ term.unop unop.isFunc vf, from valid.eq.true.mpr this,
        have h3: ⊨ term.unop unop.isFunc (term.subst_env (σ₂[g↦vf]) g), from g_subst.symm ▸ this,
        have term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g) = term.unop unop.isFunc (term.subst_env (σ₂[g↦vf]) g),
        from term.subst_env.unop,
        have h4: ⊨ vc.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from this.symm ▸ h3,
        have prop.erased_n (prop.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)))
           = vc.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)),
        by unfold prop.erased_n,
        have h5: ⊨ prop.erased_n (prop.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g))), from this.symm ▸ h4,
        have prop.subst_env (σ₂[g↦vf]) (prop.term (term.unop unop.isFunc g))
           = prop.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from prop.subst_env.term,
        have ⊨ prop.erased_n (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from this.symm ▸ h5,
        show ⊨ prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)),
        from valid.instantiated_n_of_erased_n this
      ),

      let forallp := prop.implies R.to_prop (prop.pre g gx)
                  ⋀ prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop) in
      let pfunc: prop := prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S)) in

      have h4: ∀v, ⊨ vc.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp).instantiated_n, from (
        assume v: value,

        have h5: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))).instantiated_n, from (
          have h6: ⊨ vc.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).instantiated_p
                                (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).instantiated_n, from valid.implies.mp (
            assume h8: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).instantiated_p,
            have vc.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop.instantiated_p
                = (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).instantiated_p, from instantiated_p_distrib_subst_env,
            have ⊨ vc.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop.instantiated_p, from this.symm ▸ h8,
            have h9: ⊨ vc.pre vf v, from valid.pre.mp this,
            have term.subst gx v gx = v, from term.subst.var.same,
            have h10: ⊨ vc.pre vf (term.subst gx v gx), from this.symm ▸ h9,
            have ¬(gx = g ∨ gx ∈ σ₂), from not_or_distrib.mpr ⟨g_neq_gx.symm, gx_not_free_in_σ₂⟩,
            have gx ∉ (σ₂[g↦vf]), from (mt env.contains.inv) this,
            have (σ₂[g↦vf]) gx = none, from env.contains_apply_equiv.left.mpr this,
            have term.subst_env (σ₂[g↦vf]) gx = gx, from term.subst_env.var.left.mp this,
            have h11: ⊨ vc.pre vf (term.subst gx v (term.subst_env (σ₂[g↦vf]) gx)),
            from this.symm ▸ h10,
            have term.subst_env (σ₂[g↦vf][gx↦v]) gx = term.subst gx v (term.subst_env (σ₂[g↦vf]) gx),
            by unfold term.subst_env,
            have h12: ⊨ vc.pre vf (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from this.symm ▸ h11,
            have term.subst gx v (term.value vf) = vf, by unfold term.subst,
            have ⊨ vc.pre (term.subst gx v vf) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from this.symm ▸ h12,
            have h13: ⊨ vc.pre (term.subst gx v (term.subst_env (σ₂[g↦vf]) g)) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from g_subst.symm ▸ this,
            have term.subst_env (σ₂[g↦vf][gx↦v]) g = term.subst gx v (term.subst_env (σ₂[g↦vf]) g),
            by unfold term.subst_env,
            have h14: ⊨ vc.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from this.symm ▸ h13,
            have prop.erased_n (prop.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx))
               = (vc.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx)),
            by unfold prop.erased_n,
            have h15: ⊨ (prop.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx)).erased_n,
            from this.symm ▸ h14,
            have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)
               = prop.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from prop.subst_env.pre,
            have ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).erased_n, from this.symm ▸ h15,
            show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).instantiated_n,
            from valid.instantiated_n_of_erased_n this
          ),
          have h8: ⊨ (prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop)
                                   (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx))).instantiated_n,
          from valid.instantiated_n_implies h6,
          have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))
             = prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop)
                            (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)),
          from prop.subst_env.implies,
          show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))).instantiated_n,
          from this.symm ▸ h8
        ),

        have h6: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                     (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated_n, from (
          have h7: ⊨ vc.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)).instantiated_p
                                (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).instantiated_n,
          from valid.implies.mp (
            assume h8: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)).instantiated_p,
            have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)
               = prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from prop.subst_env.post,
            have ⊨ (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx))
                          .instantiated_p,
            from this ▸ h8,
            have h9: ⊨ (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx))
                          .erased_p, from valid.erased_p_of_instantiated_p this,
            have (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx)).erased_n
                = vc.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            by unfold prop.erased_n,
            have h10: ⊨ vc.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from this ▸ h9,
            have term.subst_env (σ₂[g↦vf][gx↦v]) g = term.subst gx v (term.subst_env (σ₂[g↦vf]) g),
            by unfold term.subst_env,
            have ⊨ vc.post (term.subst gx v (term.subst_env (σ₂[g↦vf]) g)) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from this ▸ h10,
            have h11: ⊨ vc.post (term.subst gx v vf) (term.subst_env (σ₂[g↦vf][gx↦v]) gx), from g_subst ▸ this,
            have term.subst gx v (term.value vf) = vf, by unfold term.subst,
            have h12: ⊨ vc.post vf (term.subst_env (σ₂[g↦vf][gx↦v]) gx), from this ▸ h11,
            have term.subst_env (σ₂[g↦vf][gx↦v]) gx = term.subst gx v (term.subst_env (σ₂[g↦vf]) gx),
            by unfold term.subst_env,
            have h13: ⊨ vc.post vf (term.subst gx v (term.subst_env (σ₂[g↦vf]) gx)), from this ▸ h12,
            have ¬(gx = g ∨ gx ∈ σ₂), from not_or_distrib.mpr ⟨g_neq_gx.symm, gx_not_free_in_σ₂⟩,
            have gx ∉ (σ₂[g↦vf]), from (mt env.contains.inv) this,
            have (σ₂[g↦vf]) gx = none, from env.contains_apply_equiv.left.mpr this,
            have term.subst_env (σ₂[g↦vf]) gx = gx, from term.subst_env.var.left.mp this,
            have h14: ⊨ vc.post vf (term.subst gx v gx), from this ▸ h13,
            have term.subst gx v gx = v, from term.subst.var.same,
            have ⊨ vc.post vf v, from this ▸ h14,
            have h15: (σ₂[g↦vf][gx↦v] ⊨ (Q₃ (term.app g gx) ⋀ S.to_prop).instantiated_n),
            from valid.post σ₂_verified func_verified this,
            have vc.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop).instantiated_n
              = (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).instantiated_n,
            from instantiated_n_distrib_subst_env,
            show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).instantiated_n,
            from this ▸ h15
          ),
          have h8: ⊨ (prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx))
                                   (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated_n,
          from valid.instantiated_n_implies h7,
          have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop))
             = prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx))
                            (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)),
          from prop.subst_env.implies,
          show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                      (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated_n,
          from this.symm ▸ h8
        ),

        have ⊨ ((prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))).instantiated_n ⋀
                (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                                (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated_n),
        from valid.and.mp ⟨h5, h6⟩,
        have h7: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx)) ⋀
                    prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                                   (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated_n,
        from valid.instantiated_n_and this,
        have prop.subst_env (σ₂[g↦vf][gx↦v]) forallp
           = (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx)) ⋀
             prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop))),
        from prop.subst_env.and,
        have h8: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) forallp).instantiated_n, from this.symm ▸ h7,
        have prop.subst_env (σ₂[g↦vf][gx↦v]) forallp = prop.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp),
        by unfold prop.subst_env,
        have h9: ⊨ (prop.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp)).instantiated_n, from this ▸ h8,
        have vc.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp).instantiated_n
           = (prop.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp)).instantiated_n, from instantiated_n_distrib_subst,
        show ⊨ vc.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp).instantiated_n, from this.symm ▸ h9
      ),

      have h5: ⊨ prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)), from (
        have h6: ⊨ vc.univ gx (prop.subst_env (σ₂[g↦vf]) forallp).instantiated_n, from valid.univ.mp h4,
        have prop.instantiated_n (prop.forallc gx (term.subst_env (σ₂[g↦vf]) g) (prop.subst_env (σ₂[g↦vf]) forallp))
           = vc.univ gx (prop.subst_env (σ₂[g↦vf]) forallp).instantiated_n, from instantiated_n.forallc,
        have h7: ⊨ prop.instantiated_n (prop.forallc gx (term.subst_env (σ₂[g↦vf]) g) (prop.subst_env (σ₂[g↦vf]) forallp)), from this.symm ▸ h6,
        have ¬(gx = g ∨ gx ∈ σ₂), from not_or_distrib.mpr ⟨g_neq_gx.symm, gx_not_free_in_σ₂⟩,
        have gx ∉ (σ₂[g↦vf]), from (mt env.contains.inv) this,
        have (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)
            = prop.forallc gx (term.subst_env (σ₂[g↦vf]) g) (prop.subst_env (σ₂[g↦vf]) forallp)),
        from prop.subst_env.forallc this,
        show ⊨ prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)), from this.symm ▸ h7
      ),

      have ⊨ (prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)) ⋀
                  prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp))),
      from valid.and.mp ⟨h2, h5⟩,
      have h7: ⊨ prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g) ⋀
                                    prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)),
      from valid.instantiated_n_and this,
      have prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp)
         = (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g) ⋀ prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)),
      from prop.subst_env.and,
      have h8: ⊨ prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp)),
      from this.symm ▸ h7,
      have prop.func g gx R.to_prop (Q₃ (term.app g gx) ⋀ S.to_prop)
         = (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp),
      by unfold prop.func,
      have ⊨ prop.instantiated_n (prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
      from this.symm ▸ h8,
      have h9: ⊨ prop.instantiated_n pfunc, from this,

      have h10: (∀x, x ∉ FV pfunc), from (
        have ⊢ (σ₂[g↦vf]) : Q₂
          ⋀ (g ≡ (vf))
          ⋀ prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S)),
        from env.vcgen.func g_not_free_in_σ₂ g_not_free_in_σ₂ gx_not_free_in_σ₂ g_neq_gx
             σ₂_verified σ₂_verified gx_free_in_R R_fv S_fv func_verified S_valid,
        prop_func_closed func_verified this
      ),

      have h11: (∀x, x ∉ FV pfunc.instantiated_n), from (
        assume x: var,
        assume : x ∈ FV pfunc.instantiated_n,
        have x ∈ FV pfunc.erased_n, from free_in_erased_n_of_free_in_instantiated_n this,
        have x ∈ FV pfunc.erased_p ∨ x ∈ FV pfunc.erased_n, from or.inr this,
        have x ∈ FV pfunc, from free_of_erased_free this,
        show «false», from (h10 x) this
      ),

      have vc.subst_env (σ₁[f↦vf]) pfunc.instantiated_n = pfunc.instantiated_n,
      from unchanged_of_subst_env_nonfree_vc h11 (σ₁[f↦vf]),
      have (σ₁[f↦vf]) ⊨ pfunc.instantiated_n, from this.symm ▸ h9,

      have (σ₁[f↦vf]) ⊨ ((prop.term (f ≡ vf)).instantiated_n ⋀ prop.instantiated_n pfunc), from valid_env.and h1.right this,
      have (σ₁[f↦vf]) ⊨ ((prop.term (f ≡ vf)) ⋀ pfunc).instantiated_n, from valid_env.instantiated_n_and this,
      have (σ₁[f↦vf]) ⊨ Q₁.instantiated_n ⋀ ((prop.term (f ≡ vf)) ⋀ pfunc).instantiated_n, from valid_env.and h1.left this,
      show (σ₁[f↦vf]) ⊨ (Q₁ ⋀ (f ≡ vf) ⋀ pfunc).instantiated_n,
      from valid_env.instantiated_n_and this
    )}
  end

lemma env_translation_valid {R: spec} {H: history} {P: prop} {σ: env}:
  (⊢ σ: P) → (σ ⊨ R.to_prop.instantiated_n) → σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_p :=
  assume env_verified: (⊢ σ : P),
  assume R_valid: (σ ⊨ R.to_prop.instantiated_n),
  have h1: σ ⊨ prop.instantiated_n ↑H, from history_valid σ,
  have h2: σ ⊨ P.instantiated_n, from env_translation_instantiated_n_valid env_verified,
  have σ ⊨ (prop.instantiated_n ↑H ⋀ P.instantiated_n), from valid_env.and h1 h2,
  have σ ⊨ (↑H ⋀ P).instantiated_n, from valid_env.instantiated_n_and this,
  have σ ⊨ R.to_prop.instantiated_n ⋀ (↑H ⋀ P).instantiated_n, from valid_env.and R_valid this,
  have σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_n, from valid_env.instantiated_n_and this,
  show σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_p, from valid_env.instantiated_p_of_instantiated_n this

lemma consequent_of_H_P {R: spec} {H: history} {σ: env} {P Q: prop}:
  (⊢ σ: P) → (σ ⊨ R.to_prop.instantiated_n) → ⟪prop.implies (R ⋀ ↑H ⋀ P) Q⟫ → no_instantiations Q → σ ⊨ Q.erased_n :=
  assume env_verified: (⊢ σ : P),
  assume R_valid: (σ ⊨ R.to_prop.instantiated_n),
  assume impl_vc: ⟪prop.implies (R ⋀ ↑H ⋀ P) Q⟫,
  assume : no_instantiations Q,
  have h1: (prop.implies (R ⋀ ↑H ⋀ P) Q).instantiated_n = vc.or (↑R ⋀ ↑H ⋀ P).not.instantiated_n Q.erased_n,
  from or_dist_of_no_instantiations_n this,
  have h2: (↑R ⋀ ↑H ⋀ P).not.instantiated_n = (↑R ⋀ ↑H ⋀ P).instantiated_p.not, from not_dist_instantiated_n,
  have σ ⊨ (prop.implies (↑R ⋀ ↑H ⋀ P) Q).instantiated_n, from impl_vc σ,
  have σ ⊨ vc.or (↑R ⋀ ↑H ⋀ P).instantiated_p.not Q.erased_n, from h2 ▸ h1 ▸ this,
  have h4: σ ⊨ vc.implies (↑R ⋀ ↑H ⋀ P).instantiated_p Q.erased_n, from this,
  have σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_p, from env_translation_valid env_verified R_valid,
  show σ ⊨ Q.erased_n, from valid_env.mp h4 this

lemma env_translation_call_valid {R: spec} {H: history} {P: prop} {σ: env} {f x: var}:
  (⊢ σ: P) → (σ ⊨ R.to_prop.instantiated_n) → σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_p :=
  assume env_verified: (⊢ σ : P),
  assume R_valid: (σ ⊨ R.to_prop.instantiated_n),
  have h1: σ ⊨ prop.instantiated_n ↑H, from history_valid σ,
  have h2: σ ⊨ P.instantiated_n, from env_translation_instantiated_n_valid env_verified,
  have σ ⊨ (prop.instantiated_n ↑H ⋀ P.instantiated_n), from valid_env.and h1 h2,
  have σ ⊨ (↑H ⋀ P).instantiated_n, from valid_env.instantiated_n_and this,
  have σ ⊨ R.to_prop.instantiated_n ⋀ (↑H ⋀ P).instantiated_n, from valid_env.and R_valid this,
  have h3: σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_n, from valid_env.instantiated_n_and this,
  have h4: ⊨ value.true, from valid.tru,
  have term.subst_env σ value.true = value.true, from term.subst_env.value,
  have h5: ⊨ term.subst_env σ value.true, from this.symm ▸ h4,
  have vc.subst_env σ value.true = vc.term (term.subst_env σ value.true), from vc.subst_env.term,
  have h6: σ ⊨ value.true, from this.symm ▸ h5,
  have (prop.call f x).erased_n = vc.term value.true, by unfold prop.erased_n,
  have σ ⊨ (prop.call f x).erased_n, from this.symm ▸ h6,
  have σ ⊨ (prop.call f x).instantiated_n, from valid_env.instantiated_n_of_erased_n this,
  have σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_n ⋀ (prop.call f x).instantiated_n, from valid_env.and h3 this,
  have σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n, from valid_env.instantiated_n_and this,
  show σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_p, from valid_env.instantiated_p_of_instantiated_n this

lemma consequent_of_H_P_call {R: spec} {H: history} {σ: env} {P Q: prop} {f x: var}:
  (⊢ σ: P) → (σ ⊨ R.to_prop.instantiated_n) → ⟪prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q⟫ → no_instantiations Q → σ ⊨ Q.erased_n :=
  assume env_verified: (⊢ σ : P),
  assume R_valid: (σ ⊨ R.to_prop.instantiated_n),
  assume impl_vc: ⟪prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q⟫,
  assume : no_instantiations Q,
  have h1: (prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q).instantiated_n
         = vc.or ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).not.instantiated_n Q.erased_n,
  from or_dist_of_no_instantiations_n this,
  have h2: ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).not.instantiated_n = ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_p.not,
  from not_dist_instantiated_n,
  have σ ⊨ (prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q).instantiated_n, from impl_vc σ,
  have σ ⊨ vc.or ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_p.not Q.erased_n, from h2 ▸ h1 ▸ this,
  have h4: σ ⊨ vc.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_p Q.erased_n, from this,
  have σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_p, from env_translation_call_valid env_verified R_valid,
  show σ ⊨ Q.erased_n, from valid_env.mp h4 this

lemma dominates_of_pre {σ: env} {P P': prop}:
    ((σ ⊨ P.instantiated_p) →
    (σ ⊨ P'.instantiated_p) ∧
    (calls_p_subst σ P' ⊆ calls_p_subst σ P) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers_p P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers_p P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v])))) →
    dominates σ P P' :=
  
  assume h: 
    (σ ⊨ P.instantiated_p) →
    (σ ⊨ P'.instantiated_p) ∧
    (calls_p_subst σ P' ⊆ calls_p_subst σ P) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers_p P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers_p P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v]))),
  have
    dominates' P' P σ = (
    (σ ⊨ P.instantiated_p) →
    ((σ ⊨ P'.instantiated_p) ∧
    (calls_p_subst σ P' ⊆ calls_p_subst σ P) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers_p P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers_p P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v]))))),
  by unfold1 dominates',
  have dominates' P' P σ, from this.symm ▸ h,
  show dominates σ P P', from this

lemma dominates_of {σ: env} {P P': prop}:
    (σ ⊨ vc.implies P.instantiated_p P'.instantiated_p) →
    (calls_p_subst σ P' ⊆ calls_p_subst σ P) →
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers_p P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers_p P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v]))) →
    dominates σ P P' :=
  
  assume : σ ⊨ vc.implies P.instantiated_p P'.instantiated_p,
  have h_impl: (σ ⊨ P.instantiated_p) → σ ⊨ P'.instantiated_p, from valid_env.mp this,
  assume h_calls: calls_p_subst σ P' ⊆ calls_p_subst σ P,
  assume h_quantifiers_p:
    ∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers_p P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers_p P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v])),
  
  have h: 
    (σ ⊨ P.instantiated_p) →
    (σ ⊨ P'.instantiated_p) ∧
    (calls_p_subst σ P' ⊆ calls_p_subst σ P) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers_p P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers_p P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v]))),
  from λh, ⟨h_impl h, ⟨h_calls, h_quantifiers_p⟩⟩,
  have
    dominates' P' P σ = (
    (σ ⊨ P.instantiated_p) →
    ((σ ⊨ P'.instantiated_p) ∧
    (calls_p_subst σ P' ⊆ calls_p_subst σ P) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers_p P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers_p P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v]))))),
  by unfold1 dominates',
  have dominates' P' P σ, from this.symm ▸ h,
  show dominates σ P P', from this

lemma dominates.elim {σ: env} {P P': prop}:
    dominates σ P P' →
    (σ ⊨ P.instantiated_p) →
    (σ ⊨ P'.instantiated_p) ∧
    (calls_p_subst σ P' ⊆ calls_p_subst σ P) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers_p P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers_p P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v]))) :=
  
  assume : dominates σ P P',
  have h: dominates' P' P σ, from this,
  have
    dominates' P' P σ = (
    (σ ⊨ P.instantiated_p) →
    ((σ ⊨ P'.instantiated_p) ∧
    (calls_p_subst σ P' ⊆ calls_p_subst σ P) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers_p P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers_p P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v]))))),
  by unfold1 dominates',
  show 
    (σ ⊨ P.instantiated_p) →
    ((σ ⊨ P'.instantiated_p) ∧
    (calls_p_subst σ P' ⊆ calls_p_subst σ P) ∧
    (∀(t': term) (x: var) (Q': prop) (h: callquantifier.mk t' x Q' ∈ quantifiers_p P'),
                          have Q'.size < P'.size, from quantifiers_smaller_than_prop.left h,
    ∃(t: term) (Q: prop), callquantifier.mk t x Q ∈ quantifiers_p P ∧
                          (∀v: value, dominates' Q' Q (σ[x↦v])))),
  from this ▸ h
