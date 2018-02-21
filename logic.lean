import .syntax .notations .evaluation .substitution .qi .vcgen

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
  σ[f↦value.func f x R S e σ][x↦vₓ]⊨ R.to_prop.instantiated_n
  →
  ⊨ vc.pre (value.func f x R S e σ) vₓ

axiom valid.post {vₓ: value} {σ: env} {Q: prop} {Q₂: propctx} {f x: var} {R S: spec} {e: exp}:
  (⊢ σ : Q) →
  (Q && spec.func f x R S && R ⊢ e : Q₂) →
  ⊨ vc.post (value.func f x R S e σ) vₓ
  →
  (σ[f↦value.func f x R S e σ][x↦vₓ] ⊨ (Q₂ (term.app f x) && S.to_prop).instantiated)

-- axioms about instantiations

--  inst(P)   ⇒   inst_n(P)
--         ⇘    ⇗  
--     ⇑      P      ⇓
--         ⇗    ⇘ 
-- erased(P)  ⇒  erased_n(P)

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
  (calls P' = calls P) →
  (quantifiers P' = quantifiers P) →
  σ ⊨ vc.implies P'.instantiated_n P.instantiated_n →
  σ ⊨ vc.implies (P' && Q).instantiated_n (P && Q).instantiated_n

-- lemmas

lemma valid.instantiated_of_erased {P: prop}: ⊨ P.erased → ⊨ P.instantiated :=
  assume h: ⊨ P.erased,
  have P.erased = vc.subst_env env.empty P.erased, by unfold vc.subst_env,
  have env.empty ⊨ P.erased, from this ▸ h,
  have h2: env.empty ⊨ P.instantiated, from valid_env.instantiated_of_erased this,
  have  vc.subst_env env.empty P.instantiated = P.instantiated, by unfold vc.subst_env,
  show ⊨ P.instantiated, from this ▸ h2

lemma valid.instantiated_n_of_instantiated {P: prop}: ⊨ P.instantiated → ⊨ P.instantiated_n :=
  assume h: ⊨ P.instantiated,
  have P.instantiated = vc.subst_env env.empty P.instantiated, by unfold vc.subst_env,
  have env.empty ⊨ P.instantiated, from this ▸ h,
  have h2: env.empty ⊨ P.instantiated_n, from valid_env.instantiated_n_of_instantiated this,
  have  vc.subst_env env.empty P.instantiated_n = P.instantiated_n, by unfold vc.subst_env,
  show ⊨ P.instantiated_n, from this ▸ h2

lemma valid.erased_n_of_instantiated_n {P: prop}: ⊨ P.instantiated_n → ⊨ P.erased_n :=
  assume h: ⊨ P.instantiated_n,
  have P.instantiated_n = vc.subst_env env.empty P.instantiated_n, by unfold vc.subst_env,
  have env.empty ⊨ P.instantiated_n, from this ▸ h,
  have h2: env.empty ⊨ P.erased_n, from valid_env.erased_n_of_instantiated_n this,
  have vc.subst_env env.empty P.erased_n = P.erased_n, by unfold vc.subst_env,
  show ⊨ P.erased_n, from this ▸ h2

lemma valid.instantiated_and {P Q: prop}:
      ⊨ (P.instantiated && Q.instantiated) → ⊨ (P && Q).instantiated :=
  assume h: ⊨ (P.instantiated && Q.instantiated),
  have (P.instantiated && Q.instantiated) = vc.subst_env env.empty (P.instantiated && Q.instantiated),
  by unfold vc.subst_env,
  have env.empty ⊨ (P.instantiated && Q.instantiated), from this ▸ h,
  have h2: env.empty ⊨ (P && Q).instantiated, from valid_env.instantiated_and this,
  have vc.subst_env env.empty (P && Q).instantiated = (P && Q).instantiated, by unfold vc.subst_env,
  show ⊨ (P && Q).instantiated, from this ▸ h2

lemma valid.instantiated_or {P Q: prop}:
      ⊨ (P.instantiated || Q.instantiated) → ⊨ (P || Q).instantiated :=
  assume h: ⊨ (P.instantiated || Q.instantiated),
  have (P.instantiated || Q.instantiated) = vc.subst_env env.empty (P.instantiated || Q.instantiated),
  by unfold vc.subst_env,
  have env.empty ⊨ (P.instantiated || Q.instantiated), from this ▸ h,
  have h2: env.empty ⊨ (P || Q).instantiated, from valid_env.instantiated_or this,
  have vc.subst_env env.empty (P || Q).instantiated = (P || Q).instantiated, by unfold vc.subst_env,
  show ⊨ (P || Q).instantiated, from this ▸ h2

lemma valid.instantiated_implies {P Q: prop}:
      ⊨ (vc.implies P.instantiated_n Q.instantiated) → ⊨ (prop.implies P Q).instantiated :=
  assume : ⊨ (vc.implies P.instantiated_n Q.instantiated),
  have h1: ⊨ (vc.or P.instantiated_n.not Q.instantiated), from this,
  have P.not.instantiated = P.instantiated_n.not, from not_dist_instantiated,
  have ⊨ (vc.or P.not.instantiated Q.instantiated), from this.symm ▸ h1,
  have ⊨ (prop.or P.not Q).instantiated, from valid.instantiated_or this,
  show ⊨ (prop.implies P Q).instantiated, from this

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

lemma history_valid {H: callhistory}: ⟪calls_to_prop H⟫ :=
  assume σ: env,
  begin
    induction H,
    case list.nil { from (
      have h1: σ ⊨ value.true, from valid_env.true,
      have (prop.term value.true).erased = vc.term value.true, by unfold prop.erased,
      have σ ⊨ (prop.term value.true).erased, from this ▸ h1,
      have h2: σ ⊨ (prop.term value.true).instantiated, from valid_env.instantiated_of_erased this,
      have calls_to_prop list.nil = value.true, by unfold calls_to_prop,
      show σ ⊨ (calls_to_prop list.nil).instantiated, from this ▸ h2
    )},
    case list.cons h rest ih {
      cases h,
      case historyitem.nop { from (
        have h2: σ ⊨ (calls_to_prop rest).instantiated, from ih,
        have calls_to_prop (historyitem.nop :: rest) = calls_to_prop rest, by unfold calls_to_prop,
        show σ ⊨ (calls_to_prop (historyitem.nop :: rest)).instantiated, from this.symm ▸ h2
      )},
      case historyitem.call f x R S e σ₂ v { from (
        have h1: σ ⊨ value.true, from valid_env.true,
        have (prop.call (value.func f x R S e σ₂) v).erased = vc.term value.true, by unfold prop.erased,
        have σ ⊨ (prop.call (value.func f x R S e σ₂) v).erased, from this ▸ h1,
        have h2: σ ⊨ (prop.call (value.func f x R S e σ₂) v).instantiated, from valid_env.instantiated_of_erased this,
        have h3: σ ⊨ (calls_to_prop rest).instantiated, from ih,
        have σ ⊨ ((prop.call (value.func f x R S e σ₂) v).instantiated && (calls_to_prop rest).instantiated),
        from valid_env.and h2 h3,
        have h4: σ ⊨ (prop.call (value.func f x R S e σ₂) v && calls_to_prop rest).instantiated,
        from valid_env.instantiated_and this,
        have calls_to_prop (call f x R S e σ₂ v :: rest)
          = prop.call (value.func f x R S e σ₂) v && calls_to_prop rest,
        by unfold calls_to_prop,
        show σ ⊨ (calls_to_prop (call f x R S e σ₂ v :: rest)).instantiated, from this ▸ h4
      )}
    }
end
