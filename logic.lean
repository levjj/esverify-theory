import .syntax .etc .props

-- instantiation

constant prop.instantiated_p: prop → qfprop

constant prop.instantiated_n: prop → qfprop

axiom instantiated.not {P: prop}: P.not.instantiated_p = P.instantiated_n.not

def prop.erased_p: prop → qfprop
| (prop.term t)        := qfprop.term t
| (prop.not P)         := qfprop.not P.erased_n
| (prop.and P₁ P₂)     := P₁.erased_p && P₂.erased_p
| (prop.or P₁ P₂)      := P₁.erased_p || P₂.erased_p
| (prop.pre t₁ t₂)     := qfprop.pre t₁ t₂
| (prop.pre₁ op t)     := qfprop.pre₁ op t
| (prop.pre₂ op t₁ t₂) := qfprop.pre₂ op t₁ t₂
| (prop.post t₁ t₂)    := qfprop.post t₁ t₂
| (prop.call t₁ t₂)    := qfprop.call t₁ t₂
| (prop.forallc x t P) := qfprop.forallc x t p.to_propctx
| (prop.exist x P)     := qfprop.exist x p.to_propctx

 -- propositions without quantifiers or call triggers do not participate in instantiations
axiom and_dist_of_no_instantiations {P: prop} {Q: qfprop}: (P && Q).instantiated_p = P.instantiated_p && Q

axiom or_dist_of_no_instantiations {P: prop} {Q: qfprop}: (P || Q).instantiated_p = P.instantiated_p || Q

-- substitution

def term.subst (x: var) (v: value): term → term
| (term.value v')       := v'
| (term.var y)          := if x = y then v else y
| (term.unop op t)      := term.unop op t.subst
| (term.binop op t₁ t₂) := term.binop op t₁.subst t₂.subst
| (term.app t₁ t₂)      := term.app t₁.subst t₂.subst

def spec.subst (x: var) (v: value): spec → spec
| (spec.term t) :=
    spec.term (term.subst x v t)
| (spec.not R) :=
    have R.size < R.not.size, from lt_of_add_one,
    spec.not R.subst
| (spec.and R S) :=
    have R.size < (R && S).size, from lt_of_add.left,
    have S.size < (R && S).size, from lt_of_add.right,
    R.subst && S.subst
| (spec.or R S) :=
    have R.size < (R || S).size, from lt_of_add.left,
    have S.size < (R || S).size, from lt_of_add.right,
    R.subst || S.subst
| (spec.func t y R S) :=
    have R.size < (R && S).size, from lt_of_add.left,
    have S.size < (R && S).size, from lt_of_add.right,
    if x = y
    then spec.func (term.subst x v t) x R S
    else spec.func (term.subst x v t) y R.subst S.subst

def spec.subst_env: env → spec → spec
| env.empty R := R
| (σ[x↦v]) R :=
    have σ.size < (σ[x ↦ v].size), from lt_of_add_one,
    spec.subst x v (spec.subst_env σ R)

def qfprop.subst (x: var) (v: value): qfprop → qfprop
| (qfprop.term t)        := term.subst x v t
| (qfprop.not P)         := qfprop.not P.subst
| (qfprop.and P Q)       := P.subst && Q.subst
| (qfprop.or P Q)        := P.subst || Q.subst
| (qfprop.pre t₁ t₂)     := qfprop.pre (term.subst x v t₁) (term.subst x v t₂)
| (qfprop.pre₁ op t)     := qfprop.pre₁ op (term.subst x v t)
| (qfprop.pre₂ op t₁ t₂) := qfprop.pre₂ op (term.subst x v t₁) (term.subst x v t₂)
| (qfprop.post t₁ t₂)    := qfprop.post (term.subst x v t₁) (term.subst x v t₂)

def qfprop.subst_env: env → qfprop → qfprop
| env.empty P := P
| (σ[x↦v]) P :=
    have σ.size < (σ[x ↦ v].size), from lt_of_add_one,
    qfprop.subst x v (qfprop.subst_env σ P)

-- validity

inductive valid : qfprop → Prop
notation `⊨` p: 100 := valid p

| tru: ⊨ value.true

| eq {t: term}: ⊨ term.binop binop.eq t t

| and {Q P: qfprop}: ⊨ P → ⊨ Q → ⊨ (P && Q)

| orl {Q P: qfprop}: ⊨ P → ⊨ (P || Q)

| orr {Q P: qfprop}: ⊨ Q → ⊨ (P || Q)

| mp {Q P: qfprop}: ⊨ qfprop.implies P Q → ⊨ P → ⊨ Q

notation `⊨` p: 100 := valid p
notation σ `⊨` p: 100 := valid (qfprop.subst_env σ p)

-- axioms about instantiation

axiom instantiated_p_of_erased_p {σ: env} {P: prop} : σ ⊨ P.erased_p → σ ⊨ P.instantiated_p
axiom instantiated_n_of_instantiated_p {σ: env} {P: prop} : σ ⊨ P.instantiated_p → σ ⊨ P.instantiated_n
axiom erased_n_of_instantiated_n {σ: env} {P: prop} : σ ⊨ P.instantiated_n → σ ⊨ P.erased_n

-- notation ⟪ P ⟫

@[reducible]
def VC(P: prop) := ∀ (σ: env), σ ⊨ P.instantiated_p

notation `⟪` P `⟫`: 100 := VC P

-- lemmas

lemma free_of_subst_term {t: term} {x y: var} {v: value}:
          free_in_term x (term.subst y v t) → x ≠ y ∧ free_in_term x t :=
  assume x_free_in_subst: free_in_term x (term.subst y v t),
  begin
    induction t with v' z unop t₁ t₁_ih binop t₂ t₃ t₂_ih t₃_ih t₄ t₅ t₄_ih t₅_ih,
    show x ≠ y ∧ free_in_term x (term.value v'), from (
      have term.subst y v (term.value v') = v', by unfold term.subst,
      have free_in_term x v', from this ▸ x_free_in_subst,
      show x ≠ y ∧ free_in_term x (term.value v'), from absurd this free_in_term.value.inv
    ),
    show x ≠ y ∧ free_in_term x (term.var z), from (
      have hite: term.subst y v (term.var z) = (if y = z then v else z), by unfold term.subst,
      if y_is_z: y = z then
        have term.subst y v (term.var z) = v, by simp * at *,
        have free_in_term x v, from this ▸ x_free_in_subst,
        show x ≠ y ∧ free_in_term x (term.var z), from absurd this free_in_term.value.inv
      else
        have term.subst y v (term.var z) = z, by simp * at *,
        have free_in_term x z, from this ▸ x_free_in_subst,
        have x_is_z: x = z, from free_in_term.var.inv this,
        have x ≠ y, from x_is_z.symm ▸ (neq_symm y_is_z),
        show x ≠ y ∧ free_in_term x (term.var z), from ⟨this, x_is_z ▸ free_in_term.var x⟩
    ),
    show x ≠ y ∧ free_in_term x (term.unop unop t₁), from (
      have term.subst y v (term.unop unop t₁) = term.unop unop (term.subst y v t₁), by unfold term.subst,
      have free_in_term x (term.unop unop (term.subst y v t₁)), from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₁), from free_in_term.unop.inv this,
      have x ≠ y ∧ free_in_term x t₁, from t₁_ih this,
      show x ≠ y ∧ free_in_term x (term.unop unop t₁), from ⟨this.left, free_in_term.unop this.right⟩
    ),
    show x ≠ y ∧ free_in_term x (term.binop binop t₂ t₃), from (
      have term.subst y v (term.binop binop t₂ t₃) = term.binop binop (term.subst y v t₂) (term.subst y v t₃),
      by unfold term.subst,
      have free_in_term x (term.binop binop (term.subst y v t₂) (term.subst y v t₃)), from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₂) ∨ free_in_term x (term.subst y v t₃), from free_in_term.binop.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₂),
        have x ≠ y ∧ free_in_term x t₂, from t₂_ih this,
        show x ≠ y ∧ free_in_term x (term.binop binop t₂ t₃), from ⟨this.left, free_in_term.binop₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₃),
        have x ≠ y ∧ free_in_term x t₃, from t₃_ih this,
        show x ≠ y ∧ free_in_term x (term.binop binop t₂ t₃), from ⟨this.left, free_in_term.binop₂ this.right⟩
      )
    ),
    show x ≠ y ∧ free_in_term x (term.app t₄ t₅), from (
      have term.subst y v (term.app t₄ t₅) = term.app (term.subst y v t₄) (term.subst y v t₅),
      by unfold term.subst,
      have free_in_term x (term.app (term.subst y v t₄) (term.subst y v t₅)), from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₄) ∨ free_in_term x (term.subst y v t₅), from free_in_term.app.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₄),
        have x ≠ y ∧ free_in_term x t₄, from t₄_ih this,
        show x ≠ y ∧ free_in_term x (term.app t₄ t₅), from ⟨this.left, free_in_term.app₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₅),
        have x ≠ y ∧ free_in_term x t₅, from t₅_ih this,
        show x ≠ y ∧ free_in_term x (term.app t₄ t₅), from ⟨this.left, free_in_term.app₂ this.right⟩
      )
    )
  end

lemma free_of_subst_spec {R: spec} {x y: var} {v: value}:
          free_in_prop x (spec.subst y v R) → x ≠ y ∧ free_in_prop x R :=
  sorry
  -- assume x_free_in_subst: free_in_prop x (spec.subst y v R),
  -- begin
  --   induction R with t S₁ S₁_ih S₂ S₃ S₂_ih S₃_ih
  --                    S₄ S₅ S₄_ih S₅_ih f fx S₆ S₇ S₆_ih S₇_ih,
  --   show x ≠ y ∧ free_in_prop x (spec.term t).to_prop, from (
  --     have spec.subst y v (spec.term t) = spec.term (term.subst y v t), by unfold spec.subst,
  --     have x_free_in_term': free_in_prop x (spec.term (term.subst y v t)).to_prop, from this ▸ x_free_in_subst,
  --     have (spec.term (term.subst y v t)).to_prop = prop.term (term.subst y v t), by unfold spec.to_prop,
  --     have free_in_prop x (term.subst y v t), from this ▸ x_free_in_term',
  --     have free_in_term x (term.subst y v t), from free_in_prop.term.inv this,
  --     have x ≠ y ∧ free_in_term x t, from free_of_subst_term this,
  --     show x ≠ y ∧ free_in_prop x (spec.term t).to_prop, from ⟨this.left, free_in_prop.term this.right⟩
  --   ),
  --   show x ≠ y ∧ free_in_prop x S₁.not.to_prop, from (
  --     have (spec.subst y v S₁.not = (spec.subst y v S₁).not), by unfold spec.subst,
  --     have x_free_in_not': free_in_prop x (spec.subst y v S₁).not.to_prop, from this ▸ x_free_in_subst,
  --     have (spec.subst y v S₁).not.to_prop = (spec.subst y v S₁).to_prop.not, by unfold spec.to_prop,
  --     have free_in_prop x (spec.subst y v S₁).to_prop.not, from this ▸ x_free_in_not',
  --     have free_in_prop x (spec.subst y v S₁).to_prop, from free_in_prop.not.inv this,
  --     have x ≠ y ∧ free_in_prop x S₁.to_prop, from S₁_ih this,
  --     show x ≠ y ∧ free_in_prop x S₁.not.to_prop, from ⟨this.left, free_in_prop.not this.right⟩
  --   ),
  --   show x ≠ y ∧ free_in_prop x (S₂ & S₃).to_prop, from (
  --     have spec.subst y v (spec.and S₂ S₃) = (spec.subst y v S₂ & spec.subst y v S₃), by unfold spec.subst,
  --     have x_free_in_and': free_in_prop x (spec.subst y v S₂ & spec.subst y v S₃).to_prop, from this ▸ x_free_in_subst,
  --     have (spec.and (spec.subst y v S₂) (spec.subst y v S₃)).to_prop
  --        = ((spec.subst y v S₂).to_prop & (spec.subst y v S₃).to_prop),
  --     by unfold spec.to_prop,
  --     have free_in_prop x ((spec.subst y v S₂).to_prop & (spec.subst y v S₃).to_prop), from this ▸ x_free_in_and',
  --     have free_in_prop x (spec.subst y v S₂).to_prop ∨ free_in_prop x (spec.subst y v S₃).to_prop,
  --     from free_in_prop.and.inv this,
  --     or.elim this (
  --       assume : free_in_prop x (spec.subst y v S₂).to_prop,
  --       have x ≠ y ∧ free_in_prop x S₂.to_prop, from S₂_ih this,
  --       show x ≠ y ∧ free_in_prop x (S₂ & S₃).to_prop, from ⟨this.left, free_in_prop.and₁ this.right⟩
  --     ) (
  --       assume : free_in_prop x (spec.subst y v S₃).to_prop,
  --       have x ≠ y ∧ free_in_prop x S₃.to_prop, from S₃_ih this,
  --       show x ≠ y ∧ free_in_prop x (S₂ & S₃).to_prop, from ⟨this.left, free_in_prop.and₂ this.right⟩
  --     )
  --   ),
  --   show x ≠ y ∧ free_in_prop x (spec.or S₄ S₅).to_prop, from (
  --     have spec.subst y v (spec.or S₄ S₅) = spec.or (spec.subst y v S₄) (spec.subst y v S₅), by unfold spec.subst,
  --     have x_free_in_or': free_in_prop x (spec.or (spec.subst y v S₄) (spec.subst y v S₅)).to_prop,
  --     from this ▸ x_free_in_subst,
  --     have (spec.or (spec.subst y v S₄) (spec.subst y v S₅)).to_prop
  --        = (prop.or (spec.subst y v S₄).to_prop (spec.subst y v S₅).to_prop),
  --     by unfold spec.to_prop,
  --     have free_in_prop x (prop.or (spec.subst y v S₄).to_prop (spec.subst y v S₅).to_prop),
  --     from this ▸ x_free_in_or',
  --     have free_in_prop x (spec.subst y v S₄).to_prop ∨ free_in_prop x (spec.subst y v S₅).to_prop,
  --     from free_in_prop.or.inv this,
  --     or.elim this (
  --       assume : free_in_prop x (spec.subst y v S₄).to_prop,
  --       have x ≠ y ∧ free_in_prop x S₄.to_prop, from S₄_ih this,
  --       show x ≠ y ∧ free_in_prop x (spec.or S₄ S₅).to_prop, from ⟨this.left, free_in_prop.or₁ this.right⟩
  --     ) (
  --       assume : free_in_prop x (spec.subst y v S₅).to_prop,
  --       have x ≠ y ∧ free_in_prop x S₅.to_prop, from S₅_ih this,
  --       show x ≠ y ∧ free_in_prop x (spec.or S₄ S₅).to_prop, from ⟨this.left, free_in_prop.or₂ this.right⟩
  --     )
  --   ),
  --   show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from (
  --     if y_is_fx: y = fx then
  --       have h₁: spec.subst y v (spec.func f fx S₆ S₇) = spec.func (term.subst y v f) fx S₆ S₇,
  --       by { unfold spec.subst, simp * },
  --       let forallp := (prop.implies S₆.to_prop (prop.pre (term.subst y v f) fx)
  --                     & prop.implies (S₆.to_prop & prop.post (term.subst y v f) fx) S₇.to_prop) in
  --       have h₂: (spec.func (term.subst y v f) fx S₆ S₇).to_prop =
  --                (term.unop unop.isFunc (term.subst y v f) & prop.forallc fx (term.subst y v f) forallp),
  --       by unfold spec.to_prop,
  --       let forallp' := (prop.implies S₆.to_prop (prop.pre f fx)
  --                       & prop.implies (S₆.to_prop & prop.post f fx) S₇.to_prop) in
  --       have h₃: (spec.func f fx S₆ S₇).to_prop = (term.unop unop.isFunc f & prop.forallc fx f forallp'),
  --       by unfold spec.to_prop,
  --       have free_in_prop x (term.unop unop.isFunc (term.subst y v f) & prop.forallc fx (term.subst y v f) forallp),
  --       from h₂ ▸ h₁ ▸ x_free_in_subst,
  --       have free_in_prop x (term.unop unop.isFunc (term.subst y v f))
  --          ∨ free_in_prop x (prop.forallc fx (term.subst y v f) forallp),
  --       from free_in_prop.and.inv this,
  --       or.elim this (
  --         assume : free_in_prop x (term.unop unop.isFunc (term.subst y v f)),
  --         have free_in_term x (term.unop unop.isFunc (term.subst y v f)), from free_in_prop.term.inv this,
  --         have free_in_term x (term.subst y v f), from free_in_term.unop.inv this,
  --         have x_neq_y: x ≠ y, from (free_of_subst_term this).left,
  --         have free_in_term x f, from (free_of_subst_term this).right,
  --         have free_in_term x (term.unop unop.isFunc f), from free_in_term.unop this,
  --         have free_in_prop x (term.unop unop.isFunc f), from free_in_prop.term this,
  --         have free_in_prop x (term.unop unop.isFunc f & prop.forallc fx f forallp'), from free_in_prop.and₁ this,
  --         -- have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
  --         show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
  --       ) (
  --         assume : free_in_prop x (prop.forallc fx (term.subst y v f) forallp),
  --         have x_neq_fx: x ≠ fx, from (free_in_prop.forallc.inv this).left,
  --         have x_neq_y: x ≠ y, from y_is_fx.symm ▸ x_neq_fx,
  --         have free_in_term x (term.subst y v f) ∨ free_in_prop x forallp, from (free_in_prop.forallc.inv this).right,
  --         or.elim this (
  --           assume : free_in_term x (term.subst y v f),
  --           have free_in_term x f, from (free_of_subst_term this).right,
  --           have free_in_term x (term.unop unop.isFunc f), from free_in_term.unop this,
  --           have free_in_prop x (term.unop unop.isFunc f), from free_in_prop.term this,
  --           have free_in_prop x (term.unop unop.isFunc f & prop.forallc fx f forallp'), from free_in_prop.and₁ this,
  --           have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
  --           show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
  --         ) (
  --           assume : free_in_prop x forallp,
  --           or.elim (free_in_prop.and.inv this) (
  --             assume : free_in_prop x (prop.implies S₆.to_prop (prop.pre (term.subst y v f) fx)),
  --             or.elim (free_in_prop.implies.inv this) (
  --               assume : free_in_prop x S₆.to_prop,
  --               have free_in_prop x S₆.to_prop.not, from free_in_prop.not this,
  --               have free_in_prop x (prop.implies S₆.to_prop (prop.pre f fx)), from free_in_prop.or₁ this,
  --               have free_in_prop x forallp', from free_in_prop.and₁ this,
  --               have free_in_prop x (prop.forallc fx f forallp'), from free_in_prop.forallc₂ x_neq_fx this,
  --               have free_in_prop x (term.unop unop.isFunc f & prop.forallc fx f forallp'), from free_in_prop.and₂ this,
  --               have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
  --               show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
  --             ) (
  --               assume : free_in_prop x (prop.pre (term.subst y v f) fx),
  --               or.elim (free_in_prop.pre.inv this) (
  --                 assume : free_in_term x (term.subst y v f),
  --                 have free_in_term x f, from (free_of_subst_term this).right,
  --                 have free_in_term x (term.unop unop.isFunc f), from free_in_term.unop this,
  --                 have free_in_prop x (term.unop unop.isFunc f), from free_in_prop.term this,
  --                 have free_in_prop x (term.unop unop.isFunc f & prop.forallc fx f forallp'), from free_in_prop.and₁ this,
  --                 have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
  --                 show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
  --               ) (
  --                 assume : free_in_term x fx,
  --                 have x = fx, from free_in_term.var.inv this,
  --                 show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from absurd this x_neq_fx
  --               )
  --             )
  --           )
  --           (
  --             assume : free_in_prop x (prop.implies (S₆.to_prop & prop.post (term.subst y v f) fx)
  --                                                    S₇.to_prop),
  --             or.elim (free_in_prop.implies.inv this) (
  --               assume : free_in_prop x (S₆.to_prop & prop.post (term.subst y v f) fx),
  --               or.elim (free_in_prop.and.inv this) (
  --                 assume : free_in_prop x S₆.to_prop,
  --                 have free_in_prop x S₆.to_prop.not, from free_in_prop.not this,
  --                 have free_in_prop x (prop.implies S₆.to_prop (prop.pre f fx)), from free_in_prop.or₁ this,
  --                 have free_in_prop x forallp', from free_in_prop.and₁ this,
  --                 have free_in_prop x (prop.forallc fx f forallp'), from free_in_prop.forallc₂ x_neq_fx this,
  --                 have free_in_prop x (term.unop unop.isFunc f & prop.forallc fx f forallp'), from free_in_prop.and₂ this,
  --                 have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
  --                 show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
  --               ) (
  --                 assume : free_in_prop x (prop.post (term.subst y v f) fx),
  --                 or.elim (free_in_prop.post.inv this) (
  --                   assume : free_in_term x (term.subst y v f),
  --                   have free_in_term x f, from (free_of_subst_term this).right,
  --                   have free_in_term x (term.unop unop.isFunc f), from free_in_term.unop this,
  --                   have free_in_prop x (term.unop unop.isFunc f), from free_in_prop.term this,
  --                   have free_in_prop x (term.unop unop.isFunc f & prop.forallc fx f forallp'), from free_in_prop.and₁ this,
  --                   have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
  --                   show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
  --                 ) (
  --                   assume : free_in_term x fx,
  --                   have x = fx, from free_in_term.var.inv this,
  --                   show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from absurd this x_neq_fx
  --                 )
  --               )
  --             ) (
  --               assume : free_in_prop x S₇.to_prop,
  --               have free_in_prop x (prop.implies (S₆.to_prop & prop.post f fx)
  --                                                  S₇.to_prop), from free_in_prop.or₂ this,
  --               have free_in_prop x forallp', from free_in_prop.and₂ this,
  --               have free_in_prop x (prop.forallc fx f forallp'), from free_in_prop.forallc₂ x_neq_fx this,
  --               have free_in_prop x (term.unop unop.isFunc f & prop.forallc fx f forallp'), from free_in_prop.and₂ this,
  --               have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
  --               show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
  --             )
  --           )
  --         )
  --       )
  --     else
  --       have h₁: spec.subst y v (spec.func f fx S₆ S₇)
  --          = spec.func (term.subst y v f) fx (spec.subst y v S₆) (spec.subst y v S₇),
  --       by { unfold spec.subst, simp * },
  --       let forallp := (prop.implies (spec.subst y v S₆).to_prop (prop.pre (term.subst y v f) fx)
  --                     & prop.implies ((spec.subst y v S₆).to_prop & prop.post (term.subst y v f) fx)
  --                                    (spec.subst y v S₇).to_prop) in
  --       have h₂: (spec.func (term.subst y v f) fx (spec.subst y v S₆) (spec.subst y v S₇)).to_prop =
  --                (term.unop unop.isFunc (term.subst y v f) & prop.forallc fx (term.subst y v f) forallp),
  --       by unfold spec.to_prop,
  --       let forallp' := (prop.implies S₆.to_prop (prop.pre f fx)
  --                       & prop.implies (S₆.to_prop & prop.post f fx) S₇.to_prop) in
  --       have h₃: (spec.func f fx S₆ S₇).to_prop = (term.unop unop.isFunc f & prop.forallc fx f forallp'),
  --       by unfold spec.to_prop,
  --       have free_in_prop x (term.unop unop.isFunc (term.subst y v f) & prop.forallc fx (term.subst y v f) forallp),
  --       from h₂ ▸ h₁ ▸ x_free_in_subst,
  --       have free_in_prop x (term.unop unop.isFunc (term.subst y v f))
  --          ∨ free_in_prop x (prop.forallc fx (term.subst y v f) forallp),
  --       from free_in_prop.and.inv this,
  --       or.elim this (
  --         assume : free_in_prop x (term.unop unop.isFunc (term.subst y v f)),
  --         have free_in_term x (term.unop unop.isFunc (term.subst y v f)), from free_in_prop.term.inv this,
  --         have free_in_term x (term.subst y v f), from free_in_term.unop.inv this,
  --         have x_neq_y: x ≠ y , from (free_of_subst_term this).left,
  --         have free_in_term x f, from (free_of_subst_term this).right,
  --         have free_in_term x (term.unop unop.isFunc f), from free_in_term.unop this,
  --         have free_in_prop x (term.unop unop.isFunc f), from free_in_prop.term this,
  --         have free_in_prop x (term.unop unop.isFunc f & prop.forallc fx f forallp'), from free_in_prop.and₁ this,
  --         have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
  --         show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
  --       ) (
  --         assume : free_in_prop x (prop.forallc fx (term.subst y v f) forallp),
  --         have x_neq_fx: x ≠ fx, from (free_in_prop.forallc.inv this).left,
  --         have free_in_term x (term.subst y v f) ∨ free_in_prop x forallp,
  --         from (free_in_prop.forallc.inv this).right,
  --         or.elim this (
  --           assume : free_in_term x (term.subst y v f),
  --           have x_neq_y: x ≠ y , from (free_of_subst_term this).left,
  --           have free_in_term x f, from (free_of_subst_term this).right,
  --           have free_in_term x (term.unop unop.isFunc f), from free_in_term.unop this,
  --           have free_in_prop x (term.unop unop.isFunc f), from free_in_prop.term this,
  --           have free_in_prop x (term.unop unop.isFunc f & prop.forallc fx f forallp'), from free_in_prop.and₁ this,
  --           have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
  --           show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
  --         ) (
  --           assume : free_in_prop x forallp,
  --           or.elim (free_in_prop.and.inv this) (
  --             assume : free_in_prop x (prop.implies (spec.subst y v S₆).to_prop (prop.pre (term.subst y v f) fx)),
  --             or.elim (free_in_prop.implies.inv this) (
  --               assume : free_in_prop x (spec.subst y v S₆).to_prop,
  --               have x_neq_y: x ≠ y, from (S₆_ih this).left,
  --               have free_in_prop x S₆.to_prop, from (S₆_ih this).right,
  --               have free_in_prop x S₆.to_prop.not, from free_in_prop.not this,
  --               have free_in_prop x (prop.implies S₆.to_prop (prop.pre f fx)), from free_in_prop.or₁ this,
  --               have free_in_prop x forallp', from free_in_prop.and₁ this,
  --               have free_in_prop x (prop.forallc fx f forallp'), from free_in_prop.forallc₂ x_neq_fx this,
  --               have free_in_prop x (term.unop unop.isFunc f & prop.forallc fx f forallp'), from free_in_prop.and₂ this,
  --               have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
  --               show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
  --             ) (
  --               assume : free_in_prop x (prop.pre (term.subst y v f) fx),
  --               or.elim (free_in_prop.pre.inv this) (
  --                 assume : free_in_term x (term.subst y v f),
  --                 have x_neq_y: x ≠ y , from (free_of_subst_term this).left,
  --                 have free_in_term x f, from (free_of_subst_term this).right,
  --                 have free_in_term x (term.unop unop.isFunc f), from free_in_term.unop this,
  --                 have free_in_prop x (term.unop unop.isFunc f), from free_in_prop.term this,
  --                 have free_in_prop x (term.unop unop.isFunc f & prop.forallc fx f forallp'), from free_in_prop.and₁ this,
  --                 have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
  --                 show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
  --               ) (
  --                 assume : free_in_term x fx,
  --                 have x = fx, from free_in_term.var.inv this,
  --                 show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from absurd this x_neq_fx
  --               )
  --             )
  --           )
  --           (
  --             assume : free_in_prop x (prop.implies ((spec.subst y v S₆).to_prop & prop.post (term.subst y v f) fx)
  --                                                    (spec.subst y v S₇).to_prop),
  --             or.elim (free_in_prop.implies.inv this) (
  --               assume : free_in_prop x ((spec.subst y v S₆).to_prop & prop.post (term.subst y v f) fx),
  --               or.elim (free_in_prop.and.inv this) (
  --                 assume : free_in_prop x (spec.subst y v S₆).to_prop,
  --                 have x_neq_y: x ≠ y, from (S₆_ih this).left,
  --                 have free_in_prop x S₆.to_prop, from (S₆_ih this).right,
  --                 have free_in_prop x S₆.to_prop.not, from free_in_prop.not this,
  --                 have free_in_prop x (prop.implies S₆.to_prop (prop.pre f fx)), from free_in_prop.or₁ this,
  --                 have free_in_prop x forallp', from free_in_prop.and₁ this,
  --                 have free_in_prop x (prop.forallc fx f forallp'), from free_in_prop.forallc₂ x_neq_fx this,
  --                 have free_in_prop x (term.unop unop.isFunc f & prop.forallc fx f forallp'), from free_in_prop.and₂ this,
  --                 have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
  --                 show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
  --               ) (
  --                 assume : free_in_prop x (prop.post (term.subst y v f) fx),
  --                 or.elim (free_in_prop.post.inv this) (
  --                   assume : free_in_term x (term.subst y v f),
  --                   have x_neq_y: x ≠ y , from (free_of_subst_term this).left,
  --                   have free_in_term x f, from (free_of_subst_term this).right,
  --                   have free_in_term x (term.unop unop.isFunc f), from free_in_term.unop this,
  --                   have free_in_prop x (term.unop unop.isFunc f), from free_in_prop.term this,
  --                   have free_in_prop x (term.unop unop.isFunc f & prop.forallc fx f forallp'), from free_in_prop.and₁ this,
  --                   have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
  --                   show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
  --                 ) (
  --                   assume : free_in_term x fx,
  --                   have x = fx, from free_in_term.var.inv this,
  --                   show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from absurd this x_neq_fx
  --                 )
  --               )
  --             ) (
  --               assume : free_in_prop x (spec.subst y v S₇).to_prop,
  --               have x_neq_y: x ≠ y, from (S₇_ih this).left,
  --               have free_in_prop x S₇.to_prop, from (S₇_ih this).right,
  --               have free_in_prop x (prop.implies (S₆.to_prop & prop.post f fx)
  --                                                  S₇.to_prop), from free_in_prop.or₂ this,
  --               have free_in_prop x forallp', from free_in_prop.and₂ this,
  --               have free_in_prop x (prop.forallc fx f forallp'), from free_in_prop.forallc₂ x_neq_fx this,
  --               have free_in_prop x (term.unop unop.isFunc f & prop.forallc fx f forallp'), from free_in_prop.and₂ this,
  --               have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
  --               show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
  --             )
  --           )
  --         )
  --       )
  --   )
  -- end

lemma free_of_subst_env_spec {R: spec} {σ: env} {x y: var} {v: value}:
        free_in_prop x (spec.subst_env (σ[y↦v]) R).to_prop → x ≠ y ∧ free_in_prop x (spec.subst_env σ R).to_prop :=
  assume x_free: free_in_prop x (spec.subst_env (σ[y↦v]) R).to_prop,
  have spec.subst_env (σ[y↦v]) R = spec.subst y v (spec.subst_env σ R), by unfold spec.subst_env,
  have free_in_prop x (spec.subst y v (spec.subst_env σ R)).to_prop, from this ▸ x_free,
  show x ≠ y ∧ free_in_prop x (spec.subst_env σ R), from free_of_subst_spec this

lemma free_of_subst_env {R: spec} {σ: env} {x: var}:
        free_in_prop x (spec.subst_env σ R).to_prop → free_in_prop x R.to_prop :=
  assume x_free_in_subst: free_in_prop x (spec.subst_env σ R).to_prop,
  begin
    induction σ with y v σ' ih,
    show free_in_prop x R.to_prop, from (
      have spec.subst_env env.empty R = R, by unfold spec.subst_env,
      show free_in_prop x R.to_prop, from this ▸ x_free_in_subst
    ),
    show free_in_prop x R.to_prop, from (
      have free_in_prop x (spec.subst_env σ' R), from (free_of_subst_env_spec x_free_in_subst).right,
      show free_in_prop x R.to_prop, from ih this
    )
  end


lemma qfprop.subst_env.and {σ: env} {P Q: qfprop}:
      qfprop.subst_env σ (P & Q) = (qfprop.subst_env σ P & qfprop.subst_env σ Q) :=
begin
  induction σ with x v σ' ih,
  show (qfprop.subst_env env.empty (P & Q) = (qfprop.subst_env env.empty P & qfprop.subst_env env.empty Q)), by begin
    have h1: (qfprop.subst_env env.empty P = P), by unfold qfprop.subst_env,
    have h2: (qfprop.subst_env env.empty Q = Q), by unfold qfprop.subst_env,
    calc
      qfprop.subst_env env.empty (P & Q) = (P & Q) : by unfold qfprop.subst_env
                                      ... = (qfprop.subst_env env.empty P & Q) : by rw[h1]
                                      ... = (qfprop.subst_env env.empty P & qfprop.subst_env env.empty Q) : by rw[h2]
  end,
  show (qfprop.subst_env (σ'[x↦v]) (P & Q) = (qfprop.subst_env (σ'[x↦v]) P & qfprop.subst_env (σ'[x↦v]) Q)), by begin
    have h1: (qfprop.subst x v (qfprop.subst_env σ' P) = qfprop.subst_env (σ'[x↦v]) P), by unfold qfprop.subst_env,
    calc
    qfprop.subst_env (σ'[x↦v]) (P & Q) = qfprop.subst x v (qfprop.subst_env σ' (P & Q)) : by unfold qfprop.subst_env
                                   ... = qfprop.subst x v (qfprop.subst_env σ' P & qfprop.subst_env σ' Q) : by rw[ih]
                                   ... = (qfprop.subst x v (qfprop.subst_env σ' P) &
                                          qfprop.subst x v (qfprop.subst_env σ' Q)) : by refl
                                   ... = (qfprop.subst_env (σ'[x↦v]) P &
                                          qfprop.subst x v (qfprop.subst_env σ' Q)) : by unfold qfprop.subst_env
                                   ... = (qfprop.subst_env (σ'[x↦v]) P & qfprop.subst_env (σ'[x↦v]) Q) : by unfold qfprop.subst_env
  end
end

lemma valid_env.and {σ: env} {P Q: qfprop}: σ ⊨ P → σ ⊨ Q → σ ⊨ (P & Q) :=
  assume p_valid: valid (qfprop.subst_env σ P),
  assume q_valid: valid (qfprop.subst_env σ Q),
  have qfprop.subst_env σ (P & Q) = (qfprop.subst_env σ P & qfprop.subst_env σ Q), from qfprop.subst_env.and,
  show σ ⊨ (P & Q), from this.symm ▸ valid.and p_valid q_valid
