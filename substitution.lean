import .syntax .notations .freevars

-- substitution

def term.subst (x: var) (v: value): term → term
| (term.value v')       := v'
| (term.var y)          := if x = y then v else y
| (term.unop op t)      := term.unop op t.subst
| (term.binop op t₁ t₂) := term.binop op t₁.subst t₂.subst
| (term.app t₁ t₂)      := term.app t₁.subst t₂.subst

def term.subst_env: env → term → term
| env.empty t := t
| (σ[x↦v]) t :=
    have σ.size < (σ[x ↦ v].size), from lt_of_add_one,
    term.subst x v (term.subst_env σ t)

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

def vc.subst (x: var) (v: value): vc → vc
| (vc.term t)        := term.subst x v t
| (vc.not P)         := vc.not P.subst
| (vc.and P Q)       := P.subst && Q.subst
| (vc.or P Q)        := P.subst || Q.subst
| (vc.pre t₁ t₂)     := vc.pre (term.subst x v t₁) (term.subst x v t₂)
| (vc.pre₁ op t)     := vc.pre₁ op (term.subst x v t)
| (vc.pre₂ op t₁ t₂) := vc.pre₂ op (term.subst x v t₁) (term.subst x v t₂)
| (vc.post t₁ t₂)    := vc.post (term.subst x v t₁) (term.subst x v t₂)
| (vc.univ y P)      := vc.univ y (if x = y then P else P.subst)

def vc.subst_env: env → vc → vc
| env.empty P := P
| (σ[x↦v]) P :=
    have σ.size < (σ[x ↦ v].size), from lt_of_add_one,
    vc.subst x v (vc.subst_env σ P)

-- lemmas

lemma unchanged_of_subst_nonfree_term {t: term} {x: var} {v: value}:
    x ∉ FV t → (term.subst x v t = t) :=
  assume x_not_free: ¬ free_in_term x t,
  begin
    induction t with v' y unop t₁ t₁_ih binop t₂ t₃ t₂_ih t₃_ih t₄ t₅ t₄_ih t₅_ih,
    show (term.subst x v (term.value v') = ↑v'), by unfold term.subst,
    show (term.subst x v (term.var y) = (term.var y)), from (
      have h: term.subst x v (term.var y) = (if x = y then v else y), by unfold term.subst,
      if x_is_y: x = y then (
        have free_in_term y (term.var y), from free_in_term.var y,
        have free_in_term x (term.var y), from x_is_y.symm ▸ this,
        show term.subst x v (term.var y) = y, from absurd this x_not_free
      ) else (
        show term.subst x v (term.var y) = y, by { simp[x_is_y] at h, assumption }
      )
    ),
    show (term.subst x v (term.unop unop t₁) = term.unop unop t₁), from (
      have h: term.subst x v (term.unop unop t₁) = term.unop unop (term.subst x v t₁), by unfold term.subst,
      have ¬ free_in_term x t₁, from (
        assume : free_in_term x t₁,
        have free_in_term x (term.unop unop t₁), from free_in_term.unop this,
        show «false», from x_not_free this
      ),
      have term.subst x v t₁ = t₁, from t₁_ih this,
      show term.subst x v (term.unop unop t₁) = term.unop unop t₁,
      from @eq.subst term (λa, term.subst x v (term.unop unop t₁) = term.unop unop a) (term.subst x v t₁) t₁ this h
    ),
    show (term.subst x v (term.binop binop t₂ t₃) = term.binop binop t₂ t₃), from (
      have h: term.subst x v (term.binop binop t₂ t₃)
            = term.binop binop (term.subst x v t₂) (term.subst x v t₃), by unfold term.subst,
      have ¬ free_in_term x t₂, from (
        assume : free_in_term x t₂,
        have free_in_term x (term.binop binop t₂ t₃), from free_in_term.binop₁ this,
        show «false», from x_not_free this
      ),
      have t2_subst: term.subst x v t₂ = t₂, from t₂_ih this,
      have ¬ free_in_term x t₃, from (
        assume : free_in_term x t₃,
        have free_in_term x (term.binop binop t₂ t₃), from free_in_term.binop₂ this,
        show «false», from x_not_free this
      ),
      have t3_subst: term.subst x v t₃ = t₃, from t₃_ih this,
      have term.subst x v (term.binop binop t₂ t₃) = term.binop binop t₂ (term.subst x v t₃),
      from @eq.subst term (λa, term.subst x v (term.binop binop t₂ t₃) = term.binop binop a (term.subst x v t₃))
      (term.subst x v t₂) t₂ t2_subst h,
      show term.subst x v (term.binop binop t₂ t₃) = term.binop binop t₂ t₃,
      from @eq.subst term (λa, term.subst x v (term.binop binop t₂ t₃) = term.binop binop t₂ a)
      (term.subst x v t₃) t₃ t3_subst this
    ),
    show (term.subst x v (term.app t₄ t₅) = term.app t₄ t₅), from (
      have h: term.subst x v (term.app t₄ t₅)
            = term.app (term.subst x v t₄) (term.subst x v t₅), by unfold term.subst,
      have ¬ free_in_term x t₄, from (
        assume : free_in_term x t₄,
        have free_in_term x (term.app t₄ t₅), from free_in_term.app₁ this,
        show «false», from x_not_free this
      ),
      have t4_subst: term.subst x v t₄ = t₄, from t₄_ih this,
      have ¬ free_in_term x t₅, from (
        assume : free_in_term x t₅,
        have free_in_term x (term.app t₄ t₅), from free_in_term.app₂ this,
        show «false», from x_not_free this
      ),
      have t5_subst: term.subst x v t₅ = t₅, from t₅_ih this,
      have term.subst x v (term.app t₄ t₅) = term.app t₄ (term.subst x v t₅),
      from @eq.subst term (λa, term.subst x v (term.app t₄ t₅) = term.app a (term.subst x v t₅))
      (term.subst x v t₄) t₄ t4_subst h,
      show term.subst x v (term.app t₄ t₅) = term.app t₄ t₅,
      from @eq.subst term (λa, term.subst x v (term.app t₄ t₅) = term.app t₄ a)
      (term.subst x v t₅) t₅ t5_subst this
    )
  end

-- lemma unchanged_of_subst_nonfree_prop {P: term} {x: var} {v: value}:
--     x ∉ FV P → (prop.subst x v t = t) :=
--   assume x_not_free: ¬ free_in_term x t,

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
  assume x_free_in_subst: free_in_prop x (spec.subst y v R),
  begin
    induction R with t S₁ S₁_ih S₂ S₃ S₂_ih S₃_ih
                     S₄ S₅ S₄_ih S₅_ih f fx S₆ S₇ S₆_ih S₇_ih,
    show x ≠ y ∧ free_in_prop x (spec.term t).to_prop, from (
      have spec.subst y v (spec.term t) = spec.term (term.subst y v t), by unfold spec.subst,
      have x_free_in_term': free_in_prop x (spec.term (term.subst y v t)).to_prop, from this ▸ x_free_in_subst,
      have (spec.term (term.subst y v t)).to_prop = prop.term (term.subst y v t), by unfold spec.to_prop,
      have free_in_prop x (term.subst y v t), from this ▸ x_free_in_term',
      have free_in_term x (term.subst y v t), from free_in_prop.term.inv this,
      have x ≠ y ∧ free_in_term x t, from free_of_subst_term this,
      show x ≠ y ∧ free_in_prop x (spec.term t).to_prop, from ⟨this.left, free_in_prop.term this.right⟩
    ),
    show x ≠ y ∧ free_in_prop x S₁.not.to_prop, from (
      have (spec.subst y v S₁.not = (spec.subst y v S₁).not), by unfold spec.subst,
      have x_free_in_not': free_in_prop x (spec.subst y v S₁).not.to_prop, from this ▸ x_free_in_subst,
      have (spec.subst y v S₁).not.to_prop = (spec.subst y v S₁).to_prop.not, by unfold spec.to_prop,
      have free_in_prop x (spec.subst y v S₁).to_prop.not, from this ▸ x_free_in_not',
      have free_in_prop x (spec.subst y v S₁).to_prop, from free_in_prop.not.inv this,
      have x ≠ y ∧ free_in_prop x S₁.to_prop, from S₁_ih this,
      show x ≠ y ∧ free_in_prop x S₁.not.to_prop, from ⟨this.left, free_in_prop.not this.right⟩
    ),
    show x ≠ y ∧ free_in_prop x (S₂ && S₃).to_prop, from (
      have spec.subst y v (spec.and S₂ S₃) = (spec.subst y v S₂ && spec.subst y v S₃), by unfold spec.subst,
      have x_free_in_and': free_in_prop x (spec.subst y v S₂ && spec.subst y v S₃).to_prop, from this ▸ x_free_in_subst,
      have (spec.and (spec.subst y v S₂) (spec.subst y v S₃)).to_prop
         = ((spec.subst y v S₂).to_prop && (spec.subst y v S₃).to_prop),
      by unfold spec.to_prop,
      have free_in_prop x ((spec.subst y v S₂).to_prop && (spec.subst y v S₃).to_prop), from this ▸ x_free_in_and',
      have free_in_prop x (spec.subst y v S₂).to_prop ∨ free_in_prop x (spec.subst y v S₃).to_prop,
      from free_in_prop.and.inv this,
      or.elim this (
        assume : free_in_prop x (spec.subst y v S₂).to_prop,
        have x ≠ y ∧ free_in_prop x S₂.to_prop, from S₂_ih this,
        show x ≠ y ∧ free_in_prop x (S₂ && S₃).to_prop, from ⟨this.left, free_in_prop.and₁ this.right⟩
      ) (
        assume : free_in_prop x (spec.subst y v S₃).to_prop,
        have x ≠ y ∧ free_in_prop x S₃.to_prop, from S₃_ih this,
        show x ≠ y ∧ free_in_prop x (S₂ && S₃).to_prop, from ⟨this.left, free_in_prop.and₂ this.right⟩
      )
    ),
    show x ≠ y ∧ free_in_prop x (spec.or S₄ S₅).to_prop, from (
      have spec.subst y v (spec.or S₄ S₅) = (spec.subst y v S₄) || (spec.subst y v S₅), by unfold spec.subst,
      have x_free_in_or': free_in_prop x (spec.or (spec.subst y v S₄) (spec.subst y v S₅)).to_prop,
      from this ▸ x_free_in_subst,
      have (spec.or (spec.subst y v S₄) (spec.subst y v S₅)).to_prop
         = ((spec.subst y v S₄).to_prop || (spec.subst y v S₅).to_prop),
      by unfold spec.to_prop,
      have free_in_prop x (prop.or (spec.subst y v S₄).to_prop (spec.subst y v S₅).to_prop),
      from this ▸ x_free_in_or',
      have free_in_prop x (spec.subst y v S₄).to_prop ∨ free_in_prop x (spec.subst y v S₅).to_prop,
      from free_in_prop.or.inv this,
      or.elim this (
        assume : free_in_prop x (spec.subst y v S₄).to_prop,
        have x ≠ y ∧ free_in_prop x S₄.to_prop, from S₄_ih this,
        show x ≠ y ∧ free_in_prop x (spec.or S₄ S₅).to_prop, from ⟨this.left, free_in_prop.or₁ this.right⟩
      ) (
        assume : free_in_prop x (spec.subst y v S₅).to_prop,
        have x ≠ y ∧ free_in_prop x S₅.to_prop, from S₅_ih this,
        show x ≠ y ∧ free_in_prop x (spec.or S₄ S₅).to_prop, from ⟨this.left, free_in_prop.or₂ this.right⟩
      )
    ),
    show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from (
      if y_is_fx: y = fx then
        have h₁: spec.subst y v (spec.func f fx S₆ S₇) = spec.func (term.subst y v f) fx S₆ S₇,
        by { unfold spec.subst, simp * },
        let forallp := (prop.implies S₆.to_prop (prop.pre (term.subst y v f) fx)
                      && prop.implies (S₆.to_prop && prop.post (term.subst y v f) fx) S₇.to_prop) in
        have h₂: (spec.func (term.subst y v f) fx S₆ S₇).to_prop =
                 (term.unop unop.isFunc (term.subst y v f) && prop.forallc fx (term.subst y v f) forallp),
        by unfold spec.to_prop,
        let forallp' := (prop.implies S₆.to_prop (prop.pre f fx)
                        && prop.implies (S₆.to_prop && prop.post f fx) S₇.to_prop) in
        have h₃: (spec.func f fx S₆ S₇).to_prop = (term.unop unop.isFunc f && prop.forallc fx f forallp'),
        by unfold spec.to_prop,
        have free_in_prop x (term.unop unop.isFunc (term.subst y v f) && prop.forallc fx (term.subst y v f) forallp),
        from h₂ ▸ h₁ ▸ x_free_in_subst,
        have free_in_prop x (term.unop unop.isFunc (term.subst y v f))
           ∨ free_in_prop x (prop.forallc fx (term.subst y v f) forallp),
        from free_in_prop.and.inv this,
        or.elim this (
          assume : free_in_prop x (term.unop unop.isFunc (term.subst y v f)),
          have free_in_term x (term.unop unop.isFunc (term.subst y v f)), from free_in_prop.term.inv this,
          have free_in_term x (term.subst y v f), from free_in_term.unop.inv this,
          have x_neq_y: x ≠ y, from (free_of_subst_term this).left,
          have free_in_term x f, from (free_of_subst_term this).right,
          have free_in_term x (term.unop unop.isFunc f), from free_in_term.unop this,
          have free_in_prop x (term.unop unop.isFunc f), from free_in_prop.term this,
          have free_in_prop x (term.unop unop.isFunc f && prop.forallc fx f forallp'), from free_in_prop.and₁ this,
          -- have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
          show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
        ) (
          assume : free_in_prop x (prop.forallc fx (term.subst y v f) forallp),
          have x_neq_fx: x ≠ fx, from (free_in_prop.forallc.inv this).left,
          have x_neq_y: x ≠ y, from y_is_fx.symm ▸ x_neq_fx,
          have free_in_term x (term.subst y v f) ∨ free_in_prop x forallp, from (free_in_prop.forallc.inv this).right,
          or.elim this (
            assume : free_in_term x (term.subst y v f),
            have free_in_term x f, from (free_of_subst_term this).right,
            have free_in_term x (term.unop unop.isFunc f), from free_in_term.unop this,
            have free_in_prop x (term.unop unop.isFunc f), from free_in_prop.term this,
            have free_in_prop x (term.unop unop.isFunc f && prop.forallc fx f forallp'), from free_in_prop.and₁ this,
            have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
            show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
          ) (
            assume : free_in_prop x forallp,
            or.elim (free_in_prop.and.inv this) (
              assume : free_in_prop x (prop.implies S₆.to_prop (prop.pre (term.subst y v f) fx)),
              or.elim (free_in_prop.implies.inv this) (
                assume : free_in_prop x S₆.to_prop,
                have free_in_prop x S₆.to_prop.not, from free_in_prop.not this,
                have free_in_prop x (prop.implies S₆.to_prop (prop.pre f fx)), from free_in_prop.or₁ this,
                have free_in_prop x forallp', from free_in_prop.and₁ this,
                have free_in_prop x (prop.forallc fx f forallp'), from free_in_prop.forallc₂ x_neq_fx this,
                have free_in_prop x (term.unop unop.isFunc f && prop.forallc fx f forallp'), from free_in_prop.and₂ this,
                have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
                show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
              ) (
                assume : free_in_prop x (prop.pre (term.subst y v f) fx),
                or.elim (free_in_prop.pre.inv this) (
                  assume : free_in_term x (term.subst y v f),
                  have free_in_term x f, from (free_of_subst_term this).right,
                  have free_in_term x (term.unop unop.isFunc f), from free_in_term.unop this,
                  have free_in_prop x (term.unop unop.isFunc f), from free_in_prop.term this,
                  have free_in_prop x (term.unop unop.isFunc f && prop.forallc fx f forallp'), from free_in_prop.and₁ this,
                  have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
                  show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
                ) (
                  assume : free_in_term x fx,
                  have x = fx, from free_in_term.var.inv this,
                  show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from absurd this x_neq_fx
                )
              )
            )
            (
              assume : free_in_prop x (prop.implies (S₆.to_prop && prop.post (term.subst y v f) fx)
                                                     S₇.to_prop),
              or.elim (free_in_prop.implies.inv this) (
                assume : free_in_prop x (S₆.to_prop && prop.post (term.subst y v f) fx),
                or.elim (free_in_prop.and.inv this) (
                  assume : free_in_prop x S₆.to_prop,
                  have free_in_prop x S₆.to_prop.not, from free_in_prop.not this,
                  have free_in_prop x (prop.implies S₆.to_prop (prop.pre f fx)), from free_in_prop.or₁ this,
                  have free_in_prop x forallp', from free_in_prop.and₁ this,
                  have free_in_prop x (prop.forallc fx f forallp'), from free_in_prop.forallc₂ x_neq_fx this,
                  have free_in_prop x (term.unop unop.isFunc f && prop.forallc fx f forallp'), from free_in_prop.and₂ this,
                  have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
                  show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
                ) (
                  assume : free_in_prop x (prop.post (term.subst y v f) fx),
                  or.elim (free_in_prop.post.inv this) (
                    assume : free_in_term x (term.subst y v f),
                    have free_in_term x f, from (free_of_subst_term this).right,
                    have free_in_term x (term.unop unop.isFunc f), from free_in_term.unop this,
                    have free_in_prop x (term.unop unop.isFunc f), from free_in_prop.term this,
                    have free_in_prop x (term.unop unop.isFunc f && prop.forallc fx f forallp'), from free_in_prop.and₁ this,
                    have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
                    show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
                  ) (
                    assume : free_in_term x fx,
                    have x = fx, from free_in_term.var.inv this,
                    show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from absurd this x_neq_fx
                  )
                )
              ) (
                assume : free_in_prop x S₇.to_prop,
                have free_in_prop x (prop.implies (S₆.to_prop && prop.post f fx)
                                                   S₇.to_prop), from free_in_prop.or₂ this,
                have free_in_prop x forallp', from free_in_prop.and₂ this,
                have free_in_prop x (prop.forallc fx f forallp'), from free_in_prop.forallc₂ x_neq_fx this,
                have free_in_prop x (term.unop unop.isFunc f && prop.forallc fx f forallp'), from free_in_prop.and₂ this,
                have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
                show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
              )
            )
          )
        )
      else
        have h₁: spec.subst y v (spec.func f fx S₆ S₇)
           = spec.func (term.subst y v f) fx (spec.subst y v S₆) (spec.subst y v S₇),
        by { unfold spec.subst, simp * },
        let forallp := (prop.implies (spec.subst y v S₆).to_prop (prop.pre (term.subst y v f) fx)
                      && prop.implies ((spec.subst y v S₆).to_prop && prop.post (term.subst y v f) fx)
                                     (spec.subst y v S₇).to_prop) in
        have h₂: (spec.func (term.subst y v f) fx (spec.subst y v S₆) (spec.subst y v S₇)).to_prop =
                 (term.unop unop.isFunc (term.subst y v f) && prop.forallc fx (term.subst y v f) forallp),
        by unfold spec.to_prop,
        let forallp' := (prop.implies S₆.to_prop (prop.pre f fx)
                        && prop.implies (S₆.to_prop && prop.post f fx) S₇.to_prop) in
        have h₃: (spec.func f fx S₆ S₇).to_prop = (term.unop unop.isFunc f && prop.forallc fx f forallp'),
        by unfold spec.to_prop,
        have free_in_prop x (term.unop unop.isFunc (term.subst y v f) && prop.forallc fx (term.subst y v f) forallp),
        from h₂ ▸ h₁ ▸ x_free_in_subst,
        have free_in_prop x (term.unop unop.isFunc (term.subst y v f))
           ∨ free_in_prop x (prop.forallc fx (term.subst y v f) forallp),
        from free_in_prop.and.inv this,
        or.elim this (
          assume : free_in_prop x (term.unop unop.isFunc (term.subst y v f)),
          have free_in_term x (term.unop unop.isFunc (term.subst y v f)), from free_in_prop.term.inv this,
          have free_in_term x (term.subst y v f), from free_in_term.unop.inv this,
          have x_neq_y: x ≠ y , from (free_of_subst_term this).left,
          have free_in_term x f, from (free_of_subst_term this).right,
          have free_in_term x (term.unop unop.isFunc f), from free_in_term.unop this,
          have free_in_prop x (term.unop unop.isFunc f), from free_in_prop.term this,
          have free_in_prop x (term.unop unop.isFunc f && prop.forallc fx f forallp'), from free_in_prop.and₁ this,
          have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
          show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
        ) (
          assume : free_in_prop x (prop.forallc fx (term.subst y v f) forallp),
          have x_neq_fx: x ≠ fx, from (free_in_prop.forallc.inv this).left,
          have free_in_term x (term.subst y v f) ∨ free_in_prop x forallp,
          from (free_in_prop.forallc.inv this).right,
          or.elim this (
            assume : free_in_term x (term.subst y v f),
            have x_neq_y: x ≠ y , from (free_of_subst_term this).left,
            have free_in_term x f, from (free_of_subst_term this).right,
            have free_in_term x (term.unop unop.isFunc f), from free_in_term.unop this,
            have free_in_prop x (term.unop unop.isFunc f), from free_in_prop.term this,
            have free_in_prop x (term.unop unop.isFunc f && prop.forallc fx f forallp'), from free_in_prop.and₁ this,
            have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
            show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
          ) (
            assume : free_in_prop x forallp,
            or.elim (free_in_prop.and.inv this) (
              assume : free_in_prop x (prop.implies (spec.subst y v S₆).to_prop (prop.pre (term.subst y v f) fx)),
              or.elim (free_in_prop.implies.inv this) (
                assume : free_in_prop x (spec.subst y v S₆).to_prop,
                have x_neq_y: x ≠ y, from (S₆_ih this).left,
                have free_in_prop x S₆.to_prop, from (S₆_ih this).right,
                have free_in_prop x S₆.to_prop.not, from free_in_prop.not this,
                have free_in_prop x (prop.implies S₆.to_prop (prop.pre f fx)), from free_in_prop.or₁ this,
                have free_in_prop x forallp', from free_in_prop.and₁ this,
                have free_in_prop x (prop.forallc fx f forallp'), from free_in_prop.forallc₂ x_neq_fx this,
                have free_in_prop x (term.unop unop.isFunc f && prop.forallc fx f forallp'), from free_in_prop.and₂ this,
                have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
                show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
              ) (
                assume : free_in_prop x (prop.pre (term.subst y v f) fx),
                or.elim (free_in_prop.pre.inv this) (
                  assume : free_in_term x (term.subst y v f),
                  have x_neq_y: x ≠ y , from (free_of_subst_term this).left,
                  have free_in_term x f, from (free_of_subst_term this).right,
                  have free_in_term x (term.unop unop.isFunc f), from free_in_term.unop this,
                  have free_in_prop x (term.unop unop.isFunc f), from free_in_prop.term this,
                  have free_in_prop x (term.unop unop.isFunc f && prop.forallc fx f forallp'), from free_in_prop.and₁ this,
                  have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
                  show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
                ) (
                  assume : free_in_term x fx,
                  have x = fx, from free_in_term.var.inv this,
                  show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from absurd this x_neq_fx
                )
              )
            )
            (
              assume : free_in_prop x (prop.implies ((spec.subst y v S₆).to_prop && prop.post (term.subst y v f) fx)
                                                     (spec.subst y v S₇).to_prop),
              or.elim (free_in_prop.implies.inv this) (
                assume : free_in_prop x ((spec.subst y v S₆).to_prop && prop.post (term.subst y v f) fx),
                or.elim (free_in_prop.and.inv this) (
                  assume : free_in_prop x (spec.subst y v S₆).to_prop,
                  have x_neq_y: x ≠ y, from (S₆_ih this).left,
                  have free_in_prop x S₆.to_prop, from (S₆_ih this).right,
                  have free_in_prop x S₆.to_prop.not, from free_in_prop.not this,
                  have free_in_prop x (prop.implies S₆.to_prop (prop.pre f fx)), from free_in_prop.or₁ this,
                  have free_in_prop x forallp', from free_in_prop.and₁ this,
                  have free_in_prop x (prop.forallc fx f forallp'), from free_in_prop.forallc₂ x_neq_fx this,
                  have free_in_prop x (term.unop unop.isFunc f && prop.forallc fx f forallp'), from free_in_prop.and₂ this,
                  have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
                  show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
                ) (
                  assume : free_in_prop x (prop.post (term.subst y v f) fx),
                  or.elim (free_in_prop.post.inv this) (
                    assume : free_in_term x (term.subst y v f),
                    have x_neq_y: x ≠ y , from (free_of_subst_term this).left,
                    have free_in_term x f, from (free_of_subst_term this).right,
                    have free_in_term x (term.unop unop.isFunc f), from free_in_term.unop this,
                    have free_in_prop x (term.unop unop.isFunc f), from free_in_prop.term this,
                    have free_in_prop x (term.unop unop.isFunc f && prop.forallc fx f forallp'), from free_in_prop.and₁ this,
                    have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
                    show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
                  ) (
                    assume : free_in_term x fx,
                    have x = fx, from free_in_term.var.inv this,
                    show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from absurd this x_neq_fx
                  )
                )
              ) (
                assume : free_in_prop x (spec.subst y v S₇).to_prop,
                have x_neq_y: x ≠ y, from (S₇_ih this).left,
                have free_in_prop x S₇.to_prop, from (S₇_ih this).right,
                have free_in_prop x (prop.implies (S₆.to_prop && prop.post f fx)
                                                   S₇.to_prop), from free_in_prop.or₂ this,
                have free_in_prop x forallp', from free_in_prop.and₂ this,
                have free_in_prop x (prop.forallc fx f forallp'), from free_in_prop.forallc₂ x_neq_fx this,
                have free_in_prop x (term.unop unop.isFunc f && prop.forallc fx f forallp'), from free_in_prop.and₂ this,
                have free_in_prop x (spec.func f fx S₆ S₇).to_prop, from h₃ ▸ this,
                show x ≠ y ∧ free_in_prop x (spec.func f fx S₆ S₇).to_prop, from ⟨x_neq_y, this⟩
              )
            )
          )
        )
    )
  end

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

lemma term.subst_env.var.inv {x: var} {σ: env}:
  (term.subst_env σ x = x) ∨ (∃v:value, term.subst_env σ x = v) :=
  begin
    induction σ with y v' σ' ih,
    show (term.subst_env env.empty x = x) ∨ (∃v:value, term.subst_env env.empty x = v), from (
      have (term.subst_env env.empty x = x), by unfold term.subst_env,
      show (term.subst_env env.empty x = x) ∨ (∃v:value, term.subst_env env.empty x = v), from or.inl this
    ),
    show (term.subst_env (σ'[y↦v']) x = x) ∨ (∃v:value, term.subst_env (σ'[y↦v']) x = v), from (
      have tsubst: (term.subst_env (σ'[y↦v']) x = term.subst y v' (term.subst_env σ' x)),
      by unfold term.subst_env,
      have (term.subst_env σ' ↑x = ↑x ∨ ∃ (v : value), term.subst_env σ' ↑x = ↑v), from ih,
      or.elim this (
        assume σ'_x_is_x: term.subst_env σ' ↑x = ↑x,
        have h: (term.subst_env (σ'[y↦v']) x = term.subst y v' ↑x),
        from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) x σ'_x_is_x tsubst,
        have term.subst y v' (term.var x) = (if y = x then v' else x), by unfold term.subst,
        decidable.by_cases (
          assume : x = y,
          have term.subst y v' (term.var x) = v', by simp * at *,
          have term.subst_env (σ'[y↦v']) x = v', from eq.trans h this,
          have (∃v:value, term.subst_env (σ'[y↦v']) x = v), from exists.intro v' this,
          show (term.subst_env (σ'[y↦v']) x = x) ∨ (∃v:value, term.subst_env (σ'[y↦v']) x = v), from or.inr this
        ) (
          assume : ¬(x = y),
          have ¬(y = x), from neq_symm this,
          have term.subst y v' (term.var x) = x, by simp * at *,
          have term.subst_env (σ'[y↦v']) x = x, from eq.trans h this,
          show (term.subst_env (σ'[y↦v']) x = x) ∨ (∃v:value, term.subst_env (σ'[y↦v']) x = v), from or.inl this
        )
      ) (
        assume : ∃ (v : value), term.subst_env σ' ↑x = ↑v,
        let ⟨v, σ'_x_is_v⟩ := this in
        have h: (term.subst_env (σ'[y↦v']) x = term.subst y v' ↑v),
        from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) v σ'_x_is_v tsubst,
        have term.subst y v' (term.value v) = ↑v, by unfold term.subst,
        have term.subst_env (σ'[y↦v']) x = v, from eq.trans h this,
        have (∃v:value, term.subst_env (σ'[y↦v']) x = v), from exists.intro v this,
        show (term.subst_env (σ'[y↦v']) x = x) ∨ (∃v:value, term.subst_env (σ'[y↦v']) x = v), from or.inr this
      )
    )
  end

lemma term.subst_env.value {σ: env} {v: value}: term.subst_env σ v = v :=
begin
  induction σ with x v' σ' ih,
  show (term.subst_env env.empty v = v), by unfold term.subst_env,
  show (term.subst_env (σ'[x↦v']) v = v), from (
    have h: term.subst_env σ' v = v, from ih,
    have term.subst_env (σ'[x↦v']) v = term.subst x v' (term.subst_env σ' v), by unfold term.subst_env,
    have h2: term.subst_env (σ'[x↦v']) v = term.subst x v' v,
    from @eq.subst term (λa, term.subst_env (σ'[x↦v']) v = term.subst x v' a) (term.subst_env σ' v) v h this,
    have term.subst x v' (term.value v) = ↑v, by unfold term.subst,
    show term.subst_env (σ'[x↦v']) v = v, from eq.trans h2 this
  )
end

lemma term.subst_env.var {σ: env} {x: var}:
      ((σ x = none) ↔ (term.subst_env σ x = x)) ∧ (∀v, (σ x = some v) ↔ (term.subst_env σ x = v)) :=
begin
  induction σ with y v' σ' ih,
  show (((env.empty x = none) ↔ (term.subst_env env.empty x = x))
     ∧ (∀v, (env.empty x = some v) ↔ (term.subst_env env.empty x = v))), by begin
    split,
    show ((env.empty x = none) ↔ (term.subst_env env.empty x = x)), by begin
      split,
      show ((env.empty x = none) → (term.subst_env env.empty x = x)), by begin
        assume _,
        show (term.subst_env env.empty x = x), by unfold term.subst_env
      end,
      show ((term.subst_env env.empty x = x) → (env.empty x = none)), by begin
        assume _,
        show (env.apply env.empty x = none), by unfold env.apply
      end
    end,
    show ∀v, ((env.empty x = some v) ↔ (term.subst_env env.empty x = v)), by begin
      assume v,
      split,
      show ((env.empty x = some v) → (term.subst_env env.empty x = v)), by begin
        assume env_has_some: (env.apply (env.empty) x = some v),
        have env_has_none: (env.apply env.empty x = none), by unfold env.apply,
        have : (some v = none), from env_has_some ▸ env_has_none,
        contradiction 
      end,
      show ((term.subst_env env.empty x = v) → (env.empty x = some v)), by begin
        assume subst_is_v: (term.subst_env env.empty x = v),
        have : (term.subst_env env.empty x = x), by unfold term.subst_env,
        have : (↑v = ↑x), from eq.trans subst_is_v.symm this,
        contradiction 
      end
    end
  end,
  show ((((σ'[y↦v']) x = none) ↔ (term.subst_env (σ'[y↦v']) x = x))
     ∧ (∀v, ((σ'[y↦v']) x = some v) ↔ (term.subst_env (σ'[y↦v']) x = v))), by begin
    have tsubst: (term.subst_env (σ'[y↦v']) x = term.subst y v' (term.subst_env σ' x)),
    by unfold term.subst_env,
    have app: ((σ'[y↦v']).apply x = (if y = x ∧ option.is_none (σ'.apply x) then v' else σ'.apply x)),
    by unfold env.apply,
    split,
    show (((σ'[y↦v']) x = none) ↔ (term.subst_env (σ'[y↦v']) x = x)), by begin
      split,
      show (((σ'[y↦v']) x = none) → (term.subst_env (σ'[y↦v']) x = x)), by begin
        assume σ'_does_not_have_x: ((σ'[y↦v']) x = none),
        by_cases (y = x ∧ option.is_none (σ'.apply x)) with h,
        show (term.subst_env (σ'[y↦v']) x = x), from
          have ((σ'[y↦v']).apply x) = v', by simp * at *,
          have some v' = none, from eq.trans this.symm σ'_does_not_have_x,
          by contradiction,
        show (term.subst_env (σ'[y↦v']) x = x), from
          have ((σ'[y↦v']).apply x) = σ'.apply x, by simp * at *,
          have σ'_x_is_none: σ'.apply x = none, from eq.trans this.symm σ'_does_not_have_x,
          have term.subst_env σ' x = x, from ih.left.mp σ'_x_is_none,
          have h2: term.subst_env (σ'[y↦v']) x = term.subst y v' x,
          from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) x this tsubst,
          have term.subst y v' (term.var x) = (if y = x then v' else x), by unfold term.subst,
          have ¬(y = x) ∨ ¬(option.is_none (env.apply σ' x)) , from not_and_distrib.mp h,
          have ¬(y = x), from this.elim id ( 
            assume : ¬(option.is_none (env.apply σ' x)),
            have (env.apply σ' x) ≠ none, from not_is_none.inv (env.apply σ' x) this,
            show ¬(y = x), from absurd σ'_x_is_none this
          ),
          have term.subst y v' (term.var x) = x, by simp * at *,
          show (term.subst_env (σ'[y↦v']) x = x), from eq.trans h2 this
      end,
      show ((term.subst_env (σ'[y↦v']) x = x) → ((σ'[y↦v']) x = none)), from (
        assume h: term.subst_env (σ'[y↦v']) x = x,
        have h2: term.subst y v' (term.subst_env σ' x) = x, from eq.trans tsubst.symm h,
        have (term.subst_env σ' x = x) ∨ (∃v:value, term.subst_env σ' x = v), from term.subst_env.var.inv,
        or.elim this (
          assume : term.subst_env σ' x = x,
          have σ'_x_is_none: σ' x = none, from ih.left.mpr this,
          have h3: term.subst_env (σ'[y↦v']) x = term.subst y v' x,
          from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) x this tsubst,
          have term.subst y v' (term.var x) = (if y = x then v' else x), by unfold term.subst,
          decidable.by_cases (
            assume : x = y,
            have term.subst y v' (term.var x) = v', by simp * at *,
            have term.subst_env (σ'[y↦v']) x = v', from eq.trans h3 this,
            have ↑x = ↑v', from eq.trans h.symm this,
            show (σ'[y↦v']) x = none, by contradiction
          ) (
            assume : ¬(x = y),
            have ¬(y = x), from neq_symm this,
            have (σ'[y↦v']).apply x = σ'.apply x, by simp * at *,
            show (σ'[y↦v']).apply x = none, from eq.trans this σ'_x_is_none
          )
        ) (
          assume : (∃v'':value, term.subst_env σ' x = v''),
          let ⟨v'', σ'_x_is_v''⟩ := this in
          have h3: (term.subst_env (σ'[y↦v']) x = term.subst y v' ↑v''),
          from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) v'' σ'_x_is_v'' tsubst,
          have term.subst y v' (term.value v'') = ↑v'', by unfold term.subst,
          have term.subst_env (σ'[y↦v']) x = ↑v'', from eq.trans h3 this,
          have ↑x = ↑v'', from eq.trans h.symm this,
          show (σ'[y↦v']) x = none, by contradiction
        )
      )
    end,
    show (∀v, ((σ'[y↦v']) x = some v) ↔ (term.subst_env (σ'[y↦v']) x = v)), by begin
      assume v,
      split,
      show (((σ'[y↦v']) x = some v) → (term.subst_env (σ'[y↦v']) x = v)), by begin
        assume env_has_x: ((σ'[y↦v']) x = some v),
        have app: ((σ'[y↦v']).apply x = (if y = x ∧ option.is_none (σ'.apply x) then v' else σ'.apply x)),
        by unfold env.apply,
        by_cases (y = x ∧ option.is_none (σ'.apply x)) with h,
        show (term.subst_env (σ'[y↦v']) ↑x = ↑v), from (
          have ((σ'[y↦v']).apply x = v'), by simp * at *,
          have some v' = some v, from eq.trans this.symm env_has_x,
          have v'_is_v: v' = v, by injection this,
          have option.is_none (σ'.apply x), from h.right,
          have σ'.apply x = none, from (is_none.inv (σ'.apply x)).mp this,
          have σ'_x_is_x: term.subst_env σ' x = x, from ih.left.mp this,
          have term.subst_env (σ'[y↦v']) x = term.subst y v' (term.subst_env σ' x),
          by unfold term.subst_env,
          have h2: term.subst_env (σ'[y↦v']) x = term.subst y v' (term.var x),
          from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) x σ'_x_is_x tsubst,
          have term.subst y v' (term.var x) = (if y = x then v' else x), by unfold term.subst,
          have term.subst y v' (term.var x) = v', by simp * at *,
          show term.subst_env (σ'[y↦v']) x = v, from v'_is_v ▸ eq.trans h2 this
        ),
        show (term.subst_env (σ'[y↦v']) ↑x = ↑v), from (
          have (σ'[y↦v']).apply x = σ'.apply x, by simp * at *,
          have σ'.apply x = v, from eq.trans this.symm env_has_x,
          have σ'_x_is_v: term.subst_env σ' ↑x = ↑v, from (ih.right v).mp this,
          have term.subst_env (σ'[y↦v']) x = term.subst y v' (term.subst_env σ' x),
          by unfold term.subst_env,
          have h2: term.subst_env (σ'[y↦v']) x = term.subst y v' v,
          from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) v σ'_x_is_v tsubst,
          have term.subst y v' (term.value v) = ↑v, by unfold term.subst,
          show term.subst_env (σ'[y↦v']) x = v, from eq.trans h2 this
        )
      end,
      show ((term.subst_env (σ'[y↦v']) x = v) → ((σ'[y↦v']) x = some v)), from (
        assume h: term.subst_env (σ'[y↦v']) x = v,
        have h2: term.subst y v' (term.subst_env σ' x) = v, from eq.trans tsubst.symm h,
        have (term.subst_env σ' x = x) ∨ (∃v:value, term.subst_env σ' x = v), from term.subst_env.var.inv,
        or.elim this (
          assume : term.subst_env σ' x = x,
          have σ'_x_is_none: σ' x = none, from ih.left.mpr this,
          have h3: term.subst_env (σ'[y↦v']) x = term.subst y v' x,
          from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) x this tsubst,
          have h4: term.subst y v' (term.var x) = (if y = x then v' else x), by unfold term.subst,
          decidable.by_cases (
            assume x_is_y: x = y,
            have term.subst y v' (term.var x) = (if x = x then v' else x),
            from @eq.subst var (λa, term.subst y v' (term.var x) = (if a = x then v' else x)) y x x_is_y.symm h4,
            have term.subst y v' (term.var x) = v', by { simp at this, assumption },
            have term.subst_env (σ'[y↦v']) x = v', from eq.trans h3 this,
            have ↑v = ↑v', from eq.trans h.symm this,
            have v_is_v': v = v', by injection this,
            have opt_is_none: option.is_none (env.apply σ' x), from (is_none.inv (σ' x)).mpr σ'_x_is_none,
            have (if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = v',
            by { simp[x_is_y.symm], simp[opt_is_none] },
            have (σ'[y↦v']).apply x = v', from eq.trans app this,
            have (σ'[y↦v']) x = some v', from this,
            show (σ'[y↦v']) x = some v, from @eq.subst value (λa, (σ'[y↦v']) x = some a) v' v v_is_v'.symm this
          ) (
            assume : ¬(x = y),
            have ¬(y = x), from neq_symm this,
            have term.subst y v' (term.var x) = x, by { simp[this] at h4, assumption },
            have ↑v = ↑x, from eq.trans (eq.trans h.symm h3) this,
            show ((σ'[y↦v']) x = some v), by contradiction
          )
        ) (
          assume : (∃v'':value, term.subst_env σ' x = v''),
          let ⟨v'', σ'_x_is_v''⟩ := this in
          have h3: (term.subst_env (σ'[y↦v']) x = term.subst y v' ↑v''),
          from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) v'' σ'_x_is_v'' tsubst,
          have term.subst y v' (term.value v'') = ↑v'', by unfold term.subst,
          have term.subst_env (σ'[y↦v']) x = ↑v'', from eq.trans h3 this,
          have v_is_v'': ↑v = ↑v'', from eq.trans h.symm this,
          have term.subst_env σ' x = v,
          from @eq.subst term (λa, term.subst_env σ' x = a) v'' v v_is_v''.symm σ'_x_is_v'',
          have σ'_x_app_is_v: env.apply σ' x = some v, from (ih.right v).mpr this,
          have opt_is_not_none: ¬ option.is_none (env.apply σ' x),
          from not_is_none.rinv.mp (exists.intro v σ'_x_app_is_v),
          have (if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = σ'.apply x,
          by { simp[opt_is_not_none] },
          have (σ'[y↦v']) x = σ'.apply x, from eq.trans app this,
          show (σ'[y↦v']) x = some v, from eq.trans this σ'_x_app_is_v
        )
      )
    end
  end
end

lemma term.subst_env.binop {σ: env} {op: binop} {t₁ t₂: term}:
      term.subst_env σ (term.binop op t₁ t₂) = term.binop op (term.subst_env σ t₁) (term.subst_env σ t₂) :=
begin
  induction σ with x v σ' ih,
  show (term.subst_env env.empty (term.binop op t₁ t₂)
      = term.binop op (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)), by begin
    have h1: (term.subst_env env.empty t₁ = t₁), by unfold term.subst_env,
    have h2: (term.subst_env env.empty t₂ = t₂), by unfold term.subst_env,
    calc
      term.subst_env env.empty (term.binop op t₁ t₂)
                       = (term.binop op t₁ t₂) : by unfold term.subst_env
                   ... = (term.binop op (term.subst_env env.empty t₁) t₂) : by rw[h1]
                   ... = (term.binop op (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)) : by rw[h2]
  end,
  show (term.subst_env (σ'[x↦v]) (term.binop op t₁ t₂)
     = (term.binop op (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂))), by begin
    have h1: (term.subst x v (term.subst_env σ' t₁) = term.subst_env (σ'[x↦v]) t₁), by unfold term.subst_env,
    calc
    term.subst_env (σ'[x↦v]) (term.binop op t₁ t₂)
             = term.subst x v (term.subst_env σ' (term.binop op t₁ t₂)) : by unfold term.subst_env
         ... = term.subst x v (term.binop op (term.subst_env σ' t₁) (term.subst_env σ' t₂)) : by rw[ih]
         ... = term.binop op (term.subst x v (term.subst_env σ' t₁))
                             (term.subst x v (term.subst_env σ' t₂)) : by unfold term.subst
         ... = term.binop op (term.subst_env (σ'[x↦v]) t₁)
                             (term.subst x v (term.subst_env σ' t₂)) : by unfold term.subst_env
         ... = term.binop op (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂) : by unfold term.subst_env
  end
end

lemma vc.subst_env.not {σ: env} {P: vc}:
      vc.subst_env σ P.not = (vc.subst_env σ P).not :=
begin
  induction σ with x v σ' ih,
  show (vc.subst_env env.empty P.not = (vc.subst_env env.empty P).not), by begin
    calc
      vc.subst_env env.empty P.not = P.not : by unfold vc.subst_env
                               ... = (vc.subst_env env.empty P).not : by unfold vc.subst_env
  end,
  show (vc.subst_env (σ'[x↦v]) P.not = (vc.subst_env (σ'[x↦v]) P).not), by begin
    calc
    vc.subst_env (σ'[x↦v]) P.not = vc.subst x v (vc.subst_env σ' P.not) : by unfold vc.subst_env
                             ... = vc.subst x v (vc.subst_env σ' P).not : by rw[ih]
                             ... = (vc.subst x v (vc.subst_env σ' P)).not : by unfold vc.subst
                             ... = (vc.subst_env (σ'[x↦v]) P).not : by unfold vc.subst_env
  end
end

lemma vc.subst_env.and {σ: env} {P Q: vc}:
      vc.subst_env σ (P && Q) = (vc.subst_env σ P && vc.subst_env σ Q) :=
begin
  induction σ with x v σ' ih,
  show (vc.subst_env env.empty (P && Q) = (vc.subst_env env.empty P && vc.subst_env env.empty Q)), by begin
    have h1: (vc.subst_env env.empty P = P), by unfold vc.subst_env,
    have h2: (vc.subst_env env.empty Q = Q), by unfold vc.subst_env,
    calc
      vc.subst_env env.empty (P && Q) = (P && Q) : by unfold vc.subst_env
                                  ... = (vc.subst_env env.empty P && Q) : by rw[h1]
                                  ... = (vc.subst_env env.empty P && vc.subst_env env.empty Q) : by rw[h2]
  end,
  show (vc.subst_env (σ'[x↦v]) (P && Q) = (vc.subst_env (σ'[x↦v]) P && vc.subst_env (σ'[x↦v]) Q)), by begin
    have h1: (vc.subst x v (vc.subst_env σ' P) = vc.subst_env (σ'[x↦v]) P), by unfold vc.subst_env,
    calc
    vc.subst_env (σ'[x↦v]) (P && Q) = vc.subst x v (vc.subst_env σ' (P && Q)) : by unfold vc.subst_env
                                ... = vc.subst x v (vc.subst_env σ' P && vc.subst_env σ' Q) : by rw[ih]
                                ... = (vc.subst x v (vc.subst_env σ' P) &&
                                       vc.subst x v (vc.subst_env σ' Q)) : by refl
                                ... = (vc.subst_env (σ'[x↦v]) P &&
                                       vc.subst x v (vc.subst_env σ' Q)) : by unfold vc.subst_env
                                ... = (vc.subst_env (σ'[x↦v]) P && vc.subst_env (σ'[x↦v]) Q) : by unfold vc.subst_env
  end
end

lemma vc.subst_env.or {σ: env} {P Q: vc}:
      vc.subst_env σ (P || Q) = (vc.subst_env σ P || vc.subst_env σ Q) :=
begin
  induction σ with x v σ' ih,
  show (vc.subst_env env.empty (P || Q) = (vc.subst_env env.empty P || vc.subst_env env.empty Q)), by begin
    have h1: (vc.subst_env env.empty P = P), by unfold vc.subst_env,
    have h2: (vc.subst_env env.empty Q = Q), by unfold vc.subst_env,
    calc
      vc.subst_env env.empty (P || Q) = (P || Q) : by unfold vc.subst_env
                                  ... = (vc.subst_env env.empty P || Q) : by rw[h1]
                                  ... = (vc.subst_env env.empty P || vc.subst_env env.empty Q) : by rw[h2]
  end,
  show (vc.subst_env (σ'[x↦v]) (P || Q) = (vc.subst_env (σ'[x↦v]) P || vc.subst_env (σ'[x↦v]) Q)), by begin
    have h1: (vc.subst x v (vc.subst_env σ' P) = vc.subst_env (σ'[x↦v]) P), by unfold vc.subst_env,
    calc
    vc.subst_env (σ'[x↦v]) (P || Q) = vc.subst x v (vc.subst_env σ' (P || Q)) : by unfold vc.subst_env
                                ... = vc.subst x v (vc.subst_env σ' P || vc.subst_env σ' Q) : by rw[ih]
                                ... = (vc.subst x v (vc.subst_env σ' P) ||
                                       vc.subst x v (vc.subst_env σ' Q)) : by refl
                                ... = (vc.subst_env (σ'[x↦v]) P ||
                                       vc.subst x v (vc.subst_env σ' Q)) : by unfold vc.subst_env
                                ... = (vc.subst_env (σ'[x↦v]) P || vc.subst_env (σ'[x↦v]) Q) : by unfold vc.subst_env
  end
end

lemma vc.subst_env.pre₁ {σ: env} {op: unop} {t: term}:
      vc.subst_env σ (vc.pre₁ op t) = vc.pre₁ op (term.subst_env σ t) :=
begin
  induction σ with x v σ' ih,
  show (vc.subst_env env.empty (vc.pre₁ op t) = vc.pre₁ op (term.subst_env env.empty t)), by begin
    have h1: (term.subst_env env.empty t = t), by unfold term.subst_env,
    calc
      vc.subst_env env.empty (vc.pre₁ op t) = (vc.pre₁ op t) : by unfold vc.subst_env
                                        ... = (vc.pre₁ op (term.subst_env env.empty t)) : by rw[h1]
  end,
  show (vc.subst_env (σ'[x↦v]) (vc.pre₁ op t) = vc.pre₁ op (term.subst_env (σ'[x↦v]) t)), by begin
    calc
    vc.subst_env (σ'[x↦v]) (vc.pre₁ op t) = vc.subst x v (vc.subst_env σ' (vc.pre₁ op t)) : by unfold vc.subst_env
                             ... = vc.subst x v (vc.pre₁ op (term.subst_env σ' t)) : by rw[ih]
                             ... = vc.pre₁ op (term.subst x v (term.subst_env σ' t)) : by unfold vc.subst
                             ... = vc.pre₁ op (term.subst_env (σ'[x↦v]) t) : by unfold term.subst_env
  end
end