import .syntax .etc .props

-- instantiation

constant prop.instantiated_p: prop → qfprop

constant prop.instantiated_n: prop → qfprop

def prop.erased_p: prop → qfprop := sorry

def prop.erased_n: prop → qfprop := sorry

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
    have R.size < (R & S).size, from lt_of_add.left,
    have S.size < (R & S).size, from lt_of_add.right,
    R.subst & S.subst
| (spec.or R S) :=
    have R.size < (R & S).size, from lt_of_add.left,
    have S.size < (R & S).size, from lt_of_add.right,
    spec.or R.subst S.subst
| (spec.func t y R S) :=
    have R.size < (R & S).size, from lt_of_add.left,
    have S.size < (R & S).size, from lt_of_add.right,
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
| (qfprop.and P Q)       := P.subst & Q.subst
| (qfprop.or P Q)        := qfprop.or P.subst Q.subst
| (qfprop.pre t₁ t₂)     := qfprop.pre (term.subst x v t₁) (term.subst x v t₂)
| (qfprop.pre₁ op t)     := qfprop.pre₁ op (term.subst x v t)
| (qfprop.pre₂ op t₁ t₂) := qfprop.pre₂ op (term.subst x v t₁) (term.subst x v t₂)
| (qfprop.post t₁ t₂)    := qfprop.post (term.subst x v t₁) (term.subst x v t₂)

def qfprop.subst_env: env → qfprop → qfprop
| env.empty P := P
| (σ[x↦v]) P :=
    have σ.size < (σ[x ↦ v].size), from lt_of_add_one,
    qfprop.subst x v (qfprop.subst_env σ P)

lemma not_free_of_subst_term {t: term} {x: var} {v: value}: ¬(free_in_term x (term.subst x v t)) :=
  begin
    induction t with v' y unop t₁ x_not_free_in_t₁ binop t₂ t₃ x_not_free_in_t₂ x_not_free_in_t₃
                     t₄ t₅ x_not_free_in_t₄ x_not_free_in_t₅,
    show ¬free_in_term x (term.subst x v (term.value v')), from (
      assume x_free_in_v': free_in_term x (term.subst x v (term.value v')),
      have term.subst x v (term.value v') = v', by unfold term.subst,
      have free_in_term x v', from this ▸ x_free_in_v',
      show «false», by cases this
    ),
    show ¬free_in_term x (term.subst x v (term.var y)), from (
      assume x_free_in_y: free_in_term x (term.subst x v (term.var y)),
      have hite: term.subst x v (term.var y) = (if x = y then v else y), by unfold term.subst,
      if x_is_y: x = y then
        have term.subst x v (term.var y) = v, by simp * at *,
        have free_in_term x v, from this ▸ x_free_in_y,
        show «false», by cases this
      else
        have term.subst x v (term.var y) = y, by simp * at *,
        have free_in_term x y, from this ▸ x_free_in_y,
        have x = y, from free_in_term.var.inv this,
        show «false», from x_is_y this
    ),
    show ¬free_in_term x (term.subst x v (term.unop unop t₁)), from (
      assume x_free_in_unop: free_in_term x (term.subst x v (term.unop unop t₁)),
      have term.subst x v (term.unop unop t₁) = term.unop unop (term.subst x v t₁), by unfold term.subst,
      have free_in_term x (term.unop unop (term.subst x v t₁)), from this ▸ x_free_in_unop,
      have free_in_term x (term.subst x v t₁), from free_in_term.unop.inv this,
      show «false», from x_not_free_in_t₁ this
    ),
    show ¬free_in_term x (term.subst x v (term.binop binop t₂ t₃)), from (
      assume x_free_in_binop: free_in_term x (term.subst x v (term.binop binop t₂ t₃)),
      have term.subst x v (term.binop binop t₂ t₃) = term.binop binop (term.subst x v t₂) (term.subst x v t₃),
      by unfold term.subst,
      have free_in_term x (term.binop binop (term.subst x v t₂) (term.subst x v t₃)), from this ▸ x_free_in_binop,
      have free_in_term x (term.subst x v t₂) ∨ free_in_term x (term.subst x v t₃), from free_in_term.binop.inv this,
      or.elim this (
        assume : free_in_term x (term.subst x v t₂),
        show «false», from x_not_free_in_t₂ this
      ) (
        assume : free_in_term x (term.subst x v t₃),
        show «false», from x_not_free_in_t₃ this
      )
    ),
    show ¬free_in_term x (term.subst x v (term.app t₄ t₅)), from (
      assume x_free_in_app: free_in_term x (term.subst x v (term.app t₄ t₅)),
      have term.subst x v (term.app t₄ t₅) = term.app (term.subst x v t₄) (term.subst x v t₅),
      by unfold term.subst,
      have free_in_term x (term.app (term.subst x v t₄) (term.subst x v t₅)), from this ▸ x_free_in_app,
      have free_in_term x (term.subst x v t₄) ∨ free_in_term x (term.subst x v t₅), from free_in_term.app.inv this,
      or.elim this (
        assume : free_in_term x (term.subst x v t₄),
        show «false», from x_not_free_in_t₄ this
      ) (
        assume : free_in_term x (term.subst x v t₅),
        show «false», from x_not_free_in_t₅ this
      )
    )
  end

lemma not_free_of_subst_spec {R: spec} {x: var} {v: value}: ¬ (free_in_prop x (spec.subst x v R).to_prop) :=
  begin
    induction R with t S₁ x_not_free_in_S₁ S₂ S₃ x_not_free_in_S₂ x_not_free_in_S₃
                     S₄ S₅ x_not_free_in_S₄ x_not_free_in_S₅ f fx S₆ S₇ x_not_free_in_S₆ x_not_free_in_S₇,
    show ¬free_in_prop x (spec.subst x v (spec.term t)).to_prop, from (
      assume x_free_in_term: free_in_prop x (spec.subst x v (spec.term t)).to_prop,
      have spec.subst x v (spec.term t) = spec.term (term.subst x v t), by unfold spec.subst,
      have x_free_in_term': free_in_prop x (spec.term (term.subst x v t)).to_prop, from this ▸ x_free_in_term,
      have (spec.term (term.subst x v t)).to_prop = prop.term (term.subst x v t), by unfold spec.to_prop,
      have free_in_prop x (term.subst x v t), from this ▸ x_free_in_term',
      have free_in_term x (term.subst x v t), from free_in_prop.term.inv this,
      show «false», from not_free_of_subst_term this
    ),
    show ¬free_in_prop x (spec.subst x v S₁.not).to_prop, from (
      assume x_free_in_not: free_in_prop x (spec.subst x v S₁.not).to_prop,
      have (spec.subst x v S₁.not = (spec.subst x v S₁).not), by unfold spec.subst,
      have x_free_in_not': free_in_prop x (spec.subst x v S₁).not.to_prop, from this ▸ x_free_in_not,
      have (spec.subst x v S₁).not.to_prop = (spec.subst x v S₁).to_prop.not, by unfold spec.to_prop,
      have free_in_prop x (spec.subst x v S₁).to_prop.not, from this ▸ x_free_in_not',
      have free_in_prop x (spec.subst x v S₁).to_prop, from free_in_prop.not.inv this,
      show «false», from x_not_free_in_S₁ this
    ),
    show ¬free_in_prop x (spec.subst x v (S₂ & S₃)).to_prop, from (
      assume x_free_in_and: free_in_prop x (spec.subst x v (S₂ & S₃)).to_prop,
      have spec.subst x v (spec.and S₂ S₃) = (spec.subst x v S₂ & spec.subst x v S₃), by unfold spec.subst,
      have x_free_in_and': free_in_prop x (spec.subst x v S₂ & spec.subst x v S₃).to_prop, from this ▸ x_free_in_and,
      have (spec.and (spec.subst x v S₂) (spec.subst x v S₃)).to_prop
         = ((spec.subst x v S₂).to_prop & (spec.subst x v S₃).to_prop),
      by unfold spec.to_prop,
      have free_in_prop x ((spec.subst x v S₂).to_prop & (spec.subst x v S₃).to_prop), from this ▸ x_free_in_and',
      have free_in_prop x (spec.subst x v S₂).to_prop ∨ free_in_prop x (spec.subst x v S₃).to_prop,
      from free_in_prop.and.inv this,
      or.elim this (
        assume : free_in_prop x (spec.subst x v S₂).to_prop,
        show «false», from x_not_free_in_S₂ this
      ) (
        assume : free_in_prop x (spec.subst x v S₃).to_prop,
        show «false», from x_not_free_in_S₃ this
      )
    ),
    show ¬free_in_prop x (spec.subst x v (spec.or S₄ S₅)).to_prop, from (
      assume x_free_in_or: free_in_prop x (spec.subst x v (spec.or S₄ S₅)).to_prop,
      have spec.subst x v (spec.or S₄ S₅) = spec.or (spec.subst x v S₄) (spec.subst x v S₅), by unfold spec.subst,
      have x_free_in_or': free_in_prop x (spec.or (spec.subst x v S₄) (spec.subst x v S₅)).to_prop,
      from this ▸ x_free_in_or,
      have (spec.or (spec.subst x v S₄) (spec.subst x v S₅)).to_prop
         = (prop.or (spec.subst x v S₄).to_prop (spec.subst x v S₅).to_prop),
      by unfold spec.to_prop,
      have free_in_prop x (prop.or (spec.subst x v S₄).to_prop (spec.subst x v S₅).to_prop),
      from this ▸ x_free_in_or',
      have free_in_prop x (spec.subst x v S₄).to_prop ∨ free_in_prop x (spec.subst x v S₅).to_prop,
      from free_in_prop.or.inv this,
      or.elim this (
        assume : free_in_prop x (spec.subst x v S₄).to_prop,
        show «false», from x_not_free_in_S₄ this
      ) (
        assume : free_in_prop x (spec.subst x v S₅).to_prop,
        show «false», from x_not_free_in_S₅ this
      )
    ),
    show ¬free_in_prop x (spec.subst x v (spec.func f fx S₆ S₇)).to_prop, from (
      assume x_free_in_func: free_in_prop x (spec.subst x v (spec.func f fx S₆ S₇)).to_prop,
      if x_is_fx: x = fx then
        have h₁: spec.subst x v (spec.func f fx S₆ S₇) = spec.func (term.subst x v f) fx S₆ S₇,
        by { unfold spec.subst, simp * },
        let forallp := (prop.implies S₆.to_prop (prop.pre (term.subst x v f) fx)
                      & prop.implies (S₆.to_prop & prop.post (term.subst x v f) fx) S₇.to_prop) in
        have h₂: (spec.func (term.subst x v f) fx S₆ S₇).to_prop =
                 (term.unop unop.isFunc (term.subst x v f) & prop.forallc fx (term.subst x v f) forallp),
        by unfold spec.to_prop,
        have free_in_prop x (term.unop unop.isFunc (term.subst x v f) & prop.forallc fx (term.subst x v f) forallp),
        from h₂ ▸ h₁ ▸ x_free_in_func,
        have free_in_prop x (term.unop unop.isFunc (term.subst x v f))
           ∨ free_in_prop x (prop.forallc fx (term.subst x v f) forallp),
        from free_in_prop.and.inv this,
        or.elim this (
          assume : free_in_prop x (term.unop unop.isFunc (term.subst x v f)),
          have free_in_term x (term.unop unop.isFunc (term.subst x v f)), from free_in_prop.term.inv this,
          have free_in_term x (term.subst x v f), from free_in_term.unop.inv this,
          show «false», from not_free_of_subst_term this
        ) (
          assume : free_in_prop x (prop.forallc fx (term.subst x v f) forallp),
          have (x ≠ fx) ∧ (free_in_term x (term.subst x v f) ∨ free_in_prop x forallp),
          from free_in_prop.forallc.inv this,
          have ¬ (x = fx), from this.left,
          show «false», from this x_is_fx
        )
      else
        have h₁: spec.subst x v (spec.func f fx S₆ S₇)
           = spec.func (term.subst x v f) fx (spec.subst x v S₆) (spec.subst x v S₇),
        by { unfold spec.subst, simp * },
        let forallp := (prop.implies (spec.subst x v S₆).to_prop (prop.pre (term.subst x v f) fx)
                      & prop.implies ((spec.subst x v S₆).to_prop & prop.post (term.subst x v f) fx)
                                     (spec.subst x v S₇).to_prop) in
        have h₂: (spec.func (term.subst x v f) fx (spec.subst x v S₆) (spec.subst x v S₇)).to_prop =
                 (term.unop unop.isFunc (term.subst x v f) & prop.forallc fx (term.subst x v f) forallp),
        by unfold spec.to_prop,
        have free_in_prop x (term.unop unop.isFunc (term.subst x v f) & prop.forallc fx (term.subst x v f) forallp),
        from h₂ ▸ h₁ ▸ x_free_in_func,
        have free_in_prop x (term.unop unop.isFunc (term.subst x v f))
           ∨ free_in_prop x (prop.forallc fx (term.subst x v f) forallp),
        from free_in_prop.and.inv this,
        or.elim this (
          assume : free_in_prop x (term.unop unop.isFunc (term.subst x v f)),
          have free_in_term x (term.unop unop.isFunc (term.subst x v f)), from free_in_prop.term.inv this,
          have free_in_term x (term.subst x v f), from free_in_term.unop.inv this,
          show «false», from not_free_of_subst_term this
        ) (
          assume : free_in_prop x (prop.forallc fx (term.subst x v f) forallp),
          have free_in_term x (term.subst x v f) ∨ free_in_prop x forallp,
          from (free_in_prop.forallc.inv this).right,
          or.elim this (
            assume : free_in_term x (term.subst x v f),
            show «false», from not_free_of_subst_term this
          ) (
            assume : free_in_prop x forallp,
            or.elim (free_in_prop.and.inv this) (
              assume : free_in_prop x (prop.implies (spec.subst x v S₆).to_prop (prop.pre (term.subst x v f) fx)),
              or.elim (free_in_prop.implies.inv this) (
                assume : free_in_prop x (spec.subst x v S₆).to_prop,
                show «false», from x_not_free_in_S₆ this
              ) (
                assume : free_in_prop x (prop.pre (term.subst x v f) fx),
                or.elim (free_in_prop.pre.inv this) (
                  assume : free_in_term x (term.subst x v f),
                  show «false», from not_free_of_subst_term this
                ) (
                  assume : free_in_term x fx,
                  have x = fx, from free_in_term.var.inv this,
                  show «false», from x_is_fx this
                )
              )
            )
            (
              assume : free_in_prop x (prop.implies ((spec.subst x v S₆).to_prop & prop.post (term.subst x v f) fx)
                                                     (spec.subst x v S₇).to_prop),
              or.elim (free_in_prop.implies.inv this) (
                assume : free_in_prop x ((spec.subst x v S₆).to_prop & prop.post (term.subst x v f) fx),
                or.elim (free_in_prop.and.inv this) (
                  assume : free_in_prop x (spec.subst x v S₆).to_prop,
                  show «false», from x_not_free_in_S₆ this
                ) (
                  assume : free_in_prop x (prop.post (term.subst x v f) fx),
                  or.elim (free_in_prop.post.inv this) (
                    assume : free_in_term x (term.subst x v f),
                    show «false», from not_free_of_subst_term this
                  ) (
                    assume : free_in_term x fx,
                    have x = fx, from free_in_term.var.inv this,
                    show «false», from x_is_fx this
                  )
                )
              ) (
                assume : free_in_prop x (spec.subst x v S₇).to_prop,
                show «false», from x_not_free_in_S₇ this
              )
            )
          )
        )
    )
  end

-- validity

inductive valid : qfprop → Prop
notation `⊨` p: 100 := valid p

| tru: ⊨ value.true

| eq {t: term}: ⊨ term.binop binop.eq t t

| and {q p: qfprop}: ⊨ p → ⊨ q → ⊨ (p & q)

| orl {q p: qfprop}: ⊨ p → ⊨ (qfprop.or p q)

| orr {q p: qfprop}: ⊨ q → ⊨ (qfprop.or p q)

| mp {q p: qfprop}: ⊨ qfprop.implies p q → ⊨ p → ⊨ q

notation `⊨` p: 100 := valid p
notation σ `⊨` p: 100 := valid (qfprop.subst_env σ p)

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

-- axioms about instantiation

axiom instantiated_p_of_erased_p {σ: env} {P: prop} : σ ⊨ P.erased_p → σ ⊨ P.instantiated_p
axiom instantiated_n_of_instantiated_p {σ: env} {P: prop} : σ ⊨ P.instantiated_p → σ ⊨ P.instantiated_n
axiom erased_n_of_instantiated_n {σ: env} {P: prop} : σ ⊨ P.instantiated_n → σ ⊨ P.erased_n

-- notation ⟪ P ⟫

@[reducible]
def VC(P: prop) := ∀ (σ: env), σ ⊨ P.instantiated_p

notation `⟪` P `⟫`: 100 := VC P