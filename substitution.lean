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

def prop.subst (x: var) (v: value): prop → prop
| (prop.term t)        := term.subst x v t
| (prop.not P)         := P.subst.not
| (prop.and P Q)       := P.subst && Q.subst
| (prop.or P Q)        := P.subst || Q.subst
| (prop.pre t₁ t₂)     := prop.pre (term.subst x v t₁) (term.subst x v t₂)
| (prop.pre₁ op t)     := prop.pre₁ op (term.subst x v t)
| (prop.pre₂ op t₁ t₂) := prop.pre₂ op (term.subst x v t₁) (term.subst x v t₂)
| (prop.call t₁ t₂)    := prop.call (term.subst x v t₁) (term.subst x v t₂)
| (prop.post t₁ t₂)    := prop.post (term.subst x v t₁) (term.subst x v t₂)
| (prop.forallc y t P) := prop.forallc y (term.subst x v t) (if x = y then P else P.subst)
| (prop.exis y P)      := prop.exis y (if x = y then P else P.subst)

def prop.subst_env: env → prop → prop
| env.empty P := P
| (σ[x↦v]) P :=
    have σ.size < (σ[x ↦ v].size), from lt_of_add_one,
    prop.subst x v (prop.subst_env σ P)

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

-- notation

notation σ `⊨` p: 100 := valid (vc.subst_env σ p)

notation `⟪` P `⟫`: 100 := ∀ (σ: env), σ ⊨ (prop.instantiated P)

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

lemma term.subst.var.same {x: var} {v: value}: term.subst x v x = v :=
  have h: term.subst x v (term.var x) = (if x = x then v else x), by unfold term.subst,
  have (if x = x then (term.value v) else (term.var x)) = (term.value v), by simp,
  show term.subst x v x = v, from eq.trans h this

lemma term.subst.var.diff {x y: var} {v: value}: (x ≠ y) → (term.subst x v y = y) :=
  assume x_neq_y: x ≠ y,
  have h: term.subst x v (term.var y) = (if x = y then v else y), by unfold term.subst,
  have (if x = y then (term.value v) else (term.var y)) = (term.var y), by simp[x_neq_y],
  show term.subst x v y = y, from eq.trans h this

lemma unchanged_of_subst_nonfree_vc {P: vc} {x: var} {v: value}:
    x ∉ FV P → (vc.subst x v P = P) :=
  assume x_not_free: ¬ free_in_vc x P,
  begin
    induction P,
    case vc.term t { from (
      have h: vc.subst x v (vc.term t) = term.subst x v t, by unfold vc.subst,
      have ¬ free_in_term x t, from (
        assume : free_in_term x t,
        have free_in_vc x (vc.term t), from free_in_vc.term this,
        show «false», from x_not_free this
      ),
      have term.subst x v t = t, from unchanged_of_subst_nonfree_term this,
      show vc.subst x v t = vc.term t,
      from @eq.subst term (λa, vc.subst x v (vc.term t) = vc.term a) (term.subst x v t) t this h
    )},
    case vc.not P₁ ih { from (
      have h: vc.subst x v P₁.not = (vc.subst x v P₁).not, by unfold vc.subst,
      have ¬ free_in_vc x P₁, from (
        assume : free_in_vc x P₁,
        have free_in_vc x P₁.not, from free_in_vc.not this,
        show «false», from x_not_free this
      ),
      have vc.subst x v P₁ = P₁, from ih this,
      show vc.subst x v P₁.not = P₁.not,
      from @eq.subst vc (λa, vc.subst x v P₁.not = vc.not a) (vc.subst x v P₁) P₁ this h
    )},
    case vc.and P₁ P₂ P₁_ih P₂_ih { from (
      have h: vc.subst x v (vc.and P₁ P₂) = (vc.subst x v P₁) && (vc.subst x v P₂), by unfold vc.subst,
      have ¬ free_in_vc x P₁, from (
        assume : free_in_vc x P₁,
        have free_in_vc x (P₁ && P₂), from free_in_vc.and₁ this,
        show «false», from x_not_free this
      ),
      have h1: vc.subst x v P₁ = P₁, from P₁_ih this,
      have ¬ free_in_vc x P₂, from (
        assume : free_in_vc x P₂,
        have free_in_vc x (P₁ && P₂), from free_in_vc.and₂ this,
        show «false», from x_not_free this
      ),
      have h2: vc.subst x v P₂ = P₂, from P₂_ih this,
      have vc.subst x v (P₁ && P₂) = P₁ && (vc.subst x v P₂),
      from @eq.subst vc (λa, vc.subst x v (vc.and P₁ P₂) = a && (vc.subst x v P₂)) (vc.subst x v P₁) P₁ h1 h,
      show vc.subst x v (P₁ && P₂) = P₁ && P₂,
      from @eq.subst vc (λa, vc.subst x v (vc.and P₁ P₂) = P₁ && a) (vc.subst x v P₂) P₂ h2 this
    )},
    case vc.or P₁ P₂ P₁_ih P₂_ih { from (
      have h: vc.subst x v (vc.or P₁ P₂) = (vc.subst x v P₁) || (vc.subst x v P₂), by unfold vc.subst,
      have ¬ free_in_vc x P₁, from (
        assume : free_in_vc x P₁,
        have free_in_vc x (P₁ || P₂), from free_in_vc.or₁ this,
        show «false», from x_not_free this
      ),
      have h1: vc.subst x v P₁ = P₁, from P₁_ih this,
      have ¬ free_in_vc x P₂, from (
        assume : free_in_vc x P₂,
        have free_in_vc x (P₁ || P₂), from free_in_vc.or₂ this,
        show «false», from x_not_free this
      ),
      have h2: vc.subst x v P₂ = P₂, from P₂_ih this,
      have vc.subst x v (P₁ || P₂) = P₁ || (vc.subst x v P₂),
      from @eq.subst vc (λa, vc.subst x v (vc.or P₁ P₂) = a || (vc.subst x v P₂)) (vc.subst x v P₁) P₁ h1 h,
      show vc.subst x v (P₁ || P₂) = P₁ || P₂,
      from @eq.subst vc (λa, vc.subst x v (vc.or P₁ P₂) = P₁ || a) (vc.subst x v P₂) P₂ h2 this
    )},
    case vc.pre t₁ t₂ { from (
      have h: vc.subst x v (vc.pre t₁ t₂) = vc.pre (term.subst x v t₁) (term.subst x v t₂), by unfold vc.subst,
      have ¬ free_in_term x t₁, from (
        assume : free_in_term x t₁,
        have free_in_vc x (vc.pre t₁ t₂), from free_in_vc.pre₁ this,
        show «false», from x_not_free this
      ),
      have h1: term.subst x v t₁ = t₁, from unchanged_of_subst_nonfree_term this,
      have ¬ free_in_term x t₂, from (
        assume : free_in_term x t₂,
        have free_in_vc x (vc.pre t₁ t₂), from free_in_vc.pre₂ this,
        show «false», from x_not_free this
      ),
      have h2: term.subst x v t₂ = t₂, from unchanged_of_subst_nonfree_term this,
      have vc.subst x v (vc.pre t₁ t₂) = vc.pre t₁ (term.subst x v t₂),
      from @eq.subst term (λa, vc.subst x v (vc.pre t₁ t₂) = vc.pre a (term.subst x v t₂)) (term.subst x v t₁) t₁ h1 h,
      show vc.subst x v (vc.pre t₁ t₂) = vc.pre t₁ t₂,
      from @eq.subst term (λa, vc.subst x v (vc.pre t₁ t₂) = vc.pre t₁ a) (term.subst x v t₂) t₂ h2 this
    )},
    case vc.pre₁ op t { from (
      have h: vc.subst x v (vc.pre₁ op t) = vc.pre₁ op (term.subst x v t), by unfold vc.subst,
      have ¬ free_in_term x t, from (
        assume : free_in_term x t,
        have free_in_vc x (vc.pre₁ op t), from free_in_vc.preop this,
        show «false», from x_not_free this
      ),
      have term.subst x v t = t, from unchanged_of_subst_nonfree_term this,
      show vc.subst x v (vc.pre₁ op t) = vc.pre₁ op t,
      from @eq.subst term (λa, vc.subst x v (vc.pre₁ op t) = vc.pre₁ op a) (term.subst x v t) t this h
    )},
    case vc.pre₂ op t₁ t₂ { from (
      have h: vc.subst x v (vc.pre₂ op t₁ t₂) = vc.pre₂ op (term.subst x v t₁) (term.subst x v t₂),
      by unfold vc.subst,
      have ¬ free_in_term x t₁, from (
        assume : free_in_term x t₁,
        have free_in_vc x (vc.pre₂ op t₁ t₂), from free_in_vc.preop₁ this,
        show «false», from x_not_free this
      ),
      have h1: term.subst x v t₁ = t₁, from unchanged_of_subst_nonfree_term this,
      have ¬ free_in_term x t₂, from (
        assume : free_in_term x t₂,
        have free_in_vc x (vc.pre₂ op t₁ t₂), from free_in_vc.preop₂ this,
        show «false», from x_not_free this
      ),
      have h2: term.subst x v t₂ = t₂, from unchanged_of_subst_nonfree_term this,
      have vc.subst x v (vc.pre₂ op t₁ t₂) = vc.pre₂ op t₁ (term.subst x v t₂),
      from @eq.subst term (λa, vc.subst x v (vc.pre₂ op t₁ t₂) = vc.pre₂ op a (term.subst x v t₂)) (term.subst x v t₁) t₁ h1 h,
      show vc.subst x v (vc.pre₂ op t₁ t₂) = vc.pre₂ op t₁ t₂,
      from @eq.subst term (λa, vc.subst x v (vc.pre₂ op t₁ t₂) = vc.pre₂ op t₁ a) (term.subst x v t₂) t₂ h2 this
    )},
    case vc.post t₁ t₂ { from (
      have h: vc.subst x v (vc.post t₁ t₂) = vc.post (term.subst x v t₁) (term.subst x v t₂), by unfold vc.subst,
      have ¬ free_in_term x t₁, from (
        assume : free_in_term x t₁,
        have free_in_vc x (vc.post t₁ t₂), from free_in_vc.post₁ this,
        show «false», from x_not_free this
      ),
      have h1: term.subst x v t₁ = t₁, from unchanged_of_subst_nonfree_term this,
      have ¬ free_in_term x t₂, from (
        assume : free_in_term x t₂,
        have free_in_vc x (vc.post t₁ t₂), from free_in_vc.post₂ this,
        show «false», from x_not_free this
      ),
      have h2: term.subst x v t₂ = t₂, from unchanged_of_subst_nonfree_term this,
      have vc.subst x v (vc.post t₁ t₂) = vc.post t₁ (term.subst x v t₂),
      from @eq.subst term (λa, vc.subst x v (vc.post t₁ t₂) = vc.post a (term.subst x v t₂)) (term.subst x v t₁) t₁ h1 h,
      show vc.subst x v (vc.post t₁ t₂) = vc.post t₁ t₂,
      from @eq.subst term (λa, vc.subst x v (vc.post t₁ t₂) = vc.post t₁ a) (term.subst x v t₂) t₂ h2 this
    )},
    case vc.univ y P' P'_ih { from (
      have h: vc.subst x v (vc.univ y P') = vc.univ y (if x = y then P' else vc.subst x v P'), by unfold vc.subst,
      if x_eq_y: x = y then (
        have (if x = y then P' else vc.subst x v P') = P', by simp[x_eq_y],
        show vc.subst x v (vc.univ y P') = vc.univ y P',
        from @eq.subst vc (λa, vc.subst x v (vc.univ y P') = vc.univ y a)
                          (if x = y then P' else vc.subst x v P') P' this h
      ) else (
        have (if x = y then P' else vc.subst x v P') = vc.subst x v P', by simp[x_eq_y],
        have h2: vc.subst x v (vc.univ y P') = vc.univ y (vc.subst x v P'),
        from @eq.subst vc (λa, vc.subst x v (vc.univ y P') = vc.univ y a)
                          (if x = y then P' else vc.subst x v P') (vc.subst x v P') this h,
        have ¬ free_in_vc x P', from (
          assume : free_in_vc x P',
          have free_in_vc x (vc.univ y P'), from free_in_vc.univ x_eq_y this,
          show «false», from x_not_free this
        ),
        have vc.subst x v P' = P', from P'_ih this,
        show vc.subst x v (vc.univ y P') = vc.univ y P',
        from @eq.subst vc (λa, vc.subst x v (vc.univ y P') = vc.univ y a) (vc.subst x v P') P' this h2
      )
    )}
  end

lemma unchanged_of_subst_env_nonfree_vc {P: vc}:
    (∀x, x ∉ FV P) → (∀σ, vc.subst_env σ P = P) :=
  assume x_not_free: (∀x, x ∉ FV P),
  assume σ: env,
  begin
    induction σ with x v σ' ih,

    show (vc.subst_env env.empty P = P), by unfold vc.subst_env,

    show (vc.subst_env (σ'[x↦v]) P = P), by calc
        vc.subst_env (σ'[x↦v]) P = vc.subst x v (vc.subst_env σ' P) : by unfold vc.subst_env
                             ... = vc.subst x v P : by rw[ih]
                             ... = P : unchanged_of_subst_nonfree_vc (x_not_free x)
  end

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
        have term.subst y v (term.var z) = v, by { simp[y_is_z] at hite, rw[y_is_z], from hite },
        have free_in_term x v, from this ▸ x_free_in_subst,
        show x ≠ y ∧ free_in_term x (term.var z), from absurd this free_in_term.value.inv
      else
        have term.subst y v (term.var z) = z, by { simp[y_is_z] at hite, from hite },
        have free_in_term x z, from this ▸ x_free_in_subst,
        have x_is_z: x = z, from free_in_term.var.inv this,
        have x ≠ y, from x_is_z.symm ▸ (ne.symm y_is_z),
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

lemma free_of_subst_prop {P: prop} {x y: var} {v: value}:
          free_in_prop x (prop.subst y v P) → x ≠ y ∧ free_in_prop x P :=
  assume x_free_in_subst: free_in_prop x (prop.subst y v P),
  begin
    induction P,
    case prop.term t { from (
      have prop.subst y v (prop.term t) = (term.subst y v t), by unfold prop.subst,
      have free_in_prop x (term.subst y v t), from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t), from free_in_prop.term.inv this,
      have x ≠ y ∧ free_in_term x t, from free_of_subst_term this,
      show x ≠ y ∧ free_in_prop x (prop.term t), from ⟨this.left, free_in_prop.term this.right⟩
    )},
    case prop.not P₁ P₁_ih { from (
      have (prop.subst y v P₁.not = (prop.subst y v P₁).not), by unfold prop.subst,
      have free_in_prop x (prop.subst y v P₁).not, from this ▸ x_free_in_subst,
      have free_in_prop x (prop.subst y v P₁), from free_in_prop.not.inv this,
      have x ≠ y ∧ free_in_prop x P₁, from P₁_ih this,
      show x ≠ y ∧ free_in_prop x P₁.not, from ⟨this.left, free_in_prop.not this.right⟩
    )},
    case prop.and P₂ P₃ P₂_ih P₃_ih { from (
      have prop.subst y v (prop.and P₂ P₃) = (prop.subst y v P₂ && prop.subst y v P₃), by unfold prop.subst,
      have free_in_prop x ((prop.subst y v P₂) && (prop.subst y v P₃)), from this ▸ x_free_in_subst,
      have free_in_prop x (prop.subst y v P₂) ∨ free_in_prop x (prop.subst y v P₃),
      from free_in_prop.and.inv this,
      or.elim this (
        assume : free_in_prop x (prop.subst y v P₂),
        have x ≠ y ∧ free_in_prop x P₂, from P₂_ih this,
        show x ≠ y ∧ free_in_prop x (P₂ && P₃), from ⟨this.left, free_in_prop.and₁ this.right⟩
      ) (
        assume : free_in_prop x (prop.subst y v P₃),
        have x ≠ y ∧ free_in_prop x P₃, from P₃_ih this,
        show x ≠ y ∧ free_in_prop x (P₂ && P₃), from ⟨this.left, free_in_prop.and₂ this.right⟩
      )
    )},
    case prop.or P₄ P₅ P₄_ih P₅_ih { from (
      have prop.subst y v (prop.or P₄ P₅) = (prop.subst y v P₄) || (prop.subst y v P₅), by unfold prop.subst,
      have free_in_prop x (prop.or (prop.subst y v P₄) (prop.subst y v P₅)),
      from this ▸ x_free_in_subst,
      have free_in_prop x (prop.subst y v P₄) ∨ free_in_prop x (prop.subst y v P₅),
      from free_in_prop.or.inv this,
      or.elim this (
        assume : free_in_prop x (prop.subst y v P₄),
        have x ≠ y ∧ free_in_prop x P₄, from P₄_ih this,
        show x ≠ y ∧ free_in_prop x (prop.or P₄ P₅), from ⟨this.left, free_in_prop.or₁ this.right⟩
      ) (
        assume : free_in_prop x (prop.subst y v P₅),
        have x ≠ y ∧ free_in_prop x P₅, from P₅_ih this,
        show x ≠ y ∧ free_in_prop x (prop.or P₄ P₅), from ⟨this.left, free_in_prop.or₂ this.right⟩
      )
    )},
    case prop.pre t₁ t₂ { from (
      have prop.subst y v (prop.pre t₁ t₂) = prop.pre (term.subst y v t₁) (term.subst y v t₂), by unfold prop.subst,
      have free_in_prop x (prop.pre (term.subst y v t₁) (term.subst y v t₂)),
      from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₁) ∨ free_in_term x (term.subst y v t₂), from free_in_prop.pre.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₁),
        have x ≠ y ∧ free_in_term x t₁, from free_of_subst_term this,
        show x ≠ y ∧ free_in_prop x (prop.pre t₁ t₂), from ⟨this.left, free_in_prop.pre₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₂),
        have x ≠ y ∧ free_in_term x t₂, from free_of_subst_term this,
        show x ≠ y ∧ free_in_prop x (prop.pre t₁ t₂), from ⟨this.left, free_in_prop.pre₂ this.right⟩
      )
    )},
    case prop.pre₁ op t { from (
      have prop.subst y v (prop.pre₁ op t) = prop.pre₁ op (term.subst y v t), by unfold prop.subst,
      have free_in_prop x (prop.pre₁ op (term.subst y v t)),
      from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t), from free_in_prop.pre₁.inv this,
      have x ≠ y ∧ free_in_term x t, from free_of_subst_term this,
      show x ≠ y ∧ free_in_prop x (prop.pre₁ op t), from ⟨this.left, free_in_prop.preop this.right⟩
    )},
    case prop.pre₂ op t₁ t₂ { from (
      have prop.subst y v (prop.pre₂ op t₁ t₂) = prop.pre₂ op (term.subst y v t₁) (term.subst y v t₂),
      by unfold prop.subst,
      have free_in_prop x (prop.pre₂ op (term.subst y v t₁) (term.subst y v t₂)),
      from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₁) ∨ free_in_term x (term.subst y v t₂), from free_in_prop.pre₂.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₁),
        have x ≠ y ∧ free_in_term x t₁, from free_of_subst_term this,
        show x ≠ y ∧ free_in_prop x (prop.pre₂ op t₁ t₂), from ⟨this.left, free_in_prop.preop₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₂),
        have x ≠ y ∧ free_in_term x t₂, from free_of_subst_term this,
        show x ≠ y ∧ free_in_prop x (prop.pre₂ op t₁ t₂), from ⟨this.left, free_in_prop.preop₂ this.right⟩
      )
    )},
    case prop.post t₁ t₂ { from (
      have prop.subst y v (prop.post t₁ t₂) = prop.post (term.subst y v t₁) (term.subst y v t₂), by unfold prop.subst,
      have free_in_prop x (prop.post (term.subst y v t₁) (term.subst y v t₂)),
      from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₁) ∨ free_in_term x (term.subst y v t₂), from free_in_prop.post.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₁),
        have x ≠ y ∧ free_in_term x t₁, from free_of_subst_term this,
        show x ≠ y ∧ free_in_prop x (prop.post t₁ t₂), from ⟨this.left, free_in_prop.post₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₂),
        have x ≠ y ∧ free_in_term x t₂, from free_of_subst_term this,
        show x ≠ y ∧ free_in_prop x (prop.post t₁ t₂), from ⟨this.left, free_in_prop.post₂ this.right⟩
      )
    )},
    case prop.call t₁ t₂ { from (
      have prop.subst y v (prop.call t₁ t₂) = prop.call (term.subst y v t₁) (term.subst y v t₂), by unfold prop.subst,
      have free_in_prop x (prop.call (term.subst y v t₁) (term.subst y v t₂)),
      from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₁) ∨ free_in_term x (term.subst y v t₂), from free_in_prop.call.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₁),
        have x ≠ y ∧ free_in_term x t₁, from free_of_subst_term this,
        show x ≠ y ∧ free_in_prop x (prop.call t₁ t₂), from ⟨this.left, free_in_prop.call₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₂),
        have x ≠ y ∧ free_in_term x t₂, from free_of_subst_term this,
        show x ≠ y ∧ free_in_prop x (prop.call t₁ t₂), from ⟨this.left, free_in_prop.call₂ this.right⟩
      )
    )},
    case prop.forallc z t P ih { from (
      have prop.subst y v (prop.forallc z t P) = prop.forallc z (term.subst y v t) (if y = z then P else P.subst y v),
      by unfold prop.subst,
      have free_in_prop x (prop.forallc z (term.subst y v t) (if y = z then P else P.subst y v)),
      from this ▸ x_free_in_subst,
      have x_neq_z: x ≠ z, from (free_in_prop.forallc.inv this).left,
      or.elim (free_in_prop.forallc.inv this).right (
        assume : free_in_term x (term.subst y v t),
        have x ≠ y ∧ free_in_term x t, from free_of_subst_term this,
        show x ≠ y ∧ free_in_prop x (prop.forallc z t P), from ⟨this.left, free_in_prop.forallc₁ x_neq_z this.right⟩
      ) (
        assume fre_ite: free_in_prop x (if y = z then P else P.subst y v),
        if y_eq_z: y = z then (
          have x_neq_y: x ≠ y, from y_eq_z.symm ▸ x_neq_z,
          have free_in_prop x P, by { simp[y_eq_z] at fre_ite, from fre_ite },
          show x ≠ y ∧ free_in_prop x (prop.forallc z t P), from ⟨x_neq_y, free_in_prop.forallc₂ x_neq_z this⟩
        ) else (
          have free_in_prop x (P.subst y v), by { simp[y_eq_z] at fre_ite, from fre_ite },
          have x ≠ y ∧ free_in_prop x P, from ih this,
          show x ≠ y ∧ free_in_prop x (prop.forallc z t P), from ⟨this.left, free_in_prop.forallc₂ x_neq_z this.right⟩
        )
      )
    )},
    case prop.exis z P ih { from (
      have prop.subst y v (prop.exis z P) = prop.exis z (if y = z then P else P.subst y v),
      by unfold prop.subst,
      have free_in_prop x (prop.exis z (if y = z then P else P.subst y v)),
      from this ▸ x_free_in_subst,
      have x_neq_z: x ≠ z, from (free_in_prop.exis.inv this).left,
      have fre_ite: free_in_prop x (if y = z then P else P.subst y v), from (free_in_prop.exis.inv this).right,
      if y_eq_z: y = z then (
        have x_neq_y: x ≠ y, from y_eq_z.symm ▸ x_neq_z,
        have free_in_prop x P, by { simp[y_eq_z] at fre_ite, from fre_ite },
        show x ≠ y ∧ free_in_prop x (prop.exis z P), from ⟨x_neq_y, free_in_prop.exis x_neq_z this⟩
      ) else (
        have free_in_prop x (P.subst y v), by { simp[y_eq_z] at fre_ite, from fre_ite },
        have x ≠ y ∧ free_in_prop x P, from ih this,
        show x ≠ y ∧ free_in_prop x (prop.exis z P), from ⟨this.left, free_in_prop.exis x_neq_z this.right⟩
      )
    )}
  end

lemma free_of_subst_env_prop {P: prop} {σ: env} {x y: var} {v: value}:
        free_in_prop x (prop.subst_env (σ[y↦v]) P) → x ≠ y ∧ free_in_prop x (prop.subst_env σ P) :=
  assume x_free: free_in_prop x (prop.subst_env (σ[y↦v]) P),
  have prop.subst_env (σ[y↦v]) P = prop.subst y v (prop.subst_env σ P), by unfold prop.subst_env,
  have free_in_prop x (prop.subst y v (prop.subst_env σ P)), from this ▸ x_free,
  show x ≠ y ∧ free_in_prop x (prop.subst_env σ P), from free_of_subst_prop this

lemma free_of_subst_env {P: prop} {σ: env} {x: var}:
        free_in_prop x (prop.subst_env σ P) → free_in_prop x P :=
  assume x_free_in_subst: free_in_prop x (prop.subst_env σ P),
  begin
    induction σ with y v σ' ih,
    show free_in_prop x P, from (
      have prop.subst_env env.empty P = P, by unfold prop.subst_env,
      show free_in_prop x P, from this ▸ x_free_in_subst
    ),
    show free_in_prop x P, from (
      have free_in_prop x (prop.subst_env σ' P), from (free_of_subst_env_prop x_free_in_subst).right,
      show free_in_prop x P, from ih this
    )
  end

lemma free_in_vc.subst {P: vc} {x y: var} {v: value}:
          free_in_vc x (vc.subst y v P) → x ≠ y ∧ free_in_vc x P :=
  assume x_free_in_subst: free_in_vc x (vc.subst y v P),
  begin
    induction P,
    case vc.term t { from (
      have vc.subst y v (vc.term t) = term.subst y v t, by unfold vc.subst,
      have free_in_vc x (vc.term (term.subst y v t)), from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t), from free_in_vc.term.inv this,
      have x ≠ y ∧ free_in_term x t, from free_of_subst_term this,
      show x ≠ y ∧ free_in_vc x (vc.term t), from ⟨this.left, free_in_vc.term this.right⟩
    )},
    case vc.not P₁ ih { from (
      have (vc.subst y v P₁.not = (vc.subst y v P₁).not), by unfold vc.subst,
      have free_in_vc x (vc.subst y v P₁).not, from this ▸ x_free_in_subst,
      have free_in_vc x (vc.subst y v P₁), from free_in_vc.not.inv this,
      have x ≠ y ∧ free_in_vc x P₁, from ih this,
      show x ≠ y ∧ free_in_vc x P₁.not, from ⟨this.left, free_in_vc.not this.right⟩
    )},
    case vc.and P₁ P₂ P₁_ih P₂_ih { from (
      have vc.subst y v (vc.and P₁ P₂) = (vc.subst y v P₁ && vc.subst y v P₂), by unfold vc.subst,
      have free_in_vc x (vc.subst y v P₁ && vc.subst y v P₂), from this ▸ x_free_in_subst,
      have free_in_vc x (vc.subst y v P₁) ∨ free_in_vc x (vc.subst y v P₂),
      from free_in_vc.and.inv this,
      or.elim this (
        assume : free_in_vc x (vc.subst y v P₁),
        have x ≠ y ∧ free_in_vc x P₁, from P₁_ih this,
        show x ≠ y ∧ free_in_vc x (P₁ && P₂), from ⟨this.left, free_in_vc.and₁ this.right⟩
      ) (
        assume : free_in_vc x (vc.subst y v P₂),
        have x ≠ y ∧ free_in_vc x P₂, from P₂_ih this,
        show x ≠ y ∧ free_in_vc x (P₁ && P₂), from ⟨this.left, free_in_vc.and₂ this.right⟩
      )
    )},
    case vc.or P₁ P₂ P₁_ih P₂_ih { from (
      have vc.subst y v (vc.or P₁ P₂) = (vc.subst y v P₁) || (vc.subst y v P₂), by unfold vc.subst,
      have free_in_vc x (vc.or (vc.subst y v P₁) (vc.subst y v P₂)),
      from this ▸ x_free_in_subst,
      have free_in_vc x (vc.subst y v P₁) ∨ free_in_vc x (vc.subst y v P₂),
      from free_in_vc.or.inv this,
      or.elim this (
        assume : free_in_vc x (vc.subst y v P₁),
        have x ≠ y ∧ free_in_vc x P₁, from P₁_ih this,
        show x ≠ y ∧ free_in_vc x (vc.or P₁ P₂), from ⟨this.left, free_in_vc.or₁ this.right⟩
      ) (
        assume : free_in_vc x (vc.subst y v P₂),
        have x ≠ y ∧ free_in_vc x P₂, from P₂_ih this,
        show x ≠ y ∧ free_in_vc x (vc.or P₁ P₂), from ⟨this.left, free_in_vc.or₂ this.right⟩
      )
    )},
    case vc.pre t₁ t₂ { from (
      have vc.subst y v (vc.pre t₁ t₂) = vc.pre (term.subst y v t₁) (term.subst y v t₂), by unfold vc.subst,
      have free_in_vc x (vc.pre (term.subst y v t₁) (term.subst y v t₂)),
      from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₁) ∨ free_in_term x (term.subst y v t₂),
      from free_in_vc.pre.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₁),
        have x ≠ y ∧ free_in_term x t₁, from free_of_subst_term this,
        show x ≠ y ∧ free_in_vc x (vc.pre t₁ t₂), from ⟨this.left, free_in_vc.pre₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₂),
        have x ≠ y ∧ free_in_term x t₂, from free_of_subst_term this,
        show x ≠ y ∧ free_in_vc x (vc.pre t₁ t₂), from ⟨this.left, free_in_vc.pre₂ this.right⟩
      )
    )},
    case vc.pre₁ op t { from (
      have vc.subst y v (vc.pre₁ op t) = vc.pre₁ op (term.subst y v t), by unfold vc.subst,
      have free_in_vc x (vc.pre₁ op (term.subst y v t)), from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t), from free_in_vc.pre₁.inv this,
      have x ≠ y ∧ free_in_term x t, from free_of_subst_term this,
      show x ≠ y ∧ free_in_vc x (vc.pre₁ op t), from ⟨this.left, free_in_vc.preop this.right⟩
    )},
    case vc.pre₂ op t₁ t₂ { from (
      have vc.subst y v (vc.pre₂ op t₁ t₂) = vc.pre₂ op (term.subst y v t₁) (term.subst y v t₂),
      by unfold vc.subst,
      have free_in_vc x (vc.pre₂ op (term.subst y v t₁) (term.subst y v t₂)), from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₁) ∨ free_in_term x (term.subst y v t₂),
      from free_in_vc.pre₂.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₁),
        have x ≠ y ∧ free_in_term x t₁, from free_of_subst_term this,
        show x ≠ y ∧ free_in_vc x (vc.pre₂ op t₁ t₂), from ⟨this.left, free_in_vc.preop₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₂),
        have x ≠ y ∧ free_in_term x t₂, from free_of_subst_term this,
        show x ≠ y ∧ free_in_vc x (vc.pre₂ op t₁ t₂), from ⟨this.left, free_in_vc.preop₂ this.right⟩
      )
    )},
    case vc.post t₁ t₂ { from (
      have vc.subst y v (vc.post t₁ t₂) = vc.post (term.subst y v t₁) (term.subst y v t₂), by unfold vc.subst,
      have free_in_vc x (vc.post (term.subst y v t₁) (term.subst y v t₂)),
      from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₁) ∨ free_in_term x (term.subst y v t₂),
      from free_in_vc.post.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₁),
        have x ≠ y ∧ free_in_term x t₁, from free_of_subst_term this,
        show x ≠ y ∧ free_in_vc x (vc.post t₁ t₂), from ⟨this.left, free_in_vc.post₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₂),
        have x ≠ y ∧ free_in_term x t₂, from free_of_subst_term this,
        show x ≠ y ∧ free_in_vc x (vc.post t₁ t₂), from ⟨this.left, free_in_vc.post₂ this.right⟩
      )
    )},
    case vc.univ z P' P'_ih { from (
      have h: vc.subst y v (vc.univ z P') = vc.univ z (if y = z then P' else vc.subst y v P'), by unfold vc.subst,
      if y_eq_z: y = z then (
        have (if y = z then P' else vc.subst y v P') = P', by simp[y_eq_z],
        have vc.subst y v (vc.univ z P') = vc.univ z P',
        from @eq.subst vc (λa, vc.subst y v (vc.univ z P') = vc.univ z a)
                          (if y = z then P' else vc.subst y v P') P' this h,
        have h2: free_in_vc x (vc.univ z P'),
        from @eq.subst vc (λa, free_in_vc x a) (vc.subst y v (vc.univ z P')) (vc.univ z P') this x_free_in_subst,
        have x ≠ y, from (
          assume : x = y,
          have x = z, from eq.trans this y_eq_z,
          have free_in_vc x (vc.univ x P'),
          from @eq.subst var (λa, free_in_vc x (vc.univ a P')) z x this.symm h2,
          show «false», from (free_in_vc.univ.same.inv) this
        ),
        show x ≠ y ∧ free_in_vc x (vc.univ z P'), from ⟨this, h2⟩
      ) else (
        have (if y = z then P' else vc.subst y v P') = vc.subst y v P', by simp[y_eq_z],
        have vc.subst y v (vc.univ z P') = vc.univ z (vc.subst y v P'),
        from @eq.subst vc (λa, vc.subst y v (vc.univ z P') = vc.univ z a)
                          (if y = z then P' else vc.subst y v P') (vc.subst y v P') this h,
        have free_in_vc x (vc.univ z (vc.subst y v P')), from this ▸ x_free_in_subst,
        have h2: x ≠ z ∧ free_in_vc x (vc.subst y v P'), from free_in_vc.univ.inv this,
        have x ≠ y ∧ free_in_vc x P', from P'_ih h2.right,
        show x ≠ y ∧ free_in_vc x (vc.univ z P'), from ⟨this.left, free_in_vc.univ h2.left this.right⟩
      )
    )}
  end

lemma free_in_vc.subst2 {P: vc} {σ: env} {x y: var} {v: value}:
        free_in_vc x (vc.subst_env (σ[y↦v]) P) → x ≠ y ∧ free_in_vc x (vc.subst_env σ P) :=
  assume x_free: free_in_vc x (vc.subst_env (σ[y↦v]) P),
  have vc.subst_env (σ[y↦v]) P = vc.subst y v (vc.subst_env σ P), by unfold vc.subst_env,
  have free_in_vc x (vc.subst y v (vc.subst_env σ P)), from this ▸ x_free,
  show x ≠ y ∧ free_in_vc x (vc.subst_env σ P), from free_in_vc.subst this

lemma free_in_vc.subst_env {P: vc} {σ: env} {x: var}:
        free_in_vc x (vc.subst_env σ P) → free_in_vc x P :=
  assume x_free_in_subst: free_in_vc x (vc.subst_env σ P),
  begin
    induction σ with y v σ' ih,
    show free_in_vc x P, from (
      have vc.subst_env env.empty P = P, by unfold vc.subst_env,
      show free_in_vc x P, from this ▸ x_free_in_subst
    ),
    show free_in_vc x P, from (
      have free_in_vc x (vc.subst_env σ' P), from (free_in_vc.subst2 x_free_in_subst).right,
      show free_in_vc x P, from ih this
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
        have h2: term.subst y v' (term.var x) = (if y = x then v' else x), by unfold term.subst,
        decidable.by_cases (
          assume x_is_y: x = y,
          have term.subst y v' (term.var x) = v', by { rw[x_is_y], simp[x_is_y] at h2, from h2 },
          have term.subst_env (σ'[y↦v']) x = v', from eq.trans h this,
          have (∃v:value, term.subst_env (σ'[y↦v']) x = v), from exists.intro v' this,
          show (term.subst_env (σ'[y↦v']) x = x) ∨ (∃v:value, term.subst_env (σ'[y↦v']) x = v), from or.inr this
        ) (
          assume : ¬(x = y),
          have ¬(y = x), from ne.symm this,
          have term.subst y v' (term.var x) = x,  by { simp[this] at h2, from h2 },
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
          have ((σ'[y↦v']).apply x) = v', by { simp[h] at app, rw[h.left], from app },
          have some v' = none, from eq.trans this.symm σ'_does_not_have_x,
          by contradiction,
        show (term.subst_env (σ'[y↦v']) x = x), from
          have ((σ'[y↦v']).apply x) = σ'.apply x, by { simp[h] at app, from app },
          have σ'_x_is_none: σ'.apply x = none, from eq.trans this.symm σ'_does_not_have_x,
          have term.subst_env σ' x = x, from ih.left.mp σ'_x_is_none,
          have h2: term.subst_env (σ'[y↦v']) x = term.subst y v' x,
          from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) x this tsubst,
          have h3: term.subst y v' (term.var x) = (if y = x then v' else x), by unfold term.subst,
          have ¬(y = x) ∨ ¬(option.is_none (env.apply σ' x)) , from not_and_distrib.mp h,
          have ¬(y = x), from this.elim id ( 
            assume : ¬(option.is_none (env.apply σ' x)),
            have (env.apply σ' x) ≠ none, from option.is_none.ninv.mpr this,
            show ¬(y = x), from absurd σ'_x_is_none this
          ),
          have term.subst y v' (term.var x) = x, by { simp[this] at h3, from h3 },
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
          have h4: term.subst y v' (term.var x) = (if y = x then v' else x), by unfold term.subst,
          decidable.by_cases (
            assume : x = y,
            have y_eq_x: y = x, from eq.symm this,
            have term.subst y v' (term.var x) = v', by { simp[y_eq_x] at h4, rw[y_eq_x], from h4 },
            have term.subst_env (σ'[y↦v']) x = v', from eq.trans h3 this,
            have ↑x = ↑v', from eq.trans h.symm this,
            show (σ'[y↦v']) x = none, by contradiction
          ) (
            assume : ¬(x = y),
            have y_neq_x: ¬(y = x), from ne.symm this,
            have (σ'[y↦v']).apply x = σ'.apply x, by { simp[y_neq_x] at app, from app },
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
          have ((σ'[y↦v']).apply x = v'), by { simp[h] at app, rw[h.left], from app },
          have some v' = some v, from eq.trans this.symm env_has_x,
          have v'_is_v: v' = v, by injection this,
          have option.is_none (σ'.apply x), from h.right,
          have σ'.apply x = none, from option.is_none.inv.mpr this,
          have σ'_x_is_x: term.subst_env σ' x = x, from ih.left.mp this,
          have term.subst_env (σ'[y↦v']) x = term.subst y v' (term.subst_env σ' x),
          by unfold term.subst_env,
          have h2: term.subst_env (σ'[y↦v']) x = term.subst y v' (term.var x),
          from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) x σ'_x_is_x tsubst,
          have h3: term.subst y v' (term.var x) = (if y = x then v' else x), by unfold term.subst,
          have term.subst y v' (term.var x) = v', by { simp[h.left] at h3, rw[h.left], from h3 },
          show term.subst_env (σ'[y↦v']) x = v, from v'_is_v ▸ eq.trans h2 this
        ),
        show (term.subst_env (σ'[y↦v']) ↑x = ↑v), from (
          have (σ'[y↦v']).apply x = σ'.apply x, by { simp [h] at app, from app },
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
            have term.subst y v' (term.var x) = v', by { simp at this, from this },
            have term.subst_env (σ'[y↦v']) x = v', from eq.trans h3 this,
            have ↑v = ↑v', from eq.trans h.symm this,
            have v_is_v': v = v', by injection this,
            have opt_is_none: option.is_none (env.apply σ' x), from option.is_none.inv.mp σ'_x_is_none,
            have (if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = v',
            by { simp[x_is_y.symm], simp[opt_is_none] },
            have (σ'[y↦v']).apply x = v', from eq.trans app this,
            have (σ'[y↦v']) x = some v', from this,
            show (σ'[y↦v']) x = some v, from @eq.subst value (λa, (σ'[y↦v']) x = some a) v' v v_is_v'.symm this
          ) (
            assume : ¬(x = y),
            have ¬(y = x), from ne.symm this,
            have term.subst y v' (term.var x) = x, by { simp[this] at h4, from h4 },
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
          from option.some_iff_not_none.mp (option.is_some_iff_exists.mpr (exists.intro v σ'_x_app_is_v)),
          have (if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = σ'.apply x,
          by { simp[opt_is_not_none] },
          have (σ'[y↦v']) x = σ'.apply x, from eq.trans app this,
          show (σ'[y↦v']) x = some v, from eq.trans this σ'_x_app_is_v
        )
      )
    end
  end
end

lemma term.not_free_of_subst {x: var} {v: value} {t: term}: x ∉ FV (term.subst x v t) :=
  assume x_free: x ∈ FV (term.subst x v t),
  begin
    induction t with a,

    show «false», by begin -- term.value
      unfold term.subst at x_free,
      cases x_free
    end,

    show «false», by begin -- term.var
      unfold term.subst at x_free,
      by_cases (x = a) with h,
      simp[h] at x_free,
      cases x_free,
      simp[h] at x_free,
      cases x_free,
      contradiction
    end,

    show «false», by begin -- term.unop
      unfold term.subst at x_free,
      have h, from free_in_term.unop.inv x_free,
      contradiction
    end,

    show «false», by begin -- term.binop
      unfold term.subst at x_free,
      have h, from free_in_term.binop.inv x_free,
      cases h with h1 h2,
      contradiction,
      contradiction
    end,

    show «false», by begin -- term.app
      unfold term.subst at x_free,
      have h, from free_in_term.app.inv x_free,
      cases h with h1 h2,
      contradiction,
      contradiction
    end
  end

lemma prop.not_free_of_subst {x: var} {v: value} {P: prop}: x ∉ FV (prop.subst x v P) :=
  assume x_free: x ∈ FV (prop.subst x v P),
  begin
    induction P,
    case prop.term t { from (
      have prop.subst x v (prop.term t) = (term.subst x v t), by unfold prop.subst,
      have free_in_prop x (prop.term (term.subst x v t)), from this ▸ x_free,
      have x ∈ FV (term.subst x v t), from free_in_prop.term.inv this,
      show «false», from term.not_free_of_subst this
    )},
    case prop.not P₁ P₁_ih { from (
      have prop.subst x v (prop.not P₁) = (P₁.subst x v).not, by unfold prop.subst,
      have x ∈ FV (P₁.subst x v).not, from this ▸ x_free,
      have x ∈ FV (P₁.subst x v), from free_in_prop.not.inv this,
      show «false», from P₁_ih this
    )},
    case prop.and P₁ P₂ P₁_ih P₂_ih { from (
      have prop.subst x v (prop.and P₁ P₂) = (P₁.subst x v && P₂.subst x v), by unfold prop.subst,
      have x ∈ FV (P₁.subst x v && P₂.subst x v), from this ▸ x_free,
      or.elim (free_in_prop.and.inv this) (
        assume : x ∈ FV (P₁.subst x v),
        show «false», from P₁_ih this
      ) (
        assume : x ∈ FV (P₂.subst x v),
        show «false», from P₂_ih this
      )
    )},
    case prop.or P₁ P₂ P₁_ih P₂_ih { from (
      have prop.subst x v (prop.or P₁ P₂) = (P₁.subst x v || P₂.subst x v), by unfold prop.subst,
      have x ∈ FV (P₁.subst x v || P₂.subst x v), from this ▸ x_free,
      or.elim (free_in_prop.or.inv this) (
        assume : x ∈ FV (P₁.subst x v),
        show «false», from P₁_ih this
      ) (
        assume : x ∈ FV (P₂.subst x v),
        show «false», from P₂_ih this
      )
    )},
    case prop.pre t₁ t₂ { from (
      have prop.subst x v (prop.pre t₁ t₂) = prop.pre (t₁.subst x v) (t₂.subst x v), by unfold prop.subst,
      have x ∈ FV (prop.pre (t₁.subst x v) (t₂.subst x v)), from this ▸ x_free,
      or.elim (free_in_prop.pre.inv this) (
        assume : x ∈ FV (t₁.subst x v),
        show «false», from term.not_free_of_subst this
      ) (
        assume : x ∈ FV (t₂.subst x v),
        show «false», from term.not_free_of_subst this
      )
    )},
    case prop.pre₁ op t { from (
      have prop.subst x v (prop.pre₁ op t) = prop.pre₁ op (t.subst x v), by unfold prop.subst,
      have x ∈ FV (prop.pre₁ op (t.subst x v)), from this ▸ x_free,
      have x ∈ FV (t.subst x v), from free_in_prop.pre₁.inv this,
      show «false», from term.not_free_of_subst this
    )},
    case prop.pre₂ op t₁ t₂ { from (
      have prop.subst x v (prop.pre₂ op t₁ t₂) = prop.pre₂ op (t₁.subst x v) (t₂.subst x v),
      by unfold prop.subst,
      have x ∈ FV (prop.pre₂ op (t₁.subst x v) (t₂.subst x v)), from this ▸ x_free,
      or.elim (free_in_prop.pre₂.inv this) (
        assume : x ∈ FV (t₁.subst x v),
        show «false», from term.not_free_of_subst this
      ) (
        assume : x ∈ FV (t₂.subst x v),
        show «false», from term.not_free_of_subst this
      )
    )},
    case prop.post t₁ t₂ { from (
      have prop.subst x v (prop.post t₁ t₂) = prop.post (t₁.subst x v) (t₂.subst x v), by unfold prop.subst,
      have x ∈ FV (prop.post (t₁.subst x v) (t₂.subst x v)), from this ▸ x_free,
      or.elim (free_in_prop.post.inv this) (
        assume : x ∈ FV (t₁.subst x v),
        show «false», from term.not_free_of_subst this
      ) (
        assume : x ∈ FV (t₂.subst x v),
        show «false», from term.not_free_of_subst this
      )
    )},
    case prop.call t₁ t₂ { from (
      have prop.subst x v (prop.call t₁ t₂) = prop.call (t₁.subst x v) (t₂.subst x v), by unfold prop.subst,
      have x ∈ FV (prop.call (t₁.subst x v) (t₂.subst x v)), from this ▸ x_free,
      or.elim (free_in_prop.call.inv this) (
        assume : x ∈ FV (t₁.subst x v),
        show «false», from term.not_free_of_subst this
      ) (
        assume : x ∈ FV (t₂.subst x v),
        show «false», from term.not_free_of_subst this
      )
    )},
    case prop.forallc y t P₁ P₁_ih { from (
      have prop.subst x v (prop.forallc y t P₁)
         = prop.forallc y (term.subst x v t) (if x = y then P₁ else P₁.subst x v), by unfold prop.subst,
      have x ∈ FV (prop.forallc y (t.subst x v) (if x = y then P₁ else P₁.subst x v)), from this ▸ x_free,
      have y_neq_x: x ≠ y, from (free_in_prop.forallc.inv this).left,
      have x ∈ FV (prop.forallc y (t.subst x v) (P₁.subst x v)), by { simp[y_neq_x] at this, from this },
      have x ∈ FV (t.subst x v) ∨ x ∈ FV (P₁.subst x v), from (free_in_prop.forallc.inv this).right,
      or.elim this (
        assume : x ∈ FV (t.subst x v),
        show «false», from term.not_free_of_subst this
      ) (
        assume : x ∈ FV (P₁.subst x v),
        show «false», from P₁_ih this
      )
    )},
    case prop.exis y P₁ P₁_ih { from (
      have prop.subst x v (prop.exis y P₁)
         = prop.exis y (if x = y then P₁ else P₁.subst x v), by unfold prop.subst,
      have x ∈ FV (prop.exis y (if x = y then P₁ else P₁.subst x v)), from this ▸ x_free,
      have y_neq_x: x ≠ y, from (free_in_prop.exis.inv this).left,
      have x ∈ FV (prop.exis y (P₁.subst x v)), by { simp[y_neq_x] at this, from this },
      have x ∈ FV (P₁.subst x v), from (free_in_prop.exis.inv this).right,
      show «false», from P₁_ih this
    )}
  end

lemma prop.not_free_of_subst_env {x: var} {σ: env} {P: prop}: x ∈ σ → x ∉ FV (prop.subst_env σ P) :=
  assume x_in_σ: x ∈ σ,
  assume x_free: x ∈ FV (prop.subst_env σ P),
  begin
    induction σ with y v σ' ih,

    -- env.empty
    show «false», by cases x_in_σ,

    -- σ'[x↦v]
    show «false», from (
      have prop.subst_env (σ'[y↦v]) P = prop.subst y v (prop.subst_env σ' P), by unfold prop.subst_env,
      have x ∈ FV (prop.subst y v (prop.subst_env σ' P)), from this ▸ x_free,
      have x_neq_y: x ≠ y, from (free_of_subst_prop this).left,
      have h: x ∈ FV (prop.subst_env σ' P), from (free_of_subst_prop this).right,
      have x = y ∨ x ∈ σ', from env.contains.inv x_in_σ,
      or.elim this (
        assume : x = y,
        show «false», from x_neq_y this
      ) (
        assume : x ∈ σ',
        have x ∉ FV (prop.subst_env σ' P), from ih this,
        show «false», from this h
      )
    )
  end

lemma term.subst_env.unop {σ: env} {op: unop} {t: term}:
      term.subst_env σ (term.unop op t) = term.unop op (term.subst_env σ t) :=
begin
  induction σ with x v σ' ih,

  show (term.subst_env env.empty (term.unop op t) = term.unop op (term.subst_env env.empty t)),
  by calc
        term.subst_env env.empty (term.unop op t)
      = (term.unop op t) : by unfold term.subst_env
  ... = (term.unop op (term.subst_env env.empty t)) : by unfold term.subst_env,

  show (term.subst_env (σ'[x↦v]) (term.unop op t) = (term.unop op (term.subst_env (σ'[x↦v]) t))),
  by calc
        term.subst_env (σ'[x↦v]) (term.unop op t)
      = term.subst x v (term.subst_env σ' (term.unop op t)) : by unfold term.subst_env
  ... = term.subst x v (term.unop op (term.subst_env σ' t)) : by rw[ih]
  ... = term.unop op (term.subst x v (term.subst_env σ' t)) : by unfold term.subst
  ... = term.unop op (term.subst_env (σ'[x↦v]) t) : by unfold term.subst_env
end

lemma term.subst_env.binop {σ: env} {op: binop} {t₁ t₂: term}:
      term.subst_env σ (term.binop op t₁ t₂) = term.binop op (term.subst_env σ t₁) (term.subst_env σ t₂) :=
begin
  induction σ with x v σ' ih,

  show (term.subst_env env.empty (term.binop op t₁ t₂)
      = term.binop op (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)),
  by calc
        term.subst_env env.empty (term.binop op t₁ t₂)
      = (term.binop op t₁ t₂) : by unfold term.subst_env
  ... = (term.binop op (term.subst_env env.empty t₁) t₂) : by unfold term.subst_env
  ... = (term.binop op (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)) : by unfold term.subst_env,

  show (term.subst_env (σ'[x↦v]) (term.binop op t₁ t₂)
      = (term.binop op (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂))),
  by calc
        term.subst_env (σ'[x↦v]) (term.binop op t₁ t₂)
      = term.subst x v (term.subst_env σ' (term.binop op t₁ t₂)) : by unfold term.subst_env
  ... = term.subst x v (term.binop op (term.subst_env σ' t₁) (term.subst_env σ' t₂)) : by rw[ih]
  ... = term.binop op (term.subst x v (term.subst_env σ' t₁))
                      (term.subst x v (term.subst_env σ' t₂)) : by unfold term.subst
  ... = term.binop op (term.subst_env (σ'[x↦v]) t₁)
                      (term.subst x v (term.subst_env σ' t₂)) : by unfold term.subst_env
  ... = term.binop op (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂) : by unfold term.subst_env
end

lemma prop.subst_env.term {σ: env} {t: term}:
  prop.subst_env σ t = prop.term (term.subst_env σ t) :=
begin
  induction σ with x v σ' ih,

  show (prop.subst_env env.empty t = prop.term (term.subst_env env.empty t)), by begin
    have : (term.subst_env env.empty t = t), by unfold term.subst_env,
    have h2: (prop.term (term.subst_env env.empty t) = prop.term t), by simp[this],
    calc
      prop.subst_env env.empty t = t : by unfold prop.subst_env
                             ... = prop.term t : by refl
                             ... = prop.term (term.subst_env env.empty t) : by rw[←h2]
  end,

  show (prop.subst_env (σ'[x↦v]) t = prop.term (term.subst_env (σ'[x↦v]) t)),
  by calc
        prop.subst_env (σ'[x↦v]) t = prop.subst x v (prop.subst_env σ' t) : by unfold prop.subst_env
                               ... = prop.subst x v (prop.term (term.subst_env σ' t)) : by rw[ih]
                               ... = term.subst x v (term.subst_env σ' t) : by unfold prop.subst
                               ... = term.subst_env (σ'[x↦v]) t : by unfold term.subst_env
end

lemma prop.subst_env.not {σ: env} {P: prop}:
      prop.subst_env σ P.not = (prop.subst_env σ P).not :=
begin
  induction σ with x v σ' ih,

  show (prop.subst_env env.empty P.not = (prop.subst_env env.empty P).not),
  by calc
        prop.subst_env env.empty P.not = P.not : by unfold prop.subst_env
                                   ... = (prop.subst_env env.empty P).not : by unfold prop.subst_env,

  show (prop.subst_env (σ'[x↦v]) P.not = (prop.subst_env (σ'[x↦v]) P).not),
  by calc
        prop.subst_env (σ'[x↦v]) P.not = prop.subst x v (prop.subst_env σ' P.not) : by unfold prop.subst_env
                                   ... = prop.subst x v (prop.subst_env σ' P).not : by rw[ih]
                                   ... = (prop.subst x v (prop.subst_env σ' P)).not : by unfold prop.subst
                                   ... = (prop.subst_env (σ'[x↦v]) P).not : by unfold prop.subst_env
end

lemma prop.subst_env.and {σ: env} {P Q: prop}:
      prop.subst_env σ (P && Q) = (prop.subst_env σ P && prop.subst_env σ Q) :=
begin
  induction σ with x v σ' ih,

  show (prop.subst_env env.empty (P && Q) = (prop.subst_env env.empty P && prop.subst_env env.empty Q)),
  by calc
        prop.subst_env env.empty (P && Q) = (P && Q) : by unfold prop.subst_env
                                      ... = (prop.subst_env env.empty P && Q) : by unfold prop.subst_env
                                      ... = (prop.subst_env env.empty P && prop.subst_env env.empty Q)
                                                     : by unfold prop.subst_env,

  show (prop.subst_env (σ'[x↦v]) (P && Q) = (prop.subst_env (σ'[x↦v]) P && prop.subst_env (σ'[x↦v]) Q)),
  by calc
        prop.subst_env (σ'[x↦v]) (P && Q) = prop.subst x v (prop.subst_env σ' (P && Q)) : by unfold prop.subst_env
                                      ... = prop.subst x v (prop.subst_env σ' P && prop.subst_env σ' Q) : by rw[ih]
                                      ... = (prop.subst x v (prop.subst_env σ' P) &&
                                             prop.subst x v (prop.subst_env σ' Q)) : by refl
                                      ... = (prop.subst_env (σ'[x↦v]) P &&
                                             prop.subst x v (prop.subst_env σ' Q)) : by unfold prop.subst_env
                                      ... = (prop.subst_env (σ'[x↦v]) P && prop.subst_env (σ'[x↦v]) Q)
                                                                               : by unfold prop.subst_env
end

lemma prop.subst_env.or {σ: env} {P Q: prop}:
      prop.subst_env σ (P || Q) = (prop.subst_env σ P || prop.subst_env σ Q) :=
begin
  induction σ with x v σ' ih,

  show (prop.subst_env env.empty (P || Q) = (prop.subst_env env.empty P || prop.subst_env env.empty Q)),
  by calc
        prop.subst_env env.empty (P || Q) = (P || Q) : by unfold prop.subst_env
                                      ... = (prop.subst_env env.empty P || Q) : by by unfold prop.subst_env
                                      ... = (prop.subst_env env.empty P || prop.subst_env env.empty Q)
                                                     : by unfold prop.subst_env,

  show (prop.subst_env (σ'[x↦v]) (P || Q) = (prop.subst_env (σ'[x↦v]) P || prop.subst_env (σ'[x↦v]) Q)),
  by calc
        prop.subst_env (σ'[x↦v]) (P || Q) = prop.subst x v (prop.subst_env σ' (P || Q)) : by unfold prop.subst_env
                                      ... = prop.subst x v (prop.subst_env σ' P || prop.subst_env σ' Q) : by rw[ih]
                                      ... = (prop.subst x v (prop.subst_env σ' P) ||
                                             prop.subst x v (prop.subst_env σ' Q)) : by refl
                                      ... = (prop.subst_env (σ'[x↦v]) P ||
                                             prop.subst x v (prop.subst_env σ' Q)) : by unfold prop.subst_env
                                      ... = (prop.subst_env (σ'[x↦v]) P || prop.subst_env (σ'[x↦v]) Q)
                                               : by unfold prop.subst_env
end

lemma prop.subst_env.implies {σ: env} {P Q: prop}:
      prop.subst_env σ (prop.implies P Q) = prop.implies (prop.subst_env σ P) (prop.subst_env σ Q) :=
  have h1: prop.subst_env σ (prop.implies P Q) = prop.subst_env σ (P.not || Q), by refl,
  have prop.subst_env σ (P.not || Q) = prop.subst_env σ P.not || prop.subst_env σ Q, from prop.subst_env.or,
  have h2: prop.subst_env σ (prop.implies P Q) = prop.subst_env σ P.not || prop.subst_env σ Q, from this ▸ h1,
  have prop.subst_env σ P.not = prop.not (prop.subst_env σ P), from prop.subst_env.not,
  have prop.subst_env σ (prop.implies P Q) = prop.not (prop.subst_env σ P) || prop.subst_env σ Q, from this ▸ h2,
  show prop.subst_env σ (prop.implies P Q) = prop.implies (prop.subst_env σ P) (prop.subst_env σ Q), from this

lemma prop.subst_env.pre {σ: env} {t₁ t₂: term}:
      prop.subst_env σ (prop.pre t₁ t₂) = prop.pre (term.subst_env σ t₁) (term.subst_env σ t₂) :=
begin
  induction σ with x v σ' ih,

  show (prop.subst_env env.empty (prop.pre t₁ t₂)
      = prop.pre (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)),
  by calc
        prop.subst_env env.empty (prop.pre t₁ t₂)
      = (prop.pre t₁ t₂) : by unfold prop.subst_env
  ... = (prop.pre (term.subst_env env.empty t₁) t₂) : by unfold term.subst_env
  ... = (prop.pre (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)) : by unfold term.subst_env,

  show (prop.subst_env (σ'[x↦v]) (prop.pre t₁ t₂)
      = prop.pre (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂)),
  by calc
        prop.subst_env (σ'[x↦v]) (prop.pre t₁ t₂)
      = prop.subst x v (prop.subst_env σ' (prop.pre t₁ t₂)) : by unfold prop.subst_env
  ... = prop.subst x v (prop.pre (term.subst_env σ' t₁) (term.subst_env σ' t₂)) : by rw[ih]
  ... = prop.pre (term.subst x v (term.subst_env σ' t₁)) (term.subst x v (term.subst_env σ' t₂)) : by unfold prop.subst
  ... = prop.pre (term.subst_env (σ'[x↦v]) t₁) (term.subst x v (term.subst_env σ' t₂)) : by unfold term.subst_env
  ... = prop.pre (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂) : by unfold term.subst_env
end

lemma prop.subst_env.post {σ: env} {t₁ t₂: term}:
      prop.subst_env σ (prop.post t₁ t₂) = prop.post (term.subst_env σ t₁) (term.subst_env σ t₂) :=
begin
  induction σ with x v σ' ih,

  show (prop.subst_env env.empty (prop.post t₁ t₂)
      = prop.post (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)),
  by calc
        prop.subst_env env.empty (prop.post t₁ t₂)
      = (prop.post t₁ t₂) : by unfold prop.subst_env
  ... = (prop.post (term.subst_env env.empty t₁) t₂) : by unfold term.subst_env
  ... = (prop.post (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)) : by unfold term.subst_env,

  show (prop.subst_env (σ'[x↦v]) (prop.post t₁ t₂)
      = prop.post (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂)),
  by calc
        prop.subst_env (σ'[x↦v]) (prop.post t₁ t₂)
      = prop.subst x v (prop.subst_env σ' (prop.post t₁ t₂)) : by unfold prop.subst_env
  ... = prop.subst x v (prop.post (term.subst_env σ' t₁) (term.subst_env σ' t₂)) : by rw[ih]
  ... = prop.post (term.subst x v (term.subst_env σ' t₁)) (term.subst x v (term.subst_env σ' t₂)) : by unfold prop.subst
  ... = prop.post (term.subst_env (σ'[x↦v]) t₁) (term.subst x v (term.subst_env σ' t₂)) : by unfold term.subst_env
  ... = prop.post (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂) : by unfold term.subst_env
end

lemma prop.subst_env.forallc {σ: env} {x: var} {t: term} {P: prop}:
      (x ∉ σ) → (prop.subst_env σ (prop.forallc x t P) = prop.forallc x (term.subst_env σ t) (prop.subst_env σ P)) :=
begin
  assume x_not_in_σ,
  induction σ with y v σ' ih,

  show (prop.subst_env env.empty (prop.forallc x t P)
      = prop.forallc x (term.subst_env env.empty t) (prop.subst_env env.empty P)),
  by calc
        prop.subst_env env.empty (prop.forallc x t P)
      = prop.forallc x t P : by unfold prop.subst_env
  ... = prop.forallc x t (prop.subst_env env.empty P) : by unfold prop.subst_env
  ... = prop.forallc x (term.subst_env env.empty t) (prop.subst_env env.empty P) : by unfold term.subst_env,

  show (prop.subst_env (σ'[y↦v]) (prop.forallc x t P)
      = prop.forallc x (term.subst_env (σ'[y↦v]) t) (prop.subst_env (σ'[y↦v]) P)), from (
    have ¬ (x = y ∨ x ∈ σ'), from env.contains.same.inv x_not_in_σ,
    have x_neq_y: x ≠ y, from (not_or_distrib.mp this).left,
    have x ∉ σ', from (not_or_distrib.mp this).right,
    have h: prop.subst_env σ' (prop.forallc x t P) = prop.forallc x (term.subst_env σ' t) (prop.subst_env σ' P),
    from ih this,

    calc
        prop.subst_env (σ'[y↦v]) (prop.forallc x t P)
      = prop.subst y v (prop.subst_env σ' (prop.forallc x t P)) : by unfold prop.subst_env
  ... = prop.subst y v (prop.forallc x (term.subst_env σ' t) (prop.subst_env σ' P)) : by rw[h]
  ... = prop.forallc x (term.subst y v (term.subst_env σ' t)) (if y = x then prop.subst_env σ' P else (prop.subst_env σ' P).subst y v)
     : by unfold prop.subst
  ... = prop.forallc x (term.subst y v (term.subst_env σ' t)) ((prop.subst_env σ' P).subst y v) : by simp[x_neq_y.symm]
  ... = prop.forallc x (term.subst y v (term.subst_env σ' t)) (prop.subst_env (σ'[y↦v]) P) : by unfold prop.subst_env
  ... = prop.forallc x (term.subst_env (σ'[y↦v]) t) (prop.subst_env (σ'[y↦v]) P) : by unfold term.subst_env
  )
end

lemma vc.subst.implies {x: var} {v: value} {P Q: vc}:
      vc.subst x v (vc.implies P Q) = vc.implies (vc.subst x v P) (vc.subst x v Q) :=
  by calc 
       vc.subst x v (vc.implies P Q) = vc.subst x v (vc.or (vc.not P) Q) : rfl
                                 ... = vc.subst x v (vc.not P) || vc.subst x v Q : by unfold vc.subst
                                 ... = (vc.subst x v P).not || vc.subst x v Q : by unfold vc.subst

lemma vc.subst_env.term {σ: env} {t: term}:
  vc.subst_env σ t = vc.term (term.subst_env σ t) :=
begin
  induction σ with x v σ' ih,

  show (vc.subst_env env.empty t = vc.term (term.subst_env env.empty t)), by begin
    have : (term.subst_env env.empty t = t), by unfold term.subst_env,
    have h2: (vc.term (term.subst_env env.empty t) = vc.term t), by simp[this],
    calc
      vc.subst_env env.empty t = t : by unfold vc.subst_env
                           ... = vc.term t : by refl
                           ... = vc.term (term.subst_env env.empty t) : by rw[←h2]
  end,

  show (vc.subst_env (σ'[x↦v]) t = vc.term (term.subst_env (σ'[x↦v]) t)),
  by calc
        vc.subst_env (σ'[x↦v]) t = vc.subst x v (vc.subst_env σ' t) : by unfold vc.subst_env
                             ... = vc.subst x v (vc.term (term.subst_env σ' t)) : by rw[ih]
                             ... = term.subst x v (term.subst_env σ' t) : by unfold vc.subst
                             ... = term.subst_env (σ'[x↦v]) t : by unfold term.subst_env
end

lemma vc.subst_env.not {σ: env} {P: vc}:
      vc.subst_env σ P.not = (vc.subst_env σ P).not :=
begin
  induction σ with x v σ' ih,

  show (vc.subst_env env.empty P.not = (vc.subst_env env.empty P).not),
  by calc
        vc.subst_env env.empty P.not = P.not : by unfold vc.subst_env
                                 ... = (vc.subst_env env.empty P).not : by unfold vc.subst_env,

  show (vc.subst_env (σ'[x↦v]) P.not = (vc.subst_env (σ'[x↦v]) P).not),
  by calc
        vc.subst_env (σ'[x↦v]) P.not = vc.subst x v (vc.subst_env σ' P.not) : by unfold vc.subst_env
                                 ... = vc.subst x v (vc.subst_env σ' P).not : by rw[ih]
                                 ... = (vc.subst x v (vc.subst_env σ' P)).not : by unfold vc.subst
                                 ... = (vc.subst_env (σ'[x↦v]) P).not : by unfold vc.subst_env
end

lemma vc.subst_env.and {σ: env} {P Q: vc}:
      vc.subst_env σ (P && Q) = (vc.subst_env σ P && vc.subst_env σ Q) :=
begin
  induction σ with x v σ' ih,

  show (vc.subst_env env.empty (P && Q) = (vc.subst_env env.empty P && vc.subst_env env.empty Q)),
  by calc
        vc.subst_env env.empty (P && Q) = (P && Q) : by unfold vc.subst_env
                                    ... = (vc.subst_env env.empty P && Q) : by unfold vc.subst_env
                                    ... = (vc.subst_env env.empty P && vc.subst_env env.empty Q)
                                                   : by unfold vc.subst_env,

  show (vc.subst_env (σ'[x↦v]) (P && Q) = (vc.subst_env (σ'[x↦v]) P && vc.subst_env (σ'[x↦v]) Q)),
  by calc
        vc.subst_env (σ'[x↦v]) (P && Q) = vc.subst x v (vc.subst_env σ' (P && Q)) : by unfold vc.subst_env
                                    ... = vc.subst x v (vc.subst_env σ' P && vc.subst_env σ' Q) : by rw[ih]
                                    ... = (vc.subst x v (vc.subst_env σ' P) &&
                                           vc.subst x v (vc.subst_env σ' Q)) : by refl
                                    ... = (vc.subst_env (σ'[x↦v]) P &&
                                           vc.subst x v (vc.subst_env σ' Q)) : by unfold vc.subst_env
                                    ... = (vc.subst_env (σ'[x↦v]) P && vc.subst_env (σ'[x↦v]) Q)
                                                                             : by unfold vc.subst_env
end

lemma vc.subst_env.or {σ: env} {P Q: vc}:
      vc.subst_env σ (P || Q) = (vc.subst_env σ P || vc.subst_env σ Q) :=
begin
  induction σ with x v σ' ih,

  show (vc.subst_env env.empty (P || Q) = (vc.subst_env env.empty P || vc.subst_env env.empty Q)),
  by calc
        vc.subst_env env.empty (P || Q) = (P || Q) : by unfold vc.subst_env
                                    ... = (vc.subst_env env.empty P || Q) : by by unfold vc.subst_env
                                    ... = (vc.subst_env env.empty P || vc.subst_env env.empty Q)
                                                   : by unfold vc.subst_env,

  show (vc.subst_env (σ'[x↦v]) (P || Q) = (vc.subst_env (σ'[x↦v]) P || vc.subst_env (σ'[x↦v]) Q)),
  by calc
        vc.subst_env (σ'[x↦v]) (P || Q) = vc.subst x v (vc.subst_env σ' (P || Q)) : by unfold vc.subst_env
                                    ... = vc.subst x v (vc.subst_env σ' P || vc.subst_env σ' Q) : by rw[ih]
                                    ... = (vc.subst x v (vc.subst_env σ' P) ||
                                           vc.subst x v (vc.subst_env σ' Q)) : by refl
                                    ... = (vc.subst_env (σ'[x↦v]) P ||
                                           vc.subst x v (vc.subst_env σ' Q)) : by unfold vc.subst_env
                                    ... = (vc.subst_env (σ'[x↦v]) P || vc.subst_env (σ'[x↦v]) Q)
                                             : by unfold vc.subst_env
end

lemma vc.subst_env.pre₁ {σ: env} {op: unop} {t: term}:
      vc.subst_env σ (vc.pre₁ op t) = vc.pre₁ op (term.subst_env σ t) :=
begin
  induction σ with x v σ' ih,

  show (vc.subst_env env.empty (vc.pre₁ op t) = vc.pre₁ op (term.subst_env env.empty t)),
  by calc
        vc.subst_env env.empty (vc.pre₁ op t) = (vc.pre₁ op t) : by unfold vc.subst_env
                                          ... = (vc.pre₁ op (term.subst_env env.empty t)) : by unfold term.subst_env,

  show (vc.subst_env (σ'[x↦v]) (vc.pre₁ op t) = vc.pre₁ op (term.subst_env (σ'[x↦v]) t)),
  by calc
        vc.subst_env (σ'[x↦v]) (vc.pre₁ op t) = vc.subst x v (vc.subst_env σ' (vc.pre₁ op t)) : by unfold vc.subst_env
                                          ... = vc.subst x v (vc.pre₁ op (term.subst_env σ' t)) : by rw[ih]
                                          ... = vc.pre₁ op (term.subst x v (term.subst_env σ' t)) : by unfold vc.subst
                                          ... = vc.pre₁ op (term.subst_env (σ'[x↦v]) t) : by unfold term.subst_env
end

lemma vc.subst_env.pre₂ {σ: env} {op: binop} {t₁ t₂: term}:
      vc.subst_env σ (vc.pre₂ op t₁ t₂) = vc.pre₂ op (term.subst_env σ t₁) (term.subst_env σ t₂) :=
begin
  induction σ with x v σ' ih,

  show (vc.subst_env env.empty (vc.pre₂ op t₁ t₂)
      = vc.pre₂ op (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)),
  by calc
        vc.subst_env env.empty (vc.pre₂ op t₁ t₂)
      = (vc.pre₂ op t₁ t₂) : by unfold vc.subst_env
  ... = (vc.pre₂ op (term.subst_env env.empty t₁) t₂) : by unfold term.subst_env
  ... = (vc.pre₂ op (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)) : by unfold term.subst_env,

  show (vc.subst_env (σ'[x↦v]) (vc.pre₂ op t₁ t₂)
      = vc.pre₂ op (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂)),
  by calc
        vc.subst_env (σ'[x↦v]) (vc.pre₂ op t₁ t₂)
      = vc.subst x v (vc.subst_env σ' (vc.pre₂ op t₁ t₂)) : by unfold vc.subst_env
  ... = vc.subst x v (vc.pre₂ op (term.subst_env σ' t₁) (term.subst_env σ' t₂)) : by rw[ih]
  ... = vc.pre₂ op (term.subst x v (term.subst_env σ' t₁)) (term.subst x v (term.subst_env σ' t₂)) : by unfold vc.subst
  ... = vc.pre₂ op (term.subst_env (σ'[x↦v]) t₁) (term.subst x v (term.subst_env σ' t₂)) : by unfold term.subst_env
  ... = vc.pre₂ op (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂) : by unfold term.subst_env
end

lemma vc.subst_env.univ {σ: env} {x: var} {P: vc}:
      (x ∉ σ) → (vc.subst_env σ (vc.univ x P) = vc.univ x (vc.subst_env σ P)) :=
begin
  assume x_not_in_σ,
  induction σ with y v σ' ih,

  show (vc.subst_env env.empty (vc.univ x P) = vc.univ x (vc.subst_env env.empty P)),
  by calc
        vc.subst_env env.empty (vc.univ x P) = (vc.univ x P) : by unfold vc.subst_env
                                         ... = vc.univ x (vc.subst_env env.empty P) : by unfold vc.subst_env,

  show (vc.subst_env (σ'[y↦v]) (vc.univ x P) = vc.univ x (vc.subst_env (σ'[y↦v]) P)), from (
    have ¬ (x = y ∨ x ∈ σ'), from env.contains.same.inv x_not_in_σ,
    have x_neq_y: x ≠ y, from (not_or_distrib.mp this).left,
    have x ∉ σ', from (not_or_distrib.mp this).right,
    have h: vc.subst_env σ' (vc.univ x P) = vc.univ x (vc.subst_env σ' P), from ih this,

    calc
        vc.subst_env (σ'[y↦v]) (vc.univ x P)
           = vc.subst y v (vc.subst_env σ' (vc.univ x P)) : by unfold vc.subst_env
       ... = vc.subst y v (vc.univ x (vc.subst_env σ' P)) : by rw[h]
       ... = vc.univ x (if y = x then vc.subst_env σ' P else (vc.subst_env σ' P).subst y v) : by unfold vc.subst
       ... = vc.univ x ((vc.subst_env σ' P).subst y v) : by simp[x_neq_y.symm]
       ... = vc.univ x (vc.subst_env (σ'[y↦v]) P) : by unfold vc.subst_env
  )
end
