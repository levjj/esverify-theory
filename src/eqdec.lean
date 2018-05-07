-- decidable equality of values, terms, expressions, etc.

import .syntax .etc .sizeof

instance : decidable_eq unop := by tactic.mk_dec_eq_instance
instance : decidable_eq binop := by tactic.mk_dec_eq_instance

def wf_measure : has_well_founded
(psum (Σ' (v₁ : value), value)
  (psum (Σ' (e₁ : exp), exp)
    (psum (Σ' (t₁ : term), term)
      (psum (Σ' (R : spec), spec)
            (Σ' (σ₁ : env), env)))))
:= ⟨_, measure_wf $ λ s,
  match s with
  | psum.inl a := a.1.sizeof
  | psum.inr (psum.inl a) := a.1.sizeof
  | psum.inr (psum.inr (psum.inl a)) := a.1.sizeof
  | psum.inr (psum.inr (psum.inr (psum.inl a))) := a.1.sizeof
  | psum.inr (psum.inr (psum.inr (psum.inr a))) := a.1.sizeof
  end⟩

mutual def value.dec_eq, exp.dec_eq, term.dec_eq, spec.dec_eq, env.dec_eq

with value.dec_eq : ∀ (v₁ v₂: value), decidable (v₁ = v₂)
| v₁ v₂ :=
  let z := v₁ in
  have h: z = v₁, from rfl,
  value.cases_on (λv₁, (z = v₁) → decidable (v₁ = v₂)) v₁ (
    assume : z = value.true,
    show decidable (value.true = v₂), from
    value.cases_on (λv₂, decidable (value.true = v₂)) v₂ (
      show decidable (value.true = value.true), from is_true rfl
    ) (
      have value.true ≠ value.false, by contradiction,
      show decidable (value.true = value.false), from is_false this
    ) (
      assume n: ℤ,
      have value.true ≠ value.num n, by contradiction,
      show decidable (value.true = value.num n), from is_false this
    ) (
      assume f x R S e σ, 
      have value.true ≠ value.func f x R S e σ, by contradiction,
      show decidable (value.true = value.func f x R S e σ), from is_false this
    )
  )
  (
    assume : z = value.false,
    show decidable (value.false = v₂), from
    value.cases_on (λv₂, decidable (value.false = v₂)) v₂ (
      have value.false ≠ value.true, by contradiction,
      show decidable (value.false = value.true), from is_false this
    ) (
      show decidable (value.false = value.false), from is_true rfl
    ) (
      assume n: ℤ,
      have value.false ≠ value.num n, by contradiction,
      show decidable (value.false = value.num n), from is_false this
    ) (
      assume f x R S e σ, 
      have value.false ≠ value.func f x R S e σ, by contradiction,
      show decidable (value.false = value.func f x R S e σ), from is_false this
    )
   ) (
    assume n₁: ℤ,
    assume : z = value.num n₁,
    show decidable (value.num n₁ = v₂), from
    value.cases_on (λv₂, decidable (value.num n₁ = v₂)) v₂ (
      have value.num n₁ ≠ value.true, by contradiction,
      show decidable (value.num n₁ = value.true), from is_false this
    ) (
      have value.num n₁ ≠ value.false, by contradiction,
      show decidable (value.num n₁ = value.false), from is_false this
    ) (
      assume n₂: ℤ,
      if h: n₁ = n₂ then (
        have value.num n₁ = value.num n₂, from h ▸ rfl,
        show decidable (value.num n₁ = value.num n₂), from is_true this
      ) else (
        have value.num n₁ ≠ value.num n₂, from (
          assume : value.num n₁ = value.num n₂,
          have n₁ = n₂, from value.num.inj this,
          show «false», from h this
        ),
        show decidable (value.num n₁ = value.num n₂), from is_false this
      )
    ) (
      assume f x R S e σ, 
      have value.num n₁ ≠ value.func f x R S e σ, by contradiction,
      show decidable (value.num n₁ = value.func f x R S e σ), from is_false this
    )
  )
  (
    assume f₁ x₁ R₁ S₁ e₁ σ₁, 
    assume : z = value.func f₁ x₁ R₁ S₁ e₁ σ₁,
    have v₁_is_func: v₁ = value.func f₁ x₁ R₁ S₁ e₁ σ₁, from eq.trans h this,
    show decidable (value.func f₁ x₁ R₁ S₁ e₁ σ₁ = v₂), from
    value.cases_on (λv₂, decidable (value.func f₁ x₁ R₁ S₁ e₁ σ₁ = v₂)) v₂ (
      have value.func f₁ x₁ R₁ S₁ e₁ σ₁ ≠ value.true, by contradiction,
      show decidable (value.func f₁ x₁ R₁ S₁ e₁ σ₁ = value.true), from is_false this
    ) (
      have value.func f₁ x₁ R₁ S₁ e₁ σ₁ ≠ value.false, by contradiction,
      show decidable (value.func f₁ x₁ R₁ S₁ e₁ σ₁ = value.false), from is_false this
    ) (
      assume n: ℤ,
      have value.func f₁ x₁ R₁ S₁ e₁ σ₁ ≠ value.num n, by contradiction,
      show decidable (value.func f₁ x₁ R₁ S₁ e₁ σ₁ = value.num n), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂ σ₂,
      have R₁.sizeof < v₁.sizeof, from v₁_is_func.symm ▸ sizeof_value_func_R,
      have decidable (R₁ = R₂), from spec.dec_eq R₁ R₂,
      have S₁.sizeof < v₁.sizeof, from v₁_is_func.symm ▸ sizeof_value_func_S,
      have decidable (S₁ = S₂), from spec.dec_eq S₁ S₂,
      have e₁.sizeof < v₁.sizeof, from v₁_is_func.symm ▸ sizeof_value_func_e,
      have decidable (e₁ = e₂), from exp.dec_eq e₁ e₂,
      have σ₁.sizeof < v₁.sizeof, from v₁_is_func.symm ▸ sizeof_value_func_σ,
      have decidable (σ₁ = σ₂), from env.dec_eq σ₁ σ₂,

      if h: (f₁ = f₂) ∧ (x₁ = x₂) ∧ (R₁ = R₂) ∧ (S₁ = S₂) ∧ (e₁ = e₂) ∧ (σ₁ = σ₂) then (
        have value.func f₁ x₁ R₁ S₁ e₁ σ₁ = value.func f₂ x₂ R₂ S₂ e₂ σ₂,
        from h.left ▸ h.right.left ▸ h.right.right.left ▸ h.right.right.right.left ▸
             h.right.right.right.right.left ▸ h.right.right.right.right.right ▸ rfl,
        show decidable (value.func f₁ x₁ R₁ S₁ e₁ σ₁ = value.func f₂ x₂ R₂ S₂ e₂ σ₂),
        from is_true this
      ) else (
        have value.func f₁ x₁ R₁ S₁ e₁ σ₁ ≠ value.func f₂ x₂ R₂ S₂ e₂ σ₂, from (
          assume : value.func f₁ x₁ R₁ S₁ e₁ σ₁ = value.func f₂ x₂ R₂ S₂ e₂ σ₂,
          show «false», from h (value.func.inj this)
        ),
        show decidable (value.func f₁ x₁ R₁ S₁ e₁ σ₁ = value.func f₂ x₂ R₂ S₂ e₂ σ₂),
        from is_false this
      )
    )
  ) rfl

with exp.dec_eq : ∀ (e₁ e₂: exp), decidable (e₁ = e₂)
| e₁ e₂ :=
  let z := e₁ in
  have h: z = e₁, from rfl,
  exp.cases_on (λe₁, (z = e₁) → decidable (e₁ = e₂)) e₁ (
    assume x₁ e₁',
    assume : z = exp.true x₁ e₁',
    have e₁_is_tru: e₁ = exp.true x₁ e₁', from eq.trans h this,
    show decidable (exp.true x₁ e₁' = e₂),
    from exp.cases_on (λe₂, decidable (exp.true x₁ e₁' = e₂)) e₂ (
      assume x₂ e₂',
      have e₁'.sizeof < e₁.sizeof, from e₁_is_tru.symm ▸ sizeof_exp_true,
      have decidable (e₁' = e₂'), from exp.dec_eq e₁' e₂',
      if h: (x₁ = x₂) ∧ (e₁' = e₂') then (
        have exp.true x₁ e₁' = exp.true x₂ e₂',
        from h.left ▸ h.right ▸ rfl,
        show decidable (exp.true x₁ e₁' = exp.true x₂ e₂'),
        from is_true this
      ) else (
        have exp.true x₁ e₁' ≠ exp.true x₂ e₂', from (
          assume : exp.true x₁ e₁' = exp.true x₂ e₂',
          show «false», from h (exp.true.inj this)
        ),
        show decidable (exp.true x₁ e₁' = exp.true x₂ e₂'),
        from is_false this
      )
    ) (
      assume x₂ e₂',
      have exp.true x₁ e₁' ≠ exp.false x₂ e₂', by contradiction,
      show decidable (exp.true x₁ e₁' = exp.false x₂ e₂'), from is_false this
    ) (
      assume x₂ n₂ e₂',
      have exp.true x₁ e₁' ≠ exp.num x₂ n₂ e₂', by contradiction,
      show decidable (exp.true x₁ e₁' = exp.num x₂ n₂ e₂'), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have exp.true x₁ e₁' ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', by contradiction,
      show decidable (exp.true x₁ e₁' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''), from is_false this
    ) (
      assume x₂ op₂ y₂ e₂',
      have exp.true x₁ e₁' ≠ exp.unop x₂ op₂ y₂ e₂', by contradiction,
      show decidable (exp.true x₁ e₁' = exp.unop x₂ op₂ y₂ e₂'), from is_false this
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have exp.true x₁ e₁' ≠ exp.binop x₂ op₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.true x₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ y₂ z₂ e₂',
      have exp.true x₁ e₁' ≠ exp.app x₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.true x₁ e₁' = exp.app x₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ e₂' e₂'',
      have exp.true x₁ e₁' ≠ exp.ite x₂ e₂' e₂'', by contradiction,
      show decidable (exp.true x₁ e₁' = exp.ite x₂ e₂' e₂''), from is_false this
    ) (
      assume x₂,
      have exp.true x₁ e₁' ≠ exp.return x₂, by contradiction,
      show decidable (exp.true x₁ e₁' = exp.return x₂), from is_false this
    )
  ) (
    assume x₁ e₁',
    assume : z = exp.false x₁ e₁',
    have e₁_is_false: e₁ = exp.false x₁ e₁', from eq.trans h this,
    show decidable (exp.false x₁ e₁' = e₂),
    from exp.cases_on (λe₂, decidable (exp.false x₁ e₁' = e₂)) e₂ (
      assume x₂ e₂',
      have exp.false x₁ e₁' ≠ exp.true x₂ e₂', by contradiction,
      show decidable (exp.false x₁ e₁' = exp.true x₂ e₂'), from is_false this
    ) (
      assume x₂ e₂',
      have e₁'.sizeof < e₁.sizeof, from e₁_is_false.symm ▸ sizeof_exp_false,
      have decidable (e₁' = e₂'), from exp.dec_eq e₁' e₂',
      if h: (x₁ = x₂) ∧ (e₁' = e₂') then (
        have exp.false x₁ e₁' = exp.false x₂ e₂',
        from h.left ▸ h.right ▸ rfl,
        show decidable (exp.false x₁ e₁' = exp.false x₂ e₂'),
        from is_true this
      ) else (
        have exp.false x₁ e₁' ≠ exp.false x₂ e₂', from (
          assume : exp.false x₁ e₁' = exp.false x₂ e₂',
          show «false», from h (exp.false.inj this)
        ),
        show decidable (exp.false x₁ e₁' = exp.false x₂ e₂'),
        from is_false this
      )
    ) (
      assume x₂ n₂ e₂',
      have exp.false x₁ e₁' ≠ exp.num x₂ n₂ e₂', by contradiction,
      show decidable (exp.false x₁ e₁' = exp.num x₂ n₂ e₂'), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have exp.false x₁ e₁' ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', by contradiction,
      show decidable (exp.false x₁ e₁' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''), from is_false this
    ) (
      assume x₂ op₂ y₂ e₂',
      have exp.false x₁ e₁' ≠ exp.unop x₂ op₂ y₂ e₂', by contradiction,
      show decidable (exp.false x₁ e₁' = exp.unop x₂ op₂ y₂ e₂'), from is_false this
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have exp.false x₁ e₁' ≠ exp.binop x₂ op₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.false x₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ y₂ z₂ e₂',
      have exp.false x₁ e₁' ≠ exp.app x₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.false x₁ e₁' = exp.app x₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ e₂' e₂'',
      have exp.false x₁ e₁' ≠ exp.ite x₂ e₂' e₂'', by contradiction,
      show decidable (exp.false x₁ e₁' = exp.ite x₂ e₂' e₂''), from is_false this
    ) (
      assume x₂,
      have exp.false x₁ e₁' ≠ exp.return x₂, by contradiction,
      show decidable (exp.false x₁ e₁' = exp.return x₂), from is_false this
    )
  ) (
    assume x₁ n₁ e₁',
    assume : z = exp.num x₁ n₁ e₁',
    have e₁_is_num: e₁ = exp.num x₁ n₁ e₁', from eq.trans h this,
    show decidable (exp.num x₁ n₁ e₁' = e₂),
    from exp.cases_on (λe₂, decidable (exp.num x₁ n₁ e₁' = e₂)) e₂ (
      assume x₂ e₂',
      have exp.num x₁ n₁ e₁' ≠ exp.true x₂ e₂', by contradiction,
      show decidable (exp.num x₁ n₁ e₁' = exp.true x₂ e₂'), from is_false this
    ) (
      assume x₂ e₂',
      have exp.num x₁ n₁ e₁' ≠ exp.false x₂ e₂', by contradiction,
      show decidable (exp.num x₁ n₁ e₁' = exp.false x₂ e₂'), from is_false this
    ) (
      assume x₂ n₂ e₂',
      have e₁'.sizeof < e₁.sizeof, from e₁_is_num.symm ▸ sizeof_exp_num,
      have decidable (e₁' = e₂'), from exp.dec_eq e₁' e₂',
      if h: (x₁ = x₂) ∧ (n₁ = n₂) ∧ (e₁' = e₂') then (
        have exp.num x₁ n₁ e₁' = exp.num x₂ n₂ e₂',
        from h.left ▸ h.right.left ▸ h.right.right ▸ rfl,
        show decidable (exp.num x₁ n₁ e₁' = exp.num x₂ n₂ e₂'),
        from is_true this
      ) else (
        have exp.num x₁ n₁ e₁' ≠ exp.num x₂ n₂ e₂', from (
          assume : exp.num x₁ n₁ e₁' = exp.num x₂ n₂ e₂',
          show «false», from h (exp.num.inj this)
        ),
        show decidable (exp.num x₁ n₁ e₁' = exp.num x₂ n₂ e₂'),
        from is_false this
      )
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have exp.num x₁ n₁ e₁' ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', by contradiction,
      show decidable (exp.num x₁ n₁ e₁' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''), from is_false this
    ) (
      assume x₂ op₂ y₂ e₂',
      have exp.num x₁ n₁ e₁' ≠ exp.unop x₂ op₂ y₂ e₂', by contradiction,
      show decidable (exp.num x₁ n₁ e₁' = exp.unop x₂ op₂ y₂ e₂'), from is_false this
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have exp.num x₁ n₁ e₁' ≠ exp.binop x₂ op₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.num x₁ n₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ y₂ z₂ e₂',
      have exp.num x₁ n₁ e₁' ≠ exp.app x₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.num x₁ n₁ e₁' = exp.app x₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ e₂' e₂'',
      have exp.num x₁ n₁ e₁' ≠ exp.ite x₂ e₂' e₂'', by contradiction,
      show decidable (exp.num x₁ n₁ e₁' = exp.ite x₂ e₂' e₂''), from is_false this
    ) (
      assume x₂,
      have exp.num x₁ n₁ e₁' ≠ exp.return x₂, by contradiction,
      show decidable (exp.num x₁ n₁ e₁' = exp.return x₂), from is_false this
    )
  ) (
    assume f₁ x₁ R₁ S₁ e₁' e₁'',
    assume : z = exp.func f₁ x₁ R₁ S₁ e₁' e₁'',
    have e₁_is_func: e₁ = exp.func f₁ x₁ R₁ S₁ e₁' e₁'', from eq.trans h this,
    show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = e₂),
    from exp.cases_on (λe₂, decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = e₂)) e₂ (
      assume x₂ e₂',
      have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.true x₂ e₂', by contradiction,
      show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.true x₂ e₂'), from is_false this
    ) (
      assume x₂ e₂',
      have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.false x₂ e₂', by contradiction,
      show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.false x₂ e₂'), from is_false this
    ) (
      assume x₂ n₂ e₂',
      have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.num x₂ n₂ e₂', by contradiction,
      show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.num x₂ n₂ e₂'), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have R₁.sizeof < e₁.sizeof, from e₁_is_func.symm ▸ sizeof_exp_func_R,
      have decidable (R₁ = R₂), from spec.dec_eq R₁ R₂,
      have S₁.sizeof < e₁.sizeof, from e₁_is_func.symm ▸ sizeof_exp_func_S,
      have decidable (S₁ = S₂), from spec.dec_eq S₁ S₂,
      have e₁'.sizeof < e₁.sizeof, from e₁_is_func.symm ▸ sizeof_exp_func_e₁,
      have decidable (e₁' = e₂'), from exp.dec_eq e₁' e₂',
      have e₁''.sizeof < e₁.sizeof, from e₁_is_func.symm ▸ sizeof_exp_func_e₂,
      have decidable (e₁'' = e₂''), from exp.dec_eq e₁'' e₂'',

      if h: (f₁ = f₂) ∧ (x₁ = x₂) ∧ (R₁ = R₂) ∧ (S₁ = S₂) ∧ (e₁' = e₂') ∧ (e₁'' = e₂'') then (
        have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.func f₂ x₂ R₂ S₂ e₂' e₂'',
        from h.left ▸ h.right.left ▸ h.right.right.left ▸ h.right.right.right.left ▸
             h.right.right.right.right.left ▸ h.right.right.right.right.right ▸ rfl,
        show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''),
        from is_true this
      ) else (
        have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', from (
          assume : exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.func f₂ x₂ R₂ S₂ e₂' e₂'',
          show «false», from h (exp.func.inj this)
        ),
        show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''),
        from is_false this
      )
    ) (
      assume x₂ op₂ y₂ e₂',
      have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.unop x₂ op₂ y₂ e₂', by contradiction,
      show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.unop x₂ op₂ y₂ e₂'), from is_false this
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.binop x₂ op₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.binop x₂ op₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ y₂ z₂ e₂',
      have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.app x₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.app x₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ e₂' e₂'',
      have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.ite x₂ e₂' e₂'', by contradiction,
      show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.ite x₂ e₂' e₂''), from is_false this
    ) (
      assume x₂,
      have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.return x₂, by contradiction,
      show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.return x₂), from is_false this
    )
  ) (
    assume x₁ op₁ y₁ e₁',
    assume : z = exp.unop x₁ op₁ y₁ e₁',
    have e₁_is_unop: e₁ = exp.unop x₁ op₁ y₁ e₁', from eq.trans h this,
    show decidable (exp.unop x₁ op₁ y₁ e₁' = e₂),
    from exp.cases_on (λe₂, decidable (exp.unop x₁ op₁ y₁ e₁' = e₂)) e₂ (
      assume x₂ e₂',
      have exp.unop x₁ op₁ y₁ e₁' ≠ exp.true x₂ e₂', by contradiction,
      show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.true x₂ e₂'), from is_false this
    ) (
      assume x₂ e₂',
      have exp.unop x₁ op₁ y₁ e₁' ≠ exp.false x₂ e₂', by contradiction,
      show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.false x₂ e₂'), from is_false this
    ) (
      assume x₂ n₂ e₂',
      have exp.unop x₁ op₁ y₁ e₁' ≠ exp.num x₂ n₂ e₂', by contradiction,
      show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.num x₂ n₂ e₂'), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have exp.unop x₁ op₁ y₁ e₁' ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', by contradiction,
      show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''), from is_false this
    ) (
      assume x₂ op₂ y₂ e₂',
      have e₁'.sizeof < e₁.sizeof, from e₁_is_unop.symm ▸ sizeof_exp_unop,
      have decidable (e₁' = e₂'), from exp.dec_eq e₁' e₂',
      if h: (x₁ = x₂) ∧ (op₁ = op₂) ∧ (y₁ = y₂) ∧ (e₁' = e₂') then (
        have exp.unop x₁ op₁ y₁ e₁' = exp.unop x₂ op₂ y₂ e₂',
        from h.left ▸ h.right.left ▸ h.right.right.left ▸ h.right.right.right ▸ rfl,
        show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.unop x₂ op₂ y₂ e₂'),
        from is_true this
      ) else (
        have exp.unop x₁ op₁ y₁ e₁' ≠ exp.unop x₂ op₂ y₂ e₂', from (
          assume : exp.unop x₁ op₁ y₁ e₁' = exp.unop x₂ op₂ y₂ e₂',
          show «false», from h (exp.unop.inj this)
        ),
        show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.unop x₂ op₂ y₂ e₂'),
        from is_false this
      )
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have exp.unop x₁ op₁ y₁ e₁' ≠ exp.binop x₂ op₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ y₂ z₂ e₂',
      have exp.unop x₁ op₁ y₁ e₁' ≠ exp.app x₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.app x₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ e₂' e₂'',
      have exp.unop x₁ op₁ y₁ e₁' ≠ exp.ite x₂ e₂' e₂'', by contradiction,
      show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.ite x₂ e₂' e₂''), from is_false this
    ) (
      assume x₂,
      have exp.unop x₁ op₁ y₁ e₁' ≠ exp.return x₂, by contradiction,
      show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.return x₂), from is_false this
    )
  ) (
    assume x₁ op₁ y₁ z₁ e₁',
    assume : z = exp.binop x₁ op₁ y₁ z₁ e₁',
    have e₁_is_binop: e₁ = exp.binop x₁ op₁ y₁ z₁ e₁', from eq.trans h this,
    show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = e₂),
    from exp.cases_on (λe₂, decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = e₂)) e₂ (
      assume x₂ e₂',
      have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.true x₂ e₂', by contradiction,
      show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.true x₂ e₂'), from is_false this
    ) (
      assume x₂ e₂',
      have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.false x₂ e₂', by contradiction,
      show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.false x₂ e₂'), from is_false this
    ) (
      assume x₂ n₂ e₂',
      have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.num x₂ n₂ e₂', by contradiction,
      show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.num x₂ n₂ e₂'), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', by contradiction,
      show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''), from is_false this
    ) (
      assume x₂ op₂ y₂ e₂',
      have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.unop x₂ op₂ y₂ e₂', by contradiction,
      show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.unop x₂ op₂ y₂ e₂'), from is_false this
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have e₁'.sizeof < e₁.sizeof, from e₁_is_binop.symm ▸ sizeof_exp_binop,
      have decidable (e₁' = e₂'), from exp.dec_eq e₁' e₂',
      if h: (x₁ = x₂) ∧ (op₁ = op₂) ∧ (y₁ = y₂) ∧ (z₁ = z₂) ∧ (e₁' = e₂') then (
        have exp.binop x₁ op₁ y₁ z₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂',
        from h.left ▸ h.right.left ▸ h.right.right.left ▸ h.right.right.right.left ▸
             h.right.right.right.right ▸ rfl,
        show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂'),
        from is_true this
      ) else (
        have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.binop x₂ op₂ y₂ z₂ e₂', from (
          assume : exp.binop x₁ op₁ y₁ z₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂',
          show «false», from h (exp.binop.inj this)
        ),
        show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂'),
        from is_false this
      )
    ) (
      assume x₂ y₂ z₂ e₂',
      have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.app x₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.app x₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ e₂' e₂'',
      have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.ite x₂ e₂' e₂'', by contradiction,
      show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.ite x₂ e₂' e₂''), from is_false this
    ) (
      assume x₂,
      have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.return x₂, by contradiction,
      show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.return x₂), from is_false this
    )
  ) (
    assume x₁ y₁ z₁ e₁',
    assume : z = exp.app x₁ y₁ z₁ e₁',
    have e₁_is_app: e₁ = exp.app x₁ y₁ z₁ e₁', from eq.trans h this,
    show decidable (exp.app x₁ y₁ z₁ e₁' = e₂),
    from exp.cases_on (λe₂, decidable (exp.app x₁ y₁ z₁ e₁' = e₂)) e₂ (
      assume x₂ e₂',
      have exp.app x₁ y₁ z₁ e₁' ≠ exp.true x₂ e₂', by contradiction,
      show decidable (exp.app x₁ y₁ z₁ e₁' = exp.true x₂ e₂'), from is_false this
    ) (
      assume x₂ e₂',
      have exp.app x₁ y₁ z₁ e₁' ≠ exp.false x₂ e₂', by contradiction,
      show decidable (exp.app x₁ y₁ z₁ e₁' = exp.false x₂ e₂'), from is_false this
    ) (
      assume x₂ n₂ e₂',
      have exp.app x₁ y₁ z₁ e₁' ≠ exp.num x₂ n₂ e₂', by contradiction,
      show decidable (exp.app x₁ y₁ z₁ e₁' = exp.num x₂ n₂ e₂'), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have exp.app x₁ y₁ z₁ e₁' ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', by contradiction,
      show decidable (exp.app x₁ y₁ z₁ e₁' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''), from is_false this
    ) (
      assume x₂ op₂ y₂ e₂',
      have exp.app x₁ y₁ z₁ e₁' ≠ exp.unop x₂ op₂ y₂ e₂', by contradiction,
      show decidable (exp.app x₁ y₁ z₁ e₁' = exp.unop x₂ op₂ y₂ e₂'), from is_false this
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have exp.app x₁ y₁ z₁ e₁' ≠ exp.binop x₂ op₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.app x₁ y₁ z₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ y₂ z₂ e₂',
      have e₁'.sizeof < e₁.sizeof, from e₁_is_app.symm ▸ sizeof_exp_app,
      have decidable (e₁' = e₂'), from exp.dec_eq e₁' e₂',
      if h: (x₁ = x₂) ∧ (y₁ = y₂) ∧ (z₁ = z₂) ∧ (e₁' = e₂') then (
        have exp.app x₁ y₁ z₁ e₁' = exp.app x₂ y₂ z₂ e₂',
        from h.left ▸ h.right.left ▸ h.right.right.left ▸ h.right.right.right ▸ rfl,
        show decidable (exp.app x₁ y₁ z₁ e₁' = exp.app x₂ y₂ z₂ e₂'),
        from is_true this
      ) else (
        have exp.app x₁ y₁ z₁ e₁' ≠ exp.app x₂ y₂ z₂ e₂', from (
          assume : exp.app x₁ y₁ z₁ e₁' = exp.app x₂ y₂ z₂ e₂',
          show «false», from h (exp.app.inj this)
        ),
        show decidable (exp.app x₁ y₁ z₁ e₁' = exp.app x₂ y₂ z₂ e₂'),
        from is_false this
      )
    ) (
      assume x₂ e₂' e₂'',
      have exp.app x₁ y₁ z₁ e₁' ≠ exp.ite x₂ e₂' e₂'', by contradiction,
      show decidable (exp.app x₁ y₁ z₁ e₁' = exp.ite x₂ e₂' e₂''), from is_false this
    ) (
      assume x₂,
      have exp.app x₁ y₁ z₁ e₁' ≠ exp.return x₂, by contradiction,
      show decidable (exp.app x₁ y₁ z₁ e₁' = exp.return x₂), from is_false this
    )
  ) (
    assume x₁ e₁' e₁'',
    assume : z = exp.ite x₁ e₁' e₁'',
    have e₁_is_ite: e₁ = exp.ite x₁ e₁' e₁'', from eq.trans h this,
    show decidable (exp.ite x₁ e₁' e₁'' = e₂),
    from exp.cases_on (λe₂, decidable (exp.ite x₁ e₁' e₁'' = e₂)) e₂ (
      assume x₂ e₂',
      have exp.ite x₁ e₁' e₁'' ≠ exp.true x₂ e₂', by contradiction,
      show decidable (exp.ite x₁ e₁' e₁'' = exp.true x₂ e₂'), from is_false this
    ) (
      assume x₂ e₂',
      have exp.ite x₁ e₁' e₁'' ≠ exp.false x₂ e₂', by contradiction,
      show decidable (exp.ite x₁ e₁' e₁'' = exp.false x₂ e₂'), from is_false this
    ) (
      assume x₂ n₂ e₂',
      have exp.ite x₁ e₁' e₁'' ≠ exp.num x₂ n₂ e₂', by contradiction,
      show decidable (exp.ite x₁ e₁' e₁'' = exp.num x₂ n₂ e₂'), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have exp.ite x₁ e₁' e₁'' ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', by contradiction,
      show decidable (exp.ite x₁ e₁' e₁'' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''), from is_false this
    ) (
      assume x₂ op₂ y₂ e₂',
      have exp.ite x₁ e₁' e₁'' ≠ exp.unop x₂ op₂ y₂ e₂', by contradiction,
      show decidable (exp.ite x₁ e₁' e₁'' = exp.unop x₂ op₂ y₂ e₂'), from is_false this
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have exp.ite x₁ e₁' e₁'' ≠ exp.binop x₂ op₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.ite x₁ e₁' e₁'' = exp.binop x₂ op₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ y₂ z₂ e₂',
      have exp.ite x₁ e₁' e₁'' ≠ exp.app x₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.ite x₁ e₁' e₁'' = exp.app x₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ e₂' e₂'',
      have e₁'.sizeof < e₁.sizeof, from e₁_is_ite.symm ▸ sizeof_exp_ite_e₁,
      have decidable (e₁' = e₂'), from exp.dec_eq e₁' e₂',
      have e₁''.sizeof < e₁.sizeof, from e₁_is_ite.symm ▸ sizeof_exp_ite_e₂,
      have decidable (e₁'' = e₂''), from exp.dec_eq e₁'' e₂'',
      if h: (x₁ = x₂) ∧ (e₁' = e₂') ∧ (e₁'' = e₂'') then (
        have exp.ite x₁ e₁' e₁'' = exp.ite x₂ e₂' e₂'',
        from h.left ▸ h.right.left ▸ h.right.right ▸ rfl,
        show decidable (exp.ite x₁ e₁' e₁'' = exp.ite x₂ e₂' e₂''),
        from is_true this
      ) else (
        have exp.ite x₁ e₁' e₁'' ≠ exp.ite x₂ e₂' e₂'', from (
          assume : exp.ite x₁ e₁' e₁'' = exp.ite x₂ e₂' e₂'',
          show «false», from h (exp.ite.inj this)
        ),
        show decidable (exp.ite x₁ e₁' e₁'' = exp.ite x₂ e₂' e₂''),
        from is_false this
      )
    ) (
      assume x₂,
      have exp.ite x₁ e₁' e₁'' ≠ exp.return x₂, by contradiction,
      show decidable (exp.ite x₁ e₁' e₁'' = exp.return x₂), from is_false this
    )
  ) (
    assume x₁,
    assume : z = exp.return x₁,
    have e₁_is_tru: e₁ = exp.return x₁, from eq.trans h this,
    show decidable (exp.return x₁ = e₂),
    from exp.cases_on (λe₂, decidable (exp.return x₁ = e₂)) e₂ (
      assume x₂ e₂',
      have exp.return x₁ ≠ exp.true x₂ e₂', by contradiction,
      show decidable (exp.return x₁ = exp.true x₂ e₂'), from is_false this
    ) (
      assume x₂ e₂',
      have exp.return x₁ ≠ exp.false x₂ e₂', by contradiction,
      show decidable (exp.return x₁ = exp.false x₂ e₂'), from is_false this
    ) (
      assume x₂ n₂ e₂',
      have exp.return x₁ ≠ exp.num x₂ n₂ e₂', by contradiction,
      show decidable (exp.return x₁ = exp.num x₂ n₂ e₂'), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have exp.return x₁ ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', by contradiction,
      show decidable (exp.return x₁ = exp.func f₂ x₂ R₂ S₂ e₂' e₂''), from is_false this
    ) (
      assume x₂ op₂ y₂ e₂',
      have exp.return x₁ ≠ exp.unop x₂ op₂ y₂ e₂', by contradiction,
      show decidable (exp.return x₁ = exp.unop x₂ op₂ y₂ e₂'), from is_false this
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have exp.return x₁ ≠ exp.binop x₂ op₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.return x₁ = exp.binop x₂ op₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ y₂ z₂ e₂',
      have exp.return x₁ ≠ exp.app x₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.return x₁ = exp.app x₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ e₂' e₂'',
      have exp.return x₁ ≠ exp.ite x₂ e₂' e₂'', by contradiction,
      show decidable (exp.return x₁ = exp.ite x₂ e₂' e₂''), from is_false this
    ) (
      assume x₂,
      if h: x₁ = x₂ then (
        have exp.return x₁ = exp.return x₂, from h ▸ rfl,
        show decidable (exp.return x₁ = exp.return x₂),
        from is_true this
      ) else (
        have exp.return x₁ ≠ exp.return x₂, from (
          assume : exp.return x₁ = exp.return x₂,
          show «false», from h (exp.return.inj this)
        ),
        show decidable (exp.return x₁ = exp.return x₂),
        from is_false this
      )
    )
  ) rfl

with term.dec_eq : ∀ (t₁ t₂: term), decidable (t₁ = t₂)
| t₁ t₂ :=
  let z := t₁ in
  have h: z = t₁, from rfl,
  term.cases_on (λt₁, (z = t₁) → decidable (t₁ = t₂)) t₁ (
    assume v₁,
    assume : z = term.value v₁,
    have t₁_id: t₁ = term.value v₁, from eq.trans h this,
    show decidable (term.value v₁ = t₂),
    from term.cases_on (λt₂, decidable (term.value v₁ = t₂)) t₂ (
      assume v₂,
      have v₁.sizeof < t₁.sizeof, from t₁_id.symm ▸ sizeof_term_value,
      have decidable (v₁ = v₂), from value.dec_eq v₁ v₂,
      if h: v₁ = v₂ then (
        have term.value v₁ = term.value v₂, from h ▸ rfl,
        show decidable (term.value v₁ = term.value v₂),
        from is_true this
      ) else (
        have term.value v₁ ≠ term.value v₂, from (
          assume : term.value v₁ = term.value v₂,
          show «false», from h (term.value.inj this)
        ),
        show decidable (term.value v₁ = term.value v₂),
        from is_false this
      )
    ) (
      assume x₂,
      have term.value v₁ ≠ term.var x₂, by contradiction,
      show decidable (term.value v₁ = term.var x₂), from is_false this
    ) (
      assume op₂ t₂',
      have term.value v₁ ≠ term.unop op₂ t₂', by contradiction,
      show decidable (term.value v₁ = term.unop op₂ t₂'), from is_false this
    ) (
      assume op₂ t₂' t₂'',
      have term.value v₁ ≠ term.binop op₂ t₂' t₂'', by contradiction,
      show decidable (term.value v₁ = term.binop op₂ t₂' t₂''), from is_false this
    ) (
      assume t₂' t₂'',
      have term.value v₁ ≠ term.app t₂' t₂'', by contradiction,
      show decidable (term.value v₁ = term.app t₂' t₂''), from is_false this
    )
  ) (
    assume x₁,
    assume : z = term.var x₁,
    have t₁_id: t₁ = term.var x₁, from eq.trans h this,
    show decidable (term.var x₁ = t₂),
    from term.cases_on (λt₂, decidable (term.var x₁ = t₂)) t₂ (
      assume v₂,
      have term.var x₁ ≠ term.value v₂, by contradiction,
      show decidable (term.var x₁ = term.value v₂), from is_false this
    ) (
      assume x₂,
      if h: x₁ = x₂ then (
        have term.var x₁ = term.var x₂, from h ▸ rfl,
        show decidable (term.var x₁ = term.var x₂),
        from is_true this
      ) else (
        have term.var x₁ ≠ term.var x₂, from (
          assume : term.var x₁ = term.var x₂,
          show «false», from h (term.var.inj this)
        ),
        show decidable (term.var x₁ = term.var x₂),
        from is_false this
      )
    ) (
      assume op₂ t₂',
      have term.var x₁ ≠ term.unop op₂ t₂', by contradiction,
      show decidable (term.var x₁ = term.unop op₂ t₂'), from is_false this
    ) (
      assume op₂ t₂' t₂'',
      have term.var x₁ ≠ term.binop op₂ t₂' t₂'', by contradiction,
      show decidable (term.var x₁ = term.binop op₂ t₂' t₂''), from is_false this
    ) (
      assume t₂' t₂'',
      have term.var x₁ ≠ term.app t₂' t₂'', by contradiction,
      show decidable (term.var x₁ = term.app t₂' t₂''), from is_false this
    )
  ) (
    assume op₁ t₁',
    assume : z = term.unop op₁ t₁',
    have t₁_id: t₁ = term.unop op₁ t₁', from eq.trans h this,
    show decidable (term.unop op₁ t₁' = t₂),
    from term.cases_on (λt₂, decidable (term.unop op₁ t₁' = t₂)) t₂ (
      assume v₂,
      have term.unop op₁ t₁' ≠ term.value v₂, by contradiction,
      show decidable (term.unop op₁ t₁' = term.value v₂), from is_false this
    ) (
      assume x₂,
      have term.unop op₁ t₁' ≠ term.var x₂, by contradiction,
      show decidable (term.unop op₁ t₁' = term.var x₂), from is_false this
    ) (
      assume op₂ t₂',
      have t₁'.sizeof < t₁.sizeof, from t₁_id.symm ▸ sizeof_term_unop,
      have decidable (t₁' = t₂'), from term.dec_eq t₁' t₂',
      if h: (op₁ = op₂) ∧ (t₁' = t₂') then (
        have term.unop op₁ t₁' = term.unop op₂ t₂',
        from h.left ▸ h.right ▸ rfl,
        show decidable (term.unop op₁ t₁' = term.unop op₂ t₂'),
        from is_true this
      ) else (
        have term.unop op₁ t₁' ≠ term.unop op₂ t₂', from (
          assume : term.unop op₁ t₁' = term.unop op₂ t₂',
          show «false», from h (term.unop.inj this)
        ),
        show decidable (term.unop op₁ t₁' = term.unop op₂ t₂'),
        from is_false this
      )
    ) (
      assume op₂ t₂' t₂'',
      have term.unop op₁ t₁' ≠ term.binop op₂ t₂' t₂'', by contradiction,
      show decidable (term.unop op₁ t₁' = term.binop op₂ t₂' t₂''), from is_false this
    ) (
      assume t₂' t₂'',
      have term.unop op₁ t₁' ≠ term.app t₂' t₂'', by contradiction,
      show decidable (term.unop op₁ t₁' = term.app t₂' t₂''), from is_false this
    )
  ) (
    assume op₁ t₁' t₁'',
    assume : z = term.binop op₁ t₁' t₁'',
    have t₁_id: t₁ = term.binop op₁ t₁' t₁'', from eq.trans h this,
    show decidable (term.binop op₁ t₁' t₁'' = t₂),
    from term.cases_on (λt₂, decidable (term.binop op₁ t₁' t₁'' = t₂)) t₂ (
      assume v₂,
      have term.binop op₁ t₁' t₁'' ≠ term.value v₂, by contradiction,
      show decidable (term.binop op₁ t₁' t₁'' = term.value v₂), from is_false this
    ) (
      assume x₂,
      have term.binop op₁ t₁' t₁'' ≠ term.var x₂, by contradiction,
      show decidable (term.binop op₁ t₁' t₁'' = term.var x₂), from is_false this
    ) (
      assume op₂ t₂',
      have term.binop op₁ t₁' t₁'' ≠ term.unop op₂ t₂', by contradiction,
      show decidable (term.binop op₁ t₁' t₁'' = term.unop op₂ t₂'), from is_false this
    ) (
      assume op₂ t₂' t₂'',
      have t₁'.sizeof < t₁.sizeof, from t₁_id.symm ▸ sizeof_term_binop₁,
      have decidable (t₁' = t₂'), from term.dec_eq t₁' t₂',
      have t₁''.sizeof < t₁.sizeof, from t₁_id.symm ▸ sizeof_term_binop₂,
      have decidable (t₁'' = t₂''), from term.dec_eq t₁'' t₂'',
      if h: (op₁ = op₂) ∧ (t₁' = t₂') ∧ (t₁'' = t₂'') then (
        have term.binop op₁ t₁' t₁'' = term.binop op₂ t₂' t₂'',
        from h.left ▸ h.right.left ▸ h.right.right ▸ rfl,
        show decidable (term.binop op₁ t₁' t₁'' = term.binop op₂ t₂' t₂''),
        from is_true this
      ) else (
        have term.binop op₁ t₁' t₁'' ≠ term.binop op₂ t₂' t₂'', from (
          assume : term.binop op₁ t₁' t₁'' = term.binop op₂ t₂' t₂'',
          show «false», from h (term.binop.inj this)
        ),
        show decidable (term.binop op₁ t₁' t₁'' = term.binop op₂ t₂' t₂''),
        from is_false this
      )
    ) (
      assume t₂' t₂'',
      have term.binop op₁ t₁' t₁'' ≠ term.app t₂' t₂'', by contradiction,
      show decidable (term.binop op₁ t₁' t₁'' = term.app t₂' t₂''), from is_false this
    )
  ) (
    assume t₁' t₁'',
    assume : z = term.app t₁' t₁'',
    have t₁_id: t₁ = term.app t₁' t₁'', from eq.trans h this,
    show decidable (term.app t₁' t₁'' = t₂),
    from term.cases_on (λt₂, decidable (term.app t₁' t₁'' = t₂)) t₂ (
      assume v₂,
      have term.app t₁' t₁'' ≠ term.value v₂, by contradiction,
      show decidable (term.app t₁' t₁'' = term.value v₂), from is_false this
    ) (
      assume x₂,
      have term.app t₁' t₁'' ≠ term.var x₂, by contradiction,
      show decidable (term.app t₁' t₁'' = term.var x₂), from is_false this
    ) (
      assume op₂ t₂',
      have term.app t₁' t₁'' ≠ term.unop op₂ t₂', by contradiction,
      show decidable (term.app t₁' t₁'' = term.unop op₂ t₂'), from is_false this
    ) (
      assume op₂ t₂' t₂'',
      have term.app t₁' t₁'' ≠ term.binop op₂ t₂' t₂'', by contradiction,
      show decidable (term.app t₁' t₁'' = term.binop op₂ t₂' t₂''), from is_false this
    ) (
      assume t₂' t₂'',
      have t₁'.sizeof < t₁.sizeof, from t₁_id.symm ▸ sizeof_term_app₁,
      have decidable (t₁' = t₂'), from term.dec_eq t₁' t₂',
      have t₁''.sizeof < t₁.sizeof, from t₁_id.symm ▸ sizeof_term_app₂,
      have decidable (t₁'' = t₂''), from term.dec_eq t₁'' t₂'',
      if h: (t₁' = t₂') ∧ (t₁'' = t₂'') then (
        have term.app t₁' t₁'' = term.app t₂' t₂'',
        from h.left ▸ h.right ▸ rfl,
        show decidable (term.app t₁' t₁'' = term.app t₂' t₂''),
        from is_true this
      ) else (
        have term.app t₁' t₁'' ≠ term.app t₂' t₂'', from (
          assume : term.app t₁' t₁'' = term.app t₂' t₂'',
          show «false», from h (term.app.inj this)
        ),
        show decidable (term.app t₁' t₁'' = term.app t₂' t₂''),
        from is_false this
      )
    )
  ) rfl

with spec.dec_eq : ∀ (R₁ R₂: spec), decidable (R₁ = R₂)
| R₁ R₂ :=
  let z := R₁ in
  have h: z = R₁, from rfl,
  spec.cases_on (λR₁, (z = R₁) → decidable (R₁ = R₂)) R₁ (
    assume t₁,
    assume : z = spec.term t₁,
    have R₁_id: R₁ = spec.term t₁, from eq.trans h this,
    show decidable (spec.term t₁ = R₂),
    from spec.cases_on (λR₂, decidable (spec.term t₁ = R₂)) R₂ (
      assume t₂,
      have t₁.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_term,
      have decidable (t₁ = t₂), from term.dec_eq t₁ t₂,
      if h: t₁ = t₂ then (
        have spec.term t₁ = spec.term t₂, from h ▸ rfl,
        show decidable (spec.term t₁ = spec.term t₂),
        from is_true this
      ) else (
        have spec.term t₁ ≠ spec.term t₂, from (
          assume : spec.term t₁ = spec.term t₂,
          show «false», from h (spec.term.inj this)
        ),
        show decidable (spec.term t₁ = spec.term t₂),
        from is_false this
      )
    ) (
      assume S₂,
      have spec.term t₁ ≠ spec.not S₂, by contradiction,
      show decidable (spec.term t₁ = spec.not S₂), from is_false this
    ) (
      assume S₂ S₂',
      have spec.term t₁ ≠ spec.and S₂ S₂', by contradiction,
      show decidable (spec.term t₁ = spec.and S₂ S₂'), from is_false this
    ) (
      assume S₂ S₂',
      have spec.term t₁ ≠ spec.or S₂ S₂', by contradiction,
      show decidable (spec.term t₁ = spec.or S₂ S₂'), from is_false this
    ) (
      assume t₂ x₂ S₂ S₂',
      have spec.term t₁ ≠ spec.func t₂ x₂ S₂ S₂', by contradiction,
      show decidable (spec.term t₁ = spec.func t₂ x₂ S₂ S₂'), from is_false this
    )
  ) (
    assume S₁,
    assume : z = spec.not S₁,
    have R₁_id: R₁ = spec.not S₁, from eq.trans h this,
    show decidable (spec.not S₁ = R₂),
    from spec.cases_on (λR₂, decidable (spec.not S₁ = R₂)) R₂ (
      assume t₂,
      have spec.not S₁ ≠ spec.term t₂, by contradiction,
      show decidable (spec.not S₁ = spec.term t₂), from is_false this
    ) (
      assume S₂,
      have S₁.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_not,
      have decidable (S₁ = S₂), from spec.dec_eq S₁ S₂,
      if h: S₁ = S₂ then (
        have spec.not S₁ = spec.not S₂, from h ▸ rfl,
        show decidable (spec.not S₁ = spec.not S₂),
        from is_true this
      ) else (
        have spec.not S₁ ≠ spec.not S₂, from (
          assume : spec.not S₁ = spec.not S₂,
          show «false», from h (spec.not.inj this)
        ),
        show decidable (spec.not S₁ = spec.not S₂),
        from is_false this
      )
    ) (
      assume S₂ S₂',
      have spec.not S₁ ≠ spec.and S₂ S₂', by contradiction,
      show decidable (spec.not S₁ = spec.and S₂ S₂'), from is_false this
    ) (
      assume S₂ S₂',
      have spec.not S₁ ≠ spec.or S₂ S₂', by contradiction,
      show decidable (spec.not S₁ = spec.or S₂ S₂'), from is_false this
    ) (
      assume t₂ x₂ S₂ S₂',
      have spec.not S₁ ≠ spec.func t₂ x₂ S₂ S₂', by contradiction,
      show decidable (spec.not S₁ = spec.func t₂ x₂ S₂ S₂'), from is_false this
    )
  ) (
    assume S₁ S₁',
    assume : z = spec.and S₁ S₁',
    have R₁_id: R₁ = spec.and S₁ S₁', from eq.trans h this,
    show decidable (spec.and S₁ S₁' = R₂),
    from spec.cases_on (λR₂, decidable (spec.and S₁ S₁' = R₂)) R₂ (
      assume t₂,
      have spec.and S₁ S₁' ≠ spec.term t₂, by contradiction,
      show decidable (spec.and S₁ S₁' = spec.term t₂), from is_false this
    ) (
      assume S₂,
      have spec.and S₁ S₁' ≠ spec.not S₂, by contradiction,
      show decidable (spec.and S₁ S₁' = spec.not S₂), from is_false this
    ) (
      assume S₂ S₂',
      have S₁.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_and₁,
      have decidable (S₁ = S₂), from spec.dec_eq S₁ S₂,
      have S₁'.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_and₂,
      have decidable (S₁' = S₂'), from spec.dec_eq S₁' S₂',
      if h: (S₁ = S₂) ∧ (S₁' = S₂') then (
        have spec.and S₁ S₁' = spec.and S₂ S₂',
        from h.left ▸ h.right ▸ rfl,
        show decidable (spec.and S₁ S₁' = spec.and S₂ S₂'),
        from is_true this
      ) else (
        have spec.and S₁ S₁' ≠ spec.and S₂ S₂', from (
          assume : spec.and S₁ S₁' = spec.and S₂ S₂',
          show «false», from h (spec.and.inj this)
        ),
        show decidable (spec.and S₁ S₁' = spec.and S₂ S₂'),
        from is_false this
      )
    ) (
      assume S₂ S₂',
      have spec.and S₁ S₁' ≠ spec.or S₂ S₂', by contradiction,
      show decidable (spec.and S₁ S₁' = spec.or S₂ S₂'), from is_false this
    ) (
      assume t₂ x₂ S₂ S₂',
      have spec.and S₁ S₁' ≠ spec.func t₂ x₂ S₂ S₂', by contradiction,
      show decidable (spec.and S₁ S₁' = spec.func t₂ x₂ S₂ S₂'), from is_false this
    )
  ) (
    assume S₁ S₁',
    assume : z = spec.or S₁ S₁',
    have R₁_id: R₁ = spec.or S₁ S₁', from eq.trans h this,
    show decidable (spec.or S₁ S₁' = R₂),
    from spec.cases_on (λR₂, decidable (spec.or S₁ S₁' = R₂)) R₂ (
      assume t₂,
      have spec.or S₁ S₁' ≠ spec.term t₂, by contradiction,
      show decidable (spec.or S₁ S₁' = spec.term t₂), from is_false this
    ) (
      assume S₂,
      have spec.or S₁ S₁' ≠ spec.not S₂, by contradiction,
      show decidable (spec.or S₁ S₁' = spec.not S₂), from is_false this
    ) (
      assume S₂ S₂',
      have spec.or S₁ S₁' ≠ spec.and S₂ S₂', by contradiction,
      show decidable (spec.or S₁ S₁' = spec.and S₂ S₂'), from is_false this
    ) (
      assume S₂ S₂',
      have S₁.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_and₁,
      have decidable (S₁ = S₂), from spec.dec_eq S₁ S₂,
      have S₁'.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_and₂,
      have decidable (S₁' = S₂'), from spec.dec_eq S₁' S₂',
      if h: (S₁ = S₂) ∧ (S₁' = S₂') then (
        have spec.or S₁ S₁' = spec.or S₂ S₂',
        from h.left ▸ h.right ▸ rfl,
        show decidable (spec.or S₁ S₁' = spec.or S₂ S₂'),
        from is_true this
      ) else (
        have spec.or S₁ S₁' ≠ spec.or S₂ S₂', from (
          assume : spec.or S₁ S₁' = spec.or S₂ S₂',
          show «false», from h (spec.or.inj this)
        ),
        show decidable (spec.or S₁ S₁' = spec.or S₂ S₂'),
        from is_false this
      )
    ) (
      assume t₂ x₂ S₂ S₂',
      have spec.or S₁ S₁' ≠ spec.func t₂ x₂ S₂ S₂', by contradiction,
      show decidable (spec.or S₁ S₁' = spec.func t₂ x₂ S₂ S₂'), from is_false this
    )
  ) (
    assume t₁ x₁ S₁ S₁',
    assume : z = spec.func t₁ x₁ S₁ S₁',
    have R₁_id: R₁ = spec.func t₁ x₁ S₁ S₁', from eq.trans h this,
    show decidable (spec.func t₁ x₁ S₁ S₁' = R₂),
    from spec.cases_on (λR₂, decidable (spec.func t₁ x₁ S₁ S₁' = R₂)) R₂ (
      assume t₂,
      have spec.func t₁ x₁ S₁ S₁' ≠ spec.term t₂, by contradiction,
      show decidable (spec.func t₁ x₁ S₁ S₁' = spec.term t₂), from is_false this
    ) (
      assume S₂,
      have spec.func t₁ x₁ S₁ S₁' ≠ spec.not S₂, by contradiction,
      show decidable (spec.func t₁ x₁ S₁ S₁' = spec.not S₂), from is_false this
    ) (
      assume S₂ S₂',
      have spec.func t₁ x₁ S₁ S₁' ≠ spec.and S₂ S₂', by contradiction,
      show decidable (spec.func t₁ x₁ S₁ S₁' = spec.and S₂ S₂'), from is_false this
    ) (
      assume S₂ S₂',
      have spec.func t₁ x₁ S₁ S₁' ≠ spec.or S₂ S₂', by contradiction,
      show decidable (spec.func t₁ x₁ S₁ S₁' = spec.or S₂ S₂'), from is_false this
    ) (
      assume t₂ x₂ S₂ S₂',
      have t₁.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_func_t,
      have decidable (t₁ = t₂), from term.dec_eq t₁ t₂,
      have S₁.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_func_R,
      have decidable (S₁ = S₂), from spec.dec_eq S₁ S₂,
      have S₁'.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_func_S,
      have decidable (S₁' = S₂'), from spec.dec_eq S₁' S₂',
      if h: (t₁ = t₂) ∧ (x₁ = x₂) ∧ (S₁ = S₂) ∧ (S₁' = S₂') then (
        have spec.func t₁ x₁ S₁ S₁' = spec.func t₂ x₂ S₂ S₂',
        from h.left ▸ h.right.left ▸ h.right.right.left ▸ h.right.right.right ▸ rfl,
        show decidable (spec.func t₁ x₁ S₁ S₁' = spec.func t₂ x₂ S₂ S₂'),
        from is_true this
      ) else (
        have spec.func t₁ x₁ S₁ S₁' ≠ spec.func t₂ x₂ S₂ S₂', from (
          assume : spec.func t₁ x₁ S₁ S₁' = spec.func t₂ x₂ S₂ S₂',
          show «false», from h (spec.func.inj this)
        ),
        show decidable (spec.func t₁ x₁ S₁ S₁' = spec.func t₂ x₂ S₂ S₂'),
        from is_false this
      )
    )
  ) rfl

with env.dec_eq : ∀ (σ₁ σ₂: env), decidable (σ₁ = σ₂)
| σ₁ σ₂ :=
  let z := σ₁ in
  have h: z = σ₁, from rfl,
  env.cases_on (λσ₁, (z = σ₁) → decidable (σ₁ = σ₂)) σ₁ (
    assume : z = env.empty,
    have σ₁_id: σ₁ = env.empty, from eq.trans h this,
    show decidable (env.empty = σ₂),
    from env.cases_on (λσ₂, decidable (env.empty = σ₂)) σ₂ (
      show decidable (env.empty = env.empty), from is_true rfl
    ) (
      assume σ₂' x₂ v₂,
      have env.empty ≠ env.cons σ₂' x₂ v₂, by contradiction,
      show decidable (env.empty = env.cons σ₂' x₂ v₂), from is_false this
    )
  ) (
    assume σ₁' x₁ v₁,
    assume : z = env.cons σ₁' x₁ v₁,
    have σ₁_id: σ₁ = env.cons σ₁' x₁ v₁, from eq.trans h this,
    show decidable (env.cons σ₁' x₁ v₁ = σ₂),
    from env.cases_on (λσ₂, decidable (env.cons σ₁' x₁ v₁ = σ₂)) σ₂ (
      have env.cons σ₁' x₁ v₁ ≠ env.empty, by contradiction,
      show decidable (env.cons σ₁' x₁ v₁ = env.empty), from is_false this
    ) (
      assume σ₂' x₂ v₂,
      have σ₁'.sizeof < σ₁.sizeof, from σ₁_id.symm ▸ sizeof_env_rest,
      have decidable (σ₁' = σ₂'), from env.dec_eq σ₁' σ₂',
      have v₁.sizeof < σ₁.sizeof, from σ₁_id.symm ▸ sizeof_env_value,
      have decidable (v₁ = v₂), from value.dec_eq v₁ v₂,
      if h: (σ₁' = σ₂') ∧ (x₁ = x₂) ∧ (v₁ = v₂) then (
        have env.cons σ₁' x₁ v₁ = env.cons σ₂' x₂ v₂,
        from h.left ▸ h.right.left ▸ h.right.right ▸ rfl,
        show decidable (env.cons σ₁' x₁ v₁ = env.cons σ₂' x₂ v₂),
        from is_true this
      ) else (
        have env.cons σ₁' x₁ v₁ ≠ env.cons σ₂' x₂ v₂, from (
          assume : env.cons σ₁' x₁ v₁ = env.cons σ₂' x₂ v₂,
          show «false», from h (env.cons.inj this)
        ),
        show decidable (env.cons σ₁' x₁ v₁ = env.cons σ₂' x₂ v₂),
        from is_false this
      )
    )
  ) rfl

using_well_founded
{
  rel_tac := λ _ _, `[exact wf_measure],
  dec_tac := tactic.assumption
}

instance : decidable_eq value := value.dec_eq
