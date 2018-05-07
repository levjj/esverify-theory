-- lemmas about evaluation

import .definitions2

-- lemmas

lemma binop.eq_of_equal_values {v: value}: binop.apply binop.eq v v = value.true :=
  have binop.apply binop.eq v v = (if v = v then value.true else value.false), by unfold binop.apply,
  show binop.apply binop.eq v v = value.true, by simp[this]

lemma unop.isFunc.inv {v: value}: unop.apply unop.isFunc v = value.true → 
      ∃ (f x: var) (R S: spec) (e: exp) (σ: env), v = value.func f x R S e σ :=
  assume isFunc_is_true: unop.apply unop.isFunc v = value.true,
  begin
    cases v with n f x R S e σ,

    show ∃ (f x: var) (R S: spec) (e: exp) (σ: env), value.true = value.func f x R S e σ, from (
      have h1: (unop.apply unop.isFunc value.true = value.true), from isFunc_is_true,
      have h2: (unop.apply unop.isFunc value.true = value.false), by unfold unop.apply,
      have some value.true = some value.false, from eq.trans h1.symm h2,
      have value.true = value.false, from option.some.inj this,
      false.elim (value._mut_.no_confusion this)
    ),

    show ∃ (f x: var) (R S: spec) (e: exp) (σ: env), value.false = value.func f x R S e σ, from (
      have h1: (unop.apply unop.isFunc value.false = value.true), from isFunc_is_true,
      have h2: (unop.apply unop.isFunc value.false = value.false), by unfold unop.apply,
      have some value.true = some value.false, from eq.trans h1.symm h2,
      have value.true = value.false, from option.some.inj this,
      false.elim (value._mut_.no_confusion this)
    ),

    show ∃ (f x: var) (R S: spec) (e: exp) (σ: env), value.num n = value.func f x R S e σ, from (
      have h1: (unop.apply unop.isFunc (value.num n) = value.true), from isFunc_is_true,
      have h2: (unop.apply unop.isFunc (value.num n) = value.false), by unfold unop.apply,
      have some value.true = some value.false, from eq.trans h1.symm h2,
      have value.true = value.false, from option.some.inj this,
      false.elim (value._mut_.no_confusion this)
    ),

    show ∃ (f_1 x_1: var) (R_1 S_1: spec) (e_1: exp) (σ_1: env),
        value.func f x R S e σ = value.func f_1 x_1 R_1 S_1 e_1 σ_1, from (
      exists.intro f (exists.intro x (exists.intro R (exists.intro S
                     (exists.intro e (exists.intro σ rfl)))))
    )
  end

lemma unop.isBool.inv {v: value}: unop.apply unop.isBool v = value.true → (v = value.true) ∨ (v = value.false) :=
  assume isBool_is_true: unop.apply unop.isBool v = value.true,
  begin
    cases v with n f x R S e σ,

    show ((value.true = value.true) ∨ (value.true = value.false)), from (
      or.inl rfl
    ),

    show ((value.false = value.true) ∨ (value.false = value.false)), from (
      or.inr rfl
    ),

    show (value.num n = value.true ∨ (value.num n = value.false)), from (
      have h1: unop.apply unop.isBool (value.num n) = ↑value.true, from isBool_is_true,
      have h2: (unop.apply unop.isBool (value.num n) = value.false), by unfold unop.apply,
      have some value.true = some value.false, from eq.trans h1.symm h2,
      have value.true = value.false, from option.some.inj this,
      false.elim (value._mut_.no_confusion this)
    ),

    show (value.func f x R S e σ = value.true ∨ (value.func f x R S e σ = value.false)), from (
      have h1: unop.apply unop.isBool (value.func f x R S e σ) = ↑value.true, from isBool_is_true,
      have h2: (unop.apply unop.isBool (value.func f x R S e σ) = value.false), by unfold unop.apply,
      have some value.true = some value.false, from eq.trans h1.symm h2,
      have value.true = value.false, from option.some.inj this,
      false.elim (value._mut_.no_confusion this)
    )
  end

lemma binop.eq.inv {v₁ v₂: value}: binop.apply binop.eq v₁ v₂ = value.true → (v₁ = v₂) :=
  assume eq_is_true: binop.apply binop.eq v₁ v₂ = value.true,
  begin
    by_cases (v₁ = v₂),
    from h,
    unfold binop.apply at eq_is_true,
    simp[h] at eq_is_true,
    have h2, from option.some.inj eq_is_true,
    contradiction
  end

lemma pre_preserved {s s': stack}: s ⟶* s' → (s.pre = s'.pre) :=
  begin
    assume h1,
    induction h1,
    case trans_step.rfl {
      refl
    },
    case trans_step.trans s₁ s₂ s₃ h2 h3 ih {
      apply eq.trans ih,
      cases h3,
      repeat {refl}
    }
  end

lemma unop_result_not_function {vx vy: value} {op: unop}:
      (unop.apply op vx = some vy) → (vy = value.true) ∨ (vy = value.false) :=
  begin
    assume h1,
    cases op,
    case unop.not {
      cases vx,

      unfold unop.apply at h1,
      have h2: (value.false = vy), from option.some.inj h1,
      right,
      from h2.symm,

      unfold unop.apply at h1,
      have h2: (value.true = vy), from option.some.inj h1,
      left,
      from h2.symm,

      unfold unop.apply at h1,
      contradiction,

      unfold unop.apply at h1,
      contradiction
    },
    case unop.isInt {
      cases vx,

      unfold unop.apply at h1,
      have h2: (value.false = vy), from option.some.inj h1,
      right,
      from h2.symm,

      unfold unop.apply at h1,
      have h2: (value.false = vy), from option.some.inj h1,
      right,
      from h2.symm,

      unfold unop.apply at h1,
      have h2: (value.true = vy), from option.some.inj h1,
      left,
      from h2.symm,

      unfold unop.apply at h1,
      have h2: (value.false = vy), from option.some.inj h1,
      right,
      from h2.symm
    },
    case unop.isBool {
      cases vx,

      unfold unop.apply at h1,
      have h2: (value.true = vy), from option.some.inj h1,
      left,
      from h2.symm,

      unfold unop.apply at h1,
      have h2: (value.true = vy), from option.some.inj h1,
      left,
      from h2.symm,

      unfold unop.apply at h1,
      have h2: (value.false = vy), from option.some.inj h1,
      right,
      from h2.symm,

      unfold unop.apply at h1,
      have h2: (value.false = vy), from option.some.inj h1,
      right,
      from h2.symm
    },
    case unop.isFunc {
      cases vx,

      unfold unop.apply at h1,
      have h2: (value.false = vy), from option.some.inj h1,
      right,
      from h2.symm,

      unfold unop.apply at h1,
      have h2: (value.false = vy), from option.some.inj h1,
      right,
      from h2.symm,

      unfold unop.apply at h1,
      have h2: (value.false = vy), from option.some.inj h1,
      right,
      from h2.symm,

      unfold unop.apply at h1,
      have h2: (value.true = vy), from option.some.inj h1,
      left,
      from h2.symm
    }
  end

lemma binop_result_not_function {vx vy vz: value} {op: binop}:
      (binop.apply op vx vy = some vz) → ((vz = value.true) ∨ (vz = value.false) ∨ (∃n, vz = value.num n)) :=
  begin
    assume h1,
    cases op,
    case binop.plus {
      cases vx,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction,

      cases vy,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      have h2: (value.num (a + a_1) = vz), from option.some.inj h1,
      right,
      right,
      existsi (a + a_1),
      from h2.symm,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction
    },
    case binop.minus {
      cases vx,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction,

      cases vy,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      have h2: (value.num (a - a_1) = vz), from option.some.inj h1,
      right,
      right,
      existsi (a - a_1),
      from h2.symm,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction
    },
    case binop.times {
      cases vx,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction,

      cases vy,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      have h2: (value.num (a * a_1) = vz), from option.some.inj h1,
      right,
      right,
      existsi (a * a_1),
      from h2.symm,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction
    },
    case binop.div {
      cases vx,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction,

      cases vy,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      have h2: (value.num (a / a_1) = vz), from option.some.inj h1,
      right,
      right,
      existsi (a / a_1),
      from h2.symm,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction
    },
    case binop.and {
      cases vx,
      cases vy,

      unfold binop.apply at h1,
      have h2: (value.true = vz), from option.some.inj h1,
      left,
      from h2.symm,

      unfold binop.apply at h1,
      have h2: (value.false = vz), from option.some.inj h1,
      right,
      left,
      from h2.symm,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction,

      cases vy,

      unfold binop.apply at h1,
      have h2: (value.false = vz), from option.some.inj h1,
      right,
      left,
      from h2.symm,

      unfold binop.apply at h1,
      have h2: (value.false = vz), from option.some.inj h1,
      right,
      left,
      from h2.symm,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction
    },
    case binop.or {
      cases vx,
      cases vy,

      unfold binop.apply at h1,
      have h2: (value.true = vz), from option.some.inj h1,
      left,
      from h2.symm,

      unfold binop.apply at h1,
      have h2: (value.true = vz), from option.some.inj h1,
      left,
      from h2.symm,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction,

      cases vy,

      unfold binop.apply at h1,
      have h2: (value.true = vz), from option.some.inj h1,
      left,
      from h2.symm,

      unfold binop.apply at h1,
      have h2: (value.false = vz), from option.some.inj h1,
      right,
      left,
      from h2.symm,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction
    },
    case binop.eq {
      unfold binop.apply at h1,
      by_cases (vx = vy),
      simp[h] at h1,

      have h2: (value.true = vz), from option.some.inj h1,
      left,
      from h2.symm,

      simp[h] at h1,
      have h2: (value.false = vz), from option.some.inj h1,
      right,
      left,
      from h2.symm
    },
    case binop.lt {
      cases vx,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction,

      cases vy,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      by_cases (a < a_1),

      simp[h] at h1,
      have h2: (value.true = vz), from option.some.inj h1,
      left,
      from h2.symm,

      simp[h] at h1,
      have h2: (value.false = vz), from option.some.inj h1,
      right,
      left,
      from h2.symm,

      unfold binop.apply at h1,
      contradiction,

      unfold binop.apply at h1,
      contradiction    }
  end
