-- lemmas about evaluation

import .definitions3

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

lemma pre_preserved {s s': dstack}: s ⟹* s' → (s.pre = s'.pre) :=
  begin
    assume h1,
    induction h1,
    case trans_dstep.rfl {
      refl
    },
    case trans_dstep.trans s₁ s₂ s₃ h2 h3 ih {
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

lemma step_dstep_progress {s s': stack}:
      (s ⟶ s') → ∀d, stack_equiv_dstack s d → ∃d', (d ⟹ d') :=
  begin
    assume h1,

    induction h1,

    case step.tru {
      assume d,
      assume h2,
      cases h2,

      existsi (dstack.top R (σ[x↦value.true]) e),
      apply dstep.tru
    },

    case step.fals {
      assume d,
      assume h2,
      cases h2,

      existsi (dstack.top R (σ[x↦value.false]) e),
      apply dstep.fals
    },

    case step.num {
      assume d,
      assume h2,
      cases h2,

      existsi (dstack.top R (σ[x↦value.num n]) e),
      apply dstep.num
    },

    case step.closure {
      assume d,
      assume h2,
      cases h2,

      existsi (dstack.top R_1 (σ[f↦value.func f x R S e₁ σ]) e₂),
      apply dstep.closure
    },

    case step.unop {
      assume d,
      assume h2,
      cases h2,

      existsi (dstack.top R (σ[y↦v]) e),
      apply dstep.unop a a_1
    },

    case step.binop {
      assume d,
      assume h2,
      cases h2,

      existsi (dstack.top R (σ[z↦v]) e),
      apply dstep.binop a a_1 a_2
    },

    case step.app {
      assume d,
      assume h2,
      cases h2,

      existsi (dstack.cons (R, (σ'[g↦value.func g z R S e σ'][z↦v]), e) R_1 σ y f x e'),
      apply dstep.app a a_1
    },

    case step.ite_true {
      assume d,
      assume h2,
      cases h2,

      existsi (dstack.top R σ e₁),
      apply dstep.ite_true a
    },

    case step.ite_false {
      assume d,
      assume h2,
      cases h2,

      existsi (dstack.top R σ e₂),
      apply dstep.ite_false a
    },

    case step.ctx s₁ s₂ σ₁ f x y e₁ steps ih {
      assume d,
      assume h2,
      cases h2,

      have h3, from ih d' a,
      cases h3 with d'' h4,

      existsi (dstack.cons d'' R σ₁ y f x e₁),
      apply dstep.ctx h4
    },

    case step.return {
      assume d,
      assume h2,
      cases h2,

      existsi (dstack.top R_1 (σ₂[y↦v]) e'),
      cases a_3,
      apply dstep.return a a_1 a_2
    }
  end

lemma step_dstep_progress.inv {d d': dstack}:
      (d ⟹ d') → ∀s, stack_equiv_dstack s d → ∃s', (s ⟶ s') :=
  begin
    assume h1,

    induction h1,

    case dstep.tru {
      assume s,
      assume h2,
      cases h2,

      existsi (stack.top (σ[x↦value.true]) e),
      apply step.tru
    },

    case dstep.fals {
      assume s,
      assume h2,
      cases h2,

      existsi (stack.top (σ[x↦value.false]) e),
      apply step.fals
    },

    case dstep.num {
      assume s,
      assume h2,
      cases h2,

      existsi (stack.top (σ[x↦value.num n]) e),
      apply step.num
    },

    case dstep.closure {
      assume s,
      assume h2,
      cases h2,

      existsi (stack.top (σ[f↦value.func f x R S e₁ σ]) e₂),
      apply step.closure,
      from spec.term value.true
    },

    case dstep.unop {
      assume s,
      assume h2,
      cases h2,

      existsi (stack.top (σ[y↦v]) e),
      apply step.unop a a_1
    },

    case dstep.binop {
      assume s,
      assume h2,
      cases h2,

      existsi (stack.top (σ[z↦v]) e),
      apply step.binop a a_1 a_2
    },

    case dstep.app {
      assume s,
      assume h2,
      cases h2,

      existsi (stack.cons ((σ'[g↦value.func g z R S e σ'][z↦v]), e) σ y f x e'),
      apply step.app a a_1
    },

    case dstep.ite_true {
      assume s,
      assume h2,
      cases h2,

      existsi (stack.top σ e₁),
      apply step.ite_true a
    },

    case dstep.ite_false {
      assume s,
      assume h2,
      cases h2,

      existsi (stack.top σ e₂),
      apply step.ite_false a
    },

    case dstep.ctx d₁ d₂ R σ₁ f x y e₁ steps ih {
      assume s,
      assume h2,
      cases h2,

      have h3, from ih s' a,
      cases h3 with s'' h4,

      existsi (stack.cons s'' σ₁ y f x e₁),
      apply step.ctx h4
    },

    case dstep.return {
      assume s,
      assume h2,
      cases h2,

      existsi (stack.top (σ₂[y↦v]) e'),
      cases a_3,
      apply step.return a a_1 a_2
    }
  end

lemma step_dstep_preservation {s: stack}:
      ∀{s': stack} {d d': dstack},
      stack_equiv_dstack s d → (s ⟶ s') → (d ⟹ d') → stack_equiv_dstack s' d' :=
  begin
    induction s,

    case stack.top σ e {
      assume s' d d',
      assume h1,
      assume h2,
      assume h3,
      cases h1,
      have h4: (dstack.top R σ e ⟹ d'), from h3,
      cases h2,

      case step.tru {
        cases h4,
        simp,
        apply stack_equiv_dstack.top
      },

      case step.fals {
        cases h4,
        simp,
        apply stack_equiv_dstack.top
      },

      case step.num {
        cases h4,
        simp,
        apply stack_equiv_dstack.top
      },

      case step.closure {
        cases h4,
        simp,
        apply stack_equiv_dstack.top
      },

      case step.unop {
        cases h4,
        simp,
        have h5, from eq.trans a.symm a_2,
        have h6: (v₁ = v₁_1), from option.some.inj h5,
        rw[h6] at a_1,
        have h7, from eq.trans a_1.symm a_3,
        have h8: (v = v_1), from option.some.inj h7,
        rw[h8],
        apply stack_equiv_dstack.top
      },

      case step.binop {
        cases h4,
        simp,
        have h5, from eq.trans a.symm a_3,
        have h6: (v₁ = v₁_1), from option.some.inj h5,
        rw[h6] at a_2,
        have h7, from eq.trans a_1.symm a_4,
        have h8: (v₂ = v₂_1), from option.some.inj h7,
        rw[h8] at a_2,
        have h9, from eq.trans a_2.symm a_5,
        have h10: (v = v_1), from option.some.inj h9,
        rw[h10],

        apply stack_equiv_dstack.top
      },

      case step.app {
        cases h4,
        apply stack_equiv_dstack.cons,
        have h5, from eq.trans a.symm a_2,
        have h6: ((value.func g z R_1 S e_1 σ') = (value.func g_1 z_1 R_2 S_1 e σ'_1)),
        from option.some.inj h5,
        injection h6,
        rw[h_1],
        rw[h_2],
        rw[h_3],
        rw[h_4],
        rw[h_5],
        rw[h_6],
        have h7, from eq.trans a_1.symm a_3,
        have h8: (v = v_1), from option.some.inj h7,
        rw[h8],
        apply stack_equiv_dstack.top
      },

      case step.ite_true {
        cases h4,
        simp,
        apply stack_equiv_dstack.top,
        have h7, from eq.trans a.symm a_1,
        have h8: (value.true = value.false), from option.some.inj h7,
        contradiction
      },

      case step.ite_false {
        cases h4,
        simp,
        have h7, from eq.trans a.symm a_1,
        have h8: (value.false = value.true), from option.some.inj h7,
        contradiction,
        apply stack_equiv_dstack.top,
      },
    },

    case stack.cons s'' σ'' f x y e'' ih {
      assume s' d d',
      assume h1,
      assume h2,
      assume h3,
      cases h1,
      cases h2,

      case step.ctx {
        cases h3,

        apply stack_equiv_dstack.cons,
        from ih a a_1 a_2,

        simp at a,
        cases a,
        cases a_1
      },

      case step.return {
        cases h3,

        simp at a,
        cases a,
        cases a_4,

        simp,
        cases a,
        have h5, from eq.trans a_1.symm a_4,
        have h6: (v = v_1), from option.some.inj h5,
        rw[h6],
        apply stack_equiv_dstack.top,
      }
    }
  end

lemma step_of_dstep_trans {d d': dstack}:
      (d ⟹* d') → ∀s, stack_equiv_dstack s d → ∃s', (s ⟶* s') ∧ stack_equiv_dstack s' d' :=
  begin
    assume h1,

    induction h1,

    assume s,
    assume h2,
    existsi s,
    split,
    from trans_step.rfl,
    from h2,

    assume s_1,
    assume h2,
    have h3, from ih_1 s_1 h2,
    cases h3 with s_2 h4,


    have h5, from step_dstep_progress.inv a_1 s_2 h4.right,
    cases h5 with s3 h6,

    existsi s3,
    split,
    apply trans_step.trans,
    from h4.left,
    from h6,

    apply step_dstep_preservation h4.right h6 a_1
  end

lemma dstep_of_step_trans {s s': stack}:
      (s ⟶* s') → ∀d, stack_equiv_dstack s d → ∃d', (d ⟹* d') ∧ stack_equiv_dstack s' d' :=
  begin
    assume h1,

    induction h1,

    assume d,
    assume h2,
    existsi d,
    split,
    from trans_dstep.rfl,
    from h2,

    assume s_1,
    assume h2,
    have h3, from ih_1 s_1 h2,
    cases h3 with s_2 h4,


    have h5: ∃ (d' : dstack), s_2⟹d', from step_dstep_progress a_1 s_2 h4.right,
    cases h5 with s3 h6,

    existsi s3,
    split,
    apply trans_dstep.trans,
    from h4.left,
    from h6,

    apply step_dstep_preservation h4.right a_1 h6 
  end

lemma step_of_dstep {R₁ R₂: spec} {σ₁ σ₂: env} {e₁ e₂: exp}: (R₁, σ₁, e₁) ⟹* (R₂, σ₂, e₂) → ((σ₁, e₁) ⟶* (σ₂, e₂)) :=
  begin
    assume h1,
    have h2: stack_equiv_dstack (σ₁, e₁) (R₁, σ₁, e₁), from stack_equiv_dstack.top,
    have h3, from step_of_dstep_trans h1 (σ₁, e₁) h2,
    cases h3 with s' h4,
    cases h4.right,
    from h4.left
  end

lemma value_or_step_of_dvalue_or_dstep {s: stack} {d: dstack}:
  stack_equiv_dstack s d → (is_dvalue d ∨ ∃d', d ⟹ d') → (is_value s ∨ ∃s', s ⟶ s') :=
  begin
    assume h1,
    assume h2,
    cases h2 with h3 h3,
    unfold is_dvalue at h3,
    cases h3 with R h4,
    cases h4 with σ h5,
    cases h5 with x h6,
    cases h6 with v h7,
    left,
    unfold is_value,
    existsi σ,
    existsi x,
    existsi v,
    split,
    rw[h7.left] at h1,
    cases h1,
    congr,
    from h7.right,
    cases h3 with d' h4,
    have h5, from step_dstep_progress.inv h4 s h1,
    right,
    from h5
  end
