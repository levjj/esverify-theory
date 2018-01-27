-- this defines a typed language arith and proves that its type system is sound

section arith

inductive typ : Type
  | num : typ
  | bool : typ

lemma typ_cases {p: Prop} (t: typ)
    (num_case: t = typ.num → p)
    (bool_case: t = typ.bool → p): p :=
  begin
    induction t,
    case typ.num {
      apply num_case rfl
    },
    case typ.bool {
      apply bool_case rfl
    }
  end

inductive exp : Type
  | num : ℕ → exp
  | bool : bool → exp
  | add : exp → exp → exp
  | ite : exp → exp → exp → exp
  | eq : exp → exp → exp

inductive is_value : exp → Prop
  | num {n: ℕ} : is_value (exp.num n)
  | bool {b: bool} : is_value (exp.bool b)

lemma is_value_cases {p: Prop} {e: exp} (e_is_value: is_value e)
    (num_case: ∀ (n: ℕ), e = exp.num n → p)
    (bool_case: ∀ (b: bool), e = exp.bool b → p): p :=
  begin
    induction e_is_value,
    case is_value.num n {
      apply num_case n rfl
    },
    case is_value.bool b {
      apply bool_case b rfl
    }
  end

inductive step : exp → exp → Prop
  notation e1 `⟶` e2:100 := step e1 e2
  | add {n1 n2: ℕ}:             exp.add (exp.num n1) (exp.num n2) ⟶ exp.num (n1 +n2)
  | add_right {e1 e2 e2': exp}: is_value e1 → (e2 ⟶ e2') →
                                (exp.add e1 e2 ⟶ exp.add e1 e2')
  | add_left {e1 e1' e2: exp}:  (e1 ⟶ e1') →
                                (exp.add e1 e2 ⟶ exp.add e1' e2)
  | ite_true {e2 e3: exp}:      exp.ite (exp.bool true) e2 e3 ⟶ e2
  | ite_false {e2 e3: exp}:     exp.ite (exp.bool false) e2 e3 ⟶ e3
  | ite {e1 e1' e2 e3: exp}:    (e1 ⟶ e1') →
                                (exp.ite e1 e2 e3 ⟶ exp.ite e1' e2 e3)
  | eq_num {n1 n2: ℕ}:          exp.eq (exp.num n1) (exp.num n2) ⟶ exp.bool (n1 = n2)
  | eq_bool {b1 b2: bool}:      exp.eq (exp.bool b1) (exp.bool b2) ⟶ exp.bool (b1 = b2)
  | eq_right {e1 e2 e2': exp}:  is_value e1 → (e2 ⟶ e2') →
                                (exp.eq e1 e2 ⟶ exp.eq e1 e2')
  | eq_left {e1 e1' e2: exp}:   (e1 ⟶ e1') →
                                (exp.eq e1 e2 ⟶ exp.eq e1' e2)

notation e1 `⟶` e2:100 := step e1 e2

inductive typed : exp → typ → Prop
  notation e1 `:::` e2:100 := typed e1 e2
  | num {n: ℕ}:                   exp.num n ::: typ.num
  | bool {b: bool}:               exp.bool b ::: typ.bool
  | add {e1 e2: exp}:             (e1 ::: typ.num) → (e2 ::: typ.num) →
                                  (exp.add e1 e2 ::: typ.num)
  | ite {e1 e2 e3: exp} {t: typ}: (e1 ::: typ.bool) → (e2 ::: t) → (e3 ::: t) →
                                  (exp.ite e1 e2 e3 ::: t)
  | eq {e1 e2: exp} {t: typ}:     (e1 ::: t) → (e2 ::: t) →
                                  (exp.eq e1 e2 ::: typ.bool)

notation e1 `:::` e2:100 := typed e1 e2

lemma typed_cases {p: Prop} {e: exp} {t: typ} (e_typed_t: e ::: t)
    (num_case: ∀ (n: ℕ), e = exp.num n → t = typ.num → p)
    (bool_case: ∀ (b: bool), e = exp.bool b → t = typ.bool → p)
    (add_case: ∀ (e1 e2: exp), (e1 ::: typ.num) → (e2 ::: typ.num) → e = exp.add e1 e2 → t = typ.num → p)
    (ite_case: ∀ (e1 e2 e3: exp), (e1 ::: typ.bool) → (e2 ::: t) → (e3 ::: t) → e = exp.ite e1 e2 e3 → p)
    (eq_case: ∀ (e1 e2: exp) (t1: typ), (e1 ::: t1) → (e2 ::: t1) → e = exp.eq e1 e2 → t = typ.bool → p): p :=
  begin
    induction e_typed_t,
    case typed.num n {
      apply num_case n rfl rfl
    },
    case typed.bool b {
      apply bool_case b rfl rfl
    },
    case typed.add e1 e2 e1_typed_num e2_typed_num {
      apply add_case e1 e2 e1_typed_num e2_typed_num rfl rfl
    },
    case typed.ite e1 e2 e3 t1 e1_typed_bool e2_typed_t e3_typed_t {
      apply ite_case e1 e2 e3 e1_typed_bool e2_typed_t e3_typed_t rfl
    },
    case typed.eq e1 e2 t1 e1_typed_t1 e2_typed_t1 {
      apply eq_case e1 e2 t1 e1_typed_t1 e2_typed_t1 rfl rfl
    },
  end

lemma numt_inversion {e: exp} (e_typed_num: e ::: typ.num) (e_is_val: is_value e): ∃n: ℕ, e = exp.num n :=
  typed_cases e_typed_num
  ( -- num
    assume n: ℕ,
    assume e_is_num: e = exp.num n,
    assume _,
    exists.intro n e_is_num 
  )
  ( -- bool
    assume _ _,
    assume numt_is_boolt: typ.num = typ.bool,
    show ∃n: ℕ, e = exp.num n, from typ.no_confusion numt_is_boolt
  )
  ( -- add
    assume e1 e2: exp,
    assume _ _,
    assume e_is_add: e = exp.add e1 e2,
    assume _,
    is_value_cases e_is_val
    (  -- is value num
      assume n: ℕ,
      assume e_is_num: e = exp.num n,
      have add_is_num: exp.add e1 e2 = exp.num n, from eq.trans (eq.symm e_is_add) e_is_num,
      show ∃n: ℕ, e = exp.num n, from exp.no_confusion add_is_num
    )
    (  -- is value bool
      assume b: bool,
      assume e_is_bool: e = exp.bool b,
      have add_is_bool: exp.add e1 e2 = exp.bool b, from eq.trans (eq.symm e_is_add) e_is_bool,
      show ∃n: ℕ, e = exp.num n, from exp.no_confusion add_is_bool
    )
  )
  ( -- ite
    assume e1 e2 e3: exp,
    assume _ _ _,
    assume e_is_ite: e = exp.ite e1 e2 e3,
    is_value_cases e_is_val
    (  -- is value num
      assume n: ℕ,
      assume e_is_num: e = exp.num n,
      have add_is_num: exp.ite e1 e2 e3 = exp.num n, from eq.trans (eq.symm e_is_ite) e_is_num,
      show ∃n: ℕ, e = exp.num n, from exp.no_confusion add_is_num
    )
    (  -- is value bool
      assume b: bool,
      assume e_is_bool: e = exp.bool b,
      have add_is_bool: exp.ite e1 e2 e3 = exp.bool b, from eq.trans (eq.symm e_is_ite) e_is_bool,
      show ∃n: ℕ, e = exp.num n, from exp.no_confusion add_is_bool
    )
  )
  ( -- eq
    assume e1 e2: exp,
    assume _ _ _,
    assume e_is_eq: e = exp.eq e1 e2,
    assume _,
    is_value_cases e_is_val
    (  -- is value num
      assume n: ℕ,
      assume e_is_num: e = exp.num n,
      have add_is_num: exp.eq e1 e2 = exp.num n, from eq.trans (eq.symm e_is_eq) e_is_num,
      show ∃n: ℕ, e = exp.num n, from exp.no_confusion add_is_num
    )
    (  -- is value bool
      assume b: bool,
      assume e_is_bool: e = exp.bool b,
      have add_is_bool: exp.eq e1 e2 = exp.bool b, from eq.trans (eq.symm e_is_eq) e_is_bool,
      show ∃n: ℕ, e = exp.num n, from exp.no_confusion add_is_bool
    )
  )

lemma boolt_inversion {e: exp} (e_typed_bool: e ::: typ.bool) (e_is_val: is_value e):
                      e = exp.bool true ∨ e = exp.bool false :=
  typed_cases e_typed_bool
  ( -- num
    assume _ _,
    assume numt_is_boolt: typ.bool = typ.num,
    show e = exp.bool true ∨ e = exp.bool false, from typ.no_confusion numt_is_boolt
  )
  ( -- bool
    assume b: bool,
    assume e_is_bool: e = exp.bool b,
    assume : typ.bool = typ.bool,
    show e = exp.bool true ∨ e = exp.bool false, by begin
      cases b,
      case tt {
        apply or.inl,
        assumption
      },
      case ff {
        apply or.inr,
        assumption
      }
    end
  )
  ( -- add
    assume e1 e2: exp,
    assume _ _,
    assume e_is_add: e = exp.add e1 e2,
    assume _,
    is_value_cases e_is_val
    (  -- is value num
      assume n: ℕ,
      assume e_is_num: e = exp.num n,
      have add_is_num: exp.add e1 e2 = exp.num n, from eq.trans (eq.symm e_is_add) e_is_num,
      show e = exp.bool true ∨ e = exp.bool false, from exp.no_confusion add_is_num
    )
    (  -- is value bool
      assume b: bool,
      assume e_is_bool: e = exp.bool b,
      have add_is_bool: exp.add e1 e2 = exp.bool b, from eq.trans (eq.symm e_is_add) e_is_bool,
      show e = exp.bool true ∨ e = exp.bool false, from exp.no_confusion add_is_bool
    )
  )
  ( -- ite
    assume e1 e2 e3: exp,
    assume _ _ _,
    assume e_is_ite: e = exp.ite e1 e2 e3,
    is_value_cases e_is_val
    (  -- is value num
      assume n: ℕ,
      assume e_is_num: e = exp.num n,
      have add_is_num: exp.ite e1 e2 e3 = exp.num n, from eq.trans (eq.symm e_is_ite) e_is_num,
      show e = exp.bool true ∨ e = exp.bool false, from exp.no_confusion add_is_num
    )
    (  -- is value bool
      assume b: bool,
      assume e_is_bool: e = exp.bool b,
      have add_is_bool: exp.ite e1 e2 e3 = exp.bool b, from eq.trans (eq.symm e_is_ite) e_is_bool,
      show e = exp.bool true ∨ e = exp.bool false, from exp.no_confusion add_is_bool
    )
  )
  ( -- eq
    assume e1 e2: exp,
    assume _ _ _,
    assume e_is_eq: e = exp.eq e1 e2,
    assume _,
    is_value_cases e_is_val
    (  -- is value num
      assume n: ℕ,
      assume e_is_num: e = exp.num n,
      have add_is_num: exp.eq e1 e2 = exp.num n, from eq.trans (eq.symm e_is_eq) e_is_num,
      show e = exp.bool true ∨ e = exp.bool false, from exp.no_confusion add_is_num
    )
    (  -- is value bool
      assume b: bool,
      assume e_is_bool: e = exp.bool b,
      have add_is_bool: exp.eq e1 e2 = exp.bool b, from eq.trans (eq.symm e_is_eq) e_is_bool,
      show e = exp.bool true ∨ e = exp.bool false, from exp.no_confusion add_is_bool
    )
  )

theorem progress(e: exp) (t: typ) (is_typed: e ::: t): is_value e ∨ ∃e', e ⟶ e' :=
  typed.rec_on is_typed
    ( -- num
      assume n: ℕ,
      let e := exp.num n in
      have e_is_val: is_value e, from is_value.num,
      show is_value e ∨ ∃e', e ⟶ e', from or.inl e_is_val
    )
    ( -- bool
      assume b: bool,
      let e := exp.bool b in
      have e_is_val: is_value e, from is_value.bool,
      show is_value e ∨ ∃e', e ⟶ e', from or.inl e_is_val
    )
    ( -- add
      assume e1 e2: exp,
      assume e1_is_numt : e1 ::: typ.num,
      assume e2_is_numt : e2 ::: typ.num,
      assume e1ih: is_value e1 ∨ ∃e1', e1 ⟶ e1',
      assume e2ih: is_value e2 ∨ ∃e2', e2 ⟶ e2',
      let e := exp.add e1 e2 in
      have e_is_add: e = exp.add e1 e2, from rfl,
      have e_steps: ∃e', e ⟶ e', from or.elim e1ih (
        assume e1_is_val: is_value e1,
        or.elim e2ih (
          assume e2_is_val: is_value e2,
          have e1_exists_num: ∃n1: ℕ, e1 = exp.num n1, from numt_inversion e1_is_numt e1_is_val,
          have e2_exists_num: ∃n2: ℕ, e2 = exp.num n2, from numt_inversion e2_is_numt e2_is_val,
          exists.elim e1_exists_num (
            assume n1: ℕ,
            assume e1_is_num: e1 = exp.num n1,
            exists.elim e2_exists_num (
              assume n2: ℕ,
              assume e2_is_num: e2 = exp.num n2,
              have exp.add (exp.num n1) (exp.num n2) ⟶ exp.num (n1 + n2), from step.add,
              have e ⟶ exp.num (n1 + n2), by { rw [←e1_is_num, ←e2_is_num, ←e_is_add] at this, assumption },
              show ∃e', e ⟶ e', from exists.intro (exp.num (n1 + n2)) this
            )
          )
        )
        (
          assume e2_can_step: ∃e2', e2 ⟶ e2',
          exists.elim e2_can_step (
            assume e2': exp,
            assume e2_steps: e2 ⟶ e2',
            have e ⟶ exp.add e1 e2', from step.add_right e1_is_val e2_steps,
            show ∃e', e ⟶ e', from exists.intro (exp.add e1 e2') this
          )
        )
      )
      (
        assume e1_can_step: ∃e1', e1 ⟶ e1',
        exists.elim e1_can_step (
          assume e1': exp,
          assume e1_steps: e1 ⟶ e1',
          have e ⟶ exp.add e1' e2, from step.add_left e1_steps,
          show ∃e', e ⟶ e', from exists.intro (exp.add e1' e2) this
        )
      ),
      show is_value e ∨ ∃e', e ⟶ e', from or.inr e_steps
    )
    ( -- ite
      assume e1 e2 e3: exp,
      assume t: typ,
      assume e1_is_bool: e1 ::: typ.bool,
      assume e2_is_t: e2 ::: t,
      assume e3_is_t: e3 ::: t,
      assume e1ih: is_value e1 ∨ ∃e1', e1 ⟶ e1',
      assume e2ih: is_value e2 ∨ ∃e2', e2 ⟶ e2',
      assume e3ih: is_value e3 ∨ ∃e3', e3 ⟶ e3',
      let e := exp.ite e1 e2 e3 in
      have e_is_ite: e = exp.ite e1 e2 e3, from rfl,
      or.elim e1ih
      ( -- is_value e1
        assume e1_is_val: is_value e1,
        have e1_bool: e1 = exp.bool true ∨ e1 = exp.bool false, from boolt_inversion e1_is_bool e1_is_val,
        or.elim e1_bool
        ( -- ite-true
          assume e1_is_true: e1 = exp.bool true,
          have exp.ite (exp.bool true) e2 e3 ⟶ e2, from step.ite_true,
          have e ⟶ e2, by { rw [←e1_is_true, ←e_is_ite] at this, assumption },
          have e_steps: ∃e', e ⟶ e', from exists.intro e2 this,
          show is_value e ∨ ∃e', e ⟶ e', from or.inr e_steps
        )
        ( -- ite-false
          assume e1_is_false: e1 = exp.bool false,
          have exp.ite (exp.bool false) e2 e3 ⟶ e3, from step.ite_false,
          have e ⟶ e3, by { rw [←e1_is_false, ←e_is_ite] at this, assumption },
          have e_steps: ∃e', e ⟶ e', from exists.intro e3 this,
          show is_value e ∨ ∃e', e ⟶ e', from or.inr e_steps
        )
      )
      ( -- e1 steps
        assume e1_can_step: ∃e1', e1 ⟶ e1',
        exists.elim e1_can_step (λe1', 
          assume e1_steps: e1 ⟶ e1',
          have e ⟶ exp.ite e1' e2 e3, from step.ite e1_steps,
          have e_steps: ∃e', e ⟶ e', from exists.intro (exp.ite e1' e2 e3) this,
          show is_value e ∨ ∃e', e ⟶ e', from or.inr e_steps
        )
      )
    )
    ( -- eq
      assume e1 e2: exp,
      assume t: typ,
      assume e1_typed_t: e1 ::: t,
      assume e2_typed_t: e2 ::: t,
      assume e1ih: is_value e1 ∨ ∃e1', e1 ⟶ e1',
      assume e2ih: is_value e2 ∨ ∃e2', e2 ⟶ e2',
      let e := exp.eq e1 e2 in
      have e_is_eq: e = exp.eq e1 e2, from rfl,
      or.elim e1ih (
        assume e1_is_val: is_value e1,
        or.elim e2ih (
          assume e2_is_val: is_value e2,
          typ_cases t
          ( -- num
            assume t_is_num: t = typ.num,
            have e1_typed_num: e1 ::: typ.num, by { rw[t_is_num] at e1_typed_t, assumption  },
            have e2_typed_num: e2 ::: typ.num, by { rw[t_is_num] at e2_typed_t, assumption  },
            have e1_exists_num: ∃n1: ℕ, e1 = exp.num n1, from numt_inversion e1_typed_num e1_is_val,
            have e2_exists_num: ∃n2: ℕ, e2 = exp.num n2, from numt_inversion e2_typed_num e2_is_val,
            exists.elim e1_exists_num (λn1, exists.elim e2_exists_num (λn2,
              assume e2_is_num: e2 = exp.num n2,
              assume e1_is_num: e1 = exp.num n1,
              have exp.eq (exp.num n1) (exp.num n2) ⟶ exp.bool (n1 = n2), from step.eq_num,
              have e ⟶ exp.bool (n1 = n2), by { rw [←e1_is_num, ←e2_is_num, ←e_is_eq] at this, assumption },
              have e_steps: ∃e', e ⟶ e', from exists.intro (exp.bool (n1 = n2)) this,
              show is_value e ∨ ∃e', e ⟶ e', from or.inr e_steps
            ))
          )
          ( -- bool
            assume t_is_bool: t = typ.bool,
            have e1_typed_bool: e1 ::: typ.bool, by { rw[t_is_bool] at e1_typed_t, assumption  },
            have e2_typed_bool: e2 ::: typ.bool, by { rw[t_is_bool] at e2_typed_t, assumption  },
            have e1_some_bool: e1 = exp.bool true ∨ e1 = exp.bool false, from boolt_inversion e1_typed_bool e1_is_val,
            have e2_some_bool: e2 = exp.bool true ∨ e2 = exp.bool false, from boolt_inversion e2_typed_bool e2_is_val,
            or.elim e1_some_bool
            (
              assume e1_is_true: e1 = exp.bool true,
              or.elim e2_some_bool
              (
                assume e2_is_true: e2 = exp.bool true,
                have e_is_true_eq_true: e = exp.eq (exp.bool true) (exp.bool true),
                by { rw [e1_is_true, e2_is_true] at e_is_eq, assumption },
                have exp.eq (exp.bool true) (exp.bool true) ⟶ exp.bool true, from step.eq_bool,
                have e ⟶ exp.bool true, by { rw [←e_is_true_eq_true] at this, assumption },
                have e_steps: ∃e', e ⟶ e', from exists.intro (exp.bool true) this,
                show is_value e ∨ ∃e', e ⟶ e', from or.inr e_steps
              )
              (
                assume e2_is_false: e2 = exp.bool false,
                have e_is_true_eq_false: e = exp.eq (exp.bool true) (exp.bool false),
                by { rw [e1_is_true, e2_is_false] at e_is_eq, assumption },
                have exp.eq (exp.bool true) (exp.bool false) ⟶ exp.bool false, from step.eq_bool,
                have e ⟶ exp.bool false, by { rw [←e_is_true_eq_false] at this, assumption },
                have e_steps: ∃e', e ⟶ e', from exists.intro (exp.bool false) this,
                show is_value e ∨ ∃e', e ⟶ e', from or.inr e_steps
              )
            )
            (
              assume e1_is_false: e1 = exp.bool false,
              or.elim e2_some_bool
              (
                assume e2_is_true: e2 = exp.bool true,
                have e_is_false_eq_true: e = exp.eq (exp.bool false) (exp.bool true),
                by { rw [e1_is_false, e2_is_true] at e_is_eq, assumption },
                have exp.eq (exp.bool false) (exp.bool true) ⟶ exp.bool false, from step.eq_bool,
                have e ⟶ exp.bool false, by { rw [←e_is_false_eq_true] at this, assumption },
                have e_steps: ∃e', e ⟶ e', from exists.intro (exp.bool false) this,
                show is_value e ∨ ∃e', e ⟶ e', from or.inr e_steps
              )
              (
                assume e2_is_false: e2 = exp.bool false,
                have e_is_false_eq_false: e = exp.eq (exp.bool false) (exp.bool false),
                by { rw [e1_is_false, e2_is_false] at e_is_eq, assumption },
                have exp.eq (exp.bool false) (exp.bool false) ⟶ exp.bool true, from step.eq_bool,
                have e ⟶ exp.bool true, by { rw [←e_is_false_eq_false] at this, assumption },
                have e_steps: ∃e', e ⟶ e', from exists.intro (exp.bool true) this,
                show is_value e ∨ ∃e', e ⟶ e', from or.inr e_steps
              )
            )
          )
        )
        (
          assume e2_can_step: ∃e2', e2 ⟶ e2',
          exists.elim e2_can_step (λe2', 
            assume e2_steps: e2 ⟶ e2',
            have e ⟶ exp.eq e1 e2', from step.eq_right e1_is_val e2_steps,
            have e_steps: ∃e', e ⟶ e', from exists.intro (exp.eq e1 e2') this,
            show is_value e ∨ ∃e', e ⟶ e', from or.inr e_steps
          )
        )
      ) (
        assume e1_can_step: ∃e1', e1 ⟶ e1',
        exists.elim e1_can_step (λe1', 
          assume e1_steps: e1 ⟶ e1',
          have e ⟶ exp.eq e1' e2, from step.eq_left e1_steps,
          have e_steps: ∃e', e ⟶ e', from exists.intro (exp.eq e1' e2) this,
          show is_value e ∨ ∃e', e ⟶ e', from or.inr e_steps
        )
      )
    )

end arith