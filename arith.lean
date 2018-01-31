-- this defines a typed language arith and proves that its type system is sound

section arith

inductive typ : Type
  | num : typ
  | bool : typ

instance : decidable_eq typ := by tactic.mk_dec_eq_instance

inductive exp : Type
  | num : ℕ → exp
  | bool : bool → exp
  | add : exp → exp → exp
  | ite : exp → exp → exp → exp
  | eq : exp → exp → exp

inductive is_value : exp → Prop
  | num {n: ℕ} : is_value (exp.num n)
  | bool {b: bool} : is_value (exp.bool b)

inductive step : exp → exp → Prop
  notation e1 `⟶` e2:100 := step e1 e2
  | add {n1 n2: ℕ}:             exp.add (exp.num n1) (exp.num n2) ⟶ exp.num (n1+n2)
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

inductive trans_step : exp → exp → Prop
  notation e `⟶*` e':100 := trans_step e e'
  | rfl {e: exp}:          e ⟶* e
  | trans {e e' e'': exp}: (e ⟶ e') → (e' ⟶* e'') → (e ⟶* e'')

notation e `⟶*` e':100 := trans_step e e'

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

lemma typ_cases {p: Prop}: ∀(t: typ),
    (t = typ.num → p) →
    (t = typ.bool → p) → p
  | typ.num num_case _ := num_case rfl
  | typ.bool _ bool_case := bool_case rfl

lemma is_value_cases {p: Prop} {e: exp} (e_is_value: is_value e)
    (num_case: ∀ (n: ℕ), e = exp.num n → p)
    (bool_case: ∀ (b: bool), e = exp.bool b → p): p :=
  begin
    cases e_is_value,
    case is_value.num n {
      show p, from num_case n rfl
    },
    case is_value.bool b {
      show p, from bool_case b rfl
    }
  end

lemma step_cases {p: Prop} {e e': exp} (e_steps: e ⟶ e')
    (add_case: ∀ (n1 n2: ℕ), e = exp.add (exp.num n1) (exp.num n2) → e' = exp.num (n1+n2) → p)
    (add_right_case: ∀ (e1 e2 e2': exp), is_value e1 → (e2 ⟶ e2') → e = exp.add e1 e2 → e' = exp.add e1 e2' → p)
    (add_left_case: ∀ (e1 e1' e2: exp), (e1 ⟶ e1') → e = exp.add e1 e2 → e' = exp.add e1' e2 → p)
    (ite_true_case: ∀ (e2 e3: exp), e = exp.ite (exp.bool true) e2 e3 → e' = e2 → p)
    (ite_false_case: ∀ (e2 e3: exp), e = exp.ite (exp.bool false) e2 e3 → e' = e3 → p)
    (ite_case: ∀ (e1 e1' e2 e3: exp), e1 ⟶ e1' → e = exp.ite e1 e2 e3 → e' = exp.ite e1' e2 e3 → p)
    (eq_num_case: ∀ (n1 n2: ℕ), e = exp.eq (exp.num n1) (exp.num n2) → e' = exp.bool (n1 = n2) → p)
    (eq_bool_case: ∀ (b1 b2: bool), e = exp.eq (exp.bool b1) (exp.bool b2) → e' = exp.bool (b1 = b2) → p)
    (eq_right_case: ∀ (e1 e2 e2': exp), is_value e1 → (e2 ⟶ e2') → e = exp.eq e1 e2 → e' = exp.eq e1 e2' → p)
    (eq_left_case: ∀ (e1 e1' e2: exp), (e1 ⟶ e1') → e = exp.eq e1 e2 → e' = exp.eq e1' e2 → p) : p :=
  begin
    induction e_steps,
    case step.add n1 n2 {
      exact add_case n1 n2 rfl rfl
    },
    case step.add_right e1 e2 e2' e1_is_value e2_steps {
      exact add_right_case e1 e2 e2' e1_is_value e2_steps rfl rfl
    },
    case step.add_left e1 e1' e2 e1_steps {
      exact add_left_case e1 e1' e2 e1_steps rfl rfl
    },
    case step.ite_true e2 e3 {
      exact ite_true_case e2 e3 rfl rfl
    },
    case step.ite_false e2 e3 {
      exact ite_false_case e2 e3 rfl rfl
    },
    case step.ite e1 e1' e2 e3 e1_steps {
      exact ite_case e1 e1' e2 e3 e1_steps rfl rfl
    },
    case step.eq_num n1 n2 {
      exact eq_num_case n1 n2 rfl rfl
    },
    case step.eq_bool b1 b2 {
      exact eq_bool_case b1 b2 rfl rfl
    },
    case step.eq_right e1 e2 e2' e1_is_value e2_steps {
      exact eq_right_case e1 e2 e2' e1_is_value e2_steps rfl rfl
    },
    case step.eq_left e1 e1' e2 e1_steps {
      exact eq_left_case e1 e1' e2 e1_steps rfl rfl
    }
  end

lemma typed_cases {p: Prop} {e: exp} {t: typ} (e_typed_t: e ::: t)
    (num_case: ∀ (n: ℕ), e = exp.num n → t = typ.num → p)
    (bool_case: ∀ (b: bool), e = exp.bool b → t = typ.bool → p)
    (add_case: ∀ (e1 e2: exp), (e1 ::: typ.num) → (e2 ::: typ.num) → e = exp.add e1 e2 → t = typ.num → p)
    (ite_case: ∀ (e1 e2 e3: exp), (e1 ::: typ.bool) → (e2 ::: t) → (e3 ::: t) → e = exp.ite e1 e2 e3 → p)
    (eq_case: ∀ (e1 e2: exp) (t1: typ), (e1 ::: t1) → (e2 ::: t1) → e = exp.eq e1 e2 → t = typ.bool → p): p :=
  begin
    induction e_typed_t,
    case typed.num n {
      exact num_case n rfl rfl
    },
    case typed.bool b {
      exact bool_case b rfl rfl
    },
    case typed.add e1 e2 e1_typed_num e2_typed_num {
      exact add_case e1 e2 e1_typed_num e2_typed_num rfl rfl
    },
    case typed.ite e1 e2 e3 t1 e1_typed_bool e2_typed_t e3_typed_t {
      exact ite_case e1 e2 e3 e1_typed_bool e2_typed_t e3_typed_t rfl
    },
    case typed.eq e1 e2 t1 e1_typed_t1 e2_typed_t1 {
      exact eq_case e1 e2 t1 e1_typed_t1 e2_typed_t1 rfl rfl
    }
  end

lemma add_is_not_value {e1 e2: exp} : ¬ is_value (exp.add e1 e2) :=
  assume add_is_value: is_value (exp.add e1 e2),
  is_value_cases add_is_value
  (  -- is value num
    assume n: ℕ,
    assume add_is_num: exp.add e1 e2 = exp.num n,
    show false, from exp.no_confusion add_is_num
  )
  (  -- is value bool
    assume b: bool,
    assume add_is_bool: exp.add e1 e2 = exp.bool b,
    show false, from exp.no_confusion add_is_bool
  )

lemma ite_is_not_value {e1 e2 e3: exp} : ¬ is_value (exp.ite e1 e2 e3) :=
  assume ite_is_value: is_value (exp.ite e1 e2 e3),
  is_value_cases ite_is_value
  (  -- is value num
    assume n: ℕ,
    assume add_is_num: exp.ite e1 e2 e3 = exp.num n,
    show false, from exp.no_confusion add_is_num
  )
  (  -- is value bool
    assume b: bool,
    assume add_is_bool: exp.ite e1 e2 e3 = exp.bool b,
    show false, from exp.no_confusion add_is_bool
  )

lemma eq_is_not_value {e1 e2: exp} : ¬ is_value (exp.eq e1 e2) :=
  assume eq_is_value: is_value (exp.eq e1 e2),
  is_value_cases eq_is_value
  (  -- is value num
    assume n: ℕ,
    assume add_is_num: exp.eq e1 e2 = exp.num n,
    show false, from exp.no_confusion add_is_num
  )
  (  -- is value bool
    assume b: bool,
    assume add_is_bool: exp.eq e1 e2 = exp.bool b,
    show false, from exp.no_confusion add_is_bool
  )

lemma value_typed_num_is_num {e: exp} (e_typed_num: e ::: typ.num) (e_is_value: is_value e): ∃n: ℕ, e = exp.num n :=
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
    have add_is_value: is_value (exp.add e1 e2), from e_is_add ▸ e_is_value,
    show ∃n: ℕ, e = exp.num n, from absurd add_is_value add_is_not_value
  )
  ( -- ite
    assume e1 e2 e3: exp,
    assume _ _ _,
    assume e_is_ite: e = exp.ite e1 e2 e3,
    have ite_is_value: is_value (exp.ite e1 e2 e3), from eq.subst e_is_ite e_is_value,
    show ∃n: ℕ, e = exp.num n, from absurd ite_is_value ite_is_not_value
  )
  ( -- eq
    assume e1 e2: exp,
    assume _ _ _,
    assume e_is_eq: e = exp.eq e1 e2,
    assume _,
    have eq_is_value: is_value (exp.eq e1 e2), from eq.subst e_is_eq e_is_value,
    show ∃n: ℕ, e = exp.num n, from absurd eq_is_value eq_is_not_value
  )

lemma value_typed_bool_is_true_or_false {e: exp} (e_typed_bool: e ::: typ.bool) (e_is_value: is_value e):
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
        left,
        show e = exp.bool tt, from e_is_bool
      },
      case ff {
        right,
        show e = exp.bool ff, from e_is_bool
      }
    end
  )
  ( -- add
    assume e1 e2: exp,
    assume _ _,
    assume e_is_add: e = exp.add e1 e2,
    assume _,
    have add_is_value: is_value (exp.add e1 e2), from eq.subst e_is_add e_is_value,
    show e = exp.bool true ∨ e = exp.bool false, from absurd add_is_value add_is_not_value
  )
  ( -- ite
    assume e1 e2 e3: exp,
    assume _ _ _,
    assume e_is_ite: e = exp.ite e1 e2 e3,
    have ite_is_value: is_value (exp.ite e1 e2 e3), from eq.subst e_is_ite e_is_value,
    show e = exp.bool true ∨ e = exp.bool false, from absurd ite_is_value ite_is_not_value
  )
  ( -- eq
    assume e1 e2: exp,
    assume _ _ _,
    assume e_is_eq: e = exp.eq e1 e2,
    assume _,
    have eq_is_value: is_value (exp.eq e1 e2), from eq.subst e_is_eq e_is_value,
    show e = exp.bool true ∨ e = exp.bool false, from absurd eq_is_value eq_is_not_value
  )

lemma bool_eq_bool_steps {e: exp} {b1 b2: bool} (e_is_eq: e = exp.eq (exp.bool b1) (exp.bool b2)):
  ∃e', e ⟶ e' :=
  have exp.eq (exp.bool b1) (exp.bool b2) ⟶ exp.bool (b1 = b2), from step.eq_bool,
  have ∃e', exp.eq (exp.bool b1) (exp.bool b2) ⟶ e', from exists.intro (exp.bool (b1 = b2)) this,
  show ∃e', e ⟶ e', from eq.symm e_is_eq ▸ this

theorem progress(e: exp) (t: typ) (e_typed_t: e ::: t): is_value e ∨ ∃e', e ⟶ e' :=
  typed.rec_on e_typed_t
  ( -- num
    assume n: ℕ,
    let e := exp.num n in
    have e_is_value: is_value e, from is_value.num,
    show is_value e ∨ ∃e', e ⟶ e', from or.inl e_is_value
  )
  ( -- bool
    assume b: bool,
    let e := exp.bool b in
    have e_is_value: is_value e, from is_value.bool,
    show is_value e ∨ ∃e', e ⟶ e', from or.inl e_is_value
  )
  ( -- add
    assume e1 e2: exp,
    assume e1_typed_num : e1 ::: typ.num,
    assume e2_typed_num : e2 ::: typ.num,
    assume e1ih: is_value e1 ∨ ∃e1', e1 ⟶ e1',
    assume e2ih: is_value e2 ∨ ∃e2', e2 ⟶ e2',
    let e := exp.add e1 e2 in
    have e_is_add: e = exp.add e1 e2, from rfl,
    have e_steps: ∃e', e ⟶ e', from or.elim e1ih
    (
      assume e1_is_value: is_value e1,
      or.elim e2ih (
        assume e2_is_value: is_value e2,
        have e1_exists_num: ∃n1: ℕ, e1 = exp.num n1, from value_typed_num_is_num e1_typed_num e1_is_value,
        have e2_exists_num: ∃n2: ℕ, e2 = exp.num n2, from value_typed_num_is_num e2_typed_num e2_is_value,
        let ⟨(n1: ℕ), (e1_is_num: e1 = exp.num n1)⟩ := e1_exists_num in
        let ⟨(n2: ℕ), (e2_is_num: e2 = exp.num n2)⟩ := e2_exists_num in
        have exp.add (exp.num n1) (exp.num n2) ⟶ exp.num (n1 + n2), from step.add,
        have e ⟶ exp.num (n1 + n2), from e_is_add.symm ▸ e1_is_num.symm ▸ e2_is_num.symm ▸ this,
        show ∃e', e ⟶ e', from exists.intro (exp.num (n1 + n2)) this
      )
      (
        assume e2_can_step: ∃e2', e2 ⟶ e2',
        exists.elim e2_can_step (
          assume e2': exp,
          assume e2_steps: e2 ⟶ e2',
          have e ⟶ exp.add e1 e2', from step.add_right e1_is_value e2_steps,
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
    assume e1_typed_bool: e1 ::: typ.bool,
    assume e2_typed_t: e2 ::: t,
    assume e3_typed_t: e3 ::: t,
    assume e1ih: is_value e1 ∨ ∃e1', e1 ⟶ e1',
    assume e2ih: is_value e2 ∨ ∃e2', e2 ⟶ e2',
    assume e3ih: is_value e3 ∨ ∃e3', e3 ⟶ e3',
    let e := exp.ite e1 e2 e3 in
    have e_is_ite: e = exp.ite e1 e2 e3, from rfl,
    have e_steps: ∃e', e ⟶ e', from or.elim e1ih
    ( -- is_value e1
      assume e1_is_value: is_value e1,
      have e1_is_bool: e1 = exp.bool true ∨ e1 = exp.bool false,
      from value_typed_bool_is_true_or_false e1_typed_bool e1_is_value,
      or.elim e1_is_bool
      ( -- ite-true
        assume e1_is_true: e1 = exp.bool true,
        have exp.ite (exp.bool true) e2 e3 ⟶ e2, from step.ite_true,
        have e ⟶ e2, from eq.substr e_is_ite (eq.substr e1_is_true this),
        show ∃e', e ⟶ e', from exists.intro e2 this
      )
      ( -- ite-false
        assume e1_is_false: e1 = exp.bool false,
        have exp.ite (exp.bool false) e2 e3 ⟶ e3, from step.ite_false,
        have e ⟶ e3, from eq.substr e_is_ite (eq.substr e1_is_false this),
        show ∃e', e ⟶ e', from exists.intro e3 this
      )
    )
    ( -- e1 steps
      assume e1_can_step: ∃e1', e1 ⟶ e1',
      exists.elim e1_can_step (
        assume e1': exp, 
        assume e1_steps: e1 ⟶ e1',
        have e ⟶ exp.ite e1' e2 e3, from step.ite e1_steps,
        show ∃e', e ⟶ e', from exists.intro (exp.ite e1' e2 e3) this
      )
    ),
    show is_value e ∨ ∃e', e ⟶ e', from or.inr e_steps
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
    have e_steps: ∃e', e ⟶ e', from or.elim e1ih (
      assume e1_is_value: is_value e1,
      or.elim e2ih (
        assume e2_is_value: is_value e2,
        typ_cases t
        ( -- num
          assume t_is_num: t = typ.num,
          have e1_typed_num: e1 ::: typ.num, from eq.subst t_is_num e1_typed_t,
          have e2_typed_num: e2 ::: typ.num, from eq.subst t_is_num e2_typed_t,
          have e1_exists_num: ∃n1: ℕ, e1 = exp.num n1, from value_typed_num_is_num e1_typed_num e1_is_value,
          have e2_exists_num: ∃n2: ℕ, e2 = exp.num n2, from value_typed_num_is_num e2_typed_num e2_is_value,
          exists.elim e1_exists_num (
            assume n1: ℕ,
            assume e1_is_num: e1 = exp.num n1,
            exists.elim e2_exists_num (
              assume n2: ℕ,
              assume e2_is_num: e2 = exp.num n2,
              have exp.eq (exp.num n1) (exp.num n2) ⟶ exp.bool (n1 = n2), from step.eq_num,
              have exp.eq e1 e2 ⟶ exp.bool (n1 = n2), from eq.substr e1_is_num (eq.substr e2_is_num this),
              have e ⟶ exp.bool (n1 = n2), from eq.substr e_is_eq this,
              show ∃e', e ⟶ e', from exists.intro (exp.bool (n1 = n2)) this
            )
          )
        )
        ( -- bool
          assume t_is_bool: t = typ.bool,
          have e1_typed_bool: e1 ::: typ.bool, from eq.subst t_is_bool e1_typed_t,
          have e2_typed_bool: e2 ::: typ.bool, from eq.subst t_is_bool e2_typed_t,
          have e1_some_bool: e1 = exp.bool true ∨ e1 = exp.bool false,
          from value_typed_bool_is_true_or_false e1_typed_bool e1_is_value,
          have e2_some_bool: e2 = exp.bool true ∨ e2 = exp.bool false,
          from value_typed_bool_is_true_or_false e2_typed_bool e2_is_value,
          or.elim e1_some_bool
          (
            assume e1_is_true: e1 = exp.bool true,
            or.elim e2_some_bool
            (
              assume e2_is_true: e2 = exp.bool true,
              have e_is_true_eq_true: e = exp.eq (exp.bool true) (exp.bool true),
              by { rw [e1_is_true, e2_is_true] at e_is_eq, assumption },
              show ∃e', e ⟶ e', from bool_eq_bool_steps e_is_true_eq_true
            )
            (
              assume e2_is_false: e2 = exp.bool false,
              have e_is_true_eq_false: e = exp.eq (exp.bool true) (exp.bool false),
              by { rw [e1_is_true, e2_is_false] at e_is_eq, assumption },
              show ∃e', e ⟶ e', from bool_eq_bool_steps e_is_true_eq_false
            )
          )
          (
            assume e1_is_false: e1 = exp.bool false,
            or.elim e2_some_bool
            (
              assume e2_is_true: e2 = exp.bool true,
              have e_is_false_eq_true: e = exp.eq (exp.bool false) (exp.bool true),
              by { rw [e1_is_false, e2_is_true] at e_is_eq, assumption },
              show ∃e', e ⟶ e', from bool_eq_bool_steps e_is_false_eq_true
            )
            (
              assume e2_is_false: e2 = exp.bool false,
              have e_is_false_eq_false: e = exp.eq (exp.bool false) (exp.bool false),
              by { rw [e1_is_false, e2_is_false] at e_is_eq, assumption },
              show ∃e', e ⟶ e', from bool_eq_bool_steps e_is_false_eq_false
            )
          )
        )
      )
      (
        assume e2_can_step: ∃e2', e2 ⟶ e2',
        exists.elim e2_can_step (λe2', 
          assume e2_steps: e2 ⟶ e2',
          have e ⟶ exp.eq e1 e2', from step.eq_right e1_is_value e2_steps,
          show ∃e', e ⟶ e', from exists.intro (exp.eq e1 e2') this
        )
      )
    )
    (
      assume e1_can_step: ∃e1', e1 ⟶ e1',
      exists.elim e1_can_step (λe1', 
        assume e1_steps: e1 ⟶ e1',
        have e ⟶ exp.eq e1' e2, from step.eq_left e1_steps,
        show ∃e', e ⟶ e', from exists.intro (exp.eq e1' e2) this
      )
    ),
    show is_value e ∨ ∃e', e ⟶ e', from or.inr e_steps
  )

lemma values_not_step {e: exp} (e_is_value: is_value e): ¬ ∃e', e ⟶ e' :=
  assume e_steps: ∃e', e ⟶ e',
  have e_is_not_value: ¬ is_value e, from exists.elim e_steps (
    assume e': exp,
    assume e_steps_to_e': e ⟶ e',
    step_cases e_steps_to_e'
    ( -- add_case
      assume n1 n2: ℕ,
      assume e_is_add: e = exp.add (exp.num n1) (exp.num n2),
      assume _,
      have  ¬ is_value (exp.add (exp.num n1) (exp.num n2)), from add_is_not_value,
      show ¬ is_value e, from e_is_add.symm ▸ this
    )
    ( -- add_right_case
      assume e1 e2 e2': exp,
      assume _ _,
      assume e_is_add: e = exp.add e1 e2,
      assume _,
      have  ¬ is_value (exp.add e1 e2), from add_is_not_value,
      show ¬ is_value e, by { rw [←e_is_add] at this, assumption }
    )
    ( -- add_left_case
      assume e1 e1' e2: exp,
      assume _,
      assume e_is_add: e = exp.add e1 e2,
      assume _,
      have  ¬ is_value (exp.add e1 e2), from add_is_not_value,
      show ¬ is_value e, by { rw [←e_is_add] at this, assumption }
    )
    ( -- ite_true_case
      assume e2 e3: exp,
      assume e_is_ite: e = exp.ite (exp.bool true) e2 e3,
      assume _,
      have  ¬ is_value (exp.ite (exp.bool true) e2 e3), from ite_is_not_value,
      show ¬ is_value e, by { rw [←e_is_ite] at this, assumption }
    )
    ( -- ite_false_case
      assume e2 e3: exp,
      assume e_is_ite: e = exp.ite (exp.bool false) e2 e3,
      assume _,
      have  ¬ is_value (exp.ite (exp.bool false) e2 e3), from ite_is_not_value,
      show ¬ is_value e, by { rw [←e_is_ite] at this, assumption }
    )
    ( -- ite_case
      assume e1 e1' e2 e3: exp,
      assume _,
      assume e_is_ite: e = exp.ite e1 e2 e3,
      assume _,
      have  ¬ is_value (exp.ite e1 e2 e3), from ite_is_not_value,
      show ¬ is_value e, by { rw [←e_is_ite] at this, assumption }
    )
    ( -- eq_num_case
      assume n1 n2: ℕ,
      assume e_is_eq: e = exp.eq (exp.num n1) (exp.num n2),
      assume _,
      have  ¬ is_value (exp.eq (exp.num n1) (exp.num n2)), from eq_is_not_value,
      show ¬ is_value e, by { rw [←e_is_eq] at this, assumption }
    )
    ( -- eq_bool_case
      assume b1 b2: bool,
      assume e_is_eq: e = exp.eq (exp.bool b1) (exp.bool b2),
      assume _,
      have  ¬ is_value (exp.eq (exp.bool b1) (exp.bool b2)), from eq_is_not_value,
      show ¬ is_value e, by { rw [←e_is_eq] at this, assumption }
    )
    ( -- eq_right_case
      assume e1 e2 e2': exp,
      assume _ _,
      assume e_is_eq: e = exp.eq e1 e2,
      assume _,
      have  ¬ is_value (exp.eq e1 e2), from eq_is_not_value,
      show ¬ is_value e, by { rw [←e_is_eq] at this, assumption }
    )
    ( -- eq_left_case
      assume e1 e1' e2: exp,
      assume _,
      assume e_is_eq: e = exp.eq e1 e2,
      assume _,
      have  ¬ is_value (exp.eq e1 e2), from eq_is_not_value,
      show ¬ is_value e, by { rw [←e_is_eq] at this, assumption }
    )
  ),
  show false, from absurd e_is_value e_is_not_value

lemma add_step_cases {p: Prop} {e1 e2 e': exp} (add_steps: exp.add e1 e2 ⟶ e')
    (add_case: ∀ (n1 n2: ℕ), e1 = exp.num n1 → e2 = exp.num n2 → e' = exp.num (n1+n2) → p)
    (add_right_case: ∀e2': exp, is_value e1 → (e2 ⟶ e2') → e' = exp.add e1 e2' → p)
    (add_left_case: ∀e1': exp, (e1 ⟶ e1') → e' = exp.add e1' e2 → p): p :=
  step_cases add_steps
  ( -- add_case
    assume n1 n2: ℕ,
    assume add_is_add: exp.add e1 e2 = exp.add (exp.num n1) (exp.num n2),
    assume e'_is_num: e' = exp.num (n1 + n2),
    have e1_is_num_n1: e1 = exp.num n1, from and.elim_left (exp.add.inj add_is_add),
    have e2_is_num_n2: e2 = exp.num n2, from and.elim_right (exp.add.inj add_is_add),
    show p, from add_case n1 n2 e1_is_num_n1 e2_is_num_n2 e'_is_num
  )
  ( -- add_right_case
    assume e1_ e2_ e2': exp,
    assume e1__is_value: is_value e1_,
    assume e2__steps: e2_ ⟶ e2',
    assume add_is_add: exp.add e1 e2 = exp.add e1_ e2_,
    assume e'_is_add_: e' = exp.add e1_ e2',
    have e1_is_e1_: e1 = e1_, from and.elim_left (exp.add.inj add_is_add),
    have e2_is_e2_: e2 = e2_, from and.elim_right (exp.add.inj add_is_add),
    have e1_is_value: is_value e1, by { rw[←e1_is_e1_] at e1__is_value, assumption },
    have e2_steps: e2 ⟶ e2', by { rw[←e2_is_e2_] at e2__steps, assumption },
    have e'_is_add: e' = exp.add e1 e2', by { rw[←e1_is_e1_] at e'_is_add_, assumption },
    show p, from add_right_case e2' e1_is_value e2_steps e'_is_add
  )
  ( -- add_left_case
    assume e1_ e1' e2_: exp,
    assume e1__steps: e1_ ⟶ e1',
    assume add_is_add: exp.add e1 e2 = exp.add e1_ e2_,
    assume e'_is_add_: e' = exp.add e1' e2_,
    have e1_is_e1_: e1 = e1_, from and.elim_left (exp.add.inj add_is_add),
    have e2_is_e2_: e2 = e2_, from and.elim_right (exp.add.inj add_is_add),
    have e1_steps: e1 ⟶ e1', by { rw[←e1_is_e1_] at e1__steps, assumption },
    have e'_is_add: e' = exp.add e1' e2, by { rw[←e2_is_e2_] at e'_is_add_, assumption },
    show p, from add_left_case e1' e1_steps e'_is_add
  )
  ( -- ite_true_case
    assume e2_ e3_: exp,
    assume add_is_ite: exp.add e1 e2 = exp.ite (exp.bool true) e2_ e3_,
    assume _,
    show p, from exp.no_confusion add_is_ite
  )
  ( -- ite_false_case
    assume e2_ e3_: exp,
    assume add_is_ite: exp.add e1 e2 = exp.ite (exp.bool false) e2_ e3_,
    assume _,
    show p, from exp.no_confusion add_is_ite
  )
  ( -- ite_case
    assume e1_ _ e2_ e3_: exp,
    assume _,
    assume add_is_ite: exp.add e1 e2 = exp.ite e1_ e2_ e3_,
    assume _,
    show p, from exp.no_confusion add_is_ite
  )
  ( -- eq_num_case
    assume n1 n2: ℕ,
    assume add_is_eq: exp.add e1 e2 = exp.eq (exp.num n1) (exp.num n2),
    assume _,
    show p, from exp.no_confusion add_is_eq
  )
  ( -- eq_bool_case
    assume b1 b2: bool,
    assume add_is_eq: exp.add e1 e2 = exp.eq (exp.bool b1) (exp.bool b2),
    assume _,
    show p, from exp.no_confusion add_is_eq
  )
  ( -- eq_right_case
    assume e1_ e2_ _: exp,
    assume _ _,
    assume add_is_eq: exp.add e1 e2 = exp.eq e1_ e2_,
    assume _,
    show p, from exp.no_confusion add_is_eq
  )
  ( -- eq_left_case
    assume e1_ _ e2_: exp,
    assume _,
    assume add_is_eq: exp.add e1 e2 = exp.eq e1_ e2_,
    assume _,
    show p, from exp.no_confusion add_is_eq
  )

lemma ite_step_cases {p: Prop} {e1 e2 e3 e': exp} (ite_steps: exp.ite e1 e2 e3 ⟶ e')
    (ite_true_case: e1 = exp.bool true → e' = e2 → p)
    (ite_false_case: e1 = exp.bool false → e' = e3 → p)
    (ite_case: ∀e1': exp, (e1 ⟶ e1') → e' = exp.ite e1' e2 e3 → p): p :=
  step_cases ite_steps
  ( -- add_case
    assume n1 n2: ℕ,
    assume ite_is_add: exp.ite e1 e2 e3 = exp.add (exp.num n1) (exp.num n2),
    assume _,
    show p, from exp.no_confusion ite_is_add
  )
  ( -- add_right_case
    assume e1_ e2_ _: exp,
    assume _ _,
    assume ite_is_add: exp.ite e1 e2 e3 = exp.add e1_ e2_,
    assume _,
    show p, from exp.no_confusion ite_is_add
  )
  ( -- add_left_case
    assume e1_ _ e2_: exp,
    assume _,
    assume ite_is_add: exp.ite e1 e2 e3 = exp.add e1_ e2_,
    assume _,
    show p, from exp.no_confusion ite_is_add
  )
  ( -- ite_true_case
    assume e2_ e3_: exp,
    assume ite_is_ite: exp.ite e1 e2 e3 = exp.ite (exp.bool true) e2_ e3_,
    assume e'_is_e2_: e' = e2_,
    have e1_is_true: e1 = exp.bool true, from and.elim_left (exp.ite.inj ite_is_ite),
    have e2_is_e2_: e2 = e2_, from and.elim_left (and.elim_right (exp.ite.inj ite_is_ite)),
    have e'_is_e2: e' = e2, by { rw[←e2_is_e2_] at e'_is_e2_, assumption },
    show p, from ite_true_case e1_is_true e'_is_e2
  )
  ( -- ite_false_case
    assume e2_ e3_: exp,
    assume ite_is_ite: exp.ite e1 e2 e3 = exp.ite (exp.bool false) e2_ e3_,
    assume e'_is_e3_: e' = e3_,
    have e1_is_false: e1 = exp.bool false, from and.elim_left (exp.ite.inj ite_is_ite),
    have e3_is_e3_: e3 = e3_, from and.elim_right (and.elim_right (exp.ite.inj ite_is_ite)),
    have e'_is_e3: e' = e3, by { rw[←e3_is_e3_] at e'_is_e3_, assumption },
    show p, from ite_false_case e1_is_false e'_is_e3
  )
  ( -- ite_case
    assume e1_ e1' e2_ e3_: exp,
    assume e1__steps: e1_ ⟶ e1',
    assume ite_is_ite: exp.ite e1 e2 e3 = exp.ite e1_ e2_ e3_,
    assume e'_is_ite_: e' = exp.ite e1' e2_ e3_,
    have e1_is_e1_: e1 = e1_, from and.elim_left (exp.ite.inj ite_is_ite),
    have e2_is_e2_: e2 = e2_, from and.elim_left (and.elim_right (exp.ite.inj ite_is_ite)),
    have e3_is_e3_: e3 = e3_, from and.elim_right (and.elim_right (exp.ite.inj ite_is_ite)),
    have e1_steps: e1 ⟶ e1', by { rw[←e1_is_e1_] at e1__steps, assumption },
    have e'_is_ite: e' = exp.ite e1' e2 e3, by { rw[←e2_is_e2_, ←e3_is_e3_] at e'_is_ite_, assumption },
    show p, from ite_case e1' e1_steps e'_is_ite
  )
  ( -- eq_num_case
    assume n1 n2: ℕ,
    assume ite_is_eq: exp.ite e1 e2 e3 = exp.eq (exp.num n1) (exp.num n2),
    assume _,
    show p, from exp.no_confusion ite_is_eq
  )
  ( -- eq_bool_case
    assume b1 b2: bool,
    assume ite_is_eq: exp.ite e1 e2 e3 = exp.eq (exp.bool b1) (exp.bool b2),
    assume _,
    show p, from exp.no_confusion ite_is_eq
  )
  ( -- eq_right_case
    assume e1_ e2_ _: exp,
    assume _ _,
    assume ite_is_eq: exp.ite e1 e2 e3 = exp.eq e1_ e2_,
    assume _,
    show p, from exp.no_confusion ite_is_eq
  )
  ( -- eq_left_case
    assume e1_ _ e2_: exp,
    assume _,
    assume ite_is_eq: exp.ite e1 e2 e3 = exp.eq e1_ e2_,
    assume _,
    show p, from exp.no_confusion ite_is_eq
  )

lemma eq_step_cases {p: Prop} {e1 e2 e': exp} (eq_steps: exp.eq e1 e2 ⟶ e')
    (eq_num_case: ∀ (n1 n2: ℕ), e1 = exp.num n1 → e2 = exp.num n2 → e' = exp.bool (n1 = n2) → p)
    (eq_bool_case: ∀ (b1 b2: bool), e1 = exp.bool b1 → e2 = exp.bool b2 → e' = exp.bool (b1 = b2) → p)
    (eq_right_case: ∀e2': exp, is_value e1 → (e2 ⟶ e2') → e' = exp.eq e1 e2' → p)
    (eq_left_case: ∀e1': exp, (e1 ⟶ e1') → e' = exp.eq e1' e2 → p): p :=
  step_cases eq_steps
  ( -- add_case
    assume n1 n2: ℕ,
    assume eq_is_add: exp.eq e1 e2 = exp.add (exp.num n1) (exp.num n2),
    assume _,
    show p, from exp.no_confusion eq_is_add
  )
  ( -- add_right_case
    assume e1_ e2_ _: exp,
    assume _ _,
    assume eq_is_add: exp.eq e1 e2 = exp.add e1_ e2_,
    assume _,
    show p, from exp.no_confusion eq_is_add
  )
  ( -- add_left_case
    assume e1_ _ e2_: exp,
    assume _,
    assume eq_is_add: exp.eq e1 e2 = exp.add e1_ e2_,
    assume _,
    show p, from exp.no_confusion eq_is_add
  )
  ( -- ite_true_case
    assume e2_ e3_: exp,
    assume eq_is_ite: exp.eq e1 e2 = exp.ite (exp.bool true) e2_ e3_,
    assume _,
    show p, from exp.no_confusion eq_is_ite
  )
  ( -- ite_false_case
    assume e2_ e3_: exp,
    assume eq_is_ite: exp.eq e1 e2 = exp.ite (exp.bool false) e2_ e3_,
    assume _,
    show p, from exp.no_confusion eq_is_ite
  )
  ( -- ite_case
    assume e1_ _ e2_ e3_: exp,
    assume _,
    assume eq_is_ite: exp.eq e1 e2 = exp.ite e1_ e2_ e3_,
    assume _,
    show p, from exp.no_confusion eq_is_ite
  )
  ( -- eq_num_case
    assume n1 n2: ℕ,
    assume eq_is_eq: exp.eq e1 e2 = exp.eq (exp.num n1) (exp.num n2),
    assume e'_is_num: e' = exp.bool (n1 = n2),
    have e1_is_num_n1: e1 = exp.num n1, from and.elim_left (exp.eq.inj eq_is_eq),
    have e2_is_num_n2: e2 = exp.num n2, from and.elim_right (exp.eq.inj eq_is_eq),
    show p, from eq_num_case n1 n2 e1_is_num_n1 e2_is_num_n2 e'_is_num
  )
  ( -- eq_bool_case
    assume b1 b2: bool,
    assume eq_is_eq: exp.eq e1 e2 = exp.eq (exp.bool b1) (exp.bool b2),
    assume e'_is_num: e' = exp.bool (b1 = b2),
    have e1_is_num_n1: e1 = exp.bool b1, from and.elim_left (exp.eq.inj eq_is_eq),
    have e2_is_num_n2: e2 = exp.bool b2, from and.elim_right (exp.eq.inj eq_is_eq),
    show p, from eq_bool_case b1 b2 e1_is_num_n1 e2_is_num_n2 e'_is_num
  )
  ( -- eq_right_case
    assume e1_ e2_ e2': exp,
    assume e1__is_value: is_value e1_,
    assume e2__steps: e2_ ⟶ e2',
    assume e_is_eq: exp.eq e1 e2 = exp.eq e1_ e2_,
    assume e'_is_eq_: e' = exp.eq e1_ e2',
    have e1_is_e1_: e1 = e1_, from and.elim_left (exp.eq.inj e_is_eq),
    have e2_is_e2_: e2 = e2_, from and.elim_right (exp.eq.inj e_is_eq),
    have e1_is_value: is_value e1, by { rw[←e1_is_e1_] at e1__is_value, assumption },
    have e2_steps: e2 ⟶ e2', by { rw[←e2_is_e2_] at e2__steps, assumption },
    have e'_is_eq: e' = exp.eq e1 e2', by { rw[←e1_is_e1_] at e'_is_eq_, assumption },
    show p, from eq_right_case e2' e1_is_value e2_steps e'_is_eq
  )
  ( -- eq_left_case
    assume e1_ e1' e2_: exp,
    assume e1__steps: e1_ ⟶ e1',
    assume e_is_eq: exp.eq e1 e2 = exp.eq e1_ e2_,
    assume e'_is_eq_: e' = exp.eq e1' e2_,
    have e1_is_e1_: e1 = e1_, from and.elim_left (exp.eq.inj e_is_eq),
    have e2_is_e2_: e2 = e2_, from and.elim_right (exp.eq.inj e_is_eq),
    have e1_steps: e1 ⟶ e1', by { rw[←e1_is_e1_] at e1__steps, assumption },
    have e'_is_eq: e' = exp.eq e1' e2, by { rw[←e2_is_e2_] at e'_is_eq_, assumption },
    show p, from eq_left_case e1' e1_steps e'_is_eq
  )

theorem preservation(e: exp) (t: typ) (e_typed_t: e ::: t): (∀e': exp, e ⟶ e' → (e' ::: t)) :=
  typed.rec_on e_typed_t
  ( -- num
    assume n: ℕ,
    let e := exp.num n in
    let t := typ.num in
    assume e': exp,
    assume e_steps: e ⟶ e',
    have e_can_step: (∃e', e ⟶ e'), from exists.intro e' e_steps,
    have e_is_value: is_value e, from is_value.num,
    show e' ::: t, from absurd e_can_step (values_not_step e_is_value)
  )
  ( -- bool
    assume b: bool,
    let e := exp.bool b in
    let t := typ.bool in
    assume e': exp,
    assume e_steps: e ⟶ e',
    have e_can_step: (∃e', e ⟶ e'), from exists.intro e' e_steps,
    have e_is_value: is_value e, from is_value.bool,
    show e' ::: t, from absurd e_can_step (values_not_step e_is_value)
  )
  ( -- add
    assume e1 e2: exp,
    let e := exp.add e1 e2 in
    let t := typ.num in
    assume e1_typed_num : e1 ::: typ.num,
    assume e2_typed_num : e2 ::: typ.num,
    assume e1ih: (∀e1': exp, e1 ⟶ e1' → (e1' ::: typ.num)),
    assume e2ih: (∀e2': exp, e2 ⟶ e2' → (e2' ::: typ.num)),
    assume e': exp,
    assume e_steps: e ⟶ e',
    have e_is_add: e = exp.add e1 e2, from rfl,
    have exp.add e1 e2 ⟶ e', by { rw[e_is_add] at e_steps, assumption },
    add_step_cases this
    ( -- add_case
      assume n1 n2: ℕ,
      assume e1_is_num_n1: e1 = exp.num n1,
      assume e2_is_num_n2: e2 = exp.num n2,
      assume e'_is_num: e' = exp.num (n1 + n2),
      have exp.num (n1 + n2) ::: typ.num, from typed.num,
      show e' ::: t, by { rw[←e'_is_num] at this, assumption }
    )
    ( -- add_right_case
      assume e2': exp,
      assume e1_is_value: is_value e1,
      assume e2_steps: e2 ⟶ e2',
      assume e'_is_add: e' = exp.add e1 e2',
      have e2'_typed_num: e2' ::: typ.num, from e2ih e2' e2_steps,
      have exp.add e1 e2' ::: typ.num, from typed.add e1_typed_num e2'_typed_num,
      show e' ::: t, by { rw[←e'_is_add] at this, assumption }
    )
    ( -- add_left_case
      assume e1': exp,
      assume e1_steps: e1 ⟶ e1',
      assume e'_is_add: e' = exp.add e1' e2,
      have e1'_typed_num: e1' ::: typ.num, from e1ih e1' e1_steps,
      have exp.add e1' e2 ::: typ.num, from typed.add e1'_typed_num e2_typed_num,
      show e' ::: t, by { rw[←e'_is_add] at this, assumption }
    )
  )
  ( -- ite
    assume e1 e2 e3: exp,
    let e := exp.ite e1 e2 e3 in
    assume t: typ,
    assume e1_is_bool: e1 ::: typ.bool,
    assume e2_typed_t: e2 ::: t,
    assume e3_typed_t: e3 ::: t,
    assume e1ih: (∀e1': exp, e1 ⟶ e1' → (e1' ::: typ.bool)),
    assume e2ih: (∀e2': exp, e2 ⟶ e2' → (e2' ::: t)),
    assume e3ih: (∀e3': exp, e3 ⟶ e3' → (e3' ::: t)),
    assume e': exp,
    assume e_steps: e ⟶ e',
    have e_is_ite: e = exp.ite e1 e2 e3, from rfl,
    have exp.ite e1 e2 e3 ⟶ e', by { rw[e_is_ite] at e_steps, assumption },
    ite_step_cases this
    ( -- ite_true_case
      assume e1_is_true: e1 = exp.bool true,
      assume e'_is_e2: e' = e2,
      show e' ::: t, by { rw[←e'_is_e2] at e2_typed_t, assumption } 
    )
    ( -- ite_false_case
      assume e1_is_false: e1 = exp.bool false,
      assume e'_is_e3: e' = e3,
      show e' ::: t, by { rw[←e'_is_e3] at e3_typed_t, assumption } 
    )
    ( -- ite_case
      assume e1': exp,
      assume e1_steps: e1 ⟶ e1',
      assume e'_is_ite: e' = exp.ite e1' e2 e3,
      have e1'_typed_bool: e1' ::: typ.bool, from e1ih e1' e1_steps,
      have exp.ite e1' e2 e3 ::: t, from typed.ite e1'_typed_bool e2_typed_t e3_typed_t,
      show e' ::: t, by { rw[←e'_is_ite] at this, assumption }
    )
  )
  ( -- eq
    assume e1 e2: exp,
    assume t1: typ,
    let e := exp.eq e1 e2 in
    let t := typ.bool in
    assume e1_typed_t1 : e1 ::: t1,
    assume e2_typed_t1 : e2 ::: t1,
    assume e1ih: (∀e1': exp, e1 ⟶ e1' → (e1' ::: t1)),
    assume e2ih: (∀e2': exp, e2 ⟶ e2' → (e2' ::: t1)),
    assume e': exp,
    assume e_steps: e ⟶ e',
    have e_is_eq: e = exp.eq e1 e2, from rfl,
    have exp.eq e1 e2 ⟶ e', by { rw[e_is_eq] at e_steps, assumption },
    eq_step_cases this
    ( -- eq_num_case
      assume n1 n2: ℕ,
      assume _ _,
      assume e'_is_bool: e' = exp.bool (n1 = n2),
      have exp.bool (n1 = n2) ::: typ.bool, from typed.bool,
      show e' ::: t, by { rw[←e'_is_bool] at this, assumption }
    )
    ( -- eq_bool_case
      assume b1 b2: bool,
      assume _ _,
      assume e'_is_bool: e' = exp.bool (b1 = b2),
      have exp.bool (b1 = b2) ::: typ.bool, from typed.bool,
      show e' ::: t, by { rw[←e'_is_bool] at this, assumption }
    )
    ( -- eq_right_case
      assume e2': exp,
      assume e1_is_value: is_value e1,
      assume e2_steps: e2 ⟶ e2',
      assume e'_is_eq: e' = exp.eq e1 e2',
      have e2'_typed_t1: e2' ::: t1, from e2ih e2' e2_steps,
      have exp.eq e1 e2' ::: typ.bool, from typed.eq e1_typed_t1 e2'_typed_t1,
      show e' ::: t, by { rw[←e'_is_eq] at this, assumption }
    )
    ( -- eq_left_case
      assume e1': exp,
      assume e1_steps: e1 ⟶ e1',
      assume e'_is_eq: e' = exp.eq e1' e2,
      have e1'_typed_t1: e1' ::: t1, from e1ih e1' e1_steps,
      have exp.eq e1' e2 ::: typ.bool, from typed.eq e1'_typed_t1 e2_typed_t1,
      show e' ::: t, by { rw[←e'_is_eq] at this, assumption }
    )
  )

theorem does_not_get_stuck {e e': exp} (e_steps: e ⟶* e'): ∀t: typ, e ::: t → is_value e' ∨ ∃e'', e' ⟶ e'' :=
  trans_step.rec_on e_steps
  ( -- e
    assume e: exp,
    assume t: typ,
    assume e_typed_t: e ::: t,
    show is_value e ∨ ∃e', e ⟶ e', from progress e t e_typed_t
  )
  (
    assume e e' e'': exp,
    assume e_step: e ⟶ e',
    assume e'_steps: e' ⟶* e'',
    assume ih: ∀t': typ, e' ::: t' → is_value e'' ∨ ∃e''', e'' ⟶ e''',
    assume t: typ,
    assume e_typed_t: e ::: t,
    have e'_typed_t: e' ::: t, from preservation e t e_typed_t e' e_step,
    show is_value e'' ∨ ∃e''', e'' ⟶ e''', from ih t e'_typed_t
  )

end arith