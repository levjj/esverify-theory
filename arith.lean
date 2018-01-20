-- this defines a typed language arith and proves that its type system is sound

section arith

inductive typ : Type
  | numt : typ
  | boolt : typ

instance : decidable_eq typ := by tactic.mk_dec_eq_instance

inductive val : Type
  | numv : ℕ → val
  | boolv : bool → val


inductive exp : Type
  | value : val → exp
  | add : exp → exp → exp
  | ite : exp → exp → exp → exp
  | eq : exp → exp → exp

open typ
open val
open exp

def is_val (e: exp): Prop := ∃v: val, e = value v

def step : exp → option exp
  | (add (value (numv v1)) (value (numv v2))) :=
      some (value (numv (v1 + v2)))
  | (add (value v1) e2) :=
      do e2' ← step e2,
         return $ add (value v1) e2'
  | (add e1 e2) :=
      do e1' ← step e1,
         return $ add e1' e2
  | (ite (value (boolv tt)) e1 e2) :=
      some e1
  | (ite (value (boolv ff)) e1 e2) :=
      some e2
  | (ite e1 e2 e3) :=
      do e1' ← step e1,
         return $ (ite e1 e2 e3)
  | (eq (value (numv v1)) (value (numv v2))) :=
      some (value (boolv (v1 = v2)))
  | (eq (value (boolv b1)) (value (boolv b2))) :=
      some (value (boolv (b1 = b2)))
  | (eq (value v1) e2) :=
      do e2' ← step e2,
         return $ eq (value v1) e2'
  | (eq e1 e2) :=
      do e1' ← step e1,
         return $ eq e1' e2
  | _ :=
      none

reserve infixl `:::`:50

inductive typed : exp → typ → Prop
  | t_num (n: ℕ) : typed (value (numv n)) numt
  | t_bool (b: bool) : typed (value (boolv b)) boolt
  | t_add (e1 e2: exp) : typed e1 numt → typed e2 numt → typed (add e1 e2) numt
  | t_ite (e1 e2 e3: exp) {t: typ} : typed e1 boolt → typed e2 t → typed e3 t → typed (ite e1 e2 e3) t
  | t_eq (e1 e2: exp) {t: typ} : typed e1 t → typed e2 t → typed (eq e1 e2) boolt

infixl `:::` := typed

theorem progress(e: exp) (t: typ) (is_typed: typed e t): is_val e ∨ step e ≠ none :=
  exp.rec_on e
    (
      assume v: val,
      let e := value v in
      have e_is_val: is_val e, from exists.intro v rfl,
      show is_val e ∨ step e ≠ none, from or.inl e_is_val
    )
    (
      assume e1 e2: exp,
      assume e1ih: is_val e1 ∨ step e1 ≠ none,
      assume e2ih: is_val e2 ∨ step e2 ≠ none,
      let e := add e1 e2 in
      or.elim e1ih (
        assume e1_is_val: is_val e1,
        or.elim e2ih (
          assume e2_is_val: is_val e2,

          show is_val e ∨ step e ≠ none, from sorry
        ) (
          assume e2_can_step: step e2 ≠ none,
          show is_val e ∨ step e ≠ none, from sorry
        )
      ) (
        assume e1_can_step: step e1 ≠ none,
        show is_val e ∨ step e ≠ none, from sorry
      )
    )
    (
      assume e1 e2 e3: exp,
      assume e1ih: is_val e1 ∨ step e1 ≠ none,
      assume e2ih: is_val e2 ∨ step e2 ≠ none,
      assume e3ih: is_val e3 ∨ step e3 ≠ none,
      let e := ite e1 e2 e3 in
      show is_val e ∨ step e ≠ none, from sorry
    )
    (
      assume e1 e2: exp,
      assume e1ih: is_val e1 ∨ step e1 ≠ none,
      assume e2ih: is_val e2 ∨ step e2 ≠ none,
      let e := exp.eq e1 e2 in
      show is_val e ∨ step e ≠ none, from sorry
    )

end arith