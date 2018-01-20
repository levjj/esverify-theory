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

def typee : exp → option typ
  | (value (boolv _)) := some boolt
  | (value (numv _)) := some numt
  | (add e1 e2) :=
      do e1typ: typ ← typee e1,
         e2typ: typ ← typee e2,
         match (e1typ, e2typ) with
           | (numt, numt) := some numt
           | _ := none
         end
  | (ite e1 e2 e3) :=
      do e1typ: typ ← typee e1,
         e2typ: typ ← typee e2,
         e3typ: typ ← typee e3,
         guard $ e1typ = boolt,
         guard $ e2typ = e3typ,
         some e2typ
  | (eq e1 e2) :=
      do e1typ: typ ← typee e1,
         e2typ: typ ← typee e2,
         match (e1typ, e2typ) with
           | (numt, numt) := some boolt
           | (boolt, boolt) := some boolt
           | _ := none
         end

-- lemma add_is_numt(e1 e2: exp): typee (add e1 e2) = none ∨ typee (add e1 e2) = some numt :=
--   by_cases
  -- let t_or_none := typee (add e1 e2) in
  -- option.cases_on t_or_none (
  --   have is_none: typee (add e1 e2) = none, from sorry,
  --   show t_or_none = none ∨ typee (add e1 e2) = some numt, from or.inl is_none
  -- ) (
  --   assume t: typ,
  --   have is_num: typee (add e1 e2) = some numt, from sorry,
  --   show t_or_none = none ∨ t_or_none = some numt, from or.inr is_num
  -- )

def typee_add_inv(e1 e2: exp) (add_is_typed: typee (add e1 e2) ≠ none): typee e1 ≠ none :=
  sorry

theorem progress(e: exp) (t: typ) (is_typed: some t = typee e): is_val e ∨ step e ≠ none :=
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