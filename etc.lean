import data.set

-- auxiliary lemmas for nat

lemma nonneg_of_nat {n: ℕ}: 0 ≤ n := nat.rec_on n
  (show 0 ≤ 0, by refl)
  (λn zero_lt_n, show 0 ≤ n + 1, from le_add_of_le_of_nonneg zero_lt_n zero_le_one)

lemma lt_of_add_one {n: ℕ}: n < n + 1 :=
  have n ≤ n, by refl,
  show n < n + 1, from lt_add_of_le_of_pos this zero_lt_one

lemma lt_of_add {n m: ℕ}: n < n + m + 1 ∧ m < n + m + 1 :=
  have n_nonneg: 0 ≤ n, from nonneg_of_nat,
  have m_nonneg: 0 ≤ m, from nonneg_of_nat,
  have n ≤ n, by refl,
  have n ≤ n + m, from le_add_of_le_of_nonneg this m_nonneg,
  have h₁: n < n + m + 1, from lt_add_of_le_of_pos this zero_lt_one,
  have m ≤ m, by refl,
  have m ≤ m + n, from le_add_of_le_of_nonneg this n_nonneg,
  have m ≤ n + m, by { rw[add_comm], assumption },
  have h₂: m < n + m + 1, from lt_add_of_le_of_pos this zero_lt_one,
  ⟨h₁, h₂⟩

-- other auxiliary lemmas

lemma some.inj.inv {α: Type} {a b: α}: a = b → (some a = some b) :=
  assume : a = b,
  by simp * at *

lemma is_none.inv {α: Type} (a: option α): option.is_none a ↔ (a = none) :=
  begin
    cases a,
    case option.some v {
      split,
      assume is_none_some,
      contradiction,
      assume is_none_some,
      contradiction,
    },
    case option.none {
      split,
      assume is_none_none,
      exact rfl,
      assume is_none_none,
      exact rfl
    }
  end

lemma not_is_none.inv {α: Type} (a: option α): ¬ option.is_none a → (a ≠ none) :=
  assume is_not_none: ¬ option.is_none a,
  begin
    cases a,
    case option.some v {
      assume is_none_some,
      contradiction
    },
    case option.none {
      assume is_none_none,
      have : (option.is_none none = tt), by unfold option.is_none,
      contradiction
    }
  end

lemma not_is_none.rinv {α: Type} {a: option α}: (∃b, a = some b) ↔ ¬ option.is_none a :=
  begin
    split,
    cases a,
    assume c,
    cases c,
    contradiction,
    assume _,
    unfold option.is_none,
    apply ff_eq_tt_eq_false,
    assume _,
    cases a,
    case option.some v {
      exact exists.intro v rfl
    },
    case option.none {
      have : (option.is_none none = tt), by unfold option.is_none,
      contradiction
    }
  end

lemma mem_of_2set {α: Type} {a b c: α}:
  a ∈ ({b, c}: set α) -> (a = b) ∨ (a = c) :=
  assume a_in_bc: a ∈ {b, c},
  have a_in_bc: a ∈ insert b (insert c (∅: set α)), by { simp * at * },
  have a = b ∨ a ∈ insert c ∅, from set.eq_or_mem_of_mem_insert a_in_bc,
  or.elim this (
    assume : a = b,
    show (a = b) ∨ (a = c), from or.inl this
  ) (
    assume : a ∈ insert c ∅,
    have a = c ∨ a ∈ ∅, from set.eq_or_mem_of_mem_insert this,
    or.elim this (
      assume : a = c,
      show (a = b) ∨ (a = c), from or.inr this
    ) (
      assume : a ∈ ∅,
      show (a = b) ∨ (a = c), from absurd this (set.not_mem_empty a)
    )
  )
