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

-- auxiliary lemmas for option

lemma some.inj.inv {α: Type} {a b: α}: a = b → (some a = some b) :=
  assume : a = b,
  by simp [this]

lemma option.some_iff_not_none {α: Type} {a: option α}: option.is_some a ↔ ¬ option.is_none a :=
  begin
    cases a,
    split,
    intro h,
    contradiction,
    intro h2,
    unfold option.is_none at h2,
    have h3: ↑tt = false, from eq_false_intro h2,
    have h4: ↑tt = true, by simp,
    have h5: false = true, from eq.trans h3.symm h4,
    have h6: true, from trivial,
    have h7: false, from h5.symm ▸ h6,
    contradiction,
    split,
    intro h8,
    intro h9,
    contradiction,
    intro h10,
    unfold option.is_some,
    change tt = tt,
    refl
  end

lemma option.none_iff_not_some {α: Type} {a: option α}: option.is_none a ↔ ¬ option.is_some a :=
  begin
    cases a,
    split,
    intro h,
    contradiction,
    intro h2,
    unfold option.is_none,
    change tt = tt,
    refl,
    split,
    intro h3,
    intro h4,
    unfold option.is_none at h3,
    change ff = tt at h3,
    contradiction,
    intro h5,
    unfold option.is_some at h5,
    have h6: ↑tt = false, from eq_false_intro h5,
    have h7: ↑tt = true, by simp,
    have h8: false = true, from eq.trans h6.symm h7,
    have h9: true, from trivial,
    have : false, from h8.symm ▸ h9,
    contradiction
  end

lemma option.is_none.inv {α: Type} {a: option α}: (a = none) ↔ option.is_none a :=
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

lemma option.is_none.ninv {α: Type} {a: option α}: (a ≠ none) ↔ ¬ option.is_none a :=
  by begin
    split,
    intro h,
    cases a,
    contradiction,
    unfold option.is_none,
    intro h2,
    change ff = tt at h2,
    contradiction,
    intro h3,
    intro h4,
    rw[h4] at h3,
    unfold option.is_none at h3,
    have h5: ↑tt = false, from eq_false_intro h3,
    have h6: ↑tt = true, by simp,
    have h7: false = true, from eq.trans h5.symm h6,
    have h8: true, from trivial,
    have r9: false, from h7.symm ▸ h8,
    contradiction
  end

lemma option.is_some_iff_exists {α: Type} {a: option α}: option.is_some a ↔ (∃b, a = some b) :=
  begin
    split,
    cases a,
    assume c,
    cases c,
    intro h,
    existsi a,
    refl,
    intro h2,
    cases h2,
    rw[a_2],
    unfold option.is_some,
    change tt = tt,
    refl
  end

-- auxiliary lemmas for sets

lemma set.two_elems_mem {α: Type} {a b c: α}:
  a ∈ ({b, c}: set α) -> (a = b) ∨ (a = c) :=
  assume a_in_bc: a ∈ {b, c},
  have a_in_bc: a ∈ insert b (insert c (∅: set α)), by { simp at a_in_bc, simp[a_in_bc] },
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

lemma set.forall_not_mem_of_eq_empty {α: Type} {s: set α}: s = ∅ → ∀ x, x ∉ s :=
  by simp[set.set_eq_def]
