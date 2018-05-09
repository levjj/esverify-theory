-- auxilliary definitions and lemmas used for termination of QI

import .definitions1

def prop.num_quantifiers: prop → ℕ
| (prop.term t)        := 0
| (prop.not P)         := P.num_quantifiers
| (prop.and P₁ P₂)     := P₁.num_quantifiers + P₂.num_quantifiers
| (prop.or P₁ P₂)      := P₁.num_quantifiers + P₂.num_quantifiers
| (prop.pre t₁ t₂)     := 0
| (prop.pre₁ op t)     := 0
| (prop.pre₂ op t₁ t₂) := 0
| (prop.post t₁ t₂)    := 0
| (prop.call t)        := 0
| (prop.forallc x P)   := 1 + P.num_quantifiers
| (prop.exis x P)      := 1 + P.num_quantifiers

lemma same_num_quantifiers_after_rename {P: prop} {x y: var}:
      P.num_quantifiers = (P.rename x y).num_quantifiers :=
  begin
    induction P,
    case prop.term t {
      unfold prop.rename,
      change (
        prop.num_quantifiers (prop.term t) =
        prop.num_quantifiers (prop.term (term.rename x y t))
      ),
      unfold prop.num_quantifiers
    },
    case prop.not P₁ ih {
      unfold prop.rename,
      unfold prop.num_quantifiers,
      from ih
    },
    case prop.and P₁ P₂ P₁_ih P₂_ih {
      unfold prop.rename,
      change (
        prop.num_quantifiers (prop.and P₁ P₂) =
        prop.num_quantifiers (prop.and (prop.rename x y P₁) (prop.rename x y P₂))
      ),
      unfold prop.num_quantifiers,
      rw[P₁_ih],
      rw[P₂_ih]
    },
    case prop.or P₁ P₂ P₁_ih P₂_ih {
      unfold prop.rename,
      change (
        prop.num_quantifiers (prop.or P₁ P₂) =
        prop.num_quantifiers (prop.or (prop.rename x y P₁) (prop.rename x y P₂))
      ),
      unfold prop.num_quantifiers,
      rw[P₁_ih],
      rw[P₂_ih]
    },
    case prop.pre t₁ t₂ {
      unfold prop.rename,
      unfold prop.num_quantifiers
    },
    case prop.pre₁ op t {
      unfold prop.rename,
      unfold prop.num_quantifiers
    },
    case prop.pre₂ op t₁ t₂ {
      unfold prop.rename,
      unfold prop.num_quantifiers
    },
    case prop.call t {
      unfold prop.rename,
      unfold prop.num_quantifiers
    },
    case prop.post t₁ t₂ {
      unfold prop.rename,
      unfold prop.num_quantifiers
    },
    case prop.forallc y P₁ P₁_ih {
      unfold prop.rename,
      by_cases (x = y) with h,
      
      simp[h],

      simp[h],
      unfold prop.num_quantifiers,
      apply eq_add_left_of_eq,
      from P₁_ih
    },
    case prop.exis y P' P'_ih {
      unfold prop.rename,
      by_cases (x = y) with h,
      
      simp[h],

      simp[h],
      unfold prop.num_quantifiers,
      apply eq_add_left_of_eq,
      from P'_ih
    }
  end

lemma lifted_prop_smaller {P: prop} {x: var}:
      ∀P', ((P.lift_p x = some P') → (P'.num_quantifiers < P.num_quantifiers)) ∧
           ((P.lift_n x = some P') → (P'.num_quantifiers < P.num_quantifiers)) :=
  begin
    induction P,
    case prop.term t {
      assume P',
      split,

      assume h1,
      unfold prop.lift_p at h1,
      contradiction,

      assume h1,
      unfold prop.lift_n at h1,
      contradiction
    },
    case prop.not P₁ ih {
      assume P',
      split,

      assume h1,
      unfold prop.lift_p at h1,
      cases h2: prop.lift_n P₁ x,

      simp[h2] at h1,
      cases h1,

      have h3, from (ih a).right h2,
      simp[h2] at h1,
      cases h1,
      unfold prop.num_quantifiers,
      from h3,

      assume h1,
      unfold prop.lift_n at h1,
      cases h2: prop.lift_p P₁ x,

      simp[h2] at h1,
      cases h1,

      have h3, from (ih a).left h2,
      simp[h2] at h1,
      cases h1,
      unfold prop.num_quantifiers,
      from h3
    },
    case prop.and P₁ P₂ P₁_ih P₂_ih {
      assume P',
      split,

      assume h1,
      unfold prop.lift_p at h1,
      cases h2: prop.lift_p P₁ x,

      simp[h2] at h1,
      cases h3: prop.lift_p P₂ x,
      simp[h3] at h1,
      cases h1,

      simp[h3] at h1,
      cases h1,
      have h3, from (P₂_ih a).left h3,
      unfold prop.num_quantifiers,
      apply nat.add_lt_add_left,
      from h3,

      simp[h2] at h1,
      cases h1,
      unfold prop.num_quantifiers,
      apply nat.add_lt_add_right,
      from (P₁_ih a).left h2,

      assume h1,
      unfold prop.lift_n at h1,
      cases h2: prop.lift_n P₁ x,

      simp[h2] at h1,
      cases h3: prop.lift_n P₂ x,
      simp[h3] at h1,
      cases h1,

      simp[h3] at h1,
      cases h1,
      have h3, from (P₂_ih a).right h3,
      unfold prop.num_quantifiers,
      apply nat.add_lt_add_left,
      from h3,

      simp[h2] at h1,
      cases h1,
      unfold prop.num_quantifiers,
      apply nat.add_lt_add_right,
      from (P₁_ih a).right h2
    },
    case prop.or P₁ P₂ P₁_ih P₂_ih {
      assume P',
      split,

      assume h1,
      unfold prop.lift_p at h1,
      cases h2: prop.lift_p P₁ x,

      simp[h2] at h1,
      cases h3: prop.lift_p P₂ x,
      simp[h3] at h1,
      cases h1,

      simp[h3] at h1,
      cases h1,
      have h3, from (P₂_ih a).left h3,
      unfold prop.num_quantifiers,
      apply nat.add_lt_add_left,
      from h3,

      simp[h2] at h1,
      cases h1,
      unfold prop.num_quantifiers,
      apply nat.add_lt_add_right,
      from (P₁_ih a).left h2,

      assume h1,
      unfold prop.lift_n at h1,
      cases h2: prop.lift_n P₁ x,

      simp[h2] at h1,
      cases h3: prop.lift_n P₂ x,
      simp[h3] at h1,
      cases h1,

      simp[h3] at h1,
      cases h1,
      have h3, from (P₂_ih a).right h3,
      unfold prop.num_quantifiers,
      apply nat.add_lt_add_left,
      from h3,

      simp[h2] at h1,
      cases h1,
      unfold prop.num_quantifiers,
      apply nat.add_lt_add_right,
      from (P₁_ih a).right h2
    },
    case prop.pre t₁ t₂ {
      assume P',
      split,

      assume h1,
      unfold prop.lift_p at h1,
      contradiction,

      assume h1,
      unfold prop.lift_n at h1,
      contradiction
    },
    case prop.pre₁ op t {
      assume P',
      split,

      assume h1,
      unfold prop.lift_p at h1,
      contradiction,

      assume h1,
      unfold prop.lift_n at h1,
      contradiction
    },
    case prop.pre₂ op t₁ t₂ {
      assume P',
      split,

      assume h1,
      unfold prop.lift_p at h1,
      contradiction,

      assume h1,
      unfold prop.lift_n at h1,
      contradiction
    },
    case prop.call t {
      assume P',
      split,

      assume h1,
      unfold prop.lift_p at h1,
      contradiction,

      assume h1,
      unfold prop.lift_n at h1,
      contradiction
    },
    case prop.post t₁ t₂ {
      assume P',
      split,

      assume h1,
      unfold prop.lift_p at h1,
      contradiction,

      assume h1,
      unfold prop.lift_n at h1,
      contradiction
    },
    case prop.forallc y P₁ P₁_ih {
      assume P',
      split,

      assume h1,
      unfold prop.lift_p at h1,
      have h2, from option.some.inj h1,
      simp[h2.symm],
      unfold prop.num_quantifiers,
      have h3: (prop.num_quantifiers P₁ = prop.num_quantifiers (prop.rename y x P₁)),
      from same_num_quantifiers_after_rename,
      rw[←h3],
      simp,
      from lt_of_add_one,

      assume h1,
      unfold prop.lift_n at h1,
      contradiction
    },
    case prop.exis y P₁ P₁_ih {
      assume P',
      split,

      assume h1,
      unfold prop.lift_p at h1,
      contradiction,

      assume h1,
      unfold prop.lift_n at h1,
      have h2, from option.some.inj h1,
      simp[h2.symm],
      unfold prop.num_quantifiers,
      have h3: (prop.num_quantifiers P₁ = prop.num_quantifiers (prop.rename y x P₁)),
      from same_num_quantifiers_after_rename,
      rw[←h3],
      simp,
      from lt_of_add_one
    }
  end

def erased_measure : has_well_founded
      (psum prop prop)
:= ⟨_, measure_wf $ λ s,
  match s with
  | psum.inl a := a.sizeof
  | psum.inr a := a.sizeof
  end⟩

def instantiate_with_measure : has_well_founded
      (psum (Σ' (p : prop), calltrigger)
            (Σ' (p : prop), calltrigger))
:= ⟨_, measure_wf $ λ s,
  match s with
  | psum.inl a := a.1.sizeof
  | psum.inr a := a.1.sizeof
  end⟩

def find_calls_measure : has_well_founded
      (psum prop prop)
:= ⟨_, measure_wf $ λ s,
  match s with
  | psum.inl a := a.sizeof
  | psum.inr a := a.sizeof
  end⟩

def prop.simplesize: prop → ℕ
| (prop.term t)        := 0
| (prop.not P)         := 1 + P.simplesize
| (prop.and P₁ P₂)     := 1 + P₁.simplesize + P₂.simplesize
| (prop.or P₁ P₂)      := 1 + P₁.simplesize + P₂.simplesize
| (prop.pre t₁ t₂)     := 0
| (prop.pre₁ op t)     := 0
| (prop.pre₂ op t₁ t₂) := 0
| (prop.call t)        := 0
| (prop.post t₁ t₂)    := 0
| (prop.forallc x P)   := 1 + P.simplesize
| (prop.exis x P)      := 1 + P.simplesize

lemma same_simplesize_after_subst {P: prop} {x: var} {v: value}:
      P.simplesize = (prop.subst x v P).simplesize :=
  begin
    induction P,
    case prop.term t {
      unfold prop.subst,
      unfold prop.simplesize,
      change (0 = prop.simplesize (prop.term (term.subst x v t))),
      unfold prop.simplesize
    },
    case prop.not P₁ ih {
      unfold prop.subst,
      unfold prop.simplesize,
      rw[ih]
    },
    case prop.and P₁ P₂ P₁_ih P₂_ih {
      unfold prop.subst,
      unfold prop.simplesize,
      change (prop.simplesize (prop.and P₁ P₂) = prop.simplesize (prop.and (prop.subst x v P₁) (prop.subst x v P₂))),
      unfold prop.simplesize,
      rw[P₁_ih],
      rw[P₂_ih]
    },
    case prop.or P₁ P₂ P₁_ih P₂_ih {
      unfold prop.subst,
      unfold prop.simplesize,
      change (prop.simplesize (prop.or P₁ P₂) = prop.simplesize (prop.or (prop.subst x v P₁) (prop.subst x v P₂))),
      unfold prop.simplesize,
      rw[P₁_ih],
      rw[P₂_ih]
    },
    case prop.pre t₁ t₂ {
      unfold prop.subst,
      unfold prop.simplesize
    },
    case prop.pre₁ op t {
      unfold prop.subst,
      unfold prop.simplesize
    },
    case prop.pre₂ op t₁ t₂ {
      unfold prop.subst,
      unfold prop.simplesize
    },
    case prop.call t {
      unfold prop.subst,
      unfold prop.simplesize
    },
    case prop.post t₁ t₂ {
      unfold prop.subst,
      unfold prop.simplesize
    },
    case prop.forallc z P' P'_ih {
      unfold prop.subst,
      unfold prop.simplesize,
      apply eq_add_left_of_eq,
      by_cases (x = z) with h1,
      simp[h1],
      simp[h1],
      from P'_ih
    },
    case prop.exis z P' P'_ih {
      unfold prop.subst,
      unfold prop.simplesize,
      apply eq_add_left_of_eq,
      by_cases (x = z) with h1,
      simp[h1],
      simp[h1],
      from P'_ih
    }
  end

lemma simplesize_prop_not {P: prop}:
      P.simplesize < P.not.simplesize :=
  begin
    unfold prop.simplesize,
    rw[add_comm],
    apply lt_add_of_pos_right,
    from zero_lt_one
  end

lemma simplesize_prop_and₁ {P S: prop}:
      P.simplesize < (prop.and P S).simplesize :=
  begin
    unfold prop.simplesize,
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    change 0 < prop.simplesize S + 1,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma simplesize_prop_and₂ {P S: prop}:
      S.simplesize < (prop.and P S).simplesize :=
  begin
    unfold prop.simplesize,
    rw[add_comm],
    apply lt_add_of_pos_right,
    change 0 < 1 + prop.simplesize P,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma simplesize_prop_or₁ {P S: prop}:
      P.simplesize < (prop.or P S).simplesize :=
  begin
    unfold prop.simplesize,
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    change 0 < prop.simplesize S + 1,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma simplesize_prop_or₂ {P S: prop}:
      S.simplesize < (prop.or P S).simplesize :=
  begin
    unfold prop.simplesize,
    rw[add_comm],
    apply lt_add_of_pos_right,
    change 0 < 1 + prop.simplesize P,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma simplesize_prop_exis {P: prop} {x: var}:
      P.simplesize < (prop.exis x P).simplesize :=
  begin
    unfold prop.simplesize,
    rw[add_comm],
    apply lt_add_of_pos_right,
    from zero_lt_one
  end

lemma simplesize_prop_forall {P: prop} {x: var}:
      P.simplesize < (prop.forallc x P).simplesize :=
  begin
    unfold prop.simplesize,
    rw[add_comm],
    apply lt_add_of_pos_right,
    from zero_lt_one
  end
 