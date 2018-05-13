-- lemmas about substitution

import .definitions1 .freevars .others

lemma env.contains.inv {σ: env} {x y: var} {v: value}: x ∈ (σ[y↦v]) → (x = y ∨ x ∈ σ) :=
  assume x_in: x ∈ (σ[y↦v]),
  show x = y ∨ x ∈ σ, by { cases x_in, left, refl, right, from a }

lemma env.contains.same.inv {σ: env} {x y: var} {v: value}: x ∉ (σ[y↦v]) → ¬ (x = y ∨ x ∈ σ) :=
  assume x_not_in: x ∉ (σ[y↦v]),
  assume : (x = y ∨ x ∈ σ),
  this.elim (
    assume x_is_y: x = y,
    have x ∈ (σ[x↦v]), from env.contains.same,
    have x ∈ (σ[y↦v]), from @eq.subst var (λa, x ∈ (σ[a↦v])) x y x_is_y this,
    show «false», from x_not_in this
  ) (
    assume : x ∈ σ,
    have x ∈ (σ[y↦v]), from env.contains.rest this,
    show «false», from x_not_in this
  )

lemma env.contains_apply_equiv {σ: env} {x: var}:
  ((σ x = none) ↔ (x ∉ σ)) ∧ ((∃v, σ x = some v) ↔ (x ∈ σ)) :=
begin
  induction σ with σ' y v' ih,
  show ((env.empty x = none) ↔ (x ∉ env.empty)) ∧ ((∃v, env.empty x = some v) ↔ (x ∈ env.empty)), by begin
    split,
    show (env.empty x = none) ↔ (x ∉ env.empty), by begin
      split,
      show (env.empty x = none) → (x ∉ env.empty), by begin
        assume : (env.empty x = none),
        by_contradiction h,
        cases h
      end,
      show (x ∉ env.empty) → (env.empty x = none), by begin
        assume : (x ∉ env.empty),
        have : (env.apply env.empty x = none), by unfold env.apply,
        show (env.empty x = none), from this
      end
    end,
    show (∃v, env.empty x = some v) ↔ (x ∈ env.empty), by begin
      split,
      show (∃v, env.empty x = some v) → (x ∈ env.empty), from (
        assume : (∃v, env.empty x = some v),
        let (⟨v, h0⟩) := this in
        have h1: env.apply env.empty x = some v, from h0,
        have h2: env.apply env.empty x = none, by unfold env.apply,
        have some v = none, from eq.trans h1.symm h2,
        show (x ∈ env.empty), by contradiction
      ),
      show (x ∈ env.empty) → (∃v,env.empty x = some v), by begin
        assume h: x ∈ env.empty,
        cases h
      end
    end
  end,
  show (((σ'[y↦v']) x = none) ↔ (x ∉ (σ'[y↦v']))) ∧ ((∃v, (σ'[y↦v']) x = some v) ↔ (x ∈ (σ'[y↦v']))), by begin
    split,
    show (((σ'[y↦v']) x = none) ↔ (x ∉ (σ'[y↦v']))), by begin
      split,
      show (((σ'[y↦v']) x = none) → (x ∉ (σ'[y↦v']))), by begin
        assume h: ((σ'[y↦v']) x = none),
        have h2: (env.apply (σ'[y↦v']) x = (if y = x ∧ option.is_none (σ'.apply x) then v' else σ'.apply x)),
        by unfold env.apply,
        have h3: ((if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = none),
        from eq.trans h2.symm h,
        have h4: (σ'.apply x = none), by begin
          by_cases (y = x ∧ option.is_none (σ'.apply x)),
          show (σ'.apply x = none), by begin
            have : ((if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = ↑v'),
            by simp[h],
            have : (none = ↑v'), from eq.trans h3.symm this,
            contradiction
          end,
          show (σ'.apply x = none), by begin
            have : ((if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = σ'.apply x),
            by simp[h],
            show (σ'.apply x = none), from eq.trans this.symm h3
          end
        end,
        have : x ∉ σ', from ih.left.mp h4,
        have h5: ¬ (x = y), by begin
          by_contradiction,
          have h6: (option.is_none (σ'.apply x) = tt), from option.is_none.inv.mp h4,
          have : (y = x ∧ option.is_none (σ'.apply x)), from ⟨a.symm, h6⟩,
          have : ((if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = ↑v'),
          by simp[this],
          have : (none = ↑v'), from eq.trans h3.symm this,
          contradiction
        end,
        by_contradiction a,
        cases a,
        case env.contains.same x_is_x {
          contradiction
        },
        case env.contains.rest x_is_x {
          contradiction
        }
      end,
      show (x ∉ (σ'[y↦v'])) → (((σ'[y↦v']) x = none)), by begin
        assume : (x ∉ (σ'[y↦v'])),
        have h7: ¬ (x = y ∨ x ∈ σ'), from env.contains.same.inv this,
        have : x ≠ y, from (not_or_distrib.mp h7).left,
        have h8: y ≠ x, from ne.symm this,
        have h9: x ∉ σ', from (not_or_distrib.mp h7).right,
        have h10: (σ'.apply x = none), from ih.left.mpr h9,
        have h11: (env.apply (σ'[y↦v']) x = (if y = x ∧ option.is_none (σ'.apply x) then v' else σ'.apply x)),
        by unfold env.apply,
        have h12: ((if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = σ'.apply x),
        by simp[h8],
        show ((σ'[y↦v']) x = none), from eq.trans (eq.trans h11 h12) h10
      end
    end,
    show ((∃v, (σ'[y↦v']) x = some v) ↔ (x ∈ (σ'[y↦v']))), by begin
      split,
      show ((∃v, (σ'[y↦v']) x = some v) → (x ∈ (σ'[y↦v']))), from (
        assume : (∃v, (σ'[y↦v']) x = some v),
        let ⟨v, h13⟩ := this in begin
        have h14: (env.apply (σ'[y↦v']) x = (if y = x ∧ option.is_none (σ'.apply x) then v' else σ'.apply x)),
        by unfold env.apply,
        by_cases (y = x ∧ option.is_none (σ'.apply x)) with h15,
        show (x ∈ (σ'[y↦v'])), by begin
          have x_is_y: (y = x), from h15.left,
          have : (x ∈ (σ'[x↦v'])), from env.contains.same,
          show x ∈ (σ'[y↦v']), from @eq.subst var (λa, x ∈ (σ'[a↦v'])) x y x_is_y.symm this
        end,
        show (x ∈ (σ'[y↦v'])), by begin
          have : ((if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = σ'.apply x),
          by simp[h15],
          have : (σ'.apply x = v), from eq.trans (eq.trans this.symm h14.symm) h13,
          have : x ∈ σ', from ih.right.mp (exists.intro v this),
          show x ∈ (σ'[y↦v']), from env.contains.rest this
        end
      end),
      show (x ∈ (σ'[y↦v'])) → (∃v, (σ'[y↦v']) x = some v), by begin
        assume h16: (x ∈ (σ'[y↦v'])),
        have h17: (env.apply (σ'[y↦v']) x = (if y = x ∧ option.is_none (σ'.apply x) then v' else σ'.apply x)),
        by unfold env.apply,
        cases h16,
        case env.contains.same {
          by_cases (x = x ∧ option.is_none (σ'.apply x)),
          show (∃v, (σ'[x↦v']) x = some v), by begin
            have : ((if x = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = v'),
            by { simp[h] },
            show (∃v, (σ'[x↦v']) x = some v), from exists.intro v' (eq.trans h17 this)
          end,
          show (∃v, (σ'[x↦v']) x = some v), by begin
            have h19: ¬option.is_none (σ'.apply x), by begin
              by_contradiction h18,
              have : (x = x ∧ option.is_none (σ'.apply x)), from ⟨rfl, h18⟩,
              exact h this
            end,
            have : ((option.is_some (σ'.apply x)):Prop), from option.some_iff_not_none.mpr h19,
            have : ∃v, (σ'.apply x) = some v, from option.is_some_iff_exists.mp this,
            cases this with v h20,
            have : ((if x = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = σ'.apply x),
            by { simp[h], simp[h19] },
            show (∃v, (σ'[x↦v']) x = some v), from exists.intro v (eq.trans (eq.trans h17 this) h20)
          end
        },
        case env.contains.rest h27 {
          have : (∃v, σ'.apply x = some v), from ih.right.mpr h27,
          cases this with v h28,
          have : ¬ (option.is_none (σ'.apply x)),
          from option.some_iff_not_none.mp (option.is_some_iff_exists.mpr (exists.intro v h28)),
          have : ((if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = σ'.apply x),
          by simp[this],
          show (∃v, (σ'[y↦v']) x = some v), from exists.intro v (eq.trans (eq.trans h17 this) h28)
        }
      end
    end
  end
end

instance {σ: env} {x: var} : decidable (env.contains σ x) :=
  let r := env.apply σ x in
  have h: r = env.apply σ x, from rfl,
  @option.rec_on value (λa, (r = a) → decidable (env.contains σ x)) r
  (
    assume : r = none,
    have env.apply σ x = none, from eq.trans h this,
    have ¬ (x ∈ σ), from env.contains_apply_equiv.left.mp this,
    is_false this
  ) (
    assume v: value,
    assume : r = some v,
    have env.apply σ x = some v, from eq.trans h this,
    have ∃v, env.apply σ x = some v, from exists.intro v this,
    have x ∈ σ, from env.contains_apply_equiv.right.mp this,
    is_true this
  ) rfl

lemma term.subst.congr {x: var} {v: value} {t₁ t₂: term}: (t₁ = t₂) → (term.subst x v t₁ = term.subst x v t₂) :=
  begin
    assume h1,
    congr,
    from h1
  end

lemma env.contains_without.inv {σ: env} {x y: var}:
      (x ∈ σ.without y) → (x ≠ y) ∧ x ∈ σ :=
  begin
    assume h1,

    induction σ with σ' z v ih,
    unfold env.without at h1,
    cases h1,

    unfold env.without at h1,

    by_cases (z = y) with h2,

    simp[h2] at h1,
    have h3, from ih h1,
    split,
    from h3.left,
    apply env.contains.rest,
    from h3.right,

    simp[h2] at h1,
    have h3, from env.contains.inv h1,
    cases h3 with h4 h5,
    rw[h4],
    split,
    from h2,
    from env.contains.same,

    have h3, from ih h5,
    split,
    from h3.left,
    apply env.contains.rest,
    from h3.right
  end

lemma env.contains_without.rinv {σ: env} {x y: var}:
      x ∈ σ ∧ (x ≠ y) → x ∈ σ.without y :=
  begin
    assume h1,

    induction σ with σ' z v ih,
    cases h1.left,

    unfold env.without,
    by_cases (z = y) with h2,

    simp[h2],
    have h3, from env.contains.inv h1.left,
    cases h3 with h4 h5,
    have : (x = y), from eq.trans h4 h2,
    have : (y ≠ y), from @eq.subst var (λa, a ≠ y) x y this h1.right,
    contradiction,

    from ih ⟨h5, h1.right⟩,

    simp[h2],
    have h3, from env.contains.inv h1.left,
    cases h3 with h4 h5,
    rw[h4],
    apply env.contains.same,

    apply env.contains.rest,
    from ih ⟨h5, h1.right⟩,
  end

lemma env.without_equiv {σ: env} {x y: var} {v: value}:
      (x ∉ σ) ∨ (σ x = v) → (x ∉ σ.without y ∨ (σ.without y x = v)) :=
  begin
    assume h1,

    induction σ with σ' z v' ih,

    cases h1 with h2 h3,
    left,
    unfold env.without,
    assume h4,
    cases h4,

    cases h3,

    cases h1 with h2 h3,
    left,
    unfold env.without,
    by_cases (z = y) with h4,
    simp[h4],
    assume h5,
    have h6, from env.contains_without.inv h5,
    have : x ∈ (σ'[z↦v']), from env.contains.rest h6.right,
    contradiction,

    simp[h4],
    assume h5,
    have h6, from env.contains.inv h5,
    cases h6 with h7 h8,
    rw[h7] at h2,
    have : z ∈ (σ'[z↦v']), from env.contains.same,
    contradiction,

    have h9, from env.contains_without.inv h8,
    have : x ∈ (σ'[z↦v']), from env.contains.rest h9.right,
    contradiction,

    by_cases (x = y) with h4,
    left,
    unfold env.without,
    by_cases (z = y) with h5,
    simp[h5],
    rw[h4],
    assume h6,
    have h7, from env.contains_without.inv h6,
    have : ¬ (y = y), from h7.left,
    contradiction,
    
    simp[h5],
    assume h6,
    have h7, from env.contains.inv h6,
    cases h7 with h8 h9,
    have : (y = z), from eq.trans h4.symm h8,
    have : ¬ (z = z), from @eq.subst var (λa, ¬ (z = a)) y z this h5,
    contradiction,

    rw[h4] at h9,
    have h10, from env.contains_without.inv h9,
    have : ¬ (y = y), from h10.left,
    contradiction,

    right,
    have h5: (env.apply (σ'[z↦v']) x = some v), from h3,
    unfold env.apply at h5,
    by_cases (z = x ∧ (option.is_none (env.apply σ' x))) with h6,
    simp[h6] at h5,
    have : (some v' = some v), from h5,
    have h7: (v' = v), from option.some.inj this,
    have h8, from env.contains_apply_equiv.left.mp (option.is_none.inv.mpr h6.right),
    have h9, from ih (or.inl h8),

    let a' := ((env.without σ' y)[z↦v']),
    have h12: (env.without (σ'[z↦v']) y = (if z = y then (env.without σ' y) else a')),
    by unfold env.without,
    rw[h12],
    change ((ite (z = y) (env.without σ' y) a') x = ↑v),
    have : ¬ (z = y), from @eq.subst var (λa, ¬ (a = y)) x z h6.left.symm h4,
    have : (ite (z = y) (env.without σ' y) a'
             = ((env.without σ' y)[z↦v'])), by simp[this],
    have h13: (
      ((ite (z = y) (env.without σ' y) a') x = ↑v)
    = (((env.without σ' y)[z↦v']) x = ↑v)
    ), by rw[this],
    rw[h13],
    change (env.apply (env.without σ' y[z↦v']) x = ↑v),
    unfold env.apply,

    cases h9 with h10 h11,

    have h14, from env.contains_apply_equiv.left.mpr h10,
    have h15, from option.is_none.inv.mp h14,
    have h16: (z = x ∧ (option.is_none (env.apply (env.without σ' y) x))), from and.intro h6.left h15,
    simp[h16],
    from some.inj.inv h7,

    have h14, from option.is_some_iff_exists.mpr (exists.intro v h11),
    have h15, from option.some_iff_not_none.mp h14,
    have h16: ¬ (z = x ∧ option.is_none (env.apply (env.without σ' y) x)),
    from not_and_distrib.mpr (or.inr h15),
    simp[h16],
    from h11,

    simp[h6] at h5,
    let a' := ((env.without σ' y)[z↦v']),
    have h7: (env.without (σ'[z↦v']) y = (if z = y then (env.without σ' y) else a')),
    by unfold env.without,
    rw[h7],

    by_cases (z = y) with h8,
    have : (ite (z = y) (env.without σ' y) ((env.without σ' y)[z↦v'])
             = (env.without σ' y)), by simp[h8],
    rw[this],
    have h8, from ih (or.inr h5),
    cases h8 with h9 h10,

    have : x ∈ σ', from env.contains_apply_equiv.right.mp (exists.intro v h5),
    have h9: x ∈ env.without σ' y,
    from env.contains_without.rinv ⟨this, h4⟩,
    contradiction,

    from h10,

    have : (ite (z = y) (env.without σ' y) ((env.without σ' y)[z↦v'])
             = ((env.without σ' y)[z↦v'])), by simp[h8],
    rw[this],
    change (env.apply ((env.without σ' y)[z↦v']) x = ↑v),
    unfold env.apply,

    have h10b: x ∈ σ', from env.contains_apply_equiv.right.mp (exists.intro v h5),
    have h11: x ∈ env.without σ' y,
    from env.contains_without.rinv ⟨h10b, h4⟩,
    have h12, from env.contains_apply_equiv.right.mpr h11,
    have h13, from option.is_some_iff_exists.mpr h12,
    have h14, from option.some_iff_not_none.mp h13,
    have h15: ¬ (z = x ∧ option.is_none (env.apply (env.without σ' y) x)),
    from not_and_distrib.mpr (or.inr h14),
    simp[h15],
    have h16, from ih (or.inr h5),
    cases h16 with h17 h18,
    contradiction,
    from h18
  end

lemma env.not_in_without {σ: env} {x y: var}: x ∉ σ → x ∉ σ.without y :=
  begin
    assume h1,

    induction σ with σ' z v' ih,

    unfold env.without,
    assume h4,
    cases h4,

    unfold env.without,
    by_cases (z = y) with h4,
    simp[h4],
    assume h5,
    have h6, from env.contains_without.inv h5,
    have : x ∈ (σ'[z↦v']), from env.contains.rest h6.right,
    contradiction,

    simp[h4],
    assume h5,
    have h6, from env.contains.inv h5,
    cases h6 with h7 h8,
    rw[h7] at h1,
    have : z ∈ (σ'[z↦v']), from env.contains.same,
    contradiction,

    have h9, from env.contains_without.inv h8,
    have : x ∈ (σ'[z↦v']), from env.contains.rest h9.right,
    contradiction
  end

lemma env.not_contains_without {σ: env} {x: var}: x ∉ σ.without x :=
  assume : x ∈ σ.without x,
  have (x ≠ x) ∧ x ∈ σ, from env.contains_without.inv this,
  show «false», from this.left (eq.refl x)

lemma env.without_equiv_with {σ: env} {x: var}: ∀y, y ∈ σ.without x → (σ.without x y = σ y) :=
  assume y: var,
  assume h1: y ∈ σ.without x,
  have y ≠ x ∧ y ∈ σ, from env.contains_without.inv h1,
  have ∃v: value, σ y = v, from env.contains_apply_equiv.right.mpr this.right,
  let ⟨v, σ_y_is_v⟩ := this in
  have y ∉ σ.without x ∨ (σ.without x y = v), from env.without_equiv (or.inr σ_y_is_v),
  or.elim this (
    assume : y ∉ σ.without x,
    show σ.without x y = σ y, from absurd h1 this
  ) (
    assume : σ.without x y = v,
    show σ.without x y = σ y, from eq.trans this σ_y_is_v.symm
  )

lemma unchanged_of_subst_nonfree_term {t: term} {x: var} {v: value}:
    x ∉ FV t → (term.subst x v t = t) :=
  assume x_not_free: ¬ free_in_term x t,
  begin
    induction t with v' y unop t₁ t₁_ih binop t₂ t₃ t₂_ih t₃_ih t₄ t₅ t₄_ih t₅_ih,
    show (term.subst x v (term.value v') = ↑v'), by unfold term.subst,
    show (term.subst x v (term.var y) = (term.var y)), from (
      have h: term.subst x v (term.var y) = (if x = y then v else y), by unfold term.subst,
      if x_is_y: x = y then (
        have free_in_term y (term.var y), from free_in_term.var y,
        have free_in_term x (term.var y), from x_is_y.symm ▸ this,
        show term.subst x v (term.var y) = y, from absurd this x_not_free
      ) else (
        show term.subst x v (term.var y) = y, by { simp[x_is_y] at h, assumption }
      )
    ),
    show (term.subst x v (term.unop unop t₁) = term.unop unop t₁), from (
      have h: term.subst x v (term.unop unop t₁) = term.unop unop (term.subst x v t₁), by unfold term.subst,
      have ¬ free_in_term x t₁, from (
        assume : free_in_term x t₁,
        have free_in_term x (term.unop unop t₁), from free_in_term.unop this,
        show «false», from x_not_free this
      ),
      have term.subst x v t₁ = t₁, from t₁_ih this,
      show term.subst x v (term.unop unop t₁) = term.unop unop t₁,
      from @eq.subst term (λa, term.subst x v (term.unop unop t₁) = term.unop unop a) (term.subst x v t₁) t₁ this h
    ),
    show (term.subst x v (term.binop binop t₂ t₃) = term.binop binop t₂ t₃), from (
      have h: term.subst x v (term.binop binop t₂ t₃)
            = term.binop binop (term.subst x v t₂) (term.subst x v t₃), by unfold term.subst,
      have ¬ free_in_term x t₂, from (
        assume : free_in_term x t₂,
        have free_in_term x (term.binop binop t₂ t₃), from free_in_term.binop₁ this,
        show «false», from x_not_free this
      ),
      have t2_subst: term.subst x v t₂ = t₂, from t₂_ih this,
      have ¬ free_in_term x t₃, from (
        assume : free_in_term x t₃,
        have free_in_term x (term.binop binop t₂ t₃), from free_in_term.binop₂ this,
        show «false», from x_not_free this
      ),
      have t3_subst: term.subst x v t₃ = t₃, from t₃_ih this,
      have term.subst x v (term.binop binop t₂ t₃) = term.binop binop t₂ (term.subst x v t₃),
      from @eq.subst term (λa, term.subst x v (term.binop binop t₂ t₃) = term.binop binop a (term.subst x v t₃))
      (term.subst x v t₂) t₂ t2_subst h,
      show term.subst x v (term.binop binop t₂ t₃) = term.binop binop t₂ t₃,
      from @eq.subst term (λa, term.subst x v (term.binop binop t₂ t₃) = term.binop binop t₂ a)
      (term.subst x v t₃) t₃ t3_subst this
    ),
    show (term.subst x v (term.app t₄ t₅) = term.app t₄ t₅), from (
      have h: term.subst x v (term.app t₄ t₅)
            = term.app (term.subst x v t₄) (term.subst x v t₅), by unfold term.subst,
      have ¬ free_in_term x t₄, from (
        assume : free_in_term x t₄,
        have free_in_term x (term.app t₄ t₅), from free_in_term.app₁ this,
        show «false», from x_not_free this
      ),
      have t4_subst: term.subst x v t₄ = t₄, from t₄_ih this,
      have ¬ free_in_term x t₅, from (
        assume : free_in_term x t₅,
        have free_in_term x (term.app t₄ t₅), from free_in_term.app₂ this,
        show «false», from x_not_free this
      ),
      have t5_subst: term.subst x v t₅ = t₅, from t₅_ih this,
      have term.subst x v (term.app t₄ t₅) = term.app t₄ (term.subst x v t₅),
      from @eq.subst term (λa, term.subst x v (term.app t₄ t₅) = term.app a (term.subst x v t₅))
      (term.subst x v t₄) t₄ t4_subst h,
      show term.subst x v (term.app t₄ t₅) = term.app t₄ t₅,
      from @eq.subst term (λa, term.subst x v (term.app t₄ t₅) = term.app t₄ a)
      (term.subst x v t₅) t₅ t5_subst this
    )
  end

lemma unchanged_of_subst_env_nonfree_term {t: term}:
    closed t → (∀σ, term.subst_env σ t = t) :=
  assume x_not_free: (∀x, x ∉ FV t),
  assume σ: env,
  begin
    induction σ with σ' x v ih,

    show (term.subst_env env.empty t = t), by unfold term.subst_env,

    show (term.subst_env (σ'[x↦v]) t = t), by calc
        term.subst_env (σ'[x↦v]) t = term.subst x v (term.subst_env σ' t) : by unfold term.subst_env
                               ... = term.subst x v t : by rw[ih]
                               ... = t : unchanged_of_subst_nonfree_term (x_not_free x)
  end

lemma term.subst.var.same {x: var} {v: value}: term.subst x v x = v :=
  have h: term.subst x v (term.var x) = (if x = x then v else x), by unfold term.subst,
  have (if x = x then (term.value v) else (term.var x)) = (term.value v), by simp,
  show term.subst x v x = v, from eq.trans h this

lemma term.subst.var.diff {x y: var} {v: value}: (x ≠ y) → (term.subst x v y = y) :=
  assume x_neq_y: x ≠ y,
  have h: term.subst x v (term.var y) = (if x = y then v else y), by unfold term.subst,
  have (if x = y then (term.value v) else (term.var y)) = (term.var y), by simp[x_neq_y],
  show term.subst x v y = y, from eq.trans h this

lemma term.substt.var.diff {x y: var} {t: term}: (x ≠ y) → (term.substt x t y = y) :=
  assume x_neq_y: x ≠ y,
  have h: term.substt x t (term.var y) = (if x = y then t else y), by unfold term.substt,
  have (if x = y then t else (term.var y)) = (term.var y), by simp[x_neq_y],
  show term.substt x t y = y, from eq.trans h this

lemma unchanged_of_subst_nonfree_prop {P: prop} {x: var} {v: value}:
    x ∉ FV P → (prop.subst x v P = P) :=
  assume x_not_free: ¬ free_in_prop x P,
  begin
    induction P,
    case prop.term t { from (
      have h: prop.subst x v (prop.term t) = term.subst x v t, by unfold prop.subst,
      have ¬ free_in_term x t, from (
        assume : free_in_term x t,
        have free_in_prop x (prop.term t), from free_in_prop.term this,
        show «false», from x_not_free this
      ),
      have term.subst x v t = t, from unchanged_of_subst_nonfree_term this,
      show prop.subst x v t = prop.term t,
      from @eq.subst term (λa, prop.subst x v (prop.term t) = prop.term a) (term.subst x v t) t this h
    )},
    case prop.not P₁ ih { from (
      have h: prop.subst x v P₁.not = (prop.subst x v P₁).not, by unfold prop.subst,
      have ¬ free_in_prop x P₁, from (
        assume : free_in_prop x P₁,
        have free_in_prop x P₁.not, from free_in_prop.not this,
        show «false», from x_not_free this
      ),
      have prop.subst x v P₁ = P₁, from ih this,
      show prop.subst x v P₁.not = P₁.not,
      from @eq.subst prop (λa, prop.subst x v P₁.not = prop.not a) (prop.subst x v P₁) P₁ this h
    )},
    case prop.and P₁ P₂ P₁_ih P₂_ih { from (
      have h: prop.subst x v (prop.and P₁ P₂) = (prop.subst x v P₁ ⋀ prop.subst x v P₂), by unfold prop.subst,
      have ¬ free_in_prop x P₁, from (
        assume : free_in_prop x P₁,
        have free_in_prop x (P₁ ⋀ P₂), from free_in_prop.and₁ this,
        show «false», from x_not_free this
      ),
      have h1: prop.subst x v P₁ = P₁, from P₁_ih this,
      have ¬ free_in_prop x P₂, from (
        assume : free_in_prop x P₂,
        have free_in_prop x (P₁ ⋀ P₂), from free_in_prop.and₂ this,
        show «false», from x_not_free this
      ),
      have h2: prop.subst x v P₂ = P₂, from P₂_ih this,
      have prop.subst x v (P₁ ⋀ P₂) = (P₁ ⋀ prop.subst x v P₂),
      from @eq.subst prop (λa, prop.subst x v (prop.and P₁ P₂) = (a ⋀ prop.subst x v P₂)) (prop.subst x v P₁) P₁ h1 h,
      show prop.subst x v (P₁ ⋀ P₂) = (P₁ ⋀ P₂),
      from @eq.subst prop (λa, prop.subst x v (prop.and P₁ P₂) = (P₁ ⋀ a)) (prop.subst x v P₂) P₂ h2 this
    )},
    case prop.or P₁ P₂ P₁_ih P₂_ih { from (
      have h: prop.subst x v (prop.or P₁ P₂) = (prop.subst x v P₁ ⋁ prop.subst x v P₂), by unfold prop.subst,
      have ¬ free_in_prop x P₁, from (
        assume : free_in_prop x P₁,
        have free_in_prop x (P₁ ⋁ P₂), from free_in_prop.or₁ this,
        show «false», from x_not_free this
      ),
      have h1: prop.subst x v P₁ = P₁, from P₁_ih this,
      have ¬ free_in_prop x P₂, from (
        assume : free_in_prop x P₂,
        have free_in_prop x (P₁ ⋁ P₂), from free_in_prop.or₂ this,
        show «false», from x_not_free this
      ),
      have h2: prop.subst x v P₂ = P₂, from P₂_ih this,
      have prop.subst x v (P₁ ⋁ P₂) = (P₁ ⋁ prop.subst x v P₂),
      from @eq.subst prop (λa, prop.subst x v (prop.or P₁ P₂) = (a ⋁ prop.subst x v P₂)) (prop.subst x v P₁) P₁ h1 h,
      show prop.subst x v (P₁ ⋁ P₂) = (P₁ ⋁ P₂),
      from @eq.subst prop (λa, prop.subst x v (prop.or P₁ P₂) = (P₁ ⋁ a)) (prop.subst x v P₂) P₂ h2 this
    )},
    case prop.pre t₁ t₂ { from (
      have h: prop.subst x v (prop.pre t₁ t₂) = prop.pre (term.subst x v t₁) (term.subst x v t₂), by unfold prop.subst,
      have ¬ free_in_term x t₁, from (
        assume : free_in_term x t₁,
        have free_in_prop x (prop.pre t₁ t₂), from free_in_prop.pre₁ this,
        show «false», from x_not_free this
      ),
      have h1: term.subst x v t₁ = t₁, from unchanged_of_subst_nonfree_term this,
      have ¬ free_in_term x t₂, from (
        assume : free_in_term x t₂,
        have free_in_prop x (prop.pre t₁ t₂), from free_in_prop.pre₂ this,
        show «false», from x_not_free this
      ),
      have h2: term.subst x v t₂ = t₂, from unchanged_of_subst_nonfree_term this,
      have prop.subst x v (prop.pre t₁ t₂) = prop.pre t₁ (term.subst x v t₂),
      from @eq.subst term (λa, prop.subst x v (prop.pre t₁ t₂) = prop.pre a (term.subst x v t₂)) (term.subst x v t₁) t₁ h1 h,
      show prop.subst x v (prop.pre t₁ t₂) = prop.pre t₁ t₂,
      from @eq.subst term (λa, prop.subst x v (prop.pre t₁ t₂) = prop.pre t₁ a) (term.subst x v t₂) t₂ h2 this
    )},
    case prop.pre₁ op t { from (
      have h: prop.subst x v (prop.pre₁ op t) = prop.pre₁ op (term.subst x v t), by unfold prop.subst,
      have ¬ free_in_term x t, from (
        assume : free_in_term x t,
        have free_in_prop x (prop.pre₁ op t), from free_in_prop.preop this,
        show «false», from x_not_free this
      ),
      have term.subst x v t = t, from unchanged_of_subst_nonfree_term this,
      show prop.subst x v (prop.pre₁ op t) = prop.pre₁ op t,
      from @eq.subst term (λa, prop.subst x v (prop.pre₁ op t) = prop.pre₁ op a) (term.subst x v t) t this h
    )},
    case prop.pre₂ op t₁ t₂ { from (
      have h: prop.subst x v (prop.pre₂ op t₁ t₂) = prop.pre₂ op (term.subst x v t₁) (term.subst x v t₂),
      by unfold prop.subst,
      have ¬ free_in_term x t₁, from (
        assume : free_in_term x t₁,
        have free_in_prop x (prop.pre₂ op t₁ t₂), from free_in_prop.preop₁ this,
        show «false», from x_not_free this
      ),
      have h1: term.subst x v t₁ = t₁, from unchanged_of_subst_nonfree_term this,
      have ¬ free_in_term x t₂, from (
        assume : free_in_term x t₂,
        have free_in_prop x (prop.pre₂ op t₁ t₂), from free_in_prop.preop₂ this,
        show «false», from x_not_free this
      ),
      have h2: term.subst x v t₂ = t₂, from unchanged_of_subst_nonfree_term this,
      have prop.subst x v (prop.pre₂ op t₁ t₂) = prop.pre₂ op t₁ (term.subst x v t₂),
      from @eq.subst term (λa, prop.subst x v (prop.pre₂ op t₁ t₂) = prop.pre₂ op a (term.subst x v t₂)) (term.subst x v t₁) t₁ h1 h,
      show prop.subst x v (prop.pre₂ op t₁ t₂) = prop.pre₂ op t₁ t₂,
      from @eq.subst term (λa, prop.subst x v (prop.pre₂ op t₁ t₂) = prop.pre₂ op t₁ a) (term.subst x v t₂) t₂ h2 this
    )},
    case prop.call t { from (
      have h: prop.subst x v (prop.call t) = prop.call (term.subst x v t), by unfold prop.subst,
      have ¬ free_in_term x t, from (
        assume : free_in_term x t,
        have free_in_prop x (prop.call t), from free_in_prop.call this,
        show «false», from x_not_free this
      ),
      have h1: term.subst x v t = t, from unchanged_of_subst_nonfree_term this,
      show prop.subst x v (prop.call t) = prop.call t,
      from @eq.subst term (λa, prop.subst x v (prop.call t) = prop.call a) (term.subst x v t) t h1 h
    )},
    case prop.post t₁ t₂ { from (
      have h: prop.subst x v (prop.post t₁ t₂) = prop.post (term.subst x v t₁) (term.subst x v t₂), by unfold prop.subst,
      have ¬ free_in_term x t₁, from (
        assume : free_in_term x t₁,
        have free_in_prop x (prop.post t₁ t₂), from free_in_prop.post₁ this,
        show «false», from x_not_free this
      ),
      have h1: term.subst x v t₁ = t₁, from unchanged_of_subst_nonfree_term this,
      have ¬ free_in_term x t₂, from (
        assume : free_in_term x t₂,
        have free_in_prop x (prop.post t₁ t₂), from free_in_prop.post₂ this,
        show «false», from x_not_free this
      ),
      have h2: term.subst x v t₂ = t₂, from unchanged_of_subst_nonfree_term this,
      have prop.subst x v (prop.post t₁ t₂) = prop.post t₁ (term.subst x v t₂),
      from @eq.subst term (λa, prop.subst x v (prop.post t₁ t₂) = prop.post a (term.subst x v t₂)) (term.subst x v t₁) t₁ h1 h,
      show prop.subst x v (prop.post t₁ t₂) = prop.post t₁ t₂,
      from @eq.subst term (λa, prop.subst x v (prop.post t₁ t₂) = prop.post t₁ a) (term.subst x v t₂) t₂ h2 this
    )},
    case prop.forallc y P' P'_ih { from (
      have h: prop.subst x v (prop.forallc y P')
            = prop.forallc y (if x = y then P' else prop.subst x v P'),
      by unfold prop.subst,

      if x_eq_y: x = y then (
        have (if x = y then P' else prop.subst x v P') = P', by simp[x_eq_y],
        show prop.subst x v (prop.forallc y P') = prop.forallc y P',
        from @eq.subst prop (λa, prop.subst x v (prop.forallc y P') = prop.forallc y a)
                            (if x = y then P' else prop.subst x v P') P' this h
      ) else (
        have (if x = y then P' else prop.subst x v P') = prop.subst x v P', by simp[x_eq_y],
        have h4: prop.subst x v (prop.forallc y P') = prop.forallc y (prop.subst x v P'),
        from @eq.subst prop (λa, prop.subst x v (prop.forallc y P') = prop.forallc y a)
                            (if x = y then P' else prop.subst x v P') (prop.subst x v P') this h,
        have ¬ free_in_prop x P', from (
          assume : free_in_prop x P',
          have free_in_prop x (prop.forallc y P'), from free_in_prop.forallc x_eq_y this,
          show «false», from x_not_free this
        ),
        have prop.subst x v P' = P', from P'_ih this,
        show prop.subst x v (prop.forallc y P') = prop.forallc y P',
        from @eq.subst prop (λa, prop.subst x v (prop.forallc y P')
                               = prop.forallc y a) (prop.subst x v P') P' this h4
      )
    )},
    case prop.exis y P' P'_ih { from (
      have h: prop.subst x v (prop.exis y P') = prop.exis y (if x = y then P' else prop.subst x v P'), by unfold prop.subst,
      if x_eq_y: x = y then (
        have (if x = y then P' else prop.subst x v P') = P', by simp[x_eq_y],
        show prop.subst x v (prop.exis y P') = prop.exis y P',
        from @eq.subst prop (λa, prop.subst x v (prop.exis y P') = prop.exis y a)
                          (if x = y then P' else prop.subst x v P') P' this h
      ) else (
        have (if x = y then P' else prop.subst x v P') = prop.subst x v P', by simp[x_eq_y],
        have h2: prop.subst x v (prop.exis y P') = prop.exis y (prop.subst x v P'),
        from @eq.subst prop (λa, prop.subst x v (prop.exis y P') = prop.exis y a)
                          (if x = y then P' else prop.subst x v P') (prop.subst x v P') this h,
        have ¬ free_in_prop x P', from (
          assume : free_in_prop x P',
          have free_in_prop x (prop.exis y P'), from free_in_prop.exis x_eq_y this,
          show «false», from x_not_free this
        ),
        have prop.subst x v P' = P', from P'_ih this,
        show prop.subst x v (prop.exis y P') = prop.exis y P',
        from @eq.subst prop (λa, prop.subst x v (prop.exis y P') = prop.exis y a) (prop.subst x v P') P' this h2
      )
    )}
  end

lemma unchanged_of_subst_nonfree_vc {P: vc} {x: var} {v: value}:
    x ∉ FV P → (vc.subst x v P = P) :=
  assume x_not_free: ¬ free_in_vc x P,
  begin
    induction P,
    case vc.term t { from (
      have h: vc.subst x v (vc.term t) = term.subst x v t, by unfold vc.subst,
      have ¬ free_in_term x t, from (
        assume : free_in_term x t,
        have free_in_vc x (vc.term t), from free_in_vc.term this,
        show «false», from x_not_free this
      ),
      have term.subst x v t = t, from unchanged_of_subst_nonfree_term this,
      show vc.subst x v t = vc.term t,
      from @eq.subst term (λa, vc.subst x v (vc.term t) = vc.term a) (term.subst x v t) t this h
    )},
    case vc.not P₁ ih { from (
      have h: vc.subst x v P₁.not = (vc.subst x v P₁).not, by unfold vc.subst,
      have ¬ free_in_vc x P₁, from (
        assume : free_in_vc x P₁,
        have free_in_vc x P₁.not, from free_in_vc.not this,
        show «false», from x_not_free this
      ),
      have vc.subst x v P₁ = P₁, from ih this,
      show vc.subst x v P₁.not = P₁.not,
      from @eq.subst vc (λa, vc.subst x v P₁.not = vc.not a) (vc.subst x v P₁) P₁ this h
    )},
    case vc.and P₁ P₂ P₁_ih P₂_ih { from (
      have h: vc.subst x v (vc.and P₁ P₂) = (vc.subst x v P₁ ⋀ vc.subst x v P₂), by unfold vc.subst,
      have ¬ free_in_vc x P₁, from (
        assume : free_in_vc x P₁,
        have free_in_vc x (P₁ ⋀ P₂), from free_in_vc.and₁ this,
        show «false», from x_not_free this
      ),
      have h1: vc.subst x v P₁ = P₁, from P₁_ih this,
      have ¬ free_in_vc x P₂, from (
        assume : free_in_vc x P₂,
        have free_in_vc x (P₁ ⋀ P₂), from free_in_vc.and₂ this,
        show «false», from x_not_free this
      ),
      have h2: vc.subst x v P₂ = P₂, from P₂_ih this,
      have vc.subst x v (P₁ ⋀ P₂) = (P₁ ⋀ vc.subst x v P₂),
      from @eq.subst vc (λa, vc.subst x v (vc.and P₁ P₂) = (a ⋀ vc.subst x v P₂)) (vc.subst x v P₁) P₁ h1 h,
      show vc.subst x v (P₁ ⋀ P₂) = (P₁ ⋀ P₂),
      from @eq.subst vc (λa, vc.subst x v (vc.and P₁ P₂) = (P₁ ⋀ a)) (vc.subst x v P₂) P₂ h2 this
    )},
    case vc.or P₁ P₂ P₁_ih P₂_ih { from (
      have h: vc.subst x v (vc.or P₁ P₂) = (vc.subst x v P₁ ⋁ vc.subst x v P₂), by unfold vc.subst,
      have ¬ free_in_vc x P₁, from (
        assume : free_in_vc x P₁,
        have free_in_vc x (P₁ ⋁ P₂), from free_in_vc.or₁ this,
        show «false», from x_not_free this
      ),
      have h1: vc.subst x v P₁ = P₁, from P₁_ih this,
      have ¬ free_in_vc x P₂, from (
        assume : free_in_vc x P₂,
        have free_in_vc x (P₁ ⋁ P₂), from free_in_vc.or₂ this,
        show «false», from x_not_free this
      ),
      have h2: vc.subst x v P₂ = P₂, from P₂_ih this,
      have vc.subst x v (P₁ ⋁ P₂) = (P₁ ⋁ vc.subst x v P₂),
      from @eq.subst vc (λa, vc.subst x v (vc.or P₁ P₂) = (a ⋁ vc.subst x v P₂)) (vc.subst x v P₁) P₁ h1 h,
      show vc.subst x v (P₁ ⋁ P₂) = (P₁ ⋁ P₂),
      from @eq.subst vc (λa, vc.subst x v (vc.or P₁ P₂) = (P₁ ⋁ a)) (vc.subst x v P₂) P₂ h2 this
    )},
    case vc.pre t₁ t₂ { from (
      have h: vc.subst x v (vc.pre t₁ t₂) = vc.pre (term.subst x v t₁) (term.subst x v t₂), by unfold vc.subst,
      have ¬ free_in_term x t₁, from (
        assume : free_in_term x t₁,
        have free_in_vc x (vc.pre t₁ t₂), from free_in_vc.pre₁ this,
        show «false», from x_not_free this
      ),
      have h1: term.subst x v t₁ = t₁, from unchanged_of_subst_nonfree_term this,
      have ¬ free_in_term x t₂, from (
        assume : free_in_term x t₂,
        have free_in_vc x (vc.pre t₁ t₂), from free_in_vc.pre₂ this,
        show «false», from x_not_free this
      ),
      have h2: term.subst x v t₂ = t₂, from unchanged_of_subst_nonfree_term this,
      have vc.subst x v (vc.pre t₁ t₂) = vc.pre t₁ (term.subst x v t₂),
      from @eq.subst term (λa, vc.subst x v (vc.pre t₁ t₂) = vc.pre a (term.subst x v t₂)) (term.subst x v t₁) t₁ h1 h,
      show vc.subst x v (vc.pre t₁ t₂) = vc.pre t₁ t₂,
      from @eq.subst term (λa, vc.subst x v (vc.pre t₁ t₂) = vc.pre t₁ a) (term.subst x v t₂) t₂ h2 this
    )},
    case vc.pre₁ op t { from (
      have h: vc.subst x v (vc.pre₁ op t) = vc.pre₁ op (term.subst x v t), by unfold vc.subst,
      have ¬ free_in_term x t, from (
        assume : free_in_term x t,
        have free_in_vc x (vc.pre₁ op t), from free_in_vc.preop this,
        show «false», from x_not_free this
      ),
      have term.subst x v t = t, from unchanged_of_subst_nonfree_term this,
      show vc.subst x v (vc.pre₁ op t) = vc.pre₁ op t,
      from @eq.subst term (λa, vc.subst x v (vc.pre₁ op t) = vc.pre₁ op a) (term.subst x v t) t this h
    )},
    case vc.pre₂ op t₁ t₂ { from (
      have h: vc.subst x v (vc.pre₂ op t₁ t₂) = vc.pre₂ op (term.subst x v t₁) (term.subst x v t₂),
      by unfold vc.subst,
      have ¬ free_in_term x t₁, from (
        assume : free_in_term x t₁,
        have free_in_vc x (vc.pre₂ op t₁ t₂), from free_in_vc.preop₁ this,
        show «false», from x_not_free this
      ),
      have h1: term.subst x v t₁ = t₁, from unchanged_of_subst_nonfree_term this,
      have ¬ free_in_term x t₂, from (
        assume : free_in_term x t₂,
        have free_in_vc x (vc.pre₂ op t₁ t₂), from free_in_vc.preop₂ this,
        show «false», from x_not_free this
      ),
      have h2: term.subst x v t₂ = t₂, from unchanged_of_subst_nonfree_term this,
      have vc.subst x v (vc.pre₂ op t₁ t₂) = vc.pre₂ op t₁ (term.subst x v t₂),
      from @eq.subst term (λa, vc.subst x v (vc.pre₂ op t₁ t₂) = vc.pre₂ op a (term.subst x v t₂)) (term.subst x v t₁) t₁ h1 h,
      show vc.subst x v (vc.pre₂ op t₁ t₂) = vc.pre₂ op t₁ t₂,
      from @eq.subst term (λa, vc.subst x v (vc.pre₂ op t₁ t₂) = vc.pre₂ op t₁ a) (term.subst x v t₂) t₂ h2 this
    )},
    case vc.post t₁ t₂ { from (
      have h: vc.subst x v (vc.post t₁ t₂) = vc.post (term.subst x v t₁) (term.subst x v t₂), by unfold vc.subst,
      have ¬ free_in_term x t₁, from (
        assume : free_in_term x t₁,
        have free_in_vc x (vc.post t₁ t₂), from free_in_vc.post₁ this,
        show «false», from x_not_free this
      ),
      have h1: term.subst x v t₁ = t₁, from unchanged_of_subst_nonfree_term this,
      have ¬ free_in_term x t₂, from (
        assume : free_in_term x t₂,
        have free_in_vc x (vc.post t₁ t₂), from free_in_vc.post₂ this,
        show «false», from x_not_free this
      ),
      have h2: term.subst x v t₂ = t₂, from unchanged_of_subst_nonfree_term this,
      have vc.subst x v (vc.post t₁ t₂) = vc.post t₁ (term.subst x v t₂),
      from @eq.subst term (λa, vc.subst x v (vc.post t₁ t₂) = vc.post a (term.subst x v t₂)) (term.subst x v t₁) t₁ h1 h,
      show vc.subst x v (vc.post t₁ t₂) = vc.post t₁ t₂,
      from @eq.subst term (λa, vc.subst x v (vc.post t₁ t₂) = vc.post t₁ a) (term.subst x v t₂) t₂ h2 this
    )},
    case vc.univ y P' P'_ih { from (
      have h: vc.subst x v (vc.univ y P') = vc.univ y (if x = y then P' else vc.subst x v P'), by unfold vc.subst,
      if x_eq_y: x = y then (
        have (if x = y then P' else vc.subst x v P') = P', by simp[x_eq_y],
        show vc.subst x v (vc.univ y P') = vc.univ y P',
        from @eq.subst vc (λa, vc.subst x v (vc.univ y P') = vc.univ y a)
                          (if x = y then P' else vc.subst x v P') P' this h
      ) else (
        have (if x = y then P' else vc.subst x v P') = vc.subst x v P', by simp[x_eq_y],
        have h2: vc.subst x v (vc.univ y P') = vc.univ y (vc.subst x v P'),
        from @eq.subst vc (λa, vc.subst x v (vc.univ y P') = vc.univ y a)
                          (if x = y then P' else vc.subst x v P') (vc.subst x v P') this h,
        have ¬ free_in_vc x P', from (
          assume : free_in_vc x P',
          have free_in_vc x (vc.univ y P'), from free_in_vc.univ x_eq_y this,
          show «false», from x_not_free this
        ),
        have vc.subst x v P' = P', from P'_ih this,
        show vc.subst x v (vc.univ y P') = vc.univ y P',
        from @eq.subst vc (λa, vc.subst x v (vc.univ y P') = vc.univ y a) (vc.subst x v P') P' this h2
      )
    )}
  end

lemma unchanged_of_subst_env_nonfree_vc {P: vc}:
    closed P → (∀σ, vc.subst_env σ P = P) :=
  assume x_not_free: (∀x, x ∉ FV P),
  assume σ: env,
  begin
    induction σ with σ' x v ih,

    show (vc.subst_env env.empty P = P), by unfold vc.subst_env,

    show (vc.subst_env (σ'[x↦v]) P = P), by calc
        vc.subst_env (σ'[x↦v]) P = vc.subst x v (vc.subst_env σ' P) : by unfold vc.subst_env
                             ... = vc.subst x v P : by rw[ih]
                             ... = P : unchanged_of_subst_nonfree_vc (x_not_free x)
  end

lemma free_of_subst_term {t: term} {x y: var} {v: value}:
          free_in_term x (term.subst y v t) → x ≠ y ∧ free_in_term x t :=
  assume x_free_in_subst: free_in_term x (term.subst y v t),
  begin
    induction t with v' z unop t₁ t₁_ih binop t₂ t₃ t₂_ih t₃_ih t₄ t₅ t₄_ih t₅_ih,
    show x ≠ y ∧ free_in_term x (term.value v'), from (
      have term.subst y v (term.value v') = v', by unfold term.subst,
      have free_in_term x v', from this ▸ x_free_in_subst,
      show x ≠ y ∧ free_in_term x (term.value v'), from absurd this free_in_term.value.inv
    ),
    show x ≠ y ∧ free_in_term x (term.var z), from (
      have hite: term.subst y v (term.var z) = (if y = z then v else z), by unfold term.subst,
      if y_is_z: y = z then
        have term.subst y v (term.var z) = v, by { simp[y_is_z] at hite, rw[y_is_z], from hite },
        have free_in_term x v, from this ▸ x_free_in_subst,
        show x ≠ y ∧ free_in_term x (term.var z), from absurd this free_in_term.value.inv
      else
        have term.subst y v (term.var z) = z, by { simp[y_is_z] at hite, from hite },
        have free_in_term x z, from this ▸ x_free_in_subst,
        have x_is_z: x = z, from free_in_term.var.inv this,
        have x ≠ y, from x_is_z.symm ▸ (ne.symm y_is_z),
        show x ≠ y ∧ free_in_term x (term.var z), from ⟨this, x_is_z ▸ free_in_term.var x⟩
    ),
    show x ≠ y ∧ free_in_term x (term.unop unop t₁), from (
      have term.subst y v (term.unop unop t₁) = term.unop unop (term.subst y v t₁), by unfold term.subst,
      have free_in_term x (term.unop unop (term.subst y v t₁)), from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₁), from free_in_term.unop.inv this,
      have x ≠ y ∧ free_in_term x t₁, from t₁_ih this,
      show x ≠ y ∧ free_in_term x (term.unop unop t₁), from ⟨this.left, free_in_term.unop this.right⟩
    ),
    show x ≠ y ∧ free_in_term x (term.binop binop t₂ t₃), from (
      have term.subst y v (term.binop binop t₂ t₃) = term.binop binop (term.subst y v t₂) (term.subst y v t₃),
      by unfold term.subst,
      have free_in_term x (term.binop binop (term.subst y v t₂) (term.subst y v t₃)), from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₂) ∨ free_in_term x (term.subst y v t₃), from free_in_term.binop.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₂),
        have x ≠ y ∧ free_in_term x t₂, from t₂_ih this,
        show x ≠ y ∧ free_in_term x (term.binop binop t₂ t₃), from ⟨this.left, free_in_term.binop₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₃),
        have x ≠ y ∧ free_in_term x t₃, from t₃_ih this,
        show x ≠ y ∧ free_in_term x (term.binop binop t₂ t₃), from ⟨this.left, free_in_term.binop₂ this.right⟩
      )
    ),
    show x ≠ y ∧ free_in_term x (term.app t₄ t₅), from (
      have term.subst y v (term.app t₄ t₅) = term.app (term.subst y v t₄) (term.subst y v t₅),
      by unfold term.subst,
      have free_in_term x (term.app (term.subst y v t₄) (term.subst y v t₅)), from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₄) ∨ free_in_term x (term.subst y v t₅), from free_in_term.app.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₄),
        have x ≠ y ∧ free_in_term x t₄, from t₄_ih this,
        show x ≠ y ∧ free_in_term x (term.app t₄ t₅), from ⟨this.left, free_in_term.app₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₅),
        have x ≠ y ∧ free_in_term x t₅, from t₅_ih this,
        show x ≠ y ∧ free_in_term x (term.app t₄ t₅), from ⟨this.left, free_in_term.app₂ this.right⟩
      )
    )
  end

lemma free_of_substt_same_term {t t': term} {x: var}:
          free_in_term x (term.substt x t' t) → free_in_term x t' :=
  assume x_free_in_subst: free_in_term x (term.substt x t' t),
  begin
    induction t with v' z unop t₁ t₁_ih binop t₂ t₃ t₂_ih t₃_ih t₄ t₅ t₄_ih t₅_ih,
    show free_in_term x t', from (
      have term.substt x t' (term.value v') = v', by unfold term.substt,
      have free_in_term x v', from this ▸ x_free_in_subst,
      show free_in_term x t', from absurd this free_in_term.value.inv
    ),
    show free_in_term x t', from (
      have hite: term.substt x t' (term.var z) = (if x = z then t' else z), by unfold term.substt,
      if x_is_z: x = z then
        have term.substt x t' (term.var z) = t', by { simp[x_is_z] at hite, rw[x_is_z], from hite },
        show free_in_term x t', from this ▸ x_free_in_subst
      else
        have term.substt x t' (term.var z) = z, by { simp[x_is_z] at hite, from hite },
        have free_in_term x z, from this ▸ x_free_in_subst,
        have x_iss_z: x = z, from free_in_term.var.inv this,
        show free_in_term x t', from absurd x_iss_z x_is_z
    ),
    show free_in_term x t', from (
      have term.substt x t' (term.unop unop t₁) = term.unop unop (term.substt x t' t₁), by unfold term.substt,
      have free_in_term x (term.unop unop (term.substt x t' t₁)), from this ▸ x_free_in_subst,
      have free_in_term x (term.substt x t' t₁), from free_in_term.unop.inv this,
      show free_in_term x t', from t₁_ih this
    ),
    show free_in_term x t', from (
      have term.substt x t' (term.binop binop t₂ t₃) = term.binop binop (term.substt x t' t₂) (term.substt x t' t₃),
      by unfold term.substt,
      have free_in_term x (term.binop binop (term.substt x t' t₂) (term.substt x t' t₃)), from this ▸ x_free_in_subst,
      have free_in_term x (term.substt x t' t₂) ∨ free_in_term x (term.substt x t' t₃),
      from free_in_term.binop.inv this,
      or.elim this (
        assume : free_in_term x (term.substt x t' t₂),
        show free_in_term x t', from t₂_ih this
      ) (
        assume : free_in_term x (term.substt x t' t₃),
        show free_in_term x t', from t₃_ih this
      )
    ),
    show free_in_term x t', from (
      have term.substt x t' (term.app t₄ t₅) = term.app (term.substt x t' t₄) (term.substt x t' t₅),
      by unfold term.substt,
      have free_in_term x (term.app (term.substt x t' t₄) (term.substt x t' t₅)), from this ▸ x_free_in_subst,
      have free_in_term x (term.substt x t' t₄) ∨ free_in_term x (term.substt x t' t₅), from free_in_term.app.inv this,
      or.elim this (
        assume : free_in_term x (term.substt x t' t₄),
        show free_in_term x t', from t₄_ih this
      ) (
        assume : free_in_term x (term.substt x t' t₅),
        show free_in_term x t', from t₅_ih this
      )
    )
  end

lemma free_of_subst_env_term_step {t: term} {σ: env} {x y: var} {v: value}:
        free_in_term x (term.subst_env (σ[y↦v]) t) → x ≠ y ∧ free_in_term x (term.subst_env σ t) :=
  assume x_free: free_in_term x (term.subst_env (σ[y↦v]) t),
  have term.subst_env (σ[y↦v]) t = term.subst y v (term.subst_env σ t), by unfold term.subst_env,
  have free_in_term x (term.subst y v (term.subst_env σ t)), from this ▸ x_free,
  show x ≠ y ∧ free_in_term x (term.subst_env σ t), from free_of_subst_term this

lemma free_of_subst_env_term {t: term} {σ: env} {x: var}:
        free_in_term x (term.subst_env σ t) → free_in_term x t ∧ x ∉ σ :=
  assume x_free_in_subst: free_in_term x (term.subst_env σ t),
  begin
    induction σ with σ' y v ih,
    show free_in_term x t ∧ x ∉ env.empty, from (
      have h2: x ∉ env.empty, by begin
        assume : x ∈ env.empty,
        have h3: env.contains env.empty x, from this,
        cases h3
      end,
      have term.subst_env env.empty t = t, by unfold term.subst_env,
      show free_in_term x t ∧ x ∉ env.empty, from ⟨this ▸ x_free_in_subst, h2⟩
    ),
    show free_in_term x t ∧ x ∉ (σ'[y↦v]), from (
      have h1: x ≠ y ∧ free_in_term x (term.subst_env σ' t),
      from free_of_subst_env_term_step x_free_in_subst,
      have h2: free_in_term x t ∧ x ∉ σ', from ih h1.right,
      have h3: x ∉ (σ'[y↦v]), by begin
        assume : x ∈ (σ'[y↦v]),
        have h3: env.contains (σ'[y↦v]) x, from this,
        cases h3,
        have h4: x ≠ x, from h1.left,
        contradiction,
        have h5: ¬ env.contains σ' x, from h2.right,
        contradiction
      end,
      show free_in_term x t ∧ x ∉ (σ'[y↦v]), from ⟨h2.left, h3⟩
    )
  end

lemma free_of_subst_prop {P: prop} {x y: var} {v: value}:
          free_in_prop x (prop.subst y v P) → x ≠ y ∧ free_in_prop x P :=
  assume x_free_in_subst: free_in_prop x (prop.subst y v P),
  begin
    induction P,
    case prop.term t { from (
      have prop.subst y v (prop.term t) = (term.subst y v t), by unfold prop.subst,
      have free_in_prop x (term.subst y v t), from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t), from free_in_prop.term.inv this,
      have x ≠ y ∧ free_in_term x t, from free_of_subst_term this,
      show x ≠ y ∧ free_in_prop x (prop.term t), from ⟨this.left, free_in_prop.term this.right⟩
    )},
    case prop.not P₁ P₁_ih { from (
      have (prop.subst y v P₁.not = (prop.subst y v P₁).not), by unfold prop.subst,
      have free_in_prop x (prop.subst y v P₁).not, from this ▸ x_free_in_subst,
      have free_in_prop x (prop.subst y v P₁), from free_in_prop.not.inv this,
      have x ≠ y ∧ free_in_prop x P₁, from P₁_ih this,
      show x ≠ y ∧ free_in_prop x P₁.not, from ⟨this.left, free_in_prop.not this.right⟩
    )},
    case prop.and P₂ P₃ P₂_ih P₃_ih { from (
      have prop.subst y v (prop.and P₂ P₃) = (prop.subst y v P₂ ⋀ prop.subst y v P₃), by unfold prop.subst,
      have free_in_prop x ((prop.subst y v P₂) ⋀ (prop.subst y v P₃)), from this ▸ x_free_in_subst,
      have free_in_prop x (prop.subst y v P₂) ∨ free_in_prop x (prop.subst y v P₃),
      from free_in_prop.and.inv this,
      or.elim this (
        assume : free_in_prop x (prop.subst y v P₂),
        have x ≠ y ∧ free_in_prop x P₂, from P₂_ih this,
        show x ≠ y ∧ free_in_prop x (P₂ ⋀ P₃), from ⟨this.left, free_in_prop.and₁ this.right⟩
      ) (
        assume : free_in_prop x (prop.subst y v P₃),
        have x ≠ y ∧ free_in_prop x P₃, from P₃_ih this,
        show x ≠ y ∧ free_in_prop x (P₂ ⋀ P₃), from ⟨this.left, free_in_prop.and₂ this.right⟩
      )
    )},
    case prop.or P₄ P₅ P₄_ih P₅_ih { from (
      have prop.subst y v (prop.or P₄ P₅) = (prop.subst y v P₄ ⋁ prop.subst y v P₅), by unfold prop.subst,
      have free_in_prop x (prop.or (prop.subst y v P₄) (prop.subst y v P₅)),
      from this ▸ x_free_in_subst,
      have free_in_prop x (prop.subst y v P₄) ∨ free_in_prop x (prop.subst y v P₅),
      from free_in_prop.or.inv this,
      or.elim this (
        assume : free_in_prop x (prop.subst y v P₄),
        have x ≠ y ∧ free_in_prop x P₄, from P₄_ih this,
        show x ≠ y ∧ free_in_prop x (prop.or P₄ P₅), from ⟨this.left, free_in_prop.or₁ this.right⟩
      ) (
        assume : free_in_prop x (prop.subst y v P₅),
        have x ≠ y ∧ free_in_prop x P₅, from P₅_ih this,
        show x ≠ y ∧ free_in_prop x (prop.or P₄ P₅), from ⟨this.left, free_in_prop.or₂ this.right⟩
      )
    )},
    case prop.pre t₁ t₂ { from (
      have prop.subst y v (prop.pre t₁ t₂) = prop.pre (term.subst y v t₁) (term.subst y v t₂), by unfold prop.subst,
      have free_in_prop x (prop.pre (term.subst y v t₁) (term.subst y v t₂)),
      from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₁) ∨ free_in_term x (term.subst y v t₂), from free_in_prop.pre.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₁),
        have x ≠ y ∧ free_in_term x t₁, from free_of_subst_term this,
        show x ≠ y ∧ free_in_prop x (prop.pre t₁ t₂), from ⟨this.left, free_in_prop.pre₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₂),
        have x ≠ y ∧ free_in_term x t₂, from free_of_subst_term this,
        show x ≠ y ∧ free_in_prop x (prop.pre t₁ t₂), from ⟨this.left, free_in_prop.pre₂ this.right⟩
      )
    )},
    case prop.pre₁ op t { from (
      have prop.subst y v (prop.pre₁ op t) = prop.pre₁ op (term.subst y v t), by unfold prop.subst,
      have free_in_prop x (prop.pre₁ op (term.subst y v t)),
      from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t), from free_in_prop.pre₁.inv this,
      have x ≠ y ∧ free_in_term x t, from free_of_subst_term this,
      show x ≠ y ∧ free_in_prop x (prop.pre₁ op t), from ⟨this.left, free_in_prop.preop this.right⟩
    )},
    case prop.pre₂ op t₁ t₂ { from (
      have prop.subst y v (prop.pre₂ op t₁ t₂) = prop.pre₂ op (term.subst y v t₁) (term.subst y v t₂),
      by unfold prop.subst,
      have free_in_prop x (prop.pre₂ op (term.subst y v t₁) (term.subst y v t₂)),
      from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₁) ∨ free_in_term x (term.subst y v t₂), from free_in_prop.pre₂.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₁),
        have x ≠ y ∧ free_in_term x t₁, from free_of_subst_term this,
        show x ≠ y ∧ free_in_prop x (prop.pre₂ op t₁ t₂), from ⟨this.left, free_in_prop.preop₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₂),
        have x ≠ y ∧ free_in_term x t₂, from free_of_subst_term this,
        show x ≠ y ∧ free_in_prop x (prop.pre₂ op t₁ t₂), from ⟨this.left, free_in_prop.preop₂ this.right⟩
      )
    )},
    case prop.post t₁ t₂ { from (
      have prop.subst y v (prop.post t₁ t₂) = prop.post (term.subst y v t₁) (term.subst y v t₂), by unfold prop.subst,
      have free_in_prop x (prop.post (term.subst y v t₁) (term.subst y v t₂)),
      from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₁) ∨ free_in_term x (term.subst y v t₂), from free_in_prop.post.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₁),
        have x ≠ y ∧ free_in_term x t₁, from free_of_subst_term this,
        show x ≠ y ∧ free_in_prop x (prop.post t₁ t₂), from ⟨this.left, free_in_prop.post₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₂),
        have x ≠ y ∧ free_in_term x t₂, from free_of_subst_term this,
        show x ≠ y ∧ free_in_prop x (prop.post t₁ t₂), from ⟨this.left, free_in_prop.post₂ this.right⟩
      )
    )},
    case prop.call t { from (
      have prop.subst y v (prop.call t) = prop.call (term.subst y v t), by unfold prop.subst,
      have free_in_prop x (prop.call (term.subst y v t)),
      from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t), from free_in_prop.call.inv this,
      have x ≠ y ∧ free_in_term x t, from free_of_subst_term this,
      show x ≠ y ∧ free_in_prop x (prop.call t), from ⟨this.left, free_in_prop.call this.right⟩
    )},
    case prop.forallc z P ih { from (
      have prop.subst y v (prop.forallc z P)
         = prop.forallc z (if y = z then P else P.subst y v),
      by unfold prop.subst,
      have free_in_prop x (prop.forallc z (if y = z then P else P.subst y v)),
      from this ▸ x_free_in_subst,
      have x_neq_z: x ≠ z, from (free_in_prop.forallc.inv this).left,
      have fre_ite: free_in_prop x (if y = z then P else P.subst y v),
      from (free_in_prop.forallc.inv this).right,
      if y_eq_z: y = z then (
        have x_neq_y: x ≠ y, from y_eq_z.symm ▸ x_neq_z,
        have free_in_prop x P, by { simp[y_eq_z] at fre_ite, from fre_ite },
        show x ≠ y ∧ free_in_prop x (prop.forallc z P), from ⟨x_neq_y, free_in_prop.forallc x_neq_z this⟩
      ) else (
        have free_in_prop x (P.subst y v), by { simp[y_eq_z] at fre_ite, from fre_ite },
        have x ≠ y ∧ free_in_prop x P, from ih this,
        show x ≠ y ∧ free_in_prop x (prop.forallc z P), from ⟨this.left, free_in_prop.forallc x_neq_z this.right⟩
      )
    )},
    case prop.exis z P ih { from (
      have prop.subst y v (prop.exis z P) = prop.exis z (if y = z then P else P.subst y v),
      by unfold prop.subst,
      have free_in_prop x (prop.exis z (if y = z then P else P.subst y v)),
      from this ▸ x_free_in_subst,
      have x_neq_z: x ≠ z, from (free_in_prop.exis.inv this).left,
      have fre_ite: free_in_prop x (if y = z then P else P.subst y v), from (free_in_prop.exis.inv this).right,
      if y_eq_z: y = z then (
        have x_neq_y: x ≠ y, from y_eq_z.symm ▸ x_neq_z,
        have free_in_prop x P, by { simp[y_eq_z] at fre_ite, from fre_ite },
        show x ≠ y ∧ free_in_prop x (prop.exis z P), from ⟨x_neq_y, free_in_prop.exis x_neq_z this⟩
      ) else (
        have free_in_prop x (P.subst y v), by { simp[y_eq_z] at fre_ite, from fre_ite },
        have x ≠ y ∧ free_in_prop x P, from ih this,
        show x ≠ y ∧ free_in_prop x (prop.exis z P), from ⟨this.left, free_in_prop.exis x_neq_z this.right⟩
      )
    )}
  end

lemma free_of_subst_env_prop {P: prop} {σ: env} {x y: var} {v: value}:
        free_in_prop x (prop.subst_env (σ[y↦v]) P) → x ≠ y ∧ free_in_prop x (prop.subst_env σ P) :=
  assume x_free: free_in_prop x (prop.subst_env (σ[y↦v]) P),
  have prop.subst_env (σ[y↦v]) P = prop.subst y v (prop.subst_env σ P), by unfold prop.subst_env,
  have free_in_prop x (prop.subst y v (prop.subst_env σ P)), from this ▸ x_free,
  show x ≠ y ∧ free_in_prop x (prop.subst_env σ P), from free_of_subst_prop this

lemma free_of_subst_env {P: prop} {σ: env} {x: var}:
        free_in_prop x (prop.subst_env σ P) → free_in_prop x P :=
  assume x_free_in_subst: free_in_prop x (prop.subst_env σ P),
  begin
    induction σ with σ' y v ih,
    show free_in_prop x P, from (
      have prop.subst_env env.empty P = P, by unfold prop.subst_env,
      show free_in_prop x P, from this ▸ x_free_in_subst
    ),
    show free_in_prop x P, from (
      have free_in_prop x (prop.subst_env σ' P), from (free_of_subst_env_prop x_free_in_subst).right,
      show free_in_prop x P, from ih this
    )
  end

lemma free_in_vc.subst {P: vc} {x y: var} {v: value}:
          free_in_vc x (vc.subst y v P) → x ≠ y ∧ free_in_vc x P :=
  assume x_free_in_subst: free_in_vc x (vc.subst y v P),
  begin
    induction P,
    case vc.term t { from (
      have vc.subst y v (vc.term t) = term.subst y v t, by unfold vc.subst,
      have free_in_vc x (vc.term (term.subst y v t)), from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t), from free_in_vc.term.inv this,
      have x ≠ y ∧ free_in_term x t, from free_of_subst_term this,
      show x ≠ y ∧ free_in_vc x (vc.term t), from ⟨this.left, free_in_vc.term this.right⟩
    )},
    case vc.not P₁ ih { from (
      have (vc.subst y v P₁.not = (vc.subst y v P₁).not), by unfold vc.subst,
      have free_in_vc x (vc.subst y v P₁).not, from this ▸ x_free_in_subst,
      have free_in_vc x (vc.subst y v P₁), from free_in_vc.not.inv this,
      have x ≠ y ∧ free_in_vc x P₁, from ih this,
      show x ≠ y ∧ free_in_vc x P₁.not, from ⟨this.left, free_in_vc.not this.right⟩
    )},
    case vc.and P₁ P₂ P₁_ih P₂_ih { from (
      have vc.subst y v (vc.and P₁ P₂) = (vc.subst y v P₁ ⋀ vc.subst y v P₂), by unfold vc.subst,
      have free_in_vc x (vc.subst y v P₁ ⋀ vc.subst y v P₂), from this ▸ x_free_in_subst,
      have free_in_vc x (vc.subst y v P₁) ∨ free_in_vc x (vc.subst y v P₂),
      from free_in_vc.and.inv this,
      or.elim this (
        assume : free_in_vc x (vc.subst y v P₁),
        have x ≠ y ∧ free_in_vc x P₁, from P₁_ih this,
        show x ≠ y ∧ free_in_vc x (P₁ ⋀ P₂), from ⟨this.left, free_in_vc.and₁ this.right⟩
      ) (
        assume : free_in_vc x (vc.subst y v P₂),
        have x ≠ y ∧ free_in_vc x P₂, from P₂_ih this,
        show x ≠ y ∧ free_in_vc x (P₁ ⋀ P₂), from ⟨this.left, free_in_vc.and₂ this.right⟩
      )
    )},
    case vc.or P₁ P₂ P₁_ih P₂_ih { from (
      have vc.subst y v (vc.or P₁ P₂) = (vc.subst y v P₁ ⋁ vc.subst y v P₂), by unfold vc.subst,
      have free_in_vc x (vc.or (vc.subst y v P₁) (vc.subst y v P₂)),
      from this ▸ x_free_in_subst,
      have free_in_vc x (vc.subst y v P₁) ∨ free_in_vc x (vc.subst y v P₂),
      from free_in_vc.or.inv this,
      or.elim this (
        assume : free_in_vc x (vc.subst y v P₁),
        have x ≠ y ∧ free_in_vc x P₁, from P₁_ih this,
        show x ≠ y ∧ free_in_vc x (vc.or P₁ P₂), from ⟨this.left, free_in_vc.or₁ this.right⟩
      ) (
        assume : free_in_vc x (vc.subst y v P₂),
        have x ≠ y ∧ free_in_vc x P₂, from P₂_ih this,
        show x ≠ y ∧ free_in_vc x (vc.or P₁ P₂), from ⟨this.left, free_in_vc.or₂ this.right⟩
      )
    )},
    case vc.pre t₁ t₂ { from (
      have vc.subst y v (vc.pre t₁ t₂) = vc.pre (term.subst y v t₁) (term.subst y v t₂), by unfold vc.subst,
      have free_in_vc x (vc.pre (term.subst y v t₁) (term.subst y v t₂)),
      from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₁) ∨ free_in_term x (term.subst y v t₂),
      from free_in_vc.pre.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₁),
        have x ≠ y ∧ free_in_term x t₁, from free_of_subst_term this,
        show x ≠ y ∧ free_in_vc x (vc.pre t₁ t₂), from ⟨this.left, free_in_vc.pre₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₂),
        have x ≠ y ∧ free_in_term x t₂, from free_of_subst_term this,
        show x ≠ y ∧ free_in_vc x (vc.pre t₁ t₂), from ⟨this.left, free_in_vc.pre₂ this.right⟩
      )
    )},
    case vc.pre₁ op t { from (
      have vc.subst y v (vc.pre₁ op t) = vc.pre₁ op (term.subst y v t), by unfold vc.subst,
      have free_in_vc x (vc.pre₁ op (term.subst y v t)), from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t), from free_in_vc.pre₁.inv this,
      have x ≠ y ∧ free_in_term x t, from free_of_subst_term this,
      show x ≠ y ∧ free_in_vc x (vc.pre₁ op t), from ⟨this.left, free_in_vc.preop this.right⟩
    )},
    case vc.pre₂ op t₁ t₂ { from (
      have vc.subst y v (vc.pre₂ op t₁ t₂) = vc.pre₂ op (term.subst y v t₁) (term.subst y v t₂),
      by unfold vc.subst,
      have free_in_vc x (vc.pre₂ op (term.subst y v t₁) (term.subst y v t₂)), from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₁) ∨ free_in_term x (term.subst y v t₂),
      from free_in_vc.pre₂.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₁),
        have x ≠ y ∧ free_in_term x t₁, from free_of_subst_term this,
        show x ≠ y ∧ free_in_vc x (vc.pre₂ op t₁ t₂), from ⟨this.left, free_in_vc.preop₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₂),
        have x ≠ y ∧ free_in_term x t₂, from free_of_subst_term this,
        show x ≠ y ∧ free_in_vc x (vc.pre₂ op t₁ t₂), from ⟨this.left, free_in_vc.preop₂ this.right⟩
      )
    )},
    case vc.post t₁ t₂ { from (
      have vc.subst y v (vc.post t₁ t₂) = vc.post (term.subst y v t₁) (term.subst y v t₂), by unfold vc.subst,
      have free_in_vc x (vc.post (term.subst y v t₁) (term.subst y v t₂)),
      from this ▸ x_free_in_subst,
      have free_in_term x (term.subst y v t₁) ∨ free_in_term x (term.subst y v t₂),
      from free_in_vc.post.inv this,
      or.elim this (
        assume : free_in_term x (term.subst y v t₁),
        have x ≠ y ∧ free_in_term x t₁, from free_of_subst_term this,
        show x ≠ y ∧ free_in_vc x (vc.post t₁ t₂), from ⟨this.left, free_in_vc.post₁ this.right⟩
      ) (
        assume : free_in_term x (term.subst y v t₂),
        have x ≠ y ∧ free_in_term x t₂, from free_of_subst_term this,
        show x ≠ y ∧ free_in_vc x (vc.post t₁ t₂), from ⟨this.left, free_in_vc.post₂ this.right⟩
      )
    )},
    case vc.univ z P' P'_ih { from (
      have h: vc.subst y v (vc.univ z P') = vc.univ z (if y = z then P' else vc.subst y v P'), by unfold vc.subst,
      if y_eq_z: y = z then (
        have (if y = z then P' else vc.subst y v P') = P', by simp[y_eq_z],
        have vc.subst y v (vc.univ z P') = vc.univ z P',
        from @eq.subst vc (λa, vc.subst y v (vc.univ z P') = vc.univ z a)
                          (if y = z then P' else vc.subst y v P') P' this h,
        have h2: free_in_vc x (vc.univ z P'),
        from @eq.subst vc (λa, free_in_vc x a) (vc.subst y v (vc.univ z P')) (vc.univ z P') this x_free_in_subst,
        have x ≠ y, from (
          assume : x = y,
          have x = z, from eq.trans this y_eq_z,
          have free_in_vc x (vc.univ x P'),
          from @eq.subst var (λa, free_in_vc x (vc.univ a P')) z x this.symm h2,
          show «false», from (free_in_vc.univ.same.inv) this
        ),
        show x ≠ y ∧ free_in_vc x (vc.univ z P'), from ⟨this, h2⟩
      ) else (
        have (if y = z then P' else vc.subst y v P') = vc.subst y v P', by simp[y_eq_z],
        have vc.subst y v (vc.univ z P') = vc.univ z (vc.subst y v P'),
        from @eq.subst vc (λa, vc.subst y v (vc.univ z P') = vc.univ z a)
                          (if y = z then P' else vc.subst y v P') (vc.subst y v P') this h,
        have free_in_vc x (vc.univ z (vc.subst y v P')), from this ▸ x_free_in_subst,
        have h2: x ≠ z ∧ free_in_vc x (vc.subst y v P'), from free_in_vc.univ.inv this,
        have x ≠ y ∧ free_in_vc x P', from P'_ih h2.right,
        show x ≠ y ∧ free_in_vc x (vc.univ z P'), from ⟨this.left, free_in_vc.univ h2.left this.right⟩
      )
    )}
  end

lemma free_in_vc.subst2 {P: vc} {σ: env} {x y: var} {v: value}:
        free_in_vc x (vc.subst_env (σ[y↦v]) P) → x ≠ y ∧ free_in_vc x (vc.subst_env σ P) :=
  assume x_free: free_in_vc x (vc.subst_env (σ[y↦v]) P),
  have vc.subst_env (σ[y↦v]) P = vc.subst y v (vc.subst_env σ P), by unfold vc.subst_env,
  have free_in_vc x (vc.subst y v (vc.subst_env σ P)), from this ▸ x_free,
  show x ≠ y ∧ free_in_vc x (vc.subst_env σ P), from free_in_vc.subst this

lemma free_in_vc.subst_env {P: vc} {σ: env} {x: var}:
        free_in_vc x (vc.subst_env σ P) → free_in_vc x P :=
  assume x_free_in_subst: free_in_vc x (vc.subst_env σ P),
  begin
    induction σ with σ' y v ih,
    show free_in_vc x P, from (
      have vc.subst_env env.empty P = P, by unfold vc.subst_env,
      show free_in_vc x P, from this ▸ x_free_in_subst
    ),
    show free_in_vc x P, from (
      have free_in_vc x (vc.subst_env σ' P), from (free_in_vc.subst2 x_free_in_subst).right,
      show free_in_vc x P, from ih this
    )
  end

lemma term.subst_env.var.inv {x: var} {σ: env}:
  (term.subst_env σ x = x) ∨ (∃v:value, term.subst_env σ x = v) :=
  begin
    induction σ with σ' y v' ih,
    show (term.subst_env env.empty x = x) ∨ (∃v:value, term.subst_env env.empty x = v), from (
      have (term.subst_env env.empty x = x), by unfold term.subst_env,
      show (term.subst_env env.empty x = x) ∨ (∃v:value, term.subst_env env.empty x = v), from or.inl this
    ),
    show (term.subst_env (σ'[y↦v']) x = x) ∨ (∃v:value, term.subst_env (σ'[y↦v']) x = v), from (
      have tsubst: (term.subst_env (σ'[y↦v']) x = term.subst y v' (term.subst_env σ' x)),
      by unfold term.subst_env,
      have (term.subst_env σ' ↑x = ↑x ∨ ∃ (v : value), term.subst_env σ' ↑x = ↑v), from ih,
      or.elim this (
        assume σ'_x_is_x: term.subst_env σ' ↑x = ↑x,
        have h: (term.subst_env (σ'[y↦v']) x = term.subst y v' ↑x),
        from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) x σ'_x_is_x tsubst,
        have h2: term.subst y v' (term.var x) = (if y = x then v' else x), by unfold term.subst,
        decidable.by_cases (
          assume x_is_y: x = y,
          have term.subst y v' (term.var x) = v', by { rw[x_is_y], simp[x_is_y] at h2, from h2 },
          have term.subst_env (σ'[y↦v']) x = v', from eq.trans h this,
          have (∃v:value, term.subst_env (σ'[y↦v']) x = v), from exists.intro v' this,
          show (term.subst_env (σ'[y↦v']) x = x) ∨ (∃v:value, term.subst_env (σ'[y↦v']) x = v), from or.inr this
        ) (
          assume : ¬(x = y),
          have ¬(y = x), from ne.symm this,
          have term.subst y v' (term.var x) = x,  by { simp[this] at h2, from h2 },
          have term.subst_env (σ'[y↦v']) x = x, from eq.trans h this,
          show (term.subst_env (σ'[y↦v']) x = x) ∨ (∃v:value, term.subst_env (σ'[y↦v']) x = v), from or.inl this
        )
      ) (
        assume : ∃ (v : value), term.subst_env σ' ↑x = ↑v,
        let ⟨v, σ'_x_is_v⟩ := this in
        have h: (term.subst_env (σ'[y↦v']) x = term.subst y v' ↑v),
        from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) v σ'_x_is_v tsubst,
        have term.subst y v' (term.value v) = ↑v, by unfold term.subst,
        have term.subst_env (σ'[y↦v']) x = v, from eq.trans h this,
        have (∃v:value, term.subst_env (σ'[y↦v']) x = v), from exists.intro v this,
        show (term.subst_env (σ'[y↦v']) x = x) ∨ (∃v:value, term.subst_env (σ'[y↦v']) x = v), from or.inr this
      )
    )
  end

lemma term.subst_env.value {σ: env} {v: value}: term.subst_env σ v = v :=
begin
  induction σ with σ' x v' ih,
  show (term.subst_env env.empty v = v), by unfold term.subst_env,
  show (term.subst_env (σ'[x↦v']) v = v), from (
    have h: term.subst_env σ' v = v, from ih,
    have term.subst_env (σ'[x↦v']) v = term.subst x v' (term.subst_env σ' v), by unfold term.subst_env,
    have h2: term.subst_env (σ'[x↦v']) v = term.subst x v' v,
    from @eq.subst term (λa, term.subst_env (σ'[x↦v']) v = term.subst x v' a) (term.subst_env σ' v) v h this,
    have term.subst x v' (term.value v) = ↑v, by unfold term.subst,
    show term.subst_env (σ'[x↦v']) v = v, from eq.trans h2 this
  )
end

lemma term.subst_env.closed {σ: env} {t: term}: closed t → (term.subst_env σ t = t) :=
begin
  assume t_closed: closed t,
  induction σ with σ' x v' ih,
  show (term.subst_env env.empty t = t), by unfold term.subst_env,
  show (term.subst_env (σ'[x↦v']) t = t), from (
    have h: term.subst_env σ' t = t, from ih,
    have term.subst_env (σ'[x↦v']) t = term.subst x v' (term.subst_env σ' t), by unfold term.subst_env,
    have h2: term.subst_env (σ'[x↦v']) t = term.subst x v' t,
    from @eq.subst term (λa, term.subst_env (σ'[x↦v']) t = term.subst x v' a) (term.subst_env σ' t) t h this,
    have term.subst x v' t = t, from unchanged_of_subst_nonfree_term (t_closed x),
    show term.subst_env (σ'[x↦v']) t = t, from eq.trans h2 this
  )
end

lemma term.subst_env.var {σ: env} {x: var}:
      ((σ x = none) ↔ (term.subst_env σ x = x)) ∧ (∀v, (σ x = some v) ↔ (term.subst_env σ x = v)) :=
begin
  induction σ with σ' y v' ih,
  show (((env.empty x = none) ↔ (term.subst_env env.empty x = x))
     ∧ (∀v, (env.empty x = some v) ↔ (term.subst_env env.empty x = v))), by begin
    split,
    show ((env.empty x = none) ↔ (term.subst_env env.empty x = x)), by begin
      split,
      show ((env.empty x = none) → (term.subst_env env.empty x = x)), by begin
        assume _,
        show (term.subst_env env.empty x = x), by unfold term.subst_env
      end,
      show ((term.subst_env env.empty x = x) → (env.empty x = none)), by begin
        assume _,
        show (env.apply env.empty x = none), by unfold env.apply
      end
    end,
    show ∀v, ((env.empty x = some v) ↔ (term.subst_env env.empty x = v)), by begin
      assume v,
      split,
      show ((env.empty x = some v) → (term.subst_env env.empty x = v)), by begin
        assume env_has_some: (env.apply (env.empty) x = some v),
        have env_has_none: (env.apply env.empty x = none), by unfold env.apply,
        have : (some v = none), from env_has_some ▸ env_has_none,
        contradiction 
      end,
      show ((term.subst_env env.empty x = v) → (env.empty x = some v)), by begin
        assume subst_is_v: (term.subst_env env.empty x = v),
        have : (term.subst_env env.empty x = x), by unfold term.subst_env,
        have : (↑v = ↑x), from eq.trans subst_is_v.symm this,
        contradiction 
      end
    end
  end,
  show ((((σ'[y↦v']) x = none) ↔ (term.subst_env (σ'[y↦v']) x = x))
     ∧ (∀v, ((σ'[y↦v']) x = some v) ↔ (term.subst_env (σ'[y↦v']) x = v))), by begin
    have tsubst: (term.subst_env (σ'[y↦v']) x = term.subst y v' (term.subst_env σ' x)),
    by unfold term.subst_env,
    have app: ((σ'[y↦v']).apply x = (if y = x ∧ option.is_none (σ'.apply x) then v' else σ'.apply x)),
    by unfold env.apply,
    split,
    show (((σ'[y↦v']) x = none) ↔ (term.subst_env (σ'[y↦v']) x = x)), by begin
      split,
      show (((σ'[y↦v']) x = none) → (term.subst_env (σ'[y↦v']) x = x)), by begin
        assume σ'_does_not_have_x: ((σ'[y↦v']) x = none),
        by_cases (y = x ∧ option.is_none (σ'.apply x)) with h,
        show (term.subst_env (σ'[y↦v']) x = x), from
          have ((σ'[y↦v']).apply x) = v', by { simp[h] at app, rw[h.left], from app },
          have some v' = none, from eq.trans this.symm σ'_does_not_have_x,
          by contradiction,
        show (term.subst_env (σ'[y↦v']) x = x), from
          have ((σ'[y↦v']).apply x) = σ'.apply x, by { simp[h] at app, from app },
          have σ'_x_is_none: σ'.apply x = none, from eq.trans this.symm σ'_does_not_have_x,
          have term.subst_env σ' x = x, from ih.left.mp σ'_x_is_none,
          have h2: term.subst_env (σ'[y↦v']) x = term.subst y v' x,
          from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) x this tsubst,
          have h3: term.subst y v' (term.var x) = (if y = x then v' else x), by unfold term.subst,
          have ¬(y = x) ∨ ¬(option.is_none (env.apply σ' x)) , from not_and_distrib.mp h,
          have ¬(y = x), from this.elim id ( 
            assume : ¬(option.is_none (env.apply σ' x)),
            have (env.apply σ' x) ≠ none, from option.is_none.ninv.mpr this,
            show ¬(y = x), from absurd σ'_x_is_none this
          ),
          have term.subst y v' (term.var x) = x, by { simp[this] at h3, from h3 },
          show (term.subst_env (σ'[y↦v']) x = x), from eq.trans h2 this
      end,
      show ((term.subst_env (σ'[y↦v']) x = x) → ((σ'[y↦v']) x = none)), from (
        assume h: term.subst_env (σ'[y↦v']) x = x,
        have h2: term.subst y v' (term.subst_env σ' x) = x, from eq.trans tsubst.symm h,
        have (term.subst_env σ' x = x) ∨ (∃v:value, term.subst_env σ' x = v), from term.subst_env.var.inv,
        or.elim this (
          assume : term.subst_env σ' x = x,
          have σ'_x_is_none: σ' x = none, from ih.left.mpr this,
          have h3: term.subst_env (σ'[y↦v']) x = term.subst y v' x,
          from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) x this tsubst,
          have h4: term.subst y v' (term.var x) = (if y = x then v' else x), by unfold term.subst,
          decidable.by_cases (
            assume : x = y,
            have y_eq_x: y = x, from eq.symm this,
            have term.subst y v' (term.var x) = v', by { simp[y_eq_x] at h4, rw[y_eq_x], from h4 },
            have term.subst_env (σ'[y↦v']) x = v', from eq.trans h3 this,
            have ↑x = ↑v', from eq.trans h.symm this,
            show (σ'[y↦v']) x = none, by contradiction
          ) (
            assume : ¬(x = y),
            have y_neq_x: ¬(y = x), from ne.symm this,
            have (σ'[y↦v']).apply x = σ'.apply x, by { simp[y_neq_x] at app, from app },
            show (σ'[y↦v']).apply x = none, from eq.trans this σ'_x_is_none
          )
        ) (
          assume : (∃v'':value, term.subst_env σ' x = v''),
          let ⟨v'', σ'_x_is_v''⟩ := this in
          have h3: (term.subst_env (σ'[y↦v']) x = term.subst y v' ↑v''),
          from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) v'' σ'_x_is_v'' tsubst,
          have term.subst y v' (term.value v'') = ↑v'', by unfold term.subst,
          have term.subst_env (σ'[y↦v']) x = ↑v'', from eq.trans h3 this,
          have ↑x = ↑v'', from eq.trans h.symm this,
          show (σ'[y↦v']) x = none, by contradiction
        )
      )
    end,
    show (∀v, ((σ'[y↦v']) x = some v) ↔ (term.subst_env (σ'[y↦v']) x = v)), by begin
      assume v,
      split,
      show (((σ'[y↦v']) x = some v) → (term.subst_env (σ'[y↦v']) x = v)), by begin
        assume env_has_x: ((σ'[y↦v']) x = some v),
        have app: ((σ'[y↦v']).apply x = (if y = x ∧ option.is_none (σ'.apply x) then v' else σ'.apply x)),
        by unfold env.apply,
        by_cases (y = x ∧ option.is_none (σ'.apply x)) with h,
        show (term.subst_env (σ'[y↦v']) ↑x = ↑v), from (
          have ((σ'[y↦v']).apply x = v'), by { simp[h] at app, rw[h.left], from app },
          have some v' = some v, from eq.trans this.symm env_has_x,
          have v'_is_v: v' = v, by injection this,
          have option.is_none (σ'.apply x), from h.right,
          have σ'.apply x = none, from option.is_none.inv.mpr this,
          have σ'_x_is_x: term.subst_env σ' x = x, from ih.left.mp this,
          have term.subst_env (σ'[y↦v']) x = term.subst y v' (term.subst_env σ' x),
          by unfold term.subst_env,
          have h2: term.subst_env (σ'[y↦v']) x = term.subst y v' (term.var x),
          from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) x σ'_x_is_x tsubst,
          have h3: term.subst y v' (term.var x) = (if y = x then v' else x), by unfold term.subst,
          have term.subst y v' (term.var x) = v', by { simp[h.left] at h3, rw[h.left], from h3 },
          show term.subst_env (σ'[y↦v']) x = v, from v'_is_v ▸ eq.trans h2 this
        ),
        show (term.subst_env (σ'[y↦v']) ↑x = ↑v), from (
          have (σ'[y↦v']).apply x = σ'.apply x, by { simp [h] at app, from app },
          have σ'.apply x = v, from eq.trans this.symm env_has_x,
          have σ'_x_is_v: term.subst_env σ' ↑x = ↑v, from (ih.right v).mp this,
          have term.subst_env (σ'[y↦v']) x = term.subst y v' (term.subst_env σ' x),
          by unfold term.subst_env,
          have h2: term.subst_env (σ'[y↦v']) x = term.subst y v' v,
          from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) v σ'_x_is_v tsubst,
          have term.subst y v' (term.value v) = ↑v, by unfold term.subst,
          show term.subst_env (σ'[y↦v']) x = v, from eq.trans h2 this
        )
      end,
      show ((term.subst_env (σ'[y↦v']) x = v) → ((σ'[y↦v']) x = some v)), from (
        assume h: term.subst_env (σ'[y↦v']) x = v,
        have h2: term.subst y v' (term.subst_env σ' x) = v, from eq.trans tsubst.symm h,
        have (term.subst_env σ' x = x) ∨ (∃v:value, term.subst_env σ' x = v), from term.subst_env.var.inv,
        or.elim this (
          assume : term.subst_env σ' x = x,
          have σ'_x_is_none: σ' x = none, from ih.left.mpr this,
          have h3: term.subst_env (σ'[y↦v']) x = term.subst y v' x,
          from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) x this tsubst,
          have h4: term.subst y v' (term.var x) = (if y = x then v' else x), by unfold term.subst,
          decidable.by_cases (
            assume x_is_y: x = y,
            have term.subst y v' (term.var x) = (if x = x then v' else x),
            from @eq.subst var (λa, term.subst y v' (term.var x) = (if a = x then v' else x)) y x x_is_y.symm h4,
            have term.subst y v' (term.var x) = v', by { simp at this, from this },
            have term.subst_env (σ'[y↦v']) x = v', from eq.trans h3 this,
            have ↑v = ↑v', from eq.trans h.symm this,
            have v_is_v': v = v', by injection this,
            have opt_is_none: option.is_none (env.apply σ' x), from option.is_none.inv.mp σ'_x_is_none,
            have (if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = v',
            by { simp[x_is_y.symm], simp[opt_is_none] },
            have (σ'[y↦v']).apply x = v', from eq.trans app this,
            have (σ'[y↦v']) x = some v', from this,
            show (σ'[y↦v']) x = some v, from @eq.subst value (λa, (σ'[y↦v']) x = some a) v' v v_is_v'.symm this
          ) (
            assume : ¬(x = y),
            have ¬(y = x), from ne.symm this,
            have term.subst y v' (term.var x) = x, by { simp[this] at h4, from h4 },
            have ↑v = ↑x, from eq.trans (eq.trans h.symm h3) this,
            show ((σ'[y↦v']) x = some v), by contradiction
          )
        ) (
          assume : (∃v'':value, term.subst_env σ' x = v''),
          let ⟨v'', σ'_x_is_v''⟩ := this in
          have h3: (term.subst_env (σ'[y↦v']) x = term.subst y v' ↑v''),
          from @eq.subst term (λa, term.subst_env (σ'[y↦v']) x = term.subst y v' a) (term.subst_env σ' x) v'' σ'_x_is_v'' tsubst,
          have term.subst y v' (term.value v'') = ↑v'', by unfold term.subst,
          have term.subst_env (σ'[y↦v']) x = ↑v'', from eq.trans h3 this,
          have v_is_v'': ↑v = ↑v'', from eq.trans h.symm this,
          have term.subst_env σ' x = v,
          from @eq.subst term (λa, term.subst_env σ' x = a) v'' v v_is_v''.symm σ'_x_is_v'',
          have σ'_x_app_is_v: env.apply σ' x = some v, from (ih.right v).mpr this,
          have opt_is_not_none: ¬ option.is_none (env.apply σ' x),
          from option.some_iff_not_none.mp (option.is_some_iff_exists.mpr (exists.intro v σ'_x_app_is_v)),
          have (if y = x ∧ option.is_none (σ'.apply x) then ↑v' else σ'.apply x) = σ'.apply x,
          by { simp[opt_is_not_none] },
          have (σ'[y↦v']) x = σ'.apply x, from eq.trans app this,
          show (σ'[y↦v']) x = some v, from eq.trans this σ'_x_app_is_v
        )
      )
    end
  end
end

lemma term.not_free_of_subst {x: var} {v: value} {t: term}: x ∉ FV (term.subst x v t) :=
  assume x_free: x ∈ FV (term.subst x v t),
  begin
    induction t with a,

    show «false», by begin -- term.value
      unfold term.subst at x_free,
      cases x_free
    end,

    show «false», by begin -- term.var
      unfold term.subst at x_free,
      by_cases (x = a) with h,
      simp[h] at x_free,
      cases x_free,
      simp[h] at x_free,
      cases x_free,
      contradiction
    end,

    show «false», by begin -- term.unop
      unfold term.subst at x_free,
      have h, from free_in_term.unop.inv x_free,
      contradiction
    end,

    show «false», by begin -- term.binop
      unfold term.subst at x_free,
      have h, from free_in_term.binop.inv x_free,
      cases h with h1 h2,
      contradiction,
      contradiction
    end,

    show «false», by begin -- term.app
      unfold term.subst at x_free,
      have h, from free_in_term.app.inv x_free,
      cases h with h1 h2,
      contradiction,
      contradiction
    end
  end

lemma term.not_free_of_substt {x: var} {t₁ t₂: term}: closed t₁ → x ∉ FV (term.substt x t₁ t₂) :=
  assume t_closed: closed t₁,
  assume x_free: x ∈ FV (term.substt x t₁ t₂),
  begin
    induction t₂ with a,

    show «false», by begin -- term.value
      unfold term.substt at x_free,
      cases x_free
    end,

    show «false», by begin -- term.var
      unfold term.substt at x_free,
      by_cases (x = a) with h,
      simp[h] at x_free,
      have : a ∉ FV t₁, from t_closed a,
      contradiction,
      simp[h] at x_free,
      cases x_free,
      contradiction
    end,

    show «false», by begin -- term.unop
      unfold term.substt at x_free,
      have h, from free_in_term.unop.inv x_free,
      contradiction
    end,

    show «false», by begin -- term.binop
      unfold term.substt at x_free,
      have h, from free_in_term.binop.inv x_free,
      cases h with h1 h2,
      contradiction,
      contradiction
    end,

    show «false», by begin -- term.app
      unfold term.substt at x_free,
      have h, from free_in_term.app.inv x_free,
      cases h with h1 h2,
      contradiction,
      contradiction
    end
  end

lemma term.not_free_of_subst_env {x: var} {σ: env} {t: term}: x ∈ σ → x ∉ FV (term.subst_env σ t) :=
  assume x_in_σ: x ∈ σ,
  assume x_free: x ∈ FV (term.subst_env σ t),
  begin
    induction σ with σ' y v ih,

    -- env.empty
    show «false», by cases x_in_σ,

    -- σ'[x↦v]
    show «false», from (
      have term.subst_env (σ'[y↦v]) t = term.subst y v (term.subst_env σ' t), by unfold term.subst_env,
      have x ∈ FV (term.subst y v (term.subst_env σ' t)), from this ▸ x_free,
      have x_neq_y: x ≠ y, from (free_of_subst_term this).left,
      have h: x ∈ FV (term.subst_env σ' t), from (free_of_subst_term this).right,
      have x = y ∨ x ∈ σ', from env.contains.inv x_in_σ,
      or.elim this (
        assume : x = y,
        show «false», from x_neq_y this
      ) (
        assume : x ∈ σ',
        have x ∉ FV (term.subst_env σ' t), from ih this,
        show «false», from this h
      )
    )
  end

lemma prop.not_free_of_subst {x: var} {v: value} {P: prop}: x ∉ FV (prop.subst x v P) :=
  assume x_free: x ∈ FV (prop.subst x v P),
  begin
    induction P,
    case prop.term t { from (
      have prop.subst x v (prop.term t) = (term.subst x v t), by unfold prop.subst,
      have free_in_prop x (prop.term (term.subst x v t)), from this ▸ x_free,
      have x ∈ FV (term.subst x v t), from free_in_prop.term.inv this,
      show «false», from term.not_free_of_subst this
    )},
    case prop.not P₁ P₁_ih { from (
      have prop.subst x v (prop.not P₁) = (P₁.subst x v).not, by unfold prop.subst,
      have x ∈ FV (P₁.subst x v).not, from this ▸ x_free,
      have x ∈ FV (P₁.subst x v), from free_in_prop.not.inv this,
      show «false», from P₁_ih this
    )},
    case prop.and P₁ P₂ P₁_ih P₂_ih { from (
      have prop.subst x v (prop.and P₁ P₂) = (P₁.subst x v ⋀ P₂.subst x v), by unfold prop.subst,
      have x ∈ FV (P₁.subst x v ⋀ P₂.subst x v), from this ▸ x_free,
      or.elim (free_in_prop.and.inv this) (
        assume : x ∈ FV (P₁.subst x v),
        show «false», from P₁_ih this
      ) (
        assume : x ∈ FV (P₂.subst x v),
        show «false», from P₂_ih this
      )
    )},
    case prop.or P₁ P₂ P₁_ih P₂_ih { from (
      have prop.subst x v (prop.or P₁ P₂) = (P₁.subst x v ⋁ P₂.subst x v), by unfold prop.subst,
      have x ∈ FV (P₁.subst x v ⋁ P₂.subst x v), from this ▸ x_free,
      or.elim (free_in_prop.or.inv this) (
        assume : x ∈ FV (P₁.subst x v),
        show «false», from P₁_ih this
      ) (
        assume : x ∈ FV (P₂.subst x v),
        show «false», from P₂_ih this
      )
    )},
    case prop.pre t₁ t₂ { from (
      have prop.subst x v (prop.pre t₁ t₂) = prop.pre (t₁.subst x v) (t₂.subst x v), by unfold prop.subst,
      have x ∈ FV (prop.pre (t₁.subst x v) (t₂.subst x v)), from this ▸ x_free,
      or.elim (free_in_prop.pre.inv this) (
        assume : x ∈ FV (t₁.subst x v),
        show «false», from term.not_free_of_subst this
      ) (
        assume : x ∈ FV (t₂.subst x v),
        show «false», from term.not_free_of_subst this
      )
    )},
    case prop.pre₁ op t { from (
      have prop.subst x v (prop.pre₁ op t) = prop.pre₁ op (t.subst x v), by unfold prop.subst,
      have x ∈ FV (prop.pre₁ op (t.subst x v)), from this ▸ x_free,
      have x ∈ FV (t.subst x v), from free_in_prop.pre₁.inv this,
      show «false», from term.not_free_of_subst this
    )},
    case prop.pre₂ op t₁ t₂ { from (
      have prop.subst x v (prop.pre₂ op t₁ t₂) = prop.pre₂ op (t₁.subst x v) (t₂.subst x v),
      by unfold prop.subst,
      have x ∈ FV (prop.pre₂ op (t₁.subst x v) (t₂.subst x v)), from this ▸ x_free,
      or.elim (free_in_prop.pre₂.inv this) (
        assume : x ∈ FV (t₁.subst x v),
        show «false», from term.not_free_of_subst this
      ) (
        assume : x ∈ FV (t₂.subst x v),
        show «false», from term.not_free_of_subst this
      )
    )},
    case prop.post t₁ t₂ { from (
      have prop.subst x v (prop.post t₁ t₂) = prop.post (t₁.subst x v) (t₂.subst x v), by unfold prop.subst,
      have x ∈ FV (prop.post (t₁.subst x v) (t₂.subst x v)), from this ▸ x_free,
      or.elim (free_in_prop.post.inv this) (
        assume : x ∈ FV (t₁.subst x v),
        show «false», from term.not_free_of_subst this
      ) (
        assume : x ∈ FV (t₂.subst x v),
        show «false», from term.not_free_of_subst this
      )
    )},
    case prop.call t { from (
      have prop.subst x v (prop.call t) = prop.call (t.subst x v), by unfold prop.subst,
      have x ∈ FV (prop.call (t.subst x v)), from this ▸ x_free,
      have x ∈ FV (t.subst x v), from free_in_prop.call.inv this,
      show «false», from term.not_free_of_subst this
    )},
    case prop.forallc y P₁ P₁_ih { from (
      have prop.subst x v (prop.forallc y P₁) = prop.forallc y (if x = y then P₁ else P₁.subst x v),
      by unfold prop.subst,
      have x ∈ FV (prop.forallc y (if x = y then P₁ else P₁.subst x v)),
      from this ▸ x_free,
      have y_neq_x: x ≠ y, from (free_in_prop.forallc.inv this).left,
      have x ∈ FV (prop.forallc y (P₁.subst x v)), by { simp[y_neq_x] at this, from this },
      have x ∈ FV (P₁.subst x v), from (free_in_prop.forallc.inv this).right,
      show «false», from P₁_ih this
    )},
    case prop.exis y P₁ P₁_ih { from (
      have prop.subst x v (prop.exis y P₁)
         = prop.exis y (if x = y then P₁ else P₁.subst x v), by unfold prop.subst,
      have x ∈ FV (prop.exis y (if x = y then P₁ else P₁.subst x v)), from this ▸ x_free,
      have y_neq_x: x ≠ y, from (free_in_prop.exis.inv this).left,
      have x ∈ FV (prop.exis y (P₁.subst x v)), by { simp[y_neq_x] at this, from this },
      have x ∈ FV (P₁.subst x v), from (free_in_prop.exis.inv this).right,
      show «false», from P₁_ih this
    )}
  end

lemma prop.not_free_of_subst_env {x: var} {σ: env} {P: prop}: x ∈ σ → x ∉ FV (prop.subst_env σ P) :=
  assume x_in_σ: x ∈ σ,
  assume x_free: x ∈ FV (prop.subst_env σ P),
  begin
    induction σ with σ' y v ih,

    -- env.empty
    show «false», by cases x_in_σ,

    -- σ'[x↦v]
    show «false», from (
      have prop.subst_env (σ'[y↦v]) P = prop.subst y v (prop.subst_env σ' P), by unfold prop.subst_env,
      have x ∈ FV (prop.subst y v (prop.subst_env σ' P)), from this ▸ x_free,
      have x_neq_y: x ≠ y, from (free_of_subst_prop this).left,
      have h: x ∈ FV (prop.subst_env σ' P), from (free_of_subst_prop this).right,
      have x = y ∨ x ∈ σ', from env.contains.inv x_in_σ,
      or.elim this (
        assume : x = y,
        show «false», from x_neq_y this
      ) (
        assume : x ∈ σ',
        have x ∉ FV (prop.subst_env σ' P), from ih this,
        show «false», from this h
      )
    )
  end

lemma term.closed_of_closed_subst {σ: env} {t: term}: closed_subst σ t → closed (term.subst_env σ t) :=
  assume t_closed_subst: closed_subst σ t,
  show closed (term.subst_env σ t), from (
    assume x: var,
    assume h1: x ∈ FV (term.subst_env σ t),
    have x ∈ FV t, from (free_of_subst_env_term h1).left,
    have x ∈ σ.dom, from t_closed_subst this,
    have x ∈ σ, from this,
    have h2: x ∉ FV (term.subst_env σ t), from term.not_free_of_subst_env this,
    show «false», from h2 h1
  )

lemma prop.closed_of_closed_subst {σ: env} {P: prop}: closed_subst σ P → closed (prop.subst_env σ P) :=
  assume P_closed_subst: closed_subst σ P,
  show closed (prop.subst_env σ P), from (
    assume x: var,
    assume h1: x ∈ FV (prop.subst_env σ P),
    have x ∈ FV P, from free_of_subst_env h1,
    have x ∈ σ.dom, from P_closed_subst this,
    have x ∈ σ, from this,
    have h2: x ∉ FV (prop.subst_env σ P), from prop.not_free_of_subst_env this,
    show «false», from h2 h1
  )

lemma vc.not_free_of_subst {x: var} {v: value} {P: vc}: x ∉ FV (vc.subst x v P) :=
  assume x_free: x ∈ FV (vc.subst x v P),
  begin
    induction P,
    case vc.term t { from (
      have vc.subst x v (vc.term t) = (term.subst x v t), by unfold vc.subst,
      have free_in_vc x (vc.term (term.subst x v t)), from this ▸ x_free,
      have x ∈ FV (term.subst x v t), from free_in_vc.term.inv this,
      show «false», from term.not_free_of_subst this
    )},
    case vc.not P₁ P₁_ih { from (
      have vc.subst x v (vc.not P₁) = (P₁.subst x v).not, by unfold vc.subst,
      have x ∈ FV (P₁.subst x v).not, from this ▸ x_free,
      have x ∈ FV (P₁.subst x v), from free_in_vc.not.inv this,
      show «false», from P₁_ih this
    )},
    case vc.and P₁ P₂ P₁_ih P₂_ih { from (
      have vc.subst x v (vc.and P₁ P₂) = (P₁.subst x v ⋀ P₂.subst x v), by unfold vc.subst,
      have x ∈ FV (P₁.subst x v ⋀ P₂.subst x v), from this ▸ x_free,
      or.elim (free_in_vc.and.inv this) (
        assume : x ∈ FV (P₁.subst x v),
        show «false», from P₁_ih this
      ) (
        assume : x ∈ FV (P₂.subst x v),
        show «false», from P₂_ih this
      )
    )},
    case vc.or P₁ P₂ P₁_ih P₂_ih { from (
      have vc.subst x v (vc.or P₁ P₂) = (P₁.subst x v ⋁ P₂.subst x v), by unfold vc.subst,
      have x ∈ FV (P₁.subst x v ⋁ P₂.subst x v), from this ▸ x_free,
      or.elim (free_in_vc.or.inv this) (
        assume : x ∈ FV (P₁.subst x v),
        show «false», from P₁_ih this
      ) (
        assume : x ∈ FV (P₂.subst x v),
        show «false», from P₂_ih this
      )
    )},
    case vc.pre t₁ t₂ { from (
      have vc.subst x v (vc.pre t₁ t₂) = vc.pre (t₁.subst x v) (t₂.subst x v), by unfold vc.subst,
      have x ∈ FV (vc.pre (t₁.subst x v) (t₂.subst x v)), from this ▸ x_free,
      or.elim (free_in_vc.pre.inv this) (
        assume : x ∈ FV (t₁.subst x v),
        show «false», from term.not_free_of_subst this
      ) (
        assume : x ∈ FV (t₂.subst x v),
        show «false», from term.not_free_of_subst this
      )
    )},
    case vc.pre₁ op t { from (
      have vc.subst x v (vc.pre₁ op t) = vc.pre₁ op (t.subst x v), by unfold vc.subst,
      have x ∈ FV (vc.pre₁ op (t.subst x v)), from this ▸ x_free,
      have x ∈ FV (t.subst x v), from free_in_vc.pre₁.inv this,
      show «false», from term.not_free_of_subst this
    )},
    case vc.pre₂ op t₁ t₂ { from (
      have vc.subst x v (vc.pre₂ op t₁ t₂) = vc.pre₂ op (t₁.subst x v) (t₂.subst x v),
      by unfold vc.subst,
      have x ∈ FV (vc.pre₂ op (t₁.subst x v) (t₂.subst x v)), from this ▸ x_free,
      or.elim (free_in_vc.pre₂.inv this) (
        assume : x ∈ FV (t₁.subst x v),
        show «false», from term.not_free_of_subst this
      ) (
        assume : x ∈ FV (t₂.subst x v),
        show «false», from term.not_free_of_subst this
      )
    )},
    case vc.post t₁ t₂ { from (
      have vc.subst x v (vc.post t₁ t₂) = vc.post (t₁.subst x v) (t₂.subst x v), by unfold vc.subst,
      have x ∈ FV (vc.post (t₁.subst x v) (t₂.subst x v)), from this ▸ x_free,
      or.elim (free_in_vc.post.inv this) (
        assume : x ∈ FV (t₁.subst x v),
        show «false», from term.not_free_of_subst this
      ) (
        assume : x ∈ FV (t₂.subst x v),
        show «false», from term.not_free_of_subst this
      )
    )},
    case vc.univ y P₁ P₁_ih { from (
      have vc.subst x v (vc.univ y P₁)
         = vc.univ y (if x = y then P₁ else P₁.subst x v), by unfold vc.subst,
      have x ∈ FV (vc.univ y (if x = y then P₁ else P₁.subst x v)), from this ▸ x_free,
      have y_neq_x: x ≠ y, from (free_in_vc.univ.inv this).left,
      have x ∈ FV (vc.univ y (P₁.subst x v)), by { simp[y_neq_x] at this, from this },
      have x ∈ FV (P₁.subst x v), from (free_in_vc.univ.inv this).right,
      show «false», from P₁_ih this
    )}
  end

lemma vc.not_free_of_substt {x: var} {t: term} {P: vc}: closed t → x ∉ FV (vc.substt x t P) :=
  assume t_closed: closed t,
  assume x_free: x ∈ FV (vc.substt x t P),
  begin
    induction P,
    case vc.term t₂ { from (
      have vc.substt x t (vc.term t₂) = (term.substt x t t₂), by unfold vc.substt,
      have free_in_vc x (vc.term (term.substt x t t₂)), from this ▸ x_free,
      have x ∈ FV (term.substt x t t₂), from free_in_vc.term.inv this,
      show «false», from term.not_free_of_substt t_closed this
    )},
    case vc.not P₁ P₁_ih { from (
      have vc.substt x t (vc.not P₁) = (P₁.substt x t).not, by unfold vc.substt,
      have x ∈ FV (P₁.substt x t).not, from this ▸ x_free,
      have x ∈ FV (P₁.substt x t), from free_in_vc.not.inv this,
      show «false», from P₁_ih this
    )},
    case vc.and P₁ P₂ P₁_ih P₂_ih { from (
      have vc.substt x t (vc.and P₁ P₂) = (P₁.substt x t ⋀ P₂.substt x t), by unfold vc.substt,
      have x ∈ FV (P₁.substt x t ⋀ P₂.substt x t), from this ▸ x_free,
      or.elim (free_in_vc.and.inv this) (
        assume : x ∈ FV (P₁.substt x t),
        show «false», from P₁_ih this
      ) (
        assume : x ∈ FV (P₂.substt x t),
        show «false», from P₂_ih this
      )
    )},
    case vc.or P₁ P₂ P₁_ih P₂_ih { from (
      have vc.substt x t (vc.or P₁ P₂) = (P₁.substt x t ⋁ P₂.substt x t), by unfold vc.substt,
      have x ∈ FV (P₁.substt x t ⋁ P₂.substt x t), from this ▸ x_free,
      or.elim (free_in_vc.or.inv this) (
        assume : x ∈ FV (P₁.substt x t),
        show «false», from P₁_ih this
      ) (
        assume : x ∈ FV (P₂.substt x t),
        show «false», from P₂_ih this
      )
    )},
    case vc.pre t₁ t₂ { from (
      have vc.substt x t (vc.pre t₁ t₂) = vc.pre (term.substt x t t₁) (term.substt x t t₂), by unfold vc.substt,
      have x ∈ FV (vc.pre (term.substt x t t₁) (term.substt x t t₂)), from this ▸ x_free,
      or.elim (free_in_vc.pre.inv this) (
        assume : x ∈ FV (term.substt x t t₁),
        show «false», from term.not_free_of_substt t_closed this
      ) (
        assume : x ∈ FV (term.substt x t t₂),
        show «false», from term.not_free_of_substt t_closed this
      )
    )},
    case vc.pre₁ op t₁ { from (
      have vc.substt x t (vc.pre₁ op t₁) = vc.pre₁ op (term.substt x t t₁), by unfold vc.substt,
      have x ∈ FV (vc.pre₁ op (term.substt x t t₁)), from this ▸ x_free,
      have x ∈ FV (term.substt x t t₁), from free_in_vc.pre₁.inv this,
      show «false», from term.not_free_of_substt t_closed this
    )},
    case vc.pre₂ op t₁ t₂ { from (
      have vc.substt x t (vc.pre₂ op t₁ t₂) = vc.pre₂ op (term.substt x t t₁) (term.substt x t t₂),
      by unfold vc.substt,
      have x ∈ FV (vc.pre₂ op (term.substt x t t₁) (term.substt x t t₂)), from this ▸ x_free,
      or.elim (free_in_vc.pre₂.inv this) (
        assume : x ∈ FV (term.substt x t t₁),
        show «false», from term.not_free_of_substt t_closed this
      ) (
        assume : x ∈ FV (term.substt x t t₂),
        show «false», from term.not_free_of_substt t_closed this
      )
    )},
    case vc.post t₁ t₂ { from (
      have vc.substt x t (vc.post t₁ t₂) = vc.post (term.substt x t t₁) (term.substt x t t₂),
      by unfold vc.substt,
      have x ∈ FV (vc.post (term.substt x t t₁) (term.substt x t t₂)), from this ▸ x_free,
      or.elim (free_in_vc.post.inv this) (
        assume : x ∈ FV (term.substt x t t₁),
        show «false», from term.not_free_of_substt t_closed this
      ) (
        assume : x ∈ FV (term.substt x t t₂),
        show «false», from term.not_free_of_substt t_closed this
      )
    )},
    case vc.univ y P₁ P₁_ih { from (
      have vc.substt x t (vc.univ y P₁)
         = vc.univ y (if x = y then P₁ else P₁.substt x t), by unfold vc.substt,
      have x ∈ FV (vc.univ y (if x = y then P₁ else P₁.substt x t)), from this ▸ x_free,
      have y_neq_x: x ≠ y, from (free_in_vc.univ.inv this).left,
      have x ∈ FV (vc.univ y (P₁.substt x t)), by { simp[y_neq_x] at this, from this },
      have x ∈ FV (P₁.substt x t), from (free_in_vc.univ.inv this).right,
      show «false», from P₁_ih this
    )}
  end

-- lemma term.not_free_of_substte {x: var} {t₁ t₂: term} {σ: env}:
--       closed_subst σ t₁ → x ∉ FV (term.substt x (term.subst_env σ t₁) t₂) :=
--   begin
--     assume t_closed: closed_subst σ t₁,
--     assume x_free: x ∈ FV (term.substt x (term.subst_env σ t₁) t₂),
--     have h1: closed (term.subst_env σ t₁), from term.closed_of_closed_subst t_closed,
--     have h2: x ∉ FV (term.substt x (term.subst_env σ t₁) t₂), from term.not_free_of_substt h1,
--     show «false», from h2 x_free
--   end

lemma term.not_free_of_substte {x: var} {t₁ t₂: term} {σ₁ σ₂: env}:
      closed_subst σ₁ t₁ → x ∉ FV (term.substt x (term.subst_env σ₂ t₁) t₂) - (σ₁.dom - σ₂.dom) :=
  begin
    assume t_closed: closed_subst σ₁ t₁,
    assume x_free: x ∈ FV (term.substt x (term.subst_env σ₂ t₁) t₂) - (σ₁.dom - σ₂.dom),
    have h1, from set.mem_of_mem_diff x_free,
    have h2: x ∈ FV (term.subst_env σ₂ t₁), from free_of_substt_same_term h1,
    have h3: x ∈ FV t₁ ∧ x ∉ σ₂, from free_of_subst_env_term h2,
    have h4: x ∈ σ₁, from t_closed h3.left,
    have h5: x ∉ σ₂, from h3.right,
    have h6, from set.not_mem_of_mem_diff x_free,
    have h7, from set.not_mem_or_mem_of_not_mem_diff h6,
    cases h7,
    contradiction,
    contradiction
  end

lemma vc.not_free_of_substte_step {σ₁: env} {x: var} {t: term} {P: vc}:
      closed_subst σ₁ t → ∀σ₂, x ∉ FV (vc.substte x t P σ₂) - (σ₁.dom - σ₂.dom) :=
  begin
    assume t_closed: closed_subst σ₁ t,
    induction P,
    case vc.term t₂ {
      assume σ₂,
      assume x_free: x ∈ FV (vc.substte x t (vc.term t₂) σ₂) - (σ₁.dom - σ₂.dom),
      have h1, from set.mem_of_mem_diff x_free,
      have h2, from set.not_mem_of_mem_diff x_free,
      have : (vc.substte x t (vc.term t₂) σ₂ = (term.substt x (term.subst_env σ₂ t) t₂)), by unfold vc.substte,
      have : free_in_vc x (vc.term (term.substt x (term.subst_env σ₂ t) t₂)), from this ▸ h1,
      have h3: x ∈ FV (term.substt x (term.subst_env σ₂ t) t₂), from free_in_vc.term.inv this,
      have : x ∈ FV (term.substt x (term.subst_env σ₂ t) t₂) - (σ₁.dom - σ₂.dom), from set.mem_diff h3 h2, 
      from term.not_free_of_substte t_closed this
    },
    case vc.not P₁ P₁_ih {
      assume σ₂,
      assume x_free: x ∈ FV (vc.substte x t P₁.not σ₂) - (σ₁.dom - σ₂.dom),
      have h1, from set.mem_of_mem_diff x_free,
      have : (vc.substte x t (vc.not P₁) σ₂ = (P₁.substte x t σ₂).not), by unfold vc.substte,
      have : x ∈ FV (P₁.substte x t σ₂).not, from this ▸ h1,
      have h2: x ∈ FV (P₁.substte x t σ₂), from free_in_vc.not.inv this,
      have h3, from set.not_mem_of_mem_diff x_free,
      have : x ∈ FV (vc.substte x t P₁ σ₂) - (env.dom σ₁ - env.dom σ₂), from set.mem_diff h2 h3,
      from P₁_ih σ₂ this
    },
    case vc.and P₁ P₂ P₁_ih P₂_ih {
      assume σ₂,
      assume x_free: x ∈ FV (vc.substte x t (P₁ ⋀ P₂) σ₂) - (σ₁.dom - σ₂.dom),
      have h1, from set.mem_of_mem_diff x_free,
      have h2, from set.not_mem_of_mem_diff x_free,
      have : (vc.substte x t (vc.and P₁ P₂) σ₂ = (P₁.substte x t σ₂ ⋀ P₂.substte x t σ₂)), by unfold vc.substte,
      have : x ∈ FV (P₁.substte x t σ₂ ⋀ P₂.substte x t σ₂), from this ▸ h1,
      from or.elim (free_in_vc.and.inv this) (
        assume : x ∈ FV (P₁.substte x t σ₂),
        have x ∈ FV (vc.substte x t P₁ σ₂) - (env.dom σ₁ - env.dom σ₂), from set.mem_diff this h2,
        show «false», from P₁_ih σ₂ this
      ) (
        assume : x ∈ FV (P₂.substte x t σ₂),
        have x ∈ FV (vc.substte x t P₂ σ₂) - (env.dom σ₁ - env.dom σ₂), from set.mem_diff this h2,
        show «false», from P₂_ih σ₂ this
      )
    },
    case vc.or P₁ P₂ P₁_ih P₂_ih {
      assume σ₂,
      assume x_free: x ∈ FV (vc.substte x t (P₁ ⋁ P₂) σ₂) - (σ₁.dom - σ₂.dom),
      have h1, from set.mem_of_mem_diff x_free,
      have h2, from set.not_mem_of_mem_diff x_free,
      have : (vc.substte x t (vc.or P₁ P₂) σ₂ = (P₁.substte x t σ₂ ⋁ P₂.substte x t σ₂)), by unfold vc.substte,
      have : x ∈ FV (P₁.substte x t σ₂ ⋁ P₂.substte x t σ₂), from this ▸ h1,
      from or.elim (free_in_vc.or.inv this) (
        assume : x ∈ FV (P₁.substte x t σ₂),
        have x ∈ FV (vc.substte x t P₁ σ₂) - (env.dom σ₁ - env.dom σ₂), from set.mem_diff this h2,
        show «false», from P₁_ih σ₂ this
      ) (
        assume : x ∈ FV (P₂.substte x t σ₂),
        have x ∈ FV (vc.substte x t P₂ σ₂) - (env.dom σ₁ - env.dom σ₂), from set.mem_diff this h2,
        show «false», from P₂_ih σ₂ this
      )
    },
    case vc.pre t₁ t₂ {
      assume σ₂,
      assume x_free: x ∈ FV (vc.substte x t (vc.pre t₁ t₂) σ₂) - (σ₁.dom - σ₂.dom),
      have h1, from set.mem_of_mem_diff x_free,
      have h2, from set.not_mem_of_mem_diff x_free,
      have : (vc.substte x t (vc.pre t₁ t₂) σ₂
            = vc.pre (term.substt x (term.subst_env σ₂ t) t₁) (term.substt x (term.subst_env σ₂ t) t₂)),
      by unfold vc.substte,
      have : x ∈ FV (vc.pre (term.substt x (term.subst_env σ₂ t) t₁) (term.substt x (term.subst_env σ₂ t) t₂)),
      from this ▸ h1,
      from or.elim (free_in_vc.pre.inv this) (
        assume : x ∈ FV (term.substt x (term.subst_env σ₂ t) t₁),
        have x ∈ FV (term.substt x (term.subst_env σ₂ t) t₁) - (σ₁.dom - σ₂.dom), from set.mem_diff this h2, 
        term.not_free_of_substte t_closed this
      ) (
        assume : x ∈ FV (term.substt x (term.subst_env σ₂ t) t₂),
        have x ∈ FV (term.substt x (term.subst_env σ₂ t) t₂) - (σ₁.dom - σ₂.dom), from set.mem_diff this h2, 
        term.not_free_of_substte t_closed this
      )
    },
    case vc.pre₁ op t₁ {
      assume σ₂,
      assume x_free: x ∈ FV (vc.substte x t (vc.pre₁ op t₁) σ₂) - (σ₁.dom - σ₂.dom),
      have h1, from set.mem_of_mem_diff x_free,
      have h2, from set.not_mem_of_mem_diff x_free,
      have : (vc.substte x t (vc.pre₁ op t₁) σ₂ = vc.pre₁ op (term.substt x (term.subst_env σ₂ t) t₁)),
      by unfold vc.substte,
      have : x ∈ FV (vc.pre₁ op (term.substt x (term.subst_env σ₂ t) t₁)), from this ▸ h1,
      have : x ∈ FV (term.substt x (term.subst_env σ₂ t) t₁), from free_in_vc.pre₁.inv this,
      have : x ∈ FV (term.substt x (term.subst_env σ₂ t) t₁) - (σ₁.dom - σ₂.dom), from set.mem_diff this h2, 
      from term.not_free_of_substte t_closed this
    },
    case vc.pre₂ op t₁ t₂ {
      assume σ₂,
      assume x_free: x ∈ FV (vc.substte x t (vc.pre₂ op t₁ t₂) σ₂) - (σ₁.dom - σ₂.dom),
      have h1, from set.mem_of_mem_diff x_free,
      have h2, from set.not_mem_of_mem_diff x_free,
      have : (vc.substte x t (vc.pre₂ op t₁ t₂) σ₂
            = vc.pre₂ op (term.substt x (term.subst_env σ₂ t) t₁) (term.substt x (term.subst_env σ₂ t) t₂)),
      by unfold vc.substte,
      have : x ∈ FV (vc.pre₂ op (term.substt x (term.subst_env σ₂ t) t₁) (term.substt x (term.subst_env σ₂ t) t₂)),
      from this ▸ h1,
      from or.elim (free_in_vc.pre₂.inv this) (
        assume : x ∈ FV (term.substt x (term.subst_env σ₂ t) t₁),
        have x ∈ FV (term.substt x (term.subst_env σ₂ t) t₁) - (σ₁.dom - σ₂.dom), from set.mem_diff this h2, 
        term.not_free_of_substte t_closed this
      ) (
        assume : x ∈ FV (term.substt x (term.subst_env σ₂ t) t₂),
        have x ∈ FV (term.substt x (term.subst_env σ₂ t) t₂) - (σ₁.dom - σ₂.dom), from set.mem_diff this h2, 
        term.not_free_of_substte t_closed this
      )
    },
    case vc.post t₁ t₂ {
      assume σ₂,
      assume x_free: x ∈ FV (vc.substte x t (vc.post t₁ t₂) σ₂) - (σ₁.dom - σ₂.dom),
      have h1, from set.mem_of_mem_diff x_free,
      have h2, from set.not_mem_of_mem_diff x_free,
      have : (vc.substte x t (vc.post t₁ t₂) σ₂
            = vc.post (term.substt x (term.subst_env σ₂ t) t₁) (term.substt x (term.subst_env σ₂ t) t₂)),
      by unfold vc.substte,
      have : x ∈ FV (vc.post (term.substt x (term.subst_env σ₂ t) t₁) (term.substt x (term.subst_env σ₂ t) t₂)),
      from this ▸ h1,
      from or.elim (free_in_vc.post.inv this) (
        assume : x ∈ FV (term.substt x (term.subst_env σ₂ t) t₁),
        have x ∈ FV (term.substt x (term.subst_env σ₂ t) t₁) - (σ₁.dom - σ₂.dom), from set.mem_diff this h2, 
        term.not_free_of_substte t_closed this
      ) (
        assume : x ∈ FV (term.substt x (term.subst_env σ₂ t) t₂),
        have x ∈ FV (term.substt x (term.subst_env σ₂ t) t₂) - (σ₁.dom - σ₂.dom), from set.mem_diff this h2, 
        term.not_free_of_substte t_closed this
      )
    },
    case vc.univ y P₁ P₁_ih {
      assume σ₂,
      assume x_free: x ∈ FV (vc.substte x t (vc.univ y P₁) σ₂) - (σ₁.dom - σ₂.dom),
      have h1, from set.mem_of_mem_diff x_free,
      have h2, from set.not_mem_of_mem_diff x_free,
      have : (vc.substte x t (vc.univ y P₁) σ₂ = vc.univ y (if x = y then P₁ else P₁.substte x t (σ₂.without y))),
      by unfold vc.substte,
      have : x ∈ FV (vc.univ y (if x = y then P₁ else P₁.substte x t (σ₂.without y))), from this ▸ h1,
      have y_neq_x: x ≠ y, from (free_in_vc.univ.inv this).left,
      have : x ∈ FV (vc.univ y (P₁.substte x t (σ₂.without y))), by { simp[y_neq_x] at this, from this },
      have h3: x ∈ FV (P₁.substte x t (σ₂.without y)), from (free_in_vc.univ.inv this).right,
      have h4: x ∉ σ₁.dom - (σ₂.without y).dom, by begin
        assume h5: x ∈ env.dom σ₁ - env.dom (env.without σ₂ y),
        have h6, from set.mem_of_mem_diff h5,
        have h7, from set.not_mem_of_mem_diff h5,
        have h8, from set.not_mem_or_mem_of_not_mem_diff h2,
        cases h8 with h9 h10,
        contradiction,
        have : x ∈ σ₂.without y, from env.contains_without.rinv ⟨h10, y_neq_x⟩,
        contradiction
      end,
      have : x ∈ FV (vc.substte x t P₁ (σ₂.without y)) - (env.dom σ₁ - env.dom (σ₂.without y)),
      from set.mem_diff h3 h4,
      show «false», from P₁_ih (σ₂.without y) this
    }
  end

lemma vc.not_free_of_substte {σ: env} {x: var} {t: term} {P: vc}:
      closed_subst σ t → x ∉ FV (vc.substte x t P σ) :=
  begin
    assume t_closed: closed_subst σ t,
    have : x ∉ FV (vc.substte x t P σ) \ (σ.dom - σ.dom), from vc.not_free_of_substte_step t_closed σ,
    rw[set.diff_self] at this,
    rw[set.diff_empty] at this,
    from this
  end

lemma vc.not_free_of_subst_env {x: var} {σ: env} {P: vc}: x ∈ σ → x ∉ FV (vc.subst_env σ P) :=
  assume x_in_σ: x ∈ σ,
  assume x_free: x ∈ FV (vc.subst_env σ P),
  begin
    induction σ with σ' y v ih,

    -- env.empty
    show «false», by cases x_in_σ,

    -- σ'[x↦v]
    show «false», from (
      have vc.subst_env (σ'[y↦v]) P = vc.subst y v (vc.subst_env σ' P), by unfold vc.subst_env,
      have x ∈ FV (vc.subst y v (vc.subst_env σ' P)), from this ▸ x_free,
      have x_neq_y: x ≠ y, from (free_in_vc.subst this).left,
      have h: x ∈ FV (vc.subst_env σ' P), from (free_in_vc.subst this).right,
      have x = y ∨ x ∈ σ', from env.contains.inv x_in_σ,
      or.elim this (
        assume : x = y,
        show «false», from x_neq_y this
      ) (
        assume : x ∈ σ',
        have x ∉ FV (vc.subst_env σ' P), from ih this,
        show «false», from this h
      )
    )
  end

lemma vc.closed_of_closed_subst {σ: env} {P: vc}: closed_subst σ P → closed (vc.subst_env σ P) :=
  assume P_closed_subst: closed_subst σ P,
  show closed (vc.subst_env σ P), from (
    assume x: var,
    assume h1: x ∈ FV (vc.subst_env σ P),
    have x ∈ FV P, from free_in_vc.subst_env h1,
    have x ∈ σ.dom, from P_closed_subst this,
    have x ∈ σ, from this,
    have h2: x ∉ FV (vc.subst_env σ P), from vc.not_free_of_subst_env this,
    show «false», from h2 h1
  )

lemma term.free_of_diff_subst {x y: var} {v: value} {t: term}: x ∈ FV t → x ≠ y → x ∈ FV (term.subst y v t) :=
  assume x_free: x ∈ FV t,
  assume x_neq_y: x ≠ y,
  show x ∈ FV (term.subst y v t), from begin
    induction t with v' z unop t₁ t₁_ih binop t₂ t₃ t₂_ih t₃_ih t₄ t₅ t₄_ih t₅_ih,

    show x ∈ FV (term.subst y v (term.value v')), by begin -- term.value
      unfold term.subst,
      from x_free
    end,

    show x ∈ FV (term.subst y v (term.var z)), by begin -- term.var
      have : (x = z), from free_in_term.var.inv x_free,
      rw[this] at x_neq_y,

      have : (term.subst y v z = z), from term.subst.var.diff x_neq_y.symm,
      change x ∈ FV (term.subst y v ↑z),
      rw[this],
      from x_free
    end,

    show x ∈ FV (term.subst y v (term.unop unop t₁)), by begin -- term.unop
      unfold term.subst,
      apply free_in_term.unop,
      have : x ∈ FV t₁, from free_in_term.unop.inv x_free,
      from t₁_ih this
    end,

    show x ∈ FV (term.subst y v (term.binop binop t₂ t₃)), by begin -- term.binop
      unfold term.subst,
      have : x ∈ FV t₂ ∨ x ∈ FV t₃, from free_in_term.binop.inv x_free,
      cases this with h,
      apply free_in_term.binop₁,
      from t₂_ih h,
      apply free_in_term.binop₂,
      from t₃_ih a
    end,

    show x ∈ FV (term.subst y v (term.app t₄ t₅)), by begin -- term.binop
      unfold term.subst,
      have : x ∈ FV t₄ ∨ x ∈ FV t₅, from free_in_term.app.inv x_free,
      cases this with h,
      apply free_in_term.app₁,
      from t₄_ih h,
      apply free_in_term.app₂,
      from t₅_ih a
    end,
  end

lemma vc.free_of_diff_subst {x y: var} {v: value} {P: vc}: x ∈ FV P → x ≠ y → x ∈ FV (vc.subst y v P) :=
  assume x_free: x ∈ FV P,
  assume x_neq_y: x ≠ y,
  show x ∈ FV (vc.subst y v P), from begin
    induction P,
    case vc.term t {
      unfold vc.subst,
      apply free_in_vc.term,
      have h2, from free_in_vc.term.inv x_free,
      from term.free_of_diff_subst h2 x_neq_y
    },
    case vc.not P₁ P₁_ih {
      unfold vc.subst,
      apply free_in_vc.not,
      have h2, from free_in_vc.not.inv x_free,
      from P₁_ih h2
    },
    case vc.and P₁ P₂ P₁_ih P₂_ih {
      unfold vc.subst,
      have : x ∈ FV P₁ ∨ x ∈ FV P₂, from free_in_vc.and.inv x_free,
      cases this with h,
      apply free_in_vc.and₁,
      from P₁_ih h,
      apply free_in_vc.and₂,
      from P₂_ih a
    },
    case vc.or P₁ P₂ P₁_ih P₂_ih {
      unfold vc.subst,
      have : x ∈ FV P₁ ∨ x ∈ FV P₂, from free_in_vc.or.inv x_free,
      cases this with h,
      apply free_in_vc.or₁,
      from P₁_ih h,
      apply free_in_vc.or₂,
      from P₂_ih a
    },
    case vc.pre t₁ t₂ {
      unfold vc.subst,
      have : x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.pre.inv x_free,
      cases this with h,
      apply free_in_vc.pre₁,
      from term.free_of_diff_subst h x_neq_y,
      apply free_in_vc.pre₂,
      from term.free_of_diff_subst a x_neq_y
    },
    case vc.pre₁ op t {
      unfold vc.subst,
      apply free_in_vc.preop,
      have h2, from free_in_vc.pre₁.inv x_free,
      from term.free_of_diff_subst h2 x_neq_y
    },
    case vc.pre₂ op t₁ t₂ {
      unfold vc.subst,
      have : x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.pre₂.inv x_free,
      cases this with h,
      apply free_in_vc.preop₁,
      from term.free_of_diff_subst h x_neq_y,
      apply free_in_vc.preop₂,
      from term.free_of_diff_subst a x_neq_y
    },
    case vc.post t₁ t₂ {
      unfold vc.subst,
      have : x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.post.inv x_free,
      cases this with h,
      apply free_in_vc.post₁,
      from term.free_of_diff_subst h x_neq_y,
      apply free_in_vc.post₂,
      from term.free_of_diff_subst a x_neq_y
    },
    case vc.univ z P₁ P₁_ih {
      unfold vc.subst,
      have h2, from free_in_vc.univ.inv x_free,
      apply free_in_vc.univ,
      from h2.left,
      by_cases (y = z),
      rw[h],
      simp,
      from h2.right,
      simp[h],
      from P₁_ih h2.right
    }
  end

lemma term.free_of_subst_env {x: var} {σ: env} {t: term}: x ∈ FV t → x ∉ σ → x ∈ FV (term.subst_env σ t) :=
  assume x_free: x ∈ FV t,
  assume x_not_in_σ: x ∉ σ,
  show x ∈ FV (term.subst_env σ t), begin
    induction σ with σ' y v ih,

    -- env.empty
    show x ∈ FV (term.subst_env env.empty t), begin
      unfold term.subst_env,
      from x_free
    end,

    -- σ'[x↦v]
    show x ∈ FV (term.subst_env (σ'[y↦v]) t), begin
      unfold term.subst_env,
      by_cases (x = y),
      begin -- x = y
        rw[h] at x_not_in_σ,
        have : y ∈ (σ'[y↦v]), from env.contains.same,
        contradiction
      end,
      begin -- x ≠ y
        by_cases (x ∈ σ') with h2,
        begin -- x ∈ σ'
          have : x ∈ (σ'[y↦v]), from env.contains.rest h2,
          contradiction
        end,
        begin -- x ∉ σ'
          have : x ∈ FV (term.subst_env σ' t), from ih h2,
          from term.free_of_diff_subst this h
        end,
      end
    end
  end

lemma vc.free_of_subst_env {x: var} {σ: env} {P: vc}: x ∈ FV P → x ∉ σ → x ∈ FV (vc.subst_env σ P) :=
  assume x_free: x ∈ FV P,
  assume x_not_in_σ: x ∉ σ,
  show x ∈ FV (vc.subst_env σ P), begin
    induction σ with σ' y v ih,

    -- env.empty
    show x ∈ FV (vc.subst_env env.empty P), begin
      unfold vc.subst_env,
      from x_free
    end,

    -- σ'[x↦v]
    show x ∈ FV (vc.subst_env (σ'[y↦v]) P), begin
      unfold vc.subst_env,
      by_cases (x = y),
      begin -- x = y
        rw[h] at x_not_in_σ,
        have : y ∈ (σ'[y↦v]), from env.contains.same,
        contradiction
      end,
      begin -- x ≠ y
        by_cases (x ∈ σ') with h2,
        begin -- x ∈ σ'
          have : x ∈ (σ'[y↦v]), from env.contains.rest h2,
          contradiction
        end,
        begin -- x ∉ σ'
          have : x ∈ FV (vc.subst_env σ' P), from ih h2,
          from vc.free_of_diff_subst this h
        end,
      end
    end
  end

lemma term.free_of_free_in_subst {x y: var} {v: value} {t: term}: x ∈ FV (term.subst y v t) → x ∈ FV t :=
  begin
    assume h1,
    induction t with v' z unop t₁ t₁_ih binop t₂ t₃ t₂_ih t₃_ih t₄ t₅ t₄_ih t₅_ih,

    show x ∈ FV (term.value v'), by begin
      unfold term.subst at h1,
      cases h1
    end,

    show x ∈ FV (term.var z), by begin
      unfold term.subst at h1,
      by_cases (y = z) with h2,
      simp[h2] at h1,
      cases h1,
      simp[h2] at h1,
      from h1
    end,

    show x ∈ FV (term.unop unop t₁), by begin
      unfold term.subst at h1,
      apply free_in_term.unop,
      have h2, from free_in_term.unop.inv h1,
      from t₁_ih h2
    end,

    show x ∈ FV (term.binop binop t₂ t₃), by begin
      unfold term.subst at h1,
      have h2, from free_in_term.binop.inv h1,
      cases h2,
      apply free_in_term.binop₁,
      from t₂_ih a,
      apply free_in_term.binop₂,
      from t₃_ih a
    end,

    show x ∈ FV (term.app t₄ t₅), by begin
      unfold term.subst at h1,
      have h2, from free_in_term.app.inv h1,
      cases h2,
      apply free_in_term.app₁,
      from t₄_ih a,
      apply free_in_term.app₂,
      from t₅_ih a
    end
  end

lemma term.closed_subst_of_closed {σ: env} {t: term}: closed (term.subst_env σ t) → closed_subst σ t :=
  assume t_closed_subst: closed (term.subst_env σ t),
  show closed_subst σ t, from (
    assume x: var,
    assume h1: x ∈ FV t,
    have ¬ x ∉ σ, from mt (term.free_of_subst_env h1) (t_closed_subst x),
    have x ∈ σ, from of_not_not this,
    show x ∈ σ.dom, from this
  )

lemma prop.free_of_free_in_subst {x y: var} {v: value} {P: prop}: x ∈ FV (prop.subst y v P) → x ∈ FV P :=
  begin
    assume h1,
    induction P,
    case prop.term t {
      apply free_in_prop.term,
      have h2, from free_in_prop.term.inv h1,
      from term.free_of_free_in_subst h2
    },
    case prop.not P₁ ih {
      apply free_in_prop.not,
      unfold prop.subst at h1,
      have h2, from free_in_prop.not.inv h1,
      from ih h2     
    },
    case prop.and P₁ P₂ P₁_ih P₂_ih {
      unfold prop.subst at h1,
      have h2, from free_in_prop.and.inv h1,
      cases h2,
      apply free_in_prop.and₁,
      from P₁_ih a,
      apply free_in_prop.and₂,
      from P₂_ih a
    },
    case prop.or P₁ P₂ P₁_ih P₂_ih {
      unfold prop.subst at h1,
      have h2, from free_in_prop.or.inv h1,
      cases h2,
      apply free_in_prop.or₁,
      from P₁_ih a,
      apply free_in_prop.or₂,
      from P₂_ih a
    },
    case prop.pre t₁ t₂ {
      unfold prop.subst at h1,
      have h2, from free_in_prop.pre.inv h1,
      cases h2,
      apply free_in_prop.pre₁,
      from term.free_of_free_in_subst a,
      apply free_in_prop.pre₂,
      from term.free_of_free_in_subst  a
    },
    case prop.pre₁ op t {
      unfold prop.subst at h1,
      have h2, from free_in_prop.pre₁.inv h1,
      apply free_in_prop.preop,
      from term.free_of_free_in_subst h2
    },
    case prop.pre₂ op t₁ t₂ {
      unfold prop.subst at h1,
      have h2, from free_in_prop.pre₂.inv h1,
      cases h2,
      apply free_in_prop.preop₁,
      from term.free_of_free_in_subst a,
      apply free_in_prop.preop₂,
      from term.free_of_free_in_subst  a
    },
    case prop.call t {
      unfold prop.subst at h1,
      have h2, from free_in_prop.call.inv h1,
      apply free_in_prop.call,
      from term.free_of_free_in_subst h2
    },
    case prop.post t₁ t₂ {
      unfold prop.subst at h1,
      have h2, from free_in_prop.post.inv h1,
      cases h2,
      apply free_in_prop.post₁,
      from term.free_of_free_in_subst a,
      apply free_in_prop.post₂,
      from term.free_of_free_in_subst  a
    },
    case prop.forallc z P' P'_ih {
      unfold prop.subst at h1,
      have h2, from free_in_prop.forallc.inv h1,
      by_cases (y = z) with h3,
      have h4, from h2.right,
      rw[h3] at h4,
      simp at h4,
      apply free_in_prop.forallc,
      from h2.left,
      from h4,

      have h4, from h2.right,
      simp[h3] at h4,
      apply free_in_prop.forallc,
      from h2.left,
      simp[h3] at h4,
      from P'_ih h4
    },
    case prop.exis z P' P'_ih {
      unfold prop.subst at h1,
      have h2, from free_in_prop.exis.inv h1,
      by_cases (y = z) with h3,
      have h4, from h2.right,
      rw[h3] at h4,
      simp at h4,
      apply free_in_prop.exis,
      from h2.left,
      from h4,

      have h4, from h2.right,
      simp[h3] at h4,
      have : ((ite (y = z) P' (prop.subst y v P')) = (prop.subst y v P')), by simp[h3],
      rw[this] at h4,
      apply free_in_prop.exis,
      from h2.left,
      from P'_ih h4
    }
  end

lemma prop.free_of_free_subst_env {x: var} {σ: env} {P: prop}: x ∈ FV (prop.subst_env σ P) → x ∈ FV P :=
  assume x_free: x ∈ FV (prop.subst_env σ P),
  show x ∈ FV P, begin
    induction σ with σ' y v ih,

    -- env.empty
    show x ∈ FV P, begin
      unfold prop.subst_env at x_free,
      from x_free
    end,

    -- σ'[x↦v]
    show x ∈ FV P, begin
      unfold prop.subst_env at x_free,
      have h1: x ∈ FV (prop.subst_env σ' P), from prop.free_of_free_in_subst x_free,
      from ih h1
    end
  end

lemma vc.free_of_free_in_subst {x y: var} {v: value} {P: vc}: x ∈ FV (vc.subst y v P) → x ∈ FV P :=
  begin
    assume h1,
    induction P,
    case vc.term t {
      apply free_in_vc.term,
      have h2, from free_in_vc.term.inv h1,
      from term.free_of_free_in_subst h2
    },
    case vc.not P₁ ih {
      apply free_in_vc.not,
      unfold vc.subst at h1,
      have h2, from free_in_vc.not.inv h1,
      from ih h2     
    },
    case vc.and P₁ P₂ P₁_ih P₂_ih {
      unfold vc.subst at h1,
      have h2, from free_in_vc.and.inv h1,
      cases h2,
      apply free_in_vc.and₁,
      from P₁_ih a,
      apply free_in_vc.and₂,
      from P₂_ih a
    },
    case vc.or P₁ P₂ P₁_ih P₂_ih {
      unfold vc.subst at h1,
      have h2, from free_in_vc.or.inv h1,
      cases h2,
      apply free_in_vc.or₁,
      from P₁_ih a,
      apply free_in_vc.or₂,
      from P₂_ih a
    },
    case vc.pre t₁ t₂ {
      unfold vc.subst at h1,
      have h2, from free_in_vc.pre.inv h1,
      cases h2,
      apply free_in_vc.pre₁,
      from term.free_of_free_in_subst a,
      apply free_in_vc.pre₂,
      from term.free_of_free_in_subst  a
    },
    case vc.pre₁ op t {
      unfold vc.subst at h1,
      have h2, from free_in_vc.pre₁.inv h1,
      apply free_in_vc.preop,
      from term.free_of_free_in_subst h2
    },
    case vc.pre₂ op t₁ t₂ {
      unfold vc.subst at h1,
      have h2, from free_in_vc.pre₂.inv h1,
      cases h2,
      apply free_in_vc.preop₁,
      from term.free_of_free_in_subst a,
      apply free_in_vc.preop₂,
      from term.free_of_free_in_subst  a
    },
    case vc.post t₁ t₂ {
      unfold vc.subst at h1,
      have h2, from free_in_vc.post.inv h1,
      cases h2,
      apply free_in_vc.post₁,
      from term.free_of_free_in_subst a,
      apply free_in_vc.post₂,
      from term.free_of_free_in_subst  a
    },
    case vc.univ z P' P'_ih {
      unfold vc.subst at h1,
      have h2, from free_in_vc.univ.inv h1,
      by_cases (y = z) with h3,
      have h4, from h2.right,
      rw[h3] at h4,
      simp at h4,
      apply free_in_vc.univ,
      from h2.left,
      from h4,

      have h4, from h2.right,
      simp[h3] at h4,
      have : ((ite (y = z) P' (vc.subst y v P')) = (vc.subst y v P')), by simp[h3],
      rw[this] at h4,
      apply free_in_vc.univ,
      from h2.left,
      from P'_ih h4
    }
  end

lemma vc.free_of_free_subst_env {x: var} {σ: env} {P: vc}: x ∈ FV (vc.subst_env σ P) → x ∈ FV P :=
  assume x_free: x ∈ FV (vc.subst_env σ P),
  show x ∈ FV P, begin
    induction σ with σ' y v ih,

    -- env.empty
    show x ∈ FV P, begin
      unfold vc.subst_env at x_free,
      from x_free
    end,

    -- σ'[x↦v]
    show x ∈ FV P, begin
      unfold vc.subst_env at x_free,
      have h1: x ∈ FV (vc.subst_env σ' P), from vc.free_of_free_in_subst x_free,
      from ih h1
    end
  end

lemma vc.closed_subst_of_closed {σ: env} {P: vc}: closed (vc.subst_env σ P) → closed_subst σ P :=
  assume P_closed_subst: closed (vc.subst_env σ P),
  show closed_subst σ P, from (
    assume x: var,
    assume h1: x ∈ FV P,
    have ¬ x ∉ σ, from mt (vc.free_of_subst_env h1) (P_closed_subst x),
    have x ∈ σ, from of_not_not this,
    show x ∈ σ.dom, from this
  )

lemma prop.closed_any_subst_of_closed {σ: env} {P: prop}: closed P → closed_subst σ P :=
  assume P_closed: closed P,
  show closed_subst σ P, from (
    assume x: var,
    assume : x ∈ FV P,
    show x ∈ σ.dom, from absurd this (P_closed x)
  )

lemma term.subst_env.unop {σ: env} {op: unop} {t: term}:
      term.subst_env σ (term.unop op t) = term.unop op (term.subst_env σ t) :=
begin
  induction σ with σ' x v ih,

  show (term.subst_env env.empty (term.unop op t) = term.unop op (term.subst_env env.empty t)),
  by calc
        term.subst_env env.empty (term.unop op t)
      = (term.unop op t) : by unfold term.subst_env
  ... = (term.unop op (term.subst_env env.empty t)) : by unfold term.subst_env,

  show (term.subst_env (σ'[x↦v]) (term.unop op t) = (term.unop op (term.subst_env (σ'[x↦v]) t))),
  by calc
        term.subst_env (σ'[x↦v]) (term.unop op t)
      = term.subst x v (term.subst_env σ' (term.unop op t)) : by unfold term.subst_env
  ... = term.subst x v (term.unop op (term.subst_env σ' t)) : by rw[ih]
  ... = term.unop op (term.subst x v (term.subst_env σ' t)) : by unfold term.subst
  ... = term.unop op (term.subst_env (σ'[x↦v]) t) : by unfold term.subst_env
end

lemma term.subst_env.binop {σ: env} {op: binop} {t₁ t₂: term}:
      term.subst_env σ (term.binop op t₁ t₂) = term.binop op (term.subst_env σ t₁) (term.subst_env σ t₂) :=
begin
  induction σ with σ' x v ih,

  show (term.subst_env env.empty (term.binop op t₁ t₂)
      = term.binop op (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)),
  by calc
        term.subst_env env.empty (term.binop op t₁ t₂)
      = (term.binop op t₁ t₂) : by unfold term.subst_env
  ... = (term.binop op (term.subst_env env.empty t₁) t₂) : by unfold term.subst_env
  ... = (term.binop op (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)) : by unfold term.subst_env,

  show (term.subst_env (σ'[x↦v]) (term.binop op t₁ t₂)
      = (term.binop op (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂))),
  by calc
        term.subst_env (σ'[x↦v]) (term.binop op t₁ t₂)
      = term.subst x v (term.subst_env σ' (term.binop op t₁ t₂)) : by unfold term.subst_env
  ... = term.subst x v (term.binop op (term.subst_env σ' t₁) (term.subst_env σ' t₂)) : by rw[ih]
  ... = term.binop op (term.subst x v (term.subst_env σ' t₁))
                      (term.subst x v (term.subst_env σ' t₂)) : by unfold term.subst
  ... = term.binop op (term.subst_env (σ'[x↦v]) t₁)
                      (term.subst x v (term.subst_env σ' t₂)) : by unfold term.subst_env
  ... = term.binop op (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂) : by unfold term.subst_env
end

lemma term.subst_env.app {σ: env} {t₁ t₂: term}:
      term.subst_env σ (term.app t₁ t₂) = term.app (term.subst_env σ t₁) (term.subst_env σ t₂) :=
begin
  induction σ with σ' x v ih,

  show (term.subst_env env.empty (term.app t₁ t₂)
      = term.app (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)),
  by calc
        term.subst_env env.empty (term.app t₁ t₂)
      = (term.app t₁ t₂) : by unfold term.subst_env
  ... = (term.app (term.subst_env env.empty t₁) t₂) : by unfold term.subst_env
  ... = (term.app (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)) : by unfold term.subst_env,

  show (term.subst_env (σ'[x↦v]) (term.app t₁ t₂)
      = (term.app (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂))),
  by calc
        term.subst_env (σ'[x↦v]) (term.app t₁ t₂)
      = term.subst x v (term.subst_env σ' (term.app t₁ t₂)) : by unfold term.subst_env
  ... = term.subst x v (term.app (term.subst_env σ' t₁) (term.subst_env σ' t₂)) : by rw[ih]
  ... = term.app (term.subst x v (term.subst_env σ' t₁))
                      (term.subst x v (term.subst_env σ' t₂)) : by unfold term.subst
  ... = term.app (term.subst_env (σ'[x↦v]) t₁)
                      (term.subst x v (term.subst_env σ' t₂)) : by unfold term.subst_env
  ... = term.app (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂) : by unfold term.subst_env
end

lemma prop.subst_env.term {σ: env} {t: term}:
  prop.subst_env σ t = prop.term (term.subst_env σ t) :=
begin
  induction σ with σ' x v ih,

  show (prop.subst_env env.empty t = prop.term (term.subst_env env.empty t)), by begin
    have : (term.subst_env env.empty t = t), by unfold term.subst_env,
    have h2: (prop.term (term.subst_env env.empty t) = prop.term t), by simp[this],
    calc
      prop.subst_env env.empty t = t : by unfold prop.subst_env
                             ... = prop.term t : by refl
                             ... = prop.term (term.subst_env env.empty t) : by rw[←h2]
  end,

  show (prop.subst_env (σ'[x↦v]) t = prop.term (term.subst_env (σ'[x↦v]) t)),
  by calc
        prop.subst_env (σ'[x↦v]) t = prop.subst x v (prop.subst_env σ' t) : by unfold prop.subst_env
                               ... = prop.subst x v (prop.term (term.subst_env σ' t)) : by rw[ih]
                               ... = term.subst x v (term.subst_env σ' t) : by unfold prop.subst
                               ... = term.subst_env (σ'[x↦v]) t : by unfold term.subst_env
end

lemma prop.subst_env.not {σ: env} {P: prop}:
      prop.subst_env σ P.not = (prop.subst_env σ P).not :=
begin
  induction σ with σ' x v ih,

  show (prop.subst_env env.empty P.not = (prop.subst_env env.empty P).not),
  by calc
        prop.subst_env env.empty P.not = P.not : by unfold prop.subst_env
                                   ... = (prop.subst_env env.empty P).not : by unfold prop.subst_env,

  show (prop.subst_env (σ'[x↦v]) P.not = (prop.subst_env (σ'[x↦v]) P).not),
  by calc
        prop.subst_env (σ'[x↦v]) P.not = prop.subst x v (prop.subst_env σ' P.not) : by unfold prop.subst_env
                                   ... = prop.subst x v (prop.subst_env σ' P).not : by rw[ih]
                                   ... = (prop.subst x v (prop.subst_env σ' P)).not : by unfold prop.subst
                                   ... = (prop.subst_env (σ'[x↦v]) P).not : by unfold prop.subst_env
end

lemma prop.subst_env.and {σ: env} {P Q: prop}:
      prop.subst_env σ (P ⋀ Q) = (prop.subst_env σ P ⋀ prop.subst_env σ Q) :=
begin
  induction σ with σ' x v ih,

  show (prop.subst_env env.empty (P ⋀ Q) = (prop.subst_env env.empty P ⋀ prop.subst_env env.empty Q)),
  by calc
        prop.subst_env env.empty (P ⋀ Q) = (P ⋀ Q) : by unfold prop.subst_env
                                      ... = (prop.subst_env env.empty P ⋀ Q) : by unfold prop.subst_env
                                      ... = (prop.subst_env env.empty P ⋀ prop.subst_env env.empty Q)
                                                     : by unfold prop.subst_env,

  show (prop.subst_env (σ'[x↦v]) (P ⋀ Q) = (prop.subst_env (σ'[x↦v]) P ⋀ prop.subst_env (σ'[x↦v]) Q)),
  by calc
        prop.subst_env (σ'[x↦v]) (P ⋀ Q) = prop.subst x v (prop.subst_env σ' (P ⋀ Q)) : by unfold prop.subst_env
                                      ... = prop.subst x v (prop.subst_env σ' P ⋀ prop.subst_env σ' Q) : by rw[ih]
                                      ... = (prop.subst x v (prop.subst_env σ' P) ⋀
                                             prop.subst x v (prop.subst_env σ' Q)) : by refl
                                      ... = (prop.subst_env (σ'[x↦v]) P ⋀
                                             prop.subst x v (prop.subst_env σ' Q)) : by unfold prop.subst_env
                                      ... = (prop.subst_env (σ'[x↦v]) P ⋀ prop.subst_env (σ'[x↦v]) Q)
                                                                               : by unfold prop.subst_env
end

lemma prop.subst_env.or {σ: env} {P Q: prop}:
      prop.subst_env σ (P ⋁ Q) = (prop.subst_env σ P ⋁ prop.subst_env σ Q) :=
begin
  induction σ with σ' x v ih,

  show (prop.subst_env env.empty (P ⋁ Q) = (prop.subst_env env.empty P ⋁ prop.subst_env env.empty Q)),
  by calc
        prop.subst_env env.empty (P ⋁ Q) = (P ⋁ Q) : by unfold prop.subst_env
                                      ... = (prop.subst_env env.empty P ⋁ Q) : by by unfold prop.subst_env
                                      ... = (prop.subst_env env.empty P ⋁ prop.subst_env env.empty Q)
                                                     : by unfold prop.subst_env,

  show (prop.subst_env (σ'[x↦v]) (P ⋁ Q) = (prop.subst_env (σ'[x↦v]) P ⋁ prop.subst_env (σ'[x↦v]) Q)),
  by calc
        prop.subst_env (σ'[x↦v]) (P ⋁ Q) = prop.subst x v (prop.subst_env σ' (P ⋁ Q)) : by unfold prop.subst_env
                                      ... = prop.subst x v (prop.subst_env σ' P ⋁ prop.subst_env σ' Q) : by rw[ih]
                                      ... = (prop.subst x v (prop.subst_env σ' P) ⋁
                                             prop.subst x v (prop.subst_env σ' Q)) : by refl
                                      ... = (prop.subst_env (σ'[x↦v]) P ⋁
                                             prop.subst x v (prop.subst_env σ' Q)) : by unfold prop.subst_env
                                      ... = (prop.subst_env (σ'[x↦v]) P ⋁ prop.subst_env (σ'[x↦v]) Q)
                                               : by unfold prop.subst_env
end

lemma prop.subst_env.implies {σ: env} {P Q: prop}:
      prop.subst_env σ (prop.implies P Q) = prop.implies (prop.subst_env σ P) (prop.subst_env σ Q) :=
  have h1: prop.subst_env σ (prop.implies P Q) = prop.subst_env σ (P.not ⋁ Q), by refl,
  have prop.subst_env σ (P.not ⋁ Q) = (prop.subst_env σ P.not ⋁ prop.subst_env σ Q), from prop.subst_env.or,
  have h2: prop.subst_env σ (prop.implies P Q) = (prop.subst_env σ P.not ⋁ prop.subst_env σ Q), from this ▸ h1,
  have prop.subst_env σ P.not = prop.not (prop.subst_env σ P), from prop.subst_env.not,
  have prop.subst_env σ (prop.implies P Q) = (prop.not (prop.subst_env σ P) ⋁ prop.subst_env σ Q), from this ▸ h2,
  show prop.subst_env σ (prop.implies P Q) = prop.implies (prop.subst_env σ P) (prop.subst_env σ Q), from this

lemma prop.subst_env.pre {σ: env} {t₁ t₂: term}:
      prop.subst_env σ (prop.pre t₁ t₂) = prop.pre (term.subst_env σ t₁) (term.subst_env σ t₂) :=
begin
  induction σ with σ' x v ih,

  show (prop.subst_env env.empty (prop.pre t₁ t₂)
      = prop.pre (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)),
  by calc
        prop.subst_env env.empty (prop.pre t₁ t₂)
      = (prop.pre t₁ t₂) : by unfold prop.subst_env
  ... = (prop.pre (term.subst_env env.empty t₁) t₂) : by unfold term.subst_env
  ... = (prop.pre (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)) : by unfold term.subst_env,

  show (prop.subst_env (σ'[x↦v]) (prop.pre t₁ t₂)
      = prop.pre (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂)),
  by calc
        prop.subst_env (σ'[x↦v]) (prop.pre t₁ t₂)
      = prop.subst x v (prop.subst_env σ' (prop.pre t₁ t₂)) : by unfold prop.subst_env
  ... = prop.subst x v (prop.pre (term.subst_env σ' t₁) (term.subst_env σ' t₂)) : by rw[ih]
  ... = prop.pre (term.subst x v (term.subst_env σ' t₁)) (term.subst x v (term.subst_env σ' t₂)) : by unfold prop.subst
  ... = prop.pre (term.subst_env (σ'[x↦v]) t₁) (term.subst x v (term.subst_env σ' t₂)) : by unfold term.subst_env
  ... = prop.pre (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂) : by unfold term.subst_env
end

lemma prop.subst_env.post {σ: env} {t₁ t₂: term}:
      prop.subst_env σ (prop.post t₁ t₂) = prop.post (term.subst_env σ t₁) (term.subst_env σ t₂) :=
begin
  induction σ with σ' x v ih,

  show (prop.subst_env env.empty (prop.post t₁ t₂)
      = prop.post (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)),
  by calc
        prop.subst_env env.empty (prop.post t₁ t₂)
      = (prop.post t₁ t₂) : by unfold prop.subst_env
  ... = (prop.post (term.subst_env env.empty t₁) t₂) : by unfold term.subst_env
  ... = (prop.post (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)) : by unfold term.subst_env,

  show (prop.subst_env (σ'[x↦v]) (prop.post t₁ t₂)
      = prop.post (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂)),
  by calc
        prop.subst_env (σ'[x↦v]) (prop.post t₁ t₂)
      = prop.subst x v (prop.subst_env σ' (prop.post t₁ t₂)) : by unfold prop.subst_env
  ... = prop.subst x v (prop.post (term.subst_env σ' t₁) (term.subst_env σ' t₂)) : by rw[ih]
  ... = prop.post (term.subst x v (term.subst_env σ' t₁)) (term.subst x v (term.subst_env σ' t₂)) : by unfold prop.subst
  ... = prop.post (term.subst_env (σ'[x↦v]) t₁) (term.subst x v (term.subst_env σ' t₂)) : by unfold term.subst_env
  ... = prop.post (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂) : by unfold term.subst_env
end

lemma prop.subst_env.forallc_not_in {σ: env} {x: var} {P: prop}:
      (x ∉ σ) → (prop.subst_env σ (prop.forallc x P) = prop.forallc x (prop.subst_env σ P)) :=
begin
  assume x_not_in_σ,
  induction σ with σ' y v ih,

  show (prop.subst_env env.empty (prop.forallc x P)
      = prop.forallc x (prop.subst_env env.empty P)),
  by calc
        prop.subst_env env.empty (prop.forallc x P)
      = prop.forallc x P : by unfold prop.subst_env
  ... = prop.forallc x (prop.subst_env env.empty P) : by unfold prop.subst_env,

  show (prop.subst_env (σ'[y↦v]) (prop.forallc x P)
      = prop.forallc x (prop.subst_env (σ'[y↦v]) P)), from (
    have ¬ (x = y ∨ x ∈ σ'), from env.contains.same.inv x_not_in_σ,
    have x_neq_y: x ≠ y, from (not_or_distrib.mp this).left,
    have x ∉ σ', from (not_or_distrib.mp this).right,
    have h: prop.subst_env σ' (prop.forallc x P) = prop.forallc x (prop.subst_env σ' P),
    from ih this,

    calc
        prop.subst_env (σ'[y↦v]) (prop.forallc x P)
      = prop.subst y v (prop.subst_env σ' (prop.forallc x P)) : by unfold prop.subst_env
  ... = prop.subst y v (prop.forallc x (prop.subst_env σ' P)) : by rw[h]
  ... = prop.forallc x (if y = x then prop.subst_env σ' P else (prop.subst_env σ' P).subst y v)
     : by unfold prop.subst
  ... = prop.forallc x ((prop.subst_env σ' P).subst y v) : by simp[x_neq_y.symm]
  ... = prop.forallc x (prop.subst_env (σ'[y↦v]) P) : by unfold prop.subst_env
  )
end

lemma prop.subst_env.forallc {σ: env} {x: var} {P: prop}:
      (prop.subst_env σ (prop.forallc x P) = prop.forallc x (prop.subst_env (σ.without x) P)) :=
begin
  induction σ with σ' y v ih,

  show (prop.subst_env env.empty (prop.forallc x P) = prop.forallc x (prop.subst_env (env.empty.without x) P)),
  by calc
        prop.subst_env env.empty (prop.forallc x P) = (prop.forallc x P) : by unfold prop.subst_env
                                                ... = prop.forallc x (prop.subst_env env.empty P)
                                                             : by unfold prop.subst_env,

  show (prop.subst_env (σ'[y↦v]) (prop.forallc x P) = prop.forallc x (prop.subst_env ((σ'[y↦v]).without x) P)),
  by begin
    unfold prop.subst_env,
    by_cases (y = x) with h1,
    rw[←h1],
    rw[←h1] at ih,
    unfold env.without,
    simp,
    have : y ∉ FV (prop.subst_env σ' (prop.forallc y P)), from (
      assume : y ∈ FV (prop.subst_env σ' (prop.forallc y P)),
      have y ∈ FV (prop.forallc y P), from prop.free_of_free_subst_env this,
      show «false», from free_in_prop.forallc.same.inv this
    ),
    have h2: (prop.subst y v (prop.subst_env σ' (prop.forallc y P)) = prop.subst_env σ' (prop.forallc y P)),
    from unchanged_of_subst_nonfree_prop this,
    rw[h2],
    from ih,

    unfold env.without,
    simp[h1],
    unfold prop.subst_env,
    have : (prop.subst y v (prop.forallc x (prop.subst_env (env.without σ' x) P))
          = prop.forallc x (prop.subst y v (prop.subst_env (env.without σ' x) P))),
    by { unfold prop.subst, simp[h1] },
    rw[←this],
    congr,
    from ih  
  end
end

lemma vc.subst.implies {x: var} {v: value} {P Q: vc}:
      vc.subst x v (vc.implies P Q) = vc.implies (vc.subst x v P) (vc.subst x v Q) :=
  by calc 
       vc.subst x v (vc.implies P Q) = vc.subst x v (vc.or (vc.not P) Q) : rfl
                                 ... = (vc.subst x v (vc.not P) ⋁ vc.subst x v Q) : by unfold vc.subst
                                 ... = ((vc.subst x v P).not ⋁ vc.subst x v Q) : by unfold vc.subst

lemma vc.subst_env.term {σ: env} {t: term}:
  vc.subst_env σ t = vc.term (term.subst_env σ t) :=
begin
  induction σ with σ' x v ih,

  show (vc.subst_env env.empty t = vc.term (term.subst_env env.empty t)), by begin
    have : (term.subst_env env.empty t = t), by unfold term.subst_env,
    have h2: (vc.term (term.subst_env env.empty t) = vc.term t), by simp[this],
    calc
      vc.subst_env env.empty t = t : by unfold vc.subst_env
                           ... = vc.term t : by refl
                           ... = vc.term (term.subst_env env.empty t) : by rw[←h2]
  end,

  show (vc.subst_env (σ'[x↦v]) t = vc.term (term.subst_env (σ'[x↦v]) t)),
  by calc
        vc.subst_env (σ'[x↦v]) t = vc.subst x v (vc.subst_env σ' t) : by unfold vc.subst_env
                             ... = vc.subst x v (vc.term (term.subst_env σ' t)) : by rw[ih]
                             ... = term.subst x v (term.subst_env σ' t) : by unfold vc.subst
                             ... = term.subst_env (σ'[x↦v]) t : by unfold term.subst_env
end

lemma vc.subst_env.not {σ: env} {P: vc}:
      vc.subst_env σ P.not = (vc.subst_env σ P).not :=
begin
  induction σ with σ' x v ih,

  show (vc.subst_env env.empty P.not = (vc.subst_env env.empty P).not),
  by calc
        vc.subst_env env.empty P.not = P.not : by unfold vc.subst_env
                                 ... = (vc.subst_env env.empty P).not : by unfold vc.subst_env,

  show (vc.subst_env (σ'[x↦v]) P.not = (vc.subst_env (σ'[x↦v]) P).not),
  by calc
        vc.subst_env (σ'[x↦v]) P.not = vc.subst x v (vc.subst_env σ' P.not) : by unfold vc.subst_env
                                 ... = vc.subst x v (vc.subst_env σ' P).not : by rw[ih]
                                 ... = (vc.subst x v (vc.subst_env σ' P)).not : by unfold vc.subst
                                 ... = (vc.subst_env (σ'[x↦v]) P).not : by unfold vc.subst_env
end

lemma vc.subst_env.and {σ: env} {P Q: vc}:
      vc.subst_env σ (P ⋀ Q) = (vc.subst_env σ P ⋀ vc.subst_env σ Q) :=
begin
  induction σ with σ' x v ih,

  show (vc.subst_env env.empty (P ⋀ Q) = (vc.subst_env env.empty P ⋀ vc.subst_env env.empty Q)),
  by calc
        vc.subst_env env.empty (P ⋀ Q) = (P ⋀ Q) : by unfold vc.subst_env
                                    ... = (vc.subst_env env.empty P ⋀ Q) : by unfold vc.subst_env
                                    ... = (vc.subst_env env.empty P ⋀ vc.subst_env env.empty Q)
                                                   : by unfold vc.subst_env,

  show (vc.subst_env (σ'[x↦v]) (P ⋀ Q) = (vc.subst_env (σ'[x↦v]) P ⋀ vc.subst_env (σ'[x↦v]) Q)),
  by calc
        vc.subst_env (σ'[x↦v]) (P ⋀ Q) = vc.subst x v (vc.subst_env σ' (P ⋀ Q)) : by unfold vc.subst_env
                                    ... = vc.subst x v (vc.subst_env σ' P ⋀ vc.subst_env σ' Q) : by rw[ih]
                                    ... = (vc.subst x v (vc.subst_env σ' P) ⋀
                                           vc.subst x v (vc.subst_env σ' Q)) : by refl
                                    ... = (vc.subst_env (σ'[x↦v]) P ⋀
                                           vc.subst x v (vc.subst_env σ' Q)) : by unfold vc.subst_env
                                    ... = (vc.subst_env (σ'[x↦v]) P ⋀ vc.subst_env (σ'[x↦v]) Q)
                                                                             : by unfold vc.subst_env
end

lemma vc.subst_env.or {σ: env} {P Q: vc}:
      vc.subst_env σ (P ⋁ Q) = (vc.subst_env σ P ⋁ vc.subst_env σ Q) :=
begin
  induction σ with σ' x v ih,

  show (vc.subst_env env.empty (P ⋁ Q) = (vc.subst_env env.empty P ⋁ vc.subst_env env.empty Q)),
  by calc
        vc.subst_env env.empty (P ⋁ Q) = (P ⋁ Q) : by unfold vc.subst_env
                                    ... = (vc.subst_env env.empty P ⋁ Q) : by by unfold vc.subst_env
                                    ... = (vc.subst_env env.empty P ⋁ vc.subst_env env.empty Q)
                                                   : by unfold vc.subst_env,

  show (vc.subst_env (σ'[x↦v]) (P ⋁ Q) = (vc.subst_env (σ'[x↦v]) P ⋁ vc.subst_env (σ'[x↦v]) Q)),
  by calc
        vc.subst_env (σ'[x↦v]) (P ⋁ Q) = vc.subst x v (vc.subst_env σ' (P ⋁ Q)) : by unfold vc.subst_env
                                    ... = vc.subst x v (vc.subst_env σ' P ⋁ vc.subst_env σ' Q) : by rw[ih]
                                    ... = (vc.subst x v (vc.subst_env σ' P) ⋁
                                           vc.subst x v (vc.subst_env σ' Q)) : by refl
                                    ... = (vc.subst_env (σ'[x↦v]) P ⋁
                                           vc.subst x v (vc.subst_env σ' Q)) : by unfold vc.subst_env
                                    ... = (vc.subst_env (σ'[x↦v]) P ⋁ vc.subst_env (σ'[x↦v]) Q)
                                             : by unfold vc.subst_env
end

lemma vc.subst_env.implies {σ: env} {P Q: vc}:
      vc.subst_env σ (vc.implies P Q) = vc.implies (vc.subst_env σ P) (vc.subst_env σ Q) :=
  have h1: vc.subst_env σ (vc.implies P Q) = vc.subst_env σ (vc.or P.not Q), from rfl,
  have vc.subst_env σ (vc.or P.not Q) = vc.or (vc.subst_env σ P.not) (vc.subst_env σ Q), from vc.subst_env.or,
  have h2: vc.subst_env σ (vc.implies P Q) = vc.or (vc.subst_env σ P.not) (vc.subst_env σ Q), from eq.trans h1 this,
  have vc.subst_env σ (vc.not P) = vc.not (vc.subst_env σ P), from vc.subst_env.not,
  show vc.subst_env σ (vc.implies P Q) = vc.or (vc.subst_env σ P).not (vc.subst_env σ Q), from this ▸ h2

lemma vc.subst_env.pre₁ {σ: env} {op: unop} {t: term}:
      vc.subst_env σ (vc.pre₁ op t) = vc.pre₁ op (term.subst_env σ t) :=
begin
  induction σ with σ' x v ih,

  show (vc.subst_env env.empty (vc.pre₁ op t) = vc.pre₁ op (term.subst_env env.empty t)),
  by calc
        vc.subst_env env.empty (vc.pre₁ op t) = (vc.pre₁ op t) : by unfold vc.subst_env
                                          ... = (vc.pre₁ op (term.subst_env env.empty t)) : by unfold term.subst_env,

  show (vc.subst_env (σ'[x↦v]) (vc.pre₁ op t) = vc.pre₁ op (term.subst_env (σ'[x↦v]) t)),
  by calc
        vc.subst_env (σ'[x↦v]) (vc.pre₁ op t) = vc.subst x v (vc.subst_env σ' (vc.pre₁ op t)) : by unfold vc.subst_env
                                          ... = vc.subst x v (vc.pre₁ op (term.subst_env σ' t)) : by rw[ih]
                                          ... = vc.pre₁ op (term.subst x v (term.subst_env σ' t)) : by unfold vc.subst
                                          ... = vc.pre₁ op (term.subst_env (σ'[x↦v]) t) : by unfold term.subst_env
end

lemma vc.subst_env.pre₂ {σ: env} {op: binop} {t₁ t₂: term}:
      vc.subst_env σ (vc.pre₂ op t₁ t₂) = vc.pre₂ op (term.subst_env σ t₁) (term.subst_env σ t₂) :=
begin
  induction σ with σ' x v ih,

  show (vc.subst_env env.empty (vc.pre₂ op t₁ t₂)
      = vc.pre₂ op (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)),
  by calc
        vc.subst_env env.empty (vc.pre₂ op t₁ t₂)
      = (vc.pre₂ op t₁ t₂) : by unfold vc.subst_env
  ... = (vc.pre₂ op (term.subst_env env.empty t₁) t₂) : by unfold term.subst_env
  ... = (vc.pre₂ op (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)) : by unfold term.subst_env,

  show (vc.subst_env (σ'[x↦v]) (vc.pre₂ op t₁ t₂)
      = vc.pre₂ op (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂)),
  by calc
        vc.subst_env (σ'[x↦v]) (vc.pre₂ op t₁ t₂)
      = vc.subst x v (vc.subst_env σ' (vc.pre₂ op t₁ t₂)) : by unfold vc.subst_env
  ... = vc.subst x v (vc.pre₂ op (term.subst_env σ' t₁) (term.subst_env σ' t₂)) : by rw[ih]
  ... = vc.pre₂ op (term.subst x v (term.subst_env σ' t₁)) (term.subst x v (term.subst_env σ' t₂)) : by unfold vc.subst
  ... = vc.pre₂ op (term.subst_env (σ'[x↦v]) t₁) (term.subst x v (term.subst_env σ' t₂)) : by unfold term.subst_env
  ... = vc.pre₂ op (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂) : by unfold term.subst_env
end

lemma vc.subst_env.pre {σ: env} {t₁ t₂: term}:
      vc.subst_env σ (vc.pre t₁ t₂) = vc.pre (term.subst_env σ t₁) (term.subst_env σ t₂) :=
begin
  induction σ with σ' x v ih,

  show (vc.subst_env env.empty (vc.pre t₁ t₂)
      = vc.pre (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)),
  by calc
        vc.subst_env env.empty (vc.pre t₁ t₂)
      = (vc.pre t₁ t₂) : by unfold vc.subst_env
  ... = (vc.pre (term.subst_env env.empty t₁) t₂) : by unfold term.subst_env
  ... = (vc.pre (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)) : by unfold term.subst_env,

  show (vc.subst_env (σ'[x↦v]) (vc.pre t₁ t₂)
      = vc.pre (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂)),
  by calc
        vc.subst_env (σ'[x↦v]) (vc.pre t₁ t₂)
      = vc.subst x v (vc.subst_env σ' (vc.pre t₁ t₂)) : by unfold vc.subst_env
  ... = vc.subst x v (vc.pre (term.subst_env σ' t₁) (term.subst_env σ' t₂)) : by rw[ih]
  ... = vc.pre (term.subst x v (term.subst_env σ' t₁)) (term.subst x v (term.subst_env σ' t₂)) : by unfold vc.subst
  ... = vc.pre (term.subst_env (σ'[x↦v]) t₁) (term.subst x v (term.subst_env σ' t₂)) : by unfold term.subst_env
  ... = vc.pre (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂) : by unfold term.subst_env
end

lemma vc.subst_env.post {σ: env} {t₁ t₂: term}:
      vc.subst_env σ (vc.post t₁ t₂) = vc.post (term.subst_env σ t₁) (term.subst_env σ t₂) :=
begin
  induction σ with σ' x v ih,

  show (vc.subst_env env.empty (vc.post t₁ t₂)
      = vc.post (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)),
  by calc
        vc.subst_env env.empty (vc.post t₁ t₂)
      = (vc.post t₁ t₂) : by unfold vc.subst_env
  ... = (vc.post (term.subst_env env.empty t₁) t₂) : by unfold term.subst_env
  ... = (vc.post (term.subst_env env.empty t₁) (term.subst_env env.empty t₂)) : by unfold term.subst_env,

  show (vc.subst_env (σ'[x↦v]) (vc.post t₁ t₂)
      = vc.post (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂)),
  by calc
        vc.subst_env (σ'[x↦v]) (vc.post t₁ t₂)
      = vc.subst x v (vc.subst_env σ' (vc.post t₁ t₂)) : by unfold vc.subst_env
  ... = vc.subst x v (vc.post (term.subst_env σ' t₁) (term.subst_env σ' t₂)) : by rw[ih]
  ... = vc.post (term.subst x v (term.subst_env σ' t₁)) (term.subst x v (term.subst_env σ' t₂)) : by unfold vc.subst
  ... = vc.post (term.subst_env (σ'[x↦v]) t₁) (term.subst x v (term.subst_env σ' t₂)) : by unfold term.subst_env
  ... = vc.post (term.subst_env (σ'[x↦v]) t₁) (term.subst_env (σ'[x↦v]) t₂) : by unfold term.subst_env
end

lemma vc.subst_env.univ_not_in {σ: env} {x: var} {P: vc}:
      (x ∉ σ) → (vc.subst_env σ (vc.univ x P) = vc.univ x (vc.subst_env σ P)) :=
begin
  assume x_not_in_σ,
  induction σ with σ' y v ih,

  show (vc.subst_env env.empty (vc.univ x P) = vc.univ x (vc.subst_env env.empty P)),
  by calc
        vc.subst_env env.empty (vc.univ x P) = (vc.univ x P) : by unfold vc.subst_env
                                         ... = vc.univ x (vc.subst_env env.empty P) : by unfold vc.subst_env,

  show (vc.subst_env (σ'[y↦v]) (vc.univ x P) = vc.univ x (vc.subst_env (σ'[y↦v]) P)), from (
    have ¬ (x = y ∨ x ∈ σ'), from env.contains.same.inv x_not_in_σ,
    have x_neq_y: x ≠ y, from (not_or_distrib.mp this).left,
    have x ∉ σ', from (not_or_distrib.mp this).right,
    have h: vc.subst_env σ' (vc.univ x P) = vc.univ x (vc.subst_env σ' P), from ih this,

    calc
        vc.subst_env (σ'[y↦v]) (vc.univ x P)
           = vc.subst y v (vc.subst_env σ' (vc.univ x P)) : by unfold vc.subst_env
       ... = vc.subst y v (vc.univ x (vc.subst_env σ' P)) : by rw[h]
       ... = vc.univ x (if y = x then vc.subst_env σ' P else (vc.subst_env σ' P).subst y v) : by unfold vc.subst
       ... = vc.univ x ((vc.subst_env σ' P).subst y v) : by simp[x_neq_y.symm]
       ... = vc.univ x (vc.subst_env (σ'[y↦v]) P) : by unfold vc.subst_env
  )
end

lemma vc.subst_env.univ {σ: env} {x: var} {P: vc}:
      (vc.subst_env σ (vc.univ x P) = vc.univ x (vc.subst_env (σ.without x) P)) :=
begin
  induction σ with σ' y v ih,

  show (vc.subst_env env.empty (vc.univ x P) = vc.univ x (vc.subst_env (env.empty.without x) P)),
  by calc
        vc.subst_env env.empty (vc.univ x P) = (vc.univ x P) : by unfold vc.subst_env
                                         ... = vc.univ x (vc.subst_env env.empty P) : by unfold vc.subst_env,

  show (vc.subst_env (σ'[y↦v]) (vc.univ x P) = vc.univ x (vc.subst_env ((σ'[y↦v]).without x) P)), by begin
    unfold vc.subst_env,
    by_cases (y = x) with h1,
    rw[←h1],
    rw[←h1] at ih,
    unfold env.without,
    simp,
    have : y ∉ FV (vc.subst_env σ' (vc.univ y P)), from (
      assume : y ∈ FV (vc.subst_env σ' (vc.univ y P)),
      have y ∈ FV (vc.univ y P), from vc.free_of_free_subst_env this,
      show «false», from free_in_vc.univ.same.inv this
    ),
    have h2: (vc.subst y v (vc.subst_env σ' (vc.univ y P)) = vc.subst_env σ' (vc.univ y P)),
    from unchanged_of_subst_nonfree_vc this,
    rw[h2],
    from ih,

    unfold env.without,
    simp[h1],
    unfold vc.subst_env,
    have : (vc.subst y v (vc.univ x (vc.subst_env (env.without σ' x) P))
         = vc.univ x (vc.subst y v (vc.subst_env (env.without σ' x) P))),
    by { unfold vc.subst, simp[h1] },
    rw[←this],
    congr,
    from ih  
  end
end

lemma term.closed_subst.value {v: value} {σ: env}: closed_subst σ (term.value v) :=
  assume x: var,
  assume : x ∈ FV (term.value v),
  show x ∈ σ.dom, from absurd this free_in_term.value.inv

lemma prop.closed_subst.term {t: term} {σ: env}: closed_subst σ t → closed_subst σ (prop.term t) :=
  assume t_closed: closed_subst σ t,
  show closed_subst σ (prop.term t), from (
    assume x: var,
    assume : x ∈ FV (prop.term t),
    have free_in_term x t, from free_in_prop.term.inv this,
    show x ∈ σ.dom, from t_closed this
  )

lemma prop.closed_subst.and {P Q: prop} {σ: env}: closed_subst σ P → closed_subst σ Q → closed_subst σ (P ⋀ Q) :=
  assume P_closed: closed_subst σ P,
  assume Q_closed: closed_subst σ Q,
  show closed_subst σ (P ⋀ Q), from (
    assume x: var,
    assume : x ∈ FV (P ⋀ Q),
    or.elim (free_in_prop.and.inv this) (
      assume : x ∈ FV P,
      show x ∈ σ.dom, from P_closed this
    ) (
      assume : x ∈ FV Q,
      show x ∈ σ.dom, from Q_closed this
    )
  )

lemma prop.closed_subst.or {P Q: prop} {σ: env}: closed_subst σ P → closed_subst σ Q → closed_subst σ (P ⋁ Q) :=
  assume P_closed_subst: closed_subst σ P,
  assume Q_closed_subst: closed_subst σ Q,
  show closed_subst σ (P ⋁ Q), from (
    assume x: var,
    assume : x ∈ FV (P ⋁ Q),
    or.elim (free_in_prop.or.inv this) (
      assume : x ∈ FV P,
      show x ∈ σ.dom, from P_closed_subst this
    ) (
      assume : x ∈ FV Q,
      show x ∈ σ.dom, from Q_closed_subst this
    )
  )

lemma prop.closed_subst.not {P: prop} {σ: env}: closed_subst σ P → closed_subst σ P.not :=
  assume P_closed_subst: closed_subst σ P,
  show closed_subst σ P.not, from (
    assume x: var,
    assume : x ∈ FV P.not,
    have x ∈ FV P, from free_in_prop.not.inv this,
    show x ∈ σ.dom, from P_closed_subst this
  )

lemma prop.closed_subst.implies {P Q: prop} {σ: env}:
      closed_subst σ P → closed_subst σ Q → closed_subst σ (prop.implies P Q) :=
  assume P_closed_subst: closed_subst σ P,
  have P_not_closed_subst: closed_subst σ P.not, from prop.closed_subst.not P_closed_subst,
  assume Q_closed_subst: closed_subst σ Q,
  show closed_subst σ (P.not ⋁ Q), from prop.closed_subst.or P_not_closed_subst Q_closed_subst

lemma prop.closed_subst.and.inv {P Q: prop} {σ: env}: closed_subst σ (P ⋀ Q) → (closed_subst σ P ∧ closed_subst σ Q) :=
  assume P_and_Q_closed_subst: closed_subst σ (P ⋀ Q),
  have P_closed_subst: closed_subst σ P, from (
    assume x: var,
    assume : x ∈ FV P,
    have x ∈ FV (P ⋀ Q), from free_in_prop.and₁ this,
    show x ∈ σ.dom, from P_and_Q_closed_subst this
  ),
  have Q_closed_subst: closed_subst σ Q, from (
    assume x: var,
    assume : x ∈ FV Q,
    have x ∈ FV (P ⋀ Q), from free_in_prop.and₂ this,
    show x ∈ σ.dom, from P_and_Q_closed_subst this
  ),
  ⟨P_closed_subst, Q_closed_subst⟩

lemma prop.closed_subst.or.inv {P Q: prop} {σ: env}: closed_subst σ (P ⋁ Q) → (closed_subst σ P ∧ closed_subst σ Q) :=
  assume P_or_Q_closed_subst: closed_subst σ (P ⋁ Q),
  have P_closed_subst: closed_subst σ P, from (
    assume x: var,
    assume : x ∈ FV P,
    have x ∈ FV (P ⋁ Q), from free_in_prop.or₁ this,
    show x ∈ σ.dom, from P_or_Q_closed_subst this
  ),
  have Q_closed_subst: closed_subst σ Q, from (
    assume x: var,
    assume : x ∈ FV Q,
    have x ∈ FV (P ⋁ Q), from free_in_prop.or₂ this,
    show x ∈ σ.dom, from P_or_Q_closed_subst this
  ),
  ⟨P_closed_subst, Q_closed_subst⟩

lemma prop.closed_subst.not.inv {P: prop} {σ: env}: closed_subst σ P.not → closed_subst σ P :=
  assume P_not_closed_subst: closed_subst σ P.not,
  show closed_subst σ P, from (
    assume x: var,
    assume : x ∈ FV P,
    have x ∈ FV P.not, from free_in_prop.not this,
    show x ∈ σ.dom, from P_not_closed_subst this
  )

lemma prop.closed_subst.implies.inv {P Q: prop} {σ: env}:
      closed_subst σ (prop.implies P Q) → closed_subst σ P ∧ closed_subst σ Q :=
  assume P_not_or_Q_closed_subst: closed_subst σ (P.not ⋁ Q),
  have P_not_closed_subst: closed_subst σ P.not, from (prop.closed_subst.or.inv P_not_or_Q_closed_subst).left,
  have P_closed_subst: closed_subst σ P, from prop.closed_subst.not.inv P_not_closed_subst,
  have Q_closed_subst: closed_subst σ Q, from (prop.closed_subst.or.inv P_not_or_Q_closed_subst).right,
  ⟨P_closed_subst, Q_closed_subst⟩

lemma prop.closed_subst.subst {P: prop} {σ: env} {x: var} {v: value}:
      closed_subst σ P → closed_subst σ (prop.subst x v P) :=
  assume P_closed_subst: closed_subst σ P,
  show closed_subst σ (prop.subst x v P), from (
    assume y: var,
    assume : y ∈ FV (prop.subst x v P),
    have y ∈ FV P, from (free_of_subst_prop this).right,
    show y ∈ σ.dom, from P_closed_subst this
  )

lemma vc.closed_subst.term {t: term} {σ: env}: closed_subst σ t → closed_subst σ (vc.term t) :=
  assume t_closed: closed_subst σ t,
  show closed_subst σ (vc.term t), from (
    assume x: var,
    assume : x ∈ FV (vc.term t),
    have free_in_term x t, from free_in_vc.term.inv this,
    show x ∈ σ.dom, from t_closed this
  )

lemma vc.closed_subst.and {P Q: vc} {σ: env}: closed_subst σ P → closed_subst σ Q → closed_subst σ (P ⋀ Q) :=
  assume P_closed_subst: closed_subst σ P,
  assume Q_closed_subst: closed_subst σ Q,
  show closed_subst σ (P ⋀ Q), from (
    assume x: var,
    assume : x ∈ FV (P ⋀ Q),
    or.elim (free_in_vc.and.inv this) (
      assume : x ∈ FV P,
      show x ∈ σ.dom, from P_closed_subst this
    ) (
      assume : x ∈ FV Q,
      show x ∈ σ.dom, from Q_closed_subst this
    )
  )

lemma vc.closed_subst.or {P Q: vc} {σ: env}: closed_subst σ P → closed_subst σ Q → closed_subst σ (P ⋁ Q) :=
  assume P_closed_subst: closed_subst σ P,
  assume Q_closed_subst: closed_subst σ Q,
  show closed_subst σ (P ⋁ Q), from (
    assume x: var,
    assume : x ∈ FV (P ⋁ Q),
    or.elim (free_in_vc.or.inv this) (
      assume : x ∈ FV P,
      show x ∈ σ.dom, from P_closed_subst this
    ) (
      assume : x ∈ FV Q,
      show x ∈ σ.dom, from Q_closed_subst this
    )
  )

lemma vc.closed_subst.not {P: vc} {σ: env}: closed_subst σ P → closed_subst σ P.not :=
  assume P_closed_subst: closed_subst σ P,
  show closed_subst σ P.not, from (
    assume x: var,
    assume : x ∈ FV P.not,
    have x ∈ FV P, from free_in_vc.not.inv this,
    show x ∈ σ.dom, from P_closed_subst this
  )

lemma vc.closed_subst.implies {P Q: vc} {σ: env}:
      closed_subst σ P → closed_subst σ Q → closed_subst σ (vc.implies P Q) :=
  assume P_closed_subst: closed_subst σ P,
  have P_not_closed_subst: closed_subst σ P.not, from vc.closed_subst.not P_closed_subst,
  assume Q_closed_subst: closed_subst σ Q,
  show closed_subst σ (P.not ⋁ Q), from vc.closed_subst.or P_not_closed_subst Q_closed_subst

lemma vc.closed_subst.term.inv {t: term} {σ: env}: closed_subst σ (vc.term t) → closed_subst σ t :=
  assume t_closed: closed_subst σ (vc.term t),
  show closed_subst σ t, from (
    assume x: var,
    assume : x ∈ FV t,
    have free_in_vc x (vc.term t), from free_in_vc.term this,
    show x ∈ σ.dom, from t_closed this
  )

lemma vc.closed_subst.and.inv {P Q: vc} {σ: env}: closed_subst σ (P ⋀ Q) → (closed_subst σ P ∧ closed_subst σ Q) :=
  assume P_and_Q_closed_subst: closed_subst σ (P ⋀ Q),
  have P_closed_subst: closed_subst σ P, from (
    assume x: var,
    assume : x ∈ FV P,
    have x ∈ FV (P ⋀ Q), from free_in_vc.and₁ this,
    show x ∈ σ.dom, from P_and_Q_closed_subst this
  ),
  have Q_closed_subst: closed_subst σ Q, from (
    assume x: var,
    assume : x ∈ FV Q,
    have x ∈ FV (P ⋀ Q), from free_in_vc.and₂ this,
    show x ∈ σ.dom, from P_and_Q_closed_subst this
  ),
  ⟨P_closed_subst, Q_closed_subst⟩

lemma vc.closed_subst.or.inv {P Q: vc} {σ: env}: closed_subst σ (P ⋁ Q) → (closed_subst σ P ∧ closed_subst σ Q) :=
  assume P_or_Q_closed_subst: closed_subst σ (P ⋁ Q),
  have P_closed_subst: closed_subst σ P, from (
    assume x: var,
    assume : x ∈ FV P,
    have x ∈ FV (P ⋁ Q), from free_in_vc.or₁ this,
    show x ∈ σ.dom, from P_or_Q_closed_subst this
  ),
  have Q_closed_subst: closed_subst σ Q, from (
    assume x: var,
    assume : x ∈ FV Q,
    have x ∈ FV (P ⋁ Q), from free_in_vc.or₂ this,
    show x ∈ σ.dom, from P_or_Q_closed_subst this
  ),
  ⟨P_closed_subst, Q_closed_subst⟩

lemma vc.closed_subst.not.inv {P: vc} {σ: env}: closed_subst σ P.not → closed_subst σ P :=
  assume P_not_closed_subst: closed_subst σ P.not,
  show closed_subst σ P, from (
    assume x: var,
    assume : x ∈ FV P,
    have x ∈ FV P.not, from free_in_vc.not this,
    show x ∈ σ.dom, from P_not_closed_subst this
  )

lemma vc.closed_subst.implies.inv {P Q: vc} {σ: env}:
      closed_subst σ (vc.implies P Q) → closed_subst σ P ∧ closed_subst σ Q :=
  assume P_not_or_Q_closed_subst: closed_subst σ (P.not ⋁ Q),
  have P_not_closed_subst: closed_subst σ P.not, from (vc.closed_subst.or.inv P_not_or_Q_closed_subst).left,
  have P_closed_subst: closed_subst σ P, from vc.closed_subst.not.inv P_not_closed_subst,
  have Q_closed_subst: closed_subst σ Q, from (vc.closed_subst.or.inv P_not_or_Q_closed_subst).right,
  ⟨P_closed_subst, Q_closed_subst⟩

lemma to_vc_closed_from_prop_closed {P: prop} {σ: env}: closed_subst σ P → closed_subst σ P.to_vc :=
  assume h1: closed_subst σ P,
  show closed_subst σ P.to_vc, from (
    assume x: var,
    assume : x ∈ FV P.to_vc,
    have x ∈ FV P, from set.mem_of_mem_of_subset this free_in_prop_of_free_in_to_vc,
    show x ∈ σ.dom, from h1 this
  )

lemma erased_p_closed_from_prop_closed {P: prop} {σ: env}: closed_subst σ P → closed_subst σ P.erased_p :=
  assume h1: closed_subst σ P,
  show closed_subst σ P.erased_p, from (
    assume x: var,
    assume : x ∈ FV P.erased_p,
    have x ∈ FV P, from set.mem_of_mem_of_subset this free_in_prop_of_free_in_erased.left,
    show x ∈ σ.dom, from h1 this
  )

lemma erased_n_closed_from_prop_closed {P: prop} {σ: env}: closed_subst σ P → closed_subst σ P.erased_n :=
  assume h1: closed_subst σ P,
  show closed_subst σ P.erased_n, from (
    assume x: var,
    assume : x ∈ FV P.erased_n,
    have x ∈ FV P, from set.mem_of_mem_of_subset this free_in_prop_of_free_in_erased.right,
    show x ∈ σ.dom, from h1 this
  )

lemma subst_closed_of_forall_closed {P: prop} {σ: env} {x: var} {v: value}:
      closed_subst σ (prop.forallc x P) → closed_subst σ (prop.subst x v P) :=
  assume h1: closed_subst σ (prop.forallc x P),
  show closed_subst σ (prop.subst x v P), from (
    assume y: var,
    assume : y ∈ FV (prop.subst x v P),
    have y ≠ x ∧ y ∈ FV P, from free_of_subst_prop this,
    have y ∈ FV (prop.forallc x P), from free_in_prop.forallc this.left this.right,
    show y ∈ σ, from h1 this
  )

lemma contains_of_free_in_nonempty_env {σ: env} {x y: var} {v: value}: (x ≠ y → y ∈ σ) → y ∈ (σ[x↦v]) :=
  assume ih: x ≠ y → y ∈ σ,
  if x_eq_y: x = y ∧ option.is_none (σ.apply y) then (
    have h: σ[x↦v].apply x = (if x = x ∧ option.is_none (σ.apply x) then ↑v else σ.apply x), by unfold env.apply,
    have (if x = x ∧ option.is_none (σ.apply x) then ↑v else σ.apply x) = ↑v, by simp [x_eq_y],
    have σ[x↦v].apply x = ↑v, from eq.trans h this,
    have σ[x↦v].apply y = some v, from x_eq_y.left ▸ this,
    have ∃v', σ[x↦v] y = some v', from exists.intro v this,
    show y ∈ (σ[x↦v]), from env.contains_apply_equiv.right.mp this
  ) else (
    have y ∈ σ, from (
      have ¬(x = y) ∨ ¬(option.is_none (σ.apply y)), from not_and_distrib.mp x_eq_y,
      this.elim (
        assume : x ≠ y,
        show y ∈ σ, from ih this        
      ) ( 
        assume : ¬(option.is_none (env.apply σ y)),
        have ¬(option.is_none (σ y)), from this,
        have option.is_some (σ y), from option.some_iff_not_none.mpr this,
        have ∃v', σ y = some v', from option.is_some_iff_exists.mp this,
        show y ∈ σ, from env.contains_apply_equiv.right.mp this
      )
    ),
    let ⟨v', σ_has_y⟩ := (env.contains_apply_equiv.right.mpr this) in
    have h: σ[x↦v].apply y = (if x = y ∧ option.is_none (σ.apply y) then ↑v else σ.apply y), by unfold env.apply,
    have (if x = y ∧ option.is_none (σ.apply y) then ↑v else σ.apply y) = σ.apply y, by simp *,
    have σ[x↦v].apply y = σ.apply y, from this ▸ h,
    have σ[x↦v].apply y = some v', from eq.trans this σ_has_y,
    have ∃v', σ[x↦v] y = some v', from exists.intro v' this,
    show y ∈ (σ[x↦v]), from env.contains_apply_equiv.right.mp this
  )

lemma contains_of_free_eq_value {P: prop} {σ: env} {x y: var} {v: value}:
  x ∈ FV (P ⋀ (y ≡ v)) → (x ∈ FV P → x ∈ σ) → x ∈ (σ[y↦v]) :=
  assume x_free_in_P: x ∈ FV (P ⋀ (y ≡ v)),
  assume ih : x ∈ FV P → x ∈ σ,
  contains_of_free_in_nonempty_env (
    assume x'_is_not_x: y ≠ x,
    have free_in_prop x P ∨ free_in_prop x (y ≡ v), from free_in_prop.and.inv x_free_in_P,
    or.elim this (
      assume x_free_in_P: free_in_prop x P,
      show x ∈ σ, from ih x_free_in_P
    ) (
      assume x_free_in_eq_v: free_in_prop x (y ≡ v),
      show x ∈ σ, by begin
        cases x_free_in_eq_v,
        case free_in_prop.term x_free_in_eq {
          cases x_free_in_eq,
          case free_in_term.binop₁ free_in_y {
            have y_is_x: (y = x), from (free_in_term.var.inv free_in_y).symm,
            contradiction
          },
          case free_in_term.binop₂ free_in_v {
            cases free_in_v
          }
        }
      end
    )
  )

lemma env.dom.inv {σ: env} {x: var} {v: value}: (σ[x↦v]).dom = (σ.dom ∪ set.insert x ∅) :=
  set.eq_of_subset_of_subset (
    assume y: var,
    assume : y ∈ (σ[x↦v]).dom,
    have y ∈ (σ[x↦v]), from this,
    or.elim (env.contains.inv this) (
      assume : y = x,
      have y ∈ set.insert x ∅, from set.mem_singleton_of_eq this,
      show y ∈ (σ.dom ∪ set.insert x ∅), from set.mem_union_right σ.dom this
    ) (
      assume : y ∈ σ,
      have y ∈ σ.dom, from this,
      show y ∈ (σ.dom ∪ set.insert x ∅), from set.mem_union_left (set.insert x ∅) this
    )
  ) (
    assume y: var,
    assume : y ∈ (σ.dom ∪ set.insert x ∅),
    or.elim (set.mem_or_mem_of_mem_union this) (
      assume : y ∈ σ.dom,
      have y ∈ σ, from this,
      have y ∈ (σ[x↦v]), from env.contains.rest this,
      show y ∈ (σ[x↦v]).dom, from this
    ) (
      assume : y ∈ set.insert x ∅,
      have y = x, from (set.mem_singleton_iff y x).mp this,
      have y ∈ (σ[x↦v]), from this ▸ env.contains.same,
      show y ∈ (σ[x↦v]).dom, from this
    )
  )

lemma env.dom.two_elems {σ: env} {x y: var} {v₁ v₂: value}: (σ[x↦v₁][y↦v₂]).dom = σ.dom ∪ {x, y} :=
  by calc (σ[x↦v₁][y↦v₂]).dom = (σ[x↦v₁]).dom ∪ set.insert y ∅ : env.dom.inv
                           ... = σ.dom ∪ set.insert x ∅ ∪ set.insert y ∅ : by rw[env.dom.inv]
                           ... = σ.dom ∪ (set.insert x ∅ ∪ set.insert y ∅) : by rw[set.union_assoc]
                           ... = σ.dom ∪ {x, y} : by rw[set.two_elems_of_insert]

lemma env.apply_of_contains {σ: env} {x: var} {v: value}: x ∉ σ → ((σ[x↦v]) x = v) :=
  begin
    intro h,
    change (env.apply (σ[x↦v]) x = some v),
    unfold env.apply,
    by_cases (x = x ∧ (option.is_none (env.apply σ x))) with h2,
    simp[h2],
    refl,
    simp at h2,
    have h3, from env.contains_apply_equiv.left.mpr h,
    have h4: (env.apply σ x = none), from h3,
    rw[h4] at h2,
    unfold option.is_none at h2,
    have h5: (↑tt = «false»), from eq_false_intro h2,
    have h6: (↑tt = «true»), by simp,
    have h7: («false» = «true»), from eq.trans h5.symm h6,
    have h8: «true», from trivial,
    have r9: «false», from h7.symm ▸ h8,
    contradiction
  end

lemma env.equiv_of_rest_and_same {σ σ': env} {x: var} {v: value}:
      (∀y, y ∈ σ → (σ y = σ' y)) → x ∉ σ → (σ' x = v) → (∀y, y ∈ (σ[x↦v]) → ((σ[x↦v]) y = σ' y)) :=
  assume h1: (∀y, y ∈ σ → (σ y = σ' y)),
  assume h2: x ∉ σ,
  assume h3: σ' x = v,
  assume y: var,
  assume h4: y ∈ (σ[x↦v]),
  if h: x = y then (
    have h5: (σ[x↦v]) y = v, from h ▸ env.apply_of_contains h2,
    show ((σ[x↦v]) y = σ' y), from eq.trans h5 (h ▸ h3.symm)
  ) else (
    have y ∈ σ, from (
      have y = x ∨ y ∈ σ, from env.contains.inv h4,
      or.elim this.symm id (
        assume : y = x,
        show y ∈ σ, from absurd this.symm h
      )
    ),
    have h6: σ y = σ' y, from h1 y this,
    have env.apply (σ[x↦v]) y = σ.apply y, by { unfold env.apply, simp[h] },
    have (σ[x↦v]) y = σ y, from this,
    show ((σ[x↦v]) y = σ' y), from this.symm ▸ h6
  )

lemma env.equiv_of_not_contains {σ σ': env} {x: var} {v: value}:
      (∀y, y ∈ σ → (σ y = σ' y)) → x ∉ σ → (∀y, y ∈ σ → (σ y = (σ'[x↦v]) y)) :=
  assume h1: (∀y, y ∈ σ → (σ y = σ' y)),
  assume h2: x ∉ σ,
  assume y: var,
  assume h4: y ∈ σ,
  if h: x = y then (
    have x ∈ σ, from h.symm ▸ h4,
    show σ y = (σ'[x↦v]) y, from absurd this h2
  ) else (
    have h2: σ y = σ' y, from h1 y h4,
    have (∃v, σ y = some v), from env.contains_apply_equiv.right.mpr h4,
    have option.is_some (σ y), from option.is_some_iff_exists.mpr this,
    have ¬ option.is_none (σ y), from option.some_iff_not_none.mp this,
    have h5: ¬ (x = y ∧ option.is_none (env.apply σ' y)), from not_and_distrib.mpr (or.inl h),
    have env.apply (σ'[x↦v]) y = σ' y, by { unfold env.apply, simp[h5], refl },
    show σ y = (σ'[x↦v]) y, from eq.trans h2 this.symm
  )

lemma env.apply_of_rest_apply {σ: env} {x y: var} {vx vy: value}:
      (σ x = vx) → ((σ[y↦vy]) x = vx) :=
  begin
    assume h1: (env.apply σ x = some vx),
    change (env.apply (σ[y↦vy]) x = ↑vx),
    unfold env.apply,
    have h2, from option.is_some_iff_exists.mpr (exists.intro vx h1),
    have h3, from option.some_iff_not_none.mp h2,
    have h4: ¬ (y = x ∧ (option.is_none (env.apply σ x))),
    from not_and_distrib.mpr (or.inr h3),
    simp[h4],
    from h1
  end

lemma term.subst_env.order {t: term} {σ: env} {x: var} {v: value}:
      (x ∉ σ) ∨ (σ x = v) → (term.subst_env σ (term.subst x v t) = term.subst x v (term.subst_env σ t)) :=
  begin
    assume h1,
    induction t with v' y unop t₁ t₁_ih binop t₂ t₃ t₂_ih t₃_ih t₄ t₅ t₄_ih t₅_ih,
    
    show (term.subst_env σ (term.subst x v (term.value v')) = term.subst x v (term.subst_env σ (term.value v'))),
    by begin
      change (term.subst_env σ (term.subst x v (term.value v')) = term.subst x v (term.subst_env σ v')),
      rw[term.subst_env.value],
      unfold term.subst,
      rw[term.subst_env.value],
      change (↑v' = term.subst x v (term.value v')),
      unfold term.subst
    end,

    show (term.subst_env σ (term.subst x v (term.var y)) = term.subst x v (term.subst_env σ (term.var y))),
    by begin
      by_cases (x = y) with h,
      simp[h],
      rw[h] at h1,
      unfold term.subst,
      simp,
      cases h1,
      have : (σ y = none), from env.contains_apply_equiv.left.mpr a,
      have h2: (term.subst_env σ (term.var y) = y), from term.subst_env.var.left.mp this,
      simp[h2],
      rw[term.subst_env.value],
      change (↑v = term.subst y v (term.var y)),
      unfold term.subst,
      simp,

      have h2: (term.subst_env σ (term.var y) = v), from (term.subst_env.var.right v).mp a,
      rw[h2],
      change (term.subst_env σ ↑v = term.subst y v (term.value v)),
      unfold term.subst,
      rw[term.subst_env.value],

      have h2: (term.subst x v (term.var y) = y), from term.subst.var.diff h,
      rw[h2],
      by_cases (y ∈ σ) with h3,
      
      have h4, from env.contains_apply_equiv.right.mpr h3,
      cases h4 with v' h5,
      have h6: (term.subst_env σ y = v'), from (term.subst_env.var.right v').mp h5,
      rw[h6],
      change (↑v' = term.subst x v (term.subst_env σ ↑y)),
      rw[h6],
      change (↑v' = term.subst x v (term.value v')),
      unfold term.subst,

      have : (σ y = none), from env.contains_apply_equiv.left.mpr h3,
      have h4: (term.subst_env σ (term.var y) = y), from term.subst_env.var.left.mp this,
      simp[h4],
      change (term.subst_env σ (term.var y) = term.subst x v (term.var y)),
      rw[h2],
      rw[h4]
    end,

    show (term.subst_env σ (term.subst x v (term.unop unop t₁))
        = term.subst x v (term.subst_env σ (term.unop unop t₁))), by begin
      rw[term.subst_env.unop],
      unfold term.subst,
      rw[term.subst_env.unop],
      congr,
      from t₁_ih
    end,

    show (term.subst_env σ (term.subst x v (term.binop binop t₂ t₃))
        = term.subst x v (term.subst_env σ (term.binop binop t₂ t₃))), by begin
      rw[term.subst_env.binop],
      unfold term.subst,
      rw[term.subst_env.binop],
      congr,
      rw[t₂_ih],
      rw[t₃_ih]
    end,

    show (term.subst_env σ (term.subst x v (term.app t₄ t₅))
        = term.subst x v (term.subst_env σ (term.app t₄ t₅))), by begin
      rw[term.subst_env.app],
      unfold term.subst,
      rw[term.subst_env.app],
      congr,
      rw[t₄_ih],
      rw[t₅_ih]
    end
  end

lemma term.substt_env.order {t' t: term} {σ: env} {x: var}:
      closed t' → (x ∉ σ) → (term.subst_env σ (term.substt x t' t) = term.substt x t' (term.subst_env σ t)) :=
  begin
    assume t'_closed,
    assume h1,
    induction t with v y unop t₁ t₁_ih binop t₂ t₃ t₂_ih t₃_ih t₄ t₅ t₄_ih t₅_ih,
    
    show (term.subst_env σ (term.substt x t' (term.value v)) = term.substt x t' (term.subst_env σ (term.value v))),
    by begin
      change (term.subst_env σ (term.substt x t' (term.value v)) = term.substt x t' (term.subst_env σ v)),
      rw[term.subst_env.value],
      unfold term.substt,
      rw[term.subst_env.value],
      change (↑v = term.substt x t' (term.value v)),
      unfold term.substt
    end,

    show (term.subst_env σ (term.substt x t' (term.var y)) = term.substt x t' (term.subst_env σ (term.var y))),
    by begin
      by_cases (x = y) with h,
      simp[h],
      rw[h] at h1,
      unfold term.substt,
      simp,
      have : (σ y = none), from env.contains_apply_equiv.left.mpr h1,
      have h2: (term.subst_env σ (term.var y) = y), from term.subst_env.var.left.mp this,
      simp[h2],
      rw[term.subst_env.closed t'_closed],
      change (t' = term.substt y t' (term.var y)),
      unfold term.substt,
      simp,

      have h2: (term.substt x t' (term.var y) = y), from term.substt.var.diff h,
      rw[h2],
      by_cases (y ∈ σ) with h3,
      
      have h4, from env.contains_apply_equiv.right.mpr h3,
      cases h4 with v' h5,
      have h6: (term.subst_env σ y = v'), from (term.subst_env.var.right v').mp h5,
      rw[h6],
      change (↑v' = term.substt x t' (term.subst_env σ ↑y)),
      rw[h6],
      change (↑v' = term.substt x t' (term.value v')),
      unfold term.substt,

      have : (σ y = none), from env.contains_apply_equiv.left.mpr h3,
      have h4: (term.subst_env σ (term.var y) = y), from term.subst_env.var.left.mp this,
      simp[h4],
      change (term.subst_env σ (term.var y) = term.substt x t' (term.var y)),
      rw[h2],
      rw[h4]
    end,

    show (term.subst_env σ (term.substt x t' (term.unop unop t₁))
        = term.substt x t' (term.subst_env σ (term.unop unop t₁))), by begin
      rw[term.subst_env.unop],
      unfold term.substt,
      rw[term.subst_env.unop],
      congr,
      from t₁_ih
    end,

    show (term.subst_env σ (term.substt x t' (term.binop binop t₂ t₃))
        = term.substt x t' (term.subst_env σ (term.binop binop t₂ t₃))), by begin
      rw[term.subst_env.binop],
      unfold term.substt,
      rw[term.subst_env.binop],
      congr,
      rw[t₂_ih],
      rw[t₃_ih]
    end,

    show (term.subst_env σ (term.substt x t' (term.app t₄ t₅))
        = term.substt x t' (term.subst_env σ (term.app t₄ t₅))), by begin
      rw[term.subst_env.app],
      unfold term.substt,
      rw[term.subst_env.app],
      congr,
      rw[t₄_ih],
      rw[t₅_ih]
    end
  end

lemma term.subst_env_inner {t: term} {σ: env} {x: var} {v: value}:
      (σ x = some v) → (term.subst_env σ (term.subst x v t) = term.subst_env σ t) :=
  begin
    assume x_is_v,

    induction σ with σ₁ y v' ih,

    show (term.subst_env env.empty (term.subst x v t) = term.subst_env env.empty t), by cases x_is_v,

    show (term.subst_env (σ₁[y↦v']) (term.subst x v t) = term.subst_env (σ₁[y↦v']) t), by begin
      unfold term.subst_env,
      have h2: (env.apply (σ₁[y↦v']) x = some v), from x_is_v,
      unfold env.apply at h2,
      by_cases (y = x ∧ (option.is_none (env.apply σ₁ x))) with h3,
      simp[h3] at h2,
      have h4: (v' = v), from option.some.inj h2,
      simp[h3],
      have h5: (σ₁ x = none), from option.is_none.inv.mpr h3.right,
      have h6: x ∉ σ₁, from env.contains_apply_equiv.left.mp h5,
      rw[h4],
      have h7: x ∉ FV (term.subst x v t), from term.not_free_of_subst,
      have h8: x ∉ FV (term.subst_env σ₁ (term.subst x v t)),
      have : ¬(free_in_term x (term.subst x v t) ∧ x ∉ σ₁), by begin
        assume : free_in_term x (term.subst x v t) ∧ x ∉ σ₁,
        show «false», from h7 this.left
      end,
      from mt free_of_subst_env_term this,
      have h9: (term.subst x v (term.subst_env σ₁ (term.subst x v t)) = (term.subst_env σ₁ (term.subst x v t))),
      from unchanged_of_subst_nonfree_term h8,
      rw[h9],
      from term.subst_env.order (or.inl h6),

      simp[h3] at h2,
      have h4, from ih h2,
      congr,
      from h4
    end
  end

lemma term.subst_env_twice {t: term} {σ: env}:
  term.subst_env σ (term.subst_env σ t) = term.subst_env σ t :=
  begin
    induction σ with σ' x v ih,
    
    show (term.subst_env env.empty (term.subst_env env.empty t) = term.subst_env env.empty t), by begin
      unfold term.subst_env
    end,

    show (term.subst_env (σ'[x↦v]) (term.subst_env (σ'[x↦v]) t) = term.subst_env (σ'[x↦v]) t), by begin

      by_cases (x ∈ σ') with h1,
      unfold term.subst_env,

      have h2: x ∉ FV (term.subst_env σ' t), from term.not_free_of_subst_env h1,
      have h3: (term.subst x v (term.subst_env σ' t) = (term.subst_env σ' t)),
      from unchanged_of_subst_nonfree_term h2,
      rw[h3],
      have h4: x ∉ FV (term.subst_env σ' (term.subst_env σ' t)), from term.not_free_of_subst_env h1,
      have h5: (term.subst x v (term.subst_env σ' (term.subst_env σ' t)) = (term.subst_env σ' (term.subst_env σ' t))),
      from unchanged_of_subst_nonfree_term h4,
      rw[h5],
      from ih,

      have h6: (term.subst_env (σ'[x↦v]) t = term.subst x v (term.subst_env σ' t)),
      by unfold term.subst_env,
      rw[h6],

      have h7: (env.apply (σ'[x↦v]) x = v), from env.apply_of_contains h1,
      have h8: (term.subst_env (σ'[x↦v]) (term.subst x v (term.subst_env σ' t))
              = term.subst_env (σ'[x↦v]) (term.subst_env σ' t)),
      from term.subst_env_inner h7,
      rw[h8],
      unfold term.subst_env,
      congr,
      from ih
    end
  end

lemma env.dom_subset_of_equivalent_env {σ₁ σ₂: env}:
  (∀z, z ∈ σ₁ → (σ₁ z = σ₂ z)) → (σ₁.dom ⊆ σ₂.dom) :=
  assume env_equiv: (∀z, z ∈ σ₁ → (σ₁ z = σ₂ z)),
  assume x: var,
  assume : x ∈ σ₁.dom,
  have h1: x ∈ σ₁, from this,
  have ∃v, σ₁ x = some v, from env.contains_apply_equiv.right.mpr h1,
  let ⟨v, h2⟩ := this in
  have σ₁ x = σ₂ x, from env_equiv x h1,
  have σ₂ x = some v, from eq.trans this.symm h2,
  show x ∈ σ₂, from env.contains_apply_equiv.right.mp (exists.intro v this)

lemma env.empty_of_dom_empty {σ: env}: (σ.dom = ∅) → (σ = env.empty) :=
  begin
    assume h1: (σ.dom = ∅),
    cases σ with σ' x v,
    refl,
    have h2, from set.subset_of_eq h1,
    have h3: x ∈ (σ'[x↦v]), from env.contains.same,
    have h4: x ∈ (σ'[x↦v]).dom, from h3,
    have h5, from set.mem_of_subset_of_mem h2 h4,
    have : x ∉ ∅, from set.not_mem_empty x,
    contradiction
  end

lemma env.empty_dom_is_empty: (env.empty.dom = ∅) :=
  begin
    apply set.eq_of_subset_of_subset,
    assume x: var,
    assume : x ∈ env.dom env.empty,
    have h2: x ∈ env.empty, from this,
    cases h2,

    assume x: var,
    assume : x ∈ ∅,
    have : x ∉ ∅, from set.not_mem_empty x,
    contradiction
  end

lemma term.subst_env_twice_equiv {t: term} {σ₁ σ₂: env}:
  (∀z, z ∈ σ₁ → (σ₁ z = σ₂ z)) → (term.subst_env σ₁ (term.subst_env σ₂ t) = term.subst_env σ₂ t) :=
  begin
    assume env_equiv: ∀z, z ∈ σ₁ → (σ₁ z = σ₂ z),
    -- have env_subst: σ₁.dom ⊆ σ₂.dom, from env.dom_subset_of_equivalent_env env_equiv,

    induction σ₁ with σ' x v ih,
    
    show (term.subst_env env.empty (term.subst_env σ₂ t) = term.subst_env σ₂ t),
    by unfold term.subst_env,

    show (term.subst_env (σ'[x↦v]) (term.subst_env σ₂ t) = term.subst_env σ₂ t), by begin
      unfold term.subst_env,
      have h1: (∀ (z : var), z ∈ σ' → (σ' z = σ₂ z)), by begin
        assume z: var,
        assume h2: z ∈ σ',
        have h3: (env.apply (σ'[x↦v]) z = σ₂ z), from env_equiv z (env.contains.rest h2),
        unfold env.apply at h3,
        have h4, from env.contains_apply_equiv.right.mpr h2,
        have h5, from option.is_some_iff_exists.mpr h4,
        have h6, from option.some_iff_not_none.mp h5,
        have h7, from not_and_of_not_right (x = z) h6,
        have h8: (ite (x = z ∧ (option.is_none (env.apply σ' z))) ↑v (env.apply σ' z) = (env.apply σ' z)),
        from ite.if_false h7,
        rw[h8] at h3,
        from h3
      end,

      have h2: (term.subst_env σ' (term.subst_env σ₂ t) = term.subst_env σ₂ t), from ih h1,
      rw[h2],
      have h3: x ∈ σ₂, by begin
        have h3: (env.apply (σ'[x↦v]) x = σ₂ x), from env_equiv x env.contains.same,
        unfold env.apply at h3,
        by_cases (x ∈ σ') with h4,

        have h5, from env.contains_apply_equiv.right.mpr h4,
        have h6, from option.is_some_iff_exists.mpr h5,
        have h7, from option.some_iff_not_none.mp h6,
        have h8, from not_and_of_not_right (x = x) h7,
        have h9: (ite (x = x ∧ (option.is_none (env.apply σ' x))) ↑v (env.apply σ' x) = (env.apply σ' x)),
        from ite.if_false h8,
        rw[h9] at h3,
        have h10: (σ' x = σ₂ x), from h3,
        rw[h10] at h5,
        from env.contains_apply_equiv.right.mp h5,

        have h5, from env.contains_apply_equiv.left.mpr h4,
        have h6, from option.is_none.inv.mp h5,
        have h7: (ite (x = x ∧ (option.is_none (env.apply σ' x))) ↑v (env.apply σ' x) = v),
        from ite.if_true ⟨rfl, h6⟩,
        rw[h7] at h3,
        from env.contains_apply_equiv.right.mp (exists.intro v h3.symm)
      end,

      have : x ∉ FV (term.subst_env σ₂ t), from term.not_free_of_subst_env h3,
      from unchanged_of_subst_nonfree_term this
    end
  end

lemma term.substte_env.order {t' t: term} {σ₁ σ₂: env} {x: var}:
      (∀z, z ∈ σ₁ → (σ₁ z = σ₂ z)) → (x ∉ σ₁) →
      (term.subst_env σ₁ (term.substt x (term.subst_env σ₂ t') t)
     = term.substt x (term.subst_env σ₂ t') (term.subst_env σ₁ t)) :=
  begin
    assume env_equiv,
    assume h1,
    induction t with v y unop t₁ t₁_ih binop t₂ t₃ t₂_ih t₃_ih t₄ t₅ t₄_ih t₅_ih,
    
    show (term.subst_env σ₁ (term.substt x (term.subst_env σ₂ t') (term.value v))
        = term.substt x (term.subst_env σ₂ t') (term.subst_env σ₁ (term.value v))),
    by begin
      change (term.subst_env σ₁ (term.substt x (term.subst_env σ₂ t') (term.value v)) =
              term.substt x (term.subst_env σ₂ t') (term.subst_env σ₁ v)),
      rw[term.subst_env.value],
      unfold term.substt,
      rw[term.subst_env.value],
      change (↑v = term.substt x (term.subst_env σ₂ t') (term.value v)),
      unfold term.substt
    end,

    show (term.subst_env σ₁ (term.substt x (term.subst_env σ₂ t') (term.var y))
        = term.substt x (term.subst_env σ₂ t') (term.subst_env σ₁ (term.var y))),
    by begin
      by_cases (x = y) with h,
      simp[h],
      rw[h] at h1,
      unfold term.substt,
      simp,
      have : (σ₁ y = none), from env.contains_apply_equiv.left.mpr h1,
      have h2: (term.subst_env σ₁ (term.var y) = y), from term.subst_env.var.left.mp this,
      simp[h2],
      have h3: (term.subst_env σ₁ (term.subst_env σ₂ t') = (term.subst_env σ₂ t')),
      from term.subst_env_twice_equiv env_equiv,
      rw[h3],
      change (term.subst_env σ₂ t' = term.substt y (term.subst_env σ₂ t') (term.var y)),
      unfold term.substt,
      simp,

      unfold term.substt,
      simp[h],
      have h3: (term.subst_env σ₁ y = y ∨ ∃v: value, term.subst_env σ₁ y = v),
      from term.subst_env.var.inv,
      cases h3 with h4 h5,

      change (term.subst_env σ₁ y = term.substt x (term.subst_env σ₂ t') (term.subst_env σ₁ y)),
      rw[h4],
      change (↑y = term.substt x (term.subst_env σ₂ t') (term.var y)),
      unfold term.substt,
      simp[h],

      cases h5 with v' h6,
      change (term.subst_env σ₁ y = term.substt x (term.subst_env σ₂ t') (term.subst_env σ₁ y)),
      rw[h6],
      change (↑v' = term.substt x (term.subst_env σ₂ t') (term.value v')),
      unfold term.substt
    end,

    show (term.subst_env σ₁ (term.substt x (term.subst_env σ₂ t') (term.unop unop t₁))
        = term.substt x (term.subst_env σ₂ t') (term.subst_env σ₁ (term.unop unop t₁))), by begin
      rw[term.subst_env.unop],
      unfold term.substt,
      rw[term.subst_env.unop],
      congr,
      from t₁_ih
    end,

    show (term.subst_env σ₁ (term.substt x (term.subst_env σ₂ t') (term.binop binop t₂ t₃))
        = term.substt x (term.subst_env σ₂ t') (term.subst_env σ₁ (term.binop binop t₂ t₃))), by begin
      rw[term.subst_env.binop],
      unfold term.substt,
      rw[term.subst_env.binop],
      congr,
      rw[t₂_ih],
      rw[t₃_ih]
    end,

    show (term.subst_env σ₁ (term.substt x (term.subst_env σ₂ t') (term.app t₄ t₅))
        = term.substt x (term.subst_env σ₂ t') (term.subst_env σ₁ (term.app t₄ t₅))), by begin
      rw[term.subst_env.app],
      unfold term.substt,
      rw[term.subst_env.app],
      congr,
      rw[t₄_ih],
      rw[t₅_ih]
    end
  end

lemma vc.subst_env.order {P: vc}:
    ∀ {σ: env} {x: var} {v: value},
      (x ∉ σ) ∨ (σ x = v) → (vc.subst_env σ (vc.subst x v P) = vc.subst x v (vc.subst_env σ P)) :=
  begin
    induction P,
    case vc.term t {
      assume σ x v,
      assume h1,
      change (vc.subst_env σ (vc.subst x v (vc.term t)) = vc.subst x v (vc.subst_env σ ↑t)),
      rw[vc.subst_env.term],
      unfold vc.subst,
      rw[vc.subst_env.term],
      congr,
      from term.subst_env.order h1
    },
    case vc.not P₁ ih {
      assume σ x v,
      assume h1,
      rw[vc.subst_env.not],
      unfold vc.subst,
      rw[vc.subst_env.not],
      congr,
      from ih h1
    },
    case vc.and P₁ P₂ P₁_ih P₂_ih {
      assume σ x v,
      assume h1,
      change (vc.subst_env σ (vc.subst x v (vc.and P₁ P₂)) = vc.subst x v (vc.subst_env σ (P₁ ⋀ P₂))),
      rw[vc.subst_env.and],
      unfold vc.subst,
      rw[vc.subst_env.and],
      congr,
      from P₁_ih h1,
      from P₂_ih h1
    },
    case vc.or P₁ P₂ P₁_ih P₂_ih {
      assume σ x v,
      assume h1,
      change (vc.subst_env σ (vc.subst x v (vc.or P₁ P₂)) = vc.subst x v (vc.subst_env σ (P₁ ⋁ P₂))),
      rw[vc.subst_env.or],
      unfold vc.subst,
      rw[vc.subst_env.or],
      congr,
      from P₁_ih h1,
      from P₂_ih h1
    },
    case vc.pre t₁ t₂ {
      assume σ x v,
      assume h1,
      rw[vc.subst_env.pre],
      unfold vc.subst,
      rw[vc.subst_env.pre],
      congr,
      from term.subst_env.order h1,
      from term.subst_env.order h1
    },
    case vc.pre₁ op t {
      assume σ x v,
      assume h1,
      rw[vc.subst_env.pre₁],
      unfold vc.subst,
      rw[vc.subst_env.pre₁],
      congr,
      from term.subst_env.order h1
    },
    case vc.pre₂ op t₁ t₂ {
      assume σ x v,
      assume h1,
      rw[vc.subst_env.pre₂],
      unfold vc.subst,
      rw[vc.subst_env.pre₂],
      congr,
      from term.subst_env.order h1,
      from term.subst_env.order h1
    },
    case vc.post t₁ t₂ {
      assume σ x v,
      assume h1,
      rw[vc.subst_env.post],
      unfold vc.subst,
      rw[vc.subst_env.post],
      congr,
      from term.subst_env.order h1,
      from term.subst_env.order h1
    },
    case vc.univ z P' P'_ih {
      assume σ x v,
      assume h1,
      rw[vc.subst_env.univ],
      unfold vc.subst,
      by_cases (x = z) with h2,

      simp[h2],
      rw[vc.subst_env.univ],

      simp[h2],
      rw[vc.subst_env.univ],
      congr,

      have h2: (x ∉ σ.without z ∨ (σ.without z x = v)),
      from env.without_equiv h1,
      have h3: (vc.subst_env (σ.without z) (vc.subst x v P') = vc.subst x v (vc.subst_env (σ.without z) P')),
      from P'_ih h2,
      rw[h3]
    }
  end

lemma vc.substt_env.order {P: vc}:
    ∀ {σ: env} {x: var} {t: term},
      closed t → (x ∉ σ) → (vc.subst_env σ (vc.substt x t P) = vc.substt x t (vc.subst_env σ P)) :=
  begin
    induction P,
    case vc.term t' {
      assume σ x t,
      assume t_closed,
      assume h1,
      change (vc.subst_env σ (vc.substt x t (vc.term t')) = vc.substt x t (vc.subst_env σ t')),
      rw[vc.subst_env.term],
      unfold vc.substt,
      rw[vc.subst_env.term],
      congr,
      from term.substt_env.order t_closed h1
    },
    case vc.not P₁ ih {
      assume σ x t,
      assume t_closed,
      assume h1,
      rw[vc.subst_env.not],
      unfold vc.substt,
      rw[vc.subst_env.not],
      congr,
      from ih t_closed h1
    },
    case vc.and P₁ P₂ P₁_ih P₂_ih {
      assume σ x t,
      assume t_closed,
      assume h1,
      change (vc.subst_env σ (vc.substt x t (vc.and P₁ P₂)) = vc.substt x t (vc.subst_env σ (P₁ ⋀ P₂))),
      rw[vc.subst_env.and],
      unfold vc.substt,
      rw[vc.subst_env.and],
      congr,
      from P₁_ih t_closed h1,
      from P₂_ih t_closed h1
    },
    case vc.or P₁ P₂ P₁_ih P₂_ih {
      assume σ x t,
      assume t_closed,
      assume h1,
      change (vc.subst_env σ (vc.substt x t (vc.or P₁ P₂)) = vc.substt x t (vc.subst_env σ (P₁ ⋁ P₂))),
      rw[vc.subst_env.or],
      unfold vc.substt,
      rw[vc.subst_env.or],
      congr,
      from P₁_ih t_closed h1,
      from P₂_ih t_closed h1
    },
    case vc.pre t₁ t₂ {
      assume σ x t,
      assume t_closed,
      assume h1,
      rw[vc.subst_env.pre],
      unfold vc.substt,
      rw[vc.subst_env.pre],
      congr,
      from term.substt_env.order t_closed h1,
      from term.substt_env.order t_closed h1
    },
    case vc.pre₁ op t {
      assume σ x t,
      assume t_closed,
      assume h1,
      rw[vc.subst_env.pre₁],
      unfold vc.substt,
      rw[vc.subst_env.pre₁],
      congr,
      from term.substt_env.order t_closed h1
    },
    case vc.pre₂ op t₁ t₂ {
      assume σ x t,
      assume t_closed,
      assume h1,
      rw[vc.subst_env.pre₂],
      unfold vc.substt,
      rw[vc.subst_env.pre₂],
      congr,
      from term.substt_env.order t_closed h1,
      from term.substt_env.order t_closed h1
    },
    case vc.post t₁ t₂ {
      assume σ x t,
      assume t_closed,
      assume h1,
      rw[vc.subst_env.post],
      unfold vc.substt,
      rw[vc.subst_env.post],
      congr,
      from term.substt_env.order t_closed h1,
      from term.substt_env.order t_closed h1
    },
    case vc.univ z P' P'_ih {
      assume σ x t,
      assume t_closed,
      assume h1,
      rw[vc.subst_env.univ],
      unfold vc.substt,
      by_cases (x = z) with h2,

      simp[h2],
      rw[vc.subst_env.univ],

      simp[h2],
      rw[vc.subst_env.univ],
      congr,

      have h2: (x ∉ σ.without z),
      from env.not_in_without h1,
      have h3: (vc.subst_env (σ.without z) (vc.substt x t P') = vc.substt x t (vc.subst_env (σ.without z) P')),
      from P'_ih t_closed h2,
      rw[h3]
    }
  end

lemma vc.substte_env.order {P: vc} {x: var} {t: term}:
    ∀ {σ₁ σ₂: env},
      (∀z, z ∈ σ₁ → (σ₁ z = σ₂ z)) → (x ∉ σ₁) →
      (vc.subst_env σ₁ (vc.substte x t P σ₂) = vc.substte x t (vc.subst_env σ₁ P) σ₂) :=
  begin
    induction P,
    case vc.term t' {
      assume σ₁ σ₂,
      assume env_equiv,
      assume x_not_in_σ₁,
      change (vc.subst_env σ₁ (vc.substte x t (vc.term t') σ₂) = vc.substte x t (vc.subst_env σ₁ t') σ₂),
      rw[vc.subst_env.term],
      unfold vc.substte,
      rw[vc.subst_env.term],
      congr,
      from term.substte_env.order env_equiv x_not_in_σ₁
    },
    case vc.not P₁ ih {
      assume σ₁ σ₂,
      assume env_equiv,
      assume x_not_in_σ₁,
      rw[vc.subst_env.not],
      unfold vc.substte,
      rw[vc.subst_env.not],
      congr,
      from ih env_equiv x_not_in_σ₁
    },
    case vc.and P₁ P₂ P₁_ih P₂_ih {
      assume σ₁ σ₂,
      assume env_equiv,
      assume x_not_in_σ₁,
      change (vc.subst_env σ₁ (vc.substte x t (vc.and P₁ P₂) σ₂) = vc.substte x t (vc.subst_env σ₁ (P₁ ⋀ P₂)) σ₂),
      rw[vc.subst_env.and],
      unfold vc.substte,
      rw[vc.subst_env.and],
      congr,
      from P₁_ih env_equiv x_not_in_σ₁,
      from P₂_ih env_equiv x_not_in_σ₁
    },
    case vc.or P₁ P₂ P₁_ih P₂_ih {
      assume σ₁ σ₂,
      assume env_equiv,
      assume x_not_in_σ₁,
      change (vc.subst_env σ₁ (vc.substte x t (vc.or P₁ P₂) σ₂) = vc.substte x t (vc.subst_env σ₁ (P₁ ⋁ P₂)) σ₂),
      rw[vc.subst_env.or],
      unfold vc.substte,
      rw[vc.subst_env.or],
      congr,
      from P₁_ih env_equiv x_not_in_σ₁,
      from P₂_ih env_equiv x_not_in_σ₁
    },
    case vc.pre t₁ t₂ {
      assume σ₁ σ₂,
      assume env_equiv,
      assume x_not_in_σ₁,
      rw[vc.subst_env.pre],
      unfold vc.substte,
      rw[vc.subst_env.pre],
      congr,
      from term.substte_env.order env_equiv x_not_in_σ₁,
      from term.substte_env.order env_equiv x_not_in_σ₁
    },
    case vc.pre₁ op t {
      assume σ₁ σ₂,
      assume env_equiv,
      assume x_not_in_σ₁,
      rw[vc.subst_env.pre₁],
      unfold vc.substte,
      rw[vc.subst_env.pre₁],
      congr,
      from term.substte_env.order env_equiv x_not_in_σ₁
    },
    case vc.pre₂ op t₁ t₂ {
      assume σ₁ σ₂,
      assume env_equiv,
      assume x_not_in_σ₁,
      rw[vc.subst_env.pre₂],
      unfold vc.substte,
      rw[vc.subst_env.pre₂],
      congr,
      from term.substte_env.order env_equiv x_not_in_σ₁,
      from term.substte_env.order env_equiv x_not_in_σ₁
    },
    case vc.post t₁ t₂ {
      assume σ₁ σ₂,
      assume env_equiv,
      assume x_not_in_σ₁,
      rw[vc.subst_env.post],
      unfold vc.substte,
      rw[vc.subst_env.post],
      congr,
      from term.substte_env.order env_equiv x_not_in_σ₁,
      from term.substte_env.order env_equiv x_not_in_σ₁
    },
    case vc.univ y P' P'_ih {
      assume σ₁ σ₂,
      assume env_equiv,
      assume x_not_in_σ₁,
      rw[vc.subst_env.univ],
      unfold vc.substte,
      by_cases (x = y) with h2,

      simp[h2],
      rw[vc.subst_env.univ],

      simp[h2],
      rw[vc.subst_env.univ],
      congr,


      have h3: (∀ (z : var), z ∈ σ₁.without y → ((σ₁.without y) z = (σ₂.without y) z)), by begin
        assume z: var,
        assume h4: z ∈ σ₁.without y,
        have h5, from env.contains_without.inv h4,
        have h6: (σ₁ z = σ₂ z), from env_equiv z h5.right,
        have h7, from env.contains_apply_equiv.right.mpr h5.right,
        rw[h6] at h7,
        have h8, from env.contains_apply_equiv.right.mp h7,
        have h9, from env.contains_without.rinv ⟨h8, h5.left⟩,
        have h10, from env.without_equiv_with z h4,
        have h11, from env.without_equiv_with z h9,
        from eq.trans h10 (eq.trans h6 h11.symm)
      end,
      have h4: (x ∉ σ₁.without y), from env.not_in_without x_not_in_σ₁,
      from P'_ih h3 h4
    }
  end

lemma vc.subst_env_inner {P: vc} {σ: env} {x: var} {v: value}:
      (σ x = some v) → (vc.subst_env σ (vc.subst x v P) = vc.subst_env σ P) :=
  begin
    assume x_is_v,

    induction σ with σ₁ y v' ih,

    show (vc.subst_env env.empty (vc.subst x v P) = vc.subst_env env.empty P), by cases x_is_v,

    show (vc.subst_env (σ₁[y↦v']) (vc.subst x v P) = vc.subst_env (σ₁[y↦v']) P), by begin
      unfold vc.subst_env,
      have h2: (env.apply (σ₁[y↦v']) x = some v), from x_is_v,
      unfold env.apply at h2,
      by_cases (y = x ∧ (option.is_none (env.apply σ₁ x))) with h3,
      simp[h3] at h2,
      have h4: (v' = v), from option.some.inj h2,
      simp[h3],
      have h5: (σ₁ x = none), from option.is_none.inv.mpr h3.right,
      have h6: x ∉ σ₁, from env.contains_apply_equiv.left.mp h5,
      rw[h4],
      have h7: x ∉ FV (vc.subst x v P), from vc.not_free_of_subst,
      have h8: x ∉ FV (vc.subst_env σ₁ (vc.subst x v P)),
      from mt free_in_vc.subst_env h7,
      have h9: (vc.subst x v (vc.subst_env σ₁ (vc.subst x v P)) = (vc.subst_env σ₁ (vc.subst x v P))),
      from unchanged_of_subst_nonfree_vc h8,
      rw[h9],
      from vc.subst_env.order (or.inl h6),

      simp[h3] at h2,
      have h4, from ih h2,
      congr,
      from h4
    end
  end

lemma vc.subst_env_with_equivalent_env {P: vc} {σ₁ σ₂: env}:
  (∀z, z ∈ σ₁ → (σ₁ z = σ₂ z)) → (vc.subst_env σ₂ (vc.subst_env σ₁ P) = vc.subst_env σ₂ P) :=
  begin
    assume env_equiv,
    induction σ₁ with σ₁' x v ih,
    
    show (vc.subst_env σ₂ (vc.subst_env env.empty P) = vc.subst_env σ₂ P), from (
      have vc.subst_env env.empty P = P, by unfold vc.subst_env,
      show vc.subst_env σ₂ (vc.subst_env env.empty P) = vc.subst_env σ₂ P, from this.symm ▸ rfl
    ),

    show (vc.subst_env σ₂ (vc.subst_env (σ₁'[x↦v]) P) = vc.subst_env σ₂ P), by begin
      unfold vc.subst_env,

      have h0: (∀ (z : var), z ∈ σ₁' → (σ₁' z = σ₂ z)), from (
        assume z: var,
        assume h1: z ∈ σ₁',
        have ∃v, σ₁' z = some v, from env.contains_apply_equiv.right.mpr h1,
        let ⟨v', h2⟩ := this in
        have option.is_some (σ₁' z), from option.is_some_iff_exists.mpr this,
        have ¬ option.is_none (σ₁' z), from option.some_iff_not_none.mp this,
        have ¬ (x = z ∧ option.is_none (env.apply σ₁' z)), from not_and_distrib.mpr (or.inr this),
        have h3: env.apply (σ₁'[x↦v]) z = σ₁' z, by { unfold env.apply, simp[this], refl },
        have z ∈ (σ₁'[x↦v]), from env.contains.rest h1,
        show σ₁' z = σ₂ z, from h3 ▸ (env_equiv z this)
      ),
      by_cases (x ∈ σ₁') with h1,

      have h2: x ∉ FV (vc.subst_env σ₁' P), from vc.not_free_of_subst_env h1,
      have h3: (vc.subst x v (vc.subst_env σ₁' P) = (vc.subst_env σ₁' P)),
      from unchanged_of_subst_nonfree_vc h2,
      rw[h3],
      from ih h0,

      have h2: x ∈ (σ₁'[x↦v]), from env.contains.same,
      have h3: ((σ₁'[x↦v]) x = σ₂ x), from env_equiv x h2,
      have h4: (env.apply (σ₁'[x↦v]) x = v), from env.apply_of_contains h1,
      have h5: (σ₂ x = some v), from eq.trans h3.symm h4,
      have h6: (vc.subst_env σ₂ (vc.subst x v (vc.subst_env σ₁' P)) = vc.subst_env σ₂ (vc.subst_env σ₁' P)),
      from vc.subst_env_inner h5,
      rw[h6],
      from ih h0
    end
  end

lemma vc.subst_env_equivalent_env {P: vc} {σ₁ σ₂: env}:
  (∀z, z ∈ σ₁ → (σ₁ z = σ₂ z)) → closed_subst σ₁ P → (vc.subst_env σ₁ P = vc.subst_env σ₂ P) :=
  assume h1: (∀z, z ∈ σ₁ → (σ₁ z = σ₂ z)),
  assume P_closed: closed_subst σ₁ P,
  have closed (vc.subst_env σ₁ P), from vc.closed_of_closed_subst P_closed,
  have h2: vc.subst_env σ₂ (vc.subst_env σ₁ P) = (vc.subst_env σ₁ P),
  from unchanged_of_subst_env_nonfree_vc this σ₂,
  have vc.subst_env σ₂ (vc.subst_env σ₁ P) = vc.subst_env σ₂ P,
  from vc.subst_env_with_equivalent_env h1,
  show vc.subst_env σ₁ P = vc.subst_env σ₂ P, from h2 ▸ this

lemma env.remove_unimportant_equivalence {σ₁ σ₂: env} {x: var}:
  (∀y, y ∈ σ₁ → (σ₁ y = σ₂ y)) → x ∉ σ₁ → (∀y, y ∈ σ₁ → (σ₁ y = σ₂.without x y)) :=
  assume h1: (∀y, y ∈ σ₁ → (σ₁ y = σ₂ y)),
  assume h2: x ∉ σ₁,
  assume y: var,
  assume h3: y ∈ σ₁,
  have ∃v, σ₁ y = some v, from env.contains_apply_equiv.right.mpr h3,
  let ⟨v, h4⟩ := this in
  have σ₁ y = σ₂ y, from h1 y h3,
  have h5: σ₂ y = v, from eq.trans this.symm h4,
  have h6: x ≠ y, from (
    assume : x = y,
    have x ∈ σ₁, from this.symm ▸ h3,
    show «false», from h2 this
  ),
  have y ∈ σ₁.dom, from h3,
  have y ∈ σ₂.dom, from set.mem_of_subset_of_mem (env.dom_subset_of_equivalent_env h1) this,
  have y ∈ σ₂, from this,
  have h7: y ∈ σ₂.without x, from env.contains_without.rinv ⟨this, h6.symm⟩,
  -- have ∃v', σ₂.without x y = some v', from env.contains_apply_equiv.right.mpr this,
  have y ∉ σ₂.without x ∨ (σ₂.without x y = v), from env.without_equiv (or.inr h5),
  or.elim this (
    assume : y ∉ σ₂.without x,
    show σ₁ y = σ₂.without x y, from absurd h7 this
  ) (
    assume : σ₂.without x y = v,
    show σ₁ y = σ₂.without x y, from eq.trans h4 this.symm
  )

lemma vc.subst_env_without_nonfree {σ: env} {P: vc} {x: var}:
  x ∉ FV P → (vc.subst_env σ P = vc.subst_env (σ.without x) P) :=
  begin
    assume h1: x ∉ FV P,

    induction σ with σ' y v ih,

    show (vc.subst_env env.empty P = vc.subst_env (env.without env.empty x) P), by begin
      unfold env.without
    end,

    show (vc.subst_env (σ'[y↦v]) P = vc.subst_env (env.without (σ'[y↦v]) x) P), by begin
      unfold env.without,
      by_cases (y = x) with h2,

      simp[h2],
      unfold vc.subst_env,
      have h3: x ∉ FV (vc.subst_env σ' P), by begin
        assume : x ∈ FV (vc.subst_env σ' P),
        have : x ∈ FV P, from free_in_vc.subst_env this,
        show «false», from h1 this
      end,
      have h4: (vc.subst x v (vc.subst_env σ' P) = (vc.subst_env σ' P)),
      from unchanged_of_subst_nonfree_vc h3,
      from eq.trans h4 ih,

      simp[h2],
      unfold vc.subst_env,
      rw[ih]
    end
  end

lemma vc.subst_env.reorder {σ: env} {x: var} {v: value} {P: vc}:
  (vc.subst_env σ (vc.subst x v P) = vc.subst x v (vc.subst_env (σ.without x) P)) :=
  have x ∉ FV (vc.subst x v P), from vc.not_free_of_subst,
  have h1: vc.subst_env σ (vc.subst x v P) = vc.subst_env (σ.without x) (vc.subst x v P),
  from vc.subst_env_without_nonfree this,
  have x ∉ σ.without x, from env.not_contains_without,
  have h2: (vc.subst_env (σ.without x) (vc.subst x v P) = vc.subst x v (vc.subst_env (σ.without x) P)),
  from vc.subst_env.order (or.inl this),
  show vc.subst_env σ (vc.subst x v P) = vc.subst x v (vc.subst_env (σ.without x) P),
  from eq.trans h1 h2

lemma vc.substt_env.reorder {σ: env} {x: var} {t: term} {P: vc}:
  closed t → (vc.subst_env σ (vc.substt x t P) = vc.substt x t (vc.subst_env (σ.without x) P)) :=
  assume t_closed: closed t,
  have x ∉ FV (vc.substt x t P), from vc.not_free_of_substt t_closed,
  have h1: vc.subst_env σ (vc.substt x t P) = vc.subst_env (σ.without x) (vc.substt x t P),
  from vc.subst_env_without_nonfree this,
  have x ∉ σ.without x, from env.not_contains_without,
  have h2: (vc.subst_env (σ.without x) (vc.substt x t P) = vc.substt x t (vc.subst_env (σ.without x) P)),
  from vc.substt_env.order t_closed this,
  show vc.subst_env σ (vc.substt x t P) = vc.substt x t (vc.subst_env (σ.without x) P),
  from eq.trans h1 h2

lemma vc.substte_env.reorder {σ: env} {x: var} {t: term} {P: vc}:
  closed_subst σ t → (vc.subst_env σ (vc.substte x t P σ) = vc.substte x t (vc.subst_env (σ.without x) P) σ) :=
  assume t_closed: closed_subst σ t,
  have x ∉ FV (vc.substte x t P σ), from vc.not_free_of_substte t_closed,
  have h1: vc.subst_env σ (vc.substte x t P σ) = vc.subst_env (σ.without x) (vc.substte x t P σ),
  from vc.subst_env_without_nonfree this,
  have h2: (∀z, z ∈ σ.without x → (σ.without x z = σ z)), from env.without_equiv_with,
  have x ∉ σ.without x, from env.not_contains_without,
  have h3: (vc.subst_env (σ.without x) (vc.substte x t P σ) = vc.substte x t (vc.subst_env (σ.without x) P) σ),
  from vc.substte_env.order h2 this,
  show vc.subst_env σ (vc.substte x t P σ) = vc.substte x t (vc.subst_env (σ.without x) P) σ,
  from eq.trans h1 h3

lemma term.substt_env.redundant {σ: env} {x: var} {t t': term}:
  (term.subst_env σ (term.substt x (term.subst_env σ t) t') = term.subst_env σ (term.substt x t t')) :=
  begin
    induction t' with v y unop t₁ t₁_ih binop t₂ t₃ t₂_ih t₃_ih t₄ t₅ t₄_ih t₅_ih,

    show (term.subst_env σ (term.substt x (term.subst_env σ t) (term.value v)) =
          term.subst_env σ (term.substt x t (term.value v))), by begin
      unfold term.substt
    end,

    show (term.subst_env σ (term.substt x (term.subst_env σ t) (term.var y)) =
          term.subst_env σ (term.substt x t (term.var y))), by begin
      unfold term.substt,
      by_cases (x = y) with h1,
      simp[h1],
      from term.subst_env_twice,
      simp[h1]
    end,

    show (term.subst_env σ (term.substt x (term.subst_env σ t) (term.unop unop t₁)) =
          term.subst_env σ (term.substt x t (term.unop unop t₁))), by begin
      unfold term.substt,
      rw[term.subst_env.unop],
      rw[term.subst_env.unop],
      congr,
      from t₁_ih
    end,

    show (term.subst_env σ (term.substt x (term.subst_env σ t) (term.binop binop t₂ t₃)) =
          term.subst_env σ (term.substt x t (term.binop binop t₂ t₃))), by begin
      unfold term.substt,
      rw[term.subst_env.binop],
      rw[term.subst_env.binop],
      congr,
      from t₂_ih,
      from t₃_ih
    end,

    show (term.subst_env σ (term.substt x (term.subst_env σ t) (term.app t₄ t₅)) =
          term.subst_env σ (term.substt x t (term.app t₄ t₅))), by begin
      unfold term.substt,
      rw[term.subst_env.app],
      rw[term.subst_env.app],
      congr,
      from t₄_ih,
      from t₅_ih
    end
  end

-- lemma vc.substt_env.redundant {x: var} {t: term} {P: vc}:
--   ∀σ, (vc.subst_env σ (vc.substt x (term.subst_env σ t) P) = vc.subst_env σ (vc.substt x t P)) :=
--   begin
--     induction P,
--     case vc.term t' {
--       assume σ,
--       unfold vc.substt,
--       rw[vc.subst_env.term],
--       rw[vc.subst_env.term],
--       apply vc.term.inj.inv,
--       from term.substt_env.redundant
--     },
--     case vc.not P₁ ih {
--       assume σ,
--       unfold vc.substt,
--       rw[vc.subst_env.not],
--       rw[vc.subst_env.not],
--       apply vc.not.inj.inv,
--       from ih σ
--     },
--     case vc.and P₁ P₂ P₁_ih P₂_ih {
--       assume σ,
--       unfold vc.substt,
--       rw[vc.subst_env.and],
--       rw[vc.subst_env.and],
--       apply vc.and.inj.inv,
--       from P₁_ih σ,
--       from P₂_ih σ
--     },
--     case vc.or P₁ P₂ P₁_ih P₂_ih {
--       assume σ,
--       unfold vc.substt,
--       rw[vc.subst_env.or],
--       rw[vc.subst_env.or],
--       apply vc.or.inj.inv,
--       from P₁_ih σ,
--       from P₂_ih σ
--     },
--     case vc.pre t₁ t₂ {
--       assume σ,
--       unfold vc.substt,
--       rw[vc.subst_env.pre],
--       rw[vc.subst_env.pre],
--       apply vc.pre.inj.inv,
--       from term.substt_env.redundant,
--       from term.substt_env.redundant
--     },
--     case vc.pre₁ op t₁ {
--       assume σ,
--       unfold vc.substt,
--       rw[vc.subst_env.pre₁],
--       rw[vc.subst_env.pre₁],
--       apply vc.pre₁.inj.inv,
--       from term.substt_env.redundant
--     },
--     case vc.pre₂ op t₁ t₂ {
--       assume σ,
--       unfold vc.substt,
--       rw[vc.subst_env.pre₂],
--       rw[vc.subst_env.pre₂],
--       apply vc.pre₂.inj.inv,
--       from term.substt_env.redundant,
--       from term.substt_env.redundant
--     },
--     case vc.post t₁ t₂ {
--       assume σ,
--       unfold vc.substt,
--       rw[vc.subst_env.post],
--       rw[vc.subst_env.post],
--       apply vc.post.inj.inv,
--       from term.substt_env.redundant,
--       from term.substt_env.redundant
--     },
--     case vc.univ y P₁ P₁_ih {
--       assume σ,
--       unfold vc.substt,
--       rw[vc.subst_env.univ],
--       rw[vc.subst_env.univ],
--       apply vc.univ.inj.inv,
--       by_cases (x = y) with h1,

--       simp[h1],
--       simp[h1],
--       from P₁_ih (σ.without y)
--     }
--   end
