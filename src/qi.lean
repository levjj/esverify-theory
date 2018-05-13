-- quantifier instantiation

import .definitions3 .freevars .substitution .logic

lemma prop.has_call_p.term.inv {c: calltrigger} {t: term}: c ∉ calls_p t :=
  assume t_has_call: prop.has_call_p c t,
  show «false», by cases t_has_call

lemma prop.has_call_p.not.inv {c: calltrigger} {P: prop}: c ∈ calls_p P.not → c ∈ calls_n P :=
  assume not_has_call: c ∈ calls_p P.not,
  begin
    cases not_has_call,
    from a
  end

lemma prop.has_call_p.and.inv {c: calltrigger} {P₁ P₂: prop}: c ∈ calls_p (P₁ ⋀ P₂) → c ∈ calls_p P₁ ∨ c ∈ calls_p P₂ :=
  assume and_has_call: c ∈ calls_p (P₁ ⋀ P₂),
  begin
    cases and_has_call,
    show c ∈ calls_p P₁ ∨ c ∈ calls_p P₂, from or.inl a,
    show c ∈ calls_p P₁ ∨ c ∈ calls_p P₂, from or.inr a
  end

lemma prop.has_call_p.or.inv {c: calltrigger} {P₁ P₂: prop}: c ∈ calls_p (P₁ ⋁ P₂) → c ∈ calls_p P₁ ∨ c ∈ calls_p P₂ :=
  assume or_has_call: c ∈ calls_p (P₁ ⋁ P₂),
  begin
    cases or_has_call,
    show c ∈ calls_p P₁ ∨ c ∈ calls_p P₂, from or.inl a,
    show c ∈ calls_p P₁ ∨ c ∈ calls_p P₂, from or.inr a
  end

lemma prop.has_call_p.pre₁.inv {c: calltrigger} {op: unop} {t: term}: c ∉ calls_p (prop.pre₁ op t) :=
  assume pre_has_call: c ∈ calls_p (prop.pre₁ op t),
  show «false», by cases pre_has_call

lemma prop.has_call_p.pre₂.inv {c: calltrigger} {op: binop} {t₁ t₂: term}: c ∉ calls_p (prop.pre₂ op t₁ t₂) :=
  assume pre_has_call: c ∈ calls_p (prop.pre₂ op t₁ t₂),
  show «false», by cases pre_has_call

lemma prop.has_call_p.pre.inv {c: calltrigger} {t₁ t₂: term}: c ∉ calls_p (prop.pre t₁ t₂) :=
  assume pre_has_call: c ∈ calls_p (prop.pre t₁ t₂),
  show «false», by cases pre_has_call

lemma prop.has_call_p.post.inv {c: calltrigger} {t₁ t₂: term}: c ∉ calls_p (prop.post t₁ t₂) :=
  assume post_has_call: c ∈ calls_p (prop.post t₁ t₂),
  show «false», by cases post_has_call

lemma prop.has_call_p.call.inv {c: calltrigger} {t: term}:
      c ∈ calls_p (prop.call t) → (c = calltrigger.mk t) :=
  assume call_has_call: c ∈ calls_p (prop.call t),
  show c = calltrigger.mk t, by { cases call_has_call, refl }

lemma prop.has_call_p.forallc.inv {c: calltrigger} {x: var} {t: term} {P: prop}:
      c ∉ calls_p (prop.forallc x P) :=
  assume forall_has_call: c ∈ calls_p (prop.forallc x P),
  begin
    cases forall_has_call
  end

lemma prop.has_call_p.exis.inv {c: calltrigger} {x: var} {P: prop}: c ∉ calls_p (prop.exis x P) :=
  assume exis_has_call: c ∈ calls_p (prop.exis x P),
  begin
    cases exis_has_call
  end

lemma prop.has_call_n.term.inv {c: calltrigger} {t: term}: c ∉ calls_n t :=
  assume t_has_call_n: prop.has_call_n c t,
  show «false», by cases t_has_call_n

lemma prop.has_call_n.not.inv {c: calltrigger} {P: prop}: c ∈ calls_n P.not → c ∈ calls_p P :=
  assume not_has_call_n: c ∈ calls_n P.not,
  begin
    cases not_has_call_n,
    from a
  end

lemma prop.has_call_n.and.inv {c: calltrigger} {P₁ P₂: prop}: c ∈ calls_n (P₁ ⋀ P₂) → c ∈ calls_n P₁ ∨ c ∈ calls_n P₂ :=
  assume and_has_call_n: c ∈ calls_n (P₁ ⋀ P₂),
  begin
    cases and_has_call_n,
    show c ∈ calls_n P₁ ∨ c ∈ calls_n P₂, from or.inl a,
    show c ∈ calls_n P₁ ∨ c ∈ calls_n P₂, from or.inr a
  end

lemma prop.has_call_n.or.inv {c: calltrigger} {P₁ P₂: prop}: c ∈ calls_n (P₁ ⋁ P₂) → c ∈ calls_n P₁ ∨ c ∈ calls_n P₂ :=
  assume or_has_call_n: c ∈ calls_n (P₁ ⋁ P₂),
  begin
    cases or_has_call_n,
    show c ∈ calls_n P₁ ∨ c ∈ calls_n P₂, from or.inl a,
    show c ∈ calls_n P₁ ∨ c ∈ calls_n P₂, from or.inr a
  end

lemma prop.has_call_n.pre₁.inv {c: calltrigger} {op: unop} {t: term}: c ∉ calls_n (prop.pre₁ op t) :=
  assume pre_has_call_n: c ∈ calls_n (prop.pre₁ op t),
  show «false», by cases pre_has_call_n

lemma prop.has_call_n.pre₂.inv {c: calltrigger} {op: binop} {t₁ t₂: term}: c ∉ calls_n (prop.pre₂ op t₁ t₂) :=
  assume pre_has_call_n: c ∈ calls_n (prop.pre₂ op t₁ t₂),
  show «false», by cases pre_has_call_n

lemma prop.has_call_n.pre.inv {c: calltrigger} {t₁ t₂: term}: c ∉ calls_n (prop.pre t₁ t₂) :=
  assume pre_has_call_n: c ∈ calls_n (prop.pre t₁ t₂),
  show «false», by cases pre_has_call_n

lemma prop.has_call_n.post.inv {c: calltrigger} {t₁ t₂: term}: c ∉ calls_n (prop.post t₁ t₂) :=
  assume post_has_call_n: c ∈ calls_n (prop.post t₁ t₂),
  show «false», by cases post_has_call_n

lemma prop.has_call_n.call.inv {c: calltrigger} {t₁ t₂: term}: c ∉ calls_n (prop.call t₁ t₂) :=
  assume call_has_call_n: c ∈ calls_n (prop.call t₁ t₂),
  show «false», by cases call_has_call_n

lemma prop.has_call_n.forallc.inv {c: calltrigger} {x: var} {t: term} {P: prop}:
      c ∉ calls_n (prop.forallc x P) :=
  assume forall_has_call_n: c ∈ calls_n (prop.forallc x P),
  begin
    cases forall_has_call_n
  end

lemma prop.has_call_n.exis.inv {c: calltrigger} {x: var} {P: prop}: c ∉ calls_n (prop.exis x P) :=
  assume exis_has_call_n: c ∈ calls_n (prop.exis x P),
  begin
    cases exis_has_call_n
  end

lemma prop.has_quantifier_p.term.inv {q: callquantifier} {t: term}: q ∉ quantifiers_p t :=
  assume t_has_quantifier_p: prop.has_quantifier_p q t,
  show «false», by cases t_has_quantifier_p

lemma prop.has_quantifier_p.not.inv {q: callquantifier} {P: prop}: q ∈ quantifiers_p P.not → q ∈ quantifiers_n P :=
  assume not_has_quantifier_p: q ∈ quantifiers_p P.not,
  begin
    cases not_has_quantifier_p with a,
    from a
  end

lemma prop.has_quantifier_p.and.inv {q: callquantifier} {P₁ P₂: prop}:
      q ∈ quantifiers_p (P₁ ⋀ P₂) → q ∈ quantifiers_p P₁ ∨ q ∈ quantifiers_p P₂ :=
  assume and_has_quantifier_p: q ∈ quantifiers_p (P₁ ⋀ P₂),
  begin
    cases and_has_quantifier_p,
    show q ∈ quantifiers_p P₁ ∨ q ∈ quantifiers_p P₂, from or.inl a,
    show q ∈ quantifiers_p P₁ ∨ q ∈ quantifiers_p P₂, from or.inr a
  end

lemma prop.has_quantifier_p.or.inv {q: callquantifier} {P₁ P₂: prop}:
      q ∈ quantifiers_p (P₁ ⋁ P₂) → q ∈ quantifiers_p P₁ ∨ q ∈ quantifiers_p P₂ :=
  assume or_has_quantifier_p: q ∈ quantifiers_p (P₁ ⋁ P₂),
  begin
    cases or_has_quantifier_p,
    show q ∈ quantifiers_p P₁ ∨ q ∈ quantifiers_p P₂, from or.inl a,
    show q ∈ quantifiers_p P₁ ∨ q ∈ quantifiers_p P₂, from or.inr a
  end

lemma prop.has_quantifier_p.pre₁.inv {q: callquantifier} {op: unop} {t: term}: q ∉ quantifiers_p (prop.pre₁ op t) :=
  assume pre_has_quantifier_p: q ∈ quantifiers_p (prop.pre₁ op t),
  show «false», by cases pre_has_quantifier_p

lemma prop.has_quantifier_p.pre₂.inv {q: callquantifier} {op: binop} {t₁ t₂: term}: q ∉ quantifiers_p (prop.pre₂ op t₁ t₂) :=
  assume pre_has_quantifier_p: q ∈ quantifiers_p (prop.pre₂ op t₁ t₂),
  show «false», by cases pre_has_quantifier_p

lemma prop.has_quantifier_p.pre.inv {q: callquantifier} {t₁ t₂: term}: q ∉ quantifiers_p (prop.pre t₁ t₂) :=
  assume pre_has_quantifier_p: q ∈ quantifiers_p (prop.pre t₁ t₂),
  show «false», by cases pre_has_quantifier_p

lemma prop.has_quantifier_p.post.inv {q: callquantifier} {t₁ t₂: term}: q ∉ quantifiers_p (prop.post t₁ t₂) :=
  assume post_has_quantifier_p: q ∈ quantifiers_p (prop.post t₁ t₂),
  show «false», by cases post_has_quantifier_p

lemma prop.has_quantifier_p.call.inv {q: callquantifier} {t₁ t₂: term}: q ∉ quantifiers_p (prop.call t₁ t₂) :=
  assume call_has_quantifier_p: q ∈ quantifiers_p (prop.call t₁ t₂),
  show «false», by cases call_has_quantifier_p

lemma prop.has_quantifier_p.forallc.inv {q: callquantifier} {x: var} {P: prop}:
      q ∈ quantifiers_p (prop.forallc x P) → (q = ⟨x, P⟩) :=
  assume forall_has_quantifier_p: q ∈ quantifiers_p (prop.forallc x P),
  begin
    cases forall_has_quantifier_p,
    from rfl
  end

lemma prop.has_quantifier_n.term.inv {q: callquantifier} {t: term}: q ∉ quantifiers_n t :=
  assume t_has_quantifier_n: prop.has_quantifier_n q t,
  show «false», by cases t_has_quantifier_n

lemma prop.has_quantifier_n.not.inv {q: callquantifier} {P: prop}: q ∈ quantifiers_n P.not → q ∈ quantifiers_p P :=
  assume not_has_quantifier_n: q ∈ quantifiers_n P.not,
  begin
    cases not_has_quantifier_n,
    from a
  end

lemma prop.has_quantifier_n.and.inv {q: callquantifier} {P₁ P₂: prop}:
      q ∈ quantifiers_n (P₁ ⋀ P₂) → q ∈ quantifiers_n P₁ ∨ q ∈ quantifiers_n P₂ :=
  assume and_has_quantifier_n: q ∈ quantifiers_n (P₁ ⋀ P₂),
  begin
    cases and_has_quantifier_n,
    show q ∈ quantifiers_n P₁ ∨ q ∈ quantifiers_n P₂, from or.inl a,
    show q ∈ quantifiers_n P₁ ∨ q ∈ quantifiers_n P₂, from or.inr a
  end

lemma prop.has_quantifier_n.or.inv {q: callquantifier} {P₁ P₂: prop}:
      q ∈ quantifiers_n (P₁ ⋁ P₂) → q ∈ quantifiers_n P₁ ∨ q ∈ quantifiers_n P₂ :=
  assume or_has_quantifier_n: q ∈ quantifiers_n (P₁ ⋁ P₂),
  begin
    cases or_has_quantifier_n,
    show q ∈ quantifiers_n P₁ ∨ q ∈ quantifiers_n P₂, from or.inl a,
    show q ∈ quantifiers_n P₁ ∨ q ∈ quantifiers_n P₂, from or.inr a
  end

lemma prop.has_quantifier_n.pre₁.inv {q: callquantifier} {op: unop} {t: term}: q ∉ quantifiers_n (prop.pre₁ op t) :=
  assume pre_has_quantifier_n: q ∈ quantifiers_n (prop.pre₁ op t),
  show «false», by cases pre_has_quantifier_n

lemma prop.has_quantifier_n.pre₂.inv {q: callquantifier} {op: binop} {t₁ t₂: term}: q ∉ quantifiers_n (prop.pre₂ op t₁ t₂) :=
  assume pre_has_quantifier_n: q ∈ quantifiers_n (prop.pre₂ op t₁ t₂),
  show «false», by cases pre_has_quantifier_n

lemma prop.has_quantifier_n.pre.inv {q: callquantifier} {t₁ t₂: term}: q ∉ quantifiers_n (prop.pre t₁ t₂) :=
  assume pre_has_quantifier_n: q ∈ quantifiers_n (prop.pre t₁ t₂),
  show «false», by cases pre_has_quantifier_n

lemma prop.has_quantifier_n.post.inv {q: callquantifier} {t₁ t₂: term}: q ∉ quantifiers_n (prop.post t₁ t₂) :=
  assume post_has_quantifier_n: q ∈ quantifiers_n (prop.post t₁ t₂),
  show «false», by cases post_has_quantifier_n

lemma prop.has_quantifier_n.call.inv {q: callquantifier} {t₁ t₂: term}: q ∉ quantifiers_n (prop.call t₁ t₂) :=
  assume call_has_quantifier_n: q ∈ quantifiers_n (prop.call t₁ t₂),
  show «false», by cases call_has_quantifier_n

lemma prop.has_quantifier_n.forallc.inv {q: callquantifier} {x: var} {P: prop}:
      q ∉ quantifiers_n (prop.forallc x P) :=
  assume forall_has_quantifier_n: q ∈ quantifiers_n (prop.forallc x P),
  begin
    cases forall_has_quantifier_n
  end

lemma prop.has_call_p_subst.term.inv {c: calltrigger} {t: term} {σ: env}:
      c ∉ calls_p_subst σ t :=
  assume : c ∈ calls_p_subst σ t,
  have c ∈ (calltrigger.subst σ) '' calls_p t, from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_p t)
      (λa, «false») c this (
    assume c': calltrigger,
    assume : c' ∈ calls_p t,
    show «false», from prop.has_call_p.term.inv this
  )

lemma prop.has_call_p_subst.and₁ {c: calltrigger} {P₁ P₂: prop} {σ: env}:
      c ∈ calls_p_subst σ P₁ → c ∈ calls_p_subst σ (P₁ ⋀ P₂) :=
  assume : c ∈ calls_p_subst σ P₁,
  have c ∈ (calltrigger.subst σ) '' calls_p P₁, from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_p P₁)
      (λa, a ∈ calls_p_subst σ (P₁ ⋀ P₂)) c this (
    assume c': calltrigger,
    assume : c' ∈ calls_p P₁,
    have c' ∈ calls_p (P₁ ⋀ P₂), from prop.has_call_p.and₁ this,
    show calltrigger.subst σ c' ∈ calls_p_subst σ (P₁ ⋀ P₂), from set.mem_image this rfl
  )

lemma prop.has_call_p_subst.and₂ {c: calltrigger} {P₁ P₂: prop} {σ: env}:
      c ∈ calls_p_subst σ P₂ → c ∈ calls_p_subst σ (P₁ ⋀ P₂) :=
  assume : c ∈ calls_p_subst σ P₂,
  have c ∈ (calltrigger.subst σ) '' calls_p P₂, from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_p P₂)
      (λa, a ∈ calls_p_subst σ (P₁ ⋀ P₂)) c this (
    assume c': calltrigger,
    assume : c' ∈ calls_p P₂,
    have c' ∈ calls_p (P₁ ⋀ P₂), from prop.has_call_p.and₂ this,
    show calltrigger.subst σ c' ∈ calls_p_subst σ (P₁ ⋀ P₂), from set.mem_image this rfl
  )

lemma prop.has_call_p_subst.not {c: calltrigger} {P: prop} {σ: env}:
      c ∈ calls_p_subst σ P → c ∈ calls_n_subst σ P.not :=
  assume : c ∈ calls_p_subst σ P,
  have c ∈ (calltrigger.subst σ) '' calls_p P, from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_p P)
      (λa, a ∈ calls_n_subst σ P.not) c this (
    assume c': calltrigger,
    assume : c' ∈ calls_p P,
    have c' ∈ calls_n P.not, from prop.has_call_n.not this,
    show calltrigger.subst σ c' ∈ calls_n_subst σ P.not, from set.mem_image this rfl
  )

lemma prop.has_call_n_subst.term.inv {c: calltrigger} {t: term} {σ: env}:
      c ∉ calls_n_subst σ t :=
  assume : c ∈ calls_n_subst σ t,
  have c ∈ (calltrigger.subst σ) '' calls_n t, from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_n t)
      (λa, «false») c this (
    assume c': calltrigger,
    assume : c' ∈ calls_n t,
    show «false», from prop.has_call_n.term.inv this
  )

lemma prop.has_call_n_subst.not {c: calltrigger} {P: prop} {σ: env}:
      c ∈ calls_n_subst σ P → c ∈ calls_p_subst σ P.not :=
  assume : c ∈ calls_n_subst σ P,
  have c ∈ (calltrigger.subst σ) '' calls_n P, from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_n P)
      (λa, a ∈ calls_p_subst σ P.not) c this (
    assume c': calltrigger,
    assume : c' ∈ calls_n P,
    have c' ∈ calls_p P.not, from prop.has_call_p.not this,
    show calltrigger.subst σ c' ∈ calls_p_subst σ P.not, from set.mem_image this rfl
  )

lemma prop.has_call_p_subst.not.inv {c: calltrigger} {P: prop} {σ: env}:
      c ∈ calls_p_subst σ P.not → c ∈ calls_n_subst σ P :=
  assume : c ∈ calls_p_subst σ P.not,
  have c ∈ (calltrigger.subst σ) '' calls_p P.not, from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_p P.not)
      (λa, a ∈ calls_n_subst σ P) c this (
    assume c': calltrigger,
    assume : c' ∈ calls_p P.not,
    have c' ∈ calls_n P, from prop.has_call_p.not.inv this,
    show calltrigger.subst σ c' ∈ calls_n_subst σ P, from set.mem_image this rfl
  )

lemma prop.has_call_n_subst.not.inv {c: calltrigger} {P: prop} {σ: env}:
      c ∈ calls_n_subst σ P.not → c ∈ calls_p_subst σ P :=
  assume : c ∈ calls_n_subst σ P.not,
  have c ∈ (calltrigger.subst σ) '' calls_n P.not, from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_n P.not)
      (λa, a ∈ calls_p_subst σ P) c this (
    assume c': calltrigger,
    assume : c' ∈ calls_n P.not,
    have c' ∈ calls_p P, from prop.has_call_n.not.inv this,
    show calltrigger.subst σ c' ∈ calls_p_subst σ P, from set.mem_image this rfl
  )

lemma prop.has_call_p_subst.and.inv {c: calltrigger} {P₁ P₂: prop} {σ: env}:
      c ∈ calls_p_subst σ (P₁ ⋀ P₂) → c ∈ calls_p_subst σ P₁ ∨ c ∈ calls_p_subst σ P₂ :=
  assume : c ∈ calls_p_subst σ (P₁ ⋀ P₂),
  have c ∈ (calltrigger.subst σ) '' calls_p (P₁ ⋀ P₂), from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_p (P₁ ⋀ P₂))
      (λa, a ∈ calls_p_subst σ P₁ ∨ a ∈ calls_p_subst σ P₂) c this (
    assume c': calltrigger,
    assume : c' ∈ calls_p (P₁ ⋀ P₂),
    or.elim (prop.has_call_p.and.inv this) (
      assume : c' ∈ calls_p P₁,
      have calltrigger.subst σ c' ∈ calls_p_subst σ P₁, from set.mem_image this rfl,
      show calltrigger.subst σ c' ∈ calls_p_subst σ P₁
         ∨ calltrigger.subst σ c' ∈ calls_p_subst σ P₂, from or.inl this
    ) (
      assume : c' ∈ calls_p P₂,
      have calltrigger.subst σ c' ∈ calls_p_subst σ P₂, from set.mem_image this rfl,
      show calltrigger.subst σ c' ∈ calls_p_subst σ P₁
         ∨ calltrigger.subst σ c' ∈ calls_p_subst σ P₂, from or.inr this
    )
  )

lemma prop.has_call_p_subst.or.inv {c: calltrigger} {P₁ P₂: prop} {σ: env}:
      c ∈ calls_p_subst σ (P₁ ⋁ P₂) → c ∈ calls_p_subst σ P₁ ∨ c ∈ calls_p_subst σ P₂ :=
  assume : c ∈ calls_p_subst σ (P₁ ⋁ P₂),
  have c ∈ (calltrigger.subst σ) '' calls_p (P₁ ⋁ P₂), from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_p (P₁ ⋁ P₂))
      (λa, a ∈ calls_p_subst σ P₁ ∨ a ∈ calls_p_subst σ P₂) c this (
    assume c': calltrigger,
    assume : c' ∈ calls_p (P₁ ⋁ P₂),
    or.elim (prop.has_call_p.or.inv this) (
      assume : c' ∈ calls_p P₁,
      have calltrigger.subst σ c' ∈ calls_p_subst σ P₁, from set.mem_image this rfl,
      show calltrigger.subst σ c' ∈ calls_p_subst σ P₁
         ∨ calltrigger.subst σ c' ∈ calls_p_subst σ P₂, from or.inl this
    ) (
      assume : c' ∈ calls_p P₂,
      have calltrigger.subst σ c' ∈ calls_p_subst σ P₂, from set.mem_image this rfl,
      show calltrigger.subst σ c' ∈ calls_p_subst σ P₁
         ∨ calltrigger.subst σ c' ∈ calls_p_subst σ P₂, from or.inr this
    )
  )

lemma prop.has_call_n_subst.and.inv {c: calltrigger} {P₁ P₂: prop} {σ: env}:
      c ∈ calls_n_subst σ (P₁ ⋀ P₂) → c ∈ calls_n_subst σ P₁ ∨ c ∈ calls_n_subst σ P₂ :=
  assume : c ∈ calls_n_subst σ (P₁ ⋀ P₂),
  have c ∈ (calltrigger.subst σ) '' calls_n (P₁ ⋀ P₂), from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_n (P₁ ⋀ P₂))
      (λa, a ∈ calls_n_subst σ P₁ ∨ a ∈ calls_n_subst σ P₂) c this (
    assume c': calltrigger,
    assume : c' ∈ calls_n (P₁ ⋀ P₂),
    or.elim (prop.has_call_n.and.inv this) (
      assume : c' ∈ calls_n P₁,
      have calltrigger.subst σ c' ∈ calls_n_subst σ P₁, from set.mem_image this rfl,
      show calltrigger.subst σ c' ∈ calls_n_subst σ P₁
         ∨ calltrigger.subst σ c' ∈ calls_n_subst σ P₂, from or.inl this
    ) (
      assume : c' ∈ calls_n P₂,
      have calltrigger.subst σ c' ∈ calls_n_subst σ P₂, from set.mem_image this rfl,
      show calltrigger.subst σ c' ∈ calls_n_subst σ P₁
         ∨ calltrigger.subst σ c' ∈ calls_n_subst σ P₂, from or.inr this
    )
  )

lemma prop.has_call_n_subst.or.inv {c: calltrigger} {P₁ P₂: prop} {σ: env}:
      c ∈ calls_n_subst σ (P₁ ⋁ P₂) → c ∈ calls_n_subst σ P₁ ∨ c ∈ calls_n_subst σ P₂ :=
  assume : c ∈ calls_n_subst σ (P₁ ⋁ P₂),
  have c ∈ (calltrigger.subst σ) '' calls_n (P₁ ⋁ P₂), from this,
  @set.mem_image_elim_on calltrigger calltrigger (calltrigger.subst σ) (calls_n (P₁ ⋁ P₂))
      (λa, a ∈ calls_n_subst σ P₁ ∨ a ∈ calls_n_subst σ P₂) c this (
    assume c': calltrigger,
    assume : c' ∈ calls_n (P₁ ⋁ P₂),
    or.elim (prop.has_call_n.or.inv this) (
      assume : c' ∈ calls_n P₁,
      have calltrigger.subst σ c' ∈ calls_n_subst σ P₁, from set.mem_image this rfl,
      show calltrigger.subst σ c' ∈ calls_n_subst σ P₁
         ∨ calltrigger.subst σ c' ∈ calls_n_subst σ P₂, from or.inl this
    ) (
      assume : c' ∈ calls_n P₂,
      have calltrigger.subst σ c' ∈ calls_n_subst σ P₂, from set.mem_image this rfl,
      show calltrigger.subst σ c' ∈ calls_n_subst σ P₁
         ∨ calltrigger.subst σ c' ∈ calls_n_subst σ P₂, from or.inr this
    )
  )

lemma no_instantiations.term {t: term}: no_instantiations t :=
  have h1: calls_p t = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_p t,
    show «false», from prop.has_call_p.term.inv this
  ),
  have h2: calls_n t = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n t,
    show «false», from prop.has_call_n.term.inv this
  ),
  have h3: quantifiers_p t = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_p t,
    show «false», from prop.has_quantifier_p.term.inv  this
  ),
  have h4: quantifiers_n t = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n t,
    show «false», from prop.has_quantifier_n.term.inv  this
  ),
  ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩

lemma no_instantiations.not {P: prop}: no_instantiations P → no_instantiations P.not :=
  assume ⟨no_calls_p_in_P, ⟨no_calls_n_in_P, ⟨no_quantifiers_p_in_P, no_quantifiers_n_in_P⟩⟩⟩,
  have h1: calls_p P.not = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_p P.not,
    have c_in_calls_p_P: c ∈ calls_n P, from prop.has_call_p.not.inv this,
    have c_not_in_calls_p_P: c ∉ calls_n P, from set.forall_not_mem_of_eq_empty no_calls_n_in_P c,
    show «false», from c_not_in_calls_p_P c_in_calls_p_P
  ),
  have h2: calls_n P.not = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n P.not,
    have c_in_calls_p_P: c ∈ calls_p P, from prop.has_call_n.not.inv this,
    have c_not_in_calls_p_P: c ∉ calls_p P, from set.forall_not_mem_of_eq_empty no_calls_p_in_P c,
    show «false», from c_not_in_calls_p_P c_in_calls_p_P
  ),
  have h3: quantifiers_p P.not = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_p P.not,
    have c_in_quantifiers_p_P: q ∈ quantifiers_n P, from prop.has_quantifier_p.not.inv this,
    have c_not_in_quantifiers_p_P: q ∉ quantifiers_n P, from set.forall_not_mem_of_eq_empty no_quantifiers_n_in_P q,
    show «false», from c_not_in_quantifiers_p_P c_in_quantifiers_p_P
  ),
  have h4: quantifiers_n P.not = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n P.not,
    have c_in_quantifiers_p_P: q ∈ quantifiers_p P, from prop.has_quantifier_n.not.inv this,
    have c_not_in_quantifiers_p_P: q ∉ quantifiers_p P, from set.forall_not_mem_of_eq_empty no_quantifiers_p_in_P q,
    show «false», from c_not_in_quantifiers_p_P c_in_quantifiers_p_P
  ),
  ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩

lemma no_instantiations.and {P₁ P₂: prop}:
      no_instantiations P₁ → no_instantiations P₂ → no_instantiations (prop.and P₁ P₂) :=
  assume ⟨no_calls_p_in_P₁, ⟨no_calls_n_in_P₁, ⟨no_quantifiers_p_in_P₁, no_quantifiers_n_in_P₁⟩⟩⟩,
  assume ⟨no_calls_p_in_P₂, ⟨no_calls_n_in_P₂, ⟨no_quantifiers_p_in_P₂, no_quantifiers_n_in_P₂⟩⟩⟩,
  have h1: calls_p (P₁ ⋀ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_p (P₁ ⋀ P₂),
    have c ∈ calls_p P₁ ∨ c ∈ calls_p P₂, from prop.has_call_p.and.inv this,
    or.elim this (
      assume c_in_calls_p_P₁: c ∈ calls_p P₁,
      have c_not_in_calls_p_P₁: c ∉ calls_p P₁, from set.forall_not_mem_of_eq_empty no_calls_p_in_P₁ c,
      show «false», from c_not_in_calls_p_P₁ c_in_calls_p_P₁
    ) (
      assume c_in_calls_p_P₂: c ∈ calls_p P₂,
      have c_not_in_calls_p_P₂: c ∉ calls_p P₂, from set.forall_not_mem_of_eq_empty no_calls_p_in_P₂ c,
      show «false», from c_not_in_calls_p_P₂ c_in_calls_p_P₂
    )
  ),
  have h2: calls_n (P₁ ⋀ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n (P₁ ⋀ P₂),
    have c ∈ calls_n P₁ ∨ c ∈ calls_n P₂, from prop.has_call_n.and.inv this,
    or.elim this (
      assume c_in_calls_p_P₁: c ∈ calls_n P₁,
      have c_not_in_calls_p_P₁: c ∉ calls_n P₁, from set.forall_not_mem_of_eq_empty no_calls_n_in_P₁ c,
      show «false», from c_not_in_calls_p_P₁ c_in_calls_p_P₁
    ) (
      assume c_in_calls_p_P₂: c ∈ calls_n P₂,
      have c_not_in_calls_p_P₂: c ∉ calls_n P₂, from set.forall_not_mem_of_eq_empty no_calls_n_in_P₂ c,
      show «false», from c_not_in_calls_p_P₂ c_in_calls_p_P₂
    )
  ),
  have h3: quantifiers_p (P₁ ⋀ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_p (P₁ ⋀ P₂),
    have q ∈ quantifiers_p P₁ ∨ q ∈ quantifiers_p P₂, from prop.has_quantifier_p.and.inv this,
    or.elim this (
      assume q_in_quantifiers_p_P₁: q ∈ quantifiers_p P₁,
      have q_not_in_quantifiers_p_P₁: q ∉ quantifiers_p P₁, from set.forall_not_mem_of_eq_empty no_quantifiers_p_in_P₁ q,
      show «false», from q_not_in_quantifiers_p_P₁ q_in_quantifiers_p_P₁
    ) (
      assume q_in_quantifiers_p_P₂: q ∈ quantifiers_p P₂,
      have q_not_in_quantifiers_p_P₂: q ∉ quantifiers_p P₂, from set.forall_not_mem_of_eq_empty no_quantifiers_p_in_P₂ q,
      show «false», from q_not_in_quantifiers_p_P₂ q_in_quantifiers_p_P₂
    )
  ),
  have h4: quantifiers_n (P₁ ⋀ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n (P₁ ⋀ P₂),
    have q ∈ quantifiers_n P₁ ∨ q ∈ quantifiers_n P₂, from prop.has_quantifier_n.and.inv this,
    or.elim this (
      assume q_in_quantifiers_p_P₁: q ∈ quantifiers_n P₁,
      have q_not_in_quantifiers_p_P₁: q ∉ quantifiers_n P₁, from set.forall_not_mem_of_eq_empty no_quantifiers_n_in_P₁ q,
      show «false», from q_not_in_quantifiers_p_P₁ q_in_quantifiers_p_P₁
    ) (
      assume q_in_quantifiers_p_P₂: q ∈ quantifiers_n P₂,
      have q_not_in_quantifiers_p_P₂: q ∉ quantifiers_n P₂, from set.forall_not_mem_of_eq_empty no_quantifiers_n_in_P₂ q,
      show «false», from q_not_in_quantifiers_p_P₂ q_in_quantifiers_p_P₂
    )
  ),
  ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩

lemma no_instantiations.or {P₁ P₂: prop}:
      no_instantiations P₁ → no_instantiations P₂ → no_instantiations (prop.or P₁ P₂) :=
  assume ⟨no_calls_p_in_P₁, ⟨no_calls_n_in_P₁, ⟨no_quantifiers_p_in_P₁, no_quantifiers_n_in_P₁⟩⟩⟩,
  assume ⟨no_calls_p_in_P₂, ⟨no_calls_n_in_P₂, ⟨no_quantifiers_p_in_P₂, no_quantifiers_n_in_P₂⟩⟩⟩,
  have h1: calls_p (P₁ ⋁ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_p (P₁ ⋁ P₂),
    have c ∈ calls_p P₁ ∨ c ∈ calls_p P₂, from prop.has_call_p.or.inv this,
    or.elim this (
      assume c_in_calls_p_P₁: c ∈ calls_p P₁,
      have c_not_in_calls_p_P₁: c ∉ calls_p P₁, from set.forall_not_mem_of_eq_empty no_calls_p_in_P₁ c,
      show «false», from c_not_in_calls_p_P₁ c_in_calls_p_P₁
    ) (
      assume c_in_calls_p_P₂: c ∈ calls_p P₂,
      have c_not_in_calls_p_P₂: c ∉ calls_p P₂, from set.forall_not_mem_of_eq_empty no_calls_p_in_P₂ c,
      show «false», from c_not_in_calls_p_P₂ c_in_calls_p_P₂
    )
  ),
  have h2: calls_n (P₁ ⋁ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n (P₁ ⋁ P₂),
    have c ∈ calls_n P₁ ∨ c ∈ calls_n P₂, from prop.has_call_n.or.inv this,
    or.elim this (
      assume c_in_calls_p_P₁: c ∈ calls_n P₁,
      have c_not_in_calls_p_P₁: c ∉ calls_n P₁, from set.forall_not_mem_of_eq_empty no_calls_n_in_P₁ c,
      show «false», from c_not_in_calls_p_P₁ c_in_calls_p_P₁
    ) (
      assume c_in_calls_p_P₂: c ∈ calls_n P₂,
      have c_not_in_calls_p_P₂: c ∉ calls_n P₂, from set.forall_not_mem_of_eq_empty no_calls_n_in_P₂ c,
      show «false», from c_not_in_calls_p_P₂ c_in_calls_p_P₂
    )
  ),
  have h3: quantifiers_p (P₁ ⋁ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_p (P₁ ⋁ P₂),
    have q ∈ quantifiers_p P₁ ∨ q ∈ quantifiers_p P₂, from prop.has_quantifier_p.or.inv this,
    or.elim this (
      assume q_in_quantifiers_p_P₁: q ∈ quantifiers_p P₁,
      have q_not_in_quantifiers_p_P₁: q ∉ quantifiers_p P₁, from set.forall_not_mem_of_eq_empty no_quantifiers_p_in_P₁ q,
      show «false», from q_not_in_quantifiers_p_P₁ q_in_quantifiers_p_P₁
    ) (
      assume q_in_quantifiers_p_P₂: q ∈ quantifiers_p P₂,
      have q_not_in_quantifiers_p_P₂: q ∉ quantifiers_p P₂, from set.forall_not_mem_of_eq_empty no_quantifiers_p_in_P₂ q,
      show «false», from q_not_in_quantifiers_p_P₂ q_in_quantifiers_p_P₂
    )
  ),
  have h4: quantifiers_n (P₁ ⋁ P₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n (P₁ ⋁ P₂),
    have q ∈ quantifiers_n P₁ ∨ q ∈ quantifiers_n P₂, from prop.has_quantifier_n.or.inv this,
    or.elim this (
      assume q_in_quantifiers_p_P₁: q ∈ quantifiers_n P₁,
      have q_not_in_quantifiers_p_P₁: q ∉ quantifiers_n P₁, from set.forall_not_mem_of_eq_empty no_quantifiers_n_in_P₁ q,
      show «false», from q_not_in_quantifiers_p_P₁ q_in_quantifiers_p_P₁
    ) (
      assume q_in_quantifiers_p_P₂: q ∈ quantifiers_n P₂,
      have q_not_in_quantifiers_p_P₂: q ∉ quantifiers_n P₂, from set.forall_not_mem_of_eq_empty no_quantifiers_n_in_P₂ q,
      show «false», from q_not_in_quantifiers_p_P₂ q_in_quantifiers_p_P₂
    )
  ),
  ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩

lemma no_instantiations.pre {t₁ t₂: term}: no_instantiations (prop.pre t₁ t₂) :=
  have h1: calls_p (prop.pre t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_p (prop.pre t₁ t₂),
    show «false», from prop.has_call_p.pre.inv this
  ),
  have h2: calls_n (prop.pre t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n (prop.pre t₁ t₂),
    show «false», from prop.has_call_n.pre.inv this
  ),
  have h3: quantifiers_p (prop.pre t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_p (prop.pre t₁ t₂),
    show «false», from prop.has_quantifier_p.pre.inv  this
  ),
  have h4: quantifiers_n (prop.pre t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n (prop.pre t₁ t₂),
    show «false», from prop.has_quantifier_n.pre.inv  this
  ),
  ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩

lemma no_instantiations.pre₁ {t: term} {op: unop}: no_instantiations (prop.pre₁ op t) :=
  have h1: calls_p (prop.pre₁ op t) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_p (prop.pre₁ op t),
    show «false», from prop.has_call_p.pre₁.inv this
  ),
  have h2: calls_n (prop.pre₁ op t) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n (prop.pre₁ op t),
    show «false», from prop.has_call_n.pre₁.inv this
  ),
  have h3: quantifiers_p (prop.pre₁ op t) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_p (prop.pre₁ op t),
    show «false», from prop.has_quantifier_p.pre₁.inv  this
  ),
  have h4: quantifiers_n (prop.pre₁ op t) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n (prop.pre₁ op t),
    show «false», from prop.has_quantifier_n.pre₁.inv  this
  ),
  ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩

lemma no_instantiations.pre₂ {t₁ t₂: term} {op: binop}: no_instantiations (prop.pre₂ op t₁ t₂) :=
  have h1: calls_p (prop.pre₂ op t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_p (prop.pre₂ op t₁ t₂),
    show «false», from prop.has_call_p.pre₂.inv this
  ),
  have h2: calls_n (prop.pre₂ op t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n (prop.pre₂ op t₁ t₂),
    show «false», from prop.has_call_n.pre₂.inv this
  ),
  have h3: quantifiers_p (prop.pre₂ op t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_p (prop.pre₂ op t₁ t₂),
    show «false», from prop.has_quantifier_p.pre₂.inv  this
  ),
  have h4: quantifiers_n (prop.pre₂ op t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n (prop.pre₂ op t₁ t₂),
    show «false», from prop.has_quantifier_n.pre₂.inv  this
  ),
  ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩

lemma no_instantiations.post {t₁ t₂: term}: no_instantiations (prop.post t₁ t₂) :=
  have h1: calls_p (prop.post t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_p (prop.post t₁ t₂),
    show «false», from prop.has_call_p.post.inv this
  ),
  have h2: calls_n (prop.post t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume c: calltrigger,
    assume : c ∈ calls_n (prop.post t₁ t₂),
    show «false», from prop.has_call_n.post.inv this
  ),
  have h3: quantifiers_p (prop.post t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_p (prop.post t₁ t₂),
    show «false», from prop.has_quantifier_p.post.inv  this
  ),
  have h4: quantifiers_n (prop.post t₁ t₂) = ∅, from set.eq_empty_of_forall_not_mem (
    assume q: callquantifier,
    assume : q ∈ quantifiers_n (prop.post t₁ t₂),
    show «false», from prop.has_quantifier_n.post.inv  this
  ),
  ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩

lemma prop.erased_n.implies {P Q: prop}:
      (prop.implies P Q).erased_n = vc.implies P.erased_p Q.erased_n :=
  by calc 
       (prop.implies P Q).erased_n = (prop.or (prop.not P) Q).erased_n : rfl
                             ... = ((prop.not P).erased_n ⋁ Q.erased_n) : by unfold prop.erased_n
                             ... = ((vc.not P.erased_p) ⋁ Q.erased_n) : by unfold prop.erased_n

lemma prop.erased_p.implies {P Q: prop}:
      (prop.implies P Q).erased_p = vc.implies P.erased_n Q.erased_p :=
  by calc 
       (prop.implies P Q).erased_p = (prop.or (prop.not P) Q).erased_p : rfl
                               ... = ((prop.not P).erased_p ⋁ Q.erased_p) : by unfold prop.erased_p
                               ... = (vc.not P.erased_n ⋁ Q.erased_p) : by unfold prop.erased_p

lemma free_of_erased_n_free {x: var} {P: prop}: (x ∈ FV P.erased_n ∨ x ∈ FV P.erased_p) → x ∈ FV P :=
  assume x_free_in_erased_n_or_erased_p,
  begin
    induction P,
    case prop.term t { from (
      or.elim x_free_in_erased_n_or_erased_p
      (
        assume x_free_in_t: free_in_vc x (prop.term t).erased_n,
        have (prop.term t).erased_n = vc.term t, by unfold prop.erased_n,
        have free_in_vc x (vc.term t), from this ▸ x_free_in_t,
        have free_in_term x t, from free_in_vc.term.inv this,
        show free_in_prop x (prop.term t), from free_in_prop.term this
      ) (
        assume x_free_in_t: free_in_vc x (prop.term t).erased_p,
        have (prop.term t).erased_p = vc.term t, by unfold prop.erased_p,
        have free_in_vc x (vc.term t), from this ▸ x_free_in_t,
        have free_in_term x t, from free_in_vc.term.inv this,
        show free_in_prop x (prop.term t), from free_in_prop.term this
      )
    )},
    case prop.not P₁ ih { from (
      or.elim x_free_in_erased_n_or_erased_p
      (
        assume x_free: x ∈ FV (prop.not P₁).erased_n,
        have (prop.not P₁).erased_n = vc.not P₁.erased_p, by unfold prop.erased_n,
        have x ∈ FV (vc.not P₁.erased_p), from this ▸ x_free,
        have x ∈ FV P₁.erased_p, from free_in_vc.not.inv this,
        have x ∈ FV P₁, from ih (or.inr this),
        show x ∈ FV P₁.not, from free_in_prop.not this
      ) (
        assume x_free: x ∈ FV (prop.not P₁).erased_p,
        have (prop.not P₁).erased_p = vc.not P₁.erased_n, by unfold prop.erased_p,
        have x ∈ FV (vc.not P₁.erased_n), from this ▸ x_free,
        have x ∈ FV P₁.erased_n, from free_in_vc.not.inv this,
        have x ∈ FV P₁, from ih (or.inl this),
        show x ∈ FV P₁.not, from free_in_prop.not this
      )
    )},
    case prop.and P₁ P₂ P₁_ih P₂_ih { from (
      or.elim x_free_in_erased_n_or_erased_p (
        assume x_free: x ∈ FV (P₁ ⋀ P₂).erased_n,
        have (prop.and P₁ P₂).erased_n = (P₁.erased_n ⋀ P₂.erased_n), by unfold prop.erased_n,
        have x ∈ FV (P₁.erased_n ⋀ P₂.erased_n), from this ▸ x_free,
        have x ∈ FV P₁.erased_n ∨ x ∈ FV P₂.erased_n, from free_in_vc.and.inv this,
        or.elim this (
          assume : x ∈ FV P₁.erased_n,
          have x ∈ FV P₁, from P₁_ih (or.inl this),
          show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₁ this
        ) (
          assume : x ∈ FV P₂.erased_n,
          have x ∈ FV P₂, from P₂_ih (or.inl this),
          show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₂ this
        )
      ) (
        assume x_free: x ∈ FV (P₁ ⋀ P₂).erased_p,
        have (prop.and P₁ P₂).erased_p = (P₁.erased_p ⋀ P₂.erased_p), by unfold prop.erased_p,
        have x ∈ FV (P₁.erased_p ⋀ P₂.erased_p), from this ▸ x_free,
        have x ∈ FV P₁.erased_p ∨ x ∈ FV P₂.erased_p, from free_in_vc.and.inv this,
        or.elim this (
          assume : x ∈ FV P₁.erased_p,
          have x ∈ FV P₁, from P₁_ih (or.inr this),
          show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₁ this
        ) (
          assume : x ∈ FV P₂.erased_p,
          have x ∈ FV P₂, from P₂_ih (or.inr this),
          show x ∈ FV (P₁ ⋀ P₂), from free_in_prop.and₂ this
        )
      )
    )},
    case prop.or P₁ P₂ P₁_ih P₂_ih { from (
      or.elim x_free_in_erased_n_or_erased_p (
        assume x_free: x ∈ FV (P₁ ⋁ P₂).erased_n,
        have (prop.or P₁ P₂).erased_n = (P₁.erased_n ⋁ P₂.erased_n), by unfold prop.erased_n,
        have x ∈ FV (P₁.erased_n ⋁ P₂.erased_n), from this ▸ x_free,
        have x ∈ FV P₁.erased_n ∨ x ∈ FV P₂.erased_n, from free_in_vc.or.inv this,
        or.elim this (
          assume : x ∈ FV P₁.erased_n,
          have x ∈ FV P₁, from P₁_ih (or.inl this),
          show x ∈ FV (P₁ ⋁ P₂), from free_in_prop.or₁ this
        ) (
          assume : x ∈ FV P₂.erased_n,
          have x ∈ FV P₂, from P₂_ih (or.inl this),
          show x ∈ FV (P₁ ⋁ P₂), from free_in_prop.or₂ this
        )
      ) (
        assume x_free: x ∈ FV (P₁ ⋁ P₂).erased_p,
        have (prop.or P₁ P₂).erased_p = (P₁.erased_p ⋁ P₂.erased_p), by unfold prop.erased_p,
        have x ∈ FV (P₁.erased_p ⋁ P₂.erased_p), from this ▸ x_free,
        have x ∈ FV P₁.erased_p ∨ x ∈ FV P₂.erased_p, from free_in_vc.or.inv this,
        or.elim this (
          assume : x ∈ FV P₁.erased_p,
          have x ∈ FV P₁, from P₁_ih (or.inr this),
          show x ∈ FV (P₁ ⋁ P₂), from free_in_prop.or₁ this
        ) (
          assume : x ∈ FV P₂.erased_p,
          have x ∈ FV P₂, from P₂_ih (or.inr this),
          show x ∈ FV (P₁ ⋁ P₂), from free_in_prop.or₂ this
        )
      )
    )},
    case prop.pre t₁ t₂ { from (
      or.elim x_free_in_erased_n_or_erased_p (
        assume x_free: x ∈ FV (prop.pre t₁ t₂).erased_n,
        have (prop.pre t₁ t₂).erased_n = vc.pre t₁ t₂, by unfold prop.erased_n,
        have x ∈ FV (vc.pre t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.pre.inv this,
        or.elim this (
          assume : x ∈ FV t₁,
          show free_in_prop x (prop.pre t₁ t₂), from free_in_prop.pre₁ this
        ) (
          assume : x ∈ FV t₂,
          show free_in_prop x (prop.pre t₁ t₂), from free_in_prop.pre₂ this
        )
      ) (
        assume x_free: x ∈ FV (prop.pre t₁ t₂).erased_p,
        have (prop.pre t₁ t₂).erased_p = vc.pre t₁ t₂, by unfold prop.erased_p,
        have x ∈ FV (vc.pre t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.pre.inv this,
        or.elim this (
          assume : x ∈ FV t₁,
          show free_in_prop x (prop.pre t₁ t₂), from free_in_prop.pre₁ this
        ) (
          assume : x ∈ FV t₂,
          show free_in_prop x (prop.pre t₁ t₂), from free_in_prop.pre₂ this
        )
      )
    )},
    case prop.pre₁ op t { from (
      or.elim x_free_in_erased_n_or_erased_p (
        assume x_free_in_t: free_in_vc x (prop.pre₁ op t).erased_n,
        have (prop.pre₁ op t).erased_n = vc.pre₁ op t, by unfold prop.erased_n,
        have free_in_vc x (vc.pre₁ op t), from this ▸ x_free_in_t,
        have free_in_term x t, from free_in_vc.pre₁.inv this,
        show free_in_prop x (prop.pre₁ op t), from free_in_prop.preop this
      ) (
        assume x_free_in_t: free_in_vc x (prop.pre₁ op t).erased_p,
        have (prop.pre₁ op t).erased_p = vc.pre₁ op t, by unfold prop.erased_p,
        have free_in_vc x (vc.pre₁ op t), from this ▸ x_free_in_t,
        have free_in_term x t, from free_in_vc.pre₁.inv this,
        show free_in_prop x (prop.pre₁ op t), from free_in_prop.preop this
      )
    )},
    case prop.pre₂ op t₁ t₂ { from (
      or.elim x_free_in_erased_n_or_erased_p (
        assume x_free: x ∈ FV (prop.pre₂ op t₁ t₂).erased_n,
        have (prop.pre₂ op t₁ t₂).erased_n = vc.pre₂ op t₁ t₂, by unfold prop.erased_n,
        have x ∈ FV (vc.pre₂ op t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.pre₂.inv this,
        or.elim this (
          assume : x ∈ FV t₁,
          show free_in_prop x (prop.pre₂ op t₁ t₂), from free_in_prop.preop₁ this
        ) (
          assume : x ∈ FV t₂,
          show free_in_prop x (prop.pre₂ op t₁ t₂), from free_in_prop.preop₂ this
        )
      ) (
        assume x_free: x ∈ FV (prop.pre₂ op t₁ t₂).erased_p,
        have (prop.pre₂ op t₁ t₂).erased_p = vc.pre₂ op t₁ t₂, by unfold prop.erased_p,
        have x ∈ FV (vc.pre₂ op t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.pre₂.inv this,
        or.elim this (
          assume : x ∈ FV t₁,
          show free_in_prop x (prop.pre₂ op t₁ t₂), from free_in_prop.preop₁ this
        ) (
          assume : x ∈ FV t₂,
          show free_in_prop x (prop.pre₂ op t₁ t₂), from free_in_prop.preop₂ this
        )
      )
    )},
    case prop.post t₁ t₂ { from (
      or.elim x_free_in_erased_n_or_erased_p (
        assume x_free: x ∈ FV (prop.post t₁ t₂).erased_n,
        have (prop.post t₁ t₂).erased_n = vc.post t₁ t₂, by unfold prop.erased_n,
        have x ∈ FV (vc.post t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.post.inv this,
        or.elim this (
          assume : x ∈ FV t₁,

          show free_in_prop x (prop.post t₁ t₂), from free_in_prop.post₁ this
        ) (
          assume : x ∈ FV t₂,

          show free_in_prop x (prop.post t₁ t₂), from free_in_prop.post₂ this
        )
      ) (
        assume x_free: x ∈ FV (prop.post t₁ t₂).erased_p,
        have (prop.post t₁ t₂).erased_p = vc.post t₁ t₂, by unfold prop.erased_p,
        have x ∈ FV (vc.post t₁ t₂), from this ▸ x_free,
        have x ∈ FV t₁ ∨ x ∈ FV t₂, from free_in_vc.post.inv this,
        or.elim this (
          assume : x ∈ FV t₁,

          show free_in_prop x (prop.post t₁ t₂), from free_in_prop.post₁ this
        ) (
          assume : x ∈ FV t₂,

          show free_in_prop x (prop.post t₁ t₂), from free_in_prop.post₂ this
        )
      )
    )},
    case prop.call t { from (
      or.elim x_free_in_erased_n_or_erased_p (
        assume x_free: x ∈ FV (prop.call t).erased_n,
        have (prop.call t).erased_n = vc.term value.true, by unfold prop.erased_n,
        have x ∈ FV (vc.term value.true), from this ▸ x_free,
        have x ∈ FV (term.value value.true), from free_in_vc.term.inv this,
        absurd this (free_in_term.value.inv)
      ) (
        assume x_free: x ∈ FV (prop.call t).erased_p,
        have (prop.call t).erased_p = vc.term value.true, by unfold prop.erased_p,
        have x ∈ FV (vc.term value.true), from this ▸ x_free,
        have x ∈ FV (term.value value.true), from free_in_vc.term.inv this,
        absurd this (free_in_term.value.inv)
      )
    )},
    case prop.forallc y P₁ ih { from (
      or.elim x_free_in_erased_n_or_erased_p (
        assume x_free: x ∈ FV (prop.forallc y P₁).erased_n,
        have (prop.forallc y P₁).erased_n = vc.univ y P₁.erased_n, by unfold prop.erased_n,
        have x ∈ FV (vc.univ y P₁.erased_n), from this ▸ x_free,
        have h2: (x ≠ y) ∧ free_in_vc x P₁.erased_n, from free_in_vc.univ.inv this,
        have x ∈ FV P₁, from ih (or.inl h2.right),
        show x ∈ FV (prop.forallc y P₁), from free_in_prop.forallc h2.left this
      ) (
        assume x_free: x ∈ FV (prop.forallc y P₁).erased_p,
        have (prop.forallc y P₁).erased_p = vc.term value.true, by unfold prop.erased_p,
        have x ∈ FV (vc.term value.true), from this ▸ x_free,
        have x ∈ FV (term.value value.true), from free_in_vc.term.inv this,
        absurd this (free_in_term.value.inv)
      )
    )},
    case prop.exis y P₁ ih { from (
      or.elim x_free_in_erased_n_or_erased_p (
        assume x_free: x ∈ FV (prop.exis y P₁).erased_n,
        have (prop.exis y P₁).erased_n = vc.not (vc.univ y (vc.not P₁.erased_n)), by unfold prop.erased_n,
        have x ∈ FV (vc.not (vc.univ y (vc.not P₁.erased_n))), from this ▸ x_free,
        have x ∈ FV (vc.univ y (vc.not P₁.erased_n)), from free_in_vc.not.inv this,
        have h2: (x ≠ y) ∧ free_in_vc x (vc.not P₁.erased_n), from free_in_vc.univ.inv this,
        have h3: x ∈ FV P₁.erased_n, from free_in_vc.not.inv h2.right,
        have x ∈ FV P₁, from ih (or.inl h3),
        show x ∈ FV (prop.exis y P₁), from free_in_prop.exis h2.left this
      )
      (
        assume x_free: x ∈ FV (prop.exis y P₁).erased_p,
        have (prop.exis y P₁).erased_p = vc.not (vc.univ y (vc.not P₁.erased_p)), by unfold prop.erased_p,
        have x ∈ FV (vc.not (vc.univ y (vc.not P₁.erased_p))), from this ▸ x_free,
        have x ∈ FV (vc.univ y (vc.not P₁.erased_p)), from free_in_vc.not.inv this,
        have h2: (x ≠ y) ∧ free_in_vc x (vc.not P₁.erased_p), from free_in_vc.univ.inv this,
        have h3: x ∈ FV P₁.erased_p, from free_in_vc.not.inv h2.right,
        have x ∈ FV P₁, from ih (or.inr h3),
        show x ∈ FV (prop.exis y P₁), from free_in_prop.exis h2.left this
      )
    )}
  end

lemma free_of_erased_free {x: var} {P: prop}: (x ∈ FV P.erased_p ∨ x ∈ FV P.erased_n) → x ∈ FV P :=
  assume : x ∈ FV P.erased_p ∨ x ∈ FV P.erased_n,
  have x ∈ FV P.erased_n ∨ x ∈ FV P.erased_p, from this.symm,
  show x ∈ FV P, from free_of_erased_n_free this

lemma prop.has_call_p.and_union {P₁ P₂: prop}:
      calls_p (P₁ ⋀ P₂) = calls_p P₁ ∪ calls_p P₂ :=
  set.eq_of_subset_of_subset (
    assume c: calltrigger,
    assume : c ∈ calls_p (P₁ ⋀ P₂),
    or.elim (prop.has_call_p.and.inv this) (
      assume : c ∈ calls_p P₁,
      show c ∈ calls_p P₁ ∪ calls_p P₂, from set.mem_union_left (calls_p P₂) this
    ) (
      assume : c ∈ calls_p P₂,
      show c ∈ calls_p P₁ ∪ calls_p P₂, from set.mem_union_right (calls_p P₁) this
    )
  ) (
    assume c: calltrigger,
    assume : c ∈ calls_p P₁ ∪ calls_p P₂,
    or.elim (set.mem_or_mem_of_mem_union this) (
      assume : c ∈ calls_p P₁,
      show c ∈ calls_p (P₁ ⋀ P₂), from prop.has_call_p.and₁ this
    ) (
      assume : c ∈ calls_p P₂,
      show c ∈ calls_p (P₁ ⋀ P₂), from prop.has_call_p.and₂ this
    )
  )

lemma prop.has_call_p.and.symm {P₁ P₂: prop}:
      calls_p (P₁ ⋀ P₂) = calls_p (P₂ ⋀ P₁) :=
  set.eq_of_subset_of_subset (
    assume c: calltrigger,
    assume : c ∈ calls_p (P₁ ⋀ P₂),
    or.elim (prop.has_call_p.and.inv this) (
      assume : c ∈ calls_p P₁,
      show c ∈ calls_p (P₂ ⋀ P₁), from prop.has_call_p.and₂ this
    ) (
      assume : c ∈ calls_p P₂,
      show c ∈ calls_p (P₂ ⋀ P₁), from prop.has_call_p.and₁ this
    )
  ) (
    assume c: calltrigger,
    assume : c ∈ calls_p (P₂ ⋀ P₁),
    or.elim (prop.has_call_p.and.inv this) (
      assume : c ∈ calls_p P₂,
      show c ∈ calls_p (P₁ ⋀ P₂), from prop.has_call_p.and₂ this
    ) (
      assume : c ∈ calls_p P₁,
      show c ∈ calls_p (P₁ ⋀ P₂), from prop.has_call_p.and₁ this
    )
  )

lemma prop.has_quantifier_p.and.symm {P₁ P₂: prop}:
      quantifiers_p (P₁ ⋀ P₂) = quantifiers_p (P₂ ⋀ P₁) :=
  set.eq_of_subset_of_subset (
    assume q: callquantifier,
    assume : q ∈ quantifiers_p (P₁ ⋀ P₂),
    or.elim (prop.has_quantifier_p.and.inv this) (
      assume : q ∈ quantifiers_p P₁,
      show q ∈ quantifiers_p (P₂ ⋀ P₁), from prop.has_quantifier_p.and₂ this
    ) (
      assume : q ∈ quantifiers_p P₂,
      show q ∈ quantifiers_p (P₂ ⋀ P₁), from prop.has_quantifier_p.and₁ this
    )
  ) (
    assume q: callquantifier,
    assume : q ∈ quantifiers_p (P₂ ⋀ P₁),
    or.elim (prop.has_quantifier_p.and.inv this) (
      assume : q ∈ quantifiers_p P₂,
      show q ∈ quantifiers_p (P₁ ⋀ P₂), from prop.has_quantifier_p.and₂ this
    ) (
      assume : q ∈ quantifiers_p P₁,
      show q ∈ quantifiers_p (P₁ ⋀ P₂), from prop.has_quantifier_p.and₁ this
    )
  )

lemma prop.has_call_p.and.comm {P₁ P₂ P₃: prop}:
      calls_p (P₁ ⋀ P₂ ⋀ P₃) = calls_p ((P₁ ⋀ P₂) ⋀ P₃) :=
  set.eq_of_subset_of_subset (
    assume c: calltrigger,
    assume : c ∈ calls_p (P₁ ⋀ P₂ ⋀ P₃),
    or.elim (prop.has_call_p.and.inv this) (
      assume : c ∈ calls_p P₁,
      have c ∈ calls_p (P₁ ⋀ P₂), from prop.has_call_p.and₁ this,
      show c ∈ calls_p ((P₁ ⋀ P₂) ⋀ P₃), from prop.has_call_p.and₁ this
    ) (
      assume : c ∈ calls_p (P₂ ⋀ P₃),
      or.elim (prop.has_call_p.and.inv this) (
        assume : c ∈ calls_p P₂,
        have c ∈ calls_p (P₁ ⋀ P₂), from prop.has_call_p.and₂ this,
        show c ∈ calls_p ((P₁ ⋀ P₂) ⋀ P₃), from prop.has_call_p.and₁ this
      ) (
        assume : c ∈ calls_p P₃,
        show c ∈ calls_p ((P₁ ⋀ P₂) ⋀ P₃), from prop.has_call_p.and₂ this
      )
    )
  ) (
    assume c: calltrigger,
    assume : c ∈ calls_p ((P₁ ⋀ P₂) ⋀ P₃),
    or.elim (prop.has_call_p.and.inv this) (
      assume : c ∈ calls_p (P₁ ⋀ P₂),
      or.elim (prop.has_call_p.and.inv this) (
        assume : c ∈ calls_p P₁,
        show c ∈ calls_p (P₁ ⋀ P₂ ⋀ P₃), from prop.has_call_p.and₁ this
      ) (
        assume : c ∈ calls_p P₂,
        have c ∈ calls_p (P₂ ⋀ P₃), from prop.has_call_p.and₁ this,
        show c ∈ calls_p (P₁ ⋀ P₂ ⋀ P₃), from prop.has_call_p.and₂ this
      )
    ) (
      assume : c ∈ calls_p P₃,
      have c ∈ calls_p (P₂ ⋀ P₃), from prop.has_call_p.and₂ this,
      show c ∈ calls_p (P₁ ⋀ P₂ ⋀ P₃), from prop.has_call_p.and₂ this
    )
  )

lemma prop.has_quantifier_p.and.comm {P₁ P₂ P₃: prop}:
      quantifiers_p (P₁ ⋀ P₂ ⋀ P₃) = quantifiers_p ((P₁ ⋀ P₂) ⋀ P₃) :=
  set.eq_of_subset_of_subset (
    assume q: callquantifier,
    assume : q ∈ quantifiers_p (P₁ ⋀ P₂ ⋀ P₃),
    or.elim (prop.has_quantifier_p.and.inv this) (
      assume : q ∈ quantifiers_p P₁,
      have q ∈ quantifiers_p (P₁ ⋀ P₂), from prop.has_quantifier_p.and₁ this,
      show q ∈ quantifiers_p ((P₁ ⋀ P₂) ⋀ P₃), from prop.has_quantifier_p.and₁ this
    ) (
      assume : q ∈ quantifiers_p (P₂ ⋀ P₃),
      or.elim (prop.has_quantifier_p.and.inv this) (
        assume : q ∈ quantifiers_p P₂,
        have q ∈ quantifiers_p (P₁ ⋀ P₂), from prop.has_quantifier_p.and₂ this,
        show q ∈ quantifiers_p ((P₁ ⋀ P₂) ⋀ P₃), from prop.has_quantifier_p.and₁ this
      ) (
        assume : q ∈ quantifiers_p P₃,
        show q ∈ quantifiers_p ((P₁ ⋀ P₂) ⋀ P₃), from prop.has_quantifier_p.and₂ this
      )
    )
  ) (
    assume q: callquantifier,
    assume : q ∈ quantifiers_p ((P₁ ⋀ P₂) ⋀ P₃),
    or.elim (prop.has_quantifier_p.and.inv this) (
      assume : q ∈ quantifiers_p (P₁ ⋀ P₂),
      or.elim (prop.has_quantifier_p.and.inv this) (
        assume : q ∈ quantifiers_p P₁,
        show q ∈ quantifiers_p (P₁ ⋀ P₂ ⋀ P₃), from prop.has_quantifier_p.and₁ this
      ) (
        assume : q ∈ quantifiers_p P₂,
        have q ∈ quantifiers_p (P₂ ⋀ P₃), from prop.has_quantifier_p.and₁ this,
        show q ∈ quantifiers_p (P₁ ⋀ P₂ ⋀ P₃), from prop.has_quantifier_p.and₂ this
      )
    ) (
      assume : q ∈ quantifiers_p P₃,
      have q ∈ quantifiers_p (P₂ ⋀ P₃), from prop.has_quantifier_p.and₂ this,
      show q ∈ quantifiers_p (P₁ ⋀ P₂ ⋀ P₃), from prop.has_quantifier_p.and₂ this
    )
  )

lemma same_calls_p_and_left {P P' Q: prop} {σ: env}:
      calls_p_subst σ P' ⊆ calls_p_subst σ P → (calls_p_subst σ (P' ⋀ Q) ⊆ calls_p_subst σ (P ⋀ Q)) :=
  assume calls_P'_P: calls_p_subst σ P' ⊆ calls_p_subst σ P,
  assume c: calltrigger,
  assume : c ∈ calls_p_subst σ (P' ⋀ Q),
  or.elim (prop.has_call_p_subst.and.inv this) (
    assume : c ∈ calls_p_subst σ P',
    have c ∈ calls_p_subst σ P, from set.mem_of_mem_of_subset this calls_P'_P,
    show c ∈ calls_p_subst σ (P ⋀ Q), from prop.has_call_p_subst.and₁ this
  )
  (
    assume : c ∈ calls_p_subst σ Q,
    show c ∈ calls_p_subst σ (P ⋀ Q), from prop.has_call_p_subst.and₂ this
  )

lemma prop.has_call_of_subst_has_call {P: prop} {c: calltrigger} {y: var} {v: value}:
          (c ∈ calls_p (prop.subst y v P) → ∃c', c' ∈ calls_p P) ∧
          (c ∈ calls_n (prop.subst y v P) → ∃c', c' ∈ calls_n P) :=
  begin
    induction P,
    case prop.term t {
      split,

      intro h,
      unfold prop.subst at h,
      cases h,

      intro h,
      unfold prop.subst at h,
      cases h
    },
    case prop.not P₁ P₁_ih {
      split,

      intro h,
      unfold prop.subst at h,
      have h2, from prop.has_call_p.not.inv h,
      have h3, from P₁_ih.right h2,
      cases h3 with c' a,
      from ⟨c', prop.has_call_p.not a⟩,

      intro h,
      unfold prop.subst at h,
      have h2, from prop.has_call_n.not.inv h,
      have h3, from P₁_ih.left h2,
      cases h3 with c' h3,
      from ⟨c', prop.has_call_n.not h3⟩,
    },
    case prop.and P₂ P₃ P₂_ih P₃_ih {
      split,

      intro h,
      unfold prop.subst at h,
      have h2, from prop.has_call_p.and.inv h,
      cases h2,
      have h3, from P₂_ih.left a,
      cases h3 with c' h3,
      from ⟨c', prop.has_call_p.and₁ h3⟩,
      have h3, from P₃_ih.left a,
      cases h3 with c' h3,
      from ⟨c', prop.has_call_p.and₂ h3⟩,

      intro h,
      unfold prop.subst at h,
      have h2, from prop.has_call_n.and.inv h,
      cases h2,
      have h3, from P₂_ih.right a,
      cases h3 with c' h3,
      from ⟨c', prop.has_call_n.and₁ h3⟩,
      have h3, from P₃_ih.right a,
      cases h3 with c' h3,
      from ⟨c', prop.has_call_n.and₂ h3⟩,
    },
    case prop.or P₄ P₅ P₄_ih P₅_ih {
      split,

      intro h,
      unfold prop.subst at h,
      have h2, from prop.has_call_p.or.inv h,
      cases h2,
      have h3, from P₄_ih.left a,
      cases h3 with c' h3,
      from ⟨c', prop.has_call_p.or₁ h3⟩,
      have h3, from P₅_ih.left a,
      cases h3 with c' h3,
      from ⟨c', prop.has_call_p.or₂ h3⟩,

      intro h,
      unfold prop.subst at h,
      have h2, from prop.has_call_n.or.inv h,
      cases h2,
      have h3, from P₄_ih.right a,
      cases h3 with c' h3,
      from ⟨c', prop.has_call_n.or₁ h3⟩,
      have h3, from P₅_ih.right a,
      cases h3 with c' h3,
      from ⟨c', prop.has_call_n.or₂ h3⟩,
    },
    case prop.pre t₁ t₂ {
      split,

      intro h,
      unfold prop.subst at h,
      cases h,

      intro h,
      unfold prop.subst at h,
      cases h
    },
    case prop.pre₁ op t {
      split,

      intro h,
      unfold prop.subst at h,
      cases h,

      intro h,
      unfold prop.subst at h,
      cases h
    },
    case prop.pre₂ op t₁ t₂ {
      split,

      intro h,
      unfold prop.subst at h,
      cases h,

      intro h,
      unfold prop.subst at h,
      cases h
    },
    case prop.post t₁ t₂ {
      split,

      intro h,
      unfold prop.subst at h,
      cases h,

      intro h,
      unfold prop.subst at h,
      cases h
    },
    case prop.call t {
      split,

      intro h,
      existsi (calltrigger.mk t),
      apply prop.has_call_p.calltrigger,

      intro h,
      unfold prop.subst at h,
      cases h
    },
    case prop.forallc z t P ih {
      split,

      intro h,
      unfold prop.subst at h,
      cases h,

      intro h,
      unfold prop.subst at h,
      cases h
    },
    case prop.exis z P ih {
      split,

      intro h,
      unfold prop.subst at h,
      cases h,

      intro h,
      unfold prop.subst at h,
      cases h
    }
  end

lemma prop.has_call_of_subst_env_has_call {P: prop} {σ: env}:
          (∀c, c ∈ calls_p (prop.subst_env σ P) → ∃c', c' ∈ calls_p P) ∧
          (∀c, c ∈ calls_n (prop.subst_env σ P) → ∃c', c' ∈ calls_n P) :=
  begin
    induction σ with σ' y v ih,

    split,

    intro c,
    intro h,
    unfold prop.subst_env at h,
    existsi c,
    from h,

    intro c,
    intro h,
    unfold prop.subst_env at h,
    existsi c,
    from h,

    split,

    intro c,
    intro h,
    unfold prop.subst_env at h,
    have h2, from prop.has_call_of_subst_has_call.left h,
    cases h2 with c' h3,
    from ih.left c' h3,

    intro c,
    intro h,
    unfold prop.subst_env at h,
    have h2, from prop.has_call_of_subst_has_call.right h,
    cases h2 with c' h3,
    from ih.right c' h3,
  end

    -- induction P,
    -- case prop.term t {
    -- },
    -- case prop.not P₁ ih {
    -- },
    -- case prop.and P₁ P₂ P₁_ih P₂_ih {
    -- },
    -- case prop.or P₁ P₂ P₁_ih P₂_ih {
    -- },
    -- case prop.pre t₁ t₂ {
    -- },
    -- case prop.pre₁ op t {
    -- },
    -- case prop.pre₂ op t₁ t₂ {
    -- },
    -- case prop.call t {
    -- },
    -- case prop.post t₁ t₂ {
    -- },
    -- case prop.forallc y P₁ P₁_ih {
    -- },
    -- case prop.exis y P₁ P₁_ih {
    -- }

lemma find_calls_equiv_has_call {P: prop} {c: calltrigger}:
       (c ∈ calls_p P ↔ c ∈ P.find_calls_p) ∧ (c ∈ calls_n P ↔ c ∈ P.find_calls_n) :=
  begin
    induction P,
    case prop.term t {
      split,

      split,

      assume h1,
      cases h1,

      assume h1,
      unfold prop.find_calls_p at h1,
      cases h1,

      split,

      assume h1,
      cases h1,

      assume h1,
      unfold prop.find_calls_n at h1,
      cases h1
    },
    case prop.not P₁ ih {
      split,

      split,

      assume h1,
      cases h1,
      have h2: c ∈ calls_n P₁, from a,
      unfold prop.find_calls_p,
      from ih.right.mp h2,

      assume h1,
      unfold prop.find_calls_p at h1,
      have h2, from ih.right.mpr h1,
      unfold has_mem.mem at h2,
      unfold set.mem at h2,
      unfold calls_n at h2,
      unfold has_mem.mem,
      unfold set.mem,
      unfold calls_p,
      from prop.has_call_p.not h2,

      split,

      assume h1,
      cases h1,
      have h2: c ∈ calls_p P₁, from a,
      unfold prop.find_calls_n,
      from ih.left.mp h2,

      assume h1,
      unfold prop.find_calls_n at h1,
      have h2, from ih.left.mpr h1,
      unfold has_mem.mem at h2,
      unfold set.mem at h2,
      unfold calls_p at h2,
      unfold has_mem.mem,
      unfold set.mem,
      unfold calls_n,
      from prop.has_call_n.not h2
    },
    case prop.and P₁ P₂ P₁_ih P₂_ih {
      split,

      split,

      assume h1,
      cases h1,

      have h2: c ∈ calls_p P₁, from a,
      unfold prop.find_calls_p,
      apply list.mem_append.mpr,
      left,
      from P₁_ih.left.mp h2,

      have h2: c ∈ calls_p P₂, from a,
      unfold prop.find_calls_p,
      apply list.mem_append.mpr,
      right,
      from P₂_ih.left.mp h2,

      assume h1,
      change prop.has_call_p c (prop.and P₁ P₂),

      unfold prop.find_calls_p at h1,
      have h2, from list.mem_append.mp h1,
      cases h2,
      have h3, from P₁_ih.left.mpr a,
      have h4: prop.has_call_p c P₁, from h3,
      from prop.has_call_p.and₁ h4,

      have h3, from P₂_ih.left.mpr a,
      have h4: prop.has_call_p c P₂, from h3,
      from prop.has_call_p.and₂ h4,

      split,

      assume h1,
      cases h1,

      have h2: c ∈ calls_n P₁, from a,
      unfold prop.find_calls_n,
      apply list.mem_append.mpr,
      left,
      from P₁_ih.right.mp h2,

      have h2: c ∈ calls_n P₂, from a,
      unfold prop.find_calls_n,
      apply list.mem_append.mpr,
      right,
      from P₂_ih.right.mp h2,

      assume h1,
      change prop.has_call_n c (prop.and P₁ P₂),

      unfold prop.find_calls_n at h1,
      have h2, from list.mem_append.mp h1,
      cases h2,
      have h3, from P₁_ih.right.mpr a,
      have h4: prop.has_call_n c P₁, from h3,
      from prop.has_call_n.and₁ h4,

      have h3, from P₂_ih.right.mpr a,
      have h4: prop.has_call_n c P₂, from h3,
      from prop.has_call_n.and₂ h4
    },
    case prop.or P₁ P₂ P₁_ih P₂_ih {
      split,

      split,

      assume h1,
      cases h1,

      have h2: c ∈ calls_p P₁, from a,
      unfold prop.find_calls_p,
      apply list.mem_append.mpr,
      left,
      from P₁_ih.left.mp h2,

      have h2: c ∈ calls_p P₂, from a,
      unfold prop.find_calls_p,
      apply list.mem_append.mpr,
      right,
      from P₂_ih.left.mp h2,

      assume h1,
      change prop.has_call_p c (prop.or P₁ P₂),

      unfold prop.find_calls_p at h1,
      have h2, from list.mem_append.mp h1,
      cases h2,
      have h3, from P₁_ih.left.mpr a,
      have h4: prop.has_call_p c P₁, from h3,
      from prop.has_call_p.or₁ h4,

      have h3, from P₂_ih.left.mpr a,
      have h4: prop.has_call_p c P₂, from h3,
      from prop.has_call_p.or₂ h4,

      split,

      assume h1,
      cases h1,

      have h2: c ∈ calls_n P₁, from a,
      unfold prop.find_calls_n,
      apply list.mem_append.mpr,
      left,
      from P₁_ih.right.mp h2,

      have h2: c ∈ calls_n P₂, from a,
      unfold prop.find_calls_n,
      apply list.mem_append.mpr,
      right,
      from P₂_ih.right.mp h2,

      assume h1,
      change prop.has_call_n c (prop.or P₁ P₂),

      unfold prop.find_calls_n at h1,
      have h2, from list.mem_append.mp h1,
      cases h2,
      have h3, from P₁_ih.right.mpr a,
      have h4: prop.has_call_n c P₁, from h3,
      from prop.has_call_n.or₁ h4,

      have h3, from P₂_ih.right.mpr a,
      have h4: prop.has_call_n c P₂, from h3,
      from prop.has_call_n.or₂ h4
    },
    case prop.pre t₁ t₂ {
      split,

      split,

      assume h1,
      cases h1,

      assume h1,
      unfold prop.find_calls_p at h1,
      cases h1,

      split,

      assume h1,
      cases h1,

      assume h1,
      unfold prop.find_calls_n at h1,
      cases h1
    },
    case prop.pre₁ op t {
      split,

      split,

      assume h1,
      cases h1,

      assume h1,
      unfold prop.find_calls_p at h1,
      cases h1,

      split,

      assume h1,
      cases h1,

      assume h1,
      unfold prop.find_calls_n at h1,
      cases h1
    },
    case prop.pre₂ op t₁ t₂ {
      split,

      split,

      assume h1,
      cases h1,

      assume h1,
      unfold prop.find_calls_p at h1,
      cases h1,

      split,

      assume h1,
      cases h1,

      assume h1,
      unfold prop.find_calls_n at h1,
      cases h1
    },
    case prop.call t {
      split,

      split,

      assume h1,
      cases h1,
      unfold prop.find_calls_p,
      simp,

      assume h1,
      unfold prop.find_calls_p at h1,
      simp at h1,
      change prop.has_call_p c (prop.call t),
      rw[h1],
      from prop.has_call_p.calltrigger,

      split,

      assume h1,
      cases h1,

      assume h1,
      unfold prop.find_calls_n at h1,
      cases h1
    },
    case prop.post t₁ t₂ {
      split,

      split,

      assume h1,
      cases h1,

      assume h1,
      unfold prop.find_calls_p at h1,
      cases h1,

      split,

      assume h1,
      cases h1,

      assume h1,
      unfold prop.find_calls_n at h1,
      cases h1
    },
    case prop.forallc y P₁ P₁_ih {
      split,

      split,

      assume h1,
      cases h1,

      assume h1,
      unfold prop.find_calls_p at h1,
      cases h1,

      split,

      assume h1,
      cases h1,

      assume h1,
      unfold prop.find_calls_n at h1,
      cases h1
    },
    case prop.exis y P₁ P₁_ih {
      split,

      split,

      assume h1,
      cases h1,

      assume h1,
      unfold prop.find_calls_p at h1,
      cases h1,

      split,

      assume h1,
      cases h1,

      assume h1,
      unfold prop.find_calls_n at h1,
      cases h1
    }
  end

lemma subst_distrib_to_vc {P: prop} {x: var} {v: value}:
      (vc.subst x v (prop.to_vc P) = prop.to_vc (prop.subst x v P)) := begin
  induction P,
  case prop.term t {
    unfold prop.subst,
    unfold prop.to_vc,
    unfold vc.subst,
    change (vc.term (term.subst x v t) = prop.to_vc (prop.term (term.subst x v t))),
    unfold prop.to_vc
  },
  case prop.not P₁ ih {
    unfold prop.subst,
    unfold prop.to_vc,
    unfold vc.subst,
    congr,
    from ih
  },
  case prop.and P₁ P₂ P₁_ih P₂_ih {
    unfold prop.subst,
    unfold prop.to_vc,
    change (vc.subst x v (vc.and (prop.to_vc P₁) (prop.to_vc P₂))
           = prop.to_vc (prop.and (prop.subst x v P₁) (prop.subst x v P₂))),
    unfold vc.subst,
    unfold prop.to_vc,
    congr,
    from P₁_ih,
    from P₂_ih
  },
  case prop.or P₁ P₂ P₁_ih P₂_ih {
    unfold prop.subst,
    unfold prop.to_vc,
    change (vc.subst x v (vc.or (prop.to_vc P₁) (prop.to_vc P₂))
           = prop.to_vc (prop.or (prop.subst x v P₁) (prop.subst x v P₂))),
    unfold vc.subst,
    unfold prop.to_vc,
    congr,
    from P₁_ih,
    from P₂_ih
  },
  case prop.pre t₁ t₂ {
    unfold prop.subst,
    unfold prop.to_vc,
    unfold vc.subst
  },
  case prop.pre₁ op t {
    unfold prop.subst,
    unfold prop.to_vc,
    unfold vc.subst
  },
  case prop.pre₂ op t₁ t₂ {
    unfold prop.subst,
    unfold prop.to_vc,
    unfold vc.subst
  },
  case prop.call t {
    unfold prop.subst,
    unfold prop.to_vc,
    unfold vc.subst,
    congr
  },
  case prop.post t₁ t₂ {
    unfold prop.subst,
    unfold prop.to_vc,
    unfold vc.subst
  },
  case prop.forallc y P₁ P₁_ih {
    unfold prop.subst,
    unfold prop.to_vc,
    unfold vc.subst,
    congr,

    by_cases (x = y) with h1,

    simp[h1],

    simp[h1],
    from P₁_ih
  },
  case prop.exis y P₁ P₁_ih {
    unfold prop.subst,
    unfold prop.to_vc,
    unfold vc.subst,
    congr,
    by_cases (x = y) with h1,

    simp[h1],

    simp[h1],
    congr,
    from P₁_ih
  }
end

lemma subst_distrib_erased {P: prop} {x: var} {v: value}:
      (vc.subst x v (prop.erased_p P) = prop.erased_p (prop.subst x v P)) ∧
      (vc.subst x v (prop.erased_n P) = prop.erased_n (prop.subst x v P)) := begin
  induction P,
  case prop.term t {
    split,

    unfold prop.subst,
    unfold prop.erased_p,
    unfold vc.subst,
    change (vc.term (term.subst x v t) = prop.erased_p (prop.term (term.subst x v t))),
    unfold prop.erased_p,

    unfold prop.subst,
    unfold prop.erased_n,
    unfold vc.subst,
    change (vc.term (term.subst x v t) = prop.erased_n (prop.term (term.subst x v t))),
    unfold prop.erased_n
  },
  case prop.not P₁ ih {
    split,

    unfold prop.subst,
    unfold prop.erased_p,
    unfold vc.subst,
    congr,
    from ih.right,

    unfold prop.subst,
    unfold prop.erased_n,
    unfold vc.subst,
    congr,
    from ih.left
  },
  case prop.and P₁ P₂ P₁_ih P₂_ih {
    split,

    unfold prop.subst,
    unfold prop.erased_p,
    change (vc.subst x v (vc.and (prop.erased_p P₁) (prop.erased_p P₂))
           = prop.erased_p (prop.and (prop.subst x v P₁) (prop.subst x v P₂))),
    unfold vc.subst,
    unfold prop.erased_p,
    congr,
    from P₁_ih.left,
    from P₂_ih.left,
    
    unfold prop.subst,
    unfold prop.erased_n,
    change (vc.subst x v (vc.and (prop.erased_n P₁) (prop.erased_n P₂))
           = prop.erased_n (prop.and (prop.subst x v P₁) (prop.subst x v P₂))),
    unfold vc.subst,
    unfold prop.erased_n,
    congr,
    from P₁_ih.right,
    from P₂_ih.right
  },
  case prop.or P₁ P₂ P₁_ih P₂_ih {
    split,

    unfold prop.subst,
    unfold prop.erased_p,
    change (vc.subst x v (vc.or (prop.erased_p P₁) (prop.erased_p P₂))
           = prop.erased_p (prop.or (prop.subst x v P₁) (prop.subst x v P₂))),
    unfold vc.subst,
    unfold prop.erased_p,
    congr,
    from P₁_ih.left,
    from P₂_ih.left,
    
    unfold prop.subst,
    unfold prop.erased_n,
    change (vc.subst x v (vc.or (prop.erased_n P₁) (prop.erased_n P₂))
           = prop.erased_n (prop.or (prop.subst x v P₁) (prop.subst x v P₂))),
    unfold vc.subst,
    unfold prop.erased_n,
    congr,
    from P₁_ih.right,
    from P₂_ih.right
  },
  case prop.pre t₁ t₂ {
    split,

    unfold prop.subst,
    unfold prop.erased_p,
    unfold vc.subst,

    unfold prop.subst,
    unfold prop.erased_n,
    unfold vc.subst
  },
  case prop.pre₁ op t {
    split,

    unfold prop.subst,
    unfold prop.erased_p,
    unfold vc.subst,

    unfold prop.subst,
    unfold prop.erased_n,
    unfold vc.subst
  },
  case prop.pre₂ op t₁ t₂ {
    split,

    unfold prop.subst,
    unfold prop.erased_p,
    unfold vc.subst,

    unfold prop.subst,
    unfold prop.erased_n,
    unfold vc.subst
  },
  case prop.call t {
    split,

    unfold prop.subst,
    unfold prop.erased_p,
    unfold vc.subst,
    congr,


    unfold prop.subst,
    unfold prop.erased_n,
    unfold vc.subst,
    congr
  },
  case prop.post t₁ t₂ {
    split,

    unfold prop.subst,
    unfold prop.erased_p,
    unfold vc.subst,

    unfold prop.subst,
    unfold prop.erased_n,
    unfold vc.subst
  },
  case prop.forallc y P₁ P₁_ih {
    split,

    unfold prop.subst,
    unfold prop.erased_p,
    unfold vc.subst,
    congr,

    unfold prop.subst,
    unfold prop.erased_n,
    unfold vc.subst,
    congr,
    by_cases (x = y) with h1,

    simp[h1],

    simp[h1],
    from P₁_ih.right
  },
  case prop.exis y P₁ P₁_ih {
    split,

    unfold prop.subst,
    unfold prop.erased_p,
    unfold vc.subst,
    congr,
    by_cases (x = y) with h1,

    simp[h1],

    simp[h1],
    congr,
    from P₁_ih.left,

    unfold prop.subst,
    unfold prop.erased_n,
    unfold vc.subst,
    congr,
    by_cases (x = y) with h1,

    simp[h1],

    simp[h1],
    congr,
    from P₁_ih.right
  }
end

lemma to_vc_valid_of_erased_n_valid:
      -- ∀(P: prop), ∀σ, closed_subst σ P → ((σ ⊨ P.erased_n) → σ ⊨ P.to_vc) ∧ ((σ ⊨ P.to_vc) → σ ⊨ P.erased_p)
      ∀(P: prop), ∀σ, ((σ ⊨ P.erased_n) → σ ⊨ P.to_vc) ∧ ((σ ⊨ P.to_vc) → σ ⊨ P.erased_p)
| (prop.term t) := begin
    assume σ,
    split,

    unfold prop.erased_n,
    unfold prop.to_vc,
    from id,

    unfold prop.erased_p,
    unfold prop.to_vc,
    from id
  end
| (prop.not P₁) :=
  have rec_wf: P₁.simplesize < (prop.not P₁).simplesize, from simplesize_prop_not,
  begin
    assume σ,
    split,

    unfold prop.erased_n,
    unfold prop.to_vc,
    assume h1,
    have h2, from mt (to_vc_valid_of_erased_n_valid P₁ σ).right,
    have h3, from valid_env.not.mpr h1,
    have h4, from h2 h3,
    from valid_env.not.mp h4,

    unfold prop.erased_p,
    unfold prop.to_vc,
    assume h1,
    have h2, from mt (to_vc_valid_of_erased_n_valid P₁ σ).left,
    have h3, from valid_env.not.mpr h1,
    have h4, from h2 h3,
    from valid_env.not.mp h4
  end
| (prop.and P₁ P₂) :=
  have rec_1: P₁.simplesize < (prop.and P₁ P₂).simplesize, from simplesize_prop_and₁,
  have rec_2: P₂.simplesize < (prop.and P₁ P₂).simplesize, from simplesize_prop_and₂,
  begin
    assume σ,
    split,

    unfold prop.erased_n,
    unfold prop.to_vc,
    assume h1,

    apply valid_env.and,
    show σ⊨prop.to_vc P₁, by begin
      have h2, from (valid_env.and.elim h1).left,
      from (to_vc_valid_of_erased_n_valid P₁ σ).left h2
    end,

    show σ⊨prop.to_vc P₂, by begin
      have h2, from (valid_env.and.elim h1).right,
      from (to_vc_valid_of_erased_n_valid P₂ σ).left h2
    end,

    unfold prop.erased_p,
    unfold prop.to_vc,
    assume h1,

    apply valid_env.and,
    show σ⊨prop.erased_p P₁, by begin
      have h2, from (valid_env.and.elim h1).left,
      from (to_vc_valid_of_erased_n_valid P₁ σ).right h2
    end,

    show σ⊨prop.erased_p P₂, by begin
      have h2, from (valid_env.and.elim h1).right,
      from (to_vc_valid_of_erased_n_valid P₂ σ).right h2
    end
  end
| (prop.or P₁ P₂) :=
  have rec_1: P₁.simplesize < (prop.or P₁ P₂).simplesize, from simplesize_prop_or₁,
  have rec_2: P₂.simplesize < (prop.or P₁ P₂).simplesize, from simplesize_prop_or₂,
  begin
    assume σ,

    split,

    unfold prop.erased_n,
    unfold prop.to_vc,
    assume h2,

    cases (valid_env.or.elim h2),

    apply valid_env.or₁,
    from (to_vc_valid_of_erased_n_valid P₁ σ).left a,

    apply valid_env.or₂,
    from (to_vc_valid_of_erased_n_valid P₂ σ).left a,

    unfold prop.erased_p,
    unfold prop.to_vc,
    assume h2,

    cases (valid_env.or.elim h2),

    apply valid_env.or₁,
    from (to_vc_valid_of_erased_n_valid P₁ σ).right a,

    apply valid_env.or₂,
    from (to_vc_valid_of_erased_n_valid P₂ σ).right a
  end
| (prop.pre t₁ t₂) := begin
    assume σ,
    split,

    unfold prop.erased_n,
    unfold prop.to_vc,
    from id,

    unfold prop.erased_p,
    unfold prop.to_vc,
    from id
  end
| (prop.pre₁ op t) := begin
    assume σ,
    split,

    unfold prop.erased_n,
    unfold prop.to_vc,
    from id,

    unfold prop.erased_p,
    unfold prop.to_vc,
    from id
  end
| (prop.pre₂ op t₁ t₂) := begin
    assume σ,
    split,

    unfold prop.erased_n,
    unfold prop.to_vc,
    from id,

    unfold prop.erased_p,
    unfold prop.to_vc,
    from id
  end
| (prop.call t) := begin
    assume σ,
    split,

    unfold prop.erased_n,
    unfold prop.to_vc,
    from id,

    unfold prop.erased_p,
    unfold prop.to_vc,
    from id
  end
| (prop.post t₁ t₂) := begin
    assume σ,
    split,

    unfold prop.erased_n,
    unfold prop.to_vc,
    from id,

    unfold prop.erased_p,
    unfold prop.to_vc,
    from id
  end
| (prop.forallc y P₁) :=
  begin
    assume σ,
    split,

    unfold prop.erased_n,
    unfold prop.to_vc,
    assume h1,
    have h2, from valid_env.univ.mpr h1,
    apply valid_env.univ.mp,
    assume v,
    have h3, from h2 v,
    have h4: (vc.subst y v (prop.erased_n P₁) = prop.erased_n (prop.subst y v P₁)),
    from subst_distrib_erased.right,
    have h5: σ ⊨ prop.erased_n (prop.subst y v P₁), from h4 ▸ h3,
    have h6: (vc.subst y v (prop.to_vc P₁) = prop.to_vc (prop.subst y v P₁)),
    from subst_distrib_to_vc,
    rw[h6],
    show σ⊨prop.to_vc (prop.subst y v P₁), from (
      have ht1: P₁.simplesize = (prop.subst y v P₁).simplesize, from same_simplesize_after_subst,
      have ht2: P₁.simplesize < (prop.forallc y P₁).simplesize, from simplesize_prop_forall,
      have rec_wf: (prop.subst y v P₁).simplesize < (prop.forallc y P₁).simplesize, from ht1 ▸ ht2,
      (to_vc_valid_of_erased_n_valid (prop.subst y v P₁) σ).left h5
    ),

    assume h1,
    unfold prop.erased_p,
    from valid_env.true
  end
| (prop.exis y P₁) := begin
    assume σ,
    split,

    unfold prop.erased_n,
    unfold prop.to_vc,
    assume h1,

    have h2, from valid_env.not.mpr h1,
    apply valid_env.not.mp,

    by_contradiction h3,
    have h4: σ⊨vc.univ y (vc.not (prop.erased_n P₁)), by begin
      have h5, from valid_env.univ.mpr h3,
      apply valid_env.univ.mp,
      assume v: value,
      have h6, from h5 v,

      have h7: (vc.subst y v (vc.not (prop.to_vc P₁)) = vc.not (vc.subst y v (prop.to_vc P₁))),
      by unfold vc.subst,
      rw[h7] at h6,
      have h8: (vc.subst y v (vc.not (prop.erased_n P₁)) = vc.not (vc.subst y v (prop.erased_n P₁))),
      by unfold vc.subst,
      rw[h8],

      have h9, from valid_env.not.mpr h6,
      apply valid_env.not.mp,

      by_contradiction h10,
      have h11: σ⊨vc.subst y v (prop.to_vc P₁), by begin

        have h12: (vc.subst y v (prop.erased_n P₁) = prop.erased_n (prop.subst y v P₁)),
        from subst_distrib_erased.right,
        have h13: σ ⊨ prop.erased_n (prop.subst y v P₁), from h12 ▸ h10,
        have h14: (vc.subst y v (prop.to_vc P₁) = prop.to_vc (prop.subst y v P₁)),
        from subst_distrib_to_vc,
        rw[h14],
        show σ⊨prop.to_vc (prop.subst y v P₁), from (
          have ht1: P₁.simplesize = (prop.subst y v P₁).simplesize, from same_simplesize_after_subst,
          have ht2: P₁.simplesize < (prop.forallc y P₁).simplesize, from simplesize_prop_forall,
          have rec_wf: (prop.subst y v P₁).simplesize < (prop.forallc y P₁).simplesize, from ht1 ▸ ht2,
          (to_vc_valid_of_erased_n_valid (prop.subst y v P₁) σ).left h13
        )
      end,
      from h9 h11
    end,
    from h2 h4,

    unfold prop.erased_p,
    unfold prop.to_vc,
    assume h1,

    have h2, from valid_env.not.mpr h1,
    apply valid_env.not.mp,

    by_contradiction h3,
    have h4: σ⊨vc.univ y (vc.not (prop.to_vc P₁)), by begin
      have h5, from valid_env.univ.mpr h3,
      apply valid_env.univ.mp,
      assume v: value,
      have h6, from h5 v,

      have h7: (vc.subst y v (vc.not (prop.erased_p P₁)) = vc.not (vc.subst y v (prop.erased_p P₁))),
      by unfold vc.subst,
      rw[h7] at h6,
      have h8: (vc.subst y v (vc.not (prop.to_vc P₁)) = vc.not (vc.subst y v (prop.to_vc P₁))),
      by unfold vc.subst,
      rw[h8],

      have h9, from valid_env.not.mpr h6,
      apply valid_env.not.mp,

      by_contradiction h10,
      have h11: σ⊨vc.subst y v (prop.erased_p P₁), by begin

        have h12: (vc.subst y v (prop.to_vc P₁) = prop.to_vc (prop.subst y v P₁)),
        from subst_distrib_to_vc,
        have h13: σ ⊨ prop.to_vc (prop.subst y v P₁), from h12 ▸ h10,
        have h14: (vc.subst y v (prop.erased_p P₁) = prop.erased_p (prop.subst y v P₁)),
        from subst_distrib_erased.left,
        rw[h14],
        show σ⊨prop.erased_p (prop.subst y v P₁), from (
          have ht1: P₁.simplesize = (prop.subst y v P₁).simplesize, from same_simplesize_after_subst,
          have ht2: P₁.simplesize < (prop.forallc y P₁).simplesize, from simplesize_prop_forall,
          have rec_wf: (prop.subst y v P₁).simplesize < (prop.forallc y P₁).simplesize, from ht1 ▸ ht2,
          (to_vc_valid_of_erased_n_valid (prop.subst y v P₁) σ).right h13
        )
      end,
      from h9 h11
    end,
    from h2 h4
  end
using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf $ λ s, s.simplesize⟩],
  dec_tac := tactic.assumption
}

lemma to_vc_valid_of_lifted_to_vc_valid {σ: env} {P Q: prop} {x: var}:
  (P.lift_p x = some Q → (σ ⊨ Q.to_vc) → σ ⊨ P.to_vc) ∧
  (P.lift_n x = some Q → (σ ⊨ P.to_vc) → σ ⊨ Q.to_vc) :=
  sorry

lemma to_vc_valid_of_lift_all_to_vc_valid: ∀P:prop, ∀σ, (σ ⊨ P.lift_all.to_vc) → σ ⊨ P.to_vc
| P :=
  begin
    assume σ,
    assume h1,
    unfold prop.lift_all at h1,
    by_cases (option.is_none_prop (prop.lift_p P (prop.fresh_var P))) with h2,

    have h3: (prop.lift_p P (prop.fresh_var P) = none), from option.is_none.inv.mpr h2,
    simp[h3] at h1,
    from h1,

    have h3, from option.some_iff_not_none.mpr h2,
    have h4: ∃Q, (prop.lift_p P (prop.fresh_var P) = some Q), from option.is_some_iff_exists.mp h3,
    cases h4 with Q h5,
    simp[h5] at h1,
    show σ ⊨ prop.to_vc P, from (
      have Q.num_quantifiers < P.num_quantifiers, from (lifted_prop_smaller Q).left h5,
      have σ ⊨ Q.to_vc, from to_vc_valid_of_lift_all_to_vc_valid Q σ h1,
      to_vc_valid_of_lifted_to_vc_valid.left h5 this
    )
  end
using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf $ λ s, s.num_quantifiers ⟩],
  dec_tac := tactic.assumption
}

lemma erased_valid_of_instantiated_with_erased_valid {σ: env} {P: prop} {t: calltrigger}:
  ((σ ⊨ (P.instantiate_with_n t).to_vc) → σ ⊨ P.to_vc) ∧
  ((σ ⊨ P.to_vc) → σ ⊨ (P.instantiate_with_p t).to_vc) :=
  begin
    induction P,
    case prop.term t {
      split,

      unfold prop.instantiate_with_n,
      from id,

      unfold prop.instantiate_with_p,
      from id
    },
    case prop.not P₁ ih {
      split,

      unfold prop.instantiate_with_n,
      unfold prop.to_vc,
      assume h1,
      apply valid_env.not.mp,

      by_contradiction,

      have h4: σ ⊨ prop.to_vc (prop.instantiate_with_p P₁ t),
      from ih.right a,
      have h5, from valid_env.not.mpr h1,
      from h5 h4,

      unfold prop.instantiate_with_p,
      unfold prop.to_vc,
      assume h1,
      apply valid_env.not.mp,

      by_contradiction,
      have h2: σ ⊨ prop.to_vc P₁,
      from ih.left a,
      have h3, from valid_env.not.mpr h1,
      from h3 h2
    },
    case prop.and P₁ P₂ P₁_ih P₂_ih {
      split,

      unfold prop.instantiate_with_n,
      unfold prop.to_vc,
      assume h1,
      have h2: σ ⊨ prop.to_vc (prop.and (prop.instantiate_with_n P₁ t) (prop.instantiate_with_n P₂ t)), from h1,
      unfold prop.to_vc at h2,
      have h3, from valid_env.and.elim h2,
      apply valid_env.and,
      show σ ⊨ prop.to_vc P₁, from P₁_ih.left h3.left,
      show σ ⊨ prop.to_vc P₂, from P₂_ih.left h3.right,

      unfold prop.instantiate_with_p,
      unfold prop.to_vc,
      assume h1,
      have h2, from valid_env.and.elim h1,
      change σ ⊨ prop.to_vc (prop.and (prop.instantiate_with_p P₁ t) (prop.instantiate_with_p P₂ t)),
      unfold prop.to_vc,
      apply valid_env.and,
      show σ ⊨ prop.to_vc (prop.instantiate_with_p P₁ t), from P₁_ih.right h2.left,
      show σ ⊨ prop.to_vc (prop.instantiate_with_p P₂ t), from P₂_ih.right h2.right
    },
    case prop.or P₁ P₂ P₁_ih P₂_ih {
      split,

      unfold prop.instantiate_with_n,
      unfold prop.to_vc,
      assume h1,
      have h2: σ ⊨ prop.to_vc (prop.or (prop.instantiate_with_n P₁ t) (prop.instantiate_with_n P₂ t)), from h1,
      unfold prop.to_vc at h2,
      cases valid_env.or.elim h2 with h3 h4,

      apply valid_env.or₁,
      from P₁_ih.left h3,

      apply valid_env.or₂,
      from P₂_ih.left h4,

      unfold prop.instantiate_with_p,
      unfold prop.to_vc,
      assume h1,
      change σ ⊨ prop.to_vc (prop.or (prop.instantiate_with_p P₁ t) (prop.instantiate_with_p P₂ t)),
      unfold prop.to_vc,
      cases valid_env.or.elim h1 with h3 h4,

      apply valid_env.or₁,
      from P₁_ih.right h3,

      apply valid_env.or₂,
      from P₂_ih.right h4
    },
    case prop.pre t₁ t₂ {
      split,

      unfold prop.instantiate_with_n,
      from id,

      unfold prop.instantiate_with_p,
      from id
    },
    case prop.pre₁ op t {
      split,

      unfold prop.instantiate_with_n,
      from id,

      unfold prop.instantiate_with_p,
      from id
    },
    case prop.pre₂ op t₁ t₂ {
      split,

      unfold prop.instantiate_with_n,
      from id,

      unfold prop.instantiate_with_p,
      from id
    },
    case prop.call t {
      split,

      unfold prop.instantiate_with_n,
      from id,

      unfold prop.instantiate_with_p,
      from id
    },
    case prop.post t₁ t₂ {
      split,

      unfold prop.instantiate_with_n,
      from id,

      unfold prop.instantiate_with_p,
      from id
    },
    case prop.forallc y P₁ P₁_ih {
      split,

      unfold prop.instantiate_with_n,
      from id,

      unfold prop.instantiate_with_p,
      unfold prop.to_vc,
      assume h1,
      change σ ⊨ prop.to_vc (prop.and (prop.forallc y P₁) (prop.substt y (t.x) P₁)),
      unfold prop.to_vc,
      apply valid_env.and,
      from h1,



      admit
    },
    case prop.exis y P₁ P₁_ih {
      admit
    }
  end

lemma to_vc_valid_of_instantiate_with_all_lifted_to_vc_valid {σ: env} {T: list calltrigger}:
  ∀P: prop, (σ ⊨ (P.instantiate_with_all T).lift_all.to_vc) → σ ⊨ P.to_vc :=
  begin
    induction T,

    case list.nil {
      assume P,
      assume h1,
      unfold prop.instantiate_with_all at h1,
      from to_vc_valid_of_lift_all_to_vc_valid P σ h1
    },

    case list.cons t T ih {
      assume P,
      assume h1,
      unfold prop.instantiate_with_all at h1,
      have h3, from ih (prop.instantiate_with_n P t),
      have h4, from h3 h1,
      from erased_valid_of_instantiated_with_erased_valid.left h4
    }
  end

lemma lifted_all_to_vc_valid_of_instantiate_rep_valid {σ: env} {n: ℕ}:
  ∀P: prop, (σ ⊨ P.instantiate_rep n) → σ ⊨ P.lift_all.to_vc :=
  begin
    induction n,

    case nat.zero {
      assume P,
      assume h1,
      unfold prop.instantiate_rep at h1,
      from (to_vc_valid_of_erased_n_valid (prop.lift_all P) σ).left h1
    },

    case nat.succ n ih {
      assume P,
      unfold prop.instantiate_rep,
      assume h1,
      have h2, from ih (prop.instantiate_with_all (prop.lift_all P) (prop.find_calls_n (prop.lift_all P))) h1,
      from to_vc_valid_of_instantiate_with_all_lifted_to_vc_valid P.lift_all h2
    }
  end

--  inst_n(P)   ⇒   inst_p(P)
--         ⇘    ⇗  
--     ⇑      P      ⇓
--         ⇗    ⇘ 
-- erased_n(P)  ⇒  erased_p(P)

lemma to_vc_valid_of_instantiated_n_valid {σ: env} {P: prop}:
  closed_subst σ P → (σ ⊨ P.instantiated_n) → σ ⊨ P.to_vc :=
  assume P_closed: closed_subst σ P,
  assume : σ ⊨ P.instantiated_n,
  have σ ⊨ P.instantiate_rep P.max_nesting_level, by { unfold prop.instantiated_n at this, from this },
  have σ ⊨ P.lift_all.to_vc, from lifted_all_to_vc_valid_of_instantiate_rep_valid P this,
  show σ ⊨ P.to_vc, from to_vc_valid_of_lift_all_to_vc_valid P σ this

lemma vc_valid_from_inst_valid {P: prop}:
  ⟪ P ⟫ → ∀ (σ: env), closed_subst σ P → σ ⊨ P.to_vc :=
  assume h1: ⟪ P ⟫,
  assume σ: env,
  assume h2: closed_subst σ P,
  have h3: σ ⊨ (prop.instantiated_n P), from h1 σ h2,
  show σ ⊨ P.to_vc, from to_vc_valid_of_instantiated_n_valid h2 h3

/-
lemma instantiated_n_closed_of_closed {P: prop}: closed P → closed P.instantiated_n :=
  assume P_closed: closed P,
  assume x: var,
  assume : x ∈ FV P.instantiated_n,
  have x ∈ FV P, from free_of_instantiated_n_free this,
  show «false», from P_closed x this

lemma instantiated_p_closed_of_closed {P: prop}: closed P → closed P.instantiated_p :=
  assume P_closed: closed P,
  assume x: var,
  assume : x ∈ FV P.instantiated_p,
  have x ∈ FV P, from free_of_instantiated_p_free this,
  show «false», from P_closed x this

lemma instantiated_n_closed_subst_of_closed {σ: env} {P: prop}:
      closed_subst σ P → closed_subst σ P.instantiated_n :=
  assume : closed_subst σ P,
  have P_closed: closed (prop.subst_env σ P), from prop.closed_of_closed_subst this,
  have closed (vc.subst_env σ P.instantiated_n), from (
    assume x: var,
    assume h: x ∈ FV (vc.subst_env σ P.instantiated_n),
    have vc.subst_env σ P.instantiated_n = (prop.subst_env σ P).instantiated_n,
    from instantiated_n_distrib_subst_env,
    have x ∈ FV (prop.subst_env σ P).instantiated_n, from this ▸ h,
    have x ∈ FV (prop.subst_env σ P), from free_of_instantiated_n_free this,
    show «false», from P_closed x this
  ),
  show closed_subst σ P.instantiated_n, from vc.closed_subst_of_closed this

lemma instantiated_p_closed_subst_of_closed {σ: env} {P: prop}:
      closed_subst σ P → closed_subst σ P.instantiated_p :=
  assume : closed_subst σ P,
  have P_closed: closed (prop.subst_env σ P), from prop.closed_of_closed_subst this,
  have closed (vc.subst_env σ P.instantiated_p), from (
    assume x: var,
    assume h: x ∈ FV (vc.subst_env σ P.instantiated_p),
    have vc.subst_env σ P.instantiated_p = (prop.subst_env σ P).instantiated_p,
    from instantiated_p_distrib_subst_env,
    have x ∈ FV (prop.subst_env σ P).instantiated_p, from this ▸ h,
    have x ∈ FV (prop.subst_env σ P), from free_of_instantiated_p_free this,
    show «false», from P_closed x this
  ),
  show closed_subst σ P.instantiated_p, from vc.closed_subst_of_closed this

lemma no_calls_in_spec {R: spec}: (calls_p R = ∅) ∧ (calls_n R = ∅) :=
begin
  induction R ;
  split ;
  apply set.eq_empty_of_forall_not_mem ;
  assume c: calltrigger ,


  change c ∉ calls_p (spec.term a).to_prop,
  unfold spec.to_prop,
  intro h,
  cases h,

  change c ∉ calls_n (spec.term a).to_prop,
  unfold spec.to_prop,
  intro h,
  cases h,

  change c ∉ calls_p (spec.not a).to_prop,
  unfold spec.to_prop,
  intro h,
  have h2, from prop.has_call_p.not.inv h,
  have h3, from (set.forall_not_mem_of_eq_empty x.right) c,
  contradiction,

  change c ∉ calls_n (spec.not a).to_prop,
  unfold spec.to_prop,
  intro h,
  have h2, from prop.has_call_n.not.inv h,
  have h3, from (set.forall_not_mem_of_eq_empty x.left) c,
  contradiction,

  change c ∉ calls_p (spec.and a a_1).to_prop,
  unfold spec.to_prop,
  intro h,
  cases prop.has_call_p.and.inv h,
  have h3, from (set.forall_not_mem_of_eq_empty x.left) c,
  contradiction,
  have h3, from (set.forall_not_mem_of_eq_empty x_1.left) c,
  contradiction,
  
  change c ∉ calls_n (spec.and a a_1).to_prop,
  unfold spec.to_prop,
  intro h,
  cases prop.has_call_n.and.inv h,
  have h3, from (set.forall_not_mem_of_eq_empty x.right) c,
  contradiction,
  have h3, from (set.forall_not_mem_of_eq_empty x_1.right) c,
  contradiction,
  
  change c ∉ calls_p (spec.or a a_1).to_prop,
  unfold spec.to_prop,
  intro h,
  cases prop.has_call_p.or.inv h,
  have h3, from (set.forall_not_mem_of_eq_empty x.left) c,
  contradiction,
  have h3, from (set.forall_not_mem_of_eq_empty x_1.left) c,
  contradiction,
  
  change c ∉ calls_n (spec.or a a_1).to_prop,
  unfold spec.to_prop,
  intro h,
  cases prop.has_call_n.or.inv h,
  have h3, from (set.forall_not_mem_of_eq_empty x.right) c,
  contradiction,
  have h3, from (set.forall_not_mem_of_eq_empty x_1.right) c,
  contradiction,

  change c ∉ calls_p (spec.func a a_1 a_2 a_3).to_prop,
  unfold spec.to_prop,
  intro h,
  cases prop.has_call_p.and.inv h,
  cases a_4,
  cases a_4,

  change c ∉ calls_n (spec.func a a_1 a_2 a_3).to_prop,
  unfold spec.to_prop,
  intro h,
  cases prop.has_call_n.and.inv h,
  cases a_4,
  cases a_4
end

lemma spec_instantiated_eq_spec_erased {R: spec}: R.to_prop.instantiated_p = R.to_prop.erased_p :=
  have calls_p R.to_prop = ∅, from no_calls_in_spec.left,
  show R.to_prop.instantiated_p = R.to_prop.erased_p, from instantiated_p_eq_erased_p_without_calls this

-/