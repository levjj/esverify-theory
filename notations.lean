import .syntax .etc

-- P → Q

@[reducible]
def spec.implies(P Q: spec): spec := spec.or (spec.not P) Q

@[reducible]
def prop.implies(P Q: prop): prop := prop.or (prop.not P) Q

@[reducible]
def propctx.implies(P Q: propctx): propctx := propctx.or (propctx.not P) Q

@[reducible]
def vc.implies(P Q: vc): vc := vc.or (vc.not P) Q

-- P ↔ Q

@[reducible]
def spec.iff(P Q: spec): spec := spec.and (spec.implies P Q) (spec.implies Q P)

@[reducible]
def prop.iff(P Q: prop): prop := prop.and (prop.implies P Q) (prop.implies Q P)

@[reducible]
def propctx.iff(P Q: propctx): propctx := propctx.and (propctx.implies P Q) (propctx.implies Q P)

@[reducible]
def vc.iff(P Q: vc): vc := vc.and (vc.implies P Q) (vc.implies Q P)

-- P ⋀ Q
class has_and (α : Type) := (and : α → α → α) 
instance : has_and spec := ⟨spec.and⟩
instance : has_and prop := ⟨prop.and⟩
instance : has_and propctx := ⟨propctx.and⟩
instance : has_and vc := ⟨vc.and⟩
infixr `⋀`:35 := has_and.and

-- P ⋁ Q
class has_or (α : Type) := (or : α → α → α) 
instance : has_or spec := ⟨spec.or⟩
instance : has_or prop := ⟨prop.or⟩
instance : has_or propctx := ⟨propctx.or⟩
instance : has_or vc := ⟨vc.or⟩
infixr `⋁`:30 := has_or.or

-- use • as hole
notation `•` := termctx.hole

-- history items
notation H `·` `call` := history.call H

-- simple coercions
instance value_to_term : has_coe value term := ⟨term.value⟩
instance var_to_term : has_coe var term := ⟨term.var⟩
instance term_to_prop : has_coe term prop := ⟨prop.term⟩
instance termctx_to_propctx : has_coe termctx propctx := ⟨propctx.term⟩
instance term_to_vc : has_coe term vc := ⟨vc.term⟩

-- use (t ≡ t)/(t ≣ t) to construct equality comparison
infix ≡ := term.binop binop.eq
infix `≣`:50 := termctx.binop binop.eq

-- syntax for let expressions
notation `lett` x `=`:1 `true` `in` e := exp.true x e
notation `letf` x `=`:1 `false` `in` e := exp.false x e
notation `letn` x `=`:1 n`in` e := exp.num x n e
notation `letf` f `[`:1 x `]` `req` R `ens` S `{`:1 e `}`:1 `in` e' := exp.func f x R S e e'
notation `letop` y `=`:1 op `[`:1 x `]`:1 `in` e := exp.unop y op x e
notation `letop2` z `=`:1 op `[`:1 x `,` y `]`:1 `in` e := exp.binop z op x y e
notation `letapp` y `=`:1 f `[`:1 x `]`:1 `in` e := exp.app y f x e

-- σ[x ↦ v]
notation e `[` x `↦` v `]` := env.cons e x v

-- (H, σ, e) : stack
instance : has_coe (spec × history × env × exp) stack := ⟨λe, stack.top e.1 e.2.1 e.2.2.1 e.2.2.2⟩

-- κ · [H, σ, let y = f [ x ] in e]
notation st `·` `[` R `,` H `,` env `,` `letapp` y `=`:1 f `[` x `]` `in` e `]` := stack.cons st R H env y f x e

-- to use values, expressions, terms, specs, histories and environments with recursion,
-- we need to show that the recursion is decreasing, i.e. its parts are smaller than the whole

lemma sizeof_value_func_R {f x: var} {R S: spec} {e: exp} {H: history} {σ: env}:
      R.sizeof < (value.func f x R S e H σ).sizeof :=
  begin
    unfold value.sizeof,
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_value_func_S {f x: var} {R S: spec} {e: exp} {H: history} {σ: env}:
      S.sizeof < (value.func f x R S e H σ).sizeof :=
  begin
    unfold value.sizeof,
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_value_func_e {f x: var} {R S: spec} {e: exp} {H: history} {σ: env}:
      e.sizeof < (value.func f x R S e H σ).sizeof :=
  begin
    unfold value.sizeof,
    rw[add_assoc],
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_value_func_H {f x: var} {R S: spec} {e: exp} {H: history} {σ: env}:
      H.sizeof < (value.func f x R S e H σ).sizeof :=
  begin
    unfold value.sizeof,
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_value_func_σ {f x: var} {R S: spec} {e: exp} {H: history} {σ: env}:
      σ.sizeof < (value.func f x R S e H σ).sizeof :=
  begin
    unfold value.sizeof,
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_exp_true {x: var} {e: exp}:
      e.sizeof < (exp.true x e).sizeof :=
  begin
    unfold exp.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_exp_false {x: var} {e: exp}:
      e.sizeof < (exp.false x e).sizeof :=
  begin
    unfold exp.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_exp_num {x: var} {n: ℤ} {e: exp}:
      e.sizeof < (exp.num x n e).sizeof :=
  begin
    unfold exp.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_exp_func_R {f x: var} {R S: spec} {e₁ e₂: exp}:
      R.sizeof < (exp.func f x R S e₁ e₂).sizeof :=
  begin
    unfold exp.sizeof,
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_exp_func_S {f x: var} {R S: spec} {e₁ e₂: exp}:
      S.sizeof < (exp.func f x R S e₁ e₂).sizeof :=
  begin
    unfold exp.sizeof,
    rw[add_assoc],
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_exp_func_e₁ {f x: var} {R S: spec} {e₁ e₂: exp}:
      e₁.sizeof < (exp.func f x R S e₁ e₂).sizeof :=
  begin
    unfold exp.sizeof,
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_exp_func_e₂ {f x: var} {R S: spec} {e₁ e₂: exp}:
      e₂.sizeof < (exp.func f x R S e₁ e₂).sizeof :=
  begin
    unfold exp.sizeof,
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_exp_unop {x y: var} {op: unop} {e: exp}:
      e.sizeof < (exp.unop y op x e).sizeof :=
  begin
    unfold exp.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_exp_binop {x y z: var} {op: binop} {e: exp}:
      e.sizeof < (exp.binop z op x y e).sizeof :=
  begin
    unfold exp.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_exp_app {x y z: var} {e: exp}:
      e.sizeof < (exp.app z x y e).sizeof :=
  begin
    unfold exp.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_exp_ite_e₁ {x: var} {e₁ e₂: exp}:
      e₁.sizeof < (exp.ite x e₁ e₂).sizeof :=
  begin
    unfold exp.sizeof,
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_exp_ite_e₂ {x: var} {e₁ e₂: exp}:
      e₂.sizeof < (exp.ite x e₁ e₂).sizeof :=
  begin
    unfold exp.sizeof,
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_term_value {v: value}:
      v.sizeof < (term.value v).sizeof :=
  begin
    unfold term.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    from zero_lt_one
  end

lemma sizeof_term_unop {op: unop} {t: term}:
      t.sizeof < (term.unop op t).sizeof :=
  begin
    unfold term.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_term_binop₁ {op: binop} {t₁ t₂: term}:
      t₁.sizeof < (term.binop op t₁ t₂).sizeof :=
  begin
    unfold term.sizeof,
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_term_binop₂ {op: binop} {t₁ t₂: term}:
      t₂.sizeof < (term.binop op t₁ t₂).sizeof :=
  begin
    unfold term.sizeof,
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_term_app₁ {t₁ t₂: term}:
      t₁.sizeof < (term.app t₁ t₂).sizeof :=
  begin
    unfold term.sizeof,
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_term_app₂ {t₁ t₂: term}:
      t₂.sizeof < (term.app t₁ t₂).sizeof :=
  begin
    unfold term.sizeof,
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_spec_term {t: term}:
      t.sizeof < (spec.term t).sizeof :=
  begin
    unfold spec.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    from zero_lt_one
  end

lemma sizeof_spec_not {R: spec}:
      R.sizeof < R.not.sizeof :=
  begin
    unfold spec.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    from zero_lt_one
  end

lemma sizeof_spec_and₁ {R S: spec}:
      R.sizeof < (spec.and R S).sizeof :=
  begin
    unfold spec.sizeof,
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    change 0 < sizeof S + 1,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_spec_and₂ {R S: spec}:
      S.sizeof < (spec.and R S).sizeof :=
  begin
    unfold spec.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    change 0 < 1 + sizeof R,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_spec_or₁ {R S: spec}:
      R.sizeof < (spec.or R S).sizeof :=
  begin
    unfold spec.sizeof,
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    change 0 < sizeof S + 1,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_spec_or₂ {R S: spec}:
      S.sizeof < (spec.or R S).sizeof :=
  begin
    unfold spec.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    change 0 < 1 + sizeof R,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_spec_func_t {f: term} {x: var} {R S: spec}:
      f.sizeof < (spec.func f x R S).sizeof :=
  begin
    unfold spec.sizeof,
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_spec_func_R {f: term} {x: var} {R S: spec}:
      R.sizeof < (spec.func f x R S).sizeof :=
  begin
    unfold spec.sizeof,
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    change 0 < sizeof S + (1 + sizeof f + sizeof x),
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_spec_func_S {f: term} {x: var} {R S: spec}:
      S.sizeof < (spec.func f x R S).sizeof :=
  begin
    unfold spec.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    change 0 < 1 + sizeof f + sizeof x + sizeof R,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_env_rest {σ: env} {x: var} {v: value}:
      σ.sizeof < (σ[x↦v]).sizeof :=
  begin
    unfold env.sizeof,
    rw[add_assoc],
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    change 0 < sizeof x + (sizeof v + 1),
    apply lt_add_of_le_of_pos nonneg_of_nat,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_env_value {σ: env} {x: var} {v: value}:
      v.sizeof < (σ[x↦v]).sizeof :=
  begin
    unfold env.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_history_rest {f x: var} {R S: spec} {e: exp} {H₁ H₂: history} {σ: env} {v: value}:
      H₁.sizeof < (history.call H₁ f x R S e H₂ σ v).sizeof :=
  begin
    unfold history.sizeof,
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_history_R {f x: var} {R S: spec} {e: exp} {H₁ H₂: history} {σ: env} {v: value}:
      R.sizeof < (history.call H₁ f x R S e H₂ σ v).sizeof :=
  begin
    unfold history.sizeof,
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_history_S {f x: var} {R S: spec} {e: exp} {H₁ H₂: history} {σ: env} {v: value}:
      S.sizeof < (history.call H₁ f x R S e H₂ σ v).sizeof :=
  begin
    unfold history.sizeof,
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_history_e {f x: var} {R S: spec} {e: exp} {H₁ H₂: history} {σ: env} {v: value}:
      e.sizeof < (history.call H₁ f x R S e H₂ σ v).sizeof :=
  begin
    unfold history.sizeof,
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_history_H {f x: var} {R S: spec} {e: exp} {H₁ H₂: history} {σ: env} {v: value}:
      H₂.sizeof < (history.call H₁ f x R S e H₂ σ v).sizeof :=
  begin
    unfold history.sizeof,
    rw[add_assoc],
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_history_σ {f x: var} {R S: spec} {e: exp} {H₁ H₂: history} {σ: env} {v: value}:
      σ.sizeof < (history.call H₁ f x R S e H₂ σ v).sizeof :=
  begin
    unfold history.sizeof,
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_history_v {f x: var} {R S: spec} {e: exp} {H₁ H₂: history} {σ: env} {v: value}:
      v.sizeof < (history.call H₁ f x R S e H₂ σ v).sizeof :=
  begin
    unfold history.sizeof,
    rw[add_comm],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_substack {s: stack} {R: spec} {H: history} {σ: env} {f x y: var} {e: exp}:
      s.sizeof < (stack.cons s R H σ f x y e).sizeof :=
  begin
    unfold stack.sizeof,
    change sizeof s < 1 + sizeof s + sizeof R + sizeof H + sizeof σ + sizeof f + sizeof x + sizeof y + sizeof e,
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    rw[add_comm],
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

-- env lookup as function application

def env.apply: env → var → option value
| env.empty _ := none
| (σ[x↦v]) y :=
  have σ.sizeof < (σ[x↦v]).sizeof, from sizeof_env_rest,
  if x = y ∧ option.is_none (σ.apply y) then v else σ.apply y

using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ e, e.1.sizeof)⟩],
  dec_tac := tactic.assumption
}

def env.rest: env → env
| env.empty := env.empty
| (σ[x↦v])  := σ

instance : has_coe_to_fun env := ⟨λ _, var → option value, env.apply⟩

inductive env.contains: env → var → Prop
| same {e: env} {x: var} {v: value} : env.contains (e[x↦v]) x 
| rest {e: env} {x y: var} {v: value} : env.contains e x → env.contains (e[y↦v]) x

instance : has_mem var env := ⟨λx σ, σ.contains x⟩ 

def env.dom (σ: env): set var := λx, x ∈ σ

-- spec to prop coercion

@[reducible]
def prop.func (f: term) (x: var) (P: prop) (Q: prop): prop := 
  term.unop unop.isFunc f ⋀
  prop.forallc x f (prop.implies P (prop.pre f x) ⋀
                    prop.implies (prop.post f x) Q)

def spec.to_prop : spec → prop
| (spec.term t)       := prop.term t
| (spec.not S)        :=
    have S.sizeof < S.not.sizeof, from sizeof_spec_not,
    prop.not S.to_prop
| (spec.and R S)      :=
    have R.sizeof < (R ⋀ S).sizeof, from sizeof_spec_and₁,
    have S.sizeof < (R ⋀ S).sizeof, from sizeof_spec_and₂,
    R.to_prop ⋀ S.to_prop
| (spec.or R S)       :=
    have R.sizeof < (R ⋁ S).sizeof, from sizeof_spec_or₁,
    have S.sizeof < (R ⋁ S).sizeof, from sizeof_spec_or₂,
    R.to_prop ⋁ S.to_prop
| (spec.func f x R S) :=
    have R.sizeof < (spec.func f x R S).sizeof, from sizeof_spec_func_R,
    have S.sizeof < (spec.func f x R S).sizeof, from sizeof_spec_func_S,
    prop.func f x R.to_prop S.to_prop

using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ e, e.sizeof)⟩],
  dec_tac := tactic.assumption
}

instance spec_to_prop : has_coe spec prop := ⟨spec.to_prop⟩

-- prop size

@[reducible]
def prop.size: prop → ℕ := @prop.rec (λ_, ℕ)
  (λ_, 0)
  (λ_ n, n + 1)
  (λ_ _ n m , n + m + 1)
  (λ_ _ n m , n + m + 1)
  (λ_ _, 0)
  (λ_ _, 0)
  (λ_ _ _, 0)
  (λ_ _, 0)
  (λ_ _, 0)
  (λ_ _ _ n, n + 1)
  (λ_ _ n, n + 1)

instance : has_sizeof prop := ⟨prop.size⟩

-- vc size

@[reducible]
def vc.size: vc → ℕ := @vc.rec (λ_, ℕ)
  (λ_, 0)
  (λ _ n, n + 1)
  (λ_ _ n m , n + m + 1)
  (λ_ _ n m , n + m + 1)
  (λ_ _, 0)
  (λ_ _, 0)
  (λ_ _ _, 0)
  (λ_ _, 0)
  (λ_ _ n, n + 1)

instance : has_sizeof vc := ⟨vc.size⟩

-- history size

@[reducible]
def historyfix: (history → ℕ) → (λ (_x : history), ℕ) history.empty :=
  assume f: history → ℕ,
  (λ (h : history), f h) history.empty 

@[reducible]
def history.size: history → ℕ := @history.rec (λ_, ℕ)
  (historyfix (λ_, 0))
  (λ _ _ _ _ _ _ _ _ _ n _, n + 1)

instance : has_sizeof history := ⟨history.size⟩

-- term to termctx coercion

def term.to_termctx : term → termctx
| (term.value v)        := termctx.value v
| (term.var x)          := termctx.var x
| (term.unop op t)      := termctx.unop op t.to_termctx
| (term.binop op t₁ t₂) := termctx.binop op t₁.to_termctx t₂.to_termctx
| (term.app t₁ t₂)      := termctx.app t₁.to_termctx t₂.to_termctx

instance term_to_termctx : has_coe term termctx := ⟨term.to_termctx⟩

-- term to termctx coercion

def prop.to_propctx : prop → propctx
| (prop.term t)        := propctx.term t
| (prop.not P)         := propctx.not P.to_propctx
| (prop.and P₁ P₂)     := P₁.to_propctx ⋀ P₂.to_propctx
| (prop.or P₁ P₂)      := P₁.to_propctx ⋁ P₂.to_propctx
| (prop.pre t₁ t₂)     := propctx.pre t₁ t₂
| (prop.pre₁ op t)     := propctx.pre₁ op t
| (prop.pre₂ op t₁ t₂) := propctx.pre₂ op t₁ t₂
| (prop.post t₁ t₂)    := propctx.post t₁ t₂
| (prop.call t₁ t₂)    := propctx.call t₁ t₂
| (prop.forallc x t P) := propctx.forallc x t P.to_propctx
| (prop.exis x P)      := propctx.exis x P.to_propctx

instance prop_to_propctx : has_coe prop propctx := ⟨prop.to_propctx⟩

-- termctx substituttion as function application

def termctx.apply: termctx → term → term
| •                           t := t
| (termctx.value v)           _ := term.value v
| (termctx.var x)             _ := term.var x
| (termctx.unop op t₁)        t := term.unop op (t₁.apply t)
| (termctx.binop op t₁ t₂)    t := term.binop op (t₁.apply t) (t₂.apply t)
| (termctx.app t₁ t₂)         t := term.app (t₁.apply t) (t₂.apply t)

instance : has_coe_to_fun termctx := ⟨λ _, term → term, termctx.apply⟩

-- propctx substituttion as function application

def propctx.apply: propctx → term → prop
| (propctx.term t₁) t        := t₁ t
| (propctx.not P) t          := prop.not (P.apply t)
| (propctx.and P₁ P₂) t      := P₁.apply t ⋀ P₂.apply t
| (propctx.or P₁ P₂) t       := P₁.apply t ⋁ P₂.apply t
| (propctx.pre t₁ t₂) t      := prop.pre (t₁ t) (t₂ t)
| (propctx.pre₁ op t₁) t     := prop.pre₁ op (t₁ t)
| (propctx.pre₂ op t₁ t₂) t  := prop.pre₂ op (t₁ t) (t₂ t)
| (propctx.post t₁ t₂) t     := prop.post (t₁ t) (t₂ t)
| (propctx.call t₁ t₂) t     := prop.call (t₁ t) (t₂ t)
| (propctx.forallc x t₁ P) t := prop.forallc x (t₁ t) (P.apply t)
| (propctx.exis x P) t       := prop.exis x (P.apply t)

instance : has_coe_to_fun propctx := ⟨λ _, term → prop, propctx.apply⟩

-- call history to prop coercion

def calls_to_prop: history → prop
| history.empty                        := value.true
| (history.call rest f x R S e H σ vₓ) :=
  have history.size rest < history.size (rest · call f x R S e H σ vₓ), from lt_of_add_one,
  calls_to_prop rest ⋀ prop.call (value.func f x R S e H σ) vₓ

instance call_to_prop: has_coe history prop := ⟨calls_to_prop⟩

-- instantiation is axiomatized in qi.lean

constant prop.instantiated_n: prop → vc

constant prop.instantiated_p: prop → vc

-- validity is axiomatized in logic.lean

constant valid : vc → Prop
notation `⊨` p: 20 := valid p

-- value eq value decidable

instance : decidable_eq unop := by tactic.mk_dec_eq_instance
instance : decidable_eq binop := by tactic.mk_dec_eq_instance

def wf_measure : has_well_founded
(psum (Σ' (v₁ : value), value)
  (psum (Σ' (e₁ : exp), exp)
    (psum (Σ' (t₁ : term), term)
      (psum (Σ' (R : spec), spec)
        (psum (Σ' (σ₁ : env), env)
          (Σ' (H₁ : history), history))))))
:= ⟨_, measure_wf $ λ s,
  match s with
  | psum.inl a := a.1.sizeof
  | psum.inr (psum.inl a) := a.1.sizeof
  | psum.inr (psum.inr (psum.inl a)) := a.1.sizeof
  | psum.inr (psum.inr (psum.inr (psum.inl a))) := a.1.sizeof
  | psum.inr (psum.inr (psum.inr (psum.inr (psum.inl a)))) := a.1.sizeof
  | psum.inr (psum.inr (psum.inr (psum.inr (psum.inr a)))) := a.1.sizeof
  end⟩

mutual def value.dec_eq, exp.dec_eq, term.dec_eq, spec.dec_eq, env.dec_eq, history.dec_eq

with value.dec_eq : ∀ (v₁ v₂: value), decidable (v₁ = v₂)
| v₁ v₂ :=
  let z := v₁ in
  have h: z = v₁, from rfl,
  value.cases_on (λv₁, (z = v₁) → decidable (v₁ = v₂)) v₁ (
    assume : z = value.true,
    show decidable (value.true = v₂), from
    value.cases_on (λv₂, decidable (value.true = v₂)) v₂ (
      show decidable (value.true = value.true), from is_true rfl
    ) (
      have value.true ≠ value.false, by contradiction,
      show decidable (value.true = value.false), from is_false this
    ) (
      assume n: ℤ,
      have value.true ≠ value.num n, by contradiction,
      show decidable (value.true = value.num n), from is_false this
    ) (
      assume f x R S e H σ, 
      have value.true ≠ value.func f x R S e H σ, by contradiction,
      show decidable (value.true = value.func f x R S e H σ), from is_false this
    )
  )
  (
    assume : z = value.false,
    show decidable (value.false = v₂), from
    value.cases_on (λv₂, decidable (value.false = v₂)) v₂ (
      have value.false ≠ value.true, by contradiction,
      show decidable (value.false = value.true), from is_false this
    ) (
      show decidable (value.false = value.false), from is_true rfl
    ) (
      assume n: ℤ,
      have value.false ≠ value.num n, by contradiction,
      show decidable (value.false = value.num n), from is_false this
    ) (
      assume f x R S e H σ, 
      have value.false ≠ value.func f x R S e H σ, by contradiction,
      show decidable (value.false = value.func f x R S e H σ), from is_false this
    )
   ) (
    assume n₁: ℤ,
    assume : z = value.num n₁,
    show decidable (value.num n₁ = v₂), from
    value.cases_on (λv₂, decidable (value.num n₁ = v₂)) v₂ (
      have value.num n₁ ≠ value.true, by contradiction,
      show decidable (value.num n₁ = value.true), from is_false this
    ) (
      have value.num n₁ ≠ value.false, by contradiction,
      show decidable (value.num n₁ = value.false), from is_false this
    ) (
      assume n₂: ℤ,
      if h: n₁ = n₂ then (
        have value.num n₁ = value.num n₂, from h ▸ rfl,
        show decidable (value.num n₁ = value.num n₂), from is_true this
      ) else (
        have value.num n₁ ≠ value.num n₂, from (
          assume : value.num n₁ = value.num n₂,
          have n₁ = n₂, from value.num.inj this,
          show «false», from h this
        ),
        show decidable (value.num n₁ = value.num n₂), from is_false this
      )
    ) (
      assume f x R S e H σ, 
      have value.num n₁ ≠ value.func f x R S e H σ, by contradiction,
      show decidable (value.num n₁ = value.func f x R S e H σ), from is_false this
    )
  )
  (
    assume f₁ x₁ R₁ S₁ e₁ H₁ σ₁, 
    assume : z = value.func f₁ x₁ R₁ S₁ e₁ H₁ σ₁,
    have v₁_is_func: v₁ = value.func f₁ x₁ R₁ S₁ e₁ H₁ σ₁, from eq.trans h this,
    show decidable (value.func f₁ x₁ R₁ S₁ e₁ H₁ σ₁ = v₂), from
    value.cases_on (λv₂, decidable (value.func f₁ x₁ R₁ S₁ e₁ H₁ σ₁ = v₂)) v₂ (
      have value.func f₁ x₁ R₁ S₁ e₁ H₁ σ₁ ≠ value.true, by contradiction,
      show decidable (value.func f₁ x₁ R₁ S₁ e₁ H₁ σ₁ = value.true), from is_false this
    ) (
      have value.func f₁ x₁ R₁ S₁ e₁ H₁ σ₁ ≠ value.false, by contradiction,
      show decidable (value.func f₁ x₁ R₁ S₁ e₁ H₁ σ₁ = value.false), from is_false this
    ) (
      assume n: ℤ,
      have value.func f₁ x₁ R₁ S₁ e₁ H₁ σ₁ ≠ value.num n, by contradiction,
      show decidable (value.func f₁ x₁ R₁ S₁ e₁ H₁ σ₁ = value.num n), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂ H₂ σ₂,
      have R₁.sizeof < v₁.sizeof, from v₁_is_func.symm ▸ sizeof_value_func_R,
      have decidable (R₁ = R₂), from spec.dec_eq R₁ R₂,
      have S₁.sizeof < v₁.sizeof, from v₁_is_func.symm ▸ sizeof_value_func_S,
      have decidable (S₁ = S₂), from spec.dec_eq S₁ S₂,
      have e₁.sizeof < v₁.sizeof, from v₁_is_func.symm ▸ sizeof_value_func_e,
      have decidable (e₁ = e₂), from exp.dec_eq e₁ e₂,
      have H₁.sizeof < v₁.sizeof, from v₁_is_func.symm ▸ sizeof_value_func_H,
      have decidable (H₁ = H₂), from history.dec_eq H₁ H₂,
      have σ₁.sizeof < v₁.sizeof, from v₁_is_func.symm ▸ sizeof_value_func_σ,
      have decidable (σ₁ = σ₂), from env.dec_eq σ₁ σ₂,

      if h: (f₁ = f₂) ∧ (x₁ = x₂) ∧ (R₁ = R₂) ∧ (S₁ = S₂) ∧ (e₁ = e₂) ∧ (H₁ = H₂) ∧ (σ₁ = σ₂) then (
        have value.func f₁ x₁ R₁ S₁ e₁ H₁ σ₁ = value.func f₂ x₂ R₂ S₂ e₂ H₂ σ₂,
        from h.left ▸ h.right.left ▸ h.right.right.left ▸ h.right.right.right.left ▸
             h.right.right.right.right.left ▸ h.right.right.right.right.right.left ▸
             h.right.right.right.right.right.right ▸ rfl,
        show decidable (value.func f₁ x₁ R₁ S₁ e₁ H₁ σ₁ = value.func f₂ x₂ R₂ S₂ e₂ H₂ σ₂),
        from is_true this
      ) else (
        have value.func f₁ x₁ R₁ S₁ e₁ H₁ σ₁ ≠ value.func f₂ x₂ R₂ S₂ e₂ H₂ σ₂, from (
          assume : value.func f₁ x₁ R₁ S₁ e₁ H₁ σ₁ = value.func f₂ x₂ R₂ S₂ e₂ H₂ σ₂,
          show «false», from h (value.func.inj this)
        ),
        show decidable (value.func f₁ x₁ R₁ S₁ e₁ H₁ σ₁ = value.func f₂ x₂ R₂ S₂ e₂ H₂ σ₂),
        from is_false this
      )
    )
  ) rfl

with exp.dec_eq : ∀ (e₁ e₂: exp), decidable (e₁ = e₂)
| e₁ e₂ :=
  let z := e₁ in
  have h: z = e₁, from rfl,
  exp.cases_on (λe₁, (z = e₁) → decidable (e₁ = e₂)) e₁ (
    assume x₁ e₁',
    assume : z = exp.true x₁ e₁',
    have e₁_is_tru: e₁ = exp.true x₁ e₁', from eq.trans h this,
    show decidable (exp.true x₁ e₁' = e₂),
    from exp.cases_on (λe₂, decidable (exp.true x₁ e₁' = e₂)) e₂ (
      assume x₂ e₂',
      have e₁'.sizeof < e₁.sizeof, from e₁_is_tru.symm ▸ sizeof_exp_true,
      have decidable (e₁' = e₂'), from exp.dec_eq e₁' e₂',
      if h: (x₁ = x₂) ∧ (e₁' = e₂') then (
        have exp.true x₁ e₁' = exp.true x₂ e₂',
        from h.left ▸ h.right ▸ rfl,
        show decidable (exp.true x₁ e₁' = exp.true x₂ e₂'),
        from is_true this
      ) else (
        have exp.true x₁ e₁' ≠ exp.true x₂ e₂', from (
          assume : exp.true x₁ e₁' = exp.true x₂ e₂',
          show «false», from h (exp.true.inj this)
        ),
        show decidable (exp.true x₁ e₁' = exp.true x₂ e₂'),
        from is_false this
      )
    ) (
      assume x₂ e₂',
      have exp.true x₁ e₁' ≠ exp.false x₂ e₂', by contradiction,
      show decidable (exp.true x₁ e₁' = exp.false x₂ e₂'), from is_false this
    ) (
      assume x₂ n₂ e₂',
      have exp.true x₁ e₁' ≠ exp.num x₂ n₂ e₂', by contradiction,
      show decidable (exp.true x₁ e₁' = exp.num x₂ n₂ e₂'), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have exp.true x₁ e₁' ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', by contradiction,
      show decidable (exp.true x₁ e₁' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''), from is_false this
    ) (
      assume x₂ op₂ y₂ e₂',
      have exp.true x₁ e₁' ≠ exp.unop x₂ op₂ y₂ e₂', by contradiction,
      show decidable (exp.true x₁ e₁' = exp.unop x₂ op₂ y₂ e₂'), from is_false this
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have exp.true x₁ e₁' ≠ exp.binop x₂ op₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.true x₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ y₂ z₂ e₂',
      have exp.true x₁ e₁' ≠ exp.app x₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.true x₁ e₁' = exp.app x₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ e₂' e₂'',
      have exp.true x₁ e₁' ≠ exp.ite x₂ e₂' e₂'', by contradiction,
      show decidable (exp.true x₁ e₁' = exp.ite x₂ e₂' e₂''), from is_false this
    ) (
      assume x₂,
      have exp.true x₁ e₁' ≠ exp.return x₂, by contradiction,
      show decidable (exp.true x₁ e₁' = exp.return x₂), from is_false this
    )
  ) (
    assume x₁ e₁',
    assume : z = exp.false x₁ e₁',
    have e₁_is_false: e₁ = exp.false x₁ e₁', from eq.trans h this,
    show decidable (exp.false x₁ e₁' = e₂),
    from exp.cases_on (λe₂, decidable (exp.false x₁ e₁' = e₂)) e₂ (
      assume x₂ e₂',
      have exp.false x₁ e₁' ≠ exp.true x₂ e₂', by contradiction,
      show decidable (exp.false x₁ e₁' = exp.true x₂ e₂'), from is_false this
    ) (
      assume x₂ e₂',
      have e₁'.sizeof < e₁.sizeof, from e₁_is_false.symm ▸ sizeof_exp_false,
      have decidable (e₁' = e₂'), from exp.dec_eq e₁' e₂',
      if h: (x₁ = x₂) ∧ (e₁' = e₂') then (
        have exp.false x₁ e₁' = exp.false x₂ e₂',
        from h.left ▸ h.right ▸ rfl,
        show decidable (exp.false x₁ e₁' = exp.false x₂ e₂'),
        from is_true this
      ) else (
        have exp.false x₁ e₁' ≠ exp.false x₂ e₂', from (
          assume : exp.false x₁ e₁' = exp.false x₂ e₂',
          show «false», from h (exp.false.inj this)
        ),
        show decidable (exp.false x₁ e₁' = exp.false x₂ e₂'),
        from is_false this
      )
    ) (
      assume x₂ n₂ e₂',
      have exp.false x₁ e₁' ≠ exp.num x₂ n₂ e₂', by contradiction,
      show decidable (exp.false x₁ e₁' = exp.num x₂ n₂ e₂'), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have exp.false x₁ e₁' ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', by contradiction,
      show decidable (exp.false x₁ e₁' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''), from is_false this
    ) (
      assume x₂ op₂ y₂ e₂',
      have exp.false x₁ e₁' ≠ exp.unop x₂ op₂ y₂ e₂', by contradiction,
      show decidable (exp.false x₁ e₁' = exp.unop x₂ op₂ y₂ e₂'), from is_false this
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have exp.false x₁ e₁' ≠ exp.binop x₂ op₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.false x₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ y₂ z₂ e₂',
      have exp.false x₁ e₁' ≠ exp.app x₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.false x₁ e₁' = exp.app x₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ e₂' e₂'',
      have exp.false x₁ e₁' ≠ exp.ite x₂ e₂' e₂'', by contradiction,
      show decidable (exp.false x₁ e₁' = exp.ite x₂ e₂' e₂''), from is_false this
    ) (
      assume x₂,
      have exp.false x₁ e₁' ≠ exp.return x₂, by contradiction,
      show decidable (exp.false x₁ e₁' = exp.return x₂), from is_false this
    )
  ) (
    assume x₁ n₁ e₁',
    assume : z = exp.num x₁ n₁ e₁',
    have e₁_is_num: e₁ = exp.num x₁ n₁ e₁', from eq.trans h this,
    show decidable (exp.num x₁ n₁ e₁' = e₂),
    from exp.cases_on (λe₂, decidable (exp.num x₁ n₁ e₁' = e₂)) e₂ (
      assume x₂ e₂',
      have exp.num x₁ n₁ e₁' ≠ exp.true x₂ e₂', by contradiction,
      show decidable (exp.num x₁ n₁ e₁' = exp.true x₂ e₂'), from is_false this
    ) (
      assume x₂ e₂',
      have exp.num x₁ n₁ e₁' ≠ exp.false x₂ e₂', by contradiction,
      show decidable (exp.num x₁ n₁ e₁' = exp.false x₂ e₂'), from is_false this
    ) (
      assume x₂ n₂ e₂',
      have e₁'.sizeof < e₁.sizeof, from e₁_is_num.symm ▸ sizeof_exp_num,
      have decidable (e₁' = e₂'), from exp.dec_eq e₁' e₂',
      if h: (x₁ = x₂) ∧ (n₁ = n₂) ∧ (e₁' = e₂') then (
        have exp.num x₁ n₁ e₁' = exp.num x₂ n₂ e₂',
        from h.left ▸ h.right.left ▸ h.right.right ▸ rfl,
        show decidable (exp.num x₁ n₁ e₁' = exp.num x₂ n₂ e₂'),
        from is_true this
      ) else (
        have exp.num x₁ n₁ e₁' ≠ exp.num x₂ n₂ e₂', from (
          assume : exp.num x₁ n₁ e₁' = exp.num x₂ n₂ e₂',
          show «false», from h (exp.num.inj this)
        ),
        show decidable (exp.num x₁ n₁ e₁' = exp.num x₂ n₂ e₂'),
        from is_false this
      )
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have exp.num x₁ n₁ e₁' ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', by contradiction,
      show decidable (exp.num x₁ n₁ e₁' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''), from is_false this
    ) (
      assume x₂ op₂ y₂ e₂',
      have exp.num x₁ n₁ e₁' ≠ exp.unop x₂ op₂ y₂ e₂', by contradiction,
      show decidable (exp.num x₁ n₁ e₁' = exp.unop x₂ op₂ y₂ e₂'), from is_false this
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have exp.num x₁ n₁ e₁' ≠ exp.binop x₂ op₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.num x₁ n₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ y₂ z₂ e₂',
      have exp.num x₁ n₁ e₁' ≠ exp.app x₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.num x₁ n₁ e₁' = exp.app x₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ e₂' e₂'',
      have exp.num x₁ n₁ e₁' ≠ exp.ite x₂ e₂' e₂'', by contradiction,
      show decidable (exp.num x₁ n₁ e₁' = exp.ite x₂ e₂' e₂''), from is_false this
    ) (
      assume x₂,
      have exp.num x₁ n₁ e₁' ≠ exp.return x₂, by contradiction,
      show decidable (exp.num x₁ n₁ e₁' = exp.return x₂), from is_false this
    )
  ) (
    assume f₁ x₁ R₁ S₁ e₁' e₁'',
    assume : z = exp.func f₁ x₁ R₁ S₁ e₁' e₁'',
    have e₁_is_func: e₁ = exp.func f₁ x₁ R₁ S₁ e₁' e₁'', from eq.trans h this,
    show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = e₂),
    from exp.cases_on (λe₂, decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = e₂)) e₂ (
      assume x₂ e₂',
      have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.true x₂ e₂', by contradiction,
      show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.true x₂ e₂'), from is_false this
    ) (
      assume x₂ e₂',
      have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.false x₂ e₂', by contradiction,
      show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.false x₂ e₂'), from is_false this
    ) (
      assume x₂ n₂ e₂',
      have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.num x₂ n₂ e₂', by contradiction,
      show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.num x₂ n₂ e₂'), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have R₁.sizeof < e₁.sizeof, from e₁_is_func.symm ▸ sizeof_exp_func_R,
      have decidable (R₁ = R₂), from spec.dec_eq R₁ R₂,
      have S₁.sizeof < e₁.sizeof, from e₁_is_func.symm ▸ sizeof_exp_func_S,
      have decidable (S₁ = S₂), from spec.dec_eq S₁ S₂,
      have e₁'.sizeof < e₁.sizeof, from e₁_is_func.symm ▸ sizeof_exp_func_e₁,
      have decidable (e₁' = e₂'), from exp.dec_eq e₁' e₂',
      have e₁''.sizeof < e₁.sizeof, from e₁_is_func.symm ▸ sizeof_exp_func_e₂,
      have decidable (e₁'' = e₂''), from exp.dec_eq e₁'' e₂'',

      if h: (f₁ = f₂) ∧ (x₁ = x₂) ∧ (R₁ = R₂) ∧ (S₁ = S₂) ∧ (e₁' = e₂') ∧ (e₁'' = e₂'') then (
        have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.func f₂ x₂ R₂ S₂ e₂' e₂'',
        from h.left ▸ h.right.left ▸ h.right.right.left ▸ h.right.right.right.left ▸
             h.right.right.right.right.left ▸ h.right.right.right.right.right ▸ rfl,
        show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''),
        from is_true this
      ) else (
        have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', from (
          assume : exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.func f₂ x₂ R₂ S₂ e₂' e₂'',
          show «false», from h (exp.func.inj this)
        ),
        show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''),
        from is_false this
      )
    ) (
      assume x₂ op₂ y₂ e₂',
      have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.unop x₂ op₂ y₂ e₂', by contradiction,
      show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.unop x₂ op₂ y₂ e₂'), from is_false this
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.binop x₂ op₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.binop x₂ op₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ y₂ z₂ e₂',
      have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.app x₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.app x₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ e₂' e₂'',
      have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.ite x₂ e₂' e₂'', by contradiction,
      show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.ite x₂ e₂' e₂''), from is_false this
    ) (
      assume x₂,
      have exp.func f₁ x₁ R₁ S₁ e₁' e₁'' ≠ exp.return x₂, by contradiction,
      show decidable (exp.func f₁ x₁ R₁ S₁ e₁' e₁'' = exp.return x₂), from is_false this
    )
  ) (
    assume x₁ op₁ y₁ e₁',
    assume : z = exp.unop x₁ op₁ y₁ e₁',
    have e₁_is_unop: e₁ = exp.unop x₁ op₁ y₁ e₁', from eq.trans h this,
    show decidable (exp.unop x₁ op₁ y₁ e₁' = e₂),
    from exp.cases_on (λe₂, decidable (exp.unop x₁ op₁ y₁ e₁' = e₂)) e₂ (
      assume x₂ e₂',
      have exp.unop x₁ op₁ y₁ e₁' ≠ exp.true x₂ e₂', by contradiction,
      show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.true x₂ e₂'), from is_false this
    ) (
      assume x₂ e₂',
      have exp.unop x₁ op₁ y₁ e₁' ≠ exp.false x₂ e₂', by contradiction,
      show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.false x₂ e₂'), from is_false this
    ) (
      assume x₂ n₂ e₂',
      have exp.unop x₁ op₁ y₁ e₁' ≠ exp.num x₂ n₂ e₂', by contradiction,
      show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.num x₂ n₂ e₂'), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have exp.unop x₁ op₁ y₁ e₁' ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', by contradiction,
      show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''), from is_false this
    ) (
      assume x₂ op₂ y₂ e₂',
      have e₁'.sizeof < e₁.sizeof, from e₁_is_unop.symm ▸ sizeof_exp_unop,
      have decidable (e₁' = e₂'), from exp.dec_eq e₁' e₂',
      if h: (x₁ = x₂) ∧ (op₁ = op₂) ∧ (y₁ = y₂) ∧ (e₁' = e₂') then (
        have exp.unop x₁ op₁ y₁ e₁' = exp.unop x₂ op₂ y₂ e₂',
        from h.left ▸ h.right.left ▸ h.right.right.left ▸ h.right.right.right ▸ rfl,
        show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.unop x₂ op₂ y₂ e₂'),
        from is_true this
      ) else (
        have exp.unop x₁ op₁ y₁ e₁' ≠ exp.unop x₂ op₂ y₂ e₂', from (
          assume : exp.unop x₁ op₁ y₁ e₁' = exp.unop x₂ op₂ y₂ e₂',
          show «false», from h (exp.unop.inj this)
        ),
        show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.unop x₂ op₂ y₂ e₂'),
        from is_false this
      )
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have exp.unop x₁ op₁ y₁ e₁' ≠ exp.binop x₂ op₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ y₂ z₂ e₂',
      have exp.unop x₁ op₁ y₁ e₁' ≠ exp.app x₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.app x₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ e₂' e₂'',
      have exp.unop x₁ op₁ y₁ e₁' ≠ exp.ite x₂ e₂' e₂'', by contradiction,
      show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.ite x₂ e₂' e₂''), from is_false this
    ) (
      assume x₂,
      have exp.unop x₁ op₁ y₁ e₁' ≠ exp.return x₂, by contradiction,
      show decidable (exp.unop x₁ op₁ y₁ e₁' = exp.return x₂), from is_false this
    )
  ) (
    assume x₁ op₁ y₁ z₁ e₁',
    assume : z = exp.binop x₁ op₁ y₁ z₁ e₁',
    have e₁_is_binop: e₁ = exp.binop x₁ op₁ y₁ z₁ e₁', from eq.trans h this,
    show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = e₂),
    from exp.cases_on (λe₂, decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = e₂)) e₂ (
      assume x₂ e₂',
      have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.true x₂ e₂', by contradiction,
      show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.true x₂ e₂'), from is_false this
    ) (
      assume x₂ e₂',
      have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.false x₂ e₂', by contradiction,
      show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.false x₂ e₂'), from is_false this
    ) (
      assume x₂ n₂ e₂',
      have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.num x₂ n₂ e₂', by contradiction,
      show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.num x₂ n₂ e₂'), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', by contradiction,
      show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''), from is_false this
    ) (
      assume x₂ op₂ y₂ e₂',
      have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.unop x₂ op₂ y₂ e₂', by contradiction,
      show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.unop x₂ op₂ y₂ e₂'), from is_false this
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have e₁'.sizeof < e₁.sizeof, from e₁_is_binop.symm ▸ sizeof_exp_binop,
      have decidable (e₁' = e₂'), from exp.dec_eq e₁' e₂',
      if h: (x₁ = x₂) ∧ (op₁ = op₂) ∧ (y₁ = y₂) ∧ (z₁ = z₂) ∧ (e₁' = e₂') then (
        have exp.binop x₁ op₁ y₁ z₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂',
        from h.left ▸ h.right.left ▸ h.right.right.left ▸ h.right.right.right.left ▸
             h.right.right.right.right ▸ rfl,
        show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂'),
        from is_true this
      ) else (
        have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.binop x₂ op₂ y₂ z₂ e₂', from (
          assume : exp.binop x₁ op₁ y₁ z₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂',
          show «false», from h (exp.binop.inj this)
        ),
        show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂'),
        from is_false this
      )
    ) (
      assume x₂ y₂ z₂ e₂',
      have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.app x₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.app x₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ e₂' e₂'',
      have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.ite x₂ e₂' e₂'', by contradiction,
      show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.ite x₂ e₂' e₂''), from is_false this
    ) (
      assume x₂,
      have exp.binop x₁ op₁ y₁ z₁ e₁' ≠ exp.return x₂, by contradiction,
      show decidable (exp.binop x₁ op₁ y₁ z₁ e₁' = exp.return x₂), from is_false this
    )
  ) (
    assume x₁ y₁ z₁ e₁',
    assume : z = exp.app x₁ y₁ z₁ e₁',
    have e₁_is_app: e₁ = exp.app x₁ y₁ z₁ e₁', from eq.trans h this,
    show decidable (exp.app x₁ y₁ z₁ e₁' = e₂),
    from exp.cases_on (λe₂, decidable (exp.app x₁ y₁ z₁ e₁' = e₂)) e₂ (
      assume x₂ e₂',
      have exp.app x₁ y₁ z₁ e₁' ≠ exp.true x₂ e₂', by contradiction,
      show decidable (exp.app x₁ y₁ z₁ e₁' = exp.true x₂ e₂'), from is_false this
    ) (
      assume x₂ e₂',
      have exp.app x₁ y₁ z₁ e₁' ≠ exp.false x₂ e₂', by contradiction,
      show decidable (exp.app x₁ y₁ z₁ e₁' = exp.false x₂ e₂'), from is_false this
    ) (
      assume x₂ n₂ e₂',
      have exp.app x₁ y₁ z₁ e₁' ≠ exp.num x₂ n₂ e₂', by contradiction,
      show decidable (exp.app x₁ y₁ z₁ e₁' = exp.num x₂ n₂ e₂'), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have exp.app x₁ y₁ z₁ e₁' ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', by contradiction,
      show decidable (exp.app x₁ y₁ z₁ e₁' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''), from is_false this
    ) (
      assume x₂ op₂ y₂ e₂',
      have exp.app x₁ y₁ z₁ e₁' ≠ exp.unop x₂ op₂ y₂ e₂', by contradiction,
      show decidable (exp.app x₁ y₁ z₁ e₁' = exp.unop x₂ op₂ y₂ e₂'), from is_false this
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have exp.app x₁ y₁ z₁ e₁' ≠ exp.binop x₂ op₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.app x₁ y₁ z₁ e₁' = exp.binop x₂ op₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ y₂ z₂ e₂',
      have e₁'.sizeof < e₁.sizeof, from e₁_is_app.symm ▸ sizeof_exp_app,
      have decidable (e₁' = e₂'), from exp.dec_eq e₁' e₂',
      if h: (x₁ = x₂) ∧ (y₁ = y₂) ∧ (z₁ = z₂) ∧ (e₁' = e₂') then (
        have exp.app x₁ y₁ z₁ e₁' = exp.app x₂ y₂ z₂ e₂',
        from h.left ▸ h.right.left ▸ h.right.right.left ▸ h.right.right.right ▸ rfl,
        show decidable (exp.app x₁ y₁ z₁ e₁' = exp.app x₂ y₂ z₂ e₂'),
        from is_true this
      ) else (
        have exp.app x₁ y₁ z₁ e₁' ≠ exp.app x₂ y₂ z₂ e₂', from (
          assume : exp.app x₁ y₁ z₁ e₁' = exp.app x₂ y₂ z₂ e₂',
          show «false», from h (exp.app.inj this)
        ),
        show decidable (exp.app x₁ y₁ z₁ e₁' = exp.app x₂ y₂ z₂ e₂'),
        from is_false this
      )
    ) (
      assume x₂ e₂' e₂'',
      have exp.app x₁ y₁ z₁ e₁' ≠ exp.ite x₂ e₂' e₂'', by contradiction,
      show decidable (exp.app x₁ y₁ z₁ e₁' = exp.ite x₂ e₂' e₂''), from is_false this
    ) (
      assume x₂,
      have exp.app x₁ y₁ z₁ e₁' ≠ exp.return x₂, by contradiction,
      show decidable (exp.app x₁ y₁ z₁ e₁' = exp.return x₂), from is_false this
    )
  ) (
    assume x₁ e₁' e₁'',
    assume : z = exp.ite x₁ e₁' e₁'',
    have e₁_is_ite: e₁ = exp.ite x₁ e₁' e₁'', from eq.trans h this,
    show decidable (exp.ite x₁ e₁' e₁'' = e₂),
    from exp.cases_on (λe₂, decidable (exp.ite x₁ e₁' e₁'' = e₂)) e₂ (
      assume x₂ e₂',
      have exp.ite x₁ e₁' e₁'' ≠ exp.true x₂ e₂', by contradiction,
      show decidable (exp.ite x₁ e₁' e₁'' = exp.true x₂ e₂'), from is_false this
    ) (
      assume x₂ e₂',
      have exp.ite x₁ e₁' e₁'' ≠ exp.false x₂ e₂', by contradiction,
      show decidable (exp.ite x₁ e₁' e₁'' = exp.false x₂ e₂'), from is_false this
    ) (
      assume x₂ n₂ e₂',
      have exp.ite x₁ e₁' e₁'' ≠ exp.num x₂ n₂ e₂', by contradiction,
      show decidable (exp.ite x₁ e₁' e₁'' = exp.num x₂ n₂ e₂'), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have exp.ite x₁ e₁' e₁'' ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', by contradiction,
      show decidable (exp.ite x₁ e₁' e₁'' = exp.func f₂ x₂ R₂ S₂ e₂' e₂''), from is_false this
    ) (
      assume x₂ op₂ y₂ e₂',
      have exp.ite x₁ e₁' e₁'' ≠ exp.unop x₂ op₂ y₂ e₂', by contradiction,
      show decidable (exp.ite x₁ e₁' e₁'' = exp.unop x₂ op₂ y₂ e₂'), from is_false this
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have exp.ite x₁ e₁' e₁'' ≠ exp.binop x₂ op₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.ite x₁ e₁' e₁'' = exp.binop x₂ op₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ y₂ z₂ e₂',
      have exp.ite x₁ e₁' e₁'' ≠ exp.app x₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.ite x₁ e₁' e₁'' = exp.app x₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ e₂' e₂'',
      have e₁'.sizeof < e₁.sizeof, from e₁_is_ite.symm ▸ sizeof_exp_ite_e₁,
      have decidable (e₁' = e₂'), from exp.dec_eq e₁' e₂',
      have e₁''.sizeof < e₁.sizeof, from e₁_is_ite.symm ▸ sizeof_exp_ite_e₂,
      have decidable (e₁'' = e₂''), from exp.dec_eq e₁'' e₂'',
      if h: (x₁ = x₂) ∧ (e₁' = e₂') ∧ (e₁'' = e₂'') then (
        have exp.ite x₁ e₁' e₁'' = exp.ite x₂ e₂' e₂'',
        from h.left ▸ h.right.left ▸ h.right.right ▸ rfl,
        show decidable (exp.ite x₁ e₁' e₁'' = exp.ite x₂ e₂' e₂''),
        from is_true this
      ) else (
        have exp.ite x₁ e₁' e₁'' ≠ exp.ite x₂ e₂' e₂'', from (
          assume : exp.ite x₁ e₁' e₁'' = exp.ite x₂ e₂' e₂'',
          show «false», from h (exp.ite.inj this)
        ),
        show decidable (exp.ite x₁ e₁' e₁'' = exp.ite x₂ e₂' e₂''),
        from is_false this
      )
    ) (
      assume x₂,
      have exp.ite x₁ e₁' e₁'' ≠ exp.return x₂, by contradiction,
      show decidable (exp.ite x₁ e₁' e₁'' = exp.return x₂), from is_false this
    )
  ) (
    assume x₁,
    assume : z = exp.return x₁,
    have e₁_is_tru: e₁ = exp.return x₁, from eq.trans h this,
    show decidable (exp.return x₁ = e₂),
    from exp.cases_on (λe₂, decidable (exp.return x₁ = e₂)) e₂ (
      assume x₂ e₂',
      have exp.return x₁ ≠ exp.true x₂ e₂', by contradiction,
      show decidable (exp.return x₁ = exp.true x₂ e₂'), from is_false this
    ) (
      assume x₂ e₂',
      have exp.return x₁ ≠ exp.false x₂ e₂', by contradiction,
      show decidable (exp.return x₁ = exp.false x₂ e₂'), from is_false this
    ) (
      assume x₂ n₂ e₂',
      have exp.return x₁ ≠ exp.num x₂ n₂ e₂', by contradiction,
      show decidable (exp.return x₁ = exp.num x₂ n₂ e₂'), from is_false this
    ) (
      assume f₂ x₂ R₂ S₂ e₂' e₂'',
      have exp.return x₁ ≠ exp.func f₂ x₂ R₂ S₂ e₂' e₂'', by contradiction,
      show decidable (exp.return x₁ = exp.func f₂ x₂ R₂ S₂ e₂' e₂''), from is_false this
    ) (
      assume x₂ op₂ y₂ e₂',
      have exp.return x₁ ≠ exp.unop x₂ op₂ y₂ e₂', by contradiction,
      show decidable (exp.return x₁ = exp.unop x₂ op₂ y₂ e₂'), from is_false this
    ) (
      assume x₂ op₂ y₂ z₂ e₂',
      have exp.return x₁ ≠ exp.binop x₂ op₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.return x₁ = exp.binop x₂ op₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ y₂ z₂ e₂',
      have exp.return x₁ ≠ exp.app x₂ y₂ z₂ e₂', by contradiction,
      show decidable (exp.return x₁ = exp.app x₂ y₂ z₂ e₂'), from is_false this
    ) (
      assume x₂ e₂' e₂'',
      have exp.return x₁ ≠ exp.ite x₂ e₂' e₂'', by contradiction,
      show decidable (exp.return x₁ = exp.ite x₂ e₂' e₂''), from is_false this
    ) (
      assume x₂,
      if h: x₁ = x₂ then (
        have exp.return x₁ = exp.return x₂, from h ▸ rfl,
        show decidable (exp.return x₁ = exp.return x₂),
        from is_true this
      ) else (
        have exp.return x₁ ≠ exp.return x₂, from (
          assume : exp.return x₁ = exp.return x₂,
          show «false», from h (exp.return.inj this)
        ),
        show decidable (exp.return x₁ = exp.return x₂),
        from is_false this
      )
    )
  ) rfl

with term.dec_eq : ∀ (t₁ t₂: term), decidable (t₁ = t₂)
| t₁ t₂ :=
  let z := t₁ in
  have h: z = t₁, from rfl,
  term.cases_on (λt₁, (z = t₁) → decidable (t₁ = t₂)) t₁ (
    assume v₁,
    assume : z = term.value v₁,
    have t₁_id: t₁ = term.value v₁, from eq.trans h this,
    show decidable (term.value v₁ = t₂),
    from term.cases_on (λt₂, decidable (term.value v₁ = t₂)) t₂ (
      assume v₂,
      have v₁.sizeof < t₁.sizeof, from t₁_id.symm ▸ sizeof_term_value,
      have decidable (v₁ = v₂), from value.dec_eq v₁ v₂,
      if h: v₁ = v₂ then (
        have term.value v₁ = term.value v₂, from h ▸ rfl,
        show decidable (term.value v₁ = term.value v₂),
        from is_true this
      ) else (
        have term.value v₁ ≠ term.value v₂, from (
          assume : term.value v₁ = term.value v₂,
          show «false», from h (term.value.inj this)
        ),
        show decidable (term.value v₁ = term.value v₂),
        from is_false this
      )
    ) (
      assume x₂,
      have term.value v₁ ≠ term.var x₂, by contradiction,
      show decidable (term.value v₁ = term.var x₂), from is_false this
    ) (
      assume op₂ t₂',
      have term.value v₁ ≠ term.unop op₂ t₂', by contradiction,
      show decidable (term.value v₁ = term.unop op₂ t₂'), from is_false this
    ) (
      assume op₂ t₂' t₂'',
      have term.value v₁ ≠ term.binop op₂ t₂' t₂'', by contradiction,
      show decidable (term.value v₁ = term.binop op₂ t₂' t₂''), from is_false this
    ) (
      assume t₂' t₂'',
      have term.value v₁ ≠ term.app t₂' t₂'', by contradiction,
      show decidable (term.value v₁ = term.app t₂' t₂''), from is_false this
    )
  ) (
    assume x₁,
    assume : z = term.var x₁,
    have t₁_id: t₁ = term.var x₁, from eq.trans h this,
    show decidable (term.var x₁ = t₂),
    from term.cases_on (λt₂, decidable (term.var x₁ = t₂)) t₂ (
      assume v₂,
      have term.var x₁ ≠ term.value v₂, by contradiction,
      show decidable (term.var x₁ = term.value v₂), from is_false this
    ) (
      assume x₂,
      if h: x₁ = x₂ then (
        have term.var x₁ = term.var x₂, from h ▸ rfl,
        show decidable (term.var x₁ = term.var x₂),
        from is_true this
      ) else (
        have term.var x₁ ≠ term.var x₂, from (
          assume : term.var x₁ = term.var x₂,
          show «false», from h (term.var.inj this)
        ),
        show decidable (term.var x₁ = term.var x₂),
        from is_false this
      )
    ) (
      assume op₂ t₂',
      have term.var x₁ ≠ term.unop op₂ t₂', by contradiction,
      show decidable (term.var x₁ = term.unop op₂ t₂'), from is_false this
    ) (
      assume op₂ t₂' t₂'',
      have term.var x₁ ≠ term.binop op₂ t₂' t₂'', by contradiction,
      show decidable (term.var x₁ = term.binop op₂ t₂' t₂''), from is_false this
    ) (
      assume t₂' t₂'',
      have term.var x₁ ≠ term.app t₂' t₂'', by contradiction,
      show decidable (term.var x₁ = term.app t₂' t₂''), from is_false this
    )
  ) (
    assume op₁ t₁',
    assume : z = term.unop op₁ t₁',
    have t₁_id: t₁ = term.unop op₁ t₁', from eq.trans h this,
    show decidable (term.unop op₁ t₁' = t₂),
    from term.cases_on (λt₂, decidable (term.unop op₁ t₁' = t₂)) t₂ (
      assume v₂,
      have term.unop op₁ t₁' ≠ term.value v₂, by contradiction,
      show decidable (term.unop op₁ t₁' = term.value v₂), from is_false this
    ) (
      assume x₂,
      have term.unop op₁ t₁' ≠ term.var x₂, by contradiction,
      show decidable (term.unop op₁ t₁' = term.var x₂), from is_false this
    ) (
      assume op₂ t₂',
      have t₁'.sizeof < t₁.sizeof, from t₁_id.symm ▸ sizeof_term_unop,
      have decidable (t₁' = t₂'), from term.dec_eq t₁' t₂',
      if h: (op₁ = op₂) ∧ (t₁' = t₂') then (
        have term.unop op₁ t₁' = term.unop op₂ t₂',
        from h.left ▸ h.right ▸ rfl,
        show decidable (term.unop op₁ t₁' = term.unop op₂ t₂'),
        from is_true this
      ) else (
        have term.unop op₁ t₁' ≠ term.unop op₂ t₂', from (
          assume : term.unop op₁ t₁' = term.unop op₂ t₂',
          show «false», from h (term.unop.inj this)
        ),
        show decidable (term.unop op₁ t₁' = term.unop op₂ t₂'),
        from is_false this
      )
    ) (
      assume op₂ t₂' t₂'',
      have term.unop op₁ t₁' ≠ term.binop op₂ t₂' t₂'', by contradiction,
      show decidable (term.unop op₁ t₁' = term.binop op₂ t₂' t₂''), from is_false this
    ) (
      assume t₂' t₂'',
      have term.unop op₁ t₁' ≠ term.app t₂' t₂'', by contradiction,
      show decidable (term.unop op₁ t₁' = term.app t₂' t₂''), from is_false this
    )
  ) (
    assume op₁ t₁' t₁'',
    assume : z = term.binop op₁ t₁' t₁'',
    have t₁_id: t₁ = term.binop op₁ t₁' t₁'', from eq.trans h this,
    show decidable (term.binop op₁ t₁' t₁'' = t₂),
    from term.cases_on (λt₂, decidable (term.binop op₁ t₁' t₁'' = t₂)) t₂ (
      assume v₂,
      have term.binop op₁ t₁' t₁'' ≠ term.value v₂, by contradiction,
      show decidable (term.binop op₁ t₁' t₁'' = term.value v₂), from is_false this
    ) (
      assume x₂,
      have term.binop op₁ t₁' t₁'' ≠ term.var x₂, by contradiction,
      show decidable (term.binop op₁ t₁' t₁'' = term.var x₂), from is_false this
    ) (
      assume op₂ t₂',
      have term.binop op₁ t₁' t₁'' ≠ term.unop op₂ t₂', by contradiction,
      show decidable (term.binop op₁ t₁' t₁'' = term.unop op₂ t₂'), from is_false this
    ) (
      assume op₂ t₂' t₂'',
      have t₁'.sizeof < t₁.sizeof, from t₁_id.symm ▸ sizeof_term_binop₁,
      have decidable (t₁' = t₂'), from term.dec_eq t₁' t₂',
      have t₁''.sizeof < t₁.sizeof, from t₁_id.symm ▸ sizeof_term_binop₂,
      have decidable (t₁'' = t₂''), from term.dec_eq t₁'' t₂'',
      if h: (op₁ = op₂) ∧ (t₁' = t₂') ∧ (t₁'' = t₂'') then (
        have term.binop op₁ t₁' t₁'' = term.binop op₂ t₂' t₂'',
        from h.left ▸ h.right.left ▸ h.right.right ▸ rfl,
        show decidable (term.binop op₁ t₁' t₁'' = term.binop op₂ t₂' t₂''),
        from is_true this
      ) else (
        have term.binop op₁ t₁' t₁'' ≠ term.binop op₂ t₂' t₂'', from (
          assume : term.binop op₁ t₁' t₁'' = term.binop op₂ t₂' t₂'',
          show «false», from h (term.binop.inj this)
        ),
        show decidable (term.binop op₁ t₁' t₁'' = term.binop op₂ t₂' t₂''),
        from is_false this
      )
    ) (
      assume t₂' t₂'',
      have term.binop op₁ t₁' t₁'' ≠ term.app t₂' t₂'', by contradiction,
      show decidable (term.binop op₁ t₁' t₁'' = term.app t₂' t₂''), from is_false this
    )
  ) (
    assume t₁' t₁'',
    assume : z = term.app t₁' t₁'',
    have t₁_id: t₁ = term.app t₁' t₁'', from eq.trans h this,
    show decidable (term.app t₁' t₁'' = t₂),
    from term.cases_on (λt₂, decidable (term.app t₁' t₁'' = t₂)) t₂ (
      assume v₂,
      have term.app t₁' t₁'' ≠ term.value v₂, by contradiction,
      show decidable (term.app t₁' t₁'' = term.value v₂), from is_false this
    ) (
      assume x₂,
      have term.app t₁' t₁'' ≠ term.var x₂, by contradiction,
      show decidable (term.app t₁' t₁'' = term.var x₂), from is_false this
    ) (
      assume op₂ t₂',
      have term.app t₁' t₁'' ≠ term.unop op₂ t₂', by contradiction,
      show decidable (term.app t₁' t₁'' = term.unop op₂ t₂'), from is_false this
    ) (
      assume op₂ t₂' t₂'',
      have term.app t₁' t₁'' ≠ term.binop op₂ t₂' t₂'', by contradiction,
      show decidable (term.app t₁' t₁'' = term.binop op₂ t₂' t₂''), from is_false this
    ) (
      assume t₂' t₂'',
      have t₁'.sizeof < t₁.sizeof, from t₁_id.symm ▸ sizeof_term_app₁,
      have decidable (t₁' = t₂'), from term.dec_eq t₁' t₂',
      have t₁''.sizeof < t₁.sizeof, from t₁_id.symm ▸ sizeof_term_app₂,
      have decidable (t₁'' = t₂''), from term.dec_eq t₁'' t₂'',
      if h: (t₁' = t₂') ∧ (t₁'' = t₂'') then (
        have term.app t₁' t₁'' = term.app t₂' t₂'',
        from h.left ▸ h.right ▸ rfl,
        show decidable (term.app t₁' t₁'' = term.app t₂' t₂''),
        from is_true this
      ) else (
        have term.app t₁' t₁'' ≠ term.app t₂' t₂'', from (
          assume : term.app t₁' t₁'' = term.app t₂' t₂'',
          show «false», from h (term.app.inj this)
        ),
        show decidable (term.app t₁' t₁'' = term.app t₂' t₂''),
        from is_false this
      )
    )
  ) rfl

with spec.dec_eq : ∀ (R₁ R₂: spec), decidable (R₁ = R₂)
| R₁ R₂ :=
  let z := R₁ in
  have h: z = R₁, from rfl,
  spec.cases_on (λR₁, (z = R₁) → decidable (R₁ = R₂)) R₁ (
    assume t₁,
    assume : z = spec.term t₁,
    have R₁_id: R₁ = spec.term t₁, from eq.trans h this,
    show decidable (spec.term t₁ = R₂),
    from spec.cases_on (λR₂, decidable (spec.term t₁ = R₂)) R₂ (
      assume t₂,
      have t₁.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_term,
      have decidable (t₁ = t₂), from term.dec_eq t₁ t₂,
      if h: t₁ = t₂ then (
        have spec.term t₁ = spec.term t₂, from h ▸ rfl,
        show decidable (spec.term t₁ = spec.term t₂),
        from is_true this
      ) else (
        have spec.term t₁ ≠ spec.term t₂, from (
          assume : spec.term t₁ = spec.term t₂,
          show «false», from h (spec.term.inj this)
        ),
        show decidable (spec.term t₁ = spec.term t₂),
        from is_false this
      )
    ) (
      assume S₂,
      have spec.term t₁ ≠ spec.not S₂, by contradiction,
      show decidable (spec.term t₁ = spec.not S₂), from is_false this
    ) (
      assume S₂ S₂',
      have spec.term t₁ ≠ spec.and S₂ S₂', by contradiction,
      show decidable (spec.term t₁ = spec.and S₂ S₂'), from is_false this
    ) (
      assume S₂ S₂',
      have spec.term t₁ ≠ spec.or S₂ S₂', by contradiction,
      show decidable (spec.term t₁ = spec.or S₂ S₂'), from is_false this
    ) (
      assume t₂ x₂ S₂ S₂',
      have spec.term t₁ ≠ spec.func t₂ x₂ S₂ S₂', by contradiction,
      show decidable (spec.term t₁ = spec.func t₂ x₂ S₂ S₂'), from is_false this
    )
  ) (
    assume S₁,
    assume : z = spec.not S₁,
    have R₁_id: R₁ = spec.not S₁, from eq.trans h this,
    show decidable (spec.not S₁ = R₂),
    from spec.cases_on (λR₂, decidable (spec.not S₁ = R₂)) R₂ (
      assume t₂,
      have spec.not S₁ ≠ spec.term t₂, by contradiction,
      show decidable (spec.not S₁ = spec.term t₂), from is_false this
    ) (
      assume S₂,
      have S₁.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_not,
      have decidable (S₁ = S₂), from spec.dec_eq S₁ S₂,
      if h: S₁ = S₂ then (
        have spec.not S₁ = spec.not S₂, from h ▸ rfl,
        show decidable (spec.not S₁ = spec.not S₂),
        from is_true this
      ) else (
        have spec.not S₁ ≠ spec.not S₂, from (
          assume : spec.not S₁ = spec.not S₂,
          show «false», from h (spec.not.inj this)
        ),
        show decidable (spec.not S₁ = spec.not S₂),
        from is_false this
      )
    ) (
      assume S₂ S₂',
      have spec.not S₁ ≠ spec.and S₂ S₂', by contradiction,
      show decidable (spec.not S₁ = spec.and S₂ S₂'), from is_false this
    ) (
      assume S₂ S₂',
      have spec.not S₁ ≠ spec.or S₂ S₂', by contradiction,
      show decidable (spec.not S₁ = spec.or S₂ S₂'), from is_false this
    ) (
      assume t₂ x₂ S₂ S₂',
      have spec.not S₁ ≠ spec.func t₂ x₂ S₂ S₂', by contradiction,
      show decidable (spec.not S₁ = spec.func t₂ x₂ S₂ S₂'), from is_false this
    )
  ) (
    assume S₁ S₁',
    assume : z = spec.and S₁ S₁',
    have R₁_id: R₁ = spec.and S₁ S₁', from eq.trans h this,
    show decidable (spec.and S₁ S₁' = R₂),
    from spec.cases_on (λR₂, decidable (spec.and S₁ S₁' = R₂)) R₂ (
      assume t₂,
      have spec.and S₁ S₁' ≠ spec.term t₂, by contradiction,
      show decidable (spec.and S₁ S₁' = spec.term t₂), from is_false this
    ) (
      assume S₂,
      have spec.and S₁ S₁' ≠ spec.not S₂, by contradiction,
      show decidable (spec.and S₁ S₁' = spec.not S₂), from is_false this
    ) (
      assume S₂ S₂',
      have S₁.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_and₁,
      have decidable (S₁ = S₂), from spec.dec_eq S₁ S₂,
      have S₁'.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_and₂,
      have decidable (S₁' = S₂'), from spec.dec_eq S₁' S₂',
      if h: (S₁ = S₂) ∧ (S₁' = S₂') then (
        have spec.and S₁ S₁' = spec.and S₂ S₂',
        from h.left ▸ h.right ▸ rfl,
        show decidable (spec.and S₁ S₁' = spec.and S₂ S₂'),
        from is_true this
      ) else (
        have spec.and S₁ S₁' ≠ spec.and S₂ S₂', from (
          assume : spec.and S₁ S₁' = spec.and S₂ S₂',
          show «false», from h (spec.and.inj this)
        ),
        show decidable (spec.and S₁ S₁' = spec.and S₂ S₂'),
        from is_false this
      )
    ) (
      assume S₂ S₂',
      have spec.and S₁ S₁' ≠ spec.or S₂ S₂', by contradiction,
      show decidable (spec.and S₁ S₁' = spec.or S₂ S₂'), from is_false this
    ) (
      assume t₂ x₂ S₂ S₂',
      have spec.and S₁ S₁' ≠ spec.func t₂ x₂ S₂ S₂', by contradiction,
      show decidable (spec.and S₁ S₁' = spec.func t₂ x₂ S₂ S₂'), from is_false this
    )
  ) (
    assume S₁ S₁',
    assume : z = spec.or S₁ S₁',
    have R₁_id: R₁ = spec.or S₁ S₁', from eq.trans h this,
    show decidable (spec.or S₁ S₁' = R₂),
    from spec.cases_on (λR₂, decidable (spec.or S₁ S₁' = R₂)) R₂ (
      assume t₂,
      have spec.or S₁ S₁' ≠ spec.term t₂, by contradiction,
      show decidable (spec.or S₁ S₁' = spec.term t₂), from is_false this
    ) (
      assume S₂,
      have spec.or S₁ S₁' ≠ spec.not S₂, by contradiction,
      show decidable (spec.or S₁ S₁' = spec.not S₂), from is_false this
    ) (
      assume S₂ S₂',
      have spec.or S₁ S₁' ≠ spec.and S₂ S₂', by contradiction,
      show decidable (spec.or S₁ S₁' = spec.and S₂ S₂'), from is_false this
    ) (
      assume S₂ S₂',
      have S₁.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_and₁,
      have decidable (S₁ = S₂), from spec.dec_eq S₁ S₂,
      have S₁'.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_and₂,
      have decidable (S₁' = S₂'), from spec.dec_eq S₁' S₂',
      if h: (S₁ = S₂) ∧ (S₁' = S₂') then (
        have spec.or S₁ S₁' = spec.or S₂ S₂',
        from h.left ▸ h.right ▸ rfl,
        show decidable (spec.or S₁ S₁' = spec.or S₂ S₂'),
        from is_true this
      ) else (
        have spec.or S₁ S₁' ≠ spec.or S₂ S₂', from (
          assume : spec.or S₁ S₁' = spec.or S₂ S₂',
          show «false», from h (spec.or.inj this)
        ),
        show decidable (spec.or S₁ S₁' = spec.or S₂ S₂'),
        from is_false this
      )
    ) (
      assume t₂ x₂ S₂ S₂',
      have spec.or S₁ S₁' ≠ spec.func t₂ x₂ S₂ S₂', by contradiction,
      show decidable (spec.or S₁ S₁' = spec.func t₂ x₂ S₂ S₂'), from is_false this
    )
  ) (
    assume t₁ x₁ S₁ S₁',
    assume : z = spec.func t₁ x₁ S₁ S₁',
    have R₁_id: R₁ = spec.func t₁ x₁ S₁ S₁', from eq.trans h this,
    show decidable (spec.func t₁ x₁ S₁ S₁' = R₂),
    from spec.cases_on (λR₂, decidable (spec.func t₁ x₁ S₁ S₁' = R₂)) R₂ (
      assume t₂,
      have spec.func t₁ x₁ S₁ S₁' ≠ spec.term t₂, by contradiction,
      show decidable (spec.func t₁ x₁ S₁ S₁' = spec.term t₂), from is_false this
    ) (
      assume S₂,
      have spec.func t₁ x₁ S₁ S₁' ≠ spec.not S₂, by contradiction,
      show decidable (spec.func t₁ x₁ S₁ S₁' = spec.not S₂), from is_false this
    ) (
      assume S₂ S₂',
      have spec.func t₁ x₁ S₁ S₁' ≠ spec.and S₂ S₂', by contradiction,
      show decidable (spec.func t₁ x₁ S₁ S₁' = spec.and S₂ S₂'), from is_false this
    ) (
      assume S₂ S₂',
      have spec.func t₁ x₁ S₁ S₁' ≠ spec.or S₂ S₂', by contradiction,
      show decidable (spec.func t₁ x₁ S₁ S₁' = spec.or S₂ S₂'), from is_false this
    ) (
      assume t₂ x₂ S₂ S₂',
      have t₁.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_func_t,
      have decidable (t₁ = t₂), from term.dec_eq t₁ t₂,
      have S₁.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_func_R,
      have decidable (S₁ = S₂), from spec.dec_eq S₁ S₂,
      have S₁'.sizeof < R₁.sizeof, from R₁_id.symm ▸ sizeof_spec_func_S,
      have decidable (S₁' = S₂'), from spec.dec_eq S₁' S₂',
      if h: (t₁ = t₂) ∧ (x₁ = x₂) ∧ (S₁ = S₂) ∧ (S₁' = S₂') then (
        have spec.func t₁ x₁ S₁ S₁' = spec.func t₂ x₂ S₂ S₂',
        from h.left ▸ h.right.left ▸ h.right.right.left ▸ h.right.right.right ▸ rfl,
        show decidable (spec.func t₁ x₁ S₁ S₁' = spec.func t₂ x₂ S₂ S₂'),
        from is_true this
      ) else (
        have spec.func t₁ x₁ S₁ S₁' ≠ spec.func t₂ x₂ S₂ S₂', from (
          assume : spec.func t₁ x₁ S₁ S₁' = spec.func t₂ x₂ S₂ S₂',
          show «false», from h (spec.func.inj this)
        ),
        show decidable (spec.func t₁ x₁ S₁ S₁' = spec.func t₂ x₂ S₂ S₂'),
        from is_false this
      )
    )
  ) rfl

with env.dec_eq : ∀ (σ₁ σ₂: env), decidable (σ₁ = σ₂)
| σ₁ σ₂ :=
  let z := σ₁ in
  have h: z = σ₁, from rfl,
  env.cases_on (λσ₁, (z = σ₁) → decidable (σ₁ = σ₂)) σ₁ (
    assume : z = env.empty,
    have σ₁_id: σ₁ = env.empty, from eq.trans h this,
    show decidable (env.empty = σ₂),
    from env.cases_on (λσ₂, decidable (env.empty = σ₂)) σ₂ (
      show decidable (env.empty = env.empty), from is_true rfl
    ) (
      assume σ₂' x₂ v₂,
      have env.empty ≠ env.cons σ₂' x₂ v₂, by contradiction,
      show decidable (env.empty = env.cons σ₂' x₂ v₂), from is_false this
    )
  ) (
    assume σ₁' x₁ v₁,
    assume : z = env.cons σ₁' x₁ v₁,
    have σ₁_id: σ₁ = env.cons σ₁' x₁ v₁, from eq.trans h this,
    show decidable (env.cons σ₁' x₁ v₁ = σ₂),
    from env.cases_on (λσ₂, decidable (env.cons σ₁' x₁ v₁ = σ₂)) σ₂ (
      have env.cons σ₁' x₁ v₁ ≠ env.empty, by contradiction,
      show decidable (env.cons σ₁' x₁ v₁ = env.empty), from is_false this
    ) (
      assume σ₂' x₂ v₂,
      have σ₁'.sizeof < σ₁.sizeof, from σ₁_id.symm ▸ sizeof_env_rest,
      have decidable (σ₁' = σ₂'), from env.dec_eq σ₁' σ₂',
      have v₁.sizeof < σ₁.sizeof, from σ₁_id.symm ▸ sizeof_env_value,
      have decidable (v₁ = v₂), from value.dec_eq v₁ v₂,
      if h: (σ₁' = σ₂') ∧ (x₁ = x₂) ∧ (v₁ = v₂) then (
        have env.cons σ₁' x₁ v₁ = env.cons σ₂' x₂ v₂,
        from h.left ▸ h.right.left ▸ h.right.right ▸ rfl,
        show decidable (env.cons σ₁' x₁ v₁ = env.cons σ₂' x₂ v₂),
        from is_true this
      ) else (
        have env.cons σ₁' x₁ v₁ ≠ env.cons σ₂' x₂ v₂, from (
          assume : env.cons σ₁' x₁ v₁ = env.cons σ₂' x₂ v₂,
          show «false», from h (env.cons.inj this)
        ),
        show decidable (env.cons σ₁' x₁ v₁ = env.cons σ₂' x₂ v₂),
        from is_false this
      )
    )
  ) rfl

with history.dec_eq : ∀ (H₁ H₂: history), decidable (H₁ = H₂)
| H₁ H₂ :=
  let z := H₁ in
  have h: z = H₁, from rfl,
  history.cases_on (λH₁, (z = H₁) → decidable (H₁ = H₂)) H₁ (
    assume : z = history.empty,
    have H₁_id: H₁ = history.empty, from eq.trans h this,
    show decidable (history.empty = H₂),
    from history.cases_on (λH₂, decidable (history.empty = H₂)) H₂ (
      show decidable (history.empty = history.empty), from is_true rfl
    ) (
      assume H₂' f₂ x₂ R₂ S₂ e₂ H₂'' σ₂ v₂,
      have history.empty ≠ history.call H₂' f₂ x₂ R₂ S₂ e₂ H₂'' σ₂ v₂, by contradiction,
      show decidable (history.empty = history.call H₂' f₂ x₂ R₂ S₂ e₂ H₂'' σ₂ v₂), from is_false this
    )
  ) (
    assume H₁' f₁ x₁ R₁ S₁ e₁ H₁'' σ₁ v₁,
    assume : z = history.call H₁' f₁ x₁ R₁ S₁ e₁ H₁'' σ₁ v₁,
    have H₁_id: H₁ = history.call H₁' f₁ x₁ R₁ S₁ e₁ H₁'' σ₁ v₁, from eq.trans h this,
    show decidable (history.call H₁' f₁ x₁ R₁ S₁ e₁ H₁'' σ₁ v₁ = H₂),
    from history.cases_on (λH₂, decidable (history.call H₁' f₁ x₁ R₁ S₁ e₁ H₁'' σ₁ v₁ = H₂)) H₂ (
      have history.call H₁' f₁ x₁ R₁ S₁ e₁ H₁'' σ₁ v₁ ≠ history.empty, by contradiction,
      show decidable (history.call H₁' f₁ x₁ R₁ S₁ e₁ H₁'' σ₁ v₁ = history.empty), from is_false this
    ) (
      assume H₂' f₂ x₂ R₂ S₂ e₂ H₂'' σ₂ v₂,
      have H₁'.sizeof < H₁.sizeof, from H₁_id.symm ▸ sizeof_history_rest,
      have decidable (H₁' = H₂'), from history.dec_eq H₁' H₂',
      have R₁.sizeof < H₁.sizeof, from H₁_id.symm ▸ sizeof_history_R,
      have decidable (R₁ = R₂), from spec.dec_eq R₁ R₂,
      have S₁.sizeof < H₁.sizeof, from H₁_id.symm ▸ sizeof_history_S,
      have decidable (S₁ = S₂), from spec.dec_eq S₁ S₂,
      have e₁.sizeof < H₁.sizeof, from H₁_id.symm ▸ sizeof_history_e,
      have decidable (e₁ = e₂), from exp.dec_eq e₁ e₂,
      have H₁''.sizeof < H₁.sizeof, from H₁_id.symm ▸ sizeof_history_H,
      have decidable (H₁'' = H₂''), from history.dec_eq H₁'' H₂'',
      have σ₁.sizeof < H₁.sizeof, from H₁_id.symm ▸ sizeof_history_σ,
      have decidable (σ₁ = σ₂), from env.dec_eq σ₁ σ₂,
      have v₁.sizeof < H₁.sizeof, from H₁_id.symm ▸ sizeof_history_v,
      have decidable (v₁ = v₂), from value.dec_eq v₁ v₂,
      if h: (H₁' = H₂') ∧ (f₁ = f₂) ∧ (x₁ = x₂) ∧ (R₁ = R₂) ∧ (S₁ = S₂) ∧ 
            (e₁ = e₂) ∧ (H₁'' = H₂'') ∧ (σ₁ = σ₂) ∧ (v₁ = v₂)
      then (
        have history.call H₁' f₁ x₁ R₁ S₁ e₁ H₁'' σ₁ v₁ = history.call H₂' f₂ x₂ R₂ S₂ e₂ H₂'' σ₂ v₂,
        from h.left ▸ h.right.left ▸ h.right.right.left ▸ h.right.right.right.left ▸
             h.right.right.right.right.left ▸ h.right.right.right.right.right.left ▸
             h.right.right.right.right.right.right.left ▸
             h.right.right.right.right.right.right.right.left ▸
             h.right.right.right.right.right.right.right.right ▸ rfl,
        show decidable (history.call H₁' f₁ x₁ R₁ S₁ e₁ H₁'' σ₁ v₁ = history.call H₂' f₂ x₂ R₂ S₂ e₂ H₂'' σ₂ v₂),
        from is_true this
      ) else (
        have history.call H₁' f₁ x₁ R₁ S₁ e₁ H₁'' σ₁ v₁ ≠ history.call H₂' f₂ x₂ R₂ S₂ e₂ H₂'' σ₂ v₂, from (
          assume : history.call H₁' f₁ x₁ R₁ S₁ e₁ H₁'' σ₁ v₁ = history.call H₂' f₂ x₂ R₂ S₂ e₂ H₂'' σ₂ v₂,
          show «false», from h (history.call.inj this)
        ),
        show decidable (history.call H₁' f₁ x₁ R₁ S₁ e₁ H₁'' σ₁ v₁ = history.call H₂' f₂ x₂ R₂ S₂ e₂ H₂'' σ₂ v₂),
        from is_false this
      )
    )
  ) rfl

using_well_founded
{
  rel_tac := λ _ _, `[exact wf_measure],
  dec_tac := tactic.assumption
}

instance : decidable_eq value := value.dec_eq
