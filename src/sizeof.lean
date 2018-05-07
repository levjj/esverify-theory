import .syntax .etc

-- to use values, expressions, terms, specs, histories and environments with recursion,
-- we need to show that the recursion is decreasing, i.e. its parts are smaller than the whole

lemma sizeof_value_func_R {f x: var} {R S: spec} {e: exp} {σ: env}:
      R.sizeof < (value.func f x R S e σ).sizeof :=
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
    from zero_lt_one
  end

lemma sizeof_value_func_S {f x: var} {R S: spec} {e: exp} {σ: env}:
      S.sizeof < (value.func f x R S e σ).sizeof :=
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
    from zero_lt_one
  end

lemma sizeof_value_func_e {f x: var} {R S: spec} {e: exp} {σ: env}:
      e.sizeof < (value.func f x R S e σ).sizeof :=
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
    from zero_lt_one
  end

lemma sizeof_value_func_σ {f x: var} {R S: spec} {e: exp} {σ: env}:
      σ.sizeof < (value.func f x R S e σ).sizeof :=
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
      σ.sizeof < (env.cons σ x v).sizeof :=
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
      v.sizeof < (env.cons σ x v).sizeof :=
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

lemma sizeof_substack {s: stack} {R: spec} {σ: env} {f x y: var} {e: exp}:
      s.sizeof < (stack.cons s R σ f x y e).sizeof :=
  begin
    unfold stack.sizeof,
    change sizeof s < 1 + sizeof s + sizeof R + sizeof σ + sizeof f + sizeof x + sizeof y + sizeof e,
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

lemma sizeof_prop_not {P: prop}:
      P.sizeof < P.not.sizeof :=
  begin
    unfold prop.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    from zero_lt_one
  end

lemma sizeof_prop_and₁ {P S: prop}:
      P.sizeof < (prop.and P S).sizeof :=
  begin
    unfold prop.sizeof,
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    change 0 < sizeof S + 1,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_prop_and₂ {P S: prop}:
      S.sizeof < (prop.and P S).sizeof :=
  begin
    unfold prop.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    change 0 < 1 + sizeof P,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_prop_or₁ {P S: prop}:
      P.sizeof < (prop.or P S).sizeof :=
  begin
    unfold prop.sizeof,
    rw[add_assoc],
    rw[add_comm],
    rw[add_assoc],
    apply lt_add_of_pos_right,
    change 0 < sizeof S + 1,
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_prop_or₂ {P S: prop}:
      S.sizeof < (prop.or P S).sizeof :=
  begin
    unfold prop.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    change 0 < 1 + sizeof P,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_prop_exis {P: prop} {x: var}:
      P.sizeof < (prop.exis x P).sizeof :=
  begin
    unfold prop.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end

lemma sizeof_prop_forall {P: prop} {x: var}:
      P.sizeof < (prop.forallc x P).sizeof :=
  begin
    unfold prop.sizeof,
    rw[add_comm],
    apply lt_add_of_pos_right,
    rw[add_comm],
    apply lt_add_of_le_of_pos nonneg_of_nat,
    from zero_lt_one
  end
 