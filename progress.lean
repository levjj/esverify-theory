import .syntax .notations .logic .evaluation .vcgen .bindings

@[reducible]
def is_value(s: stack): Prop :=
  ∃(R: spec) (H: history) (σ: env) (x: var) (v: value), s = (R, H, σ, exp.return x) ∧ (σ x = v)

lemma exp.progress {R: spec} {H: history} {P: prop} {Q: propctx} {e: exp} {σ: env}:
      (⊢ σ: P) → (FV R.to_prop ⊆ FV P) → (σ ⊨ R.to_prop.instantiated_n) → (R ⋀ H ⋀ P ⊢ e: Q) → 
      is_value (R, H, σ, e) ∨ ∃s', (R, H, σ, e) ⟶ s' :=
  assume env_verified: (⊢ σ : P),
  assume fv_R: FV R.to_prop ⊆ FV P,
  assume R_valid: (σ ⊨ R.to_prop.instantiated_n),
  assume e_verified: (R ⋀ H ⋀ P ⊢ e : Q),
  have R_closed: closed_subst σ R.to_prop, from (
    assume z: var,
    assume : z ∈ FV R.to_prop,
    have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
    show z ∈ σ.dom, from (free_iff_contains env_verified).symm ▸ this
  ),
  show is_value (R, H, σ, e) ∨ ∃s', (R, H, σ, e) ⟶ s', by begin
    cases e_verified,
    case exp.vcgen.tru x e' { from
      let s: stack := (R, H, σ, lett x = true in e') in
      have s ⟶ (R, H, σ[x↦value.true], e'), from step.tru,
      have ∃s', s ⟶ s', from exists.intro (R, H, σ[x↦value.true], e') this,
      show is_value s ∨ ∃s', s ⟶ s', from or.inr this
    },
    case exp.vcgen.fals x e' { from
      let s: stack := (R, H, σ, letf x = false in e') in
      have s ⟶ (R, H, σ[x↦value.false], e'), from step.fals,
      have ∃s', s ⟶ s', from exists.intro (R, H, σ[x↦value.false], e') this,
      show is_value s ∨ ∃s', s ⟶ s', from or.inr this
    },
    case exp.vcgen.num x n e' { from
      let s: stack := (R, H, σ, letn x = n in e') in
      have s ⟶ (R, H, σ[x↦value.num n], e'), from step.num,
      have ∃s', s ⟶ s', from exists.intro (R, H, σ[x↦value.num n], e') this,
      show is_value s ∨ ∃s', s ⟶ s', from or.inr this
    },
    case exp.vcgen.func f x R' S' e₁ e₂ { from
      let s: stack := (R, H, σ, letf f[x] req R' ens S' {e₁} in e₂) in
      have s ⟶ (R, H, σ[f↦value.func f x R' S' e₁ H σ], e₂), from step.closure,
      have ∃s', s ⟶ s', from exists.intro (R, H, σ[f↦value.func f x R' S' e₁ H σ], e₂) this,
      show is_value s ∨ ∃s', s ⟶ s', from or.inr this
    },
    case exp.vcgen.unop op x y e' Q' x_free_in_P _ e'_verified vc_valid { from
      let s: stack := (R, H, σ, letop y = op[x] in e') in
      let ⟨v, env_has_x⟩ := (val_of_free_in_hist_env env_verified fv_R x_free_in_P) in
      have no_instantiations (prop.pre₁ op x), from no_instantiations.pre₁,
      have σ ⊨ (prop.pre₁ op x).erased_n, from consequent_of_H_P env_verified R_closed R_valid vc_valid this,
      have h1: ⊨ vc.subst_env σ (vc.pre₁ op x), from this,
      have vc.subst_env σ (vc.pre₁ op x) = vc.pre₁ op (term.subst_env σ x), from vc.subst_env.pre₁,
      have ⊨ vc.pre₁ op (term.subst_env σ x), from this ▸ h1,
      have x_from_env: term.subst_env σ x = v, from (term.subst_env.var.right v).mp env_has_x,
      have ⊨ vc.pre₁ op v, from x_from_env ▸ this,
      have option.is_some (unop.apply op v), from valid.pre₁.mpr this,
      have (∃v', unop.apply op v = some v'), from option.is_some_iff_exists.mp this,
      let ⟨v', op_v_is_v'⟩ := this in
      have s ⟶ (R, H, σ[y↦v'], e'), from step.unop env_has_x op_v_is_v',
      have ∃s', s ⟶ s', from exists.intro (R, H, σ[y↦v'], e') this,
      show is_value s ∨ ∃s', s ⟶ s', from or.inr this
    },
    case exp.vcgen.binop op x y z e' Q' x_free_in_P y_free_in_P _ e'_verified vc_valid { from
      let s: stack := (R, H, σ, letop2 z = op[x,y] in e') in
      let ⟨vx, env_has_x⟩ := (val_of_free_in_hist_env env_verified fv_R x_free_in_P) in
      let ⟨vy, env_has_y⟩ := (val_of_free_in_hist_env env_verified fv_R y_free_in_P) in
      have no_instantiations (prop.pre₂ op x y), from no_instantiations.pre₂,
      have σ ⊨ (prop.pre₂ op x y).erased_n, from consequent_of_H_P env_verified R_closed R_valid vc_valid this,
      have h1: ⊨ vc.subst_env σ (vc.pre₂ op x y), from this,
      have vc.subst_env σ (vc.pre₂ op x y) = vc.pre₂ op (term.subst_env σ x) (term.subst_env σ y),
      from vc.subst_env.pre₂,
      have h2: ⊨ vc.pre₂ op (term.subst_env σ x) (term.subst_env σ y), from this ▸ h1,
      have term.subst_env σ x = vx, from (term.subst_env.var.right vx).mp env_has_x,
      have h3: ⊨ vc.pre₂ op vx (term.subst_env σ y), from this ▸ h2,
      have term.subst_env σ y = vy, from (term.subst_env.var.right vy).mp env_has_y,
      have ⊨ vc.pre₂ op vx vy, from this ▸ h3,
      have option.is_some (binop.apply op vx vy), from valid.pre₂.mpr this,
      have (∃v', binop.apply op vx vy = some v'), from option.is_some_iff_exists.mp this,
      let ⟨v', op_v_is_v'⟩ := this in
      have s ⟶ (R, H, σ[z↦v'], e'), from step.binop env_has_x env_has_y op_v_is_v',
      have ∃s', s ⟶ s', from exists.intro (R, H, σ[z↦v'], e') this,
      show is_value s ∨ ∃s', s ⟶ s', from or.inr this
    },
    case exp.vcgen.app y f x e' Q' f_free_in_P x_free_in_P _ e'_verified vc_valid { from
      let s: stack := (R, H, σ, letapp y = f [x] in e') in
      let ⟨vf, env_f_is_vf⟩ := (val_of_free_in_hist_env env_verified fv_R f_free_in_P) in
      have env_has_f: f ∈ σ, from env.contains_apply_equiv.right.mp (exists.intro vf env_f_is_vf),
      let ⟨vx, env_x_is_vx⟩ := (val_of_free_in_hist_env env_verified fv_R x_free_in_P) in
      have env_has_x: x ∈ σ, from env.contains_apply_equiv.right.mp (exists.intro vx env_x_is_vx),
      have h1: no_instantiations (term.unop unop.isFunc f), from no_instantiations.term,
      have h2: no_instantiations (prop.pre f x), from no_instantiations.pre,
      have no_instantiations (↑(term.unop unop.isFunc f) ⋀ prop.pre f x), from no_instantiations.and h1 h2,
      have h3: σ ⊨ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased_n,
      from consequent_of_H_P_call env_verified R_closed R_valid vc_valid env_has_f env_has_x this,
      have (prop.and (prop.term (term.unop unop.isFunc f)) (prop.pre f x)).erased_n
         = ((prop.term (term.unop unop.isFunc f)).erased_n ⋀ (prop.pre f x).erased_n), by unfold prop.erased_n,
      have σ ⊨ ((prop.term (term.unop unop.isFunc f)).erased_n ⋀ (prop.pre f x).erased_n), from this ▸ h3,
      have h4: ⊨ vc.subst_env σ ((prop.term (term.unop unop.isFunc f)).erased_n ⋀ (prop.pre f x).erased_n), from this,
      have vc.subst_env σ ((prop.term (term.unop unop.isFunc f)).erased_n ⋀ (prop.pre f x).erased_n)
         = (vc.subst_env σ ((prop.term (term.unop unop.isFunc f)).erased_n) ⋀ vc.subst_env σ ((prop.pre f x).erased_n)),
      from vc.subst_env.and,
      have ⊨ (vc.subst_env σ ((prop.term (term.unop unop.isFunc f)).erased_n) ⋀ vc.subst_env σ ((prop.pre f x).erased_n)),
      from this ▸ h4,
      have h5: σ ⊨ (prop.term (term.unop unop.isFunc f)).erased_n, from (valid.and.mpr this).left,
      have (prop.term (term.unop unop.isFunc f)).erased_n = vc.term (term.unop unop.isFunc f),
      by unfold prop.erased_n,
      have h6: σ ⊨ vc.term (term.unop unop.isFunc f), from this ▸ h5,
      have vc.subst_env σ (vc.term (term.unop unop.isFunc f)) = vc.term (term.subst_env σ (term.unop unop.isFunc f)),
      from vc.subst_env.term,
      have h7: ⊨ vc.term (term.subst_env σ (term.unop unop.isFunc f)), from this ▸ h6,
      have term.subst_env σ (term.unop unop.isFunc f) = term.unop unop.isFunc (term.subst_env σ f),
      from term.subst_env.unop,
      have h8: ⊨ vc.term (term.unop unop.isFunc (term.subst_env σ f)), from this ▸ h7,
      have term.subst_env σ f = vf, from (term.subst_env.var.right vf).mp env_f_is_vf,
      have ⊨ term.unop unop.isFunc vf, from this ▸ h8,
      have ⊨ (term.unop unop.isFunc vf ≡ value.true), from valid.eq.true.mp this,
      have unop.apply unop.isFunc vf = some value.true, from valid.unop.mpr this,
      have ∃(g gx: var) (gR gS: spec) (ge: exp) (gH: history) (gσ: env), vf = value.func g gx gR gS ge gH gσ,
      from unop.isFunc.inv this,
      let ⟨g, gx, gR, gS, ge, gH, gσ, vf_is_g⟩ := this in
      have some_vf_is_g: some vf = ↑(value.func g gx gR gS ge gH gσ), from some.inj.inv vf_is_g,
      have σ f = value.func g gx gR gS ge gH gσ, from eq.trans env_f_is_vf some_vf_is_g,
      let s': stack := (gR, gH, gσ[g↦value.func g gx gR gS ge gH gσ][gx↦vx], ge) · [R, H, σ, letapp y = f[x] in e'] in
      have s ⟶ s', from step.app this env_x_is_vx,
      have ∃s', s ⟶ s', from exists.intro s' this,
      show is_value s ∨ ∃s', s ⟶ s', from or.inr this
    },
    case exp.vcgen.ite x e₂ e₁ Q₁ Q₂ x_free_in_P _ _ vc_valid { from
      let s: stack := (R, H, σ, exp.ite x e₁ e₂) in
      let ⟨v, env_has_x⟩ := (val_of_free_in_hist_env env_verified fv_R x_free_in_P) in
      have no_instantiations (term.unop unop.isBool x), from no_instantiations.term,
      have h1: σ ⊨ (prop.term (term.unop unop.isBool x)).erased_n,
      from consequent_of_H_P env_verified R_closed R_valid vc_valid this,
      have (prop.term (term.unop unop.isBool x)).erased_n = vc.term (term.unop unop.isBool x),
      by unfold prop.erased_n,
      have h2: σ ⊨ vc.term (term.unop unop.isBool x), from this ▸ h1,
      have vc.subst_env σ (vc.term (term.unop unop.isBool x)) = vc.term (term.subst_env σ (term.unop unop.isBool x)),
      from vc.subst_env.term,
      have h3: ⊨ vc.term (term.subst_env σ (term.unop unop.isBool x)), from this ▸ h2,
      have term.subst_env σ (term.unop unop.isBool x) = term.unop unop.isBool (term.subst_env σ x),
      from term.subst_env.unop,
      have h4: ⊨ vc.term (term.unop unop.isBool (term.subst_env σ x)), from this ▸ h3,
      have term.subst_env σ x = v, from (term.subst_env.var.right v).mp env_has_x,
      have ⊨ term.unop unop.isBool v, from this ▸ h4,
      have ⊨ (term.unop unop.isBool v ≡ value.true), from valid.eq.true.mp this,
      have unop.apply unop.isBool v = some value.true, from valid.unop.mpr this,
      have (v = value.true) ∨ (v = value.false), from unop.isBool.inv this,
      or.elim this (
        assume : v = value.true,
        have some v = some value.true, from some.inj.inv this,
        have σ x = value.true, from eq.trans env_has_x this,
        have s ⟶ (R, H, σ, e₁), from step.ite_true this,
        have ∃s', s ⟶ s', from exists.intro (R, H, σ, e₁) this,
        show is_value s ∨ ∃s', s ⟶ s', from or.inr this
      ) (
        assume : v = value.false,
        have some v = some value.false, from some.inj.inv this,
        have σ x = value.false, from eq.trans env_has_x this,
        have s ⟶ (R, H, σ, e₂), from step.ite_false this,
        have ∃s', s ⟶ s', from exists.intro (R, H, σ, e₂) this,
        show is_value s ∨ ∃s', s ⟶ s', from or.inr this
      )
    },
    case exp.vcgen.return x x_free_in_P { from
      let s: stack := (R, H, σ, exp.return x) in
      have s_is_return: s = (R, H, σ, exp.return x), from rfl,
      let ⟨v, env_has_x⟩ := (val_of_free_in_hist_env env_verified fv_R x_free_in_P) in
      have is_value_s: is_value s
        = (∃(R': spec) (H': history) (σ': env) (x': var) (v: value), s = (R', H', σ', exp.return x') ∧ (σ' x' = v)),
      by unfold is_value,
      have (∃(R': spec) (H': history) (σ': env) (x': var) (v: value), s = (R', H', σ', exp.return x') ∧ (σ' x' = v)),
      from exists.intro R (exists.intro H (exists.intro σ (exists.intro x (exists.intro v ⟨s_is_return, env_has_x⟩)))),
      have is_value s, from is_value_s ▸ this,
      show is_value s ∨ ∃s', s ⟶ s', from or.inl this
    }
  end

theorem progress {s: stack} {Q: propctx}: (⊢ₛ s : Q) → is_value s ∨ ∃s', s ⟶ s'
:=
  assume s_verified: ⊢ₛ s : Q,
  begin
    induction s_verified,
    case stack.vcgen.top σ e Q R H P env_verified fv_R R_valid e_verified { from
      show is_value (R, H, σ, e) ∨ ∃s', (R, H, σ, e) ⟶ s', from exp.progress env_verified fv_R R_valid e_verified
    },
    case stack.vcgen.cons H' H P P' s' σ σ' f g x y fx R R' S' e₁ e₂ vₓ Q Q' Q''
                          s'_verified y_not_in_σ σ_verified σ'_verified fv_R R_valid g_is_func
                          x_is_v e₁_verified cont Q''_dom pre_vc steps ih { from
      let s := (s' · [R, H', σ, letapp y = g[x] in e₁]) in
      have s_cons: s = (s' · [R, H', σ, letapp y = g[x] in e₁]), from rfl,
      or.elim ih
      ( -- step return
        assume s'_is_value: is_value s',
        let ⟨R₂, H₂, σ₂, z, v, ⟨s'_return, env2_has_z⟩⟩ := s'_is_value in
        have s_return_cons: s = ((R₂, H₂, σ₂, exp.return z) · [R, H', σ, letapp y = g[x] in e₁]),
        from s'_return ▸ s_cons,
        have s ⟶ (R, H' · call f fx R' S' e₂ H σ' vₓ, σ[y↦v], e₁),
        from s_return_cons.symm ▸ (step.return env2_has_z g_is_func x_is_v),
        have ∃s', s ⟶ s',
        from exists.intro (R, H' · call f fx R' S' e₂ H σ' vₓ, σ[y↦v], e₁) this,
        show is_value s ∨ ∃s', s ⟶ s', from or.inr this
      )
      ( -- step ctx
        assume s'_can_step: ∃s'', s' ⟶ s'',
        let ⟨s'', s'_steps⟩ := s'_can_step in
        have s ⟶ (s'' · [R, H', σ, letapp y = g[x] in e₁]), from step.ctx s'_steps,
        have ∃s', s ⟶ s', from exists.intro (s'' · [R, H', σ, letapp y = g[x] in e₁]) this,
        show is_value s ∨ ∃s', s ⟶ s', from or.inr this
      )
    }
  end
