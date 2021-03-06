import .definitions3 .logic

lemma exp.progress {R: spec} {P: prop} {Q: propctx} {e: exp} {σ: env}:
      (⊩ σ: P) → (FV R.to_prop ⊆ FV P) → (σ ⊨ R.to_prop.to_vc) → (R ⋀ P ⊩ e: Q) → 
      is_dvalue (R, σ, e) ∨ ∃s', (R, σ, e) ⟹ s' :=
  assume env_verified: (⊩ σ : P),
  assume fv_R: FV R.to_prop ⊆ FV P,
  assume R_valid: (σ ⊨ R.to_prop.to_vc),
  assume e_verified: (R ⋀ P ⊩ e : Q),
  have R_closed: closed_subst σ R.to_prop, from (
    assume z: var,
    assume : z ∈ FV R.to_prop,
    have z ∈ FV P, from set.mem_of_subset_of_mem fv_R this,
    show z ∈ σ.dom, from (free_iff_contains env_verified).symm ▸ this
  ),
  show is_dvalue (R, σ, e) ∨ ∃s', (R, σ, e) ⟹ s', by begin
    cases e_verified,
    case exp.dvcgen.tru x e' { from
      let s: dstack := (R, σ, lett x = true in e') in
      have s ⟹ (R, σ[x↦value.true], e'), from dstep.tru,
      have ∃s', s ⟹ s', from exists.intro (R, σ[x↦value.true], e') this,
      show is_dvalue s ∨ ∃s', s ⟹ s', from or.inr this
    },
    case exp.dvcgen.fals x e' { from
      let s: dstack := (R, σ, letf x = false in e') in
      have s ⟹ (R, σ[x↦value.false], e'), from dstep.fals,
      have ∃s', s ⟹ s', from exists.intro (R, σ[x↦value.false], e') this,
      show is_dvalue s ∨ ∃s', s ⟹ s', from or.inr this
    },
    case exp.dvcgen.num x n e' { from
      let s: dstack := (R, σ, letn x = n in e') in
      have s ⟹ (R, σ[x↦value.num n], e'), from dstep.num,
      have ∃s', s ⟹ s', from exists.intro (R, σ[x↦value.num n], e') this,
      show is_dvalue s ∨ ∃s', s ⟹ s', from or.inr this
    },
    case exp.dvcgen.func f x R' S' e₁ e₂ { from
      let s: dstack := (R, σ, letf f[x] req R' ens S' {e₁} in e₂) in
      have s ⟹ (R, σ[f↦value.func f x R' S' e₁ σ], e₂), from dstep.closure,
      have ∃s', s ⟹ s', from exists.intro (R, σ[f↦value.func f x R' S' e₁ σ], e₂) this,
      show is_dvalue s ∨ ∃s', s ⟹ s', from or.inr this
    },
    case exp.dvcgen.unop op x y e' Q' x_free_in_P _ e'_verified vc_valid { from
      let s: dstack := (R, σ, letop y = op[x] in e') in
      let ⟨v, env_has_x⟩ := (val_of_free_in_pre_env env_verified fv_R x_free_in_P) in
      have closed_subst σ (prop.pre₁ op x), from (
        assume z: var,
        assume : z ∈ FV (prop.pre₁ op x),
        have free_in_term z x, from free_in_prop.pre₁.inv this,
        have z = x, from free_in_term.var.inv this,
        show z ∈ σ, from this.symm ▸ env.contains_apply_equiv.right.mp (exists.intro v env_has_x)
      ),
      have h1: σ ⊨ (prop.pre₁ op x).to_vc, from consequent_of_pre_P env_verified R_closed R_valid this vc_valid,
      have (prop.pre₁ op x).to_vc = vc.pre₁ op x, by unfold prop.to_vc,
      have h2: ⊨ vc.subst_env σ (vc.pre₁ op x), from this ▸ h1,
      have vc.subst_env σ (vc.pre₁ op x) = vc.pre₁ op (term.subst_env σ x), from vc.subst_env.pre₁,
      have ⊨ vc.pre₁ op (term.subst_env σ x), from this ▸ h2,
      have x_from_env: term.subst_env σ x = v, from (term.subst_env.var.right v).mp env_has_x,
      have ⊨ vc.pre₁ op v, from x_from_env ▸ this,
      have option.is_some (unop.apply op v), from valid.pre₁ this,
      have (∃v', unop.apply op v = some v'), from option.is_some_iff_exists.mp this,
      let ⟨v', op_v_is_v'⟩ := this in
      have s ⟹ (R, σ[y↦v'], e'), from dstep.unop env_has_x op_v_is_v',
      have ∃s', s ⟹ s', from exists.intro (R, σ[y↦v'], e') this,
      show is_dvalue s ∨ ∃s', s ⟹ s', from or.inr this
    },
    case exp.dvcgen.binop op x y z e' Q' x_free_in_P y_free_in_P _ e'_verified vc_valid { from
      let s: dstack := (R, σ, letop2 z = op[x,y] in e') in
      let ⟨vx, env_has_x⟩ := (val_of_free_in_pre_env env_verified fv_R x_free_in_P) in
      let ⟨vy, env_has_y⟩ := (val_of_free_in_pre_env env_verified fv_R y_free_in_P) in
      have closed_subst σ (prop.pre₂ op x y), from (
        assume z: var,
        assume : z ∈ FV (prop.pre₂ op x y),
        or.elim (free_in_prop.pre₂.inv this) (
          assume : free_in_term z x,
          have z = x, from free_in_term.var.inv this,
          show z ∈ σ, from this.symm ▸ env.contains_apply_equiv.right.mp (exists.intro vx env_has_x)
        ) (
          assume : free_in_term z y,
          have z = y, from free_in_term.var.inv this,
          show z ∈ σ, from this.symm ▸ env.contains_apply_equiv.right.mp (exists.intro vy env_has_y)
        )
      ),
      have h1: σ ⊨ (prop.pre₂ op x y).to_vc, from consequent_of_pre_P env_verified R_closed R_valid this vc_valid,
      have (prop.pre₂ op x y).to_vc = vc.pre₂ op x y, by unfold prop.to_vc,
      have h2: ⊨ vc.subst_env σ (vc.pre₂ op x y), from this ▸ h1,
      have vc.subst_env σ (vc.pre₂ op x y) = vc.pre₂ op (term.subst_env σ x) (term.subst_env σ y),
      from vc.subst_env.pre₂,
      have h3: ⊨ vc.pre₂ op (term.subst_env σ x) (term.subst_env σ y), from this ▸ h2,
      have term.subst_env σ x = vx, from (term.subst_env.var.right vx).mp env_has_x,
      have h4: ⊨ vc.pre₂ op vx (term.subst_env σ y), from this ▸ h3,
      have term.subst_env σ y = vy, from (term.subst_env.var.right vy).mp env_has_y,
      have ⊨ vc.pre₂ op vx vy, from this ▸ h4,
      have option.is_some (binop.apply op vx vy), from valid.pre₂ this,
      have (∃v', binop.apply op vx vy = some v'), from option.is_some_iff_exists.mp this,
      let ⟨v', op_v_is_v'⟩ := this in
      have s ⟹ (R, σ[z↦v'], e'), from dstep.binop env_has_x env_has_y op_v_is_v',
      have ∃s', s ⟹ s', from exists.intro (R, σ[z↦v'], e') this,
      show is_dvalue s ∨ ∃s', s ⟹ s', from or.inr this
    },
    case exp.dvcgen.app y f x e' Q' f_free_in_P x_free_in_P _ e'_verified vc_valid { from
      let s: dstack := (R, σ, letapp y = f [x] in e') in
      let ⟨vf, env_f_is_vf⟩ := (val_of_free_in_pre_env env_verified fv_R f_free_in_P) in
      have env_has_f: f ∈ σ, from env.contains_apply_equiv.right.mp (exists.intro vf env_f_is_vf),
      let ⟨vx, env_x_is_vx⟩ := (val_of_free_in_pre_env env_verified fv_R x_free_in_P) in
      have env_has_x: x ∈ σ, from env.contains_apply_equiv.right.mp (exists.intro vx env_x_is_vx),
      have closed_subst σ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x), from (
        assume z: var,
        assume : z ∈ FV (↑(term.unop unop.isFunc f) ⋀ prop.pre f x),
        or.elim (free_in_prop.and.inv this) (
          assume : free_in_prop z (term.unop unop.isFunc f),
          have free_in_term z (term.unop unop.isFunc f), from free_in_prop.term.inv this,
          have free_in_term z f, from free_in_term.unop.inv this,
          have z = f, from free_in_term.var.inv this,
          show z ∈ σ, from this.symm ▸ env_has_f
        ) (
          assume : z ∈ FV (prop.pre f x),
          or.elim (free_in_prop.pre.inv this) (
            assume : free_in_term z f,
            have z = f, from free_in_term.var.inv this,
            show z ∈ σ, from this.symm ▸ env_has_f
          ) (
            assume : free_in_term z x,
            have z = x, from free_in_term.var.inv this,
            show z ∈ σ, from this.symm ▸ env_has_x
          )
        )
      ),
      have h1: σ ⊨ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).to_vc,
      from consequent_of_pre_P_call env_verified R_closed R_valid env_has_x this vc_valid,
      have (prop.and (prop.term (term.unop unop.isFunc f)) (prop.pre f x)).to_vc
         = ((prop.term (term.unop unop.isFunc f)).to_vc ⋀ (prop.pre f x).to_vc),
      by unfold prop.to_vc,
      have σ ⊨ ((prop.term (term.unop unop.isFunc f)).to_vc ⋀ (prop.pre f x).to_vc), from this ▸ h1,
      have h2: ⊨ vc.subst_env σ ((prop.term (term.unop unop.isFunc f)).to_vc ⋀ (prop.pre f x).to_vc), from this,
      have vc.subst_env σ ((prop.term (term.unop unop.isFunc f)).to_vc ⋀ (prop.pre f x).to_vc)
         = (vc.subst_env σ ((prop.term (term.unop unop.isFunc f)).to_vc) ⋀ vc.subst_env σ ((prop.pre f x).to_vc)),
      from vc.subst_env.and,
      have ⊨ (vc.subst_env σ ((prop.term (term.unop unop.isFunc f)).to_vc) ⋀
              vc.subst_env σ ((prop.pre f x).to_vc)),
      from this ▸ h2,
      have h5: σ ⊨ (prop.term (term.unop unop.isFunc f)).to_vc, from (valid.and.mpr this).left,
      have (prop.term (term.unop unop.isFunc f)).to_vc = vc.term (term.unop unop.isFunc f),
      by unfold prop.to_vc,
      have h6: σ ⊨ vc.term (term.unop unop.isFunc f), from this ▸ h5,
      have vc.subst_env σ (vc.term (term.unop unop.isFunc f)) = vc.term (term.subst_env σ (term.unop unop.isFunc f)),
      from vc.subst_env.term,
      have h7: ⊨ vc.term (term.subst_env σ (term.unop unop.isFunc f)), from this ▸ h6,
      have term.subst_env σ (term.unop unop.isFunc f) = term.unop unop.isFunc (term.subst_env σ f),
      from term.subst_env.unop,
      have h8: ⊨ vc.term (term.unop unop.isFunc (term.subst_env σ f)), from this ▸ h7,
      have term.subst_env σ f = vf, from (term.subst_env.var.right vf).mp env_f_is_vf,
      have ⊨ term.unop unop.isFunc vf, from this ▸ h8,
      have ⊨ (value.true ≡ term.unop unop.isFunc vf), from valid.eq.true.mp this,
      have unop.apply unop.isFunc vf = some value.true, from valid.unop.mpr this,
      have ∃(g gx: var) (gR gS: spec) (ge: exp) (gσ: env), vf = value.func g gx gR gS ge gσ,
      from unop.isFunc.inv this,
      let ⟨g, gx, gR, gS, ge, gσ, vf_is_g⟩ := this in
      have some_vf_is_g: some vf = ↑(value.func g gx gR gS ge gσ), from some.inj.inv vf_is_g,
      have σ f = value.func g gx gR gS ge gσ, from eq.trans env_f_is_vf some_vf_is_g,
      let s': dstack := dstack.cons (gR, gσ[g↦value.func g gx gR gS ge gσ][gx↦vx], ge) R σ y f x e' in
      have s ⟹ s', from dstep.app this env_x_is_vx,
      have ∃s', s ⟹ s', from exists.intro s' this,
      show is_dvalue s ∨ ∃s', s ⟹ s', from or.inr this
    },
    case exp.dvcgen.ite x e₂ e₁ Q₁ Q₂ x_free_in_P _ _ vc_valid { from
      let s: dstack := (R, σ, exp.ite x e₁ e₂) in
      let ⟨v, env_has_x⟩ := (val_of_free_in_pre_env env_verified fv_R x_free_in_P) in
      have closed_subst σ (prop.term (term.unop unop.isBool x)), from (
        assume z: var,
        assume : z ∈ FV (prop.term (term.unop unop.isBool x)),
        have free_in_term z (term.unop unop.isBool x), from free_in_prop.term.inv this,
        have free_in_term z x, from free_in_term.unop.inv this,
        have z = x, from free_in_term.var.inv this,
        show z ∈ σ, from this.symm ▸ env.contains_apply_equiv.right.mp (exists.intro v env_has_x)
      ),
      have h1: σ ⊨ (prop.term (term.unop unop.isBool x)).to_vc,
      from consequent_of_pre_P env_verified R_closed R_valid this vc_valid,
      have (prop.term (term.unop unop.isBool x)).to_vc = vc.term (term.unop unop.isBool x),
      by unfold prop.to_vc,
      have h2: σ ⊨ vc.term (term.unop unop.isBool x), from this ▸ h1,
      have vc.subst_env σ (vc.term (term.unop unop.isBool x)) = vc.term (term.subst_env σ (term.unop unop.isBool x)),
      from vc.subst_env.term,
      have h3: ⊨ vc.term (term.subst_env σ (term.unop unop.isBool x)), from this ▸ h2,
      have term.subst_env σ (term.unop unop.isBool x) = term.unop unop.isBool (term.subst_env σ x),
      from term.subst_env.unop,
      have h4: ⊨ vc.term (term.unop unop.isBool (term.subst_env σ x)), from this ▸ h3,
      have term.subst_env σ x = v, from (term.subst_env.var.right v).mp env_has_x,
      have ⊨ term.unop unop.isBool v, from this ▸ h4,
      have ⊨ (value.true ≡ term.unop unop.isBool v), from valid.eq.true.mp this,
      have unop.apply unop.isBool v = some value.true, from valid.unop.mpr this,
      have (v = value.true) ∨ (v = value.false), from unop.isBool.inv this,
      or.elim this (
        assume : v = value.true,
        have some v = some value.true, from some.inj.inv this,
        have σ x = value.true, from eq.trans env_has_x this,
        have s ⟹ (R, σ, e₁), from dstep.ite_true this,
        have ∃s', s ⟹ s', from exists.intro (R, σ, e₁) this,
        show is_dvalue s ∨ ∃s', s ⟹ s', from or.inr this
      ) (
        assume : v = value.false,
        have some v = some value.false, from some.inj.inv this,
        have σ x = value.false, from eq.trans env_has_x this,
        have s ⟹ (R, σ, e₂), from dstep.ite_false this,
        have ∃s', s ⟹ s', from exists.intro (R, σ, e₂) this,
        show is_dvalue s ∨ ∃s', s ⟹ s', from or.inr this
      )
    },
    case exp.dvcgen.return x x_free_in_P { from
      let s: dstack := (R, σ, exp.return x) in
      have s_is_return: s = (R, σ, exp.return x), from rfl,
      let ⟨v, env_has_x⟩ := (val_of_free_in_pre_env env_verified fv_R x_free_in_P) in
      have is_value_s: is_dvalue s
        = (∃(R': spec) (σ': env) (x': var) (v: value), s = (R', σ', exp.return x') ∧ (σ' x' = v)),
      by unfold is_dvalue,
      have (∃(R': spec) (σ': env) (x': var) (v: value), s = (R', σ', exp.return x') ∧ (σ' x' = v)),
      from exists.intro R (exists.intro σ (exists.intro x (exists.intro v ⟨s_is_return, env_has_x⟩))),
      have is_dvalue s, from is_value_s ▸ this,
      show is_dvalue s ∨ ∃s', s ⟹ s', from or.inl this
    }
  end

theorem progress {s: dstack} {Q: propctx}: (⊩ₛ s : Q) → is_dvalue s ∨ ∃s', s ⟹ s'
:=
  assume s_verified: ⊩ₛ s : Q,
  begin
    induction s_verified,
    case stack.dvcgen.top σ e R P Q env_verified fv_R R_valid e_verified { from
      show is_dvalue (R, σ, e) ∨ ∃s', (R, σ, e) ⟹ s', from exp.progress env_verified fv_R R_valid e_verified
    },
    case stack.dvcgen.cons P P' P'' s' σ σ' f g x y fx R R' S' e₁ e₂ vₓ Q Q' Q''
                          s'_verified y_not_in_σ σ_verified σ'_verified σ''_verified fv_R R_valid g_is_func
                          x_is_v e₁_verified cont Q''_dom Q''_fv pre_vc steps ih { from
      let s := dstack.cons s' R σ y g x e₁ in
      have s_cons: s = (dstack.cons s' R σ y g x e₁), from rfl,
      or.elim ih
      ( -- step return
        assume s'_is_value: is_dvalue s',
        let ⟨R₂, σ₂, z, v, ⟨s'_return, env2_has_z⟩⟩ := s'_is_value in
        have s_return_cons: s = dstack.cons (R₂, σ₂, exp.return z) R σ y g x e₁,
        from s'_return ▸ s_cons,
        have s ⟹ (R, σ[y↦v], e₁),
        from s_return_cons.symm ▸ (dstep.return env2_has_z g_is_func x_is_v),
        have ∃s', s ⟹ s',
        from exists.intro (R, σ[y↦v], e₁) this,
        show is_dvalue s ∨ ∃s', s ⟹ s', from or.inr this
      )
      ( -- step ctx
        assume s'_can_step: ∃s'', s' ⟹ s'',
        let ⟨s'', s'_steps⟩ := s'_can_step in
        have s ⟹ dstack.cons s'' R σ y g x e₁, from dstep.ctx s'_steps,
        have ∃s', s ⟹ s', from exists.intro (dstack.cons s'' R σ y g x e₁) this,
        show is_dvalue s ∨ ∃s', s ⟹ s', from or.inr this
      )
    }
  end
