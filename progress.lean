import .syntax .notations .logic .evaluation .vcgen .bindings

@[reducible]
def is_value(s: stack): Prop :=
  ∃(R: spec) (H: history) (σ: env) (x: var) (v: value), s = (R, H, σ, exp.return x) ∧ (σ x = v)

lemma val_of_free_in_env {P: prop} {σ: env} {x: var}: (⊢ σ : P) → x ∈ FV P → ∃v, σ x = some v :=
  assume env_verified: ⊢ σ: P,
  assume x_free_in_P: x ∈ FV P,
  have x ∈ σ, from contains_of_free env_verified x_free_in_P,
  show ∃v, σ x = some v, from env.contains_apply_equiv.right.mpr this

lemma val_of_free_in_hist_env {R: spec} {H: history} {σ: env} {P: prop} {x: var}:
                              (⊢ σ : P) → FV R.to_prop ⊆ FV P → x ∈ FV (R.to_prop ⋀ ↑H ⋀ P) → ∃v, σ x = some v :=
  assume σ_verified: ⊢ σ : P,
  assume fv_R: FV R.to_prop ⊆ FV P,
  assume x_free_in_R_H_P: x ∈ FV (R.to_prop ⋀ ↑H ⋀ P),
  have FV (R.to_prop ⋀ ↑H ⋀ P) = FV ((R.to_prop ⋀ ↑H) ⋀ P), from free_in_prop.and_comm,
  have x ∈ FV ((R.to_prop ⋀ ↑H) ⋀ P), from this ▸ x_free_in_R_H_P,
  have free_in_prop x (R.to_prop ⋀ ↑H) ∨ free_in_prop x P, from free_in_prop.and.inv this,
  have x ∈ FV P, from or.elim this.symm id (
    assume : free_in_prop x (R.to_prop ⋀ ↑H),
    or.elim (free_in_prop.and.inv this) (
      assume : free_in_prop x R.to_prop,
      show x ∈ FV P, from set.mem_of_mem_of_subset this fv_R
    ) (
      assume : free_in_prop x H,
      show free_in_prop x P, from absurd this (call_history_closed H x)
    )
  ),
  show ∃v, σ x = some v, from val_of_free_in_env σ_verified this

lemma simple_equality_valid {σ: env} {x: var} {v: value}:
  x ∉ σ → (σ[x↦v]) ⊨ (prop.term (x ≡ v)).erased :=
  assume x_not_free_in_σ: x ∉ σ,
  have σ.apply x = none, from env.contains_apply_equiv.left.mpr x_not_free_in_σ,
  have h1: term.subst_env σ x = x, from term.subst_env.var.left.mp this,
  have (term.subst_env (σ[x↦v]) x = term.subst x v (term.subst_env σ x)),
  by unfold term.subst_env,
  have h2: term.subst_env (σ[x↦v]) x = term.subst x v x,
  from @eq.subst term (λa, term.subst_env (σ[x↦v]) x = term.subst x v a) (term.subst_env σ x) x h1 this,
  have term.subst x v (term.var x) = (if x = x then v else x), by unfold term.subst,
  have term.subst x v (term.var x) = v, by simp[this],
  have h3: term.subst_env (σ[x↦v]) x = v, from eq.trans h2 this,
  have h4: term.subst_env (σ[x↦v]) v = v, from term.subst_env.value,
  have term.subst_env (σ[x↦v]) (x ≡ v) = (term.subst_env (σ[x↦v]) x ≡ term.subst_env (σ[x↦v]) v),
  from term.subst_env.binop,
  have term.subst_env (σ[x↦v]) (x ≡ v) = (v ≡ term.subst_env (σ[x↦v]) v),
  from @eq.subst term (λa, term.subst_env (σ[x↦v]) (x ≡ v) = (a ≡ term.subst_env (σ[x↦v]) v))
                      (term.subst_env (σ[x↦v]) x) v h3 this,
  have h5: term.subst_env (σ[x↦v]) (x ≡ v) = (v ≡ v),
  from @eq.subst term (λa, term.subst_env (σ[x↦v]) (x ≡ v) = (v ≡ a))
                      (term.subst_env (σ[x↦v]) v) v h4 this,
  have h6: vc.term (term.subst_env (σ[x↦v]) (x ≡ v)) = vc.term (v ≡ v), by simp[h5],
  have vc.subst_env (σ[x↦v]) (x ≡ v) = vc.term (term.subst_env (σ[x↦v]) (x ≡ v)), from vc.subst_env.term,
  have h7: vc.subst_env (σ[x↦v]) (vc.term (x ≡ v)) = vc.term (v ≡ v), from eq.trans this h6,
  have prop.erased (prop.term (x ≡ v)) = vc.term (x ≡ v), by unfold prop.erased,
  have h8: vc.subst_env (σ[x↦v]) (prop.term (x ≡ v)).erased = vc.term (v ≡ v), from this.symm ▸ h7,
  have ⊨ vc.term (v ≡ v), from valid.refl,
  show (σ[x↦v]) ⊨ prop.erased (x ≡ v), from h8.symm ▸ this

lemma simple_equality_env_valid {P: prop} {σ: env} {x: var} {v: value}:
                                   (⊢ σ: P) → x ∉ σ → (σ ⊨ P.instantiated) → ((σ[x↦v]) ⊨ P.instantiated)
                                                             ∧ ((σ[x↦v]) ⊨ (prop.term (x ≡ v)).instantiated) :=
  assume σ_verified: ⊢ σ: P,
  assume x_not_free_in_σ: x ∉ σ,
  assume ih: σ ⊨ P.instantiated,
  have σ.apply x = none, from env.contains_apply_equiv.left.mpr x_not_free_in_σ,
  have h1: ⊨ vc.subst_env σ P.instantiated, from ih,
  have x_not_in_P: x ∉ FV (vc.subst_env σ P.instantiated), from (
    assume : x ∈ FV (vc.subst_env σ P.instantiated),
    have x ∈ FV P.instantiated, from free_in_vc.subst_env this,
    have x ∈ FV P.erased, from free_in_erased_of_free_in_instantiated this,
    have x ∈ FV P, from free_of_erased_free (or.inl this),
    have ∃v, σ x = some v, from val_of_free_in_env σ_verified this,
    have x ∈ σ, from env.contains_apply_equiv.right.mp this,
    show «false», from x_not_free_in_σ this
  ),
  have vc.subst x v (vc.subst_env σ P.instantiated) = vc.subst_env σ P.instantiated,
  from unchanged_of_subst_nonfree_vc x_not_in_P,
  have h2: ⊨ vc.subst x v (vc.subst_env σ P.instantiated),
  from @eq.subst vc (λa, ⊨ a) (vc.subst_env σ P.instantiated)
          (vc.subst x v (vc.subst_env σ P.instantiated)) this.symm h1,
  have vc.subst x v (vc.subst_env σ P.instantiated)
      = vc.subst_env (σ[x↦v]) P.instantiated, by unfold vc.subst_env, 
  have h3: ⊨ vc.subst_env (σ[x↦v]) P.instantiated, from this ▸ h2,
  have (σ[x↦v]) ⊨ (prop.term (x ≡ v)).erased,
  from simple_equality_valid x_not_free_in_σ,
  have (σ[x↦v]) ⊨ (prop.term (x ≡ v)).instantiated, from valid_env.instantiated_of_erased this,
  ⟨h3, this⟩

lemma simple_equality_env_inst_valid {P: prop} {σ: env} {x: var} {v: value}:
                                   (⊢ σ: P) → x ∉ σ → (σ ⊨ P.instantiated) → (σ[x↦v]) ⊨ (P ⋀ x ≡ v).instantiated :=
  assume σ_verified: ⊢ σ: P,
  assume x_not_free_in_σ: x ∉ σ,
  assume ih: σ ⊨ P.instantiated,
  have ((σ[x↦v]) ⊨ P.instantiated) ∧ ((σ[x↦v]) ⊨ (prop.term (x ≡ v)).instantiated),
  from simple_equality_env_valid σ_verified x_not_free_in_σ ih,
  have (σ[x↦v]) ⊨ (P.instantiated ⋀ (prop.term (x ≡ v)).instantiated),
  from valid_env.and this.left this.right,
  show (σ[x↦v]) ⊨ prop.instantiated (P ⋀ (x ≡ v)), from valid_env.instantiated_and this

lemma env_translation_erased_valid {P: prop} {σ: env}: (⊢ σ: P) → σ ⊨ P.instantiated :=
  assume env_verified: (⊢ σ : P),
  begin
    induction env_verified,
    case env.vcgen.empty {
      show env.empty ⊨ prop.instantiated (value.true), from (
        have h: prop.erased (prop.term ↑value.true) = vc.term ↑value.true, by unfold prop.erased,
        have env.empty ⊨ value.true, from valid.tru,
        have env.empty ⊨ prop.erased (value.true), from h ▸ this,
        show env.empty ⊨ prop.instantiated (value.true), from valid_env.instantiated_of_erased this
      )
    },
    case env.vcgen.tru σ' x' Q x_not_free_in_σ' σ'_verified ih {
      show (σ'[x'↦value.true]) ⊨ prop.instantiated (Q ⋀ (x' ≡ value.true)),
      from simple_equality_env_inst_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.vcgen.fls σ' x' Q x_not_free_in_σ' σ'_verified ih {
      show (σ'[x'↦value.false]) ⊨ prop.instantiated (Q ⋀ (x' ≡ value.false)),
      from simple_equality_env_inst_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.vcgen.num n σ' x' Q x_not_free_in_σ' σ'_verified ih {
      show (σ'[x'↦value.num n]) ⊨ prop.instantiated (Q ⋀ (x' ≡ value.num n)),
      from simple_equality_env_inst_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.vcgen.func σ₁ σ₂ f g gx R S e H Q₁ Q₂ Q₃
      f_not_free_in_σ₁ g_not_free_in_σ₂ gx_not_free_in_σ₂ g_neq_gx σ₁_verified σ₂_verified gx_free_in_R R_fv S_fv func_verified
      S_valid ih₁ ih₂ { from (
      let vf := value.func g gx R S e H σ₂ in
      have h1: ((σ₁[f↦vf]) ⊨ Q₁.instantiated) ∧ ((σ₁[f↦vf]) ⊨ (prop.term (f ≡ vf)).instantiated),
      from simple_equality_env_valid σ₁_verified f_not_free_in_σ₁ ih₁,

      have g_subst: term.subst_env (σ₂[g↦vf]) g = vf, from (
        have h1: term.subst g vf g = vf, from term.subst.var.same,
        have σ₂ g = none, from env.contains_apply_equiv.left.mpr g_not_free_in_σ₂,
        have term.subst_env σ₂ g = g, from term.subst_env.var.left.mp this,
        have h2: term.subst g vf (term.subst_env σ₂ g) = vf, from this.symm ▸ h1,
        have term.subst_env (σ₂[g↦vf]) g = term.subst g vf (term.subst_env σ₂ g), by unfold term.subst_env,
        show term.subst_env (σ₂[g↦vf]) g = vf, from eq.trans this h2
      ),

      have h2: ⊨ prop.instantiated (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from (
        have unop.apply unop.isFunc vf = value.true, by unfold unop.apply,
        have ⊨ (term.unop unop.isFunc vf ≡ value.true), from valid.eq.unop.mp this,
        have ⊨ term.unop unop.isFunc vf, from valid.eq.true.mpr this,
        have h3: ⊨ term.unop unop.isFunc (term.subst_env (σ₂[g↦vf]) g), from g_subst.symm ▸ this,
        have term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g) = term.unop unop.isFunc (term.subst_env (σ₂[g↦vf]) g),
        from term.subst_env.unop,
        have h4: ⊨ vc.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from this.symm ▸ h3,
        have prop.erased (prop.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)))
           = vc.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)),
        by unfold prop.erased,
        have h5: ⊨ prop.erased (prop.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g))), from this.symm ▸ h4,
        have prop.subst_env (σ₂[g↦vf]) (prop.term (term.unop unop.isFunc g))
           = prop.term (term.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from prop.subst_env.term,
        have ⊨ prop.erased (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)), from this.symm ▸ h5,
        show ⊨ prop.instantiated (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)),
        from valid.instantiated_of_erased this
      ),

      let forallp := prop.implies R.to_prop (prop.pre g gx)
                  ⋀ prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop) in
      let pfunc: prop := prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S)) in

      have h4: ∀v, ⊨ vc.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp).instantiated, from (
        assume v: value,

        have h5: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))).instantiated, from (
          have h6: ⊨ vc.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).instantiated_n
                                (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).instantiated, from valid.implies.mp (
            assume h8: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).instantiated_n,
            have vc.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop.instantiated_n
                = (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop).instantiated_n, from instantiated_n_distrib_subst_env,
            have ⊨ vc.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop.instantiated_n, from this.symm ▸ h8,
            have h9: ⊨ vc.pre vf v, from valid.pre.mp this,
            have term.subst gx v gx = v, from term.subst.var.same,
            have h10: ⊨ vc.pre vf (term.subst gx v gx), from this.symm ▸ h9,
            have ¬(gx = g ∨ gx ∈ σ₂), from not_or_distrib.mpr ⟨g_neq_gx.symm, gx_not_free_in_σ₂⟩,
            have gx ∉ (σ₂[g↦vf]), from (mt env.contains.inv) this,
            have (σ₂[g↦vf]) gx = none, from env.contains_apply_equiv.left.mpr this,
            have term.subst_env (σ₂[g↦vf]) gx = gx, from term.subst_env.var.left.mp this,
            have h11: ⊨ vc.pre vf (term.subst gx v (term.subst_env (σ₂[g↦vf]) gx)),
            from this.symm ▸ h10,
            have term.subst_env (σ₂[g↦vf][gx↦v]) gx = term.subst gx v (term.subst_env (σ₂[g↦vf]) gx),
            by unfold term.subst_env,
            have h12: ⊨ vc.pre vf (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from this.symm ▸ h11,
            have term.subst gx v (term.value vf) = vf, by unfold term.subst,
            have ⊨ vc.pre (term.subst gx v vf) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from this.symm ▸ h12,
            have h13: ⊨ vc.pre (term.subst gx v (term.subst_env (σ₂[g↦vf]) g)) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from g_subst.symm ▸ this,
            have term.subst_env (σ₂[g↦vf][gx↦v]) g = term.subst gx v (term.subst_env (σ₂[g↦vf]) g),
            by unfold term.subst_env,
            have h14: ⊨ vc.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from this.symm ▸ h13,
            have prop.erased (prop.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx))
               = (vc.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx)),
            by unfold prop.erased,
            have h15: ⊨ (prop.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx)).erased,
            from this.symm ▸ h14,
            have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)
               = prop.pre (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from prop.subst_env.pre,
            have ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).erased, from this.symm ▸ h15,
            show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)).instantiated,
            from valid.instantiated_of_erased this
          ),
          have h8: ⊨ (prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop)
                                   (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx))).instantiated,
          from valid.instantiated_implies h6,
          have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))
             = prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) R.to_prop)
                            (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.pre g gx)),
          from prop.subst_env.implies,
          show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))).instantiated,
          from this.symm ▸ h8
        ),

        have h6: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                     (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated, from (
          have h7: ⊨ vc.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)).instantiated_n
                                (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).instantiated,
          from valid.implies.mp (
            assume h8: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)).instantiated_n,
            have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx)
               = prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from prop.subst_env.post,
            have ⊨ (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx))
                          .instantiated_n,
            from this ▸ h8,
            have h9: ⊨ (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx))
                          .erased_n, from valid.erased_n_of_instantiated_n this,
            have (prop.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx)).erased_n
                = vc.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            by unfold prop.erased_n,
            have h10: ⊨ vc.post (term.subst_env (σ₂[g↦vf][gx↦v]) g) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from this ▸ h9,
            have term.subst_env (σ₂[g↦vf][gx↦v]) g = term.subst gx v (term.subst_env (σ₂[g↦vf]) g),
            by unfold term.subst_env,
            have ⊨ vc.post (term.subst gx v (term.subst_env (σ₂[g↦vf]) g)) (term.subst_env (σ₂[g↦vf][gx↦v]) gx),
            from this ▸ h10,
            have h11: ⊨ vc.post (term.subst gx v vf) (term.subst_env (σ₂[g↦vf][gx↦v]) gx), from g_subst ▸ this,
            have term.subst gx v (term.value vf) = vf, by unfold term.subst,
            have h12: ⊨ vc.post vf (term.subst_env (σ₂[g↦vf][gx↦v]) gx), from this ▸ h11,
            have term.subst_env (σ₂[g↦vf][gx↦v]) gx = term.subst gx v (term.subst_env (σ₂[g↦vf]) gx),
            by unfold term.subst_env,
            have h13: ⊨ vc.post vf (term.subst gx v (term.subst_env (σ₂[g↦vf]) gx)), from this ▸ h12,
            have ¬(gx = g ∨ gx ∈ σ₂), from not_or_distrib.mpr ⟨g_neq_gx.symm, gx_not_free_in_σ₂⟩,
            have gx ∉ (σ₂[g↦vf]), from (mt env.contains.inv) this,
            have (σ₂[g↦vf]) gx = none, from env.contains_apply_equiv.left.mpr this,
            have term.subst_env (σ₂[g↦vf]) gx = gx, from term.subst_env.var.left.mp this,
            have h14: ⊨ vc.post vf (term.subst gx v gx), from this ▸ h13,
            have term.subst gx v gx = v, from term.subst.var.same,
            have ⊨ vc.post vf v, from this ▸ h14,
            have h15: (σ₂[g↦vf][gx↦v] ⊨ (Q₃ (term.app g gx) ⋀ S.to_prop).instantiated),
            from valid.post σ₂_verified func_verified this,
            have vc.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop).instantiated
              = (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).instantiated,
            from instantiated_distrib_subst_env,
            show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)).instantiated,
            from this ▸ h15
          ),
          have h8: ⊨ (prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx))
                                   (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated,
          from valid.instantiated_implies h7,
          have prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop))
             = prop.implies (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.post g gx))
                            (prop.subst_env (σ₂[g↦vf][gx↦v]) (Q₃ (term.app g gx) ⋀ S.to_prop)),
          from prop.subst_env.implies,
          show ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                      (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated,
          from this.symm ▸ h8
        ),

        have ⊨ ((prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx))).instantiated ⋀
                (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                                (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated),
        from valid.and.mp ⟨h5, h6⟩,
        have h7: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx)) ⋀
                    prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx)
                                                                   (Q₃ (term.app g gx) ⋀ S.to_prop))).instantiated,
        from valid.instantiated_and this,
        have prop.subst_env (σ₂[g↦vf][gx↦v]) forallp
           = (prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies R.to_prop (prop.pre g gx)) ⋀
             prop.subst_env (σ₂[g↦vf][gx↦v]) (prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop))),
        from prop.subst_env.and,
        have h8: ⊨ (prop.subst_env (σ₂[g↦vf][gx↦v]) forallp).instantiated, from this.symm ▸ h7,
        have prop.subst_env (σ₂[g↦vf][gx↦v]) forallp = prop.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp),
        by unfold prop.subst_env,
        have h9: ⊨ (prop.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp)).instantiated, from this ▸ h8,
        have vc.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp).instantiated
           = (prop.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp)).instantiated, from instantiated_distrib_subst,
        show ⊨ vc.subst gx v (prop.subst_env (σ₂[g↦vf]) forallp).instantiated, from this.symm ▸ h9
      ),

      have h5: ⊨ prop.instantiated (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)), from (
        have h6: ⊨ vc.univ gx (prop.subst_env (σ₂[g↦vf]) forallp).instantiated, from valid.univ.mp h4,
        have prop.instantiated (prop.forallc gx (term.subst_env (σ₂[g↦vf]) g) (prop.subst_env (σ₂[g↦vf]) forallp))
           = vc.univ gx (prop.subst_env (σ₂[g↦vf]) forallp).instantiated, from instantiated.forallc,
        have h7: ⊨ prop.instantiated (prop.forallc gx (term.subst_env (σ₂[g↦vf]) g) (prop.subst_env (σ₂[g↦vf]) forallp)), from this.symm ▸ h6,
        have ¬(gx = g ∨ gx ∈ σ₂), from not_or_distrib.mpr ⟨g_neq_gx.symm, gx_not_free_in_σ₂⟩,
        have gx ∉ (σ₂[g↦vf]), from (mt env.contains.inv) this,
        have (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)
            = prop.forallc gx (term.subst_env (σ₂[g↦vf]) g) (prop.subst_env (σ₂[g↦vf]) forallp)),
        from prop.subst_env.forallc this,
        show ⊨ prop.instantiated (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)), from this.symm ▸ h7
      ),

      have ⊨ (prop.instantiated (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g)) ⋀
                  prop.instantiated (prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp))),
      from valid.and.mp ⟨h2, h5⟩,
      have h7: ⊨ prop.instantiated (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g) ⋀
                                    prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)),
      from valid.instantiated_and this,
      have prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp)
         = (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g) ⋀ prop.subst_env (σ₂[g↦vf]) (prop.forallc gx g forallp)),
      from prop.subst_env.and,
      have h8: ⊨ prop.instantiated (prop.subst_env (σ₂[g↦vf]) (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp)),
      from this.symm ▸ h7,
      have prop.func g gx R.to_prop (Q₃ (term.app g gx) ⋀ S.to_prop)
         = (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp),
      by unfold prop.func,
      have ⊨ prop.instantiated (prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
      from this.symm ▸ h8,
      have h9: ⊨ prop.instantiated pfunc, from this,

      have h10: (∀x, x ∉ FV pfunc), from (
        have ⊢ (σ₂[g↦vf]) : Q₂
          ⋀ (g ≡ (vf))
          ⋀ prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S)),
        from env.vcgen.func g_not_free_in_σ₂ g_not_free_in_σ₂ gx_not_free_in_σ₂ g_neq_gx
             σ₂_verified σ₂_verified gx_free_in_R R_fv S_fv func_verified S_valid,
        prop_func_closed func_verified this
      ),

      have h11: (∀x, x ∉ FV pfunc.instantiated), from (
        assume x: var,
        assume : x ∈ FV pfunc.instantiated,
        have x ∈ FV pfunc.erased, from free_in_erased_of_free_in_instantiated this,
        have x ∈ FV pfunc.erased ∨ x ∈ FV pfunc.erased_n, from or.inl this,
        have x ∈ FV pfunc, from free_of_erased_free this,
        show «false», from (h10 x) this
      ),

      have vc.subst_env (σ₁[f↦vf]) pfunc.instantiated = pfunc.instantiated,
      from unchanged_of_subst_env_nonfree_vc h11 (σ₁[f↦vf]),
      have (σ₁[f↦vf]) ⊨ pfunc.instantiated, from this.symm ▸ h9,

      have (σ₁[f↦vf]) ⊨ ((prop.term (f ≡ vf)).instantiated ⋀ prop.instantiated pfunc), from valid_env.and h1.right this,
      have (σ₁[f↦vf]) ⊨ ((prop.term (f ≡ vf)) ⋀ pfunc).instantiated, from valid_env.instantiated_and this,
      have (σ₁[f↦vf]) ⊨ Q₁.instantiated ⋀ ((prop.term (f ≡ vf)) ⋀ pfunc).instantiated, from valid_env.and h1.left this,
      show (σ₁[f↦vf]) ⊨ (Q₁ ⋀ (f ≡ vf) ⋀ pfunc).instantiated,
      from valid_env.instantiated_and this
    )}
  end

lemma env_translation_valid {R: spec} {H: history} {P: prop} {σ: env}:
  (⊢ σ: P) → (σ ⊨ R.to_prop.instantiated) → σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_n :=
  assume env_verified: (⊢ σ : P),
  assume R_valid: (σ ⊨ R.to_prop.instantiated),
  have h1: σ ⊨ prop.instantiated ↑H, from history_valid σ,
  have h2: σ ⊨ P.instantiated, from env_translation_erased_valid env_verified,
  have σ ⊨ (prop.instantiated ↑H ⋀ P.instantiated), from valid_env.and h1 h2,
  have σ ⊨ (↑H ⋀ P).instantiated, from valid_env.instantiated_and this,
  have σ ⊨ R.to_prop.instantiated ⋀ (↑H ⋀ P).instantiated, from valid_env.and R_valid this,
  have σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated, from valid_env.instantiated_and this,
  show σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_n, from valid_env.instantiated_n_of_instantiated this

lemma consequent_of_H_P {R: spec} {H: history} {σ: env} {P Q: prop}:
  (⊢ σ: P) → (σ ⊨ R.to_prop.instantiated) → ⟪prop.implies (R ⋀ ↑H ⋀ P) Q⟫ → no_instantiations Q → σ ⊨ Q.erased :=
  assume env_verified: (⊢ σ : P),
  assume R_valid: (σ ⊨ R.to_prop.instantiated),
  assume impl_vc: ⟪prop.implies (R ⋀ ↑H ⋀ P) Q⟫,
  assume : no_instantiations Q,
  have h1: (prop.implies (R ⋀ ↑H ⋀ P) Q).instantiated = vc.or (↑R ⋀ ↑H ⋀ P).not.instantiated Q.erased,
  from or_dist_of_no_instantiations this,
  have h2: (↑R ⋀ ↑H ⋀ P).not.instantiated = (↑R ⋀ ↑H ⋀ P).instantiated_n.not, from not_dist_instantiated,
  have σ ⊨ (prop.implies (↑R ⋀ ↑H ⋀ P) Q).instantiated, from impl_vc σ,
  have σ ⊨ vc.or (↑R ⋀ ↑H ⋀ P).instantiated_n.not Q.erased, from h2 ▸ h1 ▸ this,
  have h4: σ ⊨ vc.implies (↑R ⋀ ↑H ⋀ P).instantiated_n Q.erased, from this,
  have σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated_n, from env_translation_valid env_verified R_valid,
  show σ ⊨ Q.erased, from valid_env.mp h4 this

lemma env_translation_call_valid {R: spec} {H: history} {P: prop} {σ: env} {f x: var}:
  (⊢ σ: P) → (σ ⊨ R.to_prop.instantiated) → σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n :=
  assume env_verified: (⊢ σ : P),
  assume R_valid: (σ ⊨ R.to_prop.instantiated),
  have h1: σ ⊨ prop.instantiated ↑H, from history_valid σ,
  have h2: σ ⊨ P.instantiated, from env_translation_erased_valid env_verified,
  have σ ⊨ (prop.instantiated ↑H ⋀ P.instantiated), from valid_env.and h1 h2,
  have σ ⊨ (↑H ⋀ P).instantiated, from valid_env.instantiated_and this,
  have σ ⊨ R.to_prop.instantiated ⋀ (↑H ⋀ P).instantiated, from valid_env.and R_valid this,
  have h3: σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated, from valid_env.instantiated_and this,
  have h4: ⊨ value.true, from valid.tru,
  have term.subst_env σ value.true = value.true, from term.subst_env.value,
  have h5: ⊨ term.subst_env σ value.true, from this.symm ▸ h4,
  have vc.subst_env σ value.true = vc.term (term.subst_env σ value.true), from vc.subst_env.term,
  have h6: σ ⊨ value.true, from this.symm ▸ h5,
  have (prop.call f x).erased = vc.term value.true, by unfold prop.erased,
  have σ ⊨ (prop.call f x).erased, from this.symm ▸ h6,
  have σ ⊨ (prop.call f x).instantiated, from valid_env.instantiated_of_erased this,
  have σ ⊨ (↑R ⋀ ↑H ⋀ P).instantiated ⋀ (prop.call f x).instantiated, from valid_env.and h3 this,
  have σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated, from valid_env.instantiated_and this,
  show σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n, from valid_env.instantiated_n_of_instantiated this

lemma consequent_of_H_P_call {R: spec} {H: history} {σ: env} {P Q: prop} {f x: var}:
  (⊢ σ: P) → (σ ⊨ R.to_prop.instantiated) → ⟪prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q⟫ → no_instantiations Q → σ ⊨ Q.erased :=
  assume env_verified: (⊢ σ : P),
  assume R_valid: (σ ⊨ R.to_prop.instantiated),
  assume impl_vc: ⟪prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q⟫,
  assume : no_instantiations Q,
  have h1: (prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q).instantiated
         = vc.or ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).not.instantiated Q.erased,
  from or_dist_of_no_instantiations this,
  have h2: ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).not.instantiated = ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n.not,
  from not_dist_instantiated,
  have σ ⊨ (prop.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x) Q).instantiated, from impl_vc σ,
  have σ ⊨ vc.or ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n.not Q.erased, from h2 ▸ h1 ▸ this,
  have h4: σ ⊨ vc.implies ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n Q.erased, from this,
  have σ ⊨ ((↑R ⋀ ↑H ⋀ P) ⋀ prop.call f x).instantiated_n, from env_translation_call_valid env_verified R_valid,
  show σ ⊨ Q.erased, from valid_env.mp h4 this

lemma exp.progress {R: spec} {H: history} {P: prop} {Q: propctx} {e: exp} {σ: env}:
      (⊢ σ: P) → (FV R.to_prop ⊆ FV P) → (σ ⊨ R.to_prop.instantiated) → (R ⋀ H ⋀ P ⊢ e: Q) → 
      is_value (R, H, σ, e) ∨ ∃s', (R, H, σ, e) ⟶ s' :=
  assume env_verified: (⊢ σ : P),
  assume fv_R: FV R.to_prop ⊆ FV P,
  assume R_valid: (σ ⊨ R.to_prop.instantiated),
  assume e_verified: (R ⋀ H ⋀ P ⊢ e : Q),
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
      have σ ⊨ (prop.pre₁ op x).erased, from consequent_of_H_P env_verified R_valid vc_valid this,
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
      have σ ⊨ (prop.pre₂ op x y).erased, from consequent_of_H_P env_verified R_valid vc_valid this,
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
      let ⟨vf, env_has_f⟩ := (val_of_free_in_hist_env env_verified fv_R f_free_in_P) in
      let ⟨vx, env_has_x⟩ := (val_of_free_in_hist_env env_verified fv_R x_free_in_P) in
      have h1: no_instantiations (term.unop unop.isFunc f), from no_instantiations.term,
      have h2: no_instantiations (prop.pre f x), from no_instantiations.pre,
      have no_instantiations (↑(term.unop unop.isFunc f) ⋀ prop.pre f x), from no_instantiations.and h1 h2,
      have h3: σ ⊨ (↑(term.unop unop.isFunc f) ⋀ prop.pre f x).erased,
      from consequent_of_H_P_call env_verified R_valid vc_valid this,
      have (prop.and (prop.term (term.unop unop.isFunc f)) (prop.pre f x)).erased
         = ((prop.term (term.unop unop.isFunc f)).erased ⋀ (prop.pre f x).erased), by unfold prop.erased,
      have σ ⊨ ((prop.term (term.unop unop.isFunc f)).erased ⋀ (prop.pre f x).erased), from this ▸ h3,
      have h4: ⊨ vc.subst_env σ ((prop.term (term.unop unop.isFunc f)).erased ⋀ (prop.pre f x).erased), from this,
      have vc.subst_env σ ((prop.term (term.unop unop.isFunc f)).erased ⋀ (prop.pre f x).erased)
         = (vc.subst_env σ ((prop.term (term.unop unop.isFunc f)).erased) ⋀ vc.subst_env σ ((prop.pre f x).erased)),
      from vc.subst_env.and,
      have ⊨ (vc.subst_env σ ((prop.term (term.unop unop.isFunc f)).erased) ⋀ vc.subst_env σ ((prop.pre f x).erased)),
      from this ▸ h4,
      have h5: σ ⊨ (prop.term (term.unop unop.isFunc f)).erased, from (valid.and.mpr this).left,
      have (prop.term (term.unop unop.isFunc f)).erased = vc.term (term.unop unop.isFunc f),
      by unfold prop.erased,
      have h6: σ ⊨ vc.term (term.unop unop.isFunc f), from this ▸ h5,
      have vc.subst_env σ (vc.term (term.unop unop.isFunc f)) = vc.term (term.subst_env σ (term.unop unop.isFunc f)),
      from vc.subst_env.term,
      have h7: ⊨ vc.term (term.subst_env σ (term.unop unop.isFunc f)), from this ▸ h6,
      have term.subst_env σ (term.unop unop.isFunc f) = term.unop unop.isFunc (term.subst_env σ f),
      from term.subst_env.unop,
      have h8: ⊨ vc.term (term.unop unop.isFunc (term.subst_env σ f)), from this ▸ h7,
      have term.subst_env σ f = vf, from (term.subst_env.var.right vf).mp env_has_f,
      have ⊨ term.unop unop.isFunc vf, from this ▸ h8,
      have ⊨ (term.unop unop.isFunc vf ≡ value.true), from valid.eq.true.mp this,
      have unop.apply unop.isFunc vf = some value.true, from valid.eq.unop.mpr this,
      have ∃(g gx: var) (gR gS: spec) (ge: exp) (gH: history) (gσ: env), vf = value.func g gx gR gS ge gH gσ,
      from unop.isFunc.inv this,
      let ⟨g, gx, gR, gS, ge, gH, gσ, vf_is_g⟩ := this in
      have some_vf_is_g: some vf = ↑(value.func g gx gR gS ge gH gσ), from some.inj.inv vf_is_g,
      have σ f = value.func g gx gR gS ge gH gσ, from eq.trans env_has_f some_vf_is_g,
      let s': stack := (gR, gH, gσ[g↦value.func g gx gR gS ge gH gσ][gx↦vx], ge) · [R, H, σ, letapp y = f[x] in e'] in
      have s ⟶ s', from step.app this env_has_x,
      have ∃s', s ⟶ s', from exists.intro s' this,
      show is_value s ∨ ∃s', s ⟶ s', from or.inr this
    },
    case exp.vcgen.ite x e₂ e₁ Q₁ Q₂ x_free_in_P _ _ vc_valid { from
      let s: stack := (R, H, σ, exp.ite x e₁ e₂) in
      let ⟨v, env_has_x⟩ := (val_of_free_in_hist_env env_verified fv_R x_free_in_P) in
      have no_instantiations (term.unop unop.isBool x), from no_instantiations.term,
      have h1: σ ⊨ (prop.term (term.unop unop.isBool x)).erased,
      from consequent_of_H_P env_verified R_valid vc_valid this,
      have (prop.term (term.unop unop.isBool x)).erased = vc.term (term.unop unop.isBool x),
      by unfold prop.erased,
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
      have unop.apply unop.isBool v = some value.true, from valid.eq.unop.mpr this,
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

theorem progress (s: stack): (⊢ₛ s) → is_value s ∨ ∃s', s ⟶ s'
:=
  assume s_verified: ⊢ₛ s,
  begin
    induction s_verified,
    case stack.vcgen.top σ e Q R H P env_verified fv_R R_valid e_verified { from
      show is_value (R, H, σ, e) ∨ ∃s', (R, H, σ, e) ⟶ s', from exp.progress env_verified fv_R R_valid e_verified
    },
    case stack.vcgen.cons R H P s' σ σ' f g x y fx R' S' e₁ e₂ H' vₓ Q
                          s'_verified _ fv_R' R_valid g_is_func x_is_v _ cont _ _ ih { from
      let s := (s' · [R', H', σ, letapp y = g[x] in e₁]) in
      have s_cons: s = (s' · [R', H', σ, letapp y = g[x] in e₁]), from rfl,
      or.elim ih
      ( -- step return
        assume s'_is_value: is_value s',
        let ⟨R₂, H₂, σ₂, z, v, ⟨s'_return, env2_has_z⟩⟩ := s'_is_value in
        have s_return_cons: s = ((R₂, H₂, σ₂, exp.return z) · [R', H', σ, letapp y = g[x] in e₁]),
        from s'_return ▸ s_cons,
        have s ⟶ (R', H' · call f fx R S' e₂ H σ' vₓ, σ[y↦v], e₁),
        from s_return_cons.symm ▸ (step.return env2_has_z g_is_func x_is_v),
        have ∃s', s ⟶ s',
        from exists.intro (R', H' · call f fx R S' e₂ H σ' vₓ, σ[y↦v], e₁) this,
        show is_value s ∨ ∃s', s ⟶ s', from or.inr this
      )
      ( -- step ctx
        assume s'_can_step: ∃s'', s' ⟶ s'',
        let ⟨s'', s'_steps⟩ := s'_can_step in
        have s ⟶ (s'' · [R', H', σ, letapp y = g[x] in e₁]), from step.ctx s'_steps,
        have ∃s', s ⟶ s', from exists.intro (s'' · [R', H', σ, letapp y = g[x] in e₁]) this,
        show is_value s ∨ ∃s', s ⟶ s', from or.inr this
      )
    }
  end
