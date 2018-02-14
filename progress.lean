import .syntax .notations .logic .evaluation .vcgen

@[reducible]
def is_return(s: stack): Prop := ∃(σ: env) (x: var), s = (σ, exp.return x)

lemma exp.vcgen.return.inv {P: prop} {x: var} {Q: propctx}: (P ⊢ exp.return x : Q) → x ∈ FV P :=
  assume return_verified: P ⊢ exp.return x : Q,
  begin
    cases return_verified,
    case exp.vcgen.return x_free {
      show x ∈ FV P, from x_free
    }
  end

lemma stack.vcgen.top.inv {H: list call} {σ: env} {e: exp}: (H ⊩ (σ, e)) → ∃P Q, (⊢ σ: P) ∧ (H && P ⊢ e: Q) :=
  assume top_verified: H ⊩ (σ, e),
  begin
    cases top_verified,
    case stack.vcgen.top P Q env_verified e_verified {
      show ∃P Q, (⊢ σ: P) ∧ (H && P ⊢ e: Q), from exists.intro P (exists.intro Q ⟨env_verified, e_verified⟩)
    }
  end

lemma not_free_of_subst_env {P: prop} {σ: env} {x: var}:
       (⊢ σ : P) → free_in_prop x P → ∀R: spec, ¬(free_in_prop x (spec.subst_env σ R)) :=
  sorry
  -- assume env_verified: ⊢ σ : P,
  -- assume x_free_in_P: free_in_prop x P,
  -- show (∀R: spec, ¬(free_in_prop x (spec.subst_env σ R))), by begin
  --   induction env_verified,
  --   case env.vcgen.empty { from
  --     assume R: spec,
  --     assume x_free_in_subst: free_in_prop x (spec.subst_env env.empty R),
  --     have free_in_term x value.true, from free_in_prop.term.inv x_free_in_P,
  --     show «false», from free_in_term.value.inv this
  --   },
  --   case env.vcgen.tru σ' y Q _ _ ih { from
  --     assume R: spec,
  --     assume x_free_in_subst: free_in_prop x (spec.subst_env (σ'[y↦value.true]) R),
  --     have x_neq_y: x ≠ y, from (free_of_subst_env_spec x_free_in_subst).left,
  --     have free_in_prop x Q ∨ free_in_prop x (y ≡ value.true), from free_in_prop.and.inv x_free_in_P,
  --     or.elim this (
  --       assume : free_in_prop x Q,
  --       have x_free_in_R: free_in_prop x (spec.subst_env σ' R), from (free_of_subst_env_spec x_free_in_subst).right,
  --       have ¬free_in_prop x (spec.subst_env σ' R), from ih this R,
  --       show «false», from this x_free_in_R
  --     ) (
  --       assume : free_in_prop x (y ≡ value.true),
  --       have free_in_term x (y ≡ value.true), from free_in_prop.term.inv this,
  --       (free_in_term.binop.inv this).elim (
  --         assume : free_in_term x y,
  --         have x = y, from free_in_term.var.inv this,
  --         show «false», from x_neq_y this
  --       ) (
  --         assume : free_in_term x (value.true),
  --         show «false», from free_in_term.value.inv this
  --       )
  --     )
  --   },
  --   case env.vcgen.fls σ' y Q _ _ ih { from
  --     assume R: spec,
  --     assume x_free_in_subst: free_in_prop x (spec.subst_env (σ'[y↦value.false]) R),
  --     have x_neq_y: x ≠ y, from (free_of_subst_env_spec x_free_in_subst).left,
  --     have free_in_prop x Q ∨ free_in_prop x (y ≡ value.false), from free_in_prop.and.inv x_free_in_P,
  --     or.elim this (
  --       assume : free_in_prop x Q,
  --       have x_free_in_R: free_in_prop x (spec.subst_env σ' R), from (free_of_subst_env_spec x_free_in_subst).right,
  --       have ¬free_in_prop x (spec.subst_env σ' R), from ih this R,
  --       show «false», from this x_free_in_R
  --     ) (
  --       assume : free_in_prop x (y ≡ value.false),
  --       have free_in_term x (y ≡ value.false), from free_in_prop.term.inv this,
  --       (free_in_term.binop.inv this).elim (
  --         assume : free_in_term x y,
  --         have x = y, from free_in_term.var.inv this,
  --         show «false», from x_neq_y this
  --       ) (
  --         assume : free_in_term x (value.false),
  --         show «false», from free_in_term.value.inv this
  --       )
  --     )
  --   },
  --   case env.vcgen.num n σ' y Q _ _ ih { from
  --     assume R: spec,
  --     assume x_free_in_subst: free_in_prop x (spec.subst_env (σ'[y↦value.num n]) R),
  --     have x_neq_y: x ≠ y, from (free_of_subst_env_spec x_free_in_subst).left,
  --     have free_in_prop x Q ∨ free_in_prop x (y ≡ value.num n), from free_in_prop.and.inv x_free_in_P,
  --     or.elim this (
  --       assume : free_in_prop x Q,
  --       have x_free_in_R: free_in_prop x (spec.subst_env σ' R), from (free_of_subst_env_spec x_free_in_subst).right,
  --       have ¬free_in_prop x (spec.subst_env σ' R), from ih this R,
  --       show «false», from this x_free_in_R
  --     ) (
  --       assume : free_in_prop x (y ≡ value.num n),
  --       have free_in_term x (y ≡ value.num n), from free_in_prop.term.inv this,
  --       (free_in_term.binop.inv this).elim (
  --         assume : free_in_term x y,
  --         have x = y, from free_in_term.var.inv this,
  --         show «false», from x_neq_y this
  --       ) (
  --         assume : free_in_term x (value.num n),
  --         show «false», from free_in_term.value.inv this
  --       )
  --     )
  --   },
  --   case env.vcgen.func f σ₁ σ₂ g gx R' S' e Q₁ Q₂ Q₃ _ _ _ fv_R fv_S _ _ ih₁ ih₂ { from
  --     assume R: spec,
  --     assume x_free_in_subst: free_in_prop x (spec.subst_env (σ₂[f↦value.func g gx R' S' e σ₁]) R),
  --     have x_neq_f: x ≠ f, from (free_of_subst_env_spec x_free_in_subst).left,
  --     let R'' := spec.subst_env (σ₁[g↦value.func g gx R' S' e σ₁]) R' in
  --     let S'' := spec.subst_env (σ₁[g↦value.func g gx R' S' e σ₁]) S' in
  --     have free_in_prop x (Q₁ && spec.func ↑f gx R'' S'') ∨ free_in_prop x (f ≡ value.func g gx R' S' e σ₁),
  --     from free_in_prop.and.inv x_free_in_P,
  --     or.elim this (
  --       assume : free_in_prop x (Q₁ && spec.func f gx R'' S''),
  --       or.elim (free_in_prop.and.inv this) (
  --         assume : free_in_prop x Q₁,
  --         have x_free_in_R: free_in_prop x (spec.subst_env σ₂ R), from (free_of_subst_env_spec x_free_in_subst).right,
  --         have ¬free_in_prop x (spec.subst_env σ₂ R), from ih₁ this R,
  --         show «false», from this x_free_in_R
  --       ) (
  --         assume x_free_in_func: free_in_prop x (spec.func f gx R'' S''),
  --         let forallp := (prop.implies R''.to_prop (prop.pre f gx)
  --                       && prop.implies (R''.to_prop && prop.post f gx) S''.to_prop) in
  --         have h: (spec.func f gx R'' S'').to_prop = (term.unop unop.isFunc f && prop.forallc gx f forallp),
  --         by unfold spec.to_prop,
  --         have free_in_prop x (term.unop unop.isFunc f && prop.forallc gx f forallp), from h ▸ x_free_in_func,
  --         have free_in_prop x (term.unop unop.isFunc f) ∨ free_in_prop x (prop.forallc gx f forallp),
  --         from free_in_prop.and.inv this,
  --         or.elim this (
  --           assume : free_in_prop x (term.unop unop.isFunc f),
  --           have free_in_term x (term.unop unop.isFunc f), from free_in_prop.term.inv this,
  --           have free_in_term x f, from free_in_term.unop.inv this,
  --           have x = f, from free_in_term.var.inv this,
  --           show «false», from x_neq_f this
  --         ) (
  --           assume : free_in_prop x (prop.forallc gx f forallp),
  --           have x_neq_gx: x ≠ gx, from (free_in_prop.forallc.inv this).left,
  --           have free_in_term x f ∨ free_in_prop x forallp, from (free_in_prop.forallc.inv this).right,
  --           or.elim this (
  --             assume : free_in_term x f,
  --             have x = f, from free_in_term.var.inv this,
  --             show «false», from x_neq_f this
  --           ) (
  --             assume : free_in_prop x forallp,
  --             or.elim (free_in_prop.and.inv this) (
  --               assume : free_in_prop x (prop.implies R''.to_prop (prop.pre f gx)),
  --               or.elim (free_in_prop.implies.inv this) (
  --                 assume : free_in_prop x R''.to_prop,
  --                 have x ≠ g ∧ free_in_prop x (spec.subst_env σ₁ R').to_prop, from free_of_subst_env_spec this,
  --                 have x_neq_g: x ≠ g, from this.left,
  --                 have x_free_in_sR': free_in_prop x (spec.subst_env σ₁ R').to_prop, from this.right,
  --                 have x_free_in_R': x ∈ FV R'.to_prop, from free_of_subst_env x_free_in_sR',
  --                 have x ∈ FV Q₂ ∪ {g, gx}, from set.mem_of_mem_of_subset x_free_in_R' fv_R,
  --                 have x ∈ FV Q₂ ∨ x ∈ {g, gx}, from set.mem_or_mem_of_mem_union this,
  --                 or.elim this (
  --                   assume : x ∈ FV Q₂,
  --                   have ¬ free_in_prop x ↑(spec.subst_env σ₁ R'), from ih₂ this R',
  --                   show «false», from this x_free_in_sR'
  --                 ) (
  --                   assume : x ∈ {g, gx},
  --                   have (x = g) ∨ (x = gx), from mem_of_2set this,
  --                   or.elim this (
  --                     assume : x = g,
  --                     show «false», from x_neq_g this
  --                   ) (
  --                     assume : x = gx,
  --                     show «false», from x_neq_gx this
  --                   )
  --                 )
  --               ) (
  --                 assume : free_in_prop x (prop.pre f gx),
  --                 have free_in_term x f ∨ free_in_term x gx, from free_in_prop.pre.inv this,
  --                 or.elim this (
  --                   assume : free_in_term x f,
  --                   have x = f, from free_in_term.var.inv this,
  --                   show «false», from x_neq_f this
  --                 ) (
  --                   assume : free_in_term x gx,
  --                   have x = gx, from free_in_term.var.inv this,
  --                   show «false», from x_neq_gx this
  --                 )
  --               )
  --             ) (
  --               assume : free_in_prop x (prop.implies (R''.to_prop && prop.post f gx) S''.to_prop),
  --               or.elim (free_in_prop.implies.inv this) (
  --                 assume : free_in_prop x (R''.to_prop && prop.post f gx),
  --                 or.elim (free_in_prop.and.inv this) (
  --                   assume : free_in_prop x R''.to_prop,
  --                   have x ≠ g ∧ free_in_prop x (spec.subst_env σ₁ R').to_prop, from free_of_subst_env_spec this,
  --                   have x_neq_g: x ≠ g, from this.left,
  --                   have x_free_in_sR': free_in_prop x (spec.subst_env σ₁ R').to_prop, from this.right,
  --                   have x_free_in_R': x ∈ FV R'.to_prop, from free_of_subst_env x_free_in_sR',
  --                   have x ∈ FV Q₂ ∪ {g, gx}, from set.mem_of_mem_of_subset x_free_in_R' fv_R,
  --                   have x ∈ FV Q₂ ∨ x ∈ {g, gx}, from set.mem_or_mem_of_mem_union this,
  --                   or.elim this (
  --                     assume : x ∈ FV Q₂,
  --                     have ¬ free_in_prop x ↑(spec.subst_env σ₁ R'), from ih₂ this R',
  --                     show «false», from this x_free_in_sR'
  --                   ) (
  --                     assume : x ∈ {g, gx},
  --                     have (x = g) ∨ (x = gx), from mem_of_2set this,
  --                     or.elim this (
  --                       assume : x = g,
  --                       show «false», from x_neq_g this
  --                     ) (
  --                       assume : x = gx,
  --                       show «false», from x_neq_gx this
  --                     )
  --                   )
  --                 ) (
  --                   assume : free_in_prop x (prop.post f gx),
  --                   have free_in_term x f ∨ free_in_term x gx, from free_in_prop.post.inv this,
  --                   or.elim this (
  --                     assume : free_in_term x f,
  --                     have x = f, from free_in_term.var.inv this,
  --                     show «false», from x_neq_f this
  --                   ) (
  --                     assume : free_in_term x gx,
  --                     have x = gx, from free_in_term.var.inv this,
  --                     show «false», from x_neq_gx this
  --                   )
  --                 )
  --               ) (
  --                 assume : free_in_prop x S''.to_prop,
  --                 have x ≠ g ∧ free_in_prop x (spec.subst_env σ₁ S').to_prop, from free_of_subst_env_spec this,
  --                 have x_neq_g: x ≠ g, from this.left,
  --                 have x_free_in_sS': free_in_prop x (spec.subst_env σ₁ S').to_prop, from this.right,
  --                 have x_free_in_S': x ∈ FV S'.to_prop, from free_of_subst_env x_free_in_sS',
  --                 have x ∈ FV Q₂ ∪ {g, gx}, from set.mem_of_mem_of_subset x_free_in_S' fv_S,
  --                 have x ∈ FV Q₂ ∨ x ∈ {g, gx}, from set.mem_or_mem_of_mem_union this,
  --                 or.elim this (
  --                   assume : x ∈ FV Q₂,
  --                   have ¬ free_in_prop x ↑(spec.subst_env σ₁ S'), from ih₂ this S',
  --                   show «false», from this x_free_in_sS'
  --                 ) (
  --                   assume : x ∈ {g, gx},
  --                   have (x = g) ∨ (x = gx), from mem_of_2set this,
  --                   or.elim this (
  --                     assume : x = g,
  --                     show «false», from x_neq_g this
  --                   ) (
  --                     assume : x = gx,
  --                     show «false», from x_neq_gx this
  --                   )
  --                 )
  --               )
  --             )
  --           )
  --         )
  --       )
  --     ) (
  --       assume : free_in_prop x (f ≡ value.func g gx R' S' e σ₁),
  --       have free_in_term x (f ≡ value.func g gx R' S' e σ₁), from free_in_prop.term.inv this,
  --       (free_in_term.binop.inv this).elim (
  --         assume : free_in_term x f,
  --         have x = f, from free_in_term.var.inv this,
  --         show «false», from x_neq_f this
  --       ) (
  --         assume : free_in_term x (value.func g gx R' S' e σ₁),
  --         show «false», from free_in_term.value.inv this
  --       )
  --     )
  --   }
  -- end
  

lemma val_of_free_in_nonempty_env {P: prop} {σ: env} {x y: var} {v: value}:
                                  (⊢ σ : P) → (x ≠ y → ∃v', σ y = some v') →
                                  ∃v', σ[x↦v] y = some v' :=
  sorry
  -- assume env_verified: ⊢ σ : P,
  -- assume ih: x ≠ y → ∃v', σ y = some v',
  -- if x_eq_y: x = y ∧ option.is_none (σ.apply y) then (
  --   have h: σ[x↦v].apply x = (if x = x ∧ option.is_none (σ.apply x) then ↑v else σ.apply x), by unfold env.apply,
  --   have (if x = x ∧ option.is_none (σ.apply x) then ↑v else σ.apply x) = ↑v, by simp *,
  --   have σ[x↦v].apply x = ↑v, from this ▸ h,
  --   have σ[x↦v].apply y = some v, from x_eq_y.left ▸ this,
  --   show ∃v', σ[x↦v] y = some v', from exists.intro v this
  -- ) else (
  --   have ∃v', σ y = some v', from (
  --     have ¬(x = y) ∨ ¬(option.is_none (σ.apply y)), from not_and_distrib.mp x_eq_y,
  --     this.elim (
  --       assume : x ≠ y,
  --       show ∃v', σ y = some v', from ih this        
  --     ) ( 
  --       assume : ¬(option.is_none (env.apply σ y)),
  --       have ¬(option.is_none (σ y)), from this,
  --       show ∃v', σ y = some v', from not_is_none.rinv.mpr this
  --     )
  --   ),
  --   let ⟨v', σ_has_y⟩ := this in
  --   have h: σ[x↦v].apply y = (if x = y ∧ option.is_none (σ.apply y) then ↑v else σ.apply y), by unfold env.apply,
  --   have (if x = y ∧ option.is_none (σ.apply y) then ↑v else σ.apply y) = σ.apply y, by simp *,
  --   have σ[x↦v].apply y = σ.apply y, from this ▸ h,
  --   have σ[x↦v].apply y = some v', from eq.trans this σ_has_y,
  --   show ∃v', σ[x↦v] y = some v', from exists.intro v' this
  -- )

lemma val_of_free_in_env {P: prop} {σ: env} {x: var}: (⊢ σ : P) → x ∈ FV P → ∃v, σ x = some v :=
  sorry
  -- assume env_verified: ⊢ σ: P,
  -- assume x_free_in_P: x ∈ FV P,
  -- begin
  --   induction env_verified,
  --   case env.vcgen.empty {
  --     cases x_free_in_P,
  --     case free_in_prop.term x_free_in_true {
  --       cases x_free_in_true
  --     }
  --   },
  --   case env.vcgen.tru σ' x' Q _ σ'_verified ih { from
  --     val_of_free_in_nonempty_env σ'_verified (
  --       assume x'_is_not_x: x' ≠ x,
  --       have free_in_prop x Q ∨ free_in_prop x (x' ≡ value.true), from free_in_prop.and.inv x_free_in_P,
  --       or.elim this.symm
  --       (
  --         assume x_free_in_true: free_in_prop x (x' ≡ value.true),
  --         show ∃v, σ' x = some v, by begin
  --           cases x_free_in_true,
  --           case free_in_prop.term x_free_in_eq {
  --             cases x_free_in_eq,
  --             case free_in_term.binop₁ free_in_x' {
  --               have x'_is_x: (x' = x), from (free_in_term.var.inv free_in_x').symm,
  --               contradiction
  --             },
  --             case free_in_term.binop₂ free_in_true {
  --               cases free_in_true
  --             }
  --           }
  --         end
  --       )
  --       (
  --         assume x_free_in_Q: free_in_prop x Q,
  --         show ∃v, σ' x = some v, from ih x_free_in_Q
  --       )
  --     )
  --   },
  --   case env.vcgen.fls σ' x' Q _ σ'_verified ih { from
  --     val_of_free_in_nonempty_env σ'_verified (
  --       assume x'_is_not_x: x' ≠ x,
  --       have free_in_prop x Q ∨ free_in_prop x (x' ≡ value.false), from free_in_prop.and.inv x_free_in_P,
  --       or.elim this.symm
  --       (
  --         assume x_free_in_false: free_in_prop x (x' ≡ value.false),
  --         show ∃v, σ' x = some v, by begin
  --           cases x_free_in_false,
  --           case free_in_prop.term x_free_in_eq {
  --             cases x_free_in_eq,
  --             case free_in_term.binop₁ free_in_x' {
  --               have x'_is_x: (x' = x), from (free_in_term.var.inv free_in_x').symm,
  --               contradiction
  --             },
  --             case free_in_term.binop₂ free_in_false {
  --               cases free_in_false
  --             }
  --           }
  --         end
  --       )
  --       (
  --         assume x_free_in_Q: free_in_prop x Q,
  --         show ∃v, σ' x = some v, from ih x_free_in_Q
  --       )
  --     )
  --   },
  --   case env.vcgen.num n σ' x' Q _ σ'_verified ih { from
  --     val_of_free_in_nonempty_env σ'_verified (
  --       assume x'_is_not_x: x' ≠ x,
  --       have free_in_prop x Q ∨ free_in_prop x (x' ≡ value.num n), from free_in_prop.and.inv x_free_in_P,
  --       or.elim this.symm
  --       (
  --         assume x_free_in_num: free_in_prop x (x' ≡ value.num n),
  --         show ∃v, σ' x = some v, by begin
  --           cases x_free_in_num,
  --           case free_in_prop.term x_free_in_eq {
  --             cases x_free_in_eq,
  --             case free_in_term.binop₁ free_in_x' {
  --               have x'_is_x: (x' = x), from (free_in_term.var.inv free_in_x').symm,
  --               contradiction
  --             },
  --             case free_in_term.binop₂ free_in_num {
  --               cases free_in_num
  --             }
  --           }
  --         end
  --       )
  --       (
  --         assume x_free_in_Q: free_in_prop x Q,
  --         show ∃v, σ' x = some v, from ih x_free_in_Q
  --       )
  --     )
  --   },
  --   case env.vcgen.func σ₁ σ₂ f g fx R S e Q₁ Q₂ Q₃ _ σ₁_verified σ₂_verified R_fv S_fv func_verified S_valid { from
  --     val_of_free_in_nonempty_env σ₁_verified (
  --       assume f_is_not_x: f ≠ x,
  --       let R': spec := spec.subst_env (σ₂[g↦value.func g fx R S e σ₂]) R in
  --       let S': spec := spec.subst_env (σ₂[g↦value.func g fx R S e σ₂]) S in
  --       let fspec: prop := spec.func f fx R' S' in
  --       have free_in_prop x (Q₁ && fspec) ∨ free_in_prop x (f ≡ value.func g fx R S e σ₂),
  --       from free_in_prop.and.inv x_free_in_P,
  --       or.elim this
  --       (
  --         assume : free_in_prop x (Q₁ && fspec),
  --         have free_in_prop x Q₁ ∨ free_in_prop x fspec, from free_in_prop.and.inv this,
  --         or.elim this
  --         (
  --           assume : free_in_prop x Q₁,
  --           show ∃v, σ₁ x = some v, from ih_1 this
  --         )
  --         (
  --           assume : free_in_prop x fspec,
  --           have 
  --             free_in_prop x (term.unop unop.isFunc f) ∨
  --             free_in_prop x (prop.forallc fx f (prop.implies R'.to_prop (prop.pre f fx)
  --                             && prop.implies (R'.to_prop && prop.post f fx) S'.to_prop)),
  --           from free_in_prop.and.inv this,
  --           or.elim this
  --           (
  --             assume x_free_in_unopp: free_in_prop x (term.unop unop.isFunc f),
  --             show ∃v, σ₁ x = some v, by begin
  --               cases x_free_in_unopp,
  --               case free_in_prop.term x_free_in_unop {
  --                 cases x_free_in_unop,
  --                 case free_in_term.unop free_in_f {
  --                   have : (f = x), from (free_in_term.var.inv free_in_f).symm,
  --                   contradiction
  --                 }
  --               }
  --             end
  --           )
  --           (
  --             assume : free_in_prop x (prop.forallc fx f (prop.implies R'.to_prop (prop.pre f fx)
  --                                    && prop.implies (R'.to_prop && prop.post f fx) S'.to_prop)),
  --             show ∃v, σ₁ x = some v, by begin
  --               cases this,
  --               case free_in_prop.forallc₁ x_not_fx x_free_in_f {
  --                 have : (f = x), from (free_in_term.var.inv x_free_in_f).symm,
  --                 contradiction
  --               },
  --               case free_in_prop.forallc₂ x_neq_fx x_free_in_p { from
  --                 have free_in_prop x (prop.implies R'.to_prop (prop.pre f fx))
  --                    ∨ free_in_prop x (prop.implies (R'.to_prop && prop.post f fx) S'.to_prop),
  --                 from free_in_prop.and.inv x_free_in_p,
  --                 or.elim this
  --                 (
  --                   assume : free_in_prop x (prop.implies R'.to_prop (prop.pre f fx)),
  --                   have free_in_prop x (prop.or R'.to_prop.not (prop.pre f fx)), from this,
  --                   have free_in_prop x R'.to_prop.not ∨ free_in_prop x (prop.pre f fx),
  --                   from free_in_prop.or.inv this,
  --                   or.elim this
  --                   (
  --                     assume : free_in_prop x R'.to_prop.not,
  --                     have free_in_prop x R'.to_prop, from free_in_prop.not.inv this,
  --                     have free_in_prop x (spec.subst_env (σ₂[g↦value.func g fx R S e σ₂]) R).to_prop, from this,
  --                     have x ≠ g ∧ free_in_prop x (spec.subst_env σ₂ R).to_prop, from free_of_subst_env_spec this,
  --                     have x_neq_g: x ≠ g, from this.left,
  --                     have x_free_in_sR: free_in_prop x (spec.subst_env σ₂ R).to_prop, from this.right,
  --                     have x_free_in_R: x ∈ FV R.to_prop, from free_of_subst_env x_free_in_sR,
  --                     have x ∈ FV Q₂ ∪ {g, fx}, from set.mem_of_mem_of_subset x_free_in_R R_fv,
  --                     have x ∈ FV Q₂ ∨ x ∈ {g, fx}, from set.mem_or_mem_of_mem_union this,
  --                     or.elim this (
  --                       assume : x ∈ FV Q₂,
  --                       have ¬ free_in_prop x (spec.subst_env σ₂ R).to_prop,
  --                       from not_free_of_subst_env σ₂_verified this R,
  --                       show ∃v, σ₁ x = some v, from absurd x_free_in_sR this
  --                     ) (
  --                       assume : x ∈ {g, fx},
  --                       have (x = g) ∨ (x = fx), from mem_of_2set this,
  --                       or.elim this (
  --                         assume : x = g,
  --                         show ∃v, σ₁ x = some v, from absurd this x_neq_g
  --                       ) (
  --                         assume : x = fx,
  --                         show ∃v, σ₁ x = some v, from absurd this x_neq_fx
  --                       )
  --                     )
  --                   )
  --                   (
  --                     assume x_free_in_pre: free_in_prop x (prop.pre f fx),
  --                     show ∃v, σ₁ x = some v, by begin
  --                       cases x_free_in_pre,
  --                       case free_in_prop.pre₁ x_free_in_f {
  --                         have : (f = x), from (free_in_term.var.inv x_free_in_f).symm,
  --                         contradiction
  --                       },
  --                       case free_in_prop.pre₂ x_free_in_fx {
  --                         have : (x = fx), from (free_in_term.var.inv x_free_in_fx),
  --                         contradiction
  --                       }
  --                     end
  --                   )
  --                 )
  --                 (
  --                   assume : free_in_prop x (prop.implies (R'.to_prop && prop.post f fx) S'.to_prop),
  --                   or.elim (free_in_prop.implies.inv this) (
  --                     assume : free_in_prop x (R'.to_prop && prop.post f fx),
  --                     or.elim (free_in_prop.and.inv this) (
  --                       assume : free_in_prop x R'.to_prop,
  --                       have x ≠ g ∧ free_in_prop x (spec.subst_env σ₂ R).to_prop, from free_of_subst_env_spec this,
  --                       have x_neq_g: x ≠ g, from this.left,
  --                       have x_free_in_sR: free_in_prop x (spec.subst_env σ₂ R).to_prop, from this.right,
  --                       have x_free_in_R: x ∈ FV R.to_prop, from free_of_subst_env x_free_in_sR,
  --                       have x ∈ FV Q₂ ∪ {g, fx}, from set.mem_of_mem_of_subset x_free_in_R R_fv,
  --                       have x ∈ FV Q₂ ∨ x ∈ {g, fx}, from set.mem_or_mem_of_mem_union this,
  --                       or.elim this (
  --                         assume : x ∈ FV Q₂,
  --                         have ¬ free_in_prop x (spec.subst_env σ₂ R).to_prop,
  --                         from not_free_of_subst_env σ₂_verified this R,
  --                         show ∃v, σ₁ x = some v, from absurd x_free_in_sR this
  --                       ) (
  --                         assume : x ∈ {g, fx},
  --                         have (x = g) ∨ (x = fx), from mem_of_2set this,
  --                         or.elim this (
  --                           assume : x = g,
  --                           show ∃v, σ₁ x = some v, from absurd this x_neq_g
  --                         ) (
  --                           assume : x = fx,
  --                           show ∃v, σ₁ x = some v, from absurd this x_neq_fx
  --                         )
  --                       )
  --                     ) (
  --                       assume : free_in_prop x (prop.post f fx),
  --                       have free_in_term x f ∨ free_in_term x fx, from free_in_prop.post.inv this,
  --                       or.elim this (
  --                         assume : free_in_term x f,
  --                         have x = f, from free_in_term.var.inv this,
  --                         show ∃v, σ₁ x = some v, from absurd this f_is_not_x.symm 
  --                       ) (
  --                         assume : free_in_term x fx,
  --                         have x = fx, from free_in_term.var.inv this,
  --                         show ∃v, σ₁ x = some v, from absurd this x_neq_fx
  --                       )
  --                     )
  --                   ) (
  --                     assume : free_in_prop x S'.to_prop,
  --                     have x ≠ g ∧ free_in_prop x (spec.subst_env σ₂ S).to_prop, from free_of_subst_env_spec this,
  --                     have x_neq_g: x ≠ g, from this.left,
  --                     have x_free_in_sS: free_in_prop x (spec.subst_env σ₂ S).to_prop, from this.right,
  --                     have x_free_in_S: x ∈ FV S.to_prop, from free_of_subst_env x_free_in_sS,
  --                     have x ∈ FV Q₂ ∪ {g, fx}, from set.mem_of_mem_of_subset x_free_in_S S_fv,
  --                     have x ∈ FV Q₂ ∨ x ∈ {g, fx}, from set.mem_or_mem_of_mem_union this,
  --                     or.elim this (
  --                       assume : x ∈ FV Q₂,
  --                       have ¬ free_in_prop x (spec.subst_env σ₂ S).to_prop,
  --                       from not_free_of_subst_env σ₂_verified this S,
  --                       show ∃v, σ₁ x = some v, from absurd x_free_in_sS this
  --                     ) (
  --                       assume : x ∈ {g, fx},
  --                       have (x = g) ∨ (x = fx), from mem_of_2set this,
  --                       or.elim this (
  --                         assume : x = g,
  --                         show ∃v, σ₁ x = some v, from absurd this x_neq_g
  --                       ) (
  --                         assume : x = fx,
  --                         show ∃v, σ₁ x = some v, from absurd this x_neq_fx
  --                       )
  --                     )
  --                   )
  --                 )
  --               }
  --             end
  --           )
  --         )
  --       )
  --       (
  --         assume x_free_in_func: free_in_prop x (f ≡ value.func g fx R S e σ₂),
  --         show ∃v, σ₁ x = some v, by begin
  --           cases x_free_in_func,
  --           case free_in_prop.term x_free_in_eq {
  --             cases x_free_in_eq,
  --             case free_in_term.binop₁ free_in_f {
  --               have f_is_x: (f = x), from (free_in_term.var.inv free_in_f).symm,
  --               contradiction
  --             },
  --             case free_in_term.binop₂ free_in_func {
  --               cases free_in_func
  --             }
  --           }
  --         end
  --       )
  --     )
  --   }
  -- end

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

lemma env_translation_erased_valid {P: prop} {σ: env}: (⊢ σ: P) → σ ⊨ P.erased :=
  assume env_verified: (⊢ σ : P),
  begin
    induction env_verified,
    case env.vcgen.empty {
      show env.empty ⊨ prop.erased (value.true), from (
        have h: prop.erased (prop.term ↑value.true) = vc.term ↑value.true, by unfold prop.erased,
        have env.empty ⊨ value.true, from valid.tru,
        show env.empty ⊨ prop.erased (value.true), from h ▸ this
      )
    },
    case env.vcgen.tru σ' x' Q x_not_free_in_σ' σ'_verified ih {
      show (σ'[x'↦value.true]) ⊨ prop.erased (Q && (x' ≡ value.true)), from (
        have σ'.apply x' = none, from env.contains_apply_equiv.left.mpr x_not_free_in_σ',
        have h1: (σ'[x'↦value.true]) ⊨ (prop.term (x' ≡ value.true)).erased,
        from simple_equality_valid x_not_free_in_σ',
        have σ' ⊨ Q.erased, from ih,
        have h2: ⊨ vc.subst_env σ' Q.erased, from this,
        have x_not_in_q: x' ∉ FV (vc.subst_env σ' Q.erased), from (
          assume : x' ∈ FV (vc.subst_env σ' Q.erased),
          have x' ∈ FV Q.erased, from free_in_vc.subst_env this,
          have x' ∈ FV Q, from free_of_erased_free (or.inl this),
          have ∃v, σ' x' = some v, from val_of_free_in_env σ'_verified this,
          have x' ∈ σ', from env.contains_apply_equiv.right.mp this,
          show «false», from x_not_free_in_σ' this
        ),
        have vc.subst x' value.true (vc.subst_env σ' Q.erased) = vc.subst_env σ' Q.erased,
        from unchanged_of_subst_nonfree_vc x_not_in_q,
        have h: ⊨ vc.subst x' value.true (vc.subst_env σ' Q.erased),
        from @eq.subst vc (λa, ⊨ a) (vc.subst_env σ' Q.erased)
                (vc.subst x' value.true (vc.subst_env σ' Q.erased)) this.symm h2,
        have vc.subst x' value.true (vc.subst_env σ' Q.erased)
           = vc.subst_env (σ'[x'↦value.true]) Q.erased, by unfold vc.subst_env, 
        have ⊨ vc.subst_env (σ'[x'↦value.true]) Q.erased, from this ▸ h,
        have h2: (σ'[x'↦value.true]) ⊨ Q.erased, from this,
        have h3: (σ'[x'↦value.true]) ⊨ (Q.erased && (prop.term (x' ≡ value.true)).erased),
        from valid_env.and h2 h1,
        have prop.erased (prop.and Q (prop.term (x' ≡ value.true))) = Q.erased && (prop.term (x' ≡ value.true)).erased,
        by unfold prop.erased,
        show (σ'[x'↦value.true]) ⊨ prop.erased (Q && (x' ≡ value.true)), from this.symm ▸ h3
      )
    },
    case env.vcgen.fls σ' x' Q σ'_verified ih { from
      show (σ'[x'↦value.false]) ⊨ prop.erased (Q && (x' ≡ value.false)), from (
        sorry
      )
    },
    case env.vcgen.num n σ' x' Q σ'_verified ih { from
      show (σ'[x'↦value.num n]) ⊨ prop.erased (Q && (x' ≡ value.num n)), from (
        sorry
      )
    },
    case env.vcgen.func σ₁ σ₂ f g fx R S e Q₁ Q₂ Q₃ σ₁_verified σ₂_verified R_fv S_fv func_verified S_valid { from
      sorry
    }
  end

lemma env_translation_valid {H: list call} {P: prop} {σ: env}:
  ⟪H⟫ → (⊢ σ: P) → σ ⊨ (↑H && P).instantiated_n :=
  assume h_valid: ⟪H⟫,
  assume env_verified: (⊢ σ : P),
  have h1: σ ⊨ prop.instantiated ↑H, from h_valid σ,
  have σ ⊨ P.erased, from env_translation_erased_valid env_verified,
  have h2: σ ⊨ P.instantiated, from instantiated_of_erased this,
  have σ ⊨ (↑H && P).instantiated, from instantiated_and h1 h2,
  show σ ⊨ (↑H && P).instantiated_n, from instantiated_n_of_instantiated this

lemma exp.progress{H: list call} {P: prop} {Q: propctx} {e: exp} {σ: env}:
                  ⟪H⟫ → (⊢ σ: P) → (H && P ⊢ e: Q) → is_return (σ, e) ∨ ∃c s', (σ, e) ⟶ c, s'
:=
  assume h_valid: ⟪H⟫,
  assume env_verified: (⊢ σ : P),
  assume e_verified: (H && P ⊢ e : Q),
  show is_return (σ, e) ∨ ∃c s', (σ, e) ⟶ c, s', from begin
    cases e_verified,
    case exp.vcgen.tru x e' { from
      let s: stack := (σ, lett x = true in e') in
      have s ⟶ none, (σ[x↦value.true], e'), from step.tru,
      have ∃c s', s ⟶ c, s', from exists.intro none (exists.intro (σ[x↦value.true], e') this),
      show is_return s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },
    case exp.vcgen.fals x e' { from
      let s: stack := (σ, letf x = false in e') in
      have s ⟶ none, (σ[x↦value.false], e'), from step.fals,
      have ∃c s', s ⟶ c, s', from exists.intro none (exists.intro (σ[x↦value.false], e') this),
      show is_return s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },
    case exp.vcgen.num x n e' { from
      let s: stack := (σ, letn x = n in e') in
      have s ⟶ none, (σ[x↦value.num n], e'), from step.num,
      have ∃c s', s ⟶ c, s', from exists.intro none (exists.intro (σ[x↦value.num n], e') this),
      show is_return s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },
    case exp.vcgen.func f x R S e₁ e₂ { from
      let s: stack := (σ, letf f[x] req R ens S {e₁} in e₂) in
      have s ⟶ none, (σ[f↦value.func f x R S e₁ σ], e₂), from step.closure,
      have ∃c s', s ⟶ c, s', from exists.intro none (exists.intro (σ[f↦value.func f x R S e₁ σ], e₂) this),
      show is_return s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },
    case exp.vcgen.unop op x y e' Q' x_free_in_P _ e'_verified pre_valid { from
      let s: stack := (σ, letop y = op[x] in e') in
      have free_in_prop x H ∨ free_in_prop x P, from free_in_prop.and.inv x_free_in_P,
      have x ∈ FV P, from or.elim this.symm id (
        assume : free_in_prop x H,
        show free_in_prop x P, from absurd this (call_history_closed H x)
      ),
      have ∃v, σ x = some v, from val_of_free_in_env env_verified this,
      let ⟨v, env_has_x⟩ := this in
      have no_instantiations (prop.pre₁ op x), from no_instantiations.pre₁,
      have h1: (prop.implies (↑H && P) (prop.pre₁ op x)).instantiated
              = vc.or (↑H && P).not.instantiated (prop.pre₁ op x).erased,
      from or_dist_of_no_instantiations this,
      have h2: (prop.pre₁ op x).erased = (vc.pre₁ op x), by unfold prop.erased,
      have h3: (↑H && P).not.instantiated = (↑H && P).instantiated_n.not, from not_dist_instantiated,
      have σ ⊨ (prop.implies (↑H && P) (prop.pre₁ op x)).instantiated, from pre_valid σ,
      have σ ⊨ vc.or (↑H && P).instantiated_n.not (vc.pre₁ op x), from h3 ▸ h2 ▸ h1 ▸ this,
      have h4: σ ⊨ vc.implies (↑H && P).instantiated_n (vc.pre₁ op x), from this,
      have σ ⊨ (↑H && P).instantiated_n, from env_translation_valid h_valid env_verified,
      have σ ⊨ vc.pre₁ op x, from valid.mp_env h4 this,
      have h5: ⊨ vc.subst_env σ (vc.pre₁ op x), from this,
      have vc.subst_env σ (vc.pre₁ op x) = vc.pre₁ op (term.subst_env σ x), from vc.subst_env.pre₁,
      have ⊨ vc.pre₁ op (term.subst_env σ x), from this ▸ h5,
      have x_from_env: term.subst_env σ x = v, from (term.subst_env.var.right v).mp env_has_x,
      have ⊨ vc.pre₁ op v, from x_from_env ▸ this,
      have (∃v', unop.apply op v = some v'), from valid.pre₁.inv this,
      let ⟨v', op_v_is_v'⟩ := this in
      have s ⟶ none, (σ[y↦v'], e'), from step.unop env_has_x op_v_is_v',
      have ∃c s', s ⟶ c, s', from exists.intro none (exists.intro (σ[y↦v'], e') this),
      show is_return s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },


    case exp.vcgen.return a x { from
      let s: stack := (σ, exp.return x) in
      have s_is_return: s = (σ, exp.return x), from rfl,
      have is_return_s: is_return s = (∃(σ': env) (x': var), s = (σ', exp.return x')), by unfold is_return,
      have (∃(σ': env) (x': var), s = (σ', exp.return x')), from exists.intro σ (exists.intro x s_is_return),
      have is_return s, from is_return_s ▸ this,
      show is_return s ∨ ∃c s', s ⟶ c, s', from or.inl this
    }
  end

theorem progress(H: list call) (s: stack): ⟪H⟫ → (H ⊩ s) → is_return s ∨ ∃c s', s ⟶ c, s'
:=
  assume h_valid: ⟪H⟫,
  assume s_verified: H ⊩ s,
  begin
    induction s_verified,
    case stack.vcgen.top σ e Q P H env_verified e_verified { from
      show is_return (σ, e) ∨ ∃c s', (σ, e) ⟶ c, s', from exp.progress h_valid env_verified e_verified
    },
    case stack.vcgen.cons H P s' σ σ' f g x y gx R S e vₓ Q s'_verified env_verified f_is_func x_is_v _ cont ih { from
      let s := (s' · [σ, let y = f[x] in e]) in
      have s_cons: s = (s' · [σ, let y = f[x] in e]), from rfl,
      (ih h_valid).elim
      ( -- step return
        assume s'_is_return: is_return s',
        let ⟨σ₂, z, s'_return⟩ := s'_is_return in
        have s_return_cons: s = ((σ₂, exp.return z) · [σ, let y = f[x] in e]), from s'_return ▸ s_cons,
        have H ⊩ (σ₂, exp.return z), from s'_return ▸ s'_verified,
        have ∃P' Q', (⊢ σ₂: P') ∧ (H && P' ⊢ exp.return z: Q'), from stack.vcgen.top.inv this,
        let ⟨P', Q', ⟨env2_verified, return_verified⟩⟩ := this in
        have z ∈ FV (↑H && P'), from exp.vcgen.return.inv return_verified,
        have free_in_prop z H ∨ free_in_prop z P', from free_in_prop.and.inv this,
        have z ∈ FV P', from or.elim this.symm id (
          assume : free_in_prop z H,
          show free_in_prop z P', from absurd this (call_history_closed H z)
        ),
        have ∃v, σ₂ z = some v, from val_of_free_in_env env2_verified this,
        let ⟨v, env2_has_z⟩ := this in
        have s ⟶ some ⟨g, gx, R, S, e, σ', vₓ, v⟩, (σ[y↦v], e),
        from s_return_cons.symm ▸ (step.return env2_has_z f_is_func x_is_v),
        have ∃s', s ⟶ some ⟨g, gx, R, S, e, σ', vₓ, v⟩, s', from exists.intro (σ[y↦v], e) this,
        have ∃c s', s ⟶ c, s', from exists.intro (some ⟨g, gx, R, S, e, σ', vₓ, v⟩) this,
        show is_return s ∨ ∃c s', s ⟶ c, s', from or.inr this
      )
      ( -- step ctx
        assume s'_can_step: ∃c s'', s' ⟶ c, s'',
        let ⟨c, s'', s'_steps⟩ := s'_can_step in
        have s ⟶ c, (s'' · [σ, let y = f[x] in e]), from step.ctx s'_steps,
        have ∃s', s ⟶ c, s', from exists.intro (s'' · [σ, let y = f[x] in e]) this,
        have ∃c s', s ⟶ c, s', from exists.intro c this,
        show is_return s ∨ ∃c s', s ⟶ c, s', from or.inr this
      )
    }
  end
