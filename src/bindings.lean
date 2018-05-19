-- auxiliary lemmas about translation of environments/variable bindings

import .definitions3 .substitution

lemma free_of_contains {P: prop} {σ: env} {x: var}: (⊩ σ : P) → x ∈ σ → x ∈ FV P :=
  assume env_verified: ⊩ σ : P,
  assume x_contained: x ∈ σ,
  show x ∈ FV P, by begin
    induction env_verified,
    case env.dvcgen.empty {
      cases x_contained
    },
    case env.dvcgen.tru σ' y Q _ _ ih { from
      or.elim (env.contains.inv x_contained) (
        assume : x = y,
        have free_in_term x y, from this ▸ free_in_term.var x,
        have free_in_term x (y ≡ value.true), from free_in_term.binop₁ this,
        have free_in_prop x (y ≡ value.true), from free_in_prop.term this,
        show x ∈ FV (Q ⋀ y ≡ value.true), from free_in_prop.and₂ this
      ) (
        assume : x ∈ σ',
        have x ∈ FV Q, from ih this,
        show x ∈ FV (Q ⋀ y ≡ value.true), from free_in_prop.and₁ this
      )
    },
    case env.dvcgen.fls σ' y Q _ _ ih { from
      or.elim (env.contains.inv x_contained) (
        assume : x = y,
        have free_in_term x y, from this ▸ free_in_term.var x,
        have free_in_term x (y ≡ value.false), from free_in_term.binop₁ this,
        have free_in_prop x (y ≡ value.false), from free_in_prop.term this,
        show x ∈ FV (Q ⋀ y ≡ value.false), from free_in_prop.and₂ this
      ) (
        assume : x ∈ σ',
        have x ∈ FV Q, from ih this,
        show x ∈ FV (Q ⋀ y ≡ value.false), from free_in_prop.and₁ this
      )
    },
    case env.dvcgen.num n σ' y Q _ _ ih { from
      or.elim (env.contains.inv x_contained) (
        assume : x = y,
        have free_in_term x y, from this ▸ free_in_term.var x,
        have free_in_term x (y ≡ value.num n), from free_in_term.binop₁ this,
        have free_in_prop x (y ≡ value.num n), from free_in_prop.term this,
        show x ∈ FV (Q ⋀ y ≡ value.num n), from free_in_prop.and₂ this
      ) (
        assume : x ∈ σ',
        have x ∈ FV Q, from ih this,
        show x ∈ FV (Q ⋀ y ≡ value.num n), from free_in_prop.and₁ this
      )
    },
    case env.dvcgen.func f σ₂ σ₁ g gx R S e Q₁ Q₂ Q₃ _ _ _ _ _ _ _ fv_R fv_S e_verified _ ih₁ ih₂ { from
      or.elim (env.contains.inv x_contained) (
        assume : x = f,
        have free_in_term x f, from this ▸ free_in_term.var x,
        have free_in_term x (f ≡ value.func g gx R S e σ₂), from free_in_term.binop₁ this,
        have free_in_prop x (f ≡ value.func g gx R S e σ₂), from free_in_prop.term this,
        have x ∈ FV (prop.term (f ≡ value.func g gx R S e σ₂) ⋀
                     prop.subst_env (σ₂[g↦value.func g gx R S e σ₂])
                     (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))), from free_in_prop.and₁ this,
        show x ∈ FV (Q₁ ⋀ f ≡ value.func g gx R S e σ₂ ⋀
                     prop.subst_env (σ₂[g↦value.func g gx R S e σ₂])
                     (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))), from free_in_prop.and₂ this
      ) (
        assume : x ∈ σ₁,
        have x ∈ FV Q₁, from ih₁ this,
        show x ∈ FV (Q₁ ⋀ f ≡ value.func g gx R S e σ₂ ⋀
                     prop.subst_env (σ₂[g↦value.func g gx R S e σ₂])
                     (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))), from free_in_prop.and₁ this
      )
    }
  end

lemma exp.post_free {P: prop} {e: exp} {Q: propctx} {x: var}:
       (P ⊩ e : Q) → ∀t, x ∈ FV (Q t) → x ∈ FV t ∨ x ∈ FV P :=
  assume e_verified: P ⊩ e : Q,
  begin
    induction e_verified,
    case exp.dvcgen.tru P y e' Q y_not_in_P e'_verified ih { from
      assume t: term,
      assume x_free_in_Qt: x ∈ FV ((propctx.exis y ((y ≡ value.true) ⋀ Q)) t),
      have x_neq_y: x ≠ y, from (free_in_propctx.exis.inv x_free_in_Qt).left,
      have x_not_in_yv: x ∉ FV (y ≡ value.true), from (
        assume : x ∈ FV (y ≡ value.true),
        have free_in_term x y ∨ free_in_term x value.true, from free_in_term.binop.inv this,
        or.elim this (
          assume : free_in_term x y,
          have x = y, from free_in_term.var.inv this,
          show «false», from x_neq_y this
        ) (
          assume : free_in_term x value.true,
          show «false», from free_in_term.value.inv this
        )
      ),
      have x ∈ FV ((↑(y ≡ value.true) ⋀ Q) t), from (free_in_propctx.exis.inv x_free_in_Qt).right,
      have x ∈ FV (propctx.term (y ≡ value.true) t) ∨ x ∈ FV (Q t), from free_in_propctx.and.inv this,
      or.elim this (
        assume : x ∈ FV (propctx.term (y ≡ value.true) t),
        have x ∈ FV (((y ≡ value.true).to_termctx) t), from free_in_propctx.term.inv this,
        have x ∈ FV (y ≡ value.true), from free_in_termctx.term.inv this,
        show x ∈ FV t ∨ x ∈ FV P, from absurd this x_not_in_yv
      ) (
        assume : x ∈ FV (Q t),
        have x ∈ FV t ∨ x ∈ FV (P ⋀ (y ≡ value.true)), from ih t this,
        or.elim this (
          assume : x ∈ FV t,
          show x ∈ FV t ∨ x ∈ FV P, from or.inl this
        ) (
          assume : x ∈ FV (P ⋀ (y ≡ value.true)),
          or.elim (free_in_prop.and.inv this) (
            assume : x ∈ FV P,
            show x ∈ FV t ∨ x ∈ FV P, from or.inr this
          ) (
            assume : x ∈ FV (prop.term (y ≡ value.true)),
            have x ∈ FV (y ≡ value.true), from free_in_prop.term.inv this,
            show x ∈ FV t ∨ x ∈ FV P, from absurd this x_not_in_yv
          )
        )
      )
    },
    case exp.dvcgen.fals P y e' Q y_not_in_P e'_verified ih { from
      assume t: term,
      assume x_free_in_Qt: x ∈ FV ((propctx.exis y ((y ≡ value.false) ⋀ Q)) t),
      have x_neq_y: x ≠ y, from (free_in_propctx.exis.inv x_free_in_Qt).left,
      have x_not_in_yv: x ∉ FV (y ≡ value.false), from (
        assume : x ∈ FV (y ≡ value.false),
        have free_in_term x y ∨ free_in_term x value.false, from free_in_term.binop.inv this,
        or.elim this (
          assume : free_in_term x y,
          have x = y, from free_in_term.var.inv this,
          show «false», from x_neq_y this
        ) (
          assume : free_in_term x value.false,
          show «false», from free_in_term.value.inv this
        )
      ),
      have x ∈ FV ((↑(y ≡ value.false) ⋀ Q) t), from (free_in_propctx.exis.inv x_free_in_Qt).right,
      have x ∈ FV (propctx.term (y ≡ value.false) t) ∨ x ∈ FV (Q t), from free_in_propctx.and.inv this,
      or.elim this (
        assume : x ∈ FV (propctx.term (y ≡ value.false) t),
        have x ∈ FV (((y ≡ value.false).to_termctx) t), from free_in_propctx.term.inv this,
        have x ∈ FV (y ≡ value.false), from free_in_termctx.term.inv this,
        show x ∈ FV t ∨ x ∈ FV P, from absurd this x_not_in_yv
      ) (
        assume : x ∈ FV (Q t),
        have x ∈ FV t ∨ x ∈ FV (P ⋀ (y ≡ value.false)), from ih t this,
        or.elim this (
          assume : x ∈ FV t,
          show x ∈ FV t ∨ x ∈ FV P, from or.inl this
        ) (
          assume : x ∈ FV (P ⋀ (y ≡ value.false)),
          or.elim (free_in_prop.and.inv this) (
            assume : x ∈ FV P,
            show x ∈ FV t ∨ x ∈ FV P, from or.inr this
          ) (
            assume : x ∈ FV (prop.term (y ≡ value.false)),
            have x ∈ FV (y ≡ value.false), from free_in_prop.term.inv this,
            show x ∈ FV t ∨ x ∈ FV P, from absurd this x_not_in_yv
          )
        )
      )
    },
    case exp.dvcgen.num P y n e' Q y_not_in_P e'_verified ih { from
      assume t: term,
      assume x_free_in_Qt: x ∈ FV ((propctx.exis y ((y ≡ value.num n) ⋀ Q)) t),
      have x_neq_y: x ≠ y, from (free_in_propctx.exis.inv x_free_in_Qt).left,
      have x_not_in_yv: x ∉ FV (y ≡ value.num n), from (
        assume : x ∈ FV (y ≡ value.num n),
        have free_in_term x y ∨ free_in_term x (value.num n), from free_in_term.binop.inv this,
        or.elim this (
          assume : free_in_term x y,
          have x = y, from free_in_term.var.inv this,
          show «false», from x_neq_y this
        ) (
          assume : free_in_term x (value.num n),
          show «false», from free_in_term.value.inv this
        )
      ),
      have x ∈ FV ((↑(y ≡ value.num n) ⋀ Q) t), from (free_in_propctx.exis.inv x_free_in_Qt).right,
      have x ∈ FV (propctx.term (y ≡ value.num n) t) ∨ x ∈ FV (Q t), from free_in_propctx.and.inv this,
      or.elim this (
        assume : x ∈ FV (propctx.term (y ≡ value.num n) t),
        have x ∈ FV (((y ≡ value.num n).to_termctx) t), from free_in_propctx.term.inv this,
        have x ∈ FV (y ≡ value.num n), from free_in_termctx.term.inv this,
        show x ∈ FV t ∨ x ∈ FV P, from absurd this x_not_in_yv
      ) (
        assume : x ∈ FV (Q t),
        have x ∈ FV t ∨ x ∈ FV (P ⋀ (y ≡ value.num n)), from ih t this,
        or.elim this (
          assume : x ∈ FV t,
          show x ∈ FV t ∨ x ∈ FV P, from or.inl this
        ) (
          assume : x ∈ FV (P ⋀ (y ≡ value.num n)),
          or.elim (free_in_prop.and.inv this) (
            assume : x ∈ FV P,
            show x ∈ FV t ∨ x ∈ FV P, from or.inr this
          ) (
            assume : x ∈ FV (prop.term (y ≡ value.num n)),
            have x ∈ FV (y ≡ value.num n), from free_in_prop.term.inv this,
            show x ∈ FV t ∨ x ∈ FV P, from absurd this x_not_in_yv
          )
        )
      )
    },
    case exp.dvcgen.func P f fx R S e₁ e₂ Q₁ Q₂ f_not_in_P _ _ _ fv_R fv_S _ _ func_vc ih₁ ih₂ { from
      assume t: term,
      assume x_free_in_Qt: x ∈ FV ((propctx.exis f ((prop.func f fx R (Q₁ (term.app f fx) ⋀ S)) ⋀ Q₂)) t),
      have x_neq_f: x ≠ f, from (free_in_propctx.exis.inv x_free_in_Qt).left,
      have x_not_in_non_rec_func: x ∈ FV (prop.func f fx R S) → x ∈ FV P, from (
        assume : x ∈ FV (prop.func f fx R S),
        have x ∈ FV (term.var f) ∨ (x ≠ fx ∧ (x ∈ FV R.to_prop ∨ x ∈ FV S.to_prop)),
        from free_in_prop.func.inv this,
        or.elim this (
          assume : x ∈ FV (term.var f),
          have x = f, from free_in_term.var.inv this,
          show x ∈ FV P, from absurd this x_neq_f
        ) (
          assume : x ≠ fx ∧ (x ∈ FV R.to_prop ∨ x ∈ FV S.to_prop),
          have x_neq_fx: x ≠ fx, from this.left,
          or.elim this.right (
            assume : x ∈ FV R.to_prop,
            have x ∈ FV P ∪ {f, fx}, from set.mem_of_mem_of_subset this fv_R,
            have x ∈ FV P ∨ x ∈ {f, fx}, from set.mem_or_mem_of_mem_union this,
            or.elim this id (
              assume : x ∈ {f, fx},
              have (x = f) ∨ (x = fx), from set.two_elems_mem this,
              or.elim this (
                assume : x = f,
                show x ∈ FV P, from absurd this x_neq_f
              ) (
                assume : x = fx,
                show x ∈ FV P, from absurd this x_neq_fx
              )
            )
          ) (
            assume : x ∈ FV S.to_prop,
            have x ∈ FV P ∪ {f, fx}, from set.mem_of_mem_of_subset this fv_S,
            have x ∈ FV P ∨ x ∈ {f, fx}, from set.mem_or_mem_of_mem_union this,
            or.elim this id (
              assume : x ∈ {f, fx},
              have (x = f) ∨ (x = fx), from set.two_elems_mem this,
              or.elim this (
                assume : x = f,
                show x ∈ FV P, from absurd this x_neq_f
              ) (
                assume : x = fx,
                show x ∈ FV P, from absurd this x_neq_fx
              )
            )
          )
        )
      ),
      have x_not_in_func: x ∈ FV (prop.func f fx R (Q₁ (term.app f fx) ⋀ S)) → x ∈ FV P, from (
        assume : x ∈ FV (prop.func f fx R (Q₁ (term.app f fx) ⋀ S)),
        have x ∈ FV (term.var f) ∨ (x ≠ fx ∧ (x ∈ FV R.to_prop ∨ x ∈ FV (Q₁ (term.app f fx) ⋀ S))),
        from free_in_prop.func.inv this,
        or.elim this (
          assume : x ∈ FV (term.var f),
          have x = f, from free_in_term.var.inv this,
          show x ∈ FV P, from absurd this x_neq_f
        ) (
          assume : x ≠ fx ∧ (x ∈ FV R.to_prop ∨ x ∈ FV (Q₁ (term.app f fx) ⋀ S)),
          have x_neq_fx: x ≠ fx, from this.left,
          have x_not_in_R: x ∈ FV R.to_prop → x ∈ FV P, from (
            assume : x ∈ FV R.to_prop,
            have x ∈ FV P ∪ {f, fx}, from set.mem_of_mem_of_subset this fv_R,
            have x ∈ FV P ∨ x ∈ {f, fx}, from set.mem_or_mem_of_mem_union this,
            or.elim this id (
              assume : x ∈ {f, fx},
              have (x = f) ∨ (x = fx), from set.two_elems_mem this,
              or.elim this (
                assume : x = f,
                show x ∈ FV P, from absurd this x_neq_f
              ) (
                assume : x = fx,
                show x ∈ FV P, from absurd this x_neq_fx
              )
            )
          ),
          have x_not_in_S: x ∈ FV S.to_prop → x ∈ FV P, from (
            assume : x ∈ FV S.to_prop,
            have x ∈ FV P ∪ {f, fx}, from set.mem_of_mem_of_subset this fv_S,
            have x ∈ FV P ∨ x ∈ {f, fx}, from set.mem_or_mem_of_mem_union this,
            or.elim this id (
              assume : x ∈ {f, fx},
              have (x = f) ∨ (x = fx), from set.two_elems_mem this,
              or.elim this (
                assume : x = f,
                show x ∈ FV P, from absurd this x_neq_f
              ) (
                assume : x = fx,
                show x ∈ FV P, from absurd this x_neq_fx
              )
            )
          ),
          or.elim this.right x_not_in_R (
            assume : x ∈ FV (Q₁ (term.app f fx) ⋀ S),
            or.elim (free_in_prop.and.inv this) (
              assume : x ∈ FV (Q₁ (term.app f fx)),
              have x ∈ FV (term.app f fx) ∨ x ∈ FV (P ⋀ (spec.func f fx R S) ⋀ R), from ih₁ (term.app f fx) this,
              or.elim this (
                assume : x ∈ FV (term.app f fx),
                have free_in_term x f ∨ free_in_term x fx, from free_in_term.app.inv this,
                or.elim this (
                  assume : free_in_term x f,
                  have x = f, from free_in_term.var.inv this,
                  show x ∈ FV P, from absurd this x_neq_f
                ) (
                  assume : free_in_term x fx,
                  have x = fx, from free_in_term.var.inv this,
                  show x ∈ FV P, from absurd this x_neq_fx
                )
              ) (
                assume : x ∈ FV (P ⋀ (spec.func f fx R S) ⋀ R),
                or.elim (free_in_prop.and.inv this) id (
                  assume : free_in_prop x (spec.func f fx R S ⋀ R),
                  have h: free_in_prop x ((spec.func f fx R S).to_prop ⋀ R.to_prop), from this,
                  have spec.to_prop (spec.func f fx R S) = prop.func f fx R.to_prop S.to_prop, by unfold spec.to_prop,
                  have free_in_prop x (prop.func f fx R S ⋀ R.to_prop), from this ▸ h,
                  or.elim (free_in_prop.and.inv this).symm x_not_in_R (
                    assume : x ∈ FV (prop.func f fx R S),
                    show x ∈ FV P, from x_not_in_non_rec_func this
                  )
                )
              )
            ) (
              assume : x ∈ FV S.to_prop,
              have x ∈ FV P ∪ {f, fx}, from set.mem_of_mem_of_subset this fv_S,
              have x ∈ FV P ∨ x ∈ {f, fx}, from set.mem_or_mem_of_mem_union this,
              or.elim this id (
                assume : x ∈ {f, fx},
                have (x = f) ∨ (x = fx), from set.two_elems_mem this,
                or.elim this (
                  assume : x = f,
                  show x ∈ FV P, from absurd this x_neq_f
                ) (
                  assume : x = fx,
                  show x ∈ FV P, from absurd this x_neq_fx
                )
              )
            )
          )
        )
      ),
      have x ∈ FV ((propctx.and (prop.func f fx R (Q₁ (term.app f fx) ⋀ S)) Q₂) t),
      from (free_in_propctx.exis.inv x_free_in_Qt).right,
      have x ∈ FV ((prop.func f fx R (Q₁ (term.app f fx) ⋀ S)) t) ∨ x ∈ FV (Q₂ t),
      from free_in_propctx.and.inv this,
      or.elim this (
        assume : x ∈ FV ((prop.func f fx R (Q₁ (term.app f fx) ⋀ S)) t),
        have x ∈ FV (prop.func f fx R (Q₁ (term.app f fx) ⋀ S)), from free_in_propctx.prop.inv this,
        show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_func this)
      ) (
        assume : x ∈ FV (Q₂ t),
        have x ∈ FV t ∨ x ∈ FV (P ⋀ prop.func f fx R (Q₁ (term.app f fx) ⋀ S)), from ih₂ t this,
        or.elim this (
          assume : x ∈ FV t,
          show x ∈ FV t ∨ x ∈ FV P, from or.inl this
        ) (
          assume : x ∈ FV (P ⋀ prop.func f fx R (Q₁ (term.app f fx) ⋀ S)),
          or.elim (free_in_prop.and.inv this) (
            assume : x ∈ FV P,
            show x ∈ FV t ∨ x ∈ FV P, from or.inr this
          ) (
            assume : x ∈ FV (prop.func f fx R (Q₁ (term.app f fx) ⋀ S)),
            show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_func this)
          )
        )
      )
    },
    case exp.dvcgen.unop op P e' x₁ y Q x_free_in_P y_not_in_P e'_verified vc_valid ih { from
      assume t: term,
      assume x_free_in_Qt: x ∈ FV ((propctx.exis y ((y ≡ term.unop op x₁) ⋀ Q)) t),
      have x_neq_y: x ≠ y, from (free_in_propctx.exis.inv x_free_in_Qt).left,
      have x_not_in_unop: x ∈ FV (y ≡ term.unop op x₁) → x ∈ FV P, from (
        assume : x ∈ FV (y ≡ term.unop op x₁),
        have free_in_term x y ∨ free_in_term x (term.unop op x₁), from free_in_term.binop.inv this,
        or.elim this (
          assume : free_in_term x y,
          have x = y, from free_in_term.var.inv this,
          show x ∈ FV P, from absurd this x_neq_y
        ) (
          assume : free_in_term x (term.unop op x₁),
          have free_in_term x x₁, from free_in_term.unop.inv this,
          have x = x₁, from free_in_term.var.inv this,
          show x ∈ FV P, from this.symm ▸ x_free_in_P
        )
      ),
      have x ∈ FV ((↑(y ≡ term.unop op x₁) ⋀ Q) t), from (free_in_propctx.exis.inv x_free_in_Qt).right,
      have x ∈ FV (propctx.term (y ≡ term.unop op x₁) t) ∨ x ∈ FV (Q t), from free_in_propctx.and.inv this,
      or.elim this (
        assume : x ∈ FV (propctx.term (y ≡ term.unop op x₁) t),
        have x ∈ FV (((y ≡ term.unop op x₁).to_termctx) t), from free_in_propctx.term.inv this,
        have x ∈ FV (y ≡ term.unop op x₁), from free_in_termctx.term.inv this,
        show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_unop this)
      ) (
        assume : x ∈ FV (Q t),
        have x ∈ FV t ∨ x ∈ FV (P ⋀ (y ≡ term.unop op x₁)), from ih t this,
        or.elim this (
          assume : x ∈ FV t,
          show x ∈ FV t ∨ x ∈ FV P, from or.inl this
        ) (
          assume : x ∈ FV (P ⋀ (y ≡ term.unop op x₁)),
          or.elim (free_in_prop.and.inv this) (
            assume : x ∈ FV P,
            show x ∈ FV t ∨ x ∈ FV P, from or.inr this
          ) (
            assume : x ∈ FV (prop.term (y ≡ term.unop op x₁)),
            have x ∈ FV (y ≡ term.unop op x₁), from free_in_prop.term.inv this,
            show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_unop this)
          )
        )
      )
    },
    case exp.dvcgen.binop op P e' x₁ x₂ y Q x₁_free_in_P x₂_free_in_P y_not_in_P e'_verified vc_valid ih { from
      assume t: term,
      assume x_free_in_Qt: x ∈ FV ((propctx.exis y ((y ≡ term.binop op x₁ x₂) ⋀ Q)) t),
      have x_neq_y: x ≠ y, from (free_in_propctx.exis.inv x_free_in_Qt).left,
      have x_not_in_binop: x ∈ FV (y ≡ term.binop op x₁ x₂) → x ∈ FV P, from (
        assume : x ∈ FV (y ≡ term.binop op x₁ x₂),
        have free_in_term x y ∨ free_in_term x (term.binop op x₁ x₂), from free_in_term.binop.inv this,
        or.elim this (
          assume : free_in_term x y,
          have x = y, from free_in_term.var.inv this,
          show x ∈ FV P, from absurd this x_neq_y
        ) (
          assume : free_in_term x (term.binop op x₁ x₂),
          have free_in_term x x₁ ∨ free_in_term x x₂, from free_in_term.binop.inv this,
          or.elim this (
            assume : free_in_term x x₁,
            have x = x₁, from free_in_term.var.inv this,
            show x ∈ FV P, from this.symm ▸ x₁_free_in_P
          ) (
            assume : free_in_term x x₂,
            have x = x₂, from free_in_term.var.inv this,
            show x ∈ FV P, from this.symm ▸ x₂_free_in_P
          )
        )
      ),
      have x ∈ FV ((↑(y ≡ term.binop op x₁ x₂) ⋀ Q) t), from (free_in_propctx.exis.inv x_free_in_Qt).right,
      have x ∈ FV (propctx.term (y ≡ term.binop op x₁ x₂) t) ∨ x ∈ FV (Q t), from free_in_propctx.and.inv this,
      or.elim this (
        assume : x ∈ FV (propctx.term (y ≡ term.binop op x₁ x₂) t),
        have x ∈ FV (((y ≡ term.binop op x₁ x₂).to_termctx) t), from free_in_propctx.term.inv this,
        have x ∈ FV (y ≡ term.binop op x₁ x₂), from free_in_termctx.term.inv this,
        show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_binop this)
      ) (
        assume : x ∈ FV (Q t),
        have x ∈ FV t ∨ x ∈ FV (P ⋀ (y ≡ term.binop op x₁ x₂)), from ih t this,
        or.elim this (
          assume : x ∈ FV t,
          show x ∈ FV t ∨ x ∈ FV P, from or.inl this
        ) (
          assume : x ∈ FV (P ⋀ (y ≡ term.binop op x₁ x₂)),
          or.elim (free_in_prop.and.inv this) (
            assume : x ∈ FV P,
            show x ∈ FV t ∨ x ∈ FV P, from or.inr this
          ) (
            assume : x ∈ FV (prop.term (y ≡ term.binop op x₁ x₂)),
            have x ∈ FV (y ≡ term.binop op x₁ x₂), from free_in_prop.term.inv this,
            show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_binop this)
          )
        )
      )
    },
    case exp.dvcgen.app P y f e' x₁ Q f_free_in_P x₁_free_in_P y_not_in_P e'_verified vc_valid ih { from
      assume t: term,
      assume x_free_in_Qt: x ∈ FV ((propctx.exis y ((prop.call x₁) ⋀
                                                    (prop.post f x₁) ⋀
                                                    (y ≡ term.app f x₁) ⋀
                                                     Q)) t),
      have x_neq_y: x ≠ y, from (free_in_propctx.exis.inv x_free_in_Qt).left,
      have x_not_in_call: x ∈ FV (prop.call x₁) → x ∈ FV P, from (
        assume : x ∈ FV (prop.call x₁),
        have free_in_term x x₁, from free_in_prop.call.inv this,
        have x = x₁, from free_in_term.var.inv this,
        show x ∈ FV P, from this.symm ▸ x₁_free_in_P
      ),
      have x_not_in_post: x ∈ FV (prop.post f x₁) → x ∈ FV P, from (
        assume : x ∈ FV (prop.post f x₁),
        or.elim (free_in_prop.post.inv this) (
          assume : free_in_term x f,
          have x = f, from free_in_term.var.inv this,
          show x ∈ FV P, from this.symm ▸ f_free_in_P
        ) (
          assume : free_in_term x x₁,
          have x = x₁, from free_in_term.var.inv this,
          show x ∈ FV P, from this.symm ▸ x₁_free_in_P
        )
      ),
      have x_not_in_app: x ∈ FV (y ≡ term.app f x₁) → x ∈ FV P, from (
        assume : x ∈ FV (y ≡ term.app f x₁),
        have free_in_term x y ∨ free_in_term x (term.app f x₁), from free_in_term.binop.inv this,
        or.elim this (
          assume : free_in_term x y,
          have x = y, from free_in_term.var.inv this,
          show x ∈ FV P, from absurd this x_neq_y
        ) (
          assume : free_in_term x (term.app f x₁),
          have free_in_term x f ∨ free_in_term x x₁, from free_in_term.app.inv this,
          or.elim this (
            assume : free_in_term x f,
            have x = f, from free_in_term.var.inv this,
            show x ∈ FV P, from this.symm ▸ f_free_in_P
          ) (
            assume : free_in_term x x₁,
            have x = x₁, from free_in_term.var.inv this,
            show x ∈ FV P, from this.symm ▸ x₁_free_in_P
          )
        )
      ),
      have x ∈ FV ((↑(prop.call ↑x₁) ⋀ ↑(prop.post ↑f ↑x₁) ⋀ ↑(↑y ≡ term.app ↑f ↑x₁) ⋀ Q) t),
      from (free_in_propctx.exis.inv x_free_in_Qt).right,
      have x ∈ FV (((prop.call x₁):propctx) t) ∨ x ∈ FV ((↑(prop.post f x₁) ⋀ ↑(y ≡ term.app f x₁) ⋀ Q) t),
      from free_in_propctx.and.inv this,
      or.elim this (
        assume : x ∈ FV (((prop.call x₁):propctx) t),
        have x ∈ FV (prop.call x₁), from free_in_propctx.prop.inv this,
        show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_call this)
      ) (
        assume : x ∈ FV ((↑(prop.post f x₁) ⋀ ↑(y ≡ term.app f x₁) ⋀ Q) t),
        have x ∈ FV (((prop.post f x₁):propctx) t) ∨ x ∈ FV ((↑(y ≡ term.app f x₁) ⋀ Q) t),
        from free_in_propctx.and.inv this,
        or.elim this (
          assume : x ∈ FV (((prop.post f x₁):propctx) t),
          have x ∈ FV (prop.post f x₁), from free_in_propctx.prop.inv this,
          show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_post this)
        ) (
          assume : x ∈ FV ((↑(y ≡ term.app f x₁) ⋀ Q) t),
          have x ∈ FV ((↑(y ≡ term.app f x₁):propctx) t) ∨ x ∈ FV (Q t),
          from free_in_propctx.and.inv this,
          or.elim this (
            assume : x ∈ FV (((y ≡ term.app f x₁):propctx) t),
            have x ∈ FV ((y ≡ term.app f x₁):prop), from free_in_propctx.prop.inv this,
            have x ∈ FV (y ≡ term.app f x₁), from free_in_prop.term.inv this,
            show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_app this)
          ) (
            assume : x ∈ FV (Q t),
            have x ∈ FV t ∨ x ∈ FV (P ⋀ prop.call x₁ ⋀ prop.post f x₁ ⋀ (y ≡ term.app f x₁)),
            from ih t this,
            or.elim this (
              assume : x ∈ FV t,
              show x ∈ FV t ∨ x ∈ FV P, from or.inl this
            ) (
              assume : x ∈ FV (P ⋀ prop.call x₁ ⋀ prop.post f x₁ ⋀ (y ≡ term.app f x₁)),
              or.elim (free_in_prop.and.inv this) (
                assume : x ∈ FV P,
                show x ∈ FV t ∨ x ∈ FV P, from or.inr this
              ) (
                assume : x ∈ FV (prop.call x₁ ⋀ prop.post f x₁ ⋀ (y ≡ term.app f x₁)),
                or.elim (free_in_prop.and.inv this) (
                  assume : x ∈ FV (prop.call x₁),
                  show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_call this)
                ) (
                  assume : x ∈ FV (prop.post f x₁ ⋀ (y ≡ term.app f x₁)),
                  or.elim (free_in_prop.and.inv this) (
                    assume : x ∈ FV (prop.post f x₁),
                    show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_post this)
                  ) (
                    assume : free_in_prop x (y ≡ term.app f x₁),
                    have x ∈ FV (y ≡ term.app f x₁), from free_in_prop.term.inv this,
                    show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_app this)
                  )
                )
              )
            )
          )
        )
      )
    },
    case exp.dvcgen.ite P e₁ e₂ y Q₁ Q₂ y_free_in_P _ _ vc_valid ih₁ ih₂ { from
      assume t: term,
      assume x_free_in_Qt: x ∈ FV ((propctx.implies y Q₁ ⋀ propctx.implies (prop.not y) Q₂) t),
      have x_not_in_y: free_in_prop x y → x ∈ FV P, from (
        assume : free_in_prop x y,
        have free_in_term x y, from free_in_prop.term.inv this,
        have x = y, from free_in_term.var.inv this,
        show x ∈ FV P, from this.symm ▸ y_free_in_P
      ),
      have x_not_in_yn: free_in_prop x (prop.not y) → x ∈ FV P, from (
        assume : free_in_prop x (prop.not y),
        have free_in_prop x y, from free_in_prop.not.inv this,
        have free_in_term x y, from free_in_prop.term.inv this,
        have x = y, from free_in_term.var.inv this,
        show x ∈ FV P, from this.symm ▸ y_free_in_P
      ),
      or.elim (free_in_propctx.and.inv x_free_in_Qt) (
        assume : x ∈ FV ((propctx.implies y Q₁) t),
        or.elim (free_in_propctx.implies.inv this) (
          assume : x ∈ FV ((prop.term y).to_propctx t),
          have x ∈ FV (prop.term y), from free_in_propctx.prop.inv this,
          show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_y this)
        ) (
          assume : x ∈ FV (Q₁ t),
          have x ∈ FV t ∨ x ∈ FV (P ⋀ y), from ih₁ t this,
          or.elim this (
            assume : x ∈ FV t,
            show x ∈ FV t ∨ x ∈ FV P, from or.inl this
          ) (
            assume : x ∈ FV (P ⋀ y),
            or.elim (free_in_prop.and.inv this) (
              assume : x ∈ FV P,
              show x ∈ FV t ∨ x ∈ FV P, from or.inr this
            ) (
              assume : free_in_prop x y,
              have x ∈ FV P, from x_not_in_y this,
              show x ∈ FV t ∨ x ∈ FV P, from or.inr this
            )
          )
        )
      ) (
        assume : x ∈ FV ((propctx.implies (prop.not y) Q₂) t),
        or.elim (free_in_propctx.implies.inv this) (
          assume : x ∈ FV ((prop.not y).to_propctx t),
          have x ∈ FV (prop.not y), from free_in_propctx.prop.inv this,
          show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_yn this)
        ) (
          assume : x ∈ FV (Q₂ t),
          have x ∈ FV t ∨ x ∈ FV (P ⋀ (prop.not y)), from ih₂ t this,
          or.elim this (
            assume : x ∈ FV t,
            show x ∈ FV t ∨ x ∈ FV P, from or.inl this
          ) (
            assume : x ∈ FV (P ⋀ (prop.not y)),
            or.elim (free_in_prop.and.inv this) (
              assume : x ∈ FV P,
              show x ∈ FV t ∨ x ∈ FV P, from or.inr this
            ) (
              assume : free_in_prop x (prop.not y),
              have x ∈ FV P, from x_not_in_yn this,
              show x ∈ FV t ∨ x ∈ FV P, from or.inr this
            )
          )
        )
      )
    },
    case exp.dvcgen.return P y y_free_in_P { from
      assume t: term,
      assume : x ∈ FV ((propctx.term (y ≣ •)) t),
      have x ∈ FV ((y ≣ •) t), from free_in_propctx.term.inv this,
      or.elim (free_in_termctx.binop.inv this) (
        assume : x ∈ FV ((y:termctx) t),
        have free_in_term x y, from free_in_termctx.term.inv this,
        have x = y, from free_in_term.var.inv this,
        have x ∈ FV P, from this.symm ▸ y_free_in_P,
        show x ∈ FV t ∨ x ∈ FV P, from or.inr this
      ) (
        assume : x ∈ FV (• t),
        have x ∈ FV t, from free_in_termctx.hole.inv this,
        show x ∈ FV t ∨ x ∈ FV P, from or.inl this
      )
    }
  end

lemma contains_of_free {P: prop} {σ: env} {x: var}: (⊩ σ : P) → free_in_prop x P → x ∈ σ :=
  assume env_verified: ⊩ σ : P,
  assume x_free_in_P: free_in_prop x P,
  show x ∈ σ, by begin
    induction env_verified,
    case env.dvcgen.empty { from
      have free_in_term x value.true, from free_in_prop.term.inv x_free_in_P,
      show x ∈ env.empty, from absurd this free_in_term.value.inv
    },
    case env.dvcgen.tru σ' y Q _ _ ih {
      show x ∈ (σ'[y↦value.true]), from contains_of_free_eq_value x_free_in_P ih
    },
    case env.dvcgen.fls σ' y Q _ _ ih { from
      show x ∈ (σ'[y↦value.false]), from contains_of_free_eq_value x_free_in_P ih
    },
    case env.dvcgen.num n σ' y Q _ _ ih { from
      show x ∈ (σ'[y↦value.num n]), from contains_of_free_eq_value x_free_in_P ih
    },
    case env.dvcgen.func f σ₂ σ₁ g gx R S e Q₁ Q₂ Q₃ _ _ _ _ _ _ _ fv_R fv_S e_verified _ ih₁ ih₂ { from
      contains_of_free_in_nonempty_env (
        assume : f ≠ x,
        have x_neq_f: x ≠ f, from this.symm,
        let vf := value.func g gx R S e σ₂ in
        have free_in_prop x Q₁
           ∨ free_in_prop x ((f ≡ vf) ⋀ prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
        from free_in_prop.and.inv x_free_in_P,
        or.elim this (
          assume x_free_in_Q₁: free_in_prop x Q₁,
          show x ∈ σ₁, from ih₁ x_free_in_Q₁
        ) (
          assume : free_in_prop x ((f ≡ vf) ⋀ prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
          or.elim (free_in_prop.and.inv this) (
            assume x_free_in_eq_v: free_in_prop x (f ≡ vf),
            show x ∈ σ₁, by begin
              cases x_free_in_eq_v,
              case free_in_prop.term x_free_in_eq {
                cases x_free_in_eq,
                case free_in_term.binop₁ free_in_f {
                  have f_is_x: (f = x), from (free_in_term.var.inv free_in_f).symm,
                  contradiction
                },
                case free_in_term.binop₂ free_in_vf {
                  cases free_in_vf
                }
              }
            end
          ) (
            assume x_free_in_sFunc: free_in_prop x (prop.subst_env (σ₂[g↦vf]) (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
            have x ≠ g ∧ free_in_prop x (prop.subst_env σ₂ (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
            from free_of_subst_env_prop x_free_in_sFunc,
            have x_neq_g: x ≠ g, from this.left,
            have x_free_in_sFunc': free_in_prop x (prop.subst_env σ₂ (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))), from this.right,
            have x_free_in_func: free_in_prop x (prop.func g gx R (Q₃ (term.app g gx) ⋀ S)),
            from free_of_subst_env x_free_in_sFunc',
            let forallp := (prop.implies R.to_prop (prop.pre g gx)
                        ⋀ prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop)) in
            have h: prop.func g gx R.to_prop (Q₃ (term.app g gx) ⋀ S.to_prop)
                = (term.unop unop.isFunc g ⋀ prop.forallc gx forallp),
            by unfold prop.func,
            have free_in_prop x (term.unop unop.isFunc g ⋀ prop.forallc gx forallp), from h ▸ x_free_in_func,
            have free_in_prop x (term.unop unop.isFunc g) ∨ free_in_prop x (prop.forallc gx forallp),
            from free_in_prop.and.inv this,
            or.elim this (
              assume : free_in_prop x (term.unop unop.isFunc g),
              have free_in_term x (term.unop unop.isFunc g), from free_in_prop.term.inv this,
              have free_in_term x g, from free_in_term.unop.inv this,
              have x = g, from free_in_term.var.inv this,
              show x ∈ σ₁, from absurd this x_neq_g
            ) (
              assume x_free_in_forallp: free_in_prop x (prop.forallc gx forallp),
              have x_neq_gx: x ≠ gx, from (free_in_prop.forallc.inv x_free_in_forallp).left,

              have x_not_in_R: x ∉ FV R.to_prop, from (
                assume : free_in_prop x R.to_prop,
                have x ∈ FV Q₂ ∪ {g, gx}, from set.mem_of_mem_of_subset this fv_R,
                have x ∈ FV Q₂ ∨ x ∈ {g, gx}, from set.mem_or_mem_of_mem_union this,
                or.elim this (
                  assume : x ∈ FV Q₂,
                  have x ∈ σ₂, from ih₂ this,
                  have ¬ free_in_prop x (prop.subst_env σ₂ (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
                  from prop.not_free_of_subst_env this,
                  show «false», from this x_free_in_sFunc'
                ) (
                  assume : x ∈ {g, gx},
                  have (x = g) ∨ (x = gx), from set.two_elems_mem this,
                  or.elim this (
                    assume : x = g,
                    show «false», from x_neq_g this
                  ) (
                    assume : x = gx,
                    show «false», from x_neq_gx this
                  )
                )
              ),

              have x_not_in_S: x ∉ FV S.to_prop, from (
                assume : free_in_prop x S.to_prop,
                have x ∈ FV Q₂ ∪ {g, gx}, from set.mem_of_mem_of_subset this fv_S,
                have x ∈ FV Q₂ ∨ x ∈ {g, gx}, from set.mem_or_mem_of_mem_union this,
                or.elim this (
                  assume : x ∈ FV Q₂,
                  have x ∈ σ₂, from ih₂ this,
                  have ¬ free_in_prop x (prop.subst_env σ₂ (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
                  from prop.not_free_of_subst_env this,
                  show «false», from this x_free_in_sFunc'
                ) (
                  assume : x ∈ {g, gx},
                  have (x = g) ∨ (x = gx), from set.two_elems_mem this,
                  or.elim this (
                    assume : x = g,
                    show «false», from x_neq_g this
                  ) (
                    assume : x = gx,
                    show «false», from x_neq_gx this
                  )
                )
              ),

              have x_not_in_gfunc: x ∉ FV (prop.func g gx R S), from (
                assume x_free_in_gfunc: x ∈ FV (prop.func g gx R S),
                let forallp' := (prop.implies R.to_prop (prop.pre g gx)
                              ⋀ prop.implies (prop.post g gx) S.to_prop) in
                have h: prop.func g gx R.to_prop S.to_prop
                    = (term.unop unop.isFunc g ⋀ prop.forallc gx forallp'),
                by unfold prop.func,
                have free_in_prop x (term.unop unop.isFunc g ⋀ prop.forallc gx forallp'), from h ▸ x_free_in_gfunc,
                have free_in_prop x (term.unop unop.isFunc g) ∨ free_in_prop x (prop.forallc gx forallp'),
                from free_in_prop.and.inv this,
                or.elim this (
                  assume : free_in_prop x (term.unop unop.isFunc g),
                  have free_in_term x (term.unop unop.isFunc g), from free_in_prop.term.inv this,
                  have free_in_term x g, from free_in_term.unop.inv this,
                  have x = g, from free_in_term.var.inv this,
                  show «false», from x_neq_g this
                ) (
                  assume x_free_in_forallp': free_in_prop x (prop.forallc gx forallp'),
                  have x_neq_gx: x ≠ gx, from (free_in_prop.forallc.inv x_free_in_forallp').left,
                  have free_in_prop x forallp', from (free_in_prop.forallc.inv x_free_in_forallp').right,
                  or.elim (free_in_prop.and.inv this) (
                    assume : free_in_prop x (prop.implies R.to_prop (prop.pre g gx)),
                    or.elim (free_in_prop.implies.inv this) x_not_in_R (
                      assume : free_in_prop x (prop.pre g gx),
                      have free_in_term x g ∨ free_in_term x gx, from free_in_prop.pre.inv this,
                      or.elim this (
                        assume : free_in_term x g,
                        have x = g, from free_in_term.var.inv this,
                        show «false», from x_neq_g this
                      ) (
                        assume : free_in_term x gx,
                        have x = gx, from free_in_term.var.inv this,
                        show «false», from x_neq_gx this
                      )
                    )
                  ) (
                    assume : free_in_prop x (prop.implies (prop.post g gx) S.to_prop),
                    or.elim (free_in_prop.implies.inv this).symm x_not_in_S (
                      assume : free_in_prop x (prop.post g gx),
                      have free_in_term x g ∨ free_in_term x gx, from free_in_prop.post.inv this,
                      or.elim this (
                        assume : free_in_term x g,
                        have x = g, from free_in_term.var.inv this,
                        show «false», from x_neq_g this
                      ) (
                        assume : free_in_term x gx,
                        have x = gx, from free_in_term.var.inv this,
                        show «false», from x_neq_gx this
                      )
                    )
                  )
                )
              ),

              have free_in_prop x forallp, from (free_in_prop.forallc.inv x_free_in_forallp).right,
              or.elim (free_in_prop.and.inv this) (
                assume : free_in_prop x (prop.implies R.to_prop (prop.pre g gx)),
                or.elim (free_in_prop.implies.inv this) (
                  assume : x ∈ FV R.to_prop,
                  show x ∈ σ₁, from absurd this x_not_in_R
                ) (
                  assume : free_in_prop x (prop.pre g gx),
                  have free_in_term x g ∨ free_in_term x gx, from free_in_prop.pre.inv this,
                  or.elim this (
                    assume : free_in_term x g,
                    have x = g, from free_in_term.var.inv this,
                    show x ∈ σ₁, from absurd this x_neq_g
                  ) (
                    assume : free_in_term x gx,
                    have x = gx, from free_in_term.var.inv this,
                    show x ∈ σ₁, from absurd this x_neq_gx
                  )
                )
              ) (
                assume : free_in_prop x (prop.implies (prop.post g gx) (Q₃ (term.app g gx) ⋀ S.to_prop)),
                or.elim (free_in_prop.implies.inv this) (
                  assume : free_in_prop x (prop.post g gx),
                  have free_in_term x g ∨ free_in_term x gx, from free_in_prop.post.inv this,
                  or.elim this (
                    assume : free_in_term x g,
                    have x = g, from free_in_term.var.inv this,
                    show x ∈ σ₁, from absurd this x_neq_g
                  ) (
                    assume : free_in_term x gx,
                    have x = gx, from free_in_term.var.inv this,
                    show x ∈ σ₁, from absurd this x_neq_gx
                  )
                ) (
                  assume : free_in_prop x (Q₃ (term.app g gx) ⋀ S.to_prop),
                  have free_in_prop x (Q₃ (term.app g gx)) ∨ free_in_prop x S.to_prop, from free_in_prop.and.inv this,
                  or.elim this.symm (
                    assume : x ∈ FV S.to_prop,
                    show x ∈ σ₁, from absurd this x_not_in_S
                  ) (
                    assume : free_in_prop x (Q₃ (term.app g gx)),
                    have x ∈ FV (term.app g gx) ∨ x ∈ FV (Q₂ ⋀ (spec.func g gx R S) ⋀ R),
                    from exp.post_free e_verified (term.app g gx) this,
                    or.elim this (
                      assume : x ∈ FV (term.app g gx),
                      or.elim (free_in_term.app.inv this) (
                        assume : free_in_term x g,
                        have x = g, from free_in_term.var.inv this,
                        show x ∈ σ₁, from absurd this x_neq_g
                      ) (
                      assume : free_in_term x gx,
                      have x = gx, from free_in_term.var.inv this,
                      show x ∈ σ₁, from absurd this x_neq_gx
                      )
                    ) (
                      assume : x ∈ FV (Q₂ ⋀ (spec.func g gx R S) ⋀ R),
                      or.elim (free_in_prop.and.inv this) (
                        assume : x ∈ FV Q₂,
                        have x ∈ σ₂, from ih₂ this,
                        have ¬ free_in_prop x (prop.subst_env σ₂ (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))),
                        from prop.not_free_of_subst_env this,
                        show x ∈ σ₁, from absurd x_free_in_sFunc' this
                      ) (

                        assume : free_in_prop x (spec.func g gx R S ⋀ R),
                        have h: free_in_prop x ((spec.func g gx R S).to_prop ⋀ R.to_prop), from this,
                        have spec.to_prop (spec.func g gx R S) = prop.func g gx R.to_prop S.to_prop,
                        by unfold spec.to_prop,
                        have free_in_prop x (prop.func g gx R S ⋀ R.to_prop), from this ▸ h,
                        or.elim (free_in_prop.and.inv this) (
                          assume : x ∈ FV (prop.func g gx R S),
                          show x ∈ σ₁, from absurd this x_not_in_gfunc
                        ) (
                          assume : x ∈ FV R.to_prop,
                          show x ∈ σ₁, from absurd this x_not_in_R
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
   }
 end

lemma prop_func_closed {P: prop} {Q: propctx} {σ: env} {f fx: var} {R S: spec} {e: exp}:
  (⊩ (σ[f↦value.func f fx R S e σ]) : (P
       ⋀ (f ≡ value.func f fx R S e σ)
       ⋀ prop.subst_env (σ[f↦value.func f fx R S e σ]) (prop.func f fx R (Q (term.app f fx) ⋀ S)))) →
  closed (prop.subst_env (σ[f↦value.func f fx R S e σ]) (prop.func f fx R (Q (term.app f fx) ⋀ S))) :=
  assume env_verified: ⊩ (σ[f↦value.func f fx R S e σ]) : (P
       ⋀ (f ≡ value.func f fx R S e σ)
       ⋀ prop.subst_env (σ[f↦value.func f fx R S e σ]) (prop.func f fx R (Q (term.app f fx) ⋀ S))),
  assume x: var,
  assume h: x ∈ FV (prop.subst_env (σ[f↦value.func f fx R S e σ]) (prop.func f fx R (Q (term.app f fx) ⋀ S))),
  have free_in_prop x (f ≡ value.func f fx R S e σ
       ⋀ prop.subst_env (σ[f↦value.func f fx R S e σ]) (prop.func f fx R (Q (term.app f fx) ⋀ S))),
  from free_in_prop.and₂ h,
  have x ∈ FV (P
       ⋀ (f ≡ value.func f fx R S e σ)
       ⋀ prop.subst_env (σ[f↦value.func f fx R S e σ]) (prop.func f fx R (Q (term.app f fx) ⋀ S))),
  from free_in_prop.and₂ this,
  have x ∈ (σ[f↦value.func f fx R S e σ]), from contains_of_free env_verified this,
  have x ∉ FV (prop.subst_env (σ[f↦value.func f fx R S e σ]) (prop.func f fx R (Q (term.app f fx) ⋀ S))),
  from prop.not_free_of_subst_env this,
  show «false», from this h

lemma free_iff_contains {P: prop} {σ: env}: (⊩ σ : P) → (σ.dom = FV P) :=
  assume σ_verified: ⊩ σ : P,
  set.eq_of_subset_of_subset (
    assume x: var,
    assume : x ∈ σ.dom,
    have x ∈ σ, from this,
    show x ∈ FV P, from free_of_contains σ_verified this
  ) (
    assume x: var,
    assume : x ∈ FV P,
    have x ∈ σ, from contains_of_free σ_verified this,
    show x ∈ σ.dom, from this
  )

lemma env_translation_closed_subst {P: prop} {σ: env}: (⊩ σ : P) → closed_subst σ P :=
  assume σ_verified: ⊩ σ : P,
  assume z: var,
  assume : z ∈ FV P,
  show z ∈ σ.dom, from (free_iff_contains σ_verified).symm ▸ this

/-

lemma env.apply_of_vcgen {σ: env} {x: var} {v: value} {P: prop}:
      (⊢ (σ[x↦v]) : P) → ((σ[x↦v]) x = v) :=
  begin
    intro h1,
    have h2: (x ∉ σ), by begin
      cases h1,
      case env.vcgen.tru P x_not_in_σ σ_verified {
        from x_not_in_σ
      },
      case env.vcgen.fls P x_not_in_σ σ_verified {
        from x_not_in_σ
      },
      case env.vcgen.num n P x_not_in_σ σ_verified {
        from x_not_in_σ
      },
      case env.vcgen.func σ₃ f fx R S e H Q₃ Q₄ Q₂ x_not_in_σ₂ f_not_in_σ₃ fx_not_in_σ₃
                          f_neq_fx σ₂_verified σ₃_verified x_free_in_R fv_R fv_S e_verified func_vc {
        from x_not_in_σ₂
      }
    end,
    from env.apply_of_contains h2
  end

lemma env.rest_verified {P: prop} {σ: env} {x: var} {v: value}:
      (⊢ (σ[x↦v]) : P) → ∃Q, ⊢ σ : Q :=
  assume σ_verified: ⊢ (σ[x↦v]) : P,
  begin
    cases σ_verified,
    case env.vcgen.tru Q _ σ_verified {
      from exists.intro Q σ_verified
    },
    case env.vcgen.fls Q _ σ_verified {
      from exists.intro Q σ_verified
    },
    case env.vcgen.num n Q _ σ_verified {
      from exists.intro Q σ_verified
    },
    case env.vcgen.func σ₂ f fx R S H e Q Q₂ Q₃ x_not_in_σ f_not_in_σ₂
         fx_not_in_σ₂ f_neq_fx σ₁_verified {
      from exists.intro Q σ₁_verified
    }
  end
-/

/-

lemma env_free_rest {P: prop} {σ: env} {x: var} {v: value}:
      (⊢ (σ[x↦v]) : P) → (∃Q, (⊢ σ : Q) ∧ FV Q ⊆ FV P) :=
  assume σ_verified: ⊢ (σ[x↦v]) : P,
  begin
    cases σ_verified,
    case env.vcgen.tru Q _ σ_verified ih { from
      have FV Q ⊆ FV (prop.and Q (x ≡ value.true)), from free_in_prop.and_left_subset,
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ FV Q_1 ⊆ FV (prop.and Q (x ≡ value.true)),
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.fls Q _ σ_verified { from
      have FV Q ⊆ FV (prop.and Q (x ≡ value.false)), from free_in_prop.and_left_subset,
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ FV Q_1 ⊆ FV (prop.and Q (x ≡ value.false)),
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.num n Q _ σ_verified { from
      have FV Q ⊆ FV (prop.and Q (x ≡ value.num n)), from free_in_prop.and_left_subset,
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ FV Q_1 ⊆ FV (prop.and Q (x ≡ value.num n)),
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.func σ₂ f fx R S H e Q Q₂ Q₃ x_not_in_σ f_not_in_σ₂
         fx_not_in_σ₂ f_neq_fx σ₁_verified σ₂_verified fx_in_R fv_R fv_S e_verified func_vc { from
      let funcp := prop.subst_env (σ₂[f↦value.func f fx R S e H σ₂])
                                  (prop.func f fx R (Q₃ (term.app f fx) ⋀ S)) in
      have FV Q ⊆ FV (prop.and Q (x ≡ value.func f fx R S e H σ₂ ⋀ funcp)), from free_in_prop.and_left_subset,
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ FV Q_1 ⊆ FV (prop.and Q (x ≡ value.func f fx R S e H σ₂ ⋀ funcp)),
      from exists.intro Q ⟨σ₁_verified, this⟩
    }
  end

-/
