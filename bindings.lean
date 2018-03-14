import data.set

import .syntax .notations .freevars .substitution .vcgen

lemma free_of_contains {P: prop} {σ: env} {x: var}: (⊢ σ : P) → x ∈ σ → x ∈ FV P :=
  assume env_verified: ⊢ σ : P,
  assume x_contained: x ∈ σ,
  show x ∈ FV P, by begin
    induction env_verified,
    case env.vcgen.empty {
      cases x_contained
    },
    case env.vcgen.tru σ' y Q _ _ ih { from
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
    case env.vcgen.fls σ' y Q _ _ ih { from
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
    case env.vcgen.num n σ' y Q _ _ ih { from
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
    case env.vcgen.func f σ₂ σ₁ g gx R S e H Q₁ Q₂ Q₃ _ _ _ _ _ _ _ fv_R fv_S e_verified _ ih₁ ih₂ { from
      or.elim (env.contains.inv x_contained) (
        assume : x = f,
        have free_in_term x f, from this ▸ free_in_term.var x,
        have free_in_term x (f ≡ value.func g gx R S e H σ₂), from free_in_term.binop₁ this,
        have free_in_prop x (f ≡ value.func g gx R S e H σ₂), from free_in_prop.term this,
        have x ∈ FV (prop.term (f ≡ value.func g gx R S e H σ₂) ⋀
                     prop.subst_env (σ₂[g↦value.func g gx R S e H σ₂])
                     (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))), from free_in_prop.and₁ this,
        show x ∈ FV (Q₁ ⋀ f ≡ value.func g gx R S e H σ₂ ⋀
                     prop.subst_env (σ₂[g↦value.func g gx R S e H σ₂])
                     (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))), from free_in_prop.and₂ this
      ) (
        assume : x ∈ σ₁,
        have x ∈ FV Q₁, from ih₁ this,
        show x ∈ FV (Q₁ ⋀ f ≡ value.func g gx R S e H σ₂ ⋀
                     prop.subst_env (σ₂[g↦value.func g gx R S e H σ₂])
                     (prop.func g gx R (Q₃ (term.app g gx) ⋀ S))), from free_in_prop.and₁ this
      )
    }
  end

lemma exp.post_free {P: prop} {e: exp} {Q: propctx} {x: var}:
       (P ⊢ e : Q) → ∀t, x ∈ FV (Q t) → x ∈ FV t ∨ x ∈ FV P :=
  assume e_verified: P ⊢ e : Q,
  begin
    induction e_verified,
    case exp.vcgen.tru P y e' Q y_not_in_P e'_verified ih { from
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
    case exp.vcgen.fals P y e' Q y_not_in_P e'_verified ih { from
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
    case exp.vcgen.num P y n e' Q y_not_in_P e'_verified ih { from
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
    case exp.vcgen.func P f fx R S e₁ e₂ Q₁ Q₂ f_not_in_P _ _ _ fv_R fv_S _ _ func_vc ih₁ ih₂ { from
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
    case exp.vcgen.unop op P e' x₁ y Q x_free_in_P y_not_in_P e'_verified vc_valid ih { from
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
    case exp.vcgen.binop op P e' x₁ x₂ y Q x₁_free_in_P x₂_free_in_P y_not_in_P e'_verified vc_valid ih { from
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
    case exp.vcgen.app P y f e' x₁ Q f_free_in_P x₁_free_in_P y_not_in_P e'_verified vc_valid ih { from
      assume t: term,
      assume x_free_in_Qt: x ∈ FV ((propctx.exis y ((prop.call f x₁) ⋀
                                                    (prop.post f x₁) ⋀
                                                    (y ≡ term.app f x₁) ⋀
                                                     Q)) t),
      have x_neq_y: x ≠ y, from (free_in_propctx.exis.inv x_free_in_Qt).left,
      have x_not_in_call: x ∈ FV (prop.call f x₁) → x ∈ FV P, from (
        assume : x ∈ FV (prop.call f x₁),
        or.elim (free_in_prop.call.inv this) (
          assume : free_in_term x f,
          have x = f, from free_in_term.var.inv this,
          show x ∈ FV P, from this.symm ▸ f_free_in_P
        ) (
          assume : free_in_term x x₁,
          have x = x₁, from free_in_term.var.inv this,
          show x ∈ FV P, from this.symm ▸ x₁_free_in_P
        )
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
      have x ∈ FV ((↑(prop.call ↑f ↑x₁) ⋀ ↑(prop.post ↑f ↑x₁) ⋀ ↑(↑y ≡ term.app ↑f ↑x₁) ⋀ Q) t),
      from (free_in_propctx.exis.inv x_free_in_Qt).right,
      have x ∈ FV (((prop.call f x₁):propctx) t) ∨ x ∈ FV ((↑(prop.post f x₁) ⋀ ↑(y ≡ term.app f x₁) ⋀ Q) t),
      from free_in_propctx.and.inv this,
      or.elim this (
        assume : x ∈ FV (((prop.call f x₁):propctx) t),
        have x ∈ FV (prop.call f x₁), from free_in_propctx.prop.inv this,
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
            have x ∈ FV t ∨ x ∈ FV (P ⋀ prop.call f x₁ ⋀ prop.post f x₁ ⋀ (y ≡ term.app f x₁)),
            from ih t this,
            or.elim this (
              assume : x ∈ FV t,
              show x ∈ FV t ∨ x ∈ FV P, from or.inl this
            ) (
              assume : x ∈ FV (P ⋀ prop.call f x₁ ⋀ prop.post f x₁ ⋀ (y ≡ term.app f x₁)),
              or.elim (free_in_prop.and.inv this) (
                assume : x ∈ FV P,
                show x ∈ FV t ∨ x ∈ FV P, from or.inr this
              ) (
                assume : x ∈ FV (prop.call f x₁ ⋀ prop.post f x₁ ⋀ (y ≡ term.app f x₁)),
                or.elim (free_in_prop.and.inv this) (
                  assume : x ∈ FV (prop.call f x₁),
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
    case exp.vcgen.ite P e₁ e₂ y Q₁ Q₂ y_free_in_P _ _ vc_valid ih₁ ih₂ { from
      assume t: term,
      assume x_free_in_Qt: x ∈ FV ((propctx.implies y Q₁ ⋀ propctx.implies (term.unop unop.not y) Q₂) t),
      have x_not_in_y: free_in_prop x y → x ∈ FV P, from (
        assume : free_in_prop x y,
        have free_in_term x y, from free_in_prop.term.inv this,
        have x = y, from free_in_term.var.inv this,
        show x ∈ FV P, from this.symm ▸ y_free_in_P
      ),
      have x_not_in_yn: free_in_prop x (term.unop unop.not y) → x ∈ FV P, from (
        assume : free_in_prop x (term.unop unop.not y),
        have free_in_term x (term.unop unop.not y), from free_in_prop.term.inv this,
        have free_in_term x y, from free_in_term.unop.inv this,
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
        assume : x ∈ FV ((propctx.implies (term.unop unop.not y) Q₂) t),
        or.elim (free_in_propctx.implies.inv this) (
          assume : x ∈ FV ((prop.term (term.unop unop.not y)).to_propctx t),
          have x ∈ FV (prop.term (term.unop unop.not y)), from free_in_propctx.prop.inv this,
          show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_yn this)
        ) (
          assume : x ∈ FV (Q₂ t),
          have x ∈ FV t ∨ x ∈ FV (P ⋀ (term.unop unop.not y)), from ih₂ t this,
          or.elim this (
            assume : x ∈ FV t,
            show x ∈ FV t ∨ x ∈ FV P, from or.inl this
          ) (
            assume : x ∈ FV (P ⋀ (term.unop unop.not y)),
            or.elim (free_in_prop.and.inv this) (
              assume : x ∈ FV P,
              show x ∈ FV t ∨ x ∈ FV P, from or.inr this
            ) (
              assume : free_in_prop x (term.unop unop.not y),
              have x ∈ FV P, from x_not_in_yn this,
              show x ∈ FV t ∨ x ∈ FV P, from or.inr this
            )
          )
        )
      )
    },
    case exp.vcgen.return P y y_free_in_P { from
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

lemma contains_of_free_in_nonempty_env {σ: env} {x y: var} {v: value}:
                                  (x ≠ y → y ∈ σ) → y ∈ (σ[x↦v]) :=
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

lemma contains_of_free {P: prop} {σ: env} {x: var}: (⊢ σ : P) → free_in_prop x P → x ∈ σ :=
  assume env_verified: ⊢ σ : P,
  assume x_free_in_P: free_in_prop x P,
  show x ∈ σ, by begin
    induction env_verified,
    case env.vcgen.empty { from
      have free_in_term x value.true, from free_in_prop.term.inv x_free_in_P,
      show x ∈ env.empty, from absurd this free_in_term.value.inv
    },
    case env.vcgen.tru σ' y Q _ _ ih {
      show x ∈ (σ'[y↦value.true]), from contains_of_free_eq_value x_free_in_P ih
    },
    case env.vcgen.fls σ' y Q _ _ ih { from
      show x ∈ (σ'[y↦value.false]), from contains_of_free_eq_value x_free_in_P ih
    },
    case env.vcgen.num n σ' y Q _ _ ih { from
      show x ∈ (σ'[y↦value.num n]), from contains_of_free_eq_value x_free_in_P ih
    },
    case env.vcgen.func f σ₂ σ₁ g gx R S e H Q₁ Q₂ Q₃ _ _ _ _ _ _ _ fv_R fv_S e_verified _ ih₁ ih₂ { from
      contains_of_free_in_nonempty_env (
        assume : f ≠ x,
        have x_neq_f: x ≠ f, from this.symm,
        let vf := value.func g gx R S e H σ₂ in
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
                = (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp),
            by unfold prop.func,
            have free_in_prop x (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp), from h ▸ x_free_in_func,
            have free_in_prop x (term.unop unop.isFunc g) ∨ free_in_prop x (prop.forallc gx g forallp),
            from free_in_prop.and.inv this,
            or.elim this (
              assume : free_in_prop x (term.unop unop.isFunc g),
              have free_in_term x (term.unop unop.isFunc g), from free_in_prop.term.inv this,
              have free_in_term x g, from free_in_term.unop.inv this,
              have x = g, from free_in_term.var.inv this,
              show x ∈ σ₁, from absurd this x_neq_g
            ) (
              assume x_free_in_forallp: free_in_prop x (prop.forallc gx g forallp),
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
                    = (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp'),
                by unfold prop.func,
                have free_in_prop x (term.unop unop.isFunc g ⋀ prop.forallc gx g forallp'), from h ▸ x_free_in_gfunc,
                have free_in_prop x (term.unop unop.isFunc g) ∨ free_in_prop x (prop.forallc gx g forallp'),
                from free_in_prop.and.inv this,
                or.elim this (
                  assume : free_in_prop x (term.unop unop.isFunc g),
                  have free_in_term x (term.unop unop.isFunc g), from free_in_prop.term.inv this,
                  have free_in_term x g, from free_in_term.unop.inv this,
                  have x = g, from free_in_term.var.inv this,
                  show «false», from x_neq_g this
                ) (
                  assume x_free_in_forallp': free_in_prop x (prop.forallc gx g forallp'),
                  have x_neq_gx: x ≠ gx, from (free_in_prop.forallc.inv x_free_in_forallp').left,
                  have free_in_term x g ∨ free_in_prop x forallp', from (free_in_prop.forallc.inv x_free_in_forallp').right,
                  or.elim this (
                    assume : free_in_term x g,
                    have x = g, from free_in_term.var.inv this,
                    show «false», from x_neq_g this
                  ) (
                    assume : free_in_prop x forallp',
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
                )
              ),

              have free_in_term x g ∨ free_in_prop x forallp, from (free_in_prop.forallc.inv x_free_in_forallp).right,
              or.elim this (
                assume : free_in_term x g,
                have x = g, from free_in_term.var.inv this,
                show x ∈ σ₁, from absurd this x_neq_g
              ) (
                assume : free_in_prop x forallp,
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
                      have x ∈ FV (term.app g gx) ∨ x ∈ FV (↑H ⋀ Q₂ ⋀ (spec.func g gx R S) ⋀ R),
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
                        assume : x ∈ FV (↑H ⋀ Q₂ ⋀ (spec.func g gx R S) ⋀ R),
                        or.elim (free_in_prop.and.inv this) (
                          assume : x ∈ FV ↑H,
                          have h: x ∈ FV ↑H, from this,
                          have ↑H = calls_to_prop H, by refl,
                          have x ∈ FV (calls_to_prop H), from this ▸ h,
                          show x ∈ σ₁, from absurd this (call_history_closed H x)
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
        )
      )
   }
 end

lemma prop_func_closed {P: prop} {Q: propctx} {σ: env} {f fx: var} {R S: spec} {e: exp} {H: history}:
  (H ⋀ P ⋀ spec.func f fx R S ⋀ R ⊢ e : Q) →
  (⊢ (σ[f↦value.func f fx R S e H σ]) : (P
       ⋀ (f ≡ value.func f fx R S e H σ)
       ⋀ prop.subst_env (σ[f↦value.func f fx R S e H σ]) (prop.func f fx R (Q (term.app f fx) ⋀ S)))) →
  closed (prop.subst_env (σ[f↦value.func f fx R S e H σ]) (prop.func f fx R (Q (term.app f fx) ⋀ S))) :=
  assume e_verified: (H ⋀ P ⋀ spec.func f fx R S ⋀ R ⊢ e : Q),
  assume env_verified: ⊢ (σ[f↦value.func f fx R S e H σ]) : (P
       ⋀ (f ≡ value.func f fx R S e H σ)
       ⋀ prop.subst_env (σ[f↦value.func f fx R S e H σ]) (prop.func f fx R (Q (term.app f fx) ⋀ S))),
  assume x: var,
  assume h: x ∈ FV (prop.subst_env (σ[f↦value.func f fx R S e H σ]) (prop.func f fx R (Q (term.app f fx) ⋀ S))),
  have free_in_prop x (f ≡ value.func f fx R S e H σ
       ⋀ prop.subst_env (σ[f↦value.func f fx R S e H σ]) (prop.func f fx R (Q (term.app f fx) ⋀ S))),
  from free_in_prop.and₂ h,
  have x ∈ FV (P
       ⋀ (f ≡ value.func f fx R S e H σ)
       ⋀ prop.subst_env (σ[f↦value.func f fx R S e H σ]) (prop.func f fx R (Q (term.app f fx) ⋀ S))),
  from free_in_prop.and₂ this,
  have x ∈ (σ[f↦value.func f fx R S e H σ]), from contains_of_free env_verified this,
  have x ∉ FV (prop.subst_env (σ[f↦value.func f fx R S e H σ]) (prop.func f fx R (Q (term.app f fx) ⋀ S))),
  from prop.not_free_of_subst_env this,
  show «false», from this h

lemma free_iff_contains {P: prop} {σ: env}: (⊢ σ : P) → (σ.dom = FV P) :=
  assume σ_verified: ⊢ σ : P,
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

lemma env_translation_closed_subst {P: prop} {σ: env}: (⊢ σ : P) → closed_subst σ P :=
  assume σ_verified: ⊢ σ : P,
  assume z: var,
  assume : z ∈ FV P,
  show z ∈ σ.dom, from (free_iff_contains σ_verified).symm ▸ this

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

lemma env.dom.two_elems {σ: env} {x y: var} {v₁ v₂: value}:
      (σ[x↦v₁][y↦v₂]).dom = σ.dom ∪ {x, y} :=
  by calc (σ[x↦v₁][y↦v₂]).dom = (σ[x↦v₁]).dom ∪ set.insert y ∅ : env.dom.inv
                           ... = σ.dom ∪ set.insert x ∅ ∪ set.insert y ∅ : by rw[env.dom.inv]
                           ... = σ.dom ∪ (set.insert x ∅ ∪ set.insert y ∅) : by rw[set.union_assoc]
                           ... = σ.dom ∪ {x, y} : by rw[set.two_elems_of_insert]

lemma env.apply_of_contains {σ: env} {x: var} {v: value}:
      x ∉ σ → ((σ[x↦v]) x = v) :=
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

lemma env_dominates_p_rest {P: prop} {σ: env} {x: var} {v: value}:
      (⊢ (σ[x↦v]) : P) → (∃Q, (⊢ σ : Q) ∧ ∀σ', dominates_p σ' P Q) :=
  assume σ_verified: ⊢ (σ[x↦v]) : P,
  begin
    cases σ_verified,
    case env.vcgen.tru Q _ σ_verified ih { from
      have ∀σ', dominates_p σ' (prop.and Q (x ≡ value.true)) Q,
      from λσ', dominates_p.of_and_left,
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ ∀σ', dominates_p σ' (prop.and Q (x ≡ value.true)) Q_1,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.fls Q _ σ_verified { from
      have ∀σ', dominates_p σ' (prop.and Q (x ≡ value.false)) Q,
      from λσ', dominates_p.of_and_left,
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ ∀σ', dominates_p σ' (prop.and Q (x ≡ value.false)) Q_1,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.num n Q _ σ_verified { from
      have ∀σ', dominates_p σ' (prop.and Q (x ≡ value.num n)) Q,
      from λσ', dominates_p.of_and_left,
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ ∀σ', dominates_p σ' (prop.and Q (x ≡ value.num n)) Q_1,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.func σ₂ f fx R S H e Q Q₂ Q₃ x_not_in_σ f_not_in_σ₂
         fx_not_in_σ₂ f_neq_fx σ₁_verified σ₂_verified fx_in_R fv_R fv_S e_verified func_vc { from
      let funcp := prop.subst_env (σ₂[f↦value.func f fx R S e H σ₂])
                                  (prop.func f fx R (Q₃ (term.app f fx) ⋀ S)) in
      have ∀σ', dominates_p σ' (Q ⋀ x ≡ value.func f fx R S e H σ₂ ⋀ funcp) Q,
      from λσ', dominates_p.of_and_left,
      show ∃Q_1, (⊢ σ : Q_1) ∧ ∀σ', dominates_p σ' (prop.and Q ((x ≡ (value.func f fx R S e H σ₂)) ⋀ funcp)) Q_1,
      from exists.intro Q ⟨σ₁_verified, this⟩
    }
  end

lemma env_dominates_n_rest {P: prop} {σ: env} {x: var} {v: value}:
      (⊢ (σ[x↦v]) : P) → (∃Q, (⊢ σ : Q) ∧ ∀σ', dominates_n σ' P Q) :=
  assume σ_verified: ⊢ (σ[x↦v]) : P,
  begin
    cases σ_verified,
    case env.vcgen.tru Q _ σ_verified ih { from
      have ∀σ', dominates_n σ' (prop.and Q (x ≡ value.true)) Q,
      from λσ', dominates_n.of_and_left,
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ ∀σ', dominates_n σ' (prop.and Q (x ≡ value.true)) Q_1,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.fls Q _ σ_verified { from
      have ∀σ', dominates_n σ' (prop.and Q (x ≡ value.false)) Q,
      from λσ', dominates_n.of_and_left,
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ ∀σ', dominates_n σ' (prop.and Q (x ≡ value.false)) Q_1,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.num n Q _ σ_verified { from
      have ∀σ', dominates_n σ' (prop.and Q (x ≡ value.num n)) Q,
      from λσ', dominates_n.of_and_left,
      show ∃(Q_1 : prop), (⊢ σ : Q_1) ∧ ∀σ', dominates_n σ' (prop.and Q (x ≡ value.num n)) Q_1,
      from exists.intro Q ⟨σ_verified, this⟩
    },
    case env.vcgen.func σ₂ f fx R S H e Q Q₂ Q₃ x_not_in_σ f_not_in_σ₂
         fx_not_in_σ₂ f_neq_fx σ₁_verified σ₂_verified fx_in_R fv_R fv_S e_verified func_vc { from
      let funcp := prop.subst_env (σ₂[f↦value.func f fx R S e H σ₂])
                                  (prop.func f fx R (Q₃ (term.app f fx) ⋀ S)) in
      have ∀σ', dominates_n σ' (Q ⋀ x ≡ value.func f fx R S e H σ₂ ⋀ funcp) Q,
      from λσ', dominates_n.of_and_left,
      show ∃Q_1, (⊢ σ : Q_1) ∧ ∀σ', dominates_n σ' (prop.and Q ((x ≡ (value.func f fx R S e H σ₂)) ⋀ funcp)) Q_1,
      from exists.intro Q ⟨σ₁_verified, this⟩
    }
  end

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
