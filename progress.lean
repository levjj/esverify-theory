import .syntax .notations .logic .evaluation .vcgen

@[reducible]
def is_value(s: stack): Prop := ∃(σ: env) (x: var) (v: value), s = (σ, exp.return x) ∧ (σ x = v)

lemma not_free_of_subst_env_val {P: prop} {σ: env} {x y: var} {v: value}:
       free_in_prop x (P && (y ≡ v)) → (free_in_prop x P → ∀ (R : spec), ¬free_in_prop x ↑(spec.subst_env σ R)) →
       ∀R: spec, ¬(free_in_prop x (spec.subst_env (σ[y↦v]) R)) :=
  assume x_free_in_P: free_in_prop x (P && (y ≡ v)),
  assume ih: free_in_prop x P → ∀ (R : spec), ¬free_in_prop x ↑(spec.subst_env σ R),
  assume R: spec,
  assume x_free_in_subst: free_in_prop x (spec.subst_env (σ[y↦v]) R),
  have x_neq_y: x ≠ y, from (free_of_subst_env_spec x_free_in_subst).left,
  have free_in_prop x P ∨ free_in_prop x (y ≡ v), from free_in_prop.and.inv x_free_in_P,
  or.elim this (
    assume : free_in_prop x P,
    have x_free_in_R: free_in_prop x (spec.subst_env σ R), from (free_of_subst_env_spec x_free_in_subst).right,
    have ¬free_in_prop x (spec.subst_env σ R), from ih this R,
    show «false», from this x_free_in_R
  ) (
    assume : free_in_prop x (y ≡ v),
    have free_in_term x (y ≡ v), from free_in_prop.term.inv this,
    (free_in_term.binop.inv this).elim (
      assume : free_in_term x y,
      have x = y, from free_in_term.var.inv this,
      show «false», from x_neq_y this
    ) (
      assume : free_in_term x v,
      show «false», from free_in_term.value.inv this
    )
  )

lemma exp.post_free {P: prop} {e: exp} {Q: propctx} {x: var}:
       (P ⊢ e : Q) → ∀t, x ∈ FV (Q t) → x ∈ FV t ∨ x ∈ FV P :=
  assume e_verified: P ⊢ e : Q,
  begin
    induction e_verified,
    case exp.vcgen.tru P y e' Q y_not_in_P e'_verified ih { from
      assume t: term,
      assume x_free_in_Qt: x ∈ FV ((propctx.exis y ((y ≡ value.true) && Q)) t),
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
      have x ∈ FV ((↑(y ≡ value.true) && Q) t), from (free_in_propctx.exis.inv x_free_in_Qt).right,
      have x ∈ FV (propctx.term (y ≡ value.true) t) ∨ x ∈ FV (Q t), from free_in_propctx.and.inv this,
      or.elim this (
        assume : x ∈ FV (propctx.term (y ≡ value.true) t),
        have x ∈ FV (((y ≡ value.true).to_termctx) t), from free_in_propctx.term.inv this,
        have x ∈ FV (y ≡ value.true), from free_in_termctx.term.inv this,
        show x ∈ FV t ∨ x ∈ FV P, from absurd this x_not_in_yv
      ) (
        assume : x ∈ FV (Q t),
        have x ∈ FV t ∨ x ∈ FV (P && (y ≡ value.true)), from ih t this,
        or.elim this (
          assume : x ∈ FV t,
          show x ∈ FV t ∨ x ∈ FV P, from or.inl this
        ) (
          assume : x ∈ FV (P && (y ≡ value.true)),
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
      assume x_free_in_Qt: x ∈ FV ((propctx.exis y ((y ≡ value.false) && Q)) t),
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
      have x ∈ FV ((↑(y ≡ value.false) && Q) t), from (free_in_propctx.exis.inv x_free_in_Qt).right,
      have x ∈ FV (propctx.term (y ≡ value.false) t) ∨ x ∈ FV (Q t), from free_in_propctx.and.inv this,
      or.elim this (
        assume : x ∈ FV (propctx.term (y ≡ value.false) t),
        have x ∈ FV (((y ≡ value.false).to_termctx) t), from free_in_propctx.term.inv this,
        have x ∈ FV (y ≡ value.false), from free_in_termctx.term.inv this,
        show x ∈ FV t ∨ x ∈ FV P, from absurd this x_not_in_yv
      ) (
        assume : x ∈ FV (Q t),
        have x ∈ FV t ∨ x ∈ FV (P && (y ≡ value.false)), from ih t this,
        or.elim this (
          assume : x ∈ FV t,
          show x ∈ FV t ∨ x ∈ FV P, from or.inl this
        ) (
          assume : x ∈ FV (P && (y ≡ value.false)),
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
      assume x_free_in_Qt: x ∈ FV ((propctx.exis y ((y ≡ value.num n) && Q)) t),
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
      have x ∈ FV ((↑(y ≡ value.num n) && Q) t), from (free_in_propctx.exis.inv x_free_in_Qt).right,
      have x ∈ FV (propctx.term (y ≡ value.num n) t) ∨ x ∈ FV (Q t), from free_in_propctx.and.inv this,
      or.elim this (
        assume : x ∈ FV (propctx.term (y ≡ value.num n) t),
        have x ∈ FV (((y ≡ value.num n).to_termctx) t), from free_in_propctx.term.inv this,
        have x ∈ FV (y ≡ value.num n), from free_in_termctx.term.inv this,
        show x ∈ FV t ∨ x ∈ FV P, from absurd this x_not_in_yv
      ) (
        assume : x ∈ FV (Q t),
        have x ∈ FV t ∨ x ∈ FV (P && (y ≡ value.num n)), from ih t this,
        or.elim this (
          assume : x ∈ FV t,
          show x ∈ FV t ∨ x ∈ FV P, from or.inl this
        ) (
          assume : x ∈ FV (P && (y ≡ value.num n)),
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
    case exp.vcgen.func P f fx R S e₁ e₂ Q₁ Q₂ f_not_in_P fv_R fv_S _ _ func_vc ih₁ ih₂ { from
      assume t: term,
      assume x_free_in_Qt: x ∈ FV ((propctx.exis f ((prop.func f fx R (Q₁ (term.app f fx) && S)) && Q₂)) t),
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
      have x_not_in_func: x ∈ FV (prop.func f fx R (Q₁ (term.app f fx) && S)) → x ∈ FV P, from (
        assume : x ∈ FV (prop.func f fx R (Q₁ (term.app f fx) && S)),
        have x ∈ FV (term.var f) ∨ (x ≠ fx ∧ (x ∈ FV R.to_prop ∨ x ∈ FV (Q₁ (term.app f fx) && S))),
        from free_in_prop.func.inv this,
        or.elim this (
          assume : x ∈ FV (term.var f),
          have x = f, from free_in_term.var.inv this,
          show x ∈ FV P, from absurd this x_neq_f
        ) (
          assume : x ≠ fx ∧ (x ∈ FV R.to_prop ∨ x ∈ FV (Q₁ (term.app f fx) && S)),
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
            assume : x ∈ FV (Q₁ (term.app f fx) && S),
            or.elim (free_in_prop.and.inv this) (
              assume : x ∈ FV (Q₁ (term.app f fx)),
              have x ∈ FV (term.app f fx) ∨ x ∈ FV (P && (spec.func f fx R S) && R), from ih₁ (term.app f fx) this,
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
                assume : x ∈ FV (P && (spec.func f fx R S) && R),
                or.elim (free_in_prop.and.inv this).symm x_not_in_R (
                  assume : x ∈ FV (P && spec.func f fx R S),
                  or.elim (free_in_prop.and.inv this) id (
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
      have x ∈ FV ((propctx.and (prop.func f fx R (Q₁ (term.app f fx) && S)) Q₂) t),
      from (free_in_propctx.exis.inv x_free_in_Qt).right,
      have x ∈ FV ((prop.func f fx R (Q₁ (term.app f fx) && S)) t) ∨ x ∈ FV (Q₂ t),
      from free_in_propctx.and.inv this,
      or.elim this (
        assume : x ∈ FV ((prop.func f fx R (Q₁ (term.app f fx) && S)) t),
        have x ∈ FV (prop.func f fx R (Q₁ (term.app f fx) && S)), from free_in_propctx.prop.inv this,
        show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_func this)
      ) (
        assume : x ∈ FV (Q₂ t),
        have x ∈ FV t ∨ x ∈ FV (P && prop.func f fx R (Q₁ (term.app f fx) && S)), from ih₂ t this,
        or.elim this (
          assume : x ∈ FV t,
          show x ∈ FV t ∨ x ∈ FV P, from or.inl this
        ) (
          assume : x ∈ FV (P && prop.func f fx R (Q₁ (term.app f fx) && S)),
          or.elim (free_in_prop.and.inv this) (
            assume : x ∈ FV P,
            show x ∈ FV t ∨ x ∈ FV P, from or.inr this
          ) (
            assume : x ∈ FV (prop.func f fx R (Q₁ (term.app f fx) && S)),
            show x ∈ FV t ∨ x ∈ FV P, from or.inr (x_not_in_func this)
          )
        )
      )
    },
    case exp.vcgen.unop op x₁ y e' Q' x_free_in_P _ e'_verified vc_valid ih { from

    },
    case exp.vcgen.binop op x₁ x₂ y z e' Q' x_free_in_P y_free_in_P _ e'_verified vc_valid ih { from
    },
    case exp.vcgen.app y f x₁ e' Q' f_free_in_P x_free_in_P _ e'_verified vc_valid ih { from
    },
    case exp.vcgen.ite y e₂ e₁ Q₁ Q₂ x_free_in_P _ _ vc_valid ih₁ ih₂ { from
    },
    case exp.vcgen.return y y_free_in_P { from
    }
  end

lemma not_free_of_subst_env {P: prop} {σ: env} {x: var}:
       (⊢ σ : P) → free_in_prop x P → ∀R: spec, ¬(free_in_prop x (spec.subst_env σ R)) :=
  assume env_verified: ⊢ σ : P,
  assume x_free_in_P: free_in_prop x P,
  show (∀R: spec, ¬(free_in_prop x (spec.subst_env σ R))), by begin
    induction env_verified,
    case env.vcgen.empty { from
      assume R: spec,
      assume x_free_in_subst: free_in_prop x (spec.subst_env env.empty R),
      have free_in_term x value.true, from free_in_prop.term.inv x_free_in_P,
      show «false», from free_in_term.value.inv this
    },
    case env.vcgen.tru σ' y Q _ _ ih {
      show ∀R: spec, ¬(free_in_prop x (spec.subst_env (σ'[y↦value.true]) R)),
      from not_free_of_subst_env_val x_free_in_P ih
    },
    case env.vcgen.fls σ' y Q _ _ ih { from
      show ∀R: spec, ¬(free_in_prop x (spec.subst_env (σ'[y↦value.false]) R)),
      from not_free_of_subst_env_val x_free_in_P ih
    },
    case env.vcgen.num n σ' y Q _ _ ih { from
      show ∀R: spec, ¬(free_in_prop x (spec.subst_env (σ'[y↦value.num n]) R)),
      from not_free_of_subst_env_val x_free_in_P ih
    },
    case env.vcgen.func f σ₁ σ₂ g gx R' S' e Q₁ Q₂ Q₃ _ _ _ fv_R fv_S _ _ ih₁ ih₂ { from
     assume R: spec,
     assume x_free_in_subst: free_in_prop x (spec.subst_env (σ₂[f↦value.func g gx R' S' e σ₁]) R),
     have x_neq_f: x ≠ f, from (free_of_subst_env_spec x_free_in_subst).left,
     let vf := value.func g gx R' S' e σ₁ in
     let R'' := spec.subst_env (σ₁[g↦vf]) R' in
     let S'' := spec.subst_env (σ₁[g↦vf]) S' in
     let Q' := Q₃ (term.app vf gx) in
     have free_in_prop x (Q₁ && (f ≡ vf)) ∨ free_in_prop x (prop.func vf gx R'' (Q' && S'')),
     from free_in_prop.and.inv x_free_in_P,
     or.elim this (
       assume h: free_in_prop x (Q₁ && (f ≡ vf)),
       have x_neq_f: x ≠ f, from (free_of_subst_env_spec x_free_in_subst).left,
       have free_in_prop x Q₁ ∨ free_in_prop x (f ≡ vf), from free_in_prop.and.inv h,
       or.elim this (
         assume : free_in_prop x Q₁,
         have x_free_in_R: free_in_prop x (spec.subst_env σ₂ R), from (free_of_subst_env_spec x_free_in_subst).right,
         have ¬free_in_prop x (spec.subst_env σ₂ R), from ih₁ this R,
         show «false», from this x_free_in_R
       ) (
         assume : free_in_prop x (f ≡ vf),
         have free_in_term x (f ≡ vf), from free_in_prop.term.inv this,
         (free_in_term.binop.inv this).elim (
           assume : free_in_term x f,
           have x = f, from free_in_term.var.inv this,
           show «false», from x_neq_f this
         ) (
           assume : free_in_term x (vf),
           show «false», from free_in_term.value.inv this
         )
       )
     ) (
       assume x_free_in_func: free_in_prop x (prop.func vf gx R'' (Q' && S'')),
       let forallp := (prop.implies R''.to_prop (prop.pre vf gx)
                    && prop.implies (prop.post vf gx) (Q' && S''.to_prop)) in
       have h: prop.func vf gx R''.to_prop (Q' && S''.to_prop)
            = (term.unop unop.isFunc vf && prop.forallc gx vf forallp),
       by unfold prop.func,
       have free_in_prop x (term.unop unop.isFunc vf && prop.forallc gx vf forallp), from h ▸ x_free_in_func,
       have free_in_prop x (term.unop unop.isFunc vf) ∨ free_in_prop x (prop.forallc gx vf forallp),
       from free_in_prop.and.inv this,
       or.elim this (
         assume : free_in_prop x (term.unop unop.isFunc vf),
         have free_in_term x (term.unop unop.isFunc vf), from free_in_prop.term.inv this,
         have free_in_term x vf, from free_in_term.unop.inv this,
         show «false», from free_in_term.value.inv this
       ) (
         assume : free_in_prop x (prop.forallc gx vf forallp),
         have x_neq_gx: x ≠ gx, from (free_in_prop.forallc.inv this).left,
         have free_in_term x vf ∨ free_in_prop x forallp, from (free_in_prop.forallc.inv this).right,
         or.elim this (
           assume : free_in_term x vf,
           show «false», from free_in_term.value.inv this
         ) (
           assume : free_in_prop x forallp,
           or.elim (free_in_prop.and.inv this) (
             assume : free_in_prop x (prop.implies R''.to_prop (prop.pre vf gx)),
             or.elim (free_in_prop.implies.inv this) (
               assume : free_in_prop x R''.to_prop,
               have x ≠ g ∧ free_in_prop x (spec.subst_env σ₁ R').to_prop, from free_of_subst_env_spec this,
               have x_neq_g: x ≠ g, from this.left,
               have x_free_in_sR': free_in_prop x (spec.subst_env σ₁ R').to_prop, from this.right,
               have x_free_in_R': x ∈ FV R'.to_prop, from free_of_subst_env x_free_in_sR',
               have x ∈ FV Q₂ ∪ {g, gx}, from set.mem_of_mem_of_subset x_free_in_R' fv_R,
               have x ∈ FV Q₂ ∨ x ∈ {g, gx}, from set.mem_or_mem_of_mem_union this,
               or.elim this (
                 assume : x ∈ FV Q₂,
                 have ¬ free_in_prop x ↑(spec.subst_env σ₁ R'), from ih₂ this R',
                 show «false», from this x_free_in_sR'
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
             ) (
               assume : free_in_prop x (prop.pre vf gx),
               have free_in_term x vf ∨ free_in_term x gx, from free_in_prop.pre.inv this,
               or.elim this (
                 assume : free_in_term x vf,
                 show «false», from free_in_term.value.inv this
               ) (
                 assume : free_in_term x gx,
                 have x = gx, from free_in_term.var.inv this,
                 show «false», from x_neq_gx this
               )
             )
           ) (
             assume : free_in_prop x (prop.implies (prop.post vf gx) (Q' && S''.to_prop)),
             or.elim (free_in_prop.implies.inv this) (
                assume : free_in_prop x (prop.post vf gx),
                have free_in_term x vf ∨ free_in_term x gx, from free_in_prop.post.inv this,
                or.elim this (
                  assume : free_in_term x vf,
                  show «false», from free_in_term.value.inv this
                ) (
                  assume : free_in_term x gx,
                  have x = gx, from free_in_term.var.inv this,
                  show «false», from x_neq_gx this
                )
             ) (
               assume : free_in_prop x (Q' && S''.to_prop),
               have free_in_prop x Q' ∨ free_in_prop x S''.to_prop, from free_in_prop.and.inv this,
               or.elim this (
                 assume : free_in_prop x Q',

                 sorry
               ) (
                assume : free_in_prop x S''.to_prop,
                have x ≠ g ∧ free_in_prop x (spec.subst_env σ₁ S').to_prop, from free_of_subst_env_spec this,
                have x_neq_g: x ≠ g, from this.left,
                have x_free_in_sS': free_in_prop x (spec.subst_env σ₁ S').to_prop, from this.right,
                have x_free_in_S': x ∈ FV S'.to_prop, from free_of_subst_env x_free_in_sS',
                have x ∈ FV Q₂ ∪ {g, gx}, from set.mem_of_mem_of_subset x_free_in_S' fv_S,
                have x ∈ FV Q₂ ∨ x ∈ {g, gx}, from set.mem_or_mem_of_mem_union this,
                or.elim this (
                  assume : x ∈ FV Q₂,
                  have ¬ free_in_prop x ↑(spec.subst_env σ₁ S'), from ih₂ this S',
                  show «false», from this x_free_in_sS'
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
               )
             )
           )
         )
       )
     )
   }
 end

lemma val_of_free_in_nonempty_env {P: prop} {σ: env} {x y: var} {v: value}:
                                  (⊢ σ : P) → (x ≠ y → ∃v', σ y = some v') → ∃v', σ[x↦v] y = some v' :=
  assume env_verified: ⊢ σ : P,
  assume ih: x ≠ y → ∃v', σ y = some v',
  if x_eq_y: x = y ∧ option.is_none (σ.apply y) then (
    have h: σ[x↦v].apply x = (if x = x ∧ option.is_none (σ.apply x) then ↑v else σ.apply x), by unfold env.apply,
    have (if x = x ∧ option.is_none (σ.apply x) then ↑v else σ.apply x) = ↑v, by simp *,
    have σ[x↦v].apply x = ↑v, from this ▸ h,
    have σ[x↦v].apply y = some v, from x_eq_y.left ▸ this,
    show ∃v', σ[x↦v] y = some v', from exists.intro v this
  ) else (
    have ∃v', σ y = some v', from (
      have ¬(x = y) ∨ ¬(option.is_none (σ.apply y)), from not_and_distrib.mp x_eq_y,
      this.elim (
        assume : x ≠ y,
        show ∃v', σ y = some v', from ih this        
      ) ( 
        assume : ¬(option.is_none (env.apply σ y)),
        have ¬(option.is_none (σ y)), from this,
        show ∃v', σ y = some v', from not_is_none.rinv.mpr this
      )
    ),
    let ⟨v', σ_has_y⟩ := this in
    have h: σ[x↦v].apply y = (if x = y ∧ option.is_none (σ.apply y) then ↑v else σ.apply y), by unfold env.apply,
    have (if x = y ∧ option.is_none (σ.apply y) then ↑v else σ.apply y) = σ.apply y, by simp *,
    have σ[x↦v].apply y = σ.apply y, from this ▸ h,
    have σ[x↦v].apply y = some v', from eq.trans this σ_has_y,
    show ∃v', σ[x↦v] y = some v', from exists.intro v' this
  )

lemma val_of_free_in_env_value {P: prop} {σ: env} {x y: var} {v: value}:
  (⊢ σ : P) → x ∈ FV (P && (y ≡ v)) → (x ∈ FV P → (∃ (v : value), σ x = some v)) → ∃v', σ[y↦v] x = some v' :=
  assume σ_verified: ⊢ σ : P,
  assume x_free_in_P: x ∈ FV (P && (y ≡ v)),
  assume ih : x ∈ FV P → (∃ (v : value), σ x = some v),
  val_of_free_in_nonempty_env σ_verified (
    assume x'_is_not_x: y ≠ x,
    have free_in_prop x P ∨ free_in_prop x (y ≡ v), from free_in_prop.and.inv x_free_in_P,
    or.elim this.symm
    (
      assume x_free_in_eq_v: free_in_prop x (y ≡ v),
      show ∃v', σ x = some v', by begin
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
    (
      assume x_free_in_P: free_in_prop x P,
      show ∃v', σ x = some v', from ih x_free_in_P
    )
  )

lemma val_of_free_in_env {P: prop} {σ: env} {x: var}: (⊢ σ : P) → x ∈ FV P → ∃v, σ x = some v :=
  assume env_verified: ⊢ σ: P,
  assume x_free_in_P: x ∈ FV P,
  begin
    induction env_verified,
    case env.vcgen.empty {
      cases x_free_in_P,
      case free_in_prop.term x_free_in_true {
        cases x_free_in_true
      }
    },
    case env.vcgen.tru σ' x' Q _ σ'_verified ih {
      show ∃v, σ'[x'↦value.true] x = some v, from val_of_free_in_env_value σ'_verified x_free_in_P ih
    },
    case env.vcgen.fls σ' x' Q _ σ'_verified ih {
      show ∃v, σ'[x'↦value.false] x = some v, from val_of_free_in_env_value σ'_verified x_free_in_P ih
    },
    case env.vcgen.num n σ' x' Q _ σ'_verified ih { from
      show ∃v, σ'[x'↦value.num n] x = some v, from val_of_free_in_env_value σ'_verified x_free_in_P ih
    },
    case env.vcgen.func σ₁ σ₂ f g fx R S e Q₁ Q₂ Q₃ _ σ₁_verified σ₂_verified fv_R fv_S func_verified S_valid { from
      -- show ∃v, σ₁[f↦value.func g fx R S e σ₂] x = some v, from val_of_free_in_env_value σ₁_verified x_free_in_P ih_1
      val_of_free_in_nonempty_env σ₁_verified (
        assume : f ≠ x,
        have x_neq_f: x ≠ f, from this.symm,
        let R' := spec.subst_env (σ₂[g↦value.func g fx R S e σ₂]) R in
        let S' := spec.subst_env (σ₂[g↦value.func g fx R S e σ₂]) S in
        have free_in_prop x (Q₁ && (f ≡ value.func g fx R S e σ₂)) ∨ free_in_prop x (spec.func ↑f fx R' S'),
        from free_in_prop.and.inv x_free_in_P,
        or.elim this (
          assume h: free_in_prop x (Q₁ && (f ≡ value.func g fx R S e σ₂)),
          have free_in_prop x Q₁ ∨ free_in_prop x (f ≡ value.func g fx R S e σ₂), from free_in_prop.and.inv h,
          or.elim this (
            assume : free_in_prop x Q₁,
            show ∃v', σ₁ x = some v', from ih_1 this
          ) (
            assume : free_in_prop x (f ≡ value.func g fx R S e σ₂),
            have free_in_term x (f ≡ value.func g fx R S e σ₂), from free_in_prop.term.inv this,
            (free_in_term.binop.inv this).elim (
              assume : free_in_term x f,
              have x = f, from free_in_term.var.inv this,
              show ∃v', σ₁ x = some v', from absurd this x_neq_f
            ) (
              assume : free_in_term x (value.func g fx R S e σ₂),
              show ∃v', σ₁ x = some v', from absurd this free_in_term.value.inv
            )
          )
        ) (
          assume x_free_in_func: free_in_prop x (spec.func f fx R' S'),
          let forallp := (prop.implies R'.to_prop (prop.pre f fx)
                       && prop.implies (prop.post f fx) S'.to_prop) in
          have h: (spec.func f fx R' S').to_prop = (term.unop unop.isFunc f && prop.forallc fx f forallp),
          by unfold spec.to_prop,
          have free_in_prop x (term.unop unop.isFunc f && prop.forallc fx f forallp), from h ▸ x_free_in_func,
          have free_in_prop x (term.unop unop.isFunc f) ∨ free_in_prop x (prop.forallc fx f forallp),
          from free_in_prop.and.inv this,
          or.elim this (
            assume : free_in_prop x (term.unop unop.isFunc f),
            have free_in_term x (term.unop unop.isFunc f), from free_in_prop.term.inv this,
            have free_in_term x f, from free_in_term.unop.inv this,
            have x = f, from free_in_term.var.inv this,
            show ∃v', σ₁ x = some v', from absurd this x_neq_f
          ) (
            assume : free_in_prop x (prop.forallc fx f forallp),
            have x_neq_fx: x ≠ fx, from (free_in_prop.forallc.inv this).left,
            have free_in_term x f ∨ free_in_prop x forallp, from (free_in_prop.forallc.inv this).right,
            or.elim this (
              assume : free_in_term x f,
              have x = f, from free_in_term.var.inv this,
              show ∃v', σ₁ x = some v', from absurd this x_neq_f
            ) (
              assume : free_in_prop x forallp,
              or.elim (free_in_prop.and.inv this) (
                assume : free_in_prop x (prop.implies R'.to_prop (prop.pre f fx)),
                or.elim (free_in_prop.implies.inv this) (
                  assume : free_in_prop x R'.to_prop,
                  have x ≠ g ∧ free_in_prop x (spec.subst_env σ₂ R).to_prop, from free_of_subst_env_spec this,
                  have x_neq_g: x ≠ g, from this.left,
                  have x_free_in_sR': free_in_prop x (spec.subst_env σ₂ R).to_prop, from this.right,
                  have x_free_in_R': x ∈ FV R.to_prop, from free_of_subst_env x_free_in_sR',
                  have x ∈ FV Q₂ ∪ {g, fx}, from set.mem_of_mem_of_subset x_free_in_R' fv_R,
                  have x ∈ FV Q₂ ∨ x ∈ {g, fx}, from set.mem_or_mem_of_mem_union this,
                  or.elim this (
                    assume : x ∈ FV Q₂,
                    show ∃v', σ₁ x = some v',
                    from false.elim (not_free_of_subst_env σ₂_verified this R x_free_in_sR')
                  ) (
                    assume : x ∈ {g, fx},
                    have (x = g) ∨ (x = fx), from set.two_elems_mem this,
                    or.elim this (
                      assume : x = g,
                      show ∃v', σ₁ x = some v', from absurd this x_neq_g
                    ) (
                      assume : x = fx,
                      show ∃v', σ₁ x = some v', from absurd this x_neq_fx
                    )
                  )
                ) (
                  assume : free_in_prop x (prop.pre f fx),
                  have free_in_term x f ∨ free_in_term x fx, from free_in_prop.pre.inv this,
                  or.elim this (
                    assume : free_in_term x f,
                    have x = f, from free_in_term.var.inv this,
                    show ∃v', σ₁ x = some v', from absurd this x_neq_f
                  ) (
                    assume : free_in_term x fx,
                    have x = fx, from free_in_term.var.inv this,
                    show ∃v', σ₁ x = some v', from absurd this x_neq_fx
                  )
                )
              ) (
                assume : free_in_prop x (prop.implies (prop.post f fx) S'.to_prop),
                or.elim (free_in_prop.implies.inv this) (
                  assume : free_in_prop x (prop.post f fx),
                  have free_in_term x f ∨ free_in_term x fx, from free_in_prop.post.inv this,
                  or.elim this (
                    assume : free_in_term x f,
                    have x = f, from free_in_term.var.inv this,
                    show ∃v', σ₁ x = some v', from absurd this x_neq_f
                  ) (
                    assume : free_in_term x fx,
                    have x = fx, from free_in_term.var.inv this,
                    show ∃v', σ₁ x = some v', from absurd this x_neq_fx
                  )
                ) (
                  assume : free_in_prop x S'.to_prop,
                  have x ≠ g ∧ free_in_prop x (spec.subst_env σ₂ S).to_prop, from free_of_subst_env_spec this,
                  have x_neq_g: x ≠ g, from this.left,
                  have x_free_in_sS': free_in_prop x (spec.subst_env σ₂ S).to_prop, from this.right,
                  have x_free_in_S': x ∈ FV S.to_prop, from free_of_subst_env x_free_in_sS',
                  have x ∈ FV Q₂ ∪ {g, fx}, from set.mem_of_mem_of_subset x_free_in_S' fv_S,
                  have x ∈ FV Q₂ ∨ x ∈ {g, fx}, from set.mem_or_mem_of_mem_union this,
                  or.elim this (
                    assume : x ∈ FV Q₂,
                    show ∃v', σ₁ x = some v',
                    from false.elim (not_free_of_subst_env σ₂_verified this S x_free_in_sS')
                  ) (
                    assume : x ∈ {g, fx},
                    have (x = g) ∨ (x = fx), from set.two_elems_mem this,
                    or.elim this (
                      assume : x = g,
                      show ∃v', σ₁ x = some v', from absurd this x_neq_g
                    ) (
                      assume : x = fx,
                      show ∃v', σ₁ x = some v', from absurd this x_neq_fx
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

lemma val_of_free_in_hist_env {H: callhistory} {σ: env} {P: prop} {x: var}:
                              (⊢ σ : P) → x ∈ FV (↑H && P) → ∃v, σ x = some v :=
  assume σ_verified: ⊢ σ : P,
  assume x_free_in_H_P: x ∈ FV (↑H && P),
  have free_in_prop x H ∨ free_in_prop x P, from free_in_prop.and.inv x_free_in_H_P,
  have x ∈ FV P, from or.elim this.symm id (
    assume : free_in_prop x H,
    show free_in_prop x P, from absurd this (call_history_closed H x)
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
                                   (⊢ σ: P) → x ∉ σ → σ ⊨ P.erased → (σ[x↦v]) ⊨ (P && (x ≡ v)).erased :=
  assume σ_verified: ⊢ σ: P,
  assume x_not_free_in_σ: x ∉ σ,
  assume ih: σ ⊨ P.erased,
  have σ.apply x = none, from env.contains_apply_equiv.left.mpr x_not_free_in_σ,
  have h1: (σ[x↦v]) ⊨ (prop.term (x ≡ v)).erased,
  from simple_equality_valid x_not_free_in_σ,
  have h2: ⊨ vc.subst_env σ P.erased, from ih,
  have x_not_in_q: x ∉ FV (vc.subst_env σ P.erased), from (
    assume : x ∈ FV (vc.subst_env σ P.erased),
    have x ∈ FV P.erased, from free_in_vc.subst_env this,
    have x ∈ FV P, from free_of_erased_free (or.inl this),
    have ∃v, σ x = some v, from val_of_free_in_env σ_verified this,
    have x ∈ σ, from env.contains_apply_equiv.right.mp this,
    show «false», from x_not_free_in_σ this
  ),
  have vc.subst x v (vc.subst_env σ P.erased) = vc.subst_env σ P.erased,
  from unchanged_of_subst_nonfree_vc x_not_in_q,
  have h: ⊨ vc.subst x v (vc.subst_env σ P.erased),
  from @eq.subst vc (λa, ⊨ a) (vc.subst_env σ P.erased)
          (vc.subst x v (vc.subst_env σ P.erased)) this.symm h2,
  have vc.subst x v (vc.subst_env σ P.erased)
      = vc.subst_env (σ[x↦v]) P.erased, by unfold vc.subst_env, 
  have ⊨ vc.subst_env (σ[x↦v]) P.erased, from this ▸ h,
  have h2: (σ[x↦v]) ⊨ P.erased, from this,
  have h3: (σ[x↦v]) ⊨ (P.erased && (prop.term (x ≡ v)).erased),
  from valid_env.and h2 h1,
  have prop.erased (prop.and P (prop.term (x ≡ v))) = P.erased && (prop.term (x ≡ v)).erased,
  by unfold prop.erased,
  show (σ[x↦v]) ⊨ prop.erased (P && (x ≡ v)), from this.symm ▸ h3

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
      show (σ'[x'↦value.true]) ⊨ prop.erased (Q && (x' ≡ value.true)),
      from simple_equality_env_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.vcgen.fls σ' x' Q x_not_free_in_σ' σ'_verified ih {
      show (σ'[x'↦value.false]) ⊨ prop.erased (Q && (x' ≡ value.false)),
      from simple_equality_env_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.vcgen.num n σ' x' Q x_not_free_in_σ' σ'_verified ih {
      show (σ'[x'↦value.num n]) ⊨ prop.erased (Q && (x' ≡ value.num n)),
      from simple_equality_env_valid σ'_verified x_not_free_in_σ' ih
    },
    case env.vcgen.func σ₁ σ₂ f g gx R S e Q₁ Q₂ Q₃
      f_not_free_in_σ₁ σ₁_verified σ₂_verified R_fv S_fv func_verified S_valid ih₁ ih₂ { from (
      have h0: (σ₁[f↦value.func g gx R S e σ₂]) ⊨ prop.erased (Q₁ && (f ≡ value.func g gx R S e σ₂)),
      from simple_equality_env_valid σ₁_verified f_not_free_in_σ₁ ih₁,
      let R' := spec.subst_env (σ₂[g↦value.func g gx R S e σ₂]) R in
      let S' := spec.subst_env (σ₂[g↦value.func g gx R S e σ₂]) S in
      let σ' := σ₁[f↦value.func g gx R S e σ₂] in
      let forallp := prop.implies R'.to_prop (prop.pre f gx)
                  && prop.implies (prop.post f gx) S'.to_prop in
      
      have h1: σ' ⊨ prop.erased (term.unop unop.isFunc f), from (
        have unop.apply unop.isFunc (value.func g gx R S e σ₂) = value.true, by unfold unop.apply,
        have ⊨ (term.unop unop.isFunc (value.func g gx R S e σ₂) ≡ value.true), from valid.eq.unop.mp this,
        have h2: ⊨ term.unop unop.isFunc (value.func g gx R S e σ₂), from valid.eq.true.mpr this,
        have term.subst f (value.func g gx R S e σ₂) f = (value.func g gx R S e σ₂),
        from term.subst.var.same,
        have h3: ⊨ term.unop unop.isFunc (term.subst f (value.func g gx R S e σ₂) f),
        from this.symm ▸ h2,
        have σ₁ f = none, from env.contains_apply_equiv.left.mpr f_not_free_in_σ₁,
        have term.subst_env σ₁ f = f, from term.subst_env.var.left.mp this,
        have h4: ⊨ term.unop unop.isFunc (term.subst f (value.func g gx R S e σ₂) (term.subst_env σ₁ f)),
        from this.symm ▸ h3,
        have term.subst_env σ' f = term.subst f (value.func g gx R S e σ₂) (term.subst_env σ₁ f),
        by unfold term.subst_env,
        have h5: ⊨ term.unop unop.isFunc (term.subst_env σ' f), from this.symm ▸ h4,
        have term.subst_env σ' (term.unop unop.isFunc f) = term.unop unop.isFunc (term.subst_env σ' f),
        from term.subst_env.unop,
        have h6: ⊨ vc.term (term.subst_env σ' (term.unop unop.isFunc f)), from this.symm ▸ h5,
        have vc.subst_env σ' (vc.term (term.unop unop.isFunc f))
          = vc.term (term.subst_env σ' (term.unop unop.isFunc f)), from vc.subst_env.term,
        have h7: σ' ⊨ vc.term (term.unop unop.isFunc f), from this.symm ▸ h6,
        have prop.erased (prop.term (term.unop unop.isFunc f)) = vc.term (term.unop unop.isFunc f),
        by unfold prop.erased,
        show σ' ⊨ prop.erased (term.unop unop.isFunc f), from this.symm ▸ h7
      ),

      have h2: σ' ⊨ prop.erased (prop.forallc gx f forallp), from (
        have h9: σ' ⊨ vc.univ gx forallp.erased, from sorry,
        have prop.erased (prop.forallc gx f forallp) = vc.univ gx forallp.erased, by unfold prop.erased,
        show σ' ⊨ prop.erased (prop.forallc gx f forallp), from this.symm ▸ h9
      ),

      have h3: σ' ⊨ (prop.erased (term.unop unop.isFunc f) && prop.erased (prop.forallc gx f forallp)),
      from valid_env.and h1 h2,
      have prop.erased (prop.and (term.unop unop.isFunc f) (prop.forallc gx f forallp))
         = prop.erased (term.unop unop.isFunc f) && prop.erased (prop.forallc gx f forallp),
      by unfold prop.erased,
      have h4: σ' ⊨ prop.erased (term.unop unop.isFunc f && prop.forallc gx f forallp),
      from this.symm ▸ h3,
      have (spec.func f gx R' S').to_prop =
           (term.unop unop.isFunc f) && (prop.forallc gx f forallp), by unfold spec.to_prop,
      have σ' ⊨ prop.erased (spec.func f gx R' S'), from this.symm ▸ h4,
      have h5: σ' ⊨ ((Q₁ && (f ≡ value.func g gx R S e σ₂)).erased && prop.erased (spec.func f gx R' S')),
      from valid_env.and h0 this,
      have prop.erased (prop.and (Q₁ && (f ≡ value.func g gx R S e σ₂)) (spec.func f gx R' S'))
         = prop.erased (Q₁ && (f ≡ value.func g gx R S e σ₂)) && prop.erased (spec.func f gx R' S'),
      by unfold prop.erased,
      show σ' ⊨ (Q₁ && (f ≡ value.func g gx R S e σ₂) && (spec.func f gx R' S')).erased,
      from this.symm ▸ h5
    )}
  end

lemma env_translation_valid {H: callhistory} {P: prop} {σ: env}:
  (⊢ σ: P) → σ ⊨ (↑H && P).instantiated_n :=
  assume env_verified: (⊢ σ : P),
  have h1: σ ⊨ prop.instantiated ↑H, from history_valid σ,
  have σ ⊨ P.erased, from env_translation_erased_valid env_verified,
  have h2: σ ⊨ P.instantiated, from valid_env.instantiated_of_erased this,
  have σ ⊨ (prop.instantiated ↑H && P.instantiated), from valid_env.and h1 h2,
  have σ ⊨ (↑H && P).instantiated, from valid_env.instantiated_and this,
  show σ ⊨ (↑H && P).instantiated_n, from valid_env.instantiated_n_of_instantiated this

lemma consequent_of_H_P {H: callhistory} {σ: env} {P Q: prop}:
  (⊢ σ: P) → ⟪prop.implies (↑H && P) Q⟫ → no_instantiations Q → σ ⊨ Q.erased :=
  assume env_verified: (⊢ σ : P),
  assume impl_vc: ⟪prop.implies (↑H && P) Q⟫,
  assume : no_instantiations Q,
  have h1: (prop.implies (↑H && P) Q).instantiated = vc.or (↑H && P).not.instantiated Q.erased,
  from or_dist_of_no_instantiations this,
  have h2: (↑H && P).not.instantiated = (↑H && P).instantiated_n.not, from not_dist_instantiated,
  have σ ⊨ (prop.implies (↑H && P) Q).instantiated, from impl_vc σ,
  have σ ⊨ vc.or (↑H && P).instantiated_n.not Q.erased, from h2 ▸ h1 ▸ this,
  have h4: σ ⊨ vc.implies (↑H && P).instantiated_n Q.erased, from this,
  have σ ⊨ (↑H && P).instantiated_n, from env_translation_valid env_verified,
  show σ ⊨ Q.erased, from valid_env.mp h4 this

lemma env_translation_call_valid {H: callhistory} {P: prop} {σ: env} {f x: var}:
  (⊢ σ: P) → σ ⊨ (↑H && P && prop.call f x).instantiated_n :=
  assume env_verified: (⊢ σ : P),
  have h1: σ ⊨ prop.instantiated ↑H, from history_valid σ,
  have σ ⊨ P.erased, from env_translation_erased_valid env_verified,
  have h2: σ ⊨ P.instantiated, from valid_env.instantiated_of_erased this,
  have σ ⊨ (prop.instantiated ↑H && P.instantiated), from valid_env.and h1 h2,
  have h3: σ ⊨ (↑H && P).instantiated, from valid_env.instantiated_and this,
  have h4: ⊨ value.true, from valid.tru,
  have term.subst_env σ value.true = value.true, from term.subst_env.value,
  have h5: ⊨ term.subst_env σ value.true, from this.symm ▸ h4,
  have vc.subst_env σ value.true = vc.term (term.subst_env σ value.true), from vc.subst_env.term,
  have h6: σ ⊨ value.true, from this.symm ▸ h5,
  have (prop.call f x).erased = vc.term value.true, by unfold prop.erased,
  have σ ⊨ (prop.call f x).erased, from this.symm ▸ h6,
  have σ ⊨ (prop.call f x).instantiated, from valid_env.instantiated_of_erased this,
  have σ ⊨ ((↑H && P).instantiated && (prop.call f x).instantiated), from valid_env.and h3 this,
  have σ ⊨ (↑H && P && prop.call f x).instantiated, from valid_env.instantiated_and this,
  show σ ⊨ (↑H && P && prop.call f x).instantiated_n, from valid_env.instantiated_n_of_instantiated this

lemma consequent_of_H_P_call {H: callhistory} {σ: env} {P Q: prop} {f x: var}:
  (⊢ σ: P) → ⟪prop.implies (↑H && P && prop.call f x) Q⟫ → no_instantiations Q → σ ⊨ Q.erased :=
  assume env_verified: (⊢ σ : P),
  assume impl_vc: ⟪prop.implies (↑H && P && prop.call f x) Q⟫,
  assume : no_instantiations Q,
  have h1: (prop.implies (↑H && P && prop.call f x) Q).instantiated
         = vc.or (↑H && P && prop.call f x).not.instantiated Q.erased,
  from or_dist_of_no_instantiations this,
  have h2: (↑H && P && prop.call f x).not.instantiated = (↑H && P && prop.call f x).instantiated_n.not,
  from not_dist_instantiated,
  have σ ⊨ (prop.implies (↑H && P && prop.call f x) Q).instantiated, from impl_vc σ,
  have σ ⊨ vc.or (↑H && P && prop.call f x).instantiated_n.not Q.erased, from h2 ▸ h1 ▸ this,
  have h4: σ ⊨ vc.implies (↑H && P && prop.call f x).instantiated_n Q.erased, from this,
  have σ ⊨ (↑H && P && prop.call f x).instantiated_n, from env_translation_call_valid env_verified,
  show σ ⊨ Q.erased, from valid_env.mp h4 this

lemma exp.progress {H: callhistory} {P: prop} {Q: propctx} {e: exp} {σ: env}:
                   (⊢ σ: P) → (H && P ⊢ e: Q) → is_value (σ, e) ∨ ∃c s', (σ, e) ⟶ c, s'
:=
  assume env_verified: (⊢ σ : P),
  assume e_verified: (H && P ⊢ e : Q),
  show is_value (σ, e) ∨ ∃c s', (σ, e) ⟶ c, s', by begin
    cases e_verified,
    case exp.vcgen.tru x e' { from
      let s: stack := (σ, lett x = true in e') in
      have s ⟶ nop, (σ[x↦value.true], e'), from step.tru,
      have ∃c s', s ⟶ c, s', from exists.intro nop (exists.intro (σ[x↦value.true], e') this),
      show is_value s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },
    case exp.vcgen.fals x e' { from
      let s: stack := (σ, letf x = false in e') in
      have s ⟶ nop, (σ[x↦value.false], e'), from step.fals,
      have ∃c s', s ⟶ c, s', from exists.intro nop (exists.intro (σ[x↦value.false], e') this),
      show is_value s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },
    case exp.vcgen.num x n e' { from
      let s: stack := (σ, letn x = n in e') in
      have s ⟶ nop, (σ[x↦value.num n], e'), from step.num,
      have ∃c s', s ⟶ c, s', from exists.intro nop (exists.intro (σ[x↦value.num n], e') this),
      show is_value s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },
    case exp.vcgen.func f x R S e₁ e₂ { from
      let s: stack := (σ, letf f[x] req R ens S {e₁} in e₂) in
      have s ⟶ nop, (σ[f↦value.func f x R S e₁ σ], e₂), from step.closure,
      have ∃c s', s ⟶ c, s', from exists.intro nop (exists.intro (σ[f↦value.func f x R S e₁ σ], e₂) this),
      show is_value s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },
    case exp.vcgen.unop op x y e' Q' x_free_in_P _ e'_verified vc_valid { from
      let s: stack := (σ, letop y = op[x] in e') in
      let ⟨v, env_has_x⟩ := (val_of_free_in_hist_env env_verified x_free_in_P) in
      have no_instantiations (prop.pre₁ op x), from no_instantiations.pre₁,
      have σ ⊨ (prop.pre₁ op x).erased, from consequent_of_H_P env_verified vc_valid this,
      have h1: ⊨ vc.subst_env σ (vc.pre₁ op x), from this,
      have vc.subst_env σ (vc.pre₁ op x) = vc.pre₁ op (term.subst_env σ x), from vc.subst_env.pre₁,
      have ⊨ vc.pre₁ op (term.subst_env σ x), from this ▸ h1,
      have x_from_env: term.subst_env σ x = v, from (term.subst_env.var.right v).mp env_has_x,
      have ⊨ vc.pre₁ op v, from x_from_env ▸ this,
      have option.is_some (unop.apply op v), from valid.pre₁.mpr this,
      have (∃v', unop.apply op v = some v'), from exists_of_is_some this,
      let ⟨v', op_v_is_v'⟩ := this in
      have s ⟶ nop, (σ[y↦v'], e'), from step.unop env_has_x op_v_is_v',
      have ∃c s', s ⟶ c, s', from exists.intro nop (exists.intro (σ[y↦v'], e') this),
      show is_value s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },
    case exp.vcgen.binop op x y z e' Q' x_free_in_P y_free_in_P _ e'_verified vc_valid { from
      let s: stack := (σ, letop2 z = op[x,y] in e') in
      let ⟨vx, env_has_x⟩ := (val_of_free_in_hist_env env_verified x_free_in_P) in
      let ⟨vy, env_has_y⟩ := (val_of_free_in_hist_env env_verified y_free_in_P) in
      have no_instantiations (prop.pre₂ op x y), from no_instantiations.pre₂,
      have σ ⊨ (prop.pre₂ op x y).erased, from consequent_of_H_P env_verified vc_valid this,
      have h1: ⊨ vc.subst_env σ (vc.pre₂ op x y), from this,
      have vc.subst_env σ (vc.pre₂ op x y) = vc.pre₂ op (term.subst_env σ x) (term.subst_env σ y),
      from vc.subst_env.pre₂,
      have h2: ⊨ vc.pre₂ op (term.subst_env σ x) (term.subst_env σ y), from this ▸ h1,
      have term.subst_env σ x = vx, from (term.subst_env.var.right vx).mp env_has_x,
      have h3: ⊨ vc.pre₂ op vx (term.subst_env σ y), from this ▸ h2,
      have term.subst_env σ y = vy, from (term.subst_env.var.right vy).mp env_has_y,
      have ⊨ vc.pre₂ op vx vy, from this ▸ h3,
      have option.is_some (binop.apply op vx vy), from valid.pre₂.mpr this,
      have (∃v', binop.apply op vx vy = some v'), from exists_of_is_some this,
      let ⟨v', op_v_is_v'⟩ := this in
      have s ⟶ nop, (σ[z↦v'], e'), from step.binop env_has_x env_has_y op_v_is_v',
      have ∃c s', s ⟶ c, s', from exists.intro nop (exists.intro (σ[z↦v'], e') this),
      show is_value s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },
    case exp.vcgen.app y f x e' Q' f_free_in_P x_free_in_P _ e'_verified vc_valid { from
      let s: stack := (σ, letapp y = f [x] in e') in
      let ⟨vf, env_has_f⟩ := (val_of_free_in_hist_env env_verified f_free_in_P) in
      let ⟨vx, env_has_x⟩ := (val_of_free_in_hist_env env_verified x_free_in_P) in
      have h1: no_instantiations (term.unop unop.isFunc f), from no_instantiations.term,
      have h2: no_instantiations (prop.pre f x), from no_instantiations.pre,
      have no_instantiations (↑(term.unop unop.isFunc f) && prop.pre f x), from no_instantiations.and h1 h2,
      have h3: σ ⊨ (↑(term.unop unop.isFunc f) && prop.pre f x).erased,
      from consequent_of_H_P_call env_verified vc_valid this,
      have (prop.and (prop.term (term.unop unop.isFunc f)) (prop.pre f x)).erased
         = (prop.term (term.unop unop.isFunc f)).erased && (prop.pre f x).erased, by unfold prop.erased,
      have σ ⊨ ((prop.term (term.unop unop.isFunc f)).erased && (prop.pre f x).erased), from this ▸ h3,
      have h4: ⊨ vc.subst_env σ ((prop.term (term.unop unop.isFunc f)).erased && (prop.pre f x).erased), from this,
      have vc.subst_env σ ((prop.term (term.unop unop.isFunc f)).erased && (prop.pre f x).erased)
         = vc.subst_env σ ((prop.term (term.unop unop.isFunc f)).erased) && vc.subst_env σ ((prop.pre f x).erased),
      from vc.subst_env.and,
      have ⊨ (vc.subst_env σ ((prop.term (term.unop unop.isFunc f)).erased) && vc.subst_env σ ((prop.pre f x).erased)),
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
      have ∃(g gx: var) (gR gS: spec) (ge: exp) (gσ: env), vf = value.func g gx gR gS ge gσ,
      from unop.isFunc.inv this,
      let ⟨g, gx, gR, gS, ge, gσ, vf_is_g⟩ := this in
      have some_vf_is_g: some vf = ↑(value.func g gx gR gS ge gσ), from some.inj.inv vf_is_g,
      have σ f = value.func g gx gR gS ge gσ, from eq.trans env_has_f some_vf_is_g,
      let s': stack := (gσ[g↦value.func g gx gR gS ge gσ][gx↦vx], ge) · [σ, let y = f[x] in e'] in
      have s ⟶ nop, s', from step.app this env_has_x,
      have ∃c s', s ⟶ c, s', from exists.intro nop (exists.intro s' this),
      show is_value s ∨ ∃c s', s ⟶ c, s', from or.inr this
    },
    case exp.vcgen.ite x e₂ e₁ Q₁ Q₂ x_free_in_P _ _ vc_valid { from
      let s: stack := (σ, exp.ite x e₁ e₂) in
      let ⟨v, env_has_x⟩ := (val_of_free_in_hist_env env_verified x_free_in_P) in
      have no_instantiations (term.unop unop.isBool x), from no_instantiations.term,
      have h1: σ ⊨ (prop.term (term.unop unop.isBool x)).erased,
      from consequent_of_H_P env_verified vc_valid this,
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
        have s ⟶ nop, (σ, e₁), from step.ite_true this,
        have ∃c s', s ⟶ c, s', from exists.intro nop (exists.intro (σ, e₁) this),
        show is_value s ∨ ∃c s', s ⟶ c, s', from or.inr this
      ) (
        assume : v = value.false,
        have some v = some value.false, from some.inj.inv this,
        have σ x = value.false, from eq.trans env_has_x this,
        have s ⟶ nop, (σ, e₂), from step.ite_false this,
        have ∃c s', s ⟶ c, s', from exists.intro nop (exists.intro (σ, e₂) this),
        show is_value s ∨ ∃c s', s ⟶ c, s', from or.inr this
      )
    },
    case exp.vcgen.return x x_free_in_P { from
      let s: stack := (σ, exp.return x) in
      have s_is_return: s = (σ, exp.return x), from rfl,
      let ⟨v, env_has_x⟩ := (val_of_free_in_hist_env env_verified x_free_in_P) in
      have is_value_s: is_value s = (∃(σ': env) (x': var) (v: value), s = (σ', exp.return x') ∧ (σ' x' = v)),
      by unfold is_value,
      have (∃(σ': env) (x': var) (v: value), s = (σ', exp.return x') ∧ (σ' x' = v)),
      from exists.intro σ (exists.intro x (exists.intro v ⟨s_is_return, env_has_x⟩)),
      have is_value s, from is_value_s ▸ this,
      show is_value s ∨ ∃c s', s ⟶ c, s', from or.inl this
    }
  end

theorem progress(H: callhistory) (s: stack): (H ⊢ₛ s) → is_value s ∨ ∃c s', s ⟶ c, s'
:=
  assume s_verified: H ⊢ₛ s,
  begin
    induction s_verified,
    case stack.vcgen.top σ e Q P H env_verified e_verified { from
      show is_value (σ, e) ∨ ∃c s', (σ, e) ⟶ c, s', from exp.progress env_verified e_verified
    },
    case stack.vcgen.cons H P s' σ σ' f g x y fx R S e vₓ Q s'_verified _ g_is_func x_is_v _ cont _ _ ih { from
      let s := (s' · [σ, let y = g[x] in e]) in
      have s_cons: s = (s' · [σ, let y = g[x] in e]), from rfl,
      or.elim ih
      ( -- step return
        assume s'_is_value: is_value s',
        let ⟨σ₂, z, v, ⟨s'_return, env2_has_z⟩⟩ := s'_is_value in
        have s_return_cons: s = ((σ₂, exp.return z) · [σ, let y = g[x] in e]), from s'_return ▸ s_cons,
        have s ⟶ call f fx R S e σ' vₓ, (σ[y↦v], e),
        from s_return_cons.symm ▸ (step.return env2_has_z g_is_func x_is_v),
        have ∃s', s ⟶ call f fx R S e σ' vₓ, s', from exists.intro (σ[y↦v], e) this,
        have ∃c s', s ⟶ c, s', from exists.intro (call f fx R S e σ' vₓ) this,
        show is_value s ∨ ∃c s', s ⟶ c, s', from or.inr this
      )
      ( -- step ctx
        assume s'_can_step: ∃c s'', s' ⟶ c, s'',
        let ⟨c, s'', s'_steps⟩ := s'_can_step in
        have s ⟶ c, (s'' · [σ, let y = g[x] in e]), from step.ctx s'_steps,
        have ∃s', s ⟶ c, s', from exists.intro (s'' · [σ, let y = g[x] in e]) this,
        have ∃c s', s ⟶ c, s', from exists.intro c this,
        show is_value s ∨ ∃c s', s ⟶ c, s', from or.inr this
      )
    }
  end
