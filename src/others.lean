-- other minor lemmas related to verification but not included in the other files

import .definitions2

lemma unchanged_of_apply_termctx_without_hole {t tt: term}:
      t.to_termctx tt = t :=
  begin
    induction t with v y unop t₁ ih₁ binop t₂ t₃ ih₂ ih₃ t₄ t₅ ih₄ ih₅,

    show (termctx.apply (term.to_termctx (term.value v)) tt = term.value v), by begin
      unfold term.to_termctx,
      unfold termctx.apply
    end,

    show (termctx.apply (term.to_termctx (term.var y)) tt = term.var y), by begin
      unfold term.to_termctx,
      unfold termctx.apply
    end,

    show (termctx.apply (term.to_termctx (term.unop unop t₁)) tt = term.unop unop t₁), by begin
      unfold term.to_termctx,
      unfold termctx.apply,
      congr,
      from ih₁
    end,

    show (termctx.apply (term.to_termctx (term.binop binop t₂ t₃)) tt = term.binop binop t₂ t₃), by begin
      unfold term.to_termctx,
      unfold termctx.apply,
      congr,
      from ih₂,
      from ih₃
    end,

    show (termctx.apply (term.to_termctx (term.app t₄ t₅)) tt = term.app t₄ t₅), by begin
      unfold term.to_termctx,
      unfold termctx.apply,
      congr,
      from ih₄,
      from ih₅
    end
  end

lemma unchanged_of_apply_propctx_without_hole {P: prop} {t: term}:
      P.to_propctx t = P :=
  begin
    change (propctx.apply (prop.to_propctx P) t = P),
    induction P,

    case prop.term t₁ {
      unfold prop.to_propctx,
      unfold propctx.apply,
      congr,
      from unchanged_of_apply_termctx_without_hole
    },

    case prop.not P₁ ih {
      unfold prop.to_propctx,
      unfold propctx.apply,
      congr,
      from ih
    },

    case prop.and P₁ P₂ ih₁ ih₂ {
      unfold prop.to_propctx,
      change (propctx.apply (propctx.and (prop.to_propctx P₁) (prop.to_propctx P₂)) t = prop.and P₁ P₂),
      unfold propctx.apply,
      congr,
      from ih₁,
      from ih₂
    },

    case prop.or P₁ P₂ ih₁ ih₂ {
      unfold prop.to_propctx,
      change (propctx.apply (propctx.or (prop.to_propctx P₁) (prop.to_propctx P₂)) t = prop.or P₁ P₂),
      unfold propctx.apply,
      congr,
      from ih₁,
      from ih₂
    },

    case prop.pre t₁ t₂ {
      unfold prop.to_propctx,
      unfold propctx.apply,
      congr,
      from unchanged_of_apply_termctx_without_hole,
      from unchanged_of_apply_termctx_without_hole
    },

    case prop.pre₁ op t₁ {
      unfold prop.to_propctx,
      unfold propctx.apply,
      congr,
      from unchanged_of_apply_termctx_without_hole
    },

    case prop.pre₂ op t₁ t₂ {
      unfold prop.to_propctx,
      unfold propctx.apply,
      congr,
      from unchanged_of_apply_termctx_without_hole,
      from unchanged_of_apply_termctx_without_hole
    },

    case prop.post t₁ t₂ {
      unfold prop.to_propctx,
      unfold propctx.apply,
      congr,
      from unchanged_of_apply_termctx_without_hole,
      from unchanged_of_apply_termctx_without_hole
    },

    case prop.call t₁ t₂ {
      unfold prop.to_propctx,
      unfold propctx.apply,
      congr,
      from unchanged_of_apply_termctx_without_hole
    },

    case prop.forallc y P₁ ih {
      unfold prop.to_propctx,
      unfold propctx.apply,
      congr,
      from ih
    },

    case prop.exis y P₁ ih {
      unfold prop.to_propctx,
      unfold propctx.apply,
      congr,
      from ih
    }
  end

lemma vc.term.inj.inv {t₁ t₂: term}: (t₁ = t₂) → (vc.term t₁ = vc.term t₂) :=
  begin
    assume h1,
    congr,
    from h1
  end

lemma vc.not.inj.inv {P Q: vc}: (P = Q) → (vc.not P = vc.not Q) :=
  begin
    assume h1,
    congr,
    from h1
  end

lemma vc.and.inj.inv {P₁ P₂ P₃ P₄: vc}: (P₁ = P₂) → (P₃ = P₄) → (vc.and P₁ P₃ = vc.and P₂ P₄) :=
  begin
    assume h1,
    assume h2,
    congr,
    from h1,
    from h2
  end

lemma vc.or.inj.inv {P₁ P₂ P₃ P₄: vc}: (P₁ = P₂) → (P₃ = P₄) → (vc.or P₁ P₃ = vc.or P₂ P₄) :=
  begin
    assume h1,
    assume h2,
    congr,
    from h1,
    from h2
  end

lemma vc.pre.inj.inv {t₁ t₂ t₃ t₄: term}: (t₁ = t₂) → (t₃ = t₄) → (vc.pre t₁ t₃ = vc.pre t₂ t₄) :=
  begin
    assume h1,
    assume h2,
    congr,
    from h1,
    from h2
  end

lemma vc.pre₁.inj.inv {t₁ t₂: term} {op: unop}: (t₁ = t₂) → (vc.pre₁ op t₁ = vc.pre₁ op t₂) :=
  begin
    assume h1,
    congr,
    from h1
  end

lemma vc.pre₂.inj.inv {t₁ t₂ t₃ t₄: term} {op: binop}: (t₁ = t₂) → (t₃ = t₄) → (vc.pre₂ op t₁ t₃ = vc.pre₂ op t₂ t₄) :=
  begin
    assume h1,
    assume h2,
    congr,
    from h1,
    from h2
  end

lemma vc.post.inj.inv {t₁ t₂ t₃ t₄: term}: (t₁ = t₂) → (t₃ = t₄) → (vc.post t₁ t₃ = vc.post t₂ t₄) :=
  begin
    assume h1,
    assume h2,
    congr,
    from h1,
    from h2
  end

lemma vc.univ.inj.inv {P Q: vc} {x: var}: (P = Q) → (vc.univ x P = vc.univ x Q) :=
  begin
    assume h1,
    congr,
    from h1
  end
