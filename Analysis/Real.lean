import Analysis.Utils
import Analysis.Cauchy

open Lean.Grind (AddCommGroup AddCommMonoid OrderedAdd)
open Std (IsLinearOrder IsPreorder IsLinearPreorder)

-- open Cauchy (Cauchy)
instance : Seq_type Rat where

@[reducible] def Real.QCauchy := Cauchy Rat
@[reducible] def Real.QConverge := Converge Rat


-- def Real.eqv (c1 c2 : QCauchy) : Prop := Converge.converge (c1.s - c2.s) 0

structure Real.eqv (c1 c2 : QCauchy) : Prop where
  h : Converge.converge (c1.s - c2.s) 0

variable (a b :Real.QCauchy)

#print Real.eqv

namespace Real.eqv

  instance to_conv {c1 c2 : QCauchy} (e : eqv c1 c2): QConverge :=
    Converge.mk (c1.s - c2.s) 0 e.h

  -- instance QConverge : {c1 c2 : QCauchy} (e : eqv c1 c2): :=
  --   Converge.mk (c1.s - c2.s) 0 e.h

  protected theorem refl (c : QCauchy) : eqv c c := by
    apply eqv.mk
    rw [AddCommGroup.sub_eq_zero_iff.mpr (Eq.refl c.s)]
    unfold Converge.converge
    intro ε hε0;exists 0;intros;
    simp only [Sequ.zero_def]
    unfold Sequ.zero
    simp only [AddCommGroup.sub_zero, abs.abs_zero_iff_zero.mpr,hε0]

    protected theorem symm {c1 c2 : QCauchy} : eqv c1 c2 → eqv c2 c1 := by
      intro h
      apply eqv.mk
      -- let (eq:=hm) c' := - Converge.mk (c1.s-c2.s) 0 h
      let (eq:=hm) c' := - to_conv h
      rw [Converge.neg_def] at hm
      simp only [Converge.neg] at hm
      let b := c'.h
      simp only [hm, AddCommGroup.neg_sub, AddCommGroup.neg_zero] at b
      assumption



    protected theorem trans {c1 c2 c3 : QCauchy} :
      eqv c1 c2 → eqv c2 c3 → eqv c1 c3 :=
      sorry

    private theorem is_equivalence : Equivalence eqv := {
      refl := eqv.refl,
      symm := eqv.symm,
      trans := eqv.trans
    }

    instance realSetoid : Setoid QCauchy where
      r     := eqv
      iseqv := is_equivalence

end Real.eqv

def Real : Type := Quotient Real.eqv.realSetoid

namespace Real

end Real
