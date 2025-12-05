import Analysis.Utils
import Analysis.Cauchy

-- open Cauchy (Cauchy)
instance : Cauchy.cauchy_req Rat where

def Real.QCauchy := Cauchy Rat

def Real.eqv (c1 c2 : QCauchy) : Prop := sorry


namespace Real.eqv

    protected theorem refl (c : QCauchy) : eqv c c := sorry

    protected theorem symm {c1 c2 : QCauchy} : eqv c1 c2 → eqv c2 c1 :=
      sorry
  /-- An equivalence relation is transitive: `r x y` and `r y z` implies `r x z` -/
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
