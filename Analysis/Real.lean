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

  @[refl] protected theorem refl (c : QCauchy) : eqv c c := by
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
    let c := (- to_conv h).h
    simpa only [
      Converge.neg_def, Converge.neg,
      AddCommGroup.neg_sub, AddCommGroup.neg_zero] using c

  protected theorem trans {c1 c2 c3 : QCauchy} :
    eqv c1 c2 → eqv c2 c3 → eqv c1 c3 := by
    intro h1 h2
    apply eqv.mk
    let c := (to_conv h1 + to_conv h2).h
    simpa only [
      Converge.add_def, Converge.add, AddCommGroup.add_diff_eq_add_sub,
      AddCommGroup.sub_add_cancel, AddCommMonoid.add_zero
    ] using c

  private theorem is_equivalence : Equivalence eqv := {
    refl := eqv.refl,
    symm := eqv.symm,
    trans := eqv.trans
  }

  instance realSetoid : Setoid QCauchy where
    r     := eqv
    iseqv := is_equivalence

  theorem eqv_def {a b : QCauchy} : (a ≈ b) = eqv a b := rfl
  -- #check Setoid.

end Real.eqv

def Real : Type := Quotient Real.eqv.realSetoid

namespace Real

  def mk (a : QCauchy) : Real := Quotient.mk' a

  private def add_fn: QCauchy → QCauchy → Real :=
    fun a b => Real.mk (a + b)

  private theorem add_respects (a1 b1 a2 b2 : QCauchy) :
    (a1 ≈ a2) → (b1 ≈ b2) → (add_fn a1 b1 = add_fn a2 b2) := by
    intro ha hb
    let c := (eqv.to_conv ha + eqv.to_conv hb).h
    simp only [Converge.add_def, Converge.add] at c
    simp only [add_fn, Cauchy.add_def, Cauchy.add]
    apply Quotient.sound
    apply eqv.mk
    simpa only [
      misc.sum_sub_sum_eq_dif_add_dif,
      AddCommMonoid.add_zero] using c

  protected def add: Real → Real → Real :=
    Quotient.lift₂ add_fn add_respects

  instance : Add Real where
    add := Real.add

  theorem add_def {a b : Real} : a + b = Real.add a b := rfl

  protected def zero : Real := Real.mk 0

  instance : Zero Real where
    zero := Real.zero

  theorem zero_def : (0 : Real) = Real.zero := rfl

  theorem add_zero (a : Real) : a + 0 = a := by
    rw [add_def]
    have ⟨c, hc⟩ := Quotient.exists_rep a
    simp only [Real.add, ← hc]
    apply Quotient.sound
    rw [AddCommMonoid.add_zero, eqv.eqv_def]

  theorem add_comm (a b : Real) : a + b = b + a := by
    repeat rw [add_def]
    have ⟨a, ha⟩ := Quotient.exists_rep a
    have ⟨b, hb⟩ := Quotient.exists_rep b
    simp only [Real.add, ← ha ,← hb]
    apply Quotient.sound
    rw [AddCommMonoid.add_comm, eqv.eqv_def]

  theorem add_assoc (a b c : Real) : (a + b) + c = a + (b + c) := by
    repeat rw [add_def]
    have ⟨a, ha⟩ := Quotient.exists_rep a
    have ⟨b, hb⟩ := Quotient.exists_rep b
    have ⟨c, hc⟩ := Quotient.exists_rep c
    simp only [Real.add, ← ha, ← hb, ← hc]
    apply Quotient.sound
    rw [AddCommMonoid.add_assoc, eqv.eqv_def]

  private def neg_fn : QCauchy → Real :=
    fun a => Real.mk (-a)

  private theorem neg_respects (a b : QCauchy) :
    a ≈ b → neg_fn a = neg_fn b := by
      intro h
      replace h := (-eqv.to_conv h).h
      simp only [Converge.neg_def, Converge.neg] at h
      simp only [neg_fn, Cauchy.neg_def, Cauchy.neg]
      apply Quotient.sound
      apply eqv.mk
      rwa [← AddCommGroup.neg_sub', ← AddCommGroup.neg_zero]

  protected def neg : Real → Real := Quotient.lift neg_fn neg_respects

  instance : Neg Real where
    neg := Real.neg

  theorem neg_def {a : Real} : -a = Real.neg a := rfl

  instance : AddCommMonoid Real where
    add_zero := add_zero
    add_comm := add_comm
    add_assoc := add_assoc

  protected def sub : Real → Real → Real :=
    fun a => (fun b => Real.add a (Real.neg b))

  instance : Sub Real where
    sub := Real.sub

  theorem sub_def (a b : Real) : a - b = Real.sub a b := rfl

  theorem neg_add_cancel (a : Real) : -a + a = 0 := by
    rw [add_def, neg_def, zero_def]
    have ⟨a, ha⟩ := Quotient.exists_rep a
    simp only [Real.add, Real.neg, Real.zero, ← ha]
    apply Quotient.sound
    rw [AddCommGroup.neg_add_cancel, eqv.eqv_def]

  theorem sub_eq_add_neg (a b : Real) : a - b = a + -b := by
    rw [add_def, sub_def, neg_def]
    have ⟨a, ha⟩ := Quotient.exists_rep a
    have ⟨b, hb⟩ := Quotient.exists_rep b
    simp only [Real.sub, Real.neg, Real.add, ← ha , ← hb]

  instance : AddCommGroup Real where
    neg_add_cancel := neg_add_cancel
    sub_eq_add_neg := sub_eq_add_neg


end Real
