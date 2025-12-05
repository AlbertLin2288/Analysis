open Classical
open Lean.Grind (AddCommGroup AddCommMonoid OrderedAdd)
open Std (IsLinearOrder IsPreorder IsLinearPreorder)


namespace Lean.Grind.AddCommGroup
  open Lean.Grind.AddCommMonoid

  variable  {M : Type u} [AddCommGroup M]

  theorem sub_zero (a : M) : a - 0 = a := by
    simp [sub_eq_add_neg, neg_zero, add_zero]

  theorem add_diff_eq_add_sub (a b c : M):
    a + (b - c) = a + b - c := by simp [sub_eq_add_neg, add_assoc]

  theorem sub_diff_eq_add_sub (a b c : M):
    a - (b - c) = a - b + c := by
      simp [neg_add,sub_eq_add_neg, add_assoc, neg_neg]

end Lean.Grind.AddCommGroup


class tp1 (α : Type) extends
  AddCommGroup α, LE α, IsLinearOrder α, OrderedAdd α

noncomputable def abs {α : Type} [tp1 α] : α → α :=
  fun (a : α) => if (a ≤ 0) then (-a) else a

namespace abs
  variable {α : Type} [tp1 α]

  theorem neg_le_zero_iff_ge_zero (a : α) : (-a) ≤ 0 ↔ 0 ≤ a := by
    have h := @OrderedAdd.neg_le_iff _ _ _ _ _ a 0
    rw [AddCommGroup.neg_zero] at h; exact h

  theorem neg_ge_zero_iff_le_zero (a : α) : a ≤ 0 ↔ 0 ≤ (-a) := by
    have h := neg_le_zero_iff_ge_zero (-a)
    rw [AddCommGroup.neg_neg] at h; exact h

  theorem abs_ge_zero: ∀a : α, 0 ≤ abs a := by
    intro a
    unfold abs
    split
    case isTrue h => exact (neg_ge_zero_iff_le_zero a).mp h
    case isFalse h =>
      cases IsLinearOrder.le_total a 0 with
        | inl ha => contradiction
        | inr ha' => exact ha'

  theorem abs_zero_iff_zero {a : α} : abs a = 0 ↔ a = 0 := by
    apply Iff.intro
    case mp =>
      unfold abs
      split
      case isFalse h => intro;assumption
      case isTrue h => exact (AddCommGroup.neg_eq_zero a).mp
    case mpr =>
      intro h
      rw [h]
      unfold abs
      split <;> simp [AddCommGroup.neg_zero]

  theorem abs_neg_eq_abs (a : α): abs (-a) = abs a := by
    unfold abs
    split
    case isTrue h =>
      replace h := OrderedAdd.neg_le_iff.mp h
      rw [AddCommGroup.neg_zero] at h
      split
      case isTrue h'=> simp [Std.le_antisymm h' h, AddCommGroup.neg_zero]
      case isFalse h' => simp [AddCommGroup.neg_neg]
    case isFalse h =>
      split
      case isTrue => rfl
      case isFalse h' =>
        cases @Std.le_total α _ _ a 0
        case inl hl => contradiction
        case inr hr => replace hr := (neg_le_zero_iff_ge_zero a).mpr hr;contradiction

  theorem le_abs (a : α) : a ≤ abs a := by
    unfold abs;split
    case isTrue h =>
      have h' : 0 ≤ -a := (neg_ge_zero_iff_le_zero a).mp h
      exact IsPreorder.le_trans a 0 (-a) h h'
    case isFalse => exact IsPreorder.le_refl a

  theorem neg_le_abs (a : α) : (-a) ≤ abs a := by
    rw [← abs_neg_eq_abs a]
    exact le_abs (-a)





  theorem abs_sum_le_sum_abs {a b : α} :
    abs (a + b) ≤ abs a + abs b := by
      rw [abs]
      split
      . rw [AddCommGroup.neg_add]
        exact OrderedAdd.add_le_add (neg_le_abs a) (neg_le_abs b)
      . exact OrderedAdd.add_le_add (le_abs a) (le_abs b)

  theorem abs_dif_le_sum_abs {α : Type} [tp1 α] {a b : α} :
    abs (a - b) ≤ abs a + abs b := by
      rw [AddCommGroup.sub_eq_add_neg, abs]
      split
      . rw [AddCommGroup.neg_add, AddCommGroup.neg_neg]
        exact OrderedAdd.add_le_add (neg_le_abs a) (le_abs b)
      . exact OrderedAdd.add_le_add (le_abs a) (neg_le_abs b)


end abs


namespace misc
  theorem ge_max_imp_ge_left_right {m n : Nat} {N1 N2 N : Nat} :
    N = max N1 N2 → N ≤ m ∧ N ≤ n → (N1 ≤ m ∧ N1 ≤ n) ∧ (N2 ≤ m ∧ N2 ≤ n) := by
      intro hmax ⟨hm, hn⟩
      rw [hmax] at hm hn
      apply And.intro
      case left =>
        apply And.intro
        apply Std.le_trans Std.left_le_max hm
        apply Std.le_trans Std.left_le_max hn
      case right =>
        apply And.intro
        apply Std.le_trans Std.right_le_max hm
        apply Std.le_trans Std.right_le_max hn

  theorem sum_sub_sum_eq_dif_add_dif {α : Type} [AddCommGroup α] {a1 a2 b1 b2 : α}:
    (a1 + a2) - (b1 + b2) = (a1 - b1) + (a2 - b2) := by
      rw [
        AddCommGroup.sub_eq_add_neg,
        AddCommGroup.neg_add,
        AddCommMonoid.add_assoc,
        AddCommMonoid.add_comm a2 (-b1 + -b2),
        ← AddCommMonoid.add_assoc,
        ← AddCommMonoid.add_assoc,
        AddCommMonoid.add_assoc,
        AddCommMonoid.add_comm (-b2) a2,
        ← AddCommGroup.sub_eq_add_neg,
        ← AddCommGroup.sub_eq_add_neg
      ]

end misc
