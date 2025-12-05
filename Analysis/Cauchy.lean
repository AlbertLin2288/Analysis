import Analysis.Utils

open Classical
open Lean.Grind (AddCommGroup AddCommMonoid OrderedAdd)
open Std (IsLinearOrder IsPreorder IsLinearPreorder)

open abs
open misc

def Cauchy.Sequ (α : Type) : Type := Nat → α

class Cauchy.cauchy_req (α : Type) extends
  Lean.Grind.AddCommGroup α,
  LE α, LT α,
  Std.IsLinearOrder α, Std.LawfulOrderLT α,
  OrderedAdd α

namespace Cauchy.cauchy_req
  instance inst_tp1 {α : Type} [cauchy_req α] : tp1 α where
end Cauchy.cauchy_req

def Cauchy (α : Type) [Cauchy.cauchy_req α] :=
  Σ' (s : Cauchy.Sequ α), (
    ∀ε : α,
      ε > (0 : α) → ∃N : Nat, ∀(m n : Nat), (m ≥ N ∧ n ≥ N) →
        abs (s m - s n) < ε
  )

namespace Cauchy

  variable {α : Type} [cauchy_req α]

  protected def add: Cauchy α → Cauchy α → Cauchy α := by
    intro ⟨s1, h1⟩ ⟨s2, h2⟩
    let s3 : Sequ α := fun (n : Nat) => (s1 n) + (s2 n)
    apply PSigma.mk
    case fst => exact s3
    intro ε hep
    cases em (∃ε2 : α, 0 < ε2 ∧ ε2 < ε) with
    | inr hne =>
      have hl0 : ∀x : α, x < ε → x ≤ 0 := by
        simp at hne
        intro x hxε
        apply Std.not_lt.mp
        exact imp_not_comm.mp (hne x) hxε
      replace h1 := h1 ε hep
      replace h2 := h2 ε hep
      -- match h1 with  N1 h =>
      let ⟨N1, h1⟩ := h1
      let ⟨N2, h2⟩ := h2
      let (eq := hNeq) N := max N1 N2
      exists N
      intro m n hmn
      have ⟨hN1,hN2⟩ := ge_max_imp_ge_left_right hNeq hmn
      unfold s3
      generalize hd : s1 m + s2 m - (s1 n + s2 n) = d
      replace h1 := hl0 (abs (s1 m - s1 n)) (h1 m n hN1)
      replace h2 := hl0 (abs (s2 m - s2 n)) (h2 m n hN2)
      replace h1 := abs_zero_iff_zero.mp (Std.le_antisymm h1 (abs_ge_zero (s1 m - s1 n)))
      replace h2 := abs_zero_iff_zero.mp (Std.le_antisymm h2 (abs_ge_zero (s2 m - s2 n)))
      -- simp [AddCommGroup.add_assoc,AddCommGroup.add_comm] at hd
      rw [
        sum_sub_sum_eq_dif_add_dif,
        h1, h2, AddCommMonoid.add_zero 0
      ] at hd
      rw [← hd, abs_zero_iff_zero.mpr]
      exact hep;rfl
    | inl he =>
      let ⟨ε1, hε1⟩ := he
      let ⟨hε10, hε1ε⟩ := hε1
      let ε2 := ε - ε1
      have hε20 : 0 < ε2 := by
        unfold ε2;
        rw [← AddCommGroup.add_neg_cancel ε1];
        repeat rw [AddCommGroup.sub_eq_add_neg]
        apply (OrderedAdd.add_lt_left_iff (-ε1)).mp
        exact hε1ε
      -- have hε2ε : ε2 < ε := by
      replace ⟨N1, h1⟩ := h1 ε1 hε10
      replace ⟨N2, h2⟩ := h2 ε2 hε20
      let (eq := hNeq) N := max N1 N2
      exists N
      intro m n hmn
      have ⟨hN1,hN2⟩ := ge_max_imp_ge_left_right hNeq hmn
      replace h1 := h1 m n hN1
      replace h2 := h2 m n hN2
      unfold s3
      rw [sum_sub_sum_eq_dif_add_dif]
      have ε12 : ε = ε1 + ε2 := by
        unfold ε2
        rw [
          AddCommGroup.sub_eq_add_neg, AddCommMonoid.add_comm,
          AddCommMonoid.add_assoc,AddCommGroup.neg_add_cancel
        ]
        exact (AddCommMonoid.add_zero ε).symm
      rw [ε12]
      exact Std.lt_of_le_of_lt abs_sum_le_sum_abs (OrderedAdd.add_lt_add h1 h2)

  instance : Add (Cauchy α) where
    add := Cauchy.add

  theorem add_def {a b : Cauchy α} : a + b = Cauchy.add a b := rfl

  protected def zero : Cauchy α := by
    let s : Sequ α := fun _ => 0
    apply PSigma.mk s
    intro ε hε;exists 0;intros;unfold s;
    simp [AddCommGroup.sub_zero, abs_zero_iff_zero.mpr, hε]

  instance : Zero (Cauchy α) where
    zero := Cauchy.zero

  theorem zero_def : (0 : Cauchy α) = @Cauchy.zero α _ := rfl

  theorem add_zero (a : Cauchy α) : a + 0 = a := by
    -- let (eq := ea) ⟨sa, ha⟩ := a
    -- let (eq := e0) ⟨s0, h0⟩ := (0 : Cauchy α)
    rw [add_def]
    unfold Cauchy.add
    repeat split
    case h_1 eq0 =>
      cases eq0
      simp only [AddCommMonoid.add_zero]

  theorem add_comm (a b : Cauchy α) : a + b = b + a := by
    repeat rw [add_def]
    unfold Cauchy.add
    repeat split
    case h_1 eqb =>
      cases eqb
      simp only [AddCommMonoid.add_comm]

  theorem add_assoc (a b c : Cauchy α) : (a + b) + c = a + (b + c) := by
    repeat rw [add_def]
    unfold Cauchy.add
    repeat split
    simp [AddCommMonoid.add_assoc]

  protected def neg: Cauchy α → Cauchy α := by
    intro ⟨s, h⟩
    let s' : Sequ α := fun (n : Nat) => -(s n)
    apply PSigma.mk s'
    unfold s'
    simp (singlePass := true) only [← abs_neg_eq_abs]
    simp only [AddCommGroup.sub_eq_add_neg, AddCommGroup.neg_add, AddCommGroup.neg_neg]
    simp only [← AddCommGroup.sub_eq_add_neg]
    exact h

  instance : Neg (Cauchy α) where
    neg := Cauchy.neg

  theorem neg_def {a : Cauchy α} : -a = Cauchy.neg a := rfl

  instance : AddCommMonoid (Cauchy α) where
    add_zero := add_zero
    add_comm := add_comm
    add_assoc := add_assoc

  protected def sub : Cauchy α → Cauchy α → Cauchy α :=
    fun a => (fun b => Cauchy.add a (Cauchy.neg b))

  instance : Sub (Cauchy α) where
    sub := Cauchy.sub

  theorem sub_def (a b : Cauchy α) : a - b = Cauchy.sub a b := rfl

  theorem neg_add_cancel (a : Cauchy α) : -a + a = 0 := by
    rw [add_def, neg_def, zero_def]
    unfold Cauchy.add Cauchy.neg Cauchy.zero
    repeat split
    case h_1 heq =>
    cases heq
    simp only [AddCommGroup.neg_add_cancel]

  theorem sub_eq_add_neg (a b : Cauchy α) : a - b = a + -b := by
    rw [add_def, sub_def, neg_def]
    unfold Cauchy.sub Cauchy.neg Cauchy.add
    repeat split
    simp only []

  instance : AddCommGroup (Cauchy α) where
    neg_add_cancel := neg_add_cancel
    sub_eq_add_neg := sub_eq_add_neg

end Cauchy
