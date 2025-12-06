import Analysis.Utils

open Classical
open Lean.Grind (AddCommGroup AddCommMonoid OrderedAdd)
open Std (IsLinearOrder IsPreorder IsLinearPreorder)

open abs
open misc

def Sequ (α : Type) : Type := Nat → α

class Seq_type (α : Type) extends
  Lean.Grind.AddCommGroup α,
  LE α, LT α,
  Std.IsLinearOrder α, Std.LawfulOrderLT α,
  OrderedAdd α

namespace Seq_type
  instance inst_tp1 {α : Type} [Seq_type α] : tp1 α where
end Seq_type

variable {α : Type} [Seq_type α]


namespace Sequ

  protected def add: Sequ α → Sequ α → Sequ α :=
    fun s1 s2 n => (s1 n) + (s2 n)

  instance : Add (Sequ α) where
    add := Sequ.add

  theorem add_def {a b : Sequ α} : a + b = Sequ.add a b := rfl

  protected def zero : Sequ α := fun _ => 0

  instance : Zero (Sequ α) where
    zero := Sequ.zero

  theorem zero_def : (0 : Sequ α) = @Sequ.zero α _ := rfl

  theorem add_zero (a : Sequ α) : a + 0 = a := by
    rw [add_def, zero_def]
    unfold Sequ.add Sequ.zero
    simp only [AddCommMonoid.add_zero]

  theorem add_comm (a b : Sequ α) : a + b = b + a := by
    repeat rw [add_def]
    unfold Sequ.add
    simp only [AddCommMonoid.add_comm]

  theorem add_assoc (a b c : Sequ α) : (a + b) + c = a + (b + c) := by
    repeat rw [add_def]
    unfold Sequ.add
    simp [AddCommMonoid.add_assoc]

  protected def neg: Sequ α → Sequ α := fun s n => -s n

  instance : Neg (Sequ α) where
    neg := Sequ.neg

  theorem neg_def {a : Sequ α} : -a = Sequ.neg a := rfl

  instance : AddCommMonoid (Sequ α) where
    add_zero := add_zero
    add_comm := add_comm
    add_assoc := add_assoc

  protected def sub : Sequ α → Sequ α → Sequ α :=
    fun a => (fun b => Sequ.add a (Sequ.neg b))

  instance : Sub (Sequ α) where
    sub := Sequ.sub

  theorem sub_def (a b : Sequ α) : a - b = Sequ.sub a b := rfl

  theorem neg_add_cancel (a : Sequ α) : -a + a = 0 := by
    rw [add_def, neg_def, zero_def]
    unfold Sequ.add Sequ.neg Sequ.zero
    simp only [AddCommGroup.neg_add_cancel]

  theorem sub_eq_add_neg (a b : Sequ α) : a - b = a + -b := by
    rw [add_def, sub_def, neg_def]
    unfold Sequ.sub
    rfl

  instance : AddCommGroup (Sequ α) where
    neg_add_cancel := neg_add_cancel
    sub_eq_add_neg := sub_eq_add_neg


end Sequ



structure Cauchy (α : Type) [Seq_type α] where
  s : Sequ α
  h : ∀ε : α, ε > (0 : α) →
        ∃N : Nat, ∀(m n : Nat), (m ≥ N ∧ n ≥ N) →
          abs (s m - s n) < ε


namespace Cauchy

  -- def cauchy_def

  protected def add: Cauchy α → Cauchy α → Cauchy α := by
    intro ⟨s1, h1⟩ ⟨s2, h2⟩
    let s3 := s1 + s2
    -- apply PSigma.mk
    apply Cauchy.mk
    case s => exact s3
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
      rw [Sequ.add_def]
      simp only [Sequ.add]
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
      rw [Sequ.add_def]
      simp only [Sequ.add]
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
    apply Cauchy.mk 0
    intro ε hε;exists 0;intros;rw [Sequ.zero_def];unfold Sequ.zero;
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
    -- let s' : Sequ α := fun (n : Nat) => -(s n)
    apply Cauchy.mk (-s)
    rw [Sequ.neg_def]
    unfold Sequ.neg
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


def Converge.converge (s : Sequ α) (l : α) : Prop :=
  ∀ε : α, ε > 0 →
    ∃N : Nat, ∀n : Nat, N ≤ n →
      abs (s n - l) < ε

structure Converge (α : Type) [Seq_type α] where
  s : Sequ α
  l : α
  h : Converge.converge s l

namespace Converge

  -- def converge

  protected def add : Converge α → Converge α → Converge α := by
      intro ⟨s1, l1, h1⟩ ⟨s2, l2, h2⟩
      -- let s3 := s1 + s2
      apply Converge.mk (s1+s2) (l1+l2)
      intro ε hε0
      simp only [Sequ.add_def];unfold Sequ.add
      simp only [sum_sub_sum_eq_dif_add_dif]
      by_cases h : ∃ε1 : α, 0 < ε1 ∧ ε1 < ε
      case pos =>
        let ⟨ε1, ⟨hε10, hε1ε⟩⟩ := h
        let (eq := hε12) ε2 := ε - ε1
        have hε20 : 0 < ε2 := OrderedAdd.sub_pos_iff.mpr hε1ε
        let ⟨N1, h1⟩ := h1 ε1 hε10
        let ⟨N2, h2⟩ := h2 ε2 hε20
        let (eq := hMax) N := max N1 N2
        exists N;intro n hn
        simp only [AddCommGroup.sub_eq_iff.mp hε12.symm]
        replace h1 := h1 n (Std.le_trans Std.left_le_max hn)
        replace h2 := h2 n (Std.le_trans Std.right_le_max hn)
        rw (occs := .pos [2]) [AddCommMonoid.add_comm]
        apply (Std.lt_of_le_of_lt abs.abs_sum_le_sum_abs)
        exact OrderedAdd.add_lt_add h1 h2
      case neg =>
        simp at h
        replace h := fun x p => Std.not_lt.mp (imp_not_comm.mp (h x) p)
        replace ⟨N1, h1⟩ := h1 ε hε0
        replace ⟨N2, h2⟩ := h2 ε hε0
        let (eq := hMax) N := max N1 N2
        exists N; intro n hn
        replace c1 := Std.le_antisymm (h _ (h1 n (Std.le_trans Std.left_le_max hn))) (abs.abs_ge_zero _)
        replace c2 := Std.le_antisymm (h _ (h2 n (Std.le_trans Std.right_le_max hn))) (abs.abs_ge_zero _)
        apply (Std.lt_of_le_of_lt abs.abs_sum_le_sum_abs)
        simp only [c1, c2, AddCommMonoid.add_zero,hε0]

  instance : Add (Converge α) where
    add := Converge.add

  theorem add_def {a b : Converge α} : a + b = Converge.add a b := rfl

  protected def zero : Converge α := by
    apply Converge.mk 0 0
    intro ε hε;exists 0;intros;rw [Sequ.zero_def];unfold Sequ.zero;
    simp [AddCommGroup.sub_zero, abs_zero_iff_zero.mpr, hε]

  instance : Zero (Converge α) where
    zero := Converge.zero

  theorem zero_def : (0 : Converge α) = @Converge.zero α _ := rfl

  theorem add_zero (a : Converge α) : a + 0 = a := by
    -- let (eq := ea) ⟨sa, ha⟩ := a
    -- let (eq := e0) ⟨s0, h0⟩ := (0 : Cauchy α)
    rw [add_def]
    unfold Converge.add
    repeat split
    case h_1 eq0 =>
      cases eq0
      simp only [AddCommMonoid.add_zero]

  theorem add_assoc (a b c : Converge α) : (a + b) + c = a + (b + c) := by
    repeat rw [add_def]
    unfold Converge.add
    repeat split
    simp [AddCommMonoid.add_assoc]

  protected def neg : Converge α → Converge α := by
    intro ⟨s, l, h⟩
    apply Converge.mk (-s) (-l)
    rw [Sequ.neg_def]
    unfold Sequ.neg
    intro ε hε0
    let ⟨N, h⟩ := h ε hε0
    exists N
    intro n hn
    simp only [AddCommGroup.sub_eq_add_neg, ←AddCommGroup.neg_add, abs.abs_neg_eq_abs]
    rw [← AddCommGroup.sub_eq_add_neg]
    exact h n hn

  instance : Neg (Converge α) where
    neg := Converge.neg

  theorem neg_def {a : Converge α} : -a = Converge.neg a := rfl

  theorem add_comm (a b : Converge α) : a + b = b + a := by
    repeat rw [add_def]
    unfold Converge.add
    repeat split
    case h_1 eqb =>
      cases eqb
      simp only [AddCommMonoid.add_comm]

  instance : AddCommMonoid (Converge α) where
    add_zero := add_zero
    add_comm := add_comm
    add_assoc := add_assoc

  protected def sub : Converge α → Converge α → Converge α :=
    fun c1 c2 => Converge.add c1 (Converge.neg c2)

  instance : Sub (Converge α) where
    sub := Converge.sub

  theorem sub_def (a b : Converge α) : a - b = Converge.sub a b := rfl

  theorem neg_add_cancel (a : Converge α) : -a + a = 0 := by
    rw [add_def, neg_def, zero_def]
    unfold Converge.add Converge.neg Converge.zero
    repeat split
    case h_1 heq =>
    cases heq
    simp only [AddCommGroup.neg_add_cancel]

  theorem sub_eq_add_neg (a b : Converge α) : a - b = a + -b := by
    rw [add_def, sub_def, neg_def]
    unfold Converge.sub Converge.neg Converge.add
    repeat split
    simp only []

  instance : AddCommGroup (Converge α) where
    neg_add_cancel := neg_add_cancel
    sub_eq_add_neg := sub_eq_add_neg

end Converge
