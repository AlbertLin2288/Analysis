import Analysis.Utils

open Classical
open Lean.Grind (
  AddCommGroup AddCommMonoid OrderedAdd
  Semiring Ring CommSemiring CommRing OrderedRing
)
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

class Seq_ring_type (α : Type) extends
  Lean.Grind.CommRing α,
  LE α, LT α,
  Std.IsLinearOrder α, Std.LawfulOrderLT α,
  OrderedRing α

namespace Seq_ring_type
  instance {α : Type} [Seq_ring_type α] : Seq_type α where
end Seq_ring_type


namespace Sequ

  section Group

    variable {α : Type} [Seq_type α]

    protected def add: Sequ α → Sequ α → Sequ α :=
      fun s1 s2 n => (s1 n) + (s2 n)

    instance : Add (Sequ α) where
      add := Sequ.add

    theorem add_def {a b : Sequ α} : a + b = Sequ.add a b := rfl

    protected def zero : Sequ α := fun _ => OfNat.ofNat 0

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


  end Group


  section Ring

    variable {α : Type} [Seq_ring_type α]


    -- Semiring

    protected def mul : Sequ α → Sequ α → Sequ α :=
      fun a b n => a n * b n

    instance : Mul (Sequ α) where
      mul := Sequ.mul

    theorem mul_def {a b : Sequ α} : a * b = Sequ.mul a b := rfl

    protected def ofNat : Nat → Sequ α :=
      fun n _ => OfNat.ofNat n

    @[default_instance] instance : NatCast (Sequ α) where
      natCast := Sequ.ofNat

    theorem natCast_def {a : Nat} :
      Nat.cast a = Sequ.ofNat (α := α) a := rfl

    instance (n : Nat) : OfNat (Sequ α) n where
      ofNat := Sequ.ofNat n

    theorem ofNat_def (a : Nat) :
      OfNat.ofNat a = Sequ.ofNat (α := α) a := rfl

    protected def nsmul : Nat → Sequ α → Sequ α :=
      fun n a m => Semiring.nsmul.smul n (a m)

    instance : SMul Nat (Sequ α) where
      smul := Sequ.nsmul

    theorem nsmul_def {n : Nat} {a : Sequ α} : n • a = Sequ.nsmul n a := rfl

    protected def hPow : Sequ α → Nat → Sequ α :=
      fun a n m => Semiring.npow.hPow (a m) n

    instance : HPow (Sequ α) Nat (Sequ α) where
      hPow := Sequ.hPow

    theorem mul_assoc (a b c : Sequ α) :  a * b * c = a * (b * c) := by
      funext n
      exact Semiring.mul_assoc (a n) (b n) (c n)

    theorem mul_one (a : Sequ α) : a * 1 = a := by
      funext n
      exact Semiring.mul_one (a n)

    theorem one_mul (a : Sequ α) : 1 * a = a := by
      funext n
      exact Semiring.one_mul (a n)

    theorem left_distrib (a b c : Sequ α) :
      a * (b + c) = a * b + a * c := by
        funext n
        exact Semiring.left_distrib (a n) (b n) (c n)

    theorem right_distrib (a b c : Sequ α) :
      (a + b) * c = a * c + b * c := by
        funext n
        exact Semiring.right_distrib (a n) (b n) (c n)

    theorem zero_mul (a : Sequ α) : 0 * a = 0 := by
      funext n
      exact Semiring.zero_mul (a n)

    theorem mul_zero (a : Sequ α) : a * 0 = 0 := by
      funext n
      exact Semiring.mul_zero (a n)

    theorem pow_zero (a : Sequ α) : a ^ 0 = 1 := by
      funext n
      exact Semiring.pow_zero (a n)

    theorem pow_succ (a : Sequ α) (n : Nat) :
      a ^ (n + 1) = (a ^ n) * a := by
        funext x
        exact Semiring.pow_succ (a x) n

    theorem ofNat_succ (a : Nat) :
      OfNat.ofNat (α := Sequ α) (a + 1) = OfNat.ofNat a + 1 := by
      funext n
      exact Semiring.ofNat_succ a

    theorem ofNat_eq_natCast (n : Nat) :
      OfNat.ofNat (α := Sequ α) n = Nat.cast n := rfl

    theorem nsmul_eq_natCast_mul (n : Nat) (a : Sequ α) :
      n • a = Nat.cast n * a := by
      funext x
      rw [nsmul_def, Sequ.nsmul, mul_def, Sequ.mul,
        natCast_def, Sequ.ofNat, Semiring.ofNat_eq_natCast]
      exact Semiring.nsmul_eq_natCast_mul n (a x)

    instance : Semiring (Sequ α) where
      add_zero := Sequ.add_zero
      add_comm := Sequ.add_comm
      add_assoc := Sequ.add_assoc
      mul_assoc := Sequ.mul_assoc
      mul_one := mul_one
      one_mul := one_mul
      left_distrib := left_distrib
      right_distrib := right_distrib
      zero_mul := zero_mul
      mul_zero := mul_zero
      pow_zero := pow_zero
      pow_succ := pow_succ
      ofNat_succ := ofNat_succ
      ofNat_eq_natCast := ofNat_eq_natCast
      nsmul_eq_natCast_mul := nsmul_eq_natCast_mul


    -- Ring

    protected def intCast : Int → Sequ α :=
      fun i _ => Ring.intCast.intCast i

    @[default_instance] instance : IntCast (Sequ α) where
      intCast := Sequ.intCast

    theorem intCast_def {i : Int} :
      Int.cast i = Sequ.intCast (α := α) i := rfl

    protected def zsmul : Int → Sequ α → Sequ α :=
      fun i a n => Ring.zsmul.smul i (a n)

    instance : SMul Int (Sequ α) where
      smul := Sequ.zsmul

    theorem zsmul_def {i : Int} {a : Sequ α} : i • a = Sequ.zsmul i a := rfl

    theorem neg_zsmul (i : Int) (a : Sequ α) : -i • a = -(i • a) := by
      funext n
      exact Ring.neg_zsmul i (a n)

    theorem zsmul_natCast_eq_nsmul (n : Nat) (a : Sequ α) :
      (n : Int) • a = n • a  := by
        funext x
        exact Ring.zsmul_natCast_eq_nsmul n (a x)

    theorem intCast_ofNat (n : Nat) :
      Int.cast (OfNat.ofNat (α := Int) n) = OfNat.ofNat (α := Sequ α) n := by
        funext x
        exact Ring.intCast_ofNat n

    theorem intCast_neg (i : Int) :
      Int.cast (R := Sequ α) (-i) = -Int.cast i := by
        funext
        exact Ring.intCast_neg i

    instance : Ring (Sequ α) where
      neg_add_cancel := neg_add_cancel
      sub_eq_add_neg := sub_eq_add_neg
      neg_zsmul := neg_zsmul
      zsmul_natCast_eq_nsmul := zsmul_natCast_eq_nsmul
      intCast_ofNat := intCast_ofNat
      intCast_neg := intCast_neg


    -- CommSemiring

    theorem mul_comm (a b : Sequ α) : a * b = b * a := by
      funext n
      exact CommSemiring.mul_comm (a n) (b n)

    instance : CommSemiring (Sequ α) where
      mul_comm := mul_comm


    -- CommRing

    instance : CommRing (Sequ α) where

  end Ring

end Sequ


structure Cauchy (α : Type) [Seq_type α] where
  s : Sequ α
  h : ∀ε : α, ε > (0 : α) →
        ∃N : Nat, ∀(m n : Nat), (m ≥ N ∧ n ≥ N) →
          abs (s m - s n) < ε


namespace Cauchy

  section Group

    variable {α : Type} [Seq_type α]

    theorem ach {α : Type} [Seq_type α] (ε : α) (hε0 : 0 < ε) (hε : ¬(∃x : α, 0 < x ∧ x < ε)) :
      (c : Cauchy α) → (∃(N : Nat) (a : α), ∀n : Nat, N ≤ n → c.s n = a) := by
        simp at hε
        replace hε := fun x p => Std.not_lt.mp (imp_not_comm.mp (hε x) p)
        intro ⟨s, hc⟩; simp only
        replace ⟨N, hc⟩ := hc ε hε0
        exists N
        exists s N
        intro n hn
        replace hc := hε (abs (s N - s n)) (hc N n ⟨IsPreorder.le_refl N, hn⟩)
        replace hc :=  abs_zero_iff_zero.mp (Std.le_antisymm hc (abs_ge_zero (s N - s n)))
        exact (AddCommGroup.sub_eq_zero_iff.mp hc).symm

    protected def add: Cauchy α → Cauchy α → Cauchy α := by
      intro ⟨s1, h1⟩ ⟨s2, h2⟩
      let s3 := s1 + s2
      apply Cauchy.mk
      case s => exact s3
      intro ε hep
      cases em (∃ε2 : α, 0 < ε2 ∧ ε2 < ε) with
      | inr hne =>
        have hach := ach ε hep hne
        let ⟨N1, ⟨v1, h1c⟩⟩ := hach ⟨s1, h1⟩
        let ⟨N2, ⟨v2, h2c⟩⟩ := hach ⟨s2, h2⟩
        simp only at h1c h2c
        let (eq := hN) N := max N1 N2
        exists N; intro m n hmn
        have ⟨⟨hN1m, hN1n⟩, ⟨hN2m, hN2n⟩⟩ := ge_max_imp_ge_left_right hN hmn
        simp only [s3, Sequ.add_def, Sequ.add]
        rwa [
          h1c m hN1m, h2c m hN2m, h1c n hN1n, h2c n hN2n,
          AddCommGroup.sub_eq_zero_iff.mpr rfl,
          abs_zero_iff_zero.mpr rfl
        ]
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

  end Group

end Cauchy


def Converge.converge {α : Type} [Seq_type α] (s : Sequ α) (l : α) : Prop :=
  ∀ε : α, ε > 0 →
    ∃N : Nat, ∀n : Nat, N ≤ n →
      abs (s n - l) < ε

structure Converge (α : Type) [Seq_type α] where
  s : Sequ α
  l : α
  h : Converge.converge s l

namespace Converge

  section Group

    variable {α : Type} [Seq_type α]

    theorem ach {α : Type} [Seq_type α] (ε : α) (hε0 : 0 < ε) (hε : ¬(∃x : α, 0 < x ∧ x < ε)) :
      (c : Converge α) → (∃(N : Nat), ∀n : Nat, N ≤ n → c.s n = c.l) := by
        simp at hε
        intro ⟨s, l, hc⟩; simp only
        replace ⟨N, hc⟩ := hc ε hε0
        replace hε := fun x p => Std.not_lt.mp (imp_not_comm.mp (hε x) p)
        exists N
        intro n hn
        exact AddCommGroup.sub_eq_zero_iff.mp (
          abs_zero_iff_zero.mp (
            Std.le_antisymm
              (hε (abs (s n - l)) (hc n hn))
              (abs_ge_zero (s n - l))
          )
        )


    protected def add : Converge α → Converge α → Converge α := by
        intro ⟨s1, l1, h1⟩ ⟨s2, l2, h2⟩
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
          have hach := ach ε hε0 h
          replace ⟨N1, h1⟩ := hach ⟨s1, l1, h1⟩
          replace ⟨N2, h2⟩ := hach ⟨s2, l2, h2⟩
          simp only at h1 h2
          let (eq := hMax) N := max N1 N2
          exists N; intro n hn
          replace h1 := h1 n (Std.le_trans Std.left_le_max hn)
          replace h2 := h2 n (Std.le_trans Std.right_le_max hn)
          simp only [h1, h2, AddCommGroup.sub_eq_zero_iff.mpr,
            AddCommMonoid.add_zero, abs_zero_iff_zero.mpr, hε0]

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

  end Group
end Converge
