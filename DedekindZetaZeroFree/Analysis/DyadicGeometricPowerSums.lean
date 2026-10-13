module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative
namespace DyadicPowerSums

open Finset

lemma mem_dyadicRange_iff {X : ℝ} (hX : 1 ≤ X) (k : ℕ) :
    k ∈ Finset.range (Nat.log 2 ⌊X⌋₊ + 1) ↔ (2 : ℝ) ^ k ≤ X := by
  have hfl : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa using hX)
  rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_log_iff_pow_le (by norm_num) (by omega),
    Nat.le_floor_iff (by linarith)]
  norm_cast

theorem sum_dyadic_pos (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      ∑ k ∈ Finset.range (Nat.log 2 ⌊X⌋₊ + 1), ((2 : ℝ) ^ k) ^ a ≤ C * X ^ a := by
  have hr : (1 : ℝ) < (2 : ℝ) ^ a := Real.one_lt_rpow (by norm_num) ha
  refine ⟨(2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1), div_pos (by linarith) (by linarith), fun X hX => ?_⟩
  set n := Nat.log 2 ⌊X⌋₊ with hn
  have hnX : (2 : ℝ) ^ n ≤ X := (mem_dyadicRange_iff hX n).1 (by simp [hn])
  have hterm : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ a = ((2 : ℝ) ^ a) ^ k := fun k => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  simp_rw [hterm]
  rw [geom_sum_eq hr.ne']
  have h1 : ((2 : ℝ) ^ a) ^ n ≤ X ^ a := by
    rw [← hterm]; exact Real.rpow_le_rpow (by positivity) hnX ha.le
  have hpos : 0 < (2 : ℝ) ^ a - 1 := by linarith
  have : ((2 : ℝ) ^ a) ^ (n + 1) = (2 : ℝ) ^ a * ((2 : ℝ) ^ a) ^ n := by ring
  have hXa : 0 ≤ X ^ a := by positivity
  rw [div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ hpos.le
  calc ((2 : ℝ) ^ a) ^ (n + 1) - 1 ≤ ((2 : ℝ) ^ a) ^ (n + 1) := by linarith
    _ = (2 : ℝ) ^ a * ((2 : ℝ) ^ a) ^ n := this
    _ ≤ (2 : ℝ) ^ a * X ^ a := by gcongr

theorem sum_dyadic_pos_interval (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 1 ≤ Y →
      ∑ k ∈ (Finset.range (Nat.log 2 ⌊Y⌋₊ + 1)).filter (fun k => X ≤ (2 : ℝ) ^ k),
        ((2 : ℝ) ^ k) ^ a ≤ C * Y ^ a := by
  obtain ⟨C, hC, h⟩ := sum_dyadic_pos a ha
  refine ⟨C, hC, fun X Y hY => le_trans ?_ (h Y hY)⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun k _ _ => by positivity)

theorem summable_tail_dyadic_neg (a : ℝ) (ha : a < 0) (X : ℝ) :
    Summable (fun k : ℕ => if X ≤ (2 : ℝ) ^ k then ((2 : ℝ) ^ k) ^ a else 0) := by
  have hr0 : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have hr1 : (2 : ℝ) ^ a < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ha
  have hterm : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ a = ((2 : ℝ) ^ a) ^ k := fun k => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    (summable_geometric_of_lt_one hr0.le hr1)
  · split_ifs <;> positivity
  · split_ifs
    · rw [hterm]
    · positivity

theorem tsum_tail_dyadic_neg (a : ℝ) (ha : a < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      ∑' k : ℕ, (if X ≤ (2 : ℝ) ^ k then ((2 : ℝ) ^ k) ^ a else 0) ≤ C * X ^ a := by
  have hr0 : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have hr1 : (2 : ℝ) ^ a < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ha
  have hterm : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ a = ((2 : ℝ) ^ a) ^ k := fun k => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  refine ⟨1 / (1 - (2 : ℝ) ^ a), div_pos one_pos (by linarith), fun X hX => ?_⟩
  have hex : ∃ k : ℕ, X ≤ (2 : ℝ) ^ k := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt X (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, hk.le⟩
  classical
  set m := Nat.find hex with hm
  have hmX : X ≤ (2 : ℝ) ^ m := Nat.find_spec hex
  set f : ℕ → ℝ := fun k => if X ≤ (2 : ℝ) ^ k then ((2 : ℝ) ^ k) ^ a else 0 with hf
  have hsum : Summable f := summable_tail_dyadic_neg a ha X
  have hzero : ∀ k ∈ Finset.range m, f k = 0 := by
    intro k hk
    have := Nat.find_min hex (Finset.mem_range.1 hk)
    simp [hf, this]
  have hshift : ∀ k, f (k + m) = ((2 : ℝ) ^ a) ^ (k + m) := by
    intro k
    have : X ≤ (2 : ℝ) ^ (k + m) := hmX.trans (pow_le_pow_right₀ (by norm_num) (by omega))
    simp only [hf, if_pos this, hterm]
  have h := hsum.sum_add_tsum_nat_add m
  rw [Finset.sum_eq_zero hzero, zero_add] at h
  rw [← h]
  simp_rw [hshift, pow_add]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hr0.le hr1]
  have h1 : ((2 : ℝ) ^ a) ^ m ≤ X ^ a := by
    rw [← hterm]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hmX ha.le
  calc (1 - (2 : ℝ) ^ a)⁻¹ * ((2 : ℝ) ^ a) ^ m ≤ (1 - (2 : ℝ) ^ a)⁻¹ * X ^ a := by
        gcongr
    _ = _ := by ring

theorem sum_dyadic_neg_interval (a : ℝ) (ha : a < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 1 ≤ X →
      ∑ k ∈ (Finset.range (Nat.log 2 ⌊Y⌋₊ + 1)).filter (fun k => X ≤ (2 : ℝ) ^ k),
        ((2 : ℝ) ^ k) ^ a ≤ C * X ^ a := by
  obtain ⟨C, hC, h⟩ := tsum_tail_dyadic_neg a ha
  refine ⟨C, hC, fun X Y hX => le_trans ?_ (h X hX)⟩
  have hs := summable_tail_dyadic_neg a ha X
  calc _ = ∑ k ∈ (Finset.range (Nat.log 2 ⌊Y⌋₊ + 1)),
        (if X ≤ (2 : ℝ) ^ k then ((2 : ℝ) ^ k) ^ a else 0) := by
        rw [Finset.sum_filter]
    _ ≤ _ := hs.sum_le_tsum _ (fun k _ => by split_ifs <;> positivity)

end DyadicPowerSums
end DedekindZetaZeroFree.Quantitative
