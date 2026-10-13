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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped ENNReal
open Filter

namespace DedekindZetaZeroFree.Quantitative
namespace FrequencyPowerTails

variable {α : Type*}

private lemma shell_term_le (q : α → ℝ) (p K X : ℝ) (hp : 1 < p) (hX : 1 ≤ X)
    (hfin : ∀ Y : ℝ, {a | q a ≤ Y}.Finite)
    (hK : ∀ Y : ℝ, 1 ≤ Y → ((({a | q a ≤ Y} : Set α).ncard : ℕ) : ℝ) ≤ K * Y) (k : ℕ) (n : α → ℕ)
    (hn : ∀ a, X < q a → (2:ℝ)^(n a) * X ≤ q a ∧ q a < (2:ℝ)^(n a + 1) * X) :
    ∑' a, (if n a = k then (if X < q a then ENNReal.ofReal (q a ^ (-p)) else 0) else 0)
      ≤ ENNReal.ofReal (2 * max K 1 * X ^ (1 - p) * ((2:ℝ) ^ (1 - p)) ^ k) := by
  classical
  set Y : ℝ := (2:ℝ)^(k+1) * X with hY
  have hX0 : 0 < X := by linarith
  have hY1 : 1 ≤ Y := by
    have : (1:ℝ) ≤ 2^(k+1) := one_le_pow₀ (by norm_num)
    rw [hY]; nlinarith
  set s := (hfin Y).toFinset with hs
  have hsupp : ∀ a ∉ s, (if n a = k then (if X < q a then ENNReal.ofReal (q a ^ (-p)) else 0) else 0) = 0 := by
    intro a ha
    by_cases h1 : n a = k
    · by_cases h2 : X < q a
      · exfalso; apply ha
        rw [hs, Set.Finite.mem_toFinset]
        have := (hn a h2).2
        rw [h1] at this
        exact le_of_lt this
      · simp [h2]
    · simp [h1]
  rw [tsum_eq_sum hsupp]
  have hterm : ∀ a ∈ s, (if n a = k then (if X < q a then ENNReal.ofReal (q a ^ (-p)) else 0) else 0)
      ≤ ENNReal.ofReal (((2:ℝ)^k * X) ^ (-p)) := by
    intro a _
    by_cases h1 : n a = k
    · by_cases h2 : X < q a
      · simp only [h1, h2, if_true]
        apply ENNReal.ofReal_le_ofReal
        have := (hn a h2).1
        rw [h1] at this
        apply Real.rpow_le_rpow_of_nonpos (by positivity) this (by linarith)
      · simp [h2]
    · simp [h1]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (s.card : ℝ) ≤ max K 1 * Y := by
    have h1 : s.card = ({a | q a ≤ Y} : Set α).ncard := by
      rw [hs, Set.ncard_eq_toFinset_card _ (hfin Y)]
    rw [h1]
    exact (hK Y hY1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have heq : max K 1 * Y * (((2:ℝ)^k * X) ^ (-p))
      = 2 * max K 1 * X ^ (1 - p) * ((2:ℝ) ^ (1 - p)) ^ k := by
    have h2k : ((2:ℝ)^k) ^ (-p) * ((2:ℝ)^(k:ℕ)) = ((2:ℝ) ^ (1 - p)) ^ k := by
      rw [← Real.rpow_natCast (2:ℝ) k, ← Real.rpow_natCast ((2:ℝ)^(1-p)) k,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
      congr 1; ring
    have hX' : X * X ^ (-p) = X ^ (1 - p) := by
      rw [sub_eq_add_neg, Real.rpow_add hX0, Real.rpow_one]
    rw [Real.mul_rpow (by positivity) hX0.le, hY, ← h2k, ← hX']
    ring
  rw [← heq]
  exact mul_le_mul_of_nonneg_right hcard (by positivity)

private lemma dyadic_index (q : α → ℝ) (X : ℝ) (hX : 0 < X) (a : α) (h : X < q a) :
    (2:ℝ)^(Nat.log 2 ⌊q a / X⌋₊) * X ≤ q a ∧ q a < (2:ℝ)^(Nat.log 2 ⌊q a / X⌋₊ + 1) * X := by
  have h1 : 1 ≤ q a / X := by rw [le_div_iff₀ hX]; linarith
  have hm : ⌊q a / X⌋₊ ≠ 0 := (Nat.floor_pos.2 h1).ne'
  set m := ⌊q a / X⌋₊ with hm_def
  have hle : (2:ℕ)^(Nat.log 2 m) ≤ m := Nat.pow_log_le_self 2 hm
  have hlt : m < (2:ℕ)^(Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hfl : (m : ℝ) ≤ q a / X := Nat.floor_le (by positivity)
  have hfl2 : q a / X < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hle' : (2:ℝ)^(Nat.log 2 m) ≤ m := by exact_mod_cast hle
  have hlt' : (m : ℝ) + 1 ≤ (2:ℝ)^(Nat.log 2 m + 1) := by exact_mod_cast hlt
  constructor
  · have := hle'.trans hfl
    rwa [le_div_iff₀ hX] at this
  · have : q a / X < (2:ℝ)^(Nat.log 2 m + 1) := lt_of_lt_of_le hfl2 hlt'
    rwa [div_lt_iff₀ hX] at this

theorem tail_tsum_enn_le (q : α → ℝ) (p K : ℝ) (hp : 1 < p)
    (hfin : ∀ Y : ℝ, {a | q a ≤ Y}.Finite)
    (hK : ∀ Y : ℝ, 1 ≤ Y → ((({a | q a ≤ Y} : Set α).ncard : ℕ) : ℝ) ≤ K * Y)
    (X : ℝ) (hX : 1 ≤ X) :
    ∑' a, (if X < q a then ENNReal.ofReal (q a ^ (-p)) else 0)
      ≤ ENNReal.ofReal (2 * max K 1 / (1 - (2:ℝ) ^ (1 - p)) * X ^ (1 - p)) := by
  classical
  have hX0 : 0 < X := by linarith
  set n : α → ℕ := fun a => Nat.log 2 ⌊q a / X⌋₊ with hn_def
  have hn : ∀ a, X < q a → (2:ℝ)^(n a) * X ≤ q a ∧ q a < (2:ℝ)^(n a + 1) * X :=
    fun a h => dyadic_index q X hX0 a h
  set f : α → ℝ≥0∞ := fun a => if X < q a then ENNReal.ofReal (q a ^ (-p)) else 0 with hf
  have h1 : ∀ a, ∑' k : ℕ, (if n a = k then f a else 0) = f a := fun a =>
    (tsum_eq_single (n a) (fun k hk => if_neg (Ne.symm hk))).trans (if_pos rfl)
  set r : ℝ := (2:ℝ) ^ (1 - p) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set c : ℝ := 2 * max K 1 * X ^ (1 - p) with hc
  have hc0 : 0 ≤ c := by positivity
  have hsum : Summable (fun k : ℕ => c * r ^ k) := (summable_geometric_of_lt_one hr0.le hr1).mul_left c
  calc ∑' a, f a = ∑' a, ∑' k : ℕ, (if n a = k then f a else 0) := tsum_congr (fun a => (h1 a).symm)
    _ = ∑' k : ℕ, ∑' a, (if n a = k then f a else 0) := ENNReal.tsum_comm
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (c * r ^ k) :=
        ENNReal.tsum_le_tsum (fun k => shell_term_le q p K X hp hX hfin hK k n hn)
    _ = ENNReal.ofReal (∑' k : ℕ, c * r ^ k) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum).symm
    _ = _ := by
        congr 1
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1, hc]
        have : 1 - r ≠ 0 := by linarith
        field_simp

theorem tail_dominated (q : α → ℝ) (p K : ℝ) (hp : 1 < p)
    (hfin : ∀ Y : ℝ, {a | q a ≤ Y}.Finite)
    (hK : ∀ Y : ℝ, 1 ≤ Y → ((({a | q a ≤ Y} : Set α).ncard : ℕ) : ℝ) ≤ K * Y) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ (B : ℝ), 0 ≤ B → ∀ (S : Set α) (w : α → ℝ),
      (∀ a ∈ S, X < q a) → (∀ a ∈ S, 0 ≤ w a ∧ w a ≤ B * q a ^ (-p)) →
      Summable (fun a : S => w a) ∧ ∑' a : S, w a ≤ B * C * X ^ (1 - p) := by
  have hr1 : (2:ℝ) ^ (1 - p) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hd : 0 < 1 - (2:ℝ) ^ (1 - p) := by linarith
  refine ⟨2 * max K 1 / (1 - (2:ℝ) ^ (1 - p)), by positivity, ?_⟩
  intro X hX B hB S w hS hw
  classical
  have hX0 : 0 < X := by linarith
  set C : ℝ := 2 * max K 1 / (1 - (2:ℝ) ^ (1 - p)) with hC
  have hC0 : 0 < C := by positivity
  have hcore := tail_tsum_enn_le q p K hp hfin hK X hX
  have hbound : ∑' a : S, ENNReal.ofReal (w a) ≤ ENNReal.ofReal (B * (C * X ^ (1 - p))) := by
    rw [tsum_subtype S (fun a => ENNReal.ofReal (w a))]
    calc ∑' a, S.indicator (fun a => ENNReal.ofReal (w a)) a
        ≤ ∑' a, ENNReal.ofReal B * (if X < q a then ENNReal.ofReal (q a ^ (-p)) else 0) := by
          refine ENNReal.tsum_le_tsum (fun a => ?_)
          by_cases ha : a ∈ S
          · rw [Set.indicator_of_mem ha, if_pos (hS a ha), ← ENNReal.ofReal_mul hB]
            exact ENNReal.ofReal_le_ofReal (hw a ha).2
          · rw [Set.indicator_of_notMem ha]; exact bot_le
      _ = ENNReal.ofReal B * ∑' a, (if X < q a then ENNReal.ofReal (q a ^ (-p)) else 0) :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal (C * X ^ (1 - p)) := by gcongr
      _ = _ := (ENNReal.ofReal_mul hB).symm
  have hne : ∑' a : S, ENNReal.ofReal (w a) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hsm : Summable (fun a : S => w a) := by
    have := ENNReal.summable_toReal hne
    refine this.congr (fun a => ?_)
    exact ENNReal.toReal_ofReal (hw a a.2).1
  refine ⟨hsm, ?_⟩
  have h2 : ENNReal.ofReal (∑' a : S, w a) = ∑' a : S, ENNReal.ofReal (w a) :=
    ENNReal.ofReal_tsum_of_nonneg (fun a => (hw a a.2).1) hsm
  rw [← h2] at hbound
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hbound
  linarith [this]

theorem summable_tail_rpow (q : α → ℝ) (p K : ℝ) (hp : 1 < p)
    (hfin : ∀ Y : ℝ, {a | q a ≤ Y}.Finite)
    (hK : ∀ Y : ℝ, 1 ≤ Y → ((({a | q a ≤ Y} : Set α).ncard : ℕ) : ℝ) ≤ K * Y) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      Summable (fun a : {a | X < q a} => q a ^ (-p)) ∧
      ∑' a : {a | X < q a}, q a ^ (-p) ≤ C * X ^ (1 - p) := by
  obtain ⟨C, hC, h⟩ := tail_dominated q p K hp hfin hK
  refine ⟨C, hC, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have := h X hX 1 zero_le_one {a | X < q a} (fun a => q a ^ (-p)) (fun a ha => ha)
    (fun a ha => ⟨by
      have : 0 < q a := hX0.trans ha
      positivity, by rw [one_mul]⟩)
  simpa using this

end FrequencyPowerTails
end DedekindZetaZeroFree.Quantitative
