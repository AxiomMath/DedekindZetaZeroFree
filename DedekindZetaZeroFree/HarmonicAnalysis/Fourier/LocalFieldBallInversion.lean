module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegerLatticeNormalization

@[expose] public section

noncomputable section
open scoped Classical nonZeroDivisors WithZero Pointwise ENNReal NNReal
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.PoissonS.Covolume

attribute [local instance] completionMeasurable completionBorel

private theorem integral_character_subgroup_eq_zero
    {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : Measure G) [μ.IsAddLeftInvariant]
    (H : AddSubgroup G) (χ : G → ℂ)
    (hχ : ∀ a b, χ (a + b) = χ a * χ b)
    (h : G) (hh : h ∈ H) (hn : χ h ≠ 1) :
    (∫ x, (if x ∈ H then χ x else 0) ∂μ) = 0 := by
  let f : G → ℂ := fun x => if x ∈ H then χ x else 0
  have hm (x : G) : h + x ∈ H ↔ x ∈ H := by
    constructor
    · intro hx
      have : -h + (h+x) ∈ H := H.add_mem (H.neg_mem hh) hx
      simpa only [neg_add_cancel_left] using this
    · intro hx
      exact H.add_mem hh hx
  have he (x : G) : f (h + x) = χ h * f x := by
    simp only [f, hm x, hχ, mul_ite, mul_zero]
  have hv := integral_add_left_eq_self f h (μ := μ)
  simp_rw [he] at hv
  rw [integral_const_mul] at hv
  have hv' : (χ h - 1) * (∫ x, f x ∂μ) = 0 := by
    rw [sub_mul, hv, one_mul, sub_self]
  have hf : (∫ x, f x ∂μ) = 0 :=
    (mul_eq_zero.mp hv').resolve_left (sub_ne_zero.mpr hn)
  exact hf

theorem integral_character_subgroup
    {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : Measure G) [μ.IsAddLeftInvariant]
    (H : AddSubgroup G) (hH : MeasurableSet (H : Set G)) (χ : G → ℂ)
    (hχ : ∀ a b, χ (a + b) = χ a * χ b) :
    (∫ x, (if x ∈ H then χ x else 0) ∂μ) =
      if ∀ x ∈ H, χ x = 1 then (μ H).toReal else 0 := by
  by_cases ht : ∀ x ∈ H, χ x = 1
  · rw [if_pos ht]
    have he (x : G) : (if x ∈ H then χ x else 0) =
        (H : Set G).indicator (fun _ => (1 : ℂ)) x := by
      by_cases hx : x ∈ H
      · simp [hx, ht x hx]
      · simp [hx]
    simp_rw [he]
    rw [integral_indicator hH]
    simp [Measure.real]
  · rw [if_neg ht]
    push Not at ht
    obtain ⟨x, hx, hn⟩ := ht
    exact integral_character_subgroup_eq_zero μ H χ hχ x hx hn

theorem finite_scaled_ball_conductor
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (e : AddChar (v.adicCompletion F) Circle)
    (hconductor : ∀ y, (∀ z : v.adicCompletion F, ‖z‖ ≤ 1 → e (z * y) = 1) ↔
      ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExponent F v)
    (a : v.adicCompletion F) (ha : a ≠ 0) (y : v.adicCompletion F) :
    (∀ z : v.adicCompletion F, ‖z‖ ≤ ‖a‖ → e (z * y) = 1) ↔
      ‖a‖ * ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExponent F v := by
  rw [← norm_mul, ← hconductor (a * y)]
  constructor
  · intro h z hz
    rw [← mul_assoc]
    exact h (z * a) (by rw [norm_mul]; nlinarith [norm_nonneg a])
  · intro h z hz
    have hza : ‖z / a‖ ≤ 1 := by
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr ha)).mpr hz
    have hh := h (z / a) hza
    simpa only [← mul_assoc, div_mul_cancel₀ z ha] using hh

theorem finite_scaled_ball_fourier
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (e : AddChar (v.adicCompletion F) Circle)
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hconductor : ∀ y, (∀ z : v.adicCompletion F, ‖z‖ ≤ 1 → e (z * y) = 1) ↔
      ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExponent F v)
    (a : v.adicCompletion F) (ha : a ≠ 0) (y : v.adicCompletion F) :
    (∫ z, (if ‖z‖ ≤ ‖a‖ then (1 : ℂ) else 0) * (e (-z * y) : ℂ) ∂μ) =
      if ‖a‖ * ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExponent F v then
        ((μ {z | ‖z‖ ≤ ‖a‖}).toReal : ℂ) else 0 := by
  let H : AddSubgroup (v.adicCompletion F) :=
    { carrier := {z | ‖z‖ ≤ ‖a‖}
      zero_mem' := by simpa using norm_nonneg a
      add_mem' := fun hx hz => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hz)
      neg_mem' := fun hx => by simpa using hx }
  let χ : v.adicCompletion F → ℂ := fun z => (e (-z * y) : ℂ)
  have hχ (b c : v.adicCompletion F) : χ (b + c) = χ b * χ c := by
    dsimp [χ]
    rw [neg_add, add_mul, AddChar.map_add_eq_mul, Circle.coe_mul]
  have hH : MeasurableSet (H : Set (v.adicCompletion F)) :=
    isClosed_le continuous_norm continuous_const |>.measurableSet
  have hc : (∀ z ∈ H, χ z = 1) ↔
      ‖a‖ * ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExponent F v := by
    change (∀ z, ‖z‖ ≤ ‖a‖ → (e (-z * y) : ℂ) = 1) ↔ _
    simpa only [neg_mul, mul_neg, Circle.coe_eq_one, norm_neg] using
      finite_scaled_ball_conductor F v e hconductor a ha (-y)
  have hf (z : v.adicCompletion F) :
      (if ‖z‖ ≤ ‖a‖ then (1 : ℂ) else 0) * (e (-z * y) : ℂ) =
      if z ∈ H then χ z else 0 := by
    change _ = if ‖z‖ ≤ ‖a‖ then (e (-z * y) : ℂ) else 0
    simp only [ite_mul, one_mul, zero_mul]
  simp_rw [hf]
  rw [integral_character_subgroup μ H hH χ hχ, hc]
  split_ifs <;> simp [H]

theorem finite_translated_ball_fourier
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (e : AddChar (v.adicCompletion F) Circle)
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hconductor : ∀ y, (∀ z : v.adicCompletion F, ‖z‖ ≤ 1 → e (z * y) = 1) ↔
      ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExponent F v)
    (a : v.adicCompletion F) (ha : a ≠ 0) (b y : v.adicCompletion F) :
    (∫ z, (if ‖z - b‖ ≤ ‖a‖ then (1 : ℂ) else 0) * (e (-z * y) : ℂ) ∂μ) =
      (e (-b * y) : ℂ) *
        (if ‖a‖ * ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExponent F v then
          ((μ {z | ‖z‖ ≤ ‖a‖}).toReal : ℂ) else 0) := by
  let f : v.adicCompletion F → ℂ := fun z =>
    (if ‖z - b‖ ≤ ‖a‖ then (1 : ℂ) else 0) * (e (-z * y) : ℂ)
  have hf (z : v.adicCompletion F) : f (b + z) =
      (e (-b * y) : ℂ) *
        ((if ‖z‖ ≤ ‖a‖ then (1 : ℂ) else 0) * (e (-z * y) : ℂ)) := by
    dsimp [f]
    rw [add_sub_cancel_left, neg_add, add_mul, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  have hi := integral_add_left_eq_self f b (μ := μ)
  rw [← hi]
  simp_rw [hf]
  rw [integral_const_mul, finite_scaled_ball_fourier F v e μ hconductor a ha y]

end DedekindZetaZeroFree.PoissonS.Covolume

end
