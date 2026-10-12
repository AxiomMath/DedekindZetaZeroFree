module

public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.FractionalIntegrals.NormalizedKernel

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse
open MeasureTheory
open scoped RealInnerProductSpace

noncomputable def rawZonalIntegral (N : ℕ) (F : Sphere → ℂ) (x : Sphere) : ℂ :=
  ∫ y : Sphere, ((N + 1 : ℂ) / 2^N) *
    ((1 + inner ℝ (x : Ambient) (y : Ambient)) : ℂ)^N * F y ∂sphereArea

theorem positiveKernel_uniform_approximation
    [IsProbabilityMeasure sphereArea]
    (K : ℕ → Sphere → Sphere → ℝ) (b : ℝ → ℕ → ℝ)
    (hKcont : ∀ N x, Continuous (K N x))
    (hKnonneg : ∀ N x y, 0 ≤ K N x y)
    (hKmass : ∀ N x, (∫ y : Sphere, K N x y ∂sphereArea) = 1)
    (hbnonneg : ∀ δ, 0 < δ → δ ≤ 1 → ∀ N, 0 ≤ b δ N)
    (hfar : ∀ δ, 0 < δ → δ ≤ 1 → ∀ N x y,
      δ ≤ dist x y → K N x y ≤ b δ N)
    (hconcentration : ∀ δ, 0 < δ → δ ≤ 1 →
      Filter.Tendsto (b δ) Filter.atTop (nhds 0))
    (F : Sphere → ℂ) (hF : Continuous F) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ x : Sphere,
      ‖F x - ∫ y : Sphere, (K N x y : ℂ) * F y ∂sphereArea‖ ≤ ε := by
  intro ε hε
  obtain ⟨C₀, hC₀⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  let C : ℝ := max C₀ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound : ∀ x, ‖F x‖ ≤ C := fun x =>
    (hC₀ x (Set.mem_univ x)).trans (le_max_left _ _)
  obtain ⟨δ₀, hδ₀, hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hF) (ε / 2) (by linarith)
  let δ : ℝ := min δ₀ 1
  have hδ : 0 < δ := lt_min hδ₀ zero_lt_one
  have hδone : δ ≤ 1 := min_le_right _ _
  have htail := (hconcentration δ hδ hδone).eventually_le_const
    (show 0 < ε / (4 * C) from div_pos hε (by positivity))
  filter_upwards [htail] with N hN
  intro x
  have hKi : Integrable (K N x) sphereArea :=
    (hKcont N x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hKc : Continuous (fun y => (K N x y : ℂ)) := by fun_prop
  have hleft : Integrable (fun y => (K N x y : ℂ) * F x) sphereArea :=
    (hKc.mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hright : Integrable (fun y => (K N x y : ℂ) * F y) sphereArea :=
    (hKc.mul hF).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hid : F x - ∫ y, (K N x y : ℂ) * F y ∂sphereArea =
      ∫ y, (K N x y : ℂ) * (F x - F y) ∂sphereArea := by
    simp_rw [mul_sub]
    rw [integral_sub hleft hright, integral_mul_const, integral_complex_ofReal,
      hKmass N x]
    simp
  rw [hid]
  calc
    ‖∫ y, (K N x y : ℂ) * (F x - F y) ∂sphereArea‖ ≤
        ∫ y, (ε / 2) * K N x y + b δ N * (2 * C) ∂sphereArea := by
      apply norm_integral_le_of_norm_le
        ((hKi.const_mul (ε / 2)).add (integrable_const _))
      apply Filter.Eventually.of_forall
      intro y
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hKnonneg N x y)]
      by_cases hnear : dist x y < δ
      · have he : ‖F x - F y‖ ≤ ε / 2 := by
          simpa only [dist_eq_norm] using (show dist (F x) (F y) < ε / 2 from
            hclose (hnear.trans_le (min_le_left _ _))).le
        calc
          K N x y * ‖F x - F y‖ ≤ K N x y * (ε / 2) :=
            mul_le_mul_of_nonneg_left he (hKnonneg N x y)
          _ ≤ (ε / 2) * K N x y + b δ N * (2 * C) := by
            have := mul_nonneg (hbnonneg δ hδ hδone N) (show 0 ≤ 2 * C by positivity)
            nlinarith
      · have he : ‖F x - F y‖ ≤ 2 * C :=
          (norm_sub_le _ _).trans (by have := hbound x; have := hbound y; linarith)
        have hk := hfar δ hδ hδone N x y (le_of_not_gt hnear)
        calc
          K N x y * ‖F x - F y‖ ≤ K N x y * (2 * C) :=
            mul_le_mul_of_nonneg_left he (hKnonneg N x y)
          _ ≤ b δ N * (2 * C) := mul_le_mul_of_nonneg_right hk (by positivity)
          _ ≤ (ε / 2) * K N x y + b δ N * (2 * C) := by
            have := mul_nonneg (show 0 ≤ ε / 2 by positivity) (hKnonneg N x y)
            linarith
    _ = ε / 2 + b δ N * (2 * C) := by
      rw [integral_add (hKi.const_mul _) (integrable_const _), integral_const_mul,
        hKmass N x]
      simp
    _ ≤ ε := by
      have ht := mul_le_mul_of_nonneg_right hN (show 0 ≤ 2 * C by positivity)
      have hcancel : (ε / (4 * C)) * (2 * C) = ε / 2 := by
        field_simp
        <;> ring
      rw [hcancel] at ht
      linarith

end DedekindZetaZeroFree.ComplexFractionalInverse
