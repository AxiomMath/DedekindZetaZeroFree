module

public import DedekindZetaZeroFree.MeasureTheory.StereographicProjection.ConeVolume

@[expose] public section

namespace DedekindZetaZeroFree.ComplexLocal.StereographicTransport
open MeasureTheory Set
open scoped Pointwise ENNReal
open ComplexFractionalInverse.RawSphereProjection
open KPCplxCharacterHaar

noncomputable def denominator (z : ℂ) : ℝ := 1 + ‖z‖ ^ 2

private theorem denominator_pos (z : ℂ) : 0 < denominator z := by
  unfold denominator
  positivity

noncomputable def sigmaVector (z : ℂ) : rawAmbient :=
  WithLp.toLp 2 ![2 * z.re / denominator z, -2 * z.im / denominator z,
    (1 - ‖z‖ ^ 2) / denominator z]

theorem sigmaVector_norm (z : ℂ) : ‖sigmaVector z‖ = 1 := by
  have hn : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    simpa only [Complex.normSq_apply, ← sq] using (Complex.normSq_eq_norm_sq z)
  have hD := (denominator_pos z).ne'
  have hs : ‖sigmaVector z‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [sigmaVector, Fin.sum_univ_three, PiLp.toLp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    change (2 * z.re / denominator z)^2 + (-2 * z.im / denominator z)^2 +
      ((1 - ‖z‖^2) / denominator z)^2 = 1
    dsimp [denominator] at *
    field_simp
    nlinarith
  nlinarith [norm_nonneg (sigmaVector z)]

noncomputable def sigma (z : ℂ) : rawSphere :=
  ⟨sigmaVector z, mem_sphere_zero_iff_norm.mpr (sigmaVector_norm z)⟩

noncomputable def planeProbability : Measure ℂ :=
  euclideanArea.withDensity
    (fun z => ENNReal.ofReal (denominator z ^ (-2 : ℝ) / Real.pi))

theorem stereographic_measure_transport :
    MeasurePreserving sigma planeProbability rawSphereArea ∧
      (∀ z : ℂ, denominator z ^ (-2 : ℝ) / Real.pi =
        1 / (Real.pi * denominator z ^ 2)) := by
  constructor
  ·
    change MeasurePreserving RawCone.sigma RawCone.planeProbability rawSphereArea
    refine ⟨RawCone.sigma_continuous.measurable, ?_⟩
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply RawCone.sigma_continuous.measurable hs, RawCone.planeProbability,
      withDensity_apply _ (RawCone.sigma_continuous.measurable hs)]
    rw [rawSphereArea, Measure.smul_apply, smul_eq_mul, raw_mass,
      Measure.toSphere_apply' _ hs, RawCone.cone_volume_stereographic s hs]
    have hd : ∀ z : ℂ, 0 ≤ denominator z ^ (-2 : ℝ) := fun z => Real.rpow_nonneg
      (by unfold denominator; positivity) _
    simp_rw [ENNReal.ofReal_div_of_pos Real.pi_pos]
    simp_rw [div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (by simp [Real.pi_pos])]
    have he : (ENNReal.ofReal (4 * Real.pi))⁻¹ * ↑(Module.finrank ℝ rawAmbient) *
        ENNReal.ofReal (4 / 3 : ℝ) = (ENNReal.ofReal Real.pi)⁻¹ := by
      have hr : Module.finrank ℝ rawAmbient = 3 := by simp [rawAmbient]
      rw [hr]
      norm_num only [Nat.cast_ofNat]
      rw [← ENNReal.ofReal_inv_of_pos (by positivity)]
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_inv_of_pos Real.pi_pos]
      congr 1
      field_simp
      <;> ring
    simp only [← div_eq_mul_inv] at *
    rw [← mul_assoc, ← mul_assoc, he, mul_comm]
    rfl

  · intro z
    rw [Real.rpow_neg (denominator_pos z).le, Real.rpow_two]
    field_simp

end DedekindZetaZeroFree.ComplexLocal.StereographicTransport
