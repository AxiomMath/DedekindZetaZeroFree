module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.ComplexHarmonicEigenvaluesAndSmoothness

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse
open MeasureTheory Set
open scoped RealInnerProductSpace

abbrev Ambient := EuclideanSpace ℝ (Fin 3)
abbrev Sphere := ↥(Metric.sphere (0 : Ambient) 1)

noncomputable def sphereArea : Measure Sphere :=
  ((volume : Measure Ambient).toSphere Set.univ)⁻¹ •
    (volume : Measure Ambient).toSphere

noncomputable def fractionalKernel (α : ℝ) (x y : Sphere) : ℝ :=
  α * Real.rpow ((1 - inner ℝ (x : Ambient) (y : Ambient)) / 2) (α - 1)

noncomputable def fractionalIntegral (α : ℝ) (F : Sphere → ℂ) (x : Sphere) : ℂ :=
  ∫ y : Sphere, (fractionalKernel α x y : ℂ) * F y ∂sphereArea

noncomputable def sphericalScalar (β : ℂˣ) : ℝ :=
  3 * KPCplxCharacterHaar.characterScale β / 2

theorem sphericalScalar_eq_eigenvalue_zero (β : ℂˣ) :
    sphericalScalar β = KPCplxIntertwinerEigenvalues.eigenvalue β 0 :=
  (KPCplxIntertwinerEigenvalues.eigenvalue_zero β).1.symm

theorem sphericalScalar_pos (β : ℂˣ) : 0 < sphericalScalar β := by
  rw [sphericalScalar_eq_eigenvalue_zero]
  exact (KPCplxIntertwinerEigenvalues.eigenvalue_zero β).2

theorem sphereArea_isProbabilityMeasure : IsProbabilityMeasure sphereArea := by
  constructor
  rw [sphereArea, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (Measure.measure_univ_pos.mpr (Measure.toSphere_ne_zero volume)).ne'
    (measure_ne_top _ _)

theorem fractionalKernel_nonneg (α : ℝ) (hα : 0 < α) (x y : Sphere) :
    0 ≤ fractionalKernel α x y := by
  apply mul_nonneg hα.le
  apply Real.rpow_nonneg
  apply div_nonneg _ (by norm_num)
  have h : inner ℝ (x : Ambient) (y : Ambient) ≤ 1 := by
    calc
      _ ≤ ‖(x : Ambient)‖ * ‖(y : Ambient)‖ := real_inner_le_norm _ _
      _ = 1 := by simp [mem_sphere_zero_iff_norm.mp x.property,
        mem_sphere_zero_iff_norm.mp y.property]
  linarith

@[simp] theorem fractionalKernel_one (x y : Sphere) : fractionalKernel 1 x y = 1 := by
  simp [fractionalKernel]

private lemma interval_kernel_integrable (α : ℝ) (hα : 0 < α) :
    Integrable (fun t : ℝ => α * t ^ (α - 1)) (volume.restrict (Icc 0 1)) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
    (r := α - 1) (by linarith)).const_mul α
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp h

private lemma interval_kernel_mass (α : ℝ) (hα : 0 < α) :
    (∫ t : ℝ in Icc 0 1, α * t ^ (α - 1)) = 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
  simp [Real.zero_rpow hα.ne', hα.ne']

theorem fractionalKernel_mass_of_projection (α : ℝ) (hα : 0 < α) (x : Sphere)
    (hprojection : Measure.map
      (fun y : Sphere => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2) sphereArea =
      (volume : Measure ℝ).restrict (Icc 0 1)) :
    Integrable (fractionalKernel α x) sphereArea ∧
    (∫ y : Sphere, fractionalKernel α x y ∂sphereArea) = 1 := by
  let p : Sphere → ℝ := fun y => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2
  have hp : Measurable p := by dsimp [p]; fun_prop
  have hi : Integrable (fun t : ℝ => α * t ^ (α - 1)) (Measure.map p sphereArea) := by
    rw [show Measure.map p sphereArea = _ from hprojection]
    exact interval_kernel_integrable α hα
  constructor
  · exact (integrable_map_measure hi.aestronglyMeasurable hp.aemeasurable).mp hi
  · have h := integral_map hp.aemeasurable hi.aestronglyMeasurable
    rw [show Measure.map p sphereArea = _ from hprojection] at h
    exact h.symm.trans (interval_kernel_mass α hα)

theorem fractionalKernel_mass (α : ℝ) (hα : 0 < α) :
    IsProbabilityMeasure sphereArea ∧
      ∀ x : Sphere, Integrable (fractionalKernel α x) sphereArea ∧
        (∀ y : Sphere, 0 ≤ fractionalKernel α x y) ∧
        (∫ y : Sphere, fractionalKernel α x y ∂sphereArea) = 1 := by
  refine ⟨sphereArea_isProbabilityMeasure, fun x => ?_⟩
  have hprojection : Measure.map
      (fun y : Sphere => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2) sphereArea =
      (volume : Measure ℝ).restrict (Icc 0 1) :=
    (KernelMass.normalized_area_projection_rotation 3 0 x).trans
      KernelMass.normalized_area_coordinate_projection
  obtain ⟨hi, hm⟩ := fractionalKernel_mass_of_projection α hα x hprojection
  exact ⟨hi, fractionalKernel_nonneg α hα x, hm⟩

end DedekindZetaZeroFree.ComplexFractionalInverse
