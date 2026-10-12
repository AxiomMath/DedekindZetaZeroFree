module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.BoundaryGroupInvariance
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Complex.OperatorWordBounds

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Topology Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.CurrentComplexBoundary
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPGlobalResidualConstruction
open NativeComplexHCOperators KPSmoothActualFlowData
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeComplexHCOperators renaming mf_diff → mf_diff
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeComplexHCOperators renaming mf_gl → mf_gl
open _root_.DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts renaming topology_withSeminorms → topology_withSeminorms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
 abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
open scoped Matrix.Norms.Operator in
 instance : NormedAlgebra ℚ Mat := NormedAlgebra.restrictScalars ℚ ℝ _
open scoped Matrix.Norms.Operator in
theorem flow_hasDerivAt (s : ℝ) (X : Mat) (f : PrincipalSeries s) (g : ComplexGL2) (t : ℝ) :
    HasDerivAt (fun u : ℝ => f (g * matrixExponential ((u : ℂ) • X)))
      (derivative s X f (g * matrixExponential ((t : ℂ) • X))) t := by
  have hm : HasDerivAt (fun u : ℝ => (g : Mat) * NormedSpace.exp ((u : ℂ) • X))
      (((g : Mat) * NormedSpace.exp ((t : ℂ) • X)) * X) t := by
    have h := (((hasDerivAt_exp_smul_const (𝕂 := ℂ) X (t : ℂ)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (f := fun u : ℝ => (u : ℂ)) t Complex.ofRealCLM.hasDerivAt)
    have ht := h.const_mul (g : Mat)
    change HasDerivAt (fun u : ℝ => (g : Mat) * NormedSpace.exp ((u : ℂ) • X))
      ((g : Mat) * ((1 : ℂ) • (NormedSpace.exp ((t : ℂ) • X) * X))) t at ht
    simpa only [one_smul, mul_assoc] using ht
  have hc := (mf_diff s f (g * matrixExponential ((t : ℂ) • X))).hasFDerivAt.comp_hasDerivAt_of_eq t hm rfl
  have heq : (fun u : ℝ => f (g * matrixExponential ((u : ℂ) • X))) =
      matrixFunction f ∘ (fun u : ℝ => (g : Mat) * NormedSpace.exp ((u : ℂ) • X)) := by
    funext u
    exact (mf_gl f (g * matrixExponential ((u : ℂ) • X))).symm
  rw [heq]
  exact hc

open scoped Matrix.Norms.Operator in
theorem flow_continuous (X : Mat) : Continuous (fun t : ℝ => matrixExponential ((t : ℂ) • X)) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)
  · change Continuous (fun t : ℝ => ((NormedSpace.isUnit_exp ((t : ℂ) • X)).unit⁻¹).val)
    simp only [← Ring.inverse_of_isUnit, Ring.inverse_exp]
    exact NormedSpace.exp_continuous.comp ((Complex.continuous_ofReal.smul continuous_const).neg)

theorem translated_flow_continuous (s : ℝ) (X : Mat) (f : PrincipalSeries s) :
    Continuous (fun t : ℝ => KPCplxPrincipalSeriesCharts.rightTranslate s (matrixExponential ((t : ℂ) • X)) f) := by
  exact (pi_continuous s).comp ((QuotientGroup.continuous_mk.comp (flow_continuous X)).prodMk continuous_const)

theorem translated_flow_seminorm_bound (s : ℝ) (X : Mat) (f : PrincipalSeries s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      chartSeminorm s 0 (KPCplxPrincipalSeriesCharts.rightTranslate s (matrixExponential ((t : ℂ) • X)) f) ≤ B := by
  have hc := ((topology_withSeminorms s).continuous_seminorm 0).comp (translated_flow_continuous s X f)
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun t ht => (hB ⟨t,ht,rfl⟩).trans (le_max_left _ _)⟩
end DedekindZetaZeroFree.CurrentComplexBoundary

end
