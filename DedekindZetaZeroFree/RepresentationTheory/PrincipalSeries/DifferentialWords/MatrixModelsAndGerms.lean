module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.BoundaryOperatorWords

@[expose] public section

noncomputable section
open scoped Classical Topology Matrix.Norms.Operator
open Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPGlobalResidualConstruction
open NativeComplexHCOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
 instance : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℝ _
 theorem exponential_continuous (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (fun t : ℝ => KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X)) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)
  · change Continuous (fun t : ℝ => ((NormedSpace.isUnit_exp ((t : ℂ) • X)).unit⁻¹).val)
    simp only [← Ring.inverse_of_isUnit, Ring.inverse_exp]
    exact NormedSpace.exp_continuous.comp ((Complex.continuous_ofReal.smul continuous_const).neg)
 theorem exponential_zero : KPSmoothActualFlowData.matrixExponential
    (0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  apply Units.ext
  exact NormedSpace.exp_zero

def literalMatrixWord : List (Matrix (Fin 2) (Fin 2) ℂ) →
    (ComplexGL2 → ℂ) → ComplexGL2 → ℂ
  | [],f => f
  | X::w,f => fun g => deriv (fun t : ℝ => literalMatrixWord w f
      (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0

theorem literalMatrixWord_model (s : ℝ) (w : List (Matrix (Fin 2) (Fin 2) ℂ))
    (f : PrincipalSeries s) : literalMatrixWord w f =
      (CurrentComplexBoundary.matrixWord s w f).val := by
  induction w with
  | nil => rfl
  | cons X w hw =>
    funext g
    change deriv (fun t : ℝ => literalMatrixWord w f
      (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0 = _
    rw [hw]
    exact (hasDerivAt_flow s X (CurrentComplexBoundary.matrixWord s w f) g).deriv

theorem literalMatrixWord_germ (w : List (Matrix (Fin 2) (Fin 2) ℂ))
    {f h : ComplexGL2 → ℂ} {g : ComplexGL2} (he : f =ᶠ[𝓝 g] h) :
    literalMatrixWord w f =ᶠ[𝓝 g] literalMatrixWord w h := by
  induction w with
  | nil => exact he
  | cons X w hw =>
    filter_upwards [hw.eventuallyEq_nhds] with a ha
    have hc : Tendsto (fun t : ℝ => a * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))
        (𝓝 0) (𝓝 a) := by
      simpa only [Complex.ofReal_zero,zero_smul,exponential_zero,mul_one] using
        (show Continuous (fun t : ℝ => a * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X)) from continuous_const.mul (exponential_continuous X)).tendsto 0
    exact (ha.comp_tendsto hc).deriv_eq

theorem literalMatrixWord_of_model_germ (s : ℝ)
    (w : List (Matrix (Fin 2) (Fin 2) ℂ)) (f : ComplexGL2 → ℂ)
    (h : PrincipalSeries s) (g : ComplexGL2) (he : f =ᶠ[𝓝 g] h.val) :
    literalMatrixWord w f g = CurrentComplexBoundary.matrixWord s w h g := by
  have hword := (literalMatrixWord_germ w he).eq_of_nhds
  rw [literalMatrixWord_model] at hword
  exact hword
end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
