module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.TensorWordDerivatives
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.DifferentialWords.MatrixModelsAndGerms

@[expose] public section

noncomputable section
open scoped Classical Topology
open Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open KPCplxCharacterHaar
open _root_.DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices renaming exponential_continuous → exponential_continuous
open _root_.DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices renaming exponential_zero → exponential_zero
set_option backward.isDefEq.respectTransparency false
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem tupleWord_germ (w : List (MatrixLetter ι))
    {f h : (ι → ComplexGL2) → ℂ} {a : ι → ComplexGL2} (he : f =ᶠ[𝓝 a] h) :
    tupleWord w f =ᶠ[𝓝 a] tupleWord w h := by
  induction w with
  | nil => exact he
  | cons b w hw =>
    filter_upwards [hw.eventuallyEq_nhds] with x hx
    have hc : Continuous (fun t : ℝ => Function.update x b.1
        (x b.1 * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • b.2))) :=
      continuous_const.update b.1 (continuous_const.mul (exponential_continuous b.2))
    have ht : Tendsto (fun t : ℝ => Function.update x b.1
        (x b.1 * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • b.2))) (𝓝 0) (𝓝 x) := by
      simpa only [Complex.ofReal_zero,zero_smul,exponential_zero,mul_one,Function.update_eq_self]
        using hc.tendsto 0
    exact (hx.comp_tendsto ht).deriv_eq
end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
