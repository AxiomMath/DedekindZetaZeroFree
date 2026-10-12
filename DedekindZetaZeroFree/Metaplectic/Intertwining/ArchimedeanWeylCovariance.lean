module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.ArchimedeanRootTransport
public import DedekindZetaZeroFree.Metaplectic.Intertwining.StandardIntegral.AbsoluteIntegrability

@[expose] public section

noncomputable section
open scoped NumberField Classical
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

theorem actual_forward_arch_covariance
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (s : ℂ) (v : S) (u : NumberField.InfinitePlace F → ℝ)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    (∫ x : Adeles F, KPContActualSphericalFlatStage.L F ζ hζ U ι s v
      (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x *
        ((KPContFlatArchDiagonalMultiplier.aInfinity F ζ hζ u).val * g))
      ∂KPAdditiveHaar.adelicMeasure F) =
    Complex.exp (((2 : ℂ) / 3 - 2 * s) * ((∑ w, u w : ℝ) : ℂ)) *
      (∫ x : Adeles F, KPContActualSphericalFlatStage.L F ζ hζ U ι s v
        (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x * g)
        ∂KPAdditiveHaar.adelicMeasure F) := by
  simp_rw [forward_integrand_arch_transport F ζ hζ U ι s v u]
  rw [integral_const_mul, integral_arch_mul F ζ hζ u _
    (standard_measurable F ζ hζ U ι s v g)]
  rw [← mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
