module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Scattering.MeromorphicNumerators

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPContFlatArchDiagonalMultiplier KPContinuation.ChamberOutgoingSource
variable {F : Type} [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
theorem raw_induced_arch_covariance (s : ℂ) (f : KPLiteralRaw.Functions F ζ hζ)
    (hf : KPLiteralRaw.Induced F ζ hζ s f)
    (u : InfinitePlace F → ℝ) (g : KPLiteralRaw.G F ζ hζ) :
    f ((aInfinity F ζ hζ u).val * g) =
      Complex.exp (((4 : ℂ)/3 + 2*s) * ((∑ w, u w : ℝ) : ℂ)) * f g := by
  let r : KPGlobalCenterRationalCharacter.R F ζ hζ :=
    ⟨aInfinity F ζ hζ u, aInfinity_mem_rational F ζ hζ u⟩
  have hc := source_character F ζ hζ 0 u
  have hc' : (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) =
      Complex.exp (((1 : ℂ)/6) * ((2 * ∑ w, u w : ℝ) : ℂ)) := by
    change (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) *
      KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ 0 (aInfinity F ζ hζ u) = _ at hc
    simpa [KPGlobalTorusBorelTwistCompatibility.normPower] using hc
  have hn : KPGlobalTorusFunctionData.N F ζ hζ (0 : KPAdeles F) = 1 :=
    map_one (KPGlobalTorusFunctionData.Nhom F ζ hζ)
  have he := hf.2 r 0 g
  simp only [hn, mul_one] at he
  change f ((aInfinity F ζ hζ u).val * g) = _ at he
  rw [he, hc']
  unfold KPGlobalExceptionalParameter.realLogPower
  change Complex.exp ((1/2+s) *
    (Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ (aInfinity F ζ hζ u) : NNReal) : ℝ)) : ℂ)) *
    Complex.exp _ * f g = _
  rw [aInfinity_delta, Real.log_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem raw_forward_integral_arch_covariance (s : ℂ)
    (f : KPLiteralRaw.Functions F ζ hζ) (hf : KPLiteralRaw.Induced F ζ hζ s f)
    (u : InfinitePlace F → ℝ) (g : KPLiteralRaw.G F ζ hζ) :
    (∫ y : KPAdeles F, f (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ y *
      ((aInfinity F ζ hζ u).val * g)) ∂KPAdditiveHaar.adelicMeasure F) =
    Complex.exp (((2 : ℂ)/3 - 2*s) * ((∑ w, u w : ℝ) : ℂ)) *
      (∫ y : KPAdeles F, f (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ y * g)
        ∂KPAdditiveHaar.adelicMeasure F) := by
  have he (y : KPAdeles F) :
      f (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ y *
        ((aInfinity F ζ hζ u).val * g)) =
      Complex.exp (-(((4 : ℂ)/3 + 2*s) * ((∑ w, u w : ℝ) : ℂ))) *
        f (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ
          (y * ((archDiagonalIdele F ζ hζ u)⁻¹).val) * g) := by
    rw [← mul_assoc, forward_root_arch_transport, mul_assoc]
    simpa only [Finset.sum_neg_distrib, Complex.ofReal_neg, mul_neg] using
      raw_induced_arch_covariance ζ hζ s f hf (fun w => -u w) _
  have hm : Measurable (fun y : KPAdeles F =>
      f (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ y * g)) := by
    let := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
    have hN := KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous F ζ hζ
    exact (hf.1.1.comp ((continuous_const.mul hN).mul continuous_const)).measurable
  simp_rw [he]
  rw [integral_const_mul, integral_arch_mul F ζ hζ u _ hm, ← mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
theorem coreScattering_arch_covariance
    (x : RestrictedTensorSimple.Core (Plus R.A P C)
      (plusReference R.A P C) (bad R.A P C))
    (s : ℂ) (u : InfinitePlace F → ℝ)
    (g : KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12) :
    coreScattering R P C x s
      ((aInfinity F R.A.zeta12 R.A.primitive_zeta12 u).val * g) =
    Complex.exp (((2 : ℂ)/3 - 2*s) * ((∑ w, u w : ℝ) : ℂ)) *
      coreScattering R P C x s g :=
  raw_forward_integral_arch_covariance R.A.zeta12 R.A.primitive_zeta12 s
    ((coreFlatInsertion R P C x).val s) ((coreFlatInsertion R P C x).property.1 s) u g

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
