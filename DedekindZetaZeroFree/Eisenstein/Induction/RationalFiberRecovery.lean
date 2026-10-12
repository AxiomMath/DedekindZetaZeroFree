module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ProductSections.HarishChandraCompatibility
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.RationalInduction

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct
open KPGlobalTorusPeriodizationInverse hiding productModel
attribute [local instance] KPGlobalTorusPeriodizationInverse.modelTopology
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
private theorem deltaHalf_ne_zero (e : KPGlobalTorusFunctionData.E F ζ hζ) :
    KPGlobalTorusFunctionData.deltaHalf F ζ hζ e ≠ 0 := by
  have hd : (0:ℝ) < ((KPGlobalTorusFunctionData.delta F ζ hζ e : ℝ≥0) : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero _))
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hd).ne'

theorem inducedRationalFiber_core (x : RestrictedTensorSimple.Core
    (Plus A P C) (plusReference A P C) (bad A P C)) (g : Raw A) :
    inducedRationalFiber A (quotientCoreEvaluator A P C x)
      (quotientCoreEvaluator_induced A P C x)
      (scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) =
      PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F ζ hζ P
        (rawCoreFiber A P C g x) := by
  apply Subtype.ext
  apply Subtype.ext
  funext e
  obtain ⟨u,t,a,d,ht,hp,he⟩ := EisensteinReferenceSections.TorusNorms.raw_lifts F ζ hζ e
  change (KPGlobalTorusFunctionData.deltaHalf F ζ hζ e)⁻¹ *
    quotientCoreValue A P C x (e.val * scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) = _
  rw [← he, ← map_mul, ← map_mul, quotientCoreValue_raw, rawCoreValue_fiber,
    rawCoreFiber_torus A P C x u g t a d (fun _ => 0) e ht hp he]
  rw [map_smul,map_smul]
  change (KPGlobalTorusFunctionData.deltaHalf F ζ hζ e)⁻¹ *
    ((KPGlobalTorusFunctionData.deltaHalf F ζ hζ e *
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ)) *
      ((untwistRational F ζ hζ).symm (unitaryPeriodization F ζ hζ P
        (rightAction F ζ hζ (productModel F ζ hζ P) e (rawCoreFiber A P C g x)))).val.val 1) =
    ((untwistRational F ζ hζ).symm (unitaryPeriodization F ζ hζ P
      (rawCoreFiber A P C g x))).val.val e
  rw [unitaryPeriodization_intertwines,retwistRational_formula,rightAction_formula,
    one_mul,retwistRational_formula]
  simp only [map_one,Units.val_one,NNReal.coe_one,Complex.ofReal_one,one_mul]
  simp only [← mul_assoc,inv_mul_cancel₀ (deltaHalf_ne_zero A e),one_mul]

theorem originalProductScalar_core (x : RestrictedTensorSimple.Core
    (Plus A P C) (plusReference A P C) (bad A P C)) (g : Raw A) :
    originalProductScalar A P (quotientCoreEvaluator A P C x)
      (quotientCoreEvaluator_induced A P C x)
      (scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) =
        (rawCoreFiber A P C g x).val.val 1 := by
  unfold originalProductScalar originalProductFiber
  rw [inducedRationalFiber_core]
  change (averaging F ζ hζ P ((untwistRational F ζ hζ).symm
    (unitaryPeriodization F ζ hζ P (rawCoreFiber A P C g x)))).val.val 1 = _
  change (averaging F ζ hζ P ((untwistRational F ζ hζ).symm
    ((untwistRational F ζ hζ) (periodization F ζ hζ P
      ((untwistProduct F ζ hζ P).symm (rawCoreFiber A P C g x)))))).val.val 1 = _
  rw [ContinuousLinearEquiv.symm_apply_apply,averaging_periodization,retwistProduct_formula]
  simp only [map_one,Units.val_one,NNReal.coe_one,Complex.ofReal_one,one_mul]

theorem originalProductScalar_injective
    (f h : Functions F ζ hζ) (hf : KPLiteralRaw.Induced F ζ hζ 0 f)
    (hh : KPLiteralRaw.Induced F ζ hζ 0 h)
    (he : originalProductScalar A P f hf = originalProductScalar A P h hh) : f = h := by
  funext g
  have hp : originalProductFiber A P f hf g = originalProductFiber A P h hh g := by
    apply Subtype.ext
    apply Subtype.ext
    funext e
    have h1 := congrArg (fun v : ProductSmooth F ζ hζ P => v.val.val 1)
      (originalProductFiber_covariance A P f hf e 0 g)
    have h2 := congrArg (fun v : ProductSmooth F ζ hζ P => v.val.val 1)
      (originalProductFiber_covariance A P h hh e 0 g)
    have hN : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
      (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
    simp only [hN,mul_one] at h1 h2
    change originalProductScalar A P f hf (e.val*g) =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ e * (originalProductFiber A P f hf g).val.val (1*e) at h1
    change originalProductScalar A P h hh (e.val*g) =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ e * (originalProductFiber A P h hh g).val.val (1*e) at h2
    rw [one_mul] at h1 h2
    exact mul_left_cancel₀ (deltaHalf_ne_zero A e) (h1.symm.trans ((congrFun he _).trans h2))
  have hi := congrArg (periodization F ζ hζ P) hp
  change periodization F ζ hζ P (averaging F ζ hζ P _) =
    periodization F ζ hζ P (averaging F ζ hζ P _) at hi
  rw [periodization_averaging,periodization_averaging] at hi
  have hv := congrArg (fun v : ↥(KPGlobalResidualConstruction.smoothRationalFiber F ζ hζ) => v.val.val 1) hi
  simpa only [inducedRationalFiber_one] using hv
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
