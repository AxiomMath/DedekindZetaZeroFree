module

public import DedekindZetaZeroFree.Metaplectic.Iwasawa.LogarithmicModulusSupport

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources KPGlobalTorusFiniteStages KPLocalPrincipalSeries
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

def parameterValue (g : Raw R) (z : ℂ) (p : KPHilbert.Place F) :
    Plus R N P C p →ₗ[ℂ] Fiber R P C p :=
  Complex.exp (z * (localLog R P C g p : ℂ)) • localValue R N P C p (g p)

theorem parameterValue_tensor (s : RestrictedTensorSimple.Level (bad R P C))
    (g : Raw R) (z : ℂ) (y : RestrictedTensorSimple.Stage (Plus R N P C) s.val) :
    PiTensorProduct.map (fun j : s.val => parameterValue R N P C g z j) y =
      Complex.exp (z * ((∑ j : s.val, localLog R P C g j) : ℂ)) •
        PiTensorProduct.map (fun j : s.val => localValue R N P C j (g j)) y := by
  have hmap : PiTensorProduct.map (fun j : s.val => parameterValue R N P C g z j) =
      (∏ j : s.val, Complex.exp (z * (localLog R P C g j : ℂ))) •
        PiTensorProduct.map (fun j : s.val => localValue R N P C j (g j)) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro f
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
      LinearMap.smul_apply, parameterValue]
    exact (PiTensorProduct.tprod ℂ).map_smul_univ _ _
  rw [hmap, LinearMap.smul_apply]
  congr 1
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]

theorem parameterValue_finite (g : Raw R) (z : ℂ) (q : KPFinitePlace F)
    (f : Plus R N P C (.inr q)) :
    parameterValue R N P C g z (.inr q) f =
      (finiteParameterInput R N P C q (fullCompact R P C q) z f).val
        (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) (g (.inr q))) :=
  (finiteParameterInput_displacement R N P C q (fullCompact R P C q) z f _).symm

theorem parameterValue_complex (g : Raw R) (z : ℂ) (w : InfinitePlace F)
    (f : Plus R N P C (.inl w)) :
    parameterValue R N P C g z (.inl w) f =
      (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12
        (g (.inl w)).epsilon : ℂ) *
      KPComplexIntertwinerParameterMajorant.forwardSection z (complexInput f.val)
        (complexMatrix R w (g (.inl w))) := by
  rw [complexInput_forward]
  change Complex.exp (z * (↑(2 * Real.log _) : ℂ)) * (_ * _) =
    _ * (Complex.exp (2*z*(Real.log _ : ℂ)) * _)
  push_cast
  ring

theorem sourceFlat_parameter_raw (s : RestrictedTensorSimple.Level (bad R P C))
    (g : Raw R) (hg : ∀ p, p ∉ s.val →
      localValue R N P C p (g p) (plusReference R N P C p) = reference R P C p)
    (htail : ∀ p, p ∉ s.val → localLog R P C g p = 0)
    (z : ℂ) (y : RestrictedTensorSimple.Stage (Plus R N P C) s.val) :
    (sourceFlat R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s y)).val z
      (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)) =
      (comparisonSmooth R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
        (PiTensorProduct.map (fun j : s.val => parameterValue R N P C g z j) y))).val.val 1 := by
  have he : scalarSourceEvaluator R N P C
      (RestrictedTensorSimple.stageInclusion _ _ _ s y)
      (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)) =
      (comparisonSmooth R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
        (PiTensorProduct.map (fun j : s.val => localValue R N P C j (g j)) y))).val.val 1 := by
    change (comparisonSmooth R P C (quotientCoreVector R N P C
      (RestrictedTensorSimple.stageInclusion _ _ _ s y)
      (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)))).val.val 1 = _
    rw [quotientCoreVector_raw, rawCoreVector_stage R N P C s g hg]
    rfl
  rw [sourceFlat_value, height_eq_stage_localLog R P C s g htail, he, parameterValue_tensor]
  simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sum]

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
