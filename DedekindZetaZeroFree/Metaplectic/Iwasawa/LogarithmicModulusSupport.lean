module

public import DedekindZetaZeroFree.Metaplectic.Iwasawa.GlobalLogarithmicModulus

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources KPGlobalTorusFiniteStages KPLocalPrincipalSeries
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

def localLog (g : Raw R) : KPHilbert.Place F → ℝ
  | .inl w => 2 * Real.log (KPComplexIntertwinerParameterMajorant.rowRatio (complexMatrix R w (g (.inl w))))
  | .inr q => Real.log (LocalCompactChange.forwardAbs F R.A.zeta12 R.A.primitive_zeta12 q
      (C.canonical q) (fullCompact R P C q)
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) (g (.inr q))))

theorem height_eq_stage_localLog (s : RestrictedTensorSimple.Level (bad R P C))
    (g : Raw R) (htail : ∀ p, p ∉ s.val → localLog R P C g p = 0) :
    ThetaExpansion.iwasawaLogHeight R
      (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)) =
      ∑ j : s.val, localLog R P C g j := by
  have hglobal := height_raw_local_logs R P C g
  have hf : (∑ᶠ q : KPFinitePlace F, localLog R P C g (.inr q)) =
      ∑ q ∈ s.val.toRight, localLog R P C g (.inr q) := by
    apply finsum_eq_sum_of_support_subset
    intro q hq
    by_contra h
    exact hq (htail (.inr q) (fun hv => h (Finset.mem_toRight.mpr hv)))
  rw [Finset.sum_coe_sort, Finset.sum_sum_eq_sum_toLeft_add_sum_toRight, stage_toLeft R P C]
  change _ = (∑ w : InfinitePlace F, localLog R P C g (.inl w)) +
    ∑ q ∈ s.val.toRight, localLog R P C g (.inr q)
  rw [← hf]
  exact hglobal

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
