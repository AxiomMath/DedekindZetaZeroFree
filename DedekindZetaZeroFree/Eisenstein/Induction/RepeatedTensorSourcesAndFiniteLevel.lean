module

public import DedekindZetaZeroFree.Theta.Whittaker.Nonvanishing.PlusSectionFourierCoefficient
public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothGermRealization

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages MomentSources ThetaExpansion TensorActionSource
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource renaming refinedLevel → refinedLevel
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource renaming refinedLevel_le → refinedLevel_le
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)

theorem coreFlatInsertion_common_level (x : V) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F R.A.zeta12 R.A.primitive_zeta12,
      ∀ z g u, u ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 J →
        (coreFlatInsertion R P C x).val z (g * u) = (coreFlatInsertion R P C x).val z g := by
  obtain ⟨J,hJ⟩ := quotientCoreValue_uniform_level R.A P C x
  refine ⟨refinedLevel R P C J, ?_⟩
  intro z g u hu
  change Complex.exp _ * quotientCoreEvaluator R.A P C x (g * u) =
    Complex.exp _ * quotientCoreEvaluator R.A P C x g
  rw [height_compact R g ⟨u,refinedLevel_le R P C J hu⟩,
    hJ g u (Subgroup.map_mono inf_le_left hu)]

def repeatedCoreSources (x : V)
    (hspherical : ∀ z (p : KPFinitePlace F), p ∉ R.A.Sf →
      ∀ k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p),
        k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) →
      ∀ g, (coreFlatInsertion R P C x).val z
        (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) k)) =
        (coreFlatInsertion R P C x).val z g) : AdmissibleFlatSources R where
  K := fullProductCompact R
  iwasawa := full_product_compact_iwasawa R
  flat := fun _ => asLiteralFlat (coreFlatInsertion R P C x)
  finite_companions := by
    letI := SArithmeticData.sunitSixthPowerQuotient_finite F R.A
    exact Finite.of_equiv (PowerQuotient R.A.Rˣ 6)
      (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv R.A.U R.A.Rˣ 6 R.A.unitEquiv).symm.toEquiv
  level := (coreFlatInsertion_common_level R P C x).choose
  common_level := fun _ => (coreFlatInsertion_common_level R P C x).choose_spec
  ordinary := fun _ z => induced_ordinary_central_covariance R z _
    ((coreFlatInsertion R P C x).property.1 z)
  exterior_spherical := fun _ => hspherical
  dq := KPWildKernelUpperBound.quotientHaar F
  quotientHaar := inferInstance
  probability := by
    exact Measure.addHaarMeasure_self (K₀ := ⊤)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
