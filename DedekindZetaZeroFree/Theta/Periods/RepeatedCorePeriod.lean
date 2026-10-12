module

public import DedekindZetaZeroFree.Eisenstein.Induction.RepeatedTensorSourcesAndFiniteLevel
public import DedekindZetaZeroFree.Theta.Periods.NondegenerateCovariantTensorSource

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages MomentSources ThetaExpansion TensorActionSource
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)

theorem exists_repeated_core_period_source
    (hR : RootAligned R) (N : TraceHaarTransport R) (x : V)
    (hspherical : ∀ z (p : KPFinitePlace F), p ∉ R.A.Sf →
      ∀ k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p),
        k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) →
      ∀ g, (coreFlatInsertion R P C x).val z
        (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) k)) =
        (coreFlatInsertion R P C x).val z g)
    (hx : fourier R (KPWildKernelUpperBound.quotientHaar F) (coreResidue R P C x) 1 ≠ 0) :
    ∃ D : NonDegenerate.PeriodSource R N,
      (∀ v, D.realization.theta v = coreResidue R P C x) ∧
      (∀ v, (D.sources.flat v).val = (coreFlatInsertion R P C x).val) := by
  let Q := repeatedCoreSources R P C x hspherical
  let B : JointRootAlignedSources R N := ⟨hR,N,rfl,Q⟩
  obtain ⟨T⟩ := SharedSource.selected_realization_exists  R B
  have hp : ∀ v, T.theta v = coreResidue R P C x := by
    intro v
    exact ((ownedLiteralResidueFamily (full_product_compact_iwasawa R)).residue_selected T v).symm
  let D : NonDegenerate.PeriodSource R N := {
    toJointRealizedFlatSources := ⟨B,T⟩
    probe := 1
    coefficient := fourier R Q.dq (T.theta 1) 1
    coefficient_ne := by rw [hp]; exact hx
    period_limit := fourier_residue_tendsto T 1 1 }
  exact ⟨D,hp,fun _ => rfl⟩
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
