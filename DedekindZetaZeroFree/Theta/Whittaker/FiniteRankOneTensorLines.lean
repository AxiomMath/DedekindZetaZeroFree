module

public import DedekindZetaZeroFree.Theta.Whittaker.Tensors.FiniteRank
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.SphericalReferences
public import DedekindZetaZeroFree.Theta.Periods.Wild.FiniteDetection

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
set_option maxHeartbeats 2000000
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)

variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)

variable
    (hR : RootAligned R) (N : TraceHaarTransport R) (hC : C.exceptional = R.A.Sf)
    (u : ∀ j : bad R.A P C, Plus R.A P C j.val)
    (hspherical : ∀ z (p : KPFinitePlace F), p ∉ R.A.Sf →
      ∀ k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p),
        k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) →
      ∀ g, (coreFlatInsertion R P C (RestrictedTensorSimple.stageInclusion _ _ _ ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ u))).val z
        (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) k)) =
        (coreFlatInsertion R P C (RestrictedTensorSimple.stageInclusion _ _ _ ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ u))).val z g)
    (hx : fourier R (KPWildKernelUpperBound.quotientHaar F)
      (coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _
        ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ u))) 1 ≠ 0)

local notation "DC" => canonicalCovariantNative R P C μ hμ  hR N hC u hspherical hx
set_option quotPrecheck false
local notation "HC" => (DC).toGenerated.tensorHC
local notation "H" => actualImageData R P C μ hμ

open KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod WildCurrentGlobalMap
open WildFiniteExteriorAssembly KPAdelicCoverRestrictedProduct
local notation "D" => (DC).tensorDetected.toTensorActions

theorem canonicalFinite_all_rank (q : KPFinitePlace F) :
    Module.rank ℂ ((D).toTensorHC.sliceLine (Sum.inr q))≤1 := by
  by_cases hq : (3:𝓞 F)∈q.asIdeal
  · have hfin : {p:KPFinitePlace F | (3:𝓞 F)∈p.asIdeal}.Finite := by
      have h3 : (3:𝓞 F)≠0 := by norm_num
      simpa only [Ideal.dvd_iff_le,Ideal.span_singleton_le_iff_mem] using
        (Ideal.finite_factors (I:=Ideal.span {(3:𝓞 F)}) (by
          intro h
          apply h3
          exact Ideal.span_singleton_eq_bot.mp h))
    let T := hfin.toFinset
    have hqT : q∈T := by simpa [T] using hq
    obtain ⟨s,hT,x,hdet⟩ := exists_detected_stage (DC).tensorDetected T
    have ht : ∀p:KPFinitePlace F,Sum.inr p∉places T → WildCurrentTameExterior.tameSlot (Sum.inr p) := by
      intro p hp
      change (3:𝓞 F)∉p.asIdeal
      intro he
      apply hp
      simp [places,T,he]
    exact canonicalFinite_slice_rank R P C μ hμ  hR N hC u hspherical hx T s hT x hdet ht ⟨q,hqT⟩
  · exact TensorActions.finite_slice_rank_le_one_of_three_not_mem (D) q hq

def canonicalTensorFiniteLines : TensorFiniteLines R N where
  toTensorSpherical := (DC).tensorDetected.spherical
  finite_rank := canonicalFinite_all_rank R P C μ hμ  hR N hC u hspherical hx

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
