module

public import DedekindZetaZeroFree.Eisenstein.Residues.Source.UpperWordAdjoint

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open CurrentRepairedLocalBinding MomentSources KPGlobalTorusFiniteStages
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar KPGlobalResidualConstruction
open KPContActualSphericalRightFieldIdentification CurrentComplexBoundary
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "Core" => RestrictedTensorSimple.Core (LiteralSource.Plus R.A P C) (LiteralSource.plusReference R.A P C) (LiteralSource.bad R.A P C)
local instance : CompactSpace ComplexSU2 := by
  apply isCompact_iff_compactSpace.mp
  convert complexSU2_isCompact using 1
  exact Subtype.range_coe.symm
local instance : CompactSpace compactSubgroup := isCompact_iff_compactSpace.mp compactSubgroup_isCompact
include N in
theorem compact_source_upper_word_adjoint_haar
    (dk : Measure (KPMsGreenFlux.K F)) [IsProbabilityMeasure dk] [dk.IsHaarMeasure]
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (x : Core) (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    {hF : InfinitePlace.nrRealPlaces F = 0}
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (j : KPMsGreenFlux.Cusps A)
    (f : KPSmoothActualFlowData.X F ζ hζ → ℂ)
    (hf : ∀v, KPSmoothActualFlowData.SmoothAutomorphic F ζ hζ (KPSmoothActualFlowData.wordDerivative F ζ hζ v f))
    (hfx : ∀g, f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)=LiteralSource.coreResidue R P C x g)
    (w : List (Fin (groupDimension F))) :
    (∫k,t.val.val (KPMsGreenFlux.compactInsertion F ζ hζ k*c.val) *
      star (originalUpper R (actualRightWord F ζ hζ w.reverse (LiteralSource.coreResidue R P C x))
        (KPMsGreenFlux.compactInsertion F ζ hζ k*c.val)) ∂dk) =
    (-1 : ℂ)^w.length * (∫k,actualRightWord F ζ hζ w t.val.val
      (KPMsGreenFlux.compactInsertion F ζ hζ k*c.val) *
      star (originalUpper R (LiteralSource.coreResidue R P C x)
        (KPMsGreenFlux.compactInsertion F ζ hζ k*c.val)) ∂dk) := by
  let Kρ : TopologicalSpace.PositiveCompacts ComplexSU2 := ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩
  let Kν : TopologicalSpace.PositiveCompacts compactSubgroup := ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩
  let ρ := Measure.haarMeasure Kρ
  let ν := Measure.haarMeasure Kν
  letI : IsProbabilityMeasure ρ := ⟨Measure.haarMeasure_self⟩
  letI : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self⟩
  exact compact_source_upper_word_adjoint R N P C  ρ dk (fun _=>ν) t x c U A j f hf hfx w
end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
