module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactAverages.ProbabilityHaarIdentification
public import DedekindZetaZeroFree.Eisenstein.Residues.Spherical.FullBoundaryLaw

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
open KPContSectorCoveredQuotientVocabulary KPContFlatCuspIncomingEvaluation
open KPGlobalResidualConstruction
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming K_U_compact → K_U_compact
open _root_.DedekindZetaZeroFree renaming canonicalRealization → canonicalRealization
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "Core" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
variable (D : KPGlobalTorusInducingPlan.ModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (HR : KPSmoothLocalQuotientCharts.HaarRecipe F R.A.zeta12 R.A.primitive_zeta12)
variable (HP : KPMsFixedHaarDisintegration.SphericalTransport F R.A.zeta12 R.A.primitive_zeta12)
variable (M : NativeMeasuredSource F R.A.zeta12 R.A.primitive_zeta12 HR HP)
variable (U : Level F R.A.zeta12 R.A.primitive_zeta12)
local notation "H" => nativeFamily F ζ hζ HR HP
local notation "V" => EisensteinSmoothGerms.ScalarSource.atlasLevel F ζ hζ U
local instance (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

theorem spherical_boundary_full_pairing (hU : cofinalLevel F ζ hζ U = U)
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (z : KPContActualAllCuspSource.Sector F ζ hζ D HR HP H U)
    (hb : SphericalBoundaryProperty R P C D HR HP H U v z)
    (ν : Measure (K_U F ζ hζ V)) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    (dk : Measure (KPMsGreenFlux.K F)) [IsProbabilityMeasure dk] [dk.IsHaarMeasure]
    (x : Core)
    (hx : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ U →
      coreResidue R P C x (g*u)=coreResidue R P C x g)
    (u : KPContActualAllCuspSource.SmoothSections F ζ hζ D HR HP H U)
    (uH : KPContActualAllCuspSource.Sector F ζ hζ D HR HP H U)
    (huH : ((uH.val : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ HR V) :
      KPContActualAllCuspSource.Covered F ζ hζ D HR HP H U → ℂ)
      =ᵐ[KPContActualAllCuspSource.measure F ζ hζ D HR HP H U]
        KPContActualCutoffSmoothDescent.scalar F ζ hζ D HR HP H U u)
    (heigen : (uH, KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ):ℤ) 0 • uH) ∈
      (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ V HR HP H
        HR.adelicHaar HR.adelic_isHaar rfl canonicalRealization).graph)
    (hpin : KPContActualCommonDiskRightHolomorphy.lift F ζ hζ V HR HP H u.val =
      ResidualRawAverage.average F ζ hζ (K_U F ζ hζ V) ν (coreResidue R P C x)) :
    inner ℂ uH z = ((fullMass M).toReal : ℂ) *
      (∫ω, boundaryFullAverage R P C (nativeDatum F ζ hζ) dk v.val x ω ∂fullNu M) := by
  have havg (j : Cusps F ζ hζ D HR HP H U) (g : KPLiteralRaw.G F ζ hζ) :
      upperConstantTerm F ζ hζ (KPWildKernelUpperBound.quotientHaar F)
        (ResidualRawAverage.average F ζ hζ (K_U F ζ hζ V) ν (coreResidue R P C x)) g =
      ∫k, upperConstantTerm F ζ hζ (KPWildKernelUpperBound.quotientHaar F)
        (coreResidue R P C x) (g*KPMsGreenFlux.compactInsertion F ζ hζ k) ∂dk := by
    rw [ResidualAverageCusp.original_upper_average ((H).atlas V) j
      (K_U F ζ hζ V) (K_U_compact F ζ hζ V) ν (coreResidue R P C x)
      (coreResidue_raw_automorphic R P C x).1.1 (coreResidue_rational_subgroup R P C x)]
    apply ResidualCompactAverageProjection.probability_average_eq_arch F ζ hζ V ν dk
    · exact ResidualBoundaryInvariance.upper_continuous _
        (coreResidue_raw_automorphic R P C x).1.1 (coreResidue_rational_subgroup R P C x)
    · intro a c hc
      apply integral_congr_ae
      filter_upwards with q
      rw [←mul_assoc]
      exact hx _ c.val (atlasLevel_mem_globalLevel F ζ hζ D HR HP H U ⟨c,hc⟩)
  rw [hb (K_U F ζ hζ V) (K_U_compact F ζ hζ V) ν x u uH huH heigen hpin]
  refine (ResidualSphericalBoundaryBeta.projected_boundary_eq_beta F ζ hζ D HR HP H U v
    (fun j => upperConstantTerm F ζ hζ (KPWildKernelUpperBound.quotientHaar F)
      (ResidualRawAverage.average F ζ hζ (K_U F ζ hζ V) ν (coreResidue R P C x))
      (finiteRepresentative F ζ hζ D HR HP H U j 1).val)).trans ?_
  rw [spherical_boundary_full_law R P C D M U dk hU v x hx]
  apply integral_congr_ae
  filter_upwards with ω
  rw [havg ω.1]
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
