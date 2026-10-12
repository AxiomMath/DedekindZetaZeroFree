module

public import DedekindZetaZeroFree.Eisenstein.Residues.Boundary.CompatibleLevels
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.ScalarBoundaryPairing

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

include M in
theorem spherical_refined_boundary_pairing (Vnew : Level F ζ hζ)
    (hVU : Vnew.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (hU : cofinalLevel F ζ hζ U = U)
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (Z : KPContActualAllCuspSource.SmoothSections F ζ hζ D HR HP H U)
    (z : KPContActualAllCuspSource.Sector F ζ hζ D HR HP H U)
    (hz : KPContActualSmoothLineGluing.Represents F ζ hζ V HR HP H Z.val z)
    (hb : SphericalBoundaryProperty R P C D HR HP H U v z)
    (dk : Measure (KPMsGreenFlux.K F)) [IsProbabilityMeasure dk] [dk.IsHaarMeasure]
    (x : Core)
    (hx : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ U →
      coreResidue R P C x (g*u)=coreResidue R P C x g)
    (f : KPSmoothLocalQuotientCharts.X F ζ hζ → ℂ)
    (hf : MemLp f 2 HR.quotientHaar)
    (hfx : ∀g, f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) = coreResidue R P C x g) :
    (∫q, star (f q) * ResidualSphericalGeometry.originalScalar F ζ hζ V HR HP H Z q
      ∂ HR.quotientHaar) = ∫ω, ∫k, boundaryProduct R P C v.val x
      (KPMsGreenFlux.compactInsertion F ζ hζ k *
        (KPBoundedCuspFrames.actualFiniteRepresentative
          (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) Vnew) ω.1).val) ∂dk
      ∂(nativeDisintegration F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) Vnew).beta := by
  rw [spherical_original_boundary_pairing R P C D HR HP M U hU v Z z hz hb dk x hx f hf hfx]
  apply boundary_full_mass_eq_beta R P C M Vnew dk v.val x
  · intro g u hu
    exact (v.property.1 g ⟨u, ResidualBoundaryRelevel.globalLevel_mono F ζ hζ hVU hu⟩).1
  · intro g u hu
    exact hx g u (ResidualBoundaryRelevel.globalLevel_mono F ζ hζ hVU hu)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
