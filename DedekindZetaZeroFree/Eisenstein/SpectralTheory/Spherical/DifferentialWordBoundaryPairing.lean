module

public import DedekindZetaZeroFree.Eisenstein.Residues.Regularity.WordDerivativeLevel
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.RefinedBoundaryPairing

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

open ResidualWeakEnergy KPContActualSphericalRightFieldIdentification
open KPMsClearedTruncationL2.NativeWordBridge
 abbrev WD := KPSmoothActualFlowData.wordDerivative F ζ hζ

def finiteBoundaryPair (Vnew : Level F ζ hζ) (dk : Measure (KPMsGreenFlux.K F))
    (f g : KPLiteralRaw.G F ζ hζ → ℂ) : ℂ :=
  ∫ω, ∫k, f (KPMsGreenFlux.compactInsertion F ζ hζ k *
      (KPBoundedCuspFrames.actualFiniteRepresentative
        (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) Vnew) ω.1).val) *
    star (∫q : KPAdditiveQuotient F, g (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) *
      (KPMsGreenFlux.compactInsertion F ζ hζ k *
        (KPBoundedCuspFrames.actualFiniteRepresentative
          (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) Vnew) ω.1).val))
      ∂KPWildKernelUpperBound.quotientHaar F) ∂dk
    ∂(nativeDisintegration F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) Vnew).beta

include M in
theorem spherical_word_boundary_pairing (Vnew : Level F ζ hζ)
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
    (f : smoothAllWordL2 HR)
    (w : List (Fin (groupDimension F)))
    (hfx : ∀g, f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) = coreResidue R P C x g) :
    (∫q, star (WD R ((w.map (wordIndexEquiv F)).reverse) f.val q) *
      ResidualSphericalGeometry.originalScalar F ζ hζ V HR HP H Z q ∂ HR.quotientHaar) =
      finiteBoundaryPair R HR HP Vnew dk (KPContFlatSourceRecipe.flatR F ζ hζ 0 v.val).val
        (actualRightWord F ζ hζ w.reverse (coreResidue R P C x)) := by
  obtain ⟨y,hy⟩ := coreResidue_word_range R P C x w.reverse
  have hyU : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ U →
      coreResidue R P C y (g*u)=coreResidue R P C y g := by
    rw [hy]
    exact actual_word_global_level R U (coreResidue R P C x) hx w.reverse
  have hfy : ∀g, WD R ((w.map (wordIndexEquiv F)).reverse) f.val
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) = coreResidue R P C y g := by
    intro g
    have h := actualRightWord_eq_wordDerivative F ζ hζ w.reverse f.val g
    rw [funext hfx] at h
    rw [hy]
    simpa only [List.map_reverse] using h.symm
  have hp := spherical_refined_boundary_pairing R P C D HR HP M U Vnew hVU hU
    v Z z hz hb dk y hyU (WD R ((w.map (wordIndexEquiv F)).reverse) f.val)
    (f.property ((w.map (wordIndexEquiv F)).reverse)).2 hfy
  simpa only [finiteBoundaryPair, boundaryProduct,hy] using hp

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
