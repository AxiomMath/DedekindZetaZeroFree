module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteCenterSums.RightPairing
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.DifferentialWordBoundaryPairing

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
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
variable {n : ℕ} (U : Fin n → Level F R.A.zeta12 R.A.primitive_zeta12)
local notation "H" => nativeFamily F ζ hζ HR HP

local instance (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

open ResidualWeakEnergy KPContActualSphericalRightFieldIdentification
open KPMsClearedTruncationL2.NativeWordBridge

variable (m : Fin n → ℕ)
variable (w : ∀i, Fin (m i) → List (Fin (groupDimension F)))
variable (a : ∀i, Fin (m i) → ℂ)

include M in
theorem finite_center_boundary_pairing
    (v : ∀i, Fin (m i) → KPContActualSphericalFlatStage.Stage F ζ hζ (U i))
    (Z : ∀i, Fin (m i) → KPContActualAllCuspSource.SmoothSections F ζ hζ D HR HP H (U i))
    (z : ∀i, Fin (m i) → KPContActualAllCuspSource.Sector F ζ hζ D HR HP H (U i))
    (Vnew : Level F ζ hζ)
    (hVU : ∀i, Vnew.toOpenSubgroup.toSubgroup ≤ (U i).toOpenSubgroup.toSubgroup)
    (hU : ∀i, cofinalLevel F ζ hζ (U i) = U i)
    (hz : ∀i j, KPContActualSmoothLineGluing.Represents F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ D HR HP H (U i)) HR HP H
      (Z i j).val (z i j))
    (hb : ∀i j, SphericalBoundaryProperty R P C D HR HP H (U i) (v i j) (z i j))
    (he : ∀i j g, KPMsGreenFlux.casimir F ζ hζ
      (KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ D HR HP H (U i) (Z i j)) g =
      KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) 0 *
        KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ D HR HP H (U i) (Z i j) g)
    (dk : Measure (KPMsGreenFlux.K F)) [IsProbabilityMeasure dk] [dk.IsHaarMeasure]
    (x : Core)
    (hx : ∀i g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ (U i) →
      coreResidue R P C x (g*u)=coreResidue R P C x g)
    (f : smoothAllWordL2 HR)
    (hfx : ∀g, f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)=coreResidue R P C x g) :
    (∫q, star (f.val q) * ResidualHilbertCenters.finiteCenterSum F ζ hζ D HR HP H
      U m w a Z q ∂ HR.quotientHaar) =
      ∑i, ∑j, a i j * (-1 : ℂ)^(w i j).length *
        finiteBoundaryPair R HR HP Vnew dk
          (KPContFlatSourceRecipe.flatR F ζ hζ 0 (v i j).val).val
          (actualRightWord F ζ hζ (w i j).reverse (coreResidue R P C x)) := by
  rw [ResidualHilbertCenters.finiteCenterSum_pairing_right F ζ hζ D HR HP H U m w a Z z hz
    (KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) 0) he f]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact spherical_word_boundary_pairing R P C D HR HP M (U i) Vnew (hVU i) (hU i)
    (v i j) (Z i j) (z i j) (hz i j) (hb i j) dk x (hx i) f (w i j) hfx

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
