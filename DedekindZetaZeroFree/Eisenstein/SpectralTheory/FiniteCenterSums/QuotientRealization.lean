module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.DifferentialWords.SmoothL2Space

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters
open ResidualSphericalGeometry ResidualWeakEnergy KPGlobalResidualConstruction
open KPMsClearedTruncationL2.NativeWordBridge
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (M : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable {n : ℕ} (U : Fin n → KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (m : Fin n → ℕ)
variable (w : ∀ i, Fin (m i) → List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)))
variable (a : ∀ i, Fin (m i) → ℂ)
variable (Z : ∀ i, Fin (m i) → KPContActualAllCuspSource.SmoothSections F ζ hζ M R P H (U i))
 abbrev centerSumWordDerivative := KPSmoothActualFlowData.wordDerivative F ζ hζ

def finiteCenterSum : KPSmoothActualFlowData.X F ζ hζ → ℂ :=
  ∑ i, ∑ j, a i j • centerSumWordDerivative F ζ hζ ((w i j).map (wordIndexEquiv F))
    (originalScalar F ζ hζ (KPContActualAllCuspSource.level F ζ hζ M R P H (U i)) R P H (Z i j))

theorem finiteCenterSum_mem
    (z : ∀ i, Fin (m i) → KPContActualAllCuspSource.Sector F ζ hζ M R P H (U i))
    (hz : ∀ i j, KPContActualSmoothLineGluing.Represents F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ M R P H (U i)) R P H (Z i j).val (z i j))
    (eig : ℂ)
    (he : ∀ i j g, KPMsGreenFlux.casimir F ζ hζ
      (KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ M R P H (U i) (Z i j)) g =
      eig * KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ M R P H (U i) (Z i j) g) :
    finiteCenterSum F ζ hζ M R P H U m w a Z ∈ smoothAllWordL2 R := by
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  let f : KPMsClearedTruncationL2.smoothSpace F ζ hζ
      (ActualSectionLift.nativeLevel F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ M R P H (U i))) :=
    ⟨originalScalar F ζ hζ _ R P H (Z i j), originalScalar_mem_smoothSpace F ζ hζ _ R P H (Z i j)⟩
  exact word_mem_smoothAllWordL2 R f
    (represented_native_eigencenter_all_derivatives F ζ hζ M R P H (U i)
      (Z i j) (z i j) (hz i j) eig (he i j)) _

theorem finiteCenterSum_lift (g : KPSmoothActualFlowData.G F ζ hζ) :
    finiteCenterSum F ζ hζ M R P H U m w a Z
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) =
    ∑ i, ∑ j, a i j * KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ
      (w i j) (KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ M R P H (U i) (Z i j)) g := by
  simp only [finiteCenterSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  let f := originalScalar F ζ hζ (KPContActualAllCuspSource.level F ζ hζ M R P H (U i)) R P H (Z i j)
  have hl : (fun g => f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) =
      KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ M R P H (U i) (Z i j) :=
    funext (originalScalar_lift F ζ hζ _ R P H (Z i j))
  rw [← hl, actualRightWord_eq_wordDerivative]

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
