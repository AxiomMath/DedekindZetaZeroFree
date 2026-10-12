module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteCenterSums.WordPairing
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteCenterSums.QuotientRealization

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
 abbrev pairingKernelWordDerivative := KPSmoothActualFlowData.wordDerivative F ζ hζ

theorem finiteCenterSum_eq_zero_of_pairings
    (z : ∀ i, Fin (m i) → KPContActualAllCuspSource.Sector F ζ hζ M R P H (U i))
    (hz : ∀ i j, KPContActualSmoothLineGluing.Represents F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ M R P H (U i)) R P H (Z i j).val (z i j))
    (eig : ℂ)
    (he : ∀ i j g, KPMsGreenFlux.casimir F ζ hζ
      (KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ M R P H (U i) (Z i j)) g =
      eig * KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ M R P H (U i) (Z i j) g)
    (horth : ∀ i j, (∫ x,
      star (originalScalar F ζ hζ (KPContActualAllCuspSource.level F ζ hζ M R P H (U i)) R P H (Z i j) x) *
      pairingKernelWordDerivative F ζ hζ ((w i j).map (wordIndexEquiv F)).reverse
        (finiteCenterSum F ζ hζ M R P H U m w a Z) x ∂ R.quotientHaar) = 0) :
    finiteCenterSum F ζ hζ M R P H U m w a Z = 0 := by
  let total : smoothAllWordL2 R := ⟨finiteCenterSum F ζ hζ M R P H U m w a Z,
    finiteCenterSum_mem F ζ hζ M R P H U m w a Z z hz eig he⟩
  let fs : (Σ i, Fin (m i)) → smoothAllWordL2 R := fun ij =>
    ⟨originalScalar F ζ hζ (KPContActualAllCuspSource.level F ζ hζ M R P H (U ij.1)) R P H (Z ij.1 ij.2), by
      let ff : KPMsClearedTruncationL2.smoothSpace F ζ hζ
          (ActualSectionLift.nativeLevel F ζ hζ (KPContActualAllCuspSource.level F ζ hζ M R P H (U ij.1))) :=
        ⟨originalScalar F ζ hζ _ R P H (Z ij.1 ij.2),
          originalScalar_mem_smoothSpace F ζ hζ _ R P H (Z ij.1 ij.2)⟩
      exact word_mem_smoothAllWordL2 R ff
        (represented_native_eigencenter_all_derivatives F ζ hζ M R P H (U ij.1)
          (Z ij.1 ij.2) (z ij.1 ij.2) (hz ij.1 ij.2) eig (he ij.1 ij.2)) []⟩
  exact finite_word_sum_zero_of_adjoint_pairings R Finset.univ
    (fun ij => a ij.1 ij.2) fs total
    (fun ij => (w ij.1 ij.2).map (wordIndexEquiv F))
    (by
      intro x
      simp only [total, fs, finiteCenterSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Fintype.sum_sigma])
    (fun ij hij => horth ij.1 ij.2)

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
