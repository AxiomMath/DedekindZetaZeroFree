module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.DifferentialWords.KFiniteVectors
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.DifferentialWords.EigenfunctionIntegrability
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.ResidualRepresentations.FiniteCompactOrbit
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.ScalarRealization
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.DifferentialWordEigenvectors

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters
open ResidualSphericalGeometry ResidualWeakEnergy
open KPGlobalResidualConstruction KPLiteralChamber
open KPMsClearedTruncationL2.NativeWordBridge
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
 abbrev sphericalEigenfunctionWordDerivative := KPSmoothActualFlowData.wordDerivative F ζ hζ

theorem spherical_native_eigen_all_derivatives
    (Z : Smooth)
    (h2 : MemLp (originalScalar F ζ hζ level R P H Z) 2 R.quotientHaar)
    (eig : ℂ) (he : ∀ g, KPMsGreenFlux.casimir F ζ hζ
      (KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ C R P H U Z) g =
      eig * KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ C R P H U Z g) :
    ∀ w, MemLp (sphericalEigenfunctionWordDerivative F ζ hζ w (originalScalar F ζ hζ level R P H Z)) 2 R.quotientHaar := by
  let f : KPMsClearedTruncationL2.smoothSpace F ζ hζ
      (ActualSectionLift.nativeLevel F ζ hζ level) :=
    ⟨originalScalar F ζ hζ level R P H Z,
      originalScalar_mem_smoothSpace F ζ hζ level R P H Z⟩
  let up := fun g => f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)
  have hs : RawWordKFinite.NativeSmooth up := by
    intro a
    have hh := ActualSectionLift.lift_arch_smooth F ζ hζ level R P H Z a
    convert hh using 1
    funext x
    exact originalScalar_lift F ζ hζ level R P H Z _
  have hcompact (k : KPMsGreenFlux.K F) (g) :
      up (g * KPMsGreenFlux.compactInsertion F ζ hζ k) = up g :=
    originalScalar_compact F ζ hζ level R P H Z g k
  have hn : ∀ g, KPMsGreenFlux.casimir F ζ hζ up g = eig * up g := he
  let A := H.atlas level
  let Y := Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * A.threshold)
  have hd : (2 * (KPCuspLogShape.dimension F : ℝ)) ≠ 0 := by
    have hp : (0 : ℝ) < KPCuspLogShape.dimension F := by
      exact_mod_cast KPCuspLogShape.dimension_pos F H.totallyComplex
    positivity
  have hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y := by
    refine ⟨Real.exp_pos _, ?_⟩
    change A.threshold ≤ Real.log (Real.exp _) / (2 * (KPCuspLogShape.dimension F : ℝ))
    rw [Real.log_exp, mul_div_cancel_left₀ _ hd]
  apply eigen_all_word_memLp A R P (H.disintegration level) Y hY f eig
    (original_word_eigen f.val hs eig hn)
    h2
  intro w
  apply original_compact_orbit_finite
  let W := w.map (wordIndexEquiv F).symm
  have hw : W.map (wordIndexEquiv F) = w := by simp [W]
  have hk := RawWordKFinite.actualRightWord_kFinite up hs hcompact W
  have hweq : KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ W up =
      fun g => sphericalEigenfunctionWordDerivative F ζ hζ w f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
    funext g
    rw [actualRightWord_eq_wordDerivative, hw]
  rw [hweq] at hk
  exact hk

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
