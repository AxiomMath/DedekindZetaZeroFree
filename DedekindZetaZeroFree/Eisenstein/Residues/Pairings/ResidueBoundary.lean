module

public import DedekindZetaZeroFree.Eisenstein.Residues.Pairings.RegularizedCenterSource
public import DedekindZetaZeroFree.Eisenstein.Residues.Pairings.SourceBoundary

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPContFlatCuspIncomingEvaluation KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (D : KPGlobalTorusInducingPlan.ModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (Haar : KPSmoothLocalQuotientCharts.HaarRecipe F R.A.zeta12 R.A.primitive_zeta12)
variable (Transport : KPMsFixedHaarDisintegration.SphericalTransport F R.A.zeta12 R.A.primitive_zeta12)
variable (H : KPMsFixedHaarDisintegration.AllLevels F R.A.zeta12 R.A.primitive_zeta12 Haar Transport)
variable (U : KPMsRationalCompactCrossPairing.Level F R.A.zeta12 R.A.primitive_zeta12)
local instance (K : Subgroup (KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12)) :
    MeasurableSpace K := borel K
local instance (K : Subgroup (KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12)) :
    BorelSpace K := ⟨rfl⟩

local notation "V" => KPContActualAllCuspSource.level F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U
local notation "A" => H.atlas V
local notation "Ω" => KPMsFixedHaarDisintegration.Omega A
local notation "d" => (Module.finrank ℚ F / 2 : ℕ)

open KPGlobalResidualConstruction.SourceCuspidalOrthogonality
open KPContSectorCoveredQuotientVocabulary KPContSectorFixedPushforwardSupport
open KPContActualCutoffSmoothDescent
theorem actual_retained_residue_boundary
    (K : Subgroup (KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12))
    (hK : IsCompact (K : Set (KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12)))
    (ν : Measure K) [IsFiniteMeasure ν]
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] [FiniteDimensional ℂ Q]
    (ι : Q →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F R.A.zeta12 R.A.primitive_zeta12 U)

    (x : RestrictedTensorSimple.Core (Plus R.A P C)
      (plusReference R.A P C) (bad R.A P C))
    {T : ℝ} (B : KPContActualCollarBuffer.CollarBuffer F R.A.zeta12 R.A.primitive_zeta12
      V Haar Transport H T)
    (f : ℂ → Q) (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (hι : Function.Injective ι)
    (χ : KPContFlatCuspIncomingEvaluation.Cusps F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U →
      KPCutoffSource.SmoothCuspCutoff T)
    (source : KPContActualAllCuspSource.Source F R.A.zeta12 R.A.primitive_zeta12
      D Haar Transport H U ι B KPContinuation.spectralDomain f χ)
    (realization : KPContActualFixedSectorRealization.LevelRealization F R.A.zeta12
      R.A.primitive_zeta12 V Haar Transport H)
    (r : ℝ) (hr : 0 < r) (hb : Metric.ball (0:ℂ) r ⊆ KPContinuation.spectralDomain)
    (w : ℂ → KPContActualAllCuspSource.Sector F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U)
    (hw : DifferentiableOn ℂ w (Metric.ball 0 r))
    (he : ∀s ∈ Metric.ball 0 r, s ≠ 0 → w s = s •
      KPContActualHilbertSimpleGerms.v F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U
        Haar.adelicHaar Haar.adelic_isHaar rfl realization ι B
        KPContinuation.spectralDomain f χ source s)
    (u : SmoothSections F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U)
    (uH : KPContActualAllCuspSource.Sector F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U)
    (huH : ((uH.val : KPContSectorClosedLpSubspace.CoveredL2 F R.A.zeta12 R.A.primitive_zeta12 Haar V) :
      Covered F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U → ℂ)
      =ᵐ[KPContActualAllCuspSource.measure F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U]
        scalar F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U u)
    (heigen : (uH, KPContinuation.spectralCoordinate (d:ℤ) 0 • uH) ∈
      (KPContActualSectorFriedrichsSynthesis.Δ_U F R.A.zeta12 R.A.primitive_zeta12
        V Haar Transport H Haar.adelicHaar Haar.adelic_isHaar rfl realization).graph)
    (hpin : KPContActualCommonDiskRightHolomorphy.lift F R.A.zeta12 R.A.primitive_zeta12
      (atlasLevel F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U) Haar Transport H u.val =
      ResidualRawAverage.average F R.A.zeta12 R.A.primitive_zeta12 K ν (coreResidue R P C x)) :
    inner ℂ uH (w 0) =
    ((((H.disintegration V).beta Set.univ).toReal : ℂ) *
      ∫ω : Ω,
        (zeroProjection F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U ω.1
          (sheetEvaluation F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U ω.1 ι 0 (f 0))).val 0 *
        star (upperConstantTerm F R.A.zeta12 R.A.primitive_zeta12
          (KPWildKernelUpperBound.quotientHaar F)
          (ResidualRawAverage.average F R.A.zeta12 R.A.primitive_zeta12 K ν (coreResidue R P C x))
          (finiteRepresentative F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U ω.1 1).val) ∂KPMsFixedHaarDisintegration.probability A (H.disintegration V).beta) := by
  have h0 : (0:ℂ) ∈ KPContinuation.spectralDomain := by norm_num [KPContinuation.spectralDomain]
  have hs := actual_source_pairing_boundary R P C D Haar Transport H U K hK ν ι x
    B KPContinuation.spectralDomain f h0 χ source u uH huH hpin
  have hrp := ResidualHilbertCenters.actual_cleared_center_source_eigentest_pairing
    F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U
    realization ι hι f hf B χ source r hr hb w hw he uH heigen
  have hd : 0 < d := by
    rw [← (KPArch.complex_places_of_primitive_twelfth_root F R.A.zeta12 R.A.primitive_zeta12).2.1]
    exact (KPArch.complex_places_of_primitive_twelfth_root F R.A.zeta12 R.A.primitive_zeta12).2.2
  have hd' : (0:ℤ) < (d:ℤ) := by exact_mod_cast hd
  obtain ⟨hder,hne⟩ := KPContinuation.spectralCoordinate_deriv_zero (d:ℤ) hd'
  rw [hder] at hrp
  simp only [Int.cast_natCast] at hrp
  have hn : (-(4:ℂ)*(d:ℂ)/3) ≠ 0 := by
    rw [hder] at hne
    simpa only [Int.cast_natCast] using hne
  exact mul_left_cancel₀ hn (hrp.symm.trans hs)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
