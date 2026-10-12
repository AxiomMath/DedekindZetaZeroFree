module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residues.CuspHeight
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.AngularRadialCancellation
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspPairings.ExactDisintegration
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residual.IncomingCoefficientVanishing

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
theorem actual_source_pairing_boundary
    (K : Subgroup (KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12))
    (hK : IsCompact (K : Set (KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12)))
    (ν : Measure K) [IsFiniteMeasure ν]
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] [FiniteDimensional ℂ Q]
    (ι : Q →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F R.A.zeta12 R.A.primitive_zeta12 U)

    (x : RestrictedTensorSimple.Core (Plus R.A P C)
      (plusReference R.A P C) (bad R.A P C))
    {T : ℝ} (B : KPContActualCollarBuffer.CollarBuffer F R.A.zeta12 R.A.primitive_zeta12
      V Haar Transport H T)
    (O : Set ℂ) (f : ℂ → Q) (h0 : (0:ℂ) ∈ O)
    (χ : KPContFlatCuspIncomingEvaluation.Cusps F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U →
      KPCutoffSource.SmoothCuspCutoff T)
    (source : KPContActualAllCuspSource.Source F R.A.zeta12 R.A.primitive_zeta12
      D Haar Transport H U ι B O f χ)
    (u : SmoothSections F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U)
    (uH : KPContActualAllCuspSource.Sector F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U)
    (huH : ((uH.val : KPContSectorClosedLpSubspace.CoveredL2 F R.A.zeta12 R.A.primitive_zeta12 Haar V) :
      Covered F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U → ℂ)
      =ᵐ[KPContActualAllCuspSource.measure F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U]
        scalar F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U u)
    (hpin : KPContActualCommonDiskRightHolomorphy.lift F R.A.zeta12 R.A.primitive_zeta12
      (atlasLevel F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U) Haar Transport H u.val =
      ResidualRawAverage.average F R.A.zeta12 R.A.primitive_zeta12 K ν (coreResidue R P C x)) :
    inner ℂ uH (source.h 0) =
    (-(4:ℂ)*d/3) * ((((H.disintegration V).beta Set.univ).toReal : ℂ) *
      ∫ω : Ω,
        (zeroProjection F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U ω.1
          (sheetEvaluation F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U ω.1 ι 0 (f 0))).val 0 *
        star (upperConstantTerm F R.A.zeta12 R.A.primitive_zeta12
          (KPWildKernelUpperBound.quotientHaar F)
          (ResidualRawAverage.average F R.A.zeta12 R.A.primitive_zeta12 K ν (coreResidue R P C x))
          (finiteRepresentative F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U ω.1 1).val) ∂KPMsFixedHaarDisintegration.probability A (H.disintegration V).beta) := by
  let c : KPContFlatCuspIncomingEvaluation.Cusps F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U → ℂ := fun j =>
    (zeroProjection F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U j
      (sheetEvaluation F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U j ι 0 (f 0))).val 0 *
    star (upperConstantTerm F R.A.zeta12 R.A.primitive_zeta12
      (KPWildKernelUpperBound.quotientHaar F)
      (ResidualRawAverage.average F R.A.zeta12 R.A.primitive_zeta12 K ν (coreResidue R P C x))
      (finiteRepresentative F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U j 1).val)
  obtain ⟨Y,hY,a,hYe,ha,he,hi⟩ := Bridge.source_pairing_cusp_disintegration_exact
    F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U ι B O f χ source u uH huH 0 h0
  rw [hi]
  have hdim : KPCuspLogShape.dimension F = d :=
    (KPArch.complex_places_of_primitive_twelfth_root F R.A.zeta12 R.A.primitive_zeta12).2.1
  have hd : 0 < d := by
    rw [← hdim]
    exact KPCuspCharts.positive_dimension F H.totallyComplex
  have hrad (r : Set.Ioi Y) :
    (∫ω : Ω, ∫z, a ((H.disintegration V).chart Y hY (z,r))
      ∂(H.disintegration V).unipotent ω
      ∂KPMsFixedHaarDisintegration.probability A (H.disintegration V).beta) =
    ∫ω : Ω, c ω.1 * ((r.val:ℂ) *
      KPCutoffSource.incomingCommutatorMultiplier d (χ ω.1).toFun 0 (Real.log r.val/(2*d)))
      ∂KPMsFixedHaarDisintegration.probability A (H.disintegration V).beta := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rcases ω with ⟨j,b⟩
    induction b using Quotient.inductionOn with | h b =>
      have ht : B.τ < KPMsFixedHaarDisintegration.logHeight (F:=F) r.val := by
        have hh := Real.log_lt_log (Real.exp_pos _) (show Real.exp (2*(d:ℝ)*B.τ) < r.val by
          simpa only [hYe,hdim,Set.mem_Ioi] using r.property)
        rw [Real.log_exp] at hh
        dsimp [KPMsFixedHaarDisintegration.logHeight]
        rw [hdim]
        apply (lt_div_iff₀ (by positivity)).mpr
        nlinarith
      rw [Bridge.kernel_pairing_eq_upper F R.A.zeta12 R.A.primitive_zeta12
        D Haar Transport H U ι B O f χ source u 0 h0 a ha he Y hY r ht j b, hpin]
      simp only [incoming_zero_scalar,
        coreResidue_average_upper_cusp_height R P C D Haar Transport H U K hK ν]
      have hprod := KPCutoffSource.incoming_outgoing_radial_density d hd r.val
        (lt_trans hY.1 r.property)
      simp only [KPMsFixedHaarDisintegration.logHeight,hdim,star_mul]
      dsimp only [c]
      linear_combination
        (KPCutoffSource.incomingCommutatorMultiplier d (χ j).toFun 0 (Real.log r.val/(2*d)) *
          (zeroProjection F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U j
            (sheetEvaluation F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U j ι 0 (f 0))).val 0 *
          star (upperConstantTerm F R.A.zeta12 R.A.primitive_zeta12
            (KPWildKernelUpperBound.quotientHaar F)
            (ResidualRawAverage.average F R.A.zeta12 R.A.primitive_zeta12 K ν (coreResidue R P C x))
            (finiteRepresentative F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U j 1).val)) * hprod
  simp_rw [hrad]
  unfold KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Transport.cuspRadial
  have hs := integral_subtype_comap
    (μ := KPMsFixedHaarDisintegration.radialMeasure) (s := Set.Ioi Y)
    measurableSet_Ioi (fun r : ℝ => ∫ω : Ω, c ω.1 *
      ((r:ℂ)*KPCutoffSource.incomingCommutatorMultiplier d (χ ω.1).toFun 0
        (Real.log r/(2*d)))
      ∂KPMsFixedHaarDisintegration.probability A (H.disintegration V).beta)
  rw [hs]
  have hYe2 : Y = Real.exp (2*(d:ℝ)*B.τ) := by simpa only [hdim] using hYe
  rw [hYe2]
  exact KPMsFixedHaarDisintegration.actual_angular_radial_cancellation F R.A.zeta12
    R.A.primitive_zeta12 Haar Transport H V χ B.τ B.below_cutoff c

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
