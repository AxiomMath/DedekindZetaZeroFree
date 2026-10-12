module

public import DedekindZetaZeroFree.Eisenstein.Residues.Pairings.ResidueBoundary

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
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
open _root_.DedekindZetaZeroFree renaming canonicalRealization → canonicalRealization
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming cutoff → cutoff
open _root_.DedekindZetaZeroFree.KPContActualSphericalFlatStage renaming stageConclusions → stageConclusions
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming lift_eq → lift_eq
open ResidualHilbertCenters
def SphericalBoundaryProperty
    (v : KPContActualSphericalFlatStage.Stage F R.A.zeta12 R.A.primitive_zeta12 U)
    (z : KPContActualAllCuspSource.Sector F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U) : Prop :=
  ∀ (K : Subgroup (KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12))
    (hK : IsCompact (K : Set (KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12)))
    (ν : Measure K) [IsFiniteMeasure ν]
    (x : RestrictedTensorSimple.Core (Plus R.A P C)
      (plusReference R.A P C) (bad R.A P C)),
  ∀ (u : SmoothSections F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U)
    (uH : KPContActualAllCuspSource.Sector F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U)
    (huH : ((uH.val : KPContSectorClosedLpSubspace.CoveredL2 F R.A.zeta12 R.A.primitive_zeta12 Haar V) :
      Covered F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U → ℂ)
      =ᵐ[KPContActualAllCuspSource.measure F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U]
        scalar F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U u)
    (heigen : (uH, KPContinuation.spectralCoordinate (d:ℤ) 0 • uH) ∈
      (KPContActualSectorFriedrichsSynthesis.Δ_U F R.A.zeta12 R.A.primitive_zeta12
        V Haar Transport H Haar.adelicHaar Haar.adelic_isHaar rfl canonicalRealization).graph)
    (hpin : KPContActualCommonDiskRightHolomorphy.lift F R.A.zeta12 R.A.primitive_zeta12
      (atlasLevel F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U) Haar Transport H u.val =
      ResidualRawAverage.average F R.A.zeta12 R.A.primitive_zeta12 K ν (coreResidue R P C x)),
    inner ℂ uH z =
    ((((H.disintegration V).beta Set.univ).toReal : ℂ) *
      ∫ω : Ω,
        (zeroProjection F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U ω.1
          (sheetEvaluation F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U ω.1 (LinearMap.toSpanSingleton ℂ _ v) 0 (1:ℂ))).val 0 *
        star (upperConstantTerm F R.A.zeta12 R.A.primitive_zeta12
          (KPWildKernelUpperBound.quotientHaar F)
          (ResidualRawAverage.average F R.A.zeta12 R.A.primitive_zeta12 K ν (coreResidue R P C x))
          (finiteRepresentative F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U ω.1 1).val) ∂KPMsFixedHaarDisintegration.probability A (H.disintegration V).beta)

local notation "level" => V
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U
local notation "G" => KPContSectorCoveredQuotientVocabulary.ActualCover F R.A.zeta12 R.A.primitive_zeta12
theorem spherical_scalar_hilbert_boundary_centers
    (v : KPContActualSphericalFlatStage.Stage F R.A.zeta12 R.A.primitive_zeta12 U) (hv : v ≠ 0) :
    ∃ Z : ℂ → Smooth,
      (∀ s, (1 : ℝ) / 3 < s.re → ∀ g : G,
        groupScalar F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U (Z s) g =
          ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F R.A.zeta12 R.A.primitive_zeta12 s v.val).val
              (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out c) * g)) ∧
      ∀ c ∈ KPContinuation.spectralDomain,
        ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
          ∃ N : ℂ → Smooth,
            SmoothTaylorData F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U (Metric.ball c r) N ∧
            (∀ s ∈ Metric.ball c r, s ≠ c →
              groupScalar F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U (N s) =
                (s - c) • groupScalar F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U (Z s)) ∧
            (∃ z : KPContActualAllCuspSource.Sector F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U,
              KPContActualSmoothLineGluing.Represents F R.A.zeta12 R.A.primitive_zeta12 level Haar Transport H (N c).val z ∧
              (z, KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) c • z) ∈
                (sourceLaplacian F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U).graph ∧
              (c = 0 → SphericalBoundaryProperty R P C D Haar Transport H U v z)) ∧
            (KPGlobalResidualConstruction.IncomingFiberOrthogonality.AllCuspMeanZero
              F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U (N c) → N c = 0) := by
  let ι : ℂ →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F R.A.zeta12 R.A.primitive_zeta12 U :=
    LinearMap.toSpanSingleton ℂ _ v
  have hι : Function.Injective ι := by
    intro a b hab
    exact (smul_left_injective ℂ (m := v) hv) hab
  let realization : KPContActualFixedSectorRealization.LevelRealization
      F R.A.zeta12 R.A.primitive_zeta12 level Haar Transport H := canonicalRealization
  let T : ℝ := (H.atlas level).threshold + 1
  have hT : (H.atlas level).threshold < T := by dsimp [T]; linarith
  let χ : KPContActualAllCuspSource.Cusps F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U →
      KPCutoffSource.SmoothCuspCutoff T := fun _ => cutoff T
  have hf : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) KPContinuation.spectralDomain :=
    differentiableOn_const _
  obtain ⟨buffer, source, domain, W, hW, ⟨formula⟩⟩ :=
    kp_cont_actual_chamber_formula_equality F R.A.zeta12 R.A.primitive_zeta12 D Haar.adelicHaar Haar.adelic_isHaar Haar rfl
      Transport H U realization ι hι (fun _ => 1) hf T hT χ
  let Z : ℂ → Smooth := E F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U KPContinuation.spectralDomain
    (KPContActualHilbertSimpleGerms.Sigma F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U
      Haar.adelicHaar Haar.adelic_isHaar rfl realization KPContinuation.spectralDomain)
    source.descent.cutoff W
  refine ⟨Z, ?_, ?_⟩
  · intro s hs g
    rw [formula.group_equal s hs g]
    unfold KPContActualChamberNormalSeries.E
    congr 1
    funext q
    unfold KPContActualChamberNormalSeries.term KPContActualSphericalFlatStage.L
      KPContFlatCommonLevelKernel.L
    simp [ι, lift_eq]
  · have hStage := stageConclusions F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U ι hι
    have hHilb := kp_cont_actual_hilbert_simple_germs F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U
      Haar.adelicHaar Haar.adelic_isHaar rfl realization ι hι hStage
      KPContinuation.spectralDomain KPContinuation.spectralDomain_isOpen Set.Subset.rfl
      (fun _ => 1) hf buffer χ source
    intro c hc
    obtain ⟨r, hr, hb, hi, w, hw, he, _⟩ := hHilb.simple_germs c hc
    obtain ⟨N⟩ := hW.continuation.every_germ c hc r hr hb hi w hw he
    refine ⟨r, hr, hb, numerator F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U source.descent.cutoff c N.W,
      N.numerator_data, N.punctured_group, ?_, ?_⟩
    · refine ⟨w c, ?_, ?_, ?_⟩
      · simpa only [numerator_at_center] using N.represents c (Metric.mem_ball_self hr)
      · let Δ := sourceLaplacian F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U
        let a := KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ)
        let v := KPContActualHilbertSimpleGerms.v F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U
          Haar.adelicHaar Haar.adelic_isHaar rfl realization ι buffer
          KPContinuation.spectralDomain (fun _ => 1) χ source
        have hD := (kp_cont_actual_sector_friedrichs_synthesis F R.A.zeta12 R.A.primitive_zeta12
          Haar.adelicHaar Haar.adelic_isHaar level Haar rfl Transport H realization).laplacian_closed
        have hh : ContinuousAt source.h c :=
          source.hilbert_holomorphic.continuousOn.continuousAt
            (KPContinuation.spectralDomain_isOpen.mem_nhds hc)
        have hwc : ContinuousAt w c :=
          hw.continuousOn.continuousAt (Metric.ball_mem_nhds c hr)
        have ha : ContinuousAt a c :=
          (KPContinuation.spectralCoordinate_hasDerivAt ((Module.finrank ℚ F / 2 : ℕ) : ℤ) c).continuousAt
        apply closed_cleared_center_eigen Δ hD a v source.h w c ha hh hwc
        · filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds c hr), self_mem_nhdsWithin]
            with s hs hne
          have hn : s ∉ KPContActualHilbertSimpleGerms.Sigma F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U
              Haar.adelicHaar Haar.adelic_isHaar rfl realization KPContinuation.spectralDomain := by
            intro hp
            exact hne (hi ⟨hs, hp⟩)
          exact hHilb.domain_equation s ⟨hb hs, hn⟩
        · filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds c hr), self_mem_nhdsWithin]
            with s hs hne
          exact he s hs hne
      · intro hc0
        subst c
        intro K hK ν inst x u uH huH heigen hpin
        exact actual_retained_residue_boundary R P C D Haar Transport H U K hK ν ι x
          buffer (fun _ => 1) hf hι χ source realization r hr hb w hw
          (by simpa only [sub_zero] using he) u uH huH heigen hpin
    · intro hmean
      have hmean' : KPGlobalResidualConstruction.IncomingFiberOrthogonality.AllCuspMeanZero
          F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U (N.W c) := by
        simpa only [numerator_at_center] using hmean
      have hz := KPGlobalResidualConstruction.CommonSphericalDisk.CuspidalCancellation.smooth_center_eq_zero
        F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U realization ι hι (fun _ => 1) hf buffer χ source
        W c hc r hr hb hi w hw he N hmean'
      simpa only [numerator_at_center] using hz

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
