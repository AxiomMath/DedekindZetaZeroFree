module

public import DedekindZetaZeroFree.Eisenstein.Residues.Spherical.LaplacianEigenCenters
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.SourceCuspidalOrthogonality

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff
open MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming cutoff → cutoff
open _root_.DedekindZetaZeroFree renaming canonicalRealization → canonicalRealization
open _root_.DedekindZetaZeroFree.KPContActualSphericalFlatStage renaming stageConclusions → stageConclusions
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming lift_eq → lift_eq
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
local notation "G" => KPContSectorCoveredQuotientVocabulary.ActualCover F ζ hζ

def CuspEigentestOrthogonal (c : ℂ)
    (z : KPContActualAllCuspSource.Sector F ζ hζ C R P H U) : Prop :=
  ∀ (test : Smooth) (t : KPContActualAllCuspSource.Sector F ζ hζ C R P H U),
    KPContActualSmoothLineGluing.Represents F ζ hζ level R P H test.val t →
    KPGlobalResidualConstruction.IncomingFiberOrthogonality.AllCuspMeanZero
      F ζ hζ C R P H U test →
    (t, KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) c • t) ∈
      (sourceLaplacian F ζ hζ C R P H U).graph → inner ℂ t z = 0

theorem spherical_scalar_hilbert_orthogonal_centers
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U) (hv : v ≠ 0) :
    ∃ Z : ℂ → Smooth,
      (∀ s, (1 : ℝ) / 3 < s.re → ∀ g : G,
        groupScalar F ζ hζ C R P H U (Z s) g =
          ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
              (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out c) * g)) ∧
      ∀ c ∈ KPContinuation.spectralDomain,
        ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
          ∃ N : ℂ → Smooth,
            SmoothTaylorData F ζ hζ C R P H U (Metric.ball c r) N ∧
            (∀ s ∈ Metric.ball c r, s ≠ c →
              groupScalar F ζ hζ C R P H U (N s) =
                (s - c) • groupScalar F ζ hζ C R P H U (Z s)) ∧
            (∃ z : KPContActualAllCuspSource.Sector F ζ hζ C R P H U,
              KPContActualSmoothLineGluing.Represents F ζ hζ level R P H (N c).val z ∧
              (z, KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) c • z) ∈
                (sourceLaplacian F ζ hζ C R P H U).graph ∧
              CuspEigentestOrthogonal F ζ hζ C R P H U c z) ∧
            (KPGlobalResidualConstruction.IncomingFiberOrthogonality.AllCuspMeanZero
              F ζ hζ C R P H U (N c) → N c = 0) := by
  let ι : ℂ →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U :=
    LinearMap.toSpanSingleton ℂ _ v
  have hι : Function.Injective ι := by
    intro a b hab
    exact (smul_left_injective ℂ (m := v) hv) hab
  let realization : KPContActualFixedSectorRealization.LevelRealization
      F ζ hζ level R P H := canonicalRealization
  let T : ℝ := (H.atlas level).threshold + 1
  have hT : (H.atlas level).threshold < T := by dsimp [T]; linarith
  let χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U →
      KPCutoffSource.SmoothCuspCutoff T := fun _ => cutoff T
  have hf : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) KPContinuation.spectralDomain :=
    differentiableOn_const _
  obtain ⟨buffer, source, domain, W, hW, ⟨formula⟩⟩ :=
    kp_cont_actual_chamber_formula_equality F ζ hζ C R.adelicHaar R.adelic_isHaar R rfl
      P H U realization ι hι (fun _ => 1) hf T hT χ
  let Z : ℂ → Smooth := E F ζ hζ C R P H U KPContinuation.spectralDomain
    (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U
      R.adelicHaar R.adelic_isHaar rfl realization KPContinuation.spectralDomain)
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
  · have hStage := stageConclusions F ζ hζ C R P H U ι hι
    have hHilb := kp_cont_actual_hilbert_simple_germs F ζ hζ C R P H U
      R.adelicHaar R.adelic_isHaar rfl realization ι hι hStage
      KPContinuation.spectralDomain KPContinuation.spectralDomain_isOpen Set.Subset.rfl
      (fun _ => 1) hf buffer χ source
    intro c hc
    obtain ⟨r, hr, hb, hi, w, hw, he, _⟩ := hHilb.simple_germs c hc
    obtain ⟨N⟩ := hW.continuation.every_germ c hc r hr hb hi w hw he
    refine ⟨r, hr, hb, numerator F ζ hζ C R P H U source.descent.cutoff c N.W,
      N.numerator_data, N.punctured_group, ?_, ?_⟩
    · refine ⟨w c, ?_, ?_, ?_⟩
      · simpa only [numerator_at_center] using N.represents c (Metric.mem_ball_self hr)
      · let Δ := sourceLaplacian F ζ hζ C R P H U
        let a := KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ)
        let v := KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U
          R.adelicHaar R.adelic_isHaar rfl realization ι buffer
          KPContinuation.spectralDomain (fun _ => 1) χ source
        have hD := (kp_cont_actual_sector_friedrichs_synthesis F ζ hζ
          R.adelicHaar R.adelic_isHaar level R rfl P H realization).laplacian_closed
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
          have hn : s ∉ KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U
              R.adelicHaar R.adelic_isHaar rfl realization KPContinuation.spectralDomain := by
            intro hp
            exact hne (hi ⟨hs, hp⟩)
          exact hHilb.domain_equation s ⟨hb hs, hn⟩
        · filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds c hr), self_mem_nhdsWithin]
            with s hs hne
          exact he s hs hne
      · intro test t hrep hmean ht
        exact actual_cleared_center_orthogonal_cusp_eigentest F ζ hζ C R P H U
          realization ι hι (fun _ => 1) hf buffer χ source c hc r hr hb
          w hw he test t hrep hmean ht
    · intro hmean
      have hmean' : KPGlobalResidualConstruction.IncomingFiberOrthogonality.AllCuspMeanZero
          F ζ hζ C R P H U (N.W c) := by
        simpa only [numerator_at_center] using hmean
      have hz := KPGlobalResidualConstruction.CommonSphericalDisk.CuspidalCancellation.smooth_center_eq_zero
        F ζ hζ C R P H U realization ι hι (fun _ => 1) hf buffer χ source
        W c hc r hr hb hi w hw he N hmean'
      simpa only [numerator_at_center] using hz

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
