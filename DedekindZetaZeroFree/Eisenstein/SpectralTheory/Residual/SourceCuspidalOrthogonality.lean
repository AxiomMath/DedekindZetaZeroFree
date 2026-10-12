module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Eigenfunctions.GraphProjection
public import DedekindZetaZeroFree.Eisenstein.Residues.CuspidalCenterVanishing

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters
open _root_.DedekindZetaZeroFree.KPContActualSphericalFlatStage renaming stageConclusions → stageConclusions
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CommonSphericalDisk.CuspidalCancellation renaming cleared_center_unique → cleared_center_unique
open _root_.DedekindZetaZeroFree.KPBelowThresholdResolvent renaming eigen_nonneg → eigen_nonneg
open KPGlobalResidualConstruction
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (hι : Function.Injective ι) (f : ℂ → S)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable {T : ℝ}
variable (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
  KPContinuation.spectralDomain f χ)

include realization hι hf buffer in
theorem actual_cleared_center_orthogonal_cusp_eigentest
    (c : ℂ) (hc : c ∈ KPContinuation.spectralDomain)
    (r : ℝ) (hr : 0 < r) (hb : Metric.ball c r ⊆ KPContinuation.spectralDomain)
    (w : ℂ → KPContActualAllCuspSource.Sector F ζ hζ C R P H U)
    (hw : DifferentiableOn ℂ w (Metric.ball c r))
    (he : ∀ s ∈ Metric.ball c r, s ≠ c → w s = (s-c) •
      KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U
        R.adelicHaar R.adelic_isHaar rfl realization ι buffer
        KPContinuation.spectralDomain f χ source s)
    (test : KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U)
    (t : KPContActualAllCuspSource.Sector F ζ hζ C R P H U)
    (hrep : KPContActualSmoothLineGluing.Represents F ζ hζ level R P H test.val t)
    (hmean : IncomingFiberOrthogonality.AllCuspMeanZero F ζ hζ C R P H U test)
    (ht : (t, KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) c • t) ∈
      (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ level R P H
        R.adelicHaar R.adelic_isHaar rfl realization).graph) :
    inner ℂ t (w c) = 0 := by
  let v := KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U
    R.adelicHaar R.adelic_isHaar rfl realization ι buffer
    KPContinuation.spectralDomain f χ source
  let B := KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ level R P H
    R.adelicHaar R.adelic_isHaar rfl realization
  let Δ := KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ level R P H
    R.adelicHaar R.adelic_isHaar rfl realization
  have hs := kp_cont_actual_sector_friedrichs_synthesis F ζ hζ
    R.adelicHaar R.adelic_isHaar level R rfl P H realization
  have hg := kp_cont_actual_hilbert_simple_germs F ζ hζ C R P H U
    R.adelicHaar R.adelic_isHaar rfl realization ι hι
    (stageConclusions F ζ hζ C R P H U ι hι)
    KPContinuation.spectralDomain KPContinuation.spectralDomain_isOpen
    (fun _ hs => hs) f hf buffer χ source
  obtain ⟨r',hr',hb',hi',w',hw',he',hcenter',houtside'⟩ := hg.simple_germs c hc
  have heq : w c = w' c := cleared_center_unique v w w' c r r' hr hr' hw hw' he he'
  have hae : (t.val : KPContActualAllCuspSource.Covered F ζ hζ C R P H U → ℂ)
      =ᵐ[KPContActualAllCuspSource.measure F ζ hζ C R P H U]
      KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U test := by
    obtain ⟨hm, hrep⟩ := hrep
    have he : (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H test.val).val =
        KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U test := by
      rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
      rfl
    rw [← he, ← hrep]
    exact hm.coeFn_toLp
  have hpair : inner ℂ t (source.h c) = 0 :=
    SourceCuspidalOrthogonality.source_inner_eq_zero F ζ hζ C R P H U
      ι buffer KPContinuation.spectralDomain f χ source test t hae hmean c hc
  rw [heq]
  by_cases hp : c ∈ KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U
      R.adelicHaar R.adelic_isHaar rfl realization KPContinuation.spectralDomain
  · obtain ⟨μ,hμ,heigen,hcoord⟩ := hp.2
    have hnonneg : 0 ≤ μ := eigen_nonneg Δ hs.laplacian_nonnegative μ heigen
    have htest : (t, (μ : ℂ) • t) ∈ Δ.graph := by simpa only [hcoord] using ht
    exact projected_source_orthogonal_eigentest Δ B hs.genuine_inverse μ hnonneg
      t (source.h c) (w' c) _ htest (hcenter' hp μ hcoord) hpair
  · rw [houtside' hp, inner_zero_right]

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
