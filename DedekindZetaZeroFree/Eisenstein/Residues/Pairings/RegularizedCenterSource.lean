module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.EigentestPairing
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
theorem actual_cleared_center_source_eigentest_pairing
    (r : ℝ) (hr : 0 < r) (_hb : Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain)
    (w : ℂ → KPContActualAllCuspSource.Sector F ζ hζ C R P H U)
    (hw : DifferentiableOn ℂ w (Metric.ball 0 r))
    (he : ∀ s ∈ Metric.ball 0 r, s ≠ 0 → w s = s •
      KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U
        R.adelicHaar R.adelic_isHaar rfl realization ι buffer
        KPContinuation.spectralDomain f χ source s)
    (t : KPContActualAllCuspSource.Sector F ζ hζ C R P H U)
    (ht : (t, KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) 0 • t) ∈
      (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ level R P H
        R.adelicHaar R.adelic_isHaar rfl realization).graph) :
    inner ℂ t (source.h 0) =
      deriv (KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ)) 0 *
        inner ℂ t (w 0) := by
  obtain ⟨r',hr',hb',w',hw',he',hp⟩ :=
    KPContActualHilbertSimpleGerms.actual_simple_germs_zero_eigentest_pairing
      F ζ hζ C R P H U R.adelicHaar R.adelic_isHaar rfl realization
      ι buffer KPContinuation.spectralDomain f χ source hι
      (stageConclusions F ζ hζ C R P H U ι hι)
      KPContinuation.spectralDomain_isOpen (fun _ hs => hs) hf
      (by norm_num [KPContinuation.spectralDomain])
  have heq : w 0 = w' 0 := cleared_center_unique
    (KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U
      R.adelicHaar R.adelic_isHaar rfl realization ι buffer
      KPContinuation.spectralDomain f χ source)
    w w' 0 r r' hr hr' hw hw' (by simpa only [sub_zero] using he)
      (by simpa only [sub_zero] using he')
  rw [heq]
  exact hp t ht

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
