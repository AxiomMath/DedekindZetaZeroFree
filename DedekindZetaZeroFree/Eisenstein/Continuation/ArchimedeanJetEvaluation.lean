module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarGerms.Coefficients
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJetNormBounds

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology ContDiff BigOperators
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource.ArchSeries
open KPGlobalResidualConstruction
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.AnalyticScalarMultiplication renaming compactJet_series → compactJet_series
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.AnalyticScalarMultiplication renaming compactJet → compactJet
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeWordAction renaming chart_base → chart_base
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def point : Observation F :=
  (⟨archBase F, ActualDifferentialData.archBase_mem_domain F⟩,fun _ => 0)

theorem jets_point (f : space F ζ hζ) (g : KPLiteralRaw.G F ζ hζ) :
    jets F ζ hζ (g,0) f (point F) = f.val g := by
  simp [jets, point, iteratedFDeriv_zero_apply, chart_base F ζ hζ]

theorem powerSeries_eval {a : ℕ → space F ζ hζ} {f : ℂ → space F ζ hζ}
    {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : KPGlobalEisensteinData.SmoothPowerSeriesOn (jets F ζ hζ) c ρ a f)
    (g : KPLiteralRaw.G F ζ hζ) :
    HasFPowerSeriesOnBall (fun s => (f s).val g)
      (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) ((a n).val g)) c
      (ENNReal.ofReal ρ) := by
  let i : KPGlobalEisensteinData.DifferentialCompact (Observation F) (Index F ζ hζ) :=
    ⟨{point F},isCompact_singleton,(g,0)⟩
  letI : CompactSpace i.compact := isCompact_iff_compactSpace.mp i.isCompact
  let p : i.compact := ⟨point F,Set.mem_singleton _⟩
  let L : C(i.compact,ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ p
  have ht := L.comp_hasFPowerSeriesOnBall (compactJet_series (jets F ζ hζ) i hρ hf)
  have he (v : space F ζ hζ) : L (compactJet (jets F ζ hζ) i v) = v.val g :=
    jets_point F ζ hζ v g
  convert ht using 1
  · funext s; exact (he (f s)).symm
  · funext n
    ext v
    simp [ContinuousLinearMap.compFormalMultilinearSeries, he,
      ContinuousMultilinearMap.mkPiRing_apply]

end DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource.ArchSeries

end
