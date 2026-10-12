module

public import DedekindZetaZeroFree.Analysis.Sobolev.Mollification.WeakDerivativeCommutation
public import DedekindZetaZeroFree.Analysis.Sobolev.Mollification.L2Convergence

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPCompactInteriorH1

open MeasureTheory TopologicalSpace Filter
open scoped ContDiff Topology

theorem exists_nonequivariant_h1_sequence {n r : ℕ}
    (hn : 0 < n) (hr : 0 < r) {Ω O : Opens (E n)}
    {K : Set (E n)} {f : E n → V r} {g : Fin n → E n → V r}
    (hK : IsCompact K) (hKO : K ⊆ (O : Set (E n)))
    (hOΩ : (O : Set (E n)) ⊆ (Ω : Set (E n)))
    (hfg : WeakFirst Ω f g)
    (hf : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (Ω : Set (E n)) \ K → f x = 0) :
    let F := compactZeroExtension K f
    let G := fun j => compactZeroExtension K (g j)
    ∃ u : ℕ → E n → V r,
      (∀ m, ContDiff ℝ ∞ (u m)) ∧
      (∀ m, HasCompactSupport (u m)) ∧
      (∀ m, tsupport (u m) ⊆ (O : Set (E n))) ∧
      MemLp F 2 volume ∧
      (∀ j, MemLp (G j) 2 volume) ∧
      (∀ m, MemLp (u m) 2 volume) ∧
      (∀ m j, MemLp (fun x => fderiv ℝ (u m) x (coordinateDirection j)) 2 volume) ∧
      ∃ (herror : ∀ m, MemLp (fun x => u m x - F x) 2 volume)
        (hderror : ∀ m j, MemLp
          (fun x => fderiv ℝ (u m) x (coordinateDirection j) - G j x) 2 volume),
        Tendsto (fun m => l2Norm volume (fun x => u m x - F x) (herror m))
          atTop (𝓝 0) ∧
        ∀ j, Tendsto
          (fun m => l2Norm volume
            (fun x => fderiv ℝ (u m) x (coordinateDirection j) - G j x)
            (hderror m j)) atTop (𝓝 0) := by
  have hKΩ : K ⊆ (Ω : Set (E n)) := hKO.trans hOΩ
  obtain ⟨hF, hG, _hFint, _hGint, hFzero, hGzero, _hFtsup, _hGtsup, _hFae, _hGae⟩ :=
    compactZeroExtension_properties hK hKΩ hfg hf
  obtain ⟨δ, hδpos, hδO⟩ := hK.exists_cthickening_subset_open O.2 hKO
  let φ : ℕ → ContDiffBump (0 : E n) := fun m =>
    KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.shrinkingBump δ hδpos m
  have hφrOut : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0) := by
    simpa only [φ] using
      KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.shrinkingBump_rOut_tendsto
        (n := n) δ hδpos
  have hφle : ∀ m, (φ m).rOut ≤ δ := fun m => by
    simpa only [φ] using
      KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.shrinkingBump_rOut_le
        (n := n) δ hδpos m
  have hweak : ∀ (j : Fin n) (ψ : E n → ℂ), ContDiff ℝ ∞ ψ → ∀ a : Fin r,
      (∫ x, (compactZeroExtension K f x) a * coordinatePartial j ψ x ∂volume) =
        -(∫ x, (compactZeroExtension K (g j) x) a * ψ x ∂volume) :=
    fun j ψ hψ a => (compactZeroExtension_weak_identity hK hKΩ hfg hf ψ hψ j a).2.2
  have hmoll : ∀ m, ContDiff ℝ ∞ (mollifyVector (φ m) (compactZeroExtension K f)) ∧
      HasCompactSupport (mollifyVector (φ m) (compactZeroExtension K f)) ∧
      tsupport (mollifyVector (φ m) (compactZeroExtension K f)) ⊆
        Metric.cthickening (φ m).rOut K ∧
      (∀ (x : E n) (j : Fin n),
        fderiv ℝ (mollifyVector (φ m) (compactZeroExtension K f)) x (coordinateDirection j) =
          mollifyVector (φ m) (compactZeroExtension K (g j)) x) := by
    intro m
    have h := allTests_weak_derivative_mollification hn hr K hK
      (compactZeroExtension K f) (fun j => compactZeroExtension K (g j))
      hF hG hFzero hGzero hweak (φ m)
    simpa only [mollifyVector] using h
  refine ⟨fun m => mollifyVector (φ m) (compactZeroExtension K f),
    fun m => (hmoll m).1, fun m => (hmoll m).2.1, ?_, hF, hG,
    fun m => mollification_memLp hn hr K hK (compactZeroExtension K f) hF hFzero (φ m),
    ?_, ?_⟩
  · intro m
    exact ((hmoll m).2.2.1).trans ((Metric.cthickening_mono (hφle m) K).trans hδO)
  · intro m j
    have hbase := mollification_memLp hn hr K hK
      (compactZeroExtension K (g j)) (hG j) (hGzero j) (φ m)
    refine MemLp.ae_eq ?_ hbase
    filter_upwards with x
    exact ((hmoll m).2.2.2 x j).symm
  · refine ⟨fun m =>
        (mollification_memLp hn hr K hK (compactZeroExtension K f) hF hFzero (φ m)).sub hF,
      fun m j => ?_, ?_, ?_⟩
    · have hbase := (mollification_memLp hn hr K hK
        (compactZeroExtension K (g j)) (hG j) (hGzero j) (φ m)).sub (hG j)
      refine MemLp.ae_eq ?_ hbase
      filter_upwards with x
      simp only [Pi.sub_apply]
      rw [(hmoll m).2.2.2 x j]
    · simpa only [l2Norm, Pi.sub_apply] using
        mollification_l2_tendsto hn hr K hK (compactZeroExtension K f) hF hFzero φ hφrOut
    · intro j
      have hbase := mollification_l2_tendsto hn hr K hK
        (compactZeroExtension K (g j)) (hG j) (hGzero j) φ hφrOut
      refine Tendsto.congr (fun m => ?_) hbase
      simp only [l2Norm, Pi.sub_apply]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      rw [(hmoll m).2.2.2 x j]

end DedekindZetaZeroFree.KPCompactInteriorH1

end
