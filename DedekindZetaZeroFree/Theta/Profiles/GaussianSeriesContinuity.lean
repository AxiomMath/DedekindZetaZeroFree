module

public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.ShiftedGaussianSummability
public import DedekindZetaZeroFree.Theta.Profiles.ParityShapeBounds
public import DedekindZetaZeroFree.Theta.Profiles.RayThetaKernelsAndZeroModes

@[expose] public section

noncomputable section
open Classical

namespace DedekindZetaZeroFree.Hecke.AnalyticTailHelper

theorem continuous_tsum_of_compact_gaussian_bound
    {ι E H : Type*} [NormedAddCommGroup E]
    [TopologicalSpace H] [LocallyCompactSpace H]
    (y : ι → E)
    (hs : ∀ a : ℝ, 0 < a → Summable (fun i => Real.exp (-a * ‖y i‖ ^ 2)))
    (c : ι → ℂ) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C)
    (k : H → E → ℂ)
    (hcont : ∀ i, Continuous (fun h => k h (y i)))
    (hk : ∀ S : Set H, IsCompact S → ∃ P a : ℝ, 0 ≤ P ∧ 0 < a ∧
      ∀ h ∈ S, ∀ i, ‖k h (y i)‖ ≤ P * Real.exp (-a * ‖y i‖ ^ 2)) :
    Continuous (fun h => ∑' i, c i * k h (y i)) := by
  apply continuous_iff_continuousAt.mpr
  intro h
  obtain ⟨S, hS, hSh⟩ := exists_compact_mem_nhds h
  obtain ⟨P, a, hP, ha, hb⟩ := hk S hS
  have hs' := (hs a ha).mul_left (C * P)
  have hbound : ∀ i, ∀ h ∈ S,
      ‖c i * k h (y i)‖ ≤ (C * P) * Real.exp (-a * ‖y i‖ ^ 2) := by
    intro i h hh
    rw [norm_mul]
    calc
      ‖c i‖ * ‖k h (y i)‖ ≤ C * (P * Real.exp (-a * ‖y i‖ ^ 2)) :=
        mul_le_mul (hc i) (hb h hh i) (norm_nonneg _) hC
      _ = (C * P) * Real.exp (-a * ‖y i‖ ^ 2) := by ring
  exact (continuousOn_tsum (fun i => ((continuous_const).mul (hcont i)).continuousOn)
    hs' hbound).continuousAt hSh

set_option maxHeartbeats 800000 in

theorem continuous_tsum_thetaParityShape
    (K : Type) [Field K] [NumberField K] {ι : Type*}
    (δ : Finset (DedekindZetaZeroFree.AbelianQuotient.RayCoset.RealPlaces K))
    (u : ℝ) (hu : 0 < u)
    (y : ι → NumberField.mixedEmbedding.euclidean.mixedSpace K)
    (hs : ∀ a : ℝ, 0 < a → Summable (fun i => Real.exp (-a * ‖y i‖ ^ 2)))
    (c : ι → ℂ) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) :
    Continuous (fun h : DedekindZetaZeroFree.AbelianQuotient.RayCoset.logHyperplane K =>
      ∑' i, c i * DedekindZetaZeroFree.AbelianQuotient.RayParity.gδ K δ
        (DedekindZetaZeroFree.AbelianQuotient.RayParity.Q K
          (DedekindZetaZeroFree.AbelianQuotient.RayTheta.q K u h) (y i))) := by
  apply continuous_tsum_of_compact_gaussian_bound y hs c hC hc
    (fun (h : DedekindZetaZeroFree.AbelianQuotient.RayCoset.logHyperplane K) z =>
      DedekindZetaZeroFree.AbelianQuotient.RayParity.gδ K δ
        (DedekindZetaZeroFree.AbelianQuotient.RayParity.Q K
          (DedekindZetaZeroFree.AbelianQuotient.RayTheta.q K u h) z))
  · intro i
    have he := DedekindZetaZeroFree.continuousOn_thetaParityShape K δ
    have hm : Continuous (fun h : DedekindZetaZeroFree.AbelianQuotient.RayCoset.logHyperplane K =>
        (u, (h, y i))) := continuous_const.prodMk (continuous_id.prodMk continuous_const)
    unfold DedekindZetaZeroFree.AbelianQuotient.RayTheta.q
    simpa only [Function.comp_def, one_div] using he.comp_continuous hm (fun h => hu)
  · intro S hS
    obtain ⟨P, a, hP, ha, hb⟩ := DedekindZetaZeroFree.thetaParityShapeBounds K δ S hS
    refine ⟨P, a * u ^ (2 / (Module.finrank ℚ K : ℝ)), hP.le,
      mul_pos ha (Real.rpow_pos_of_pos hu _), ?_⟩
    intro h hh i
    unfold DedekindZetaZeroFree.AbelianQuotient.RayTheta.q
    simpa only [one_div, neg_mul, mul_assoc] using (hb u hu h hh (y i)).1

end DedekindZetaZeroFree.Hecke.AnalyticTailHelper

end
