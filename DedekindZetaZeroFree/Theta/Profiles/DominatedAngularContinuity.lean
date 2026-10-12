module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree

open MeasureTheory

theorem thetaDominatedAngularContinuity
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {ι : Type*} [Countable ι]
    (ν : Measure H) (D S : Set H)
    (hD : MeasurableSet D) (hνD : ν D < ⊤)
    (hS : IsCompact S) (hDS : D ⊆ S)
    (F : ℝ → H → ι → ℂ)
    (hF : ∀ i : ι, ContinuousOn (fun th : ℝ × H => F th.1 th.2 i)
      ((Set.Ioi 0) ×ˢ S))
    (hmajorant : ∀ a b : ℝ, 0 < a → a ≤ b →
      ∃ u : ι → ℝ, Summable u ∧ (∀ i : ι, 0 ≤ u i) ∧
        ∀ t ∈ Set.Icc a b, ∀ h ∈ S, ∀ i : ι, ‖F t h i‖ ≤ u i) :
    (∀ t : ℝ, 0 < t → ∀ h ∈ S, Summable (F t h)) ∧
    (∀ t : ℝ, 0 < t → IntegrableOn (fun h : H => ∑' i : ι, F t h i) D ν) ∧
    ContinuousOn (fun t : ℝ => ∫ h in D, ∑' i : ι, F t h i ∂ν) (Set.Ioi 0) ∧
    LocallyIntegrableOn (fun t : ℝ => ∫ h in D, ∑' i : ι, F t h i ∂ν)
      (Set.Ioi 0) volume := by
  classical

  have hIcc : ∀ a b : ℝ, 0 < a → a ≤ b →
      ContinuousOn (fun t : ℝ => ∫ h in D, ∑' i : ι, F t h i ∂ν) (Set.Icc a b) := by
    intro a b ha hab
    obtain ⟨u, hu_sum, -, hu_bound⟩ := hmajorant a b ha hab

    have hcontS : ∀ t ∈ Set.Icc a b,
        ContinuousOn (fun h : H => ∑' i : ι, F t h i) S := by
      intro t ht
      refine continuousOn_tsum (u := u) (fun i => ?_) hu_sum
        (fun i h hh => hu_bound t ht h hh i)
      exact (hF i).comp ((continuous_const.prodMk continuous_id).continuousOn)
        (fun h hh => ⟨lt_of_lt_of_le ha ht.1, hh⟩)
    have hmeas : ∀ t ∈ Set.Icc a b,
        AEStronglyMeasurable (fun h : H => ∑' i : ι, F t h i) (ν.restrict D) :=
      fun t ht => (hcontS t ht).aestronglyMeasurable_of_subset_isCompact hS hD hDS
    have hbound : ∀ t ∈ Set.Icc a b,
        ∀ᵐ h ∂(ν.restrict D), ‖∑' i : ι, F t h i‖ ≤ ∑' i : ι, u i := by
      intro t ht
      filter_upwards [ae_restrict_mem hD] with h hh
      have hS' : h ∈ S := hDS hh
      have hn : Summable (fun i : ι => ‖F t h i‖) :=
        Summable.of_norm_bounded hu_sum (fun i => by simpa using hu_bound t ht h hS' i)
      calc ‖∑' i : ι, F t h i‖ ≤ ∑' i : ι, ‖F t h i‖ := norm_tsum_le_tsum_norm hn
        _ ≤ ∑' i : ι, u i :=
            Summable.tsum_le_tsum (fun i => hu_bound t ht h hS' i) hn hu_sum
    have hbound_int : Integrable (fun _ : H => ∑' i : ι, u i) (ν.restrict D) := by
      haveI : IsFiniteMeasure (ν.restrict D) := ⟨by simpa using hνD⟩
      exact integrable_const _
    have hcont_ae : ∀ᵐ h ∂(ν.restrict D),
        ContinuousOn (fun t : ℝ => ∑' i : ι, F t h i) (Set.Icc a b) := by
      filter_upwards [ae_restrict_mem hD] with h hh
      have hS' : h ∈ S := hDS hh
      refine continuousOn_tsum (u := u) (fun i => ?_) hu_sum
        (fun i t ht => hu_bound t ht h hS' i)
      exact (hF i).comp ((continuous_id.prodMk continuous_const).continuousOn)
        (fun t ht => ⟨lt_of_lt_of_le ha ht.1, hS'⟩)
    exact continuousOn_of_dominated hmeas hbound hbound_int hcont_ae
  have hcontIoi : ContinuousOn (fun t : ℝ => ∫ h in D, ∑' i : ι, F t h i ∂ν)
      (Set.Ioi 0) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have ha : (0 : ℝ) < t / 2 := by linarith
    have hab : t / 2 ≤ 2 * t := by linarith
    have hca : ContinuousAt (fun t : ℝ => ∫ h in D, ∑' i : ι, F t h i ∂ν) t :=
      (hIcc (t / 2) (2 * t) ha hab).continuousAt
        (Icc_mem_nhds (show t / 2 < t by linarith) (show t < 2 * t by linarith))
    exact hca.continuousWithinAt
  refine ⟨?_, ?_, hcontIoi, hcontIoi.locallyIntegrableOn measurableSet_Ioi⟩
  · intro t ht h hh
    obtain ⟨u, hu_sum, -, hu_bound⟩ := hmajorant t t ht le_rfl
    exact Summable.of_norm_bounded hu_sum (fun i => hu_bound t ⟨le_rfl, le_rfl⟩ h hh i)
  · intro t ht
    obtain ⟨u, hu_sum, -, hu_bound⟩ := hmajorant t t ht le_rfl
    have hcont : ContinuousOn (fun h : H => ∑' i : ι, F t h i) S := by
      refine continuousOn_tsum (u := u) (fun i => ?_) hu_sum
        (fun i h hh => hu_bound t ⟨le_rfl, le_rfl⟩ h hh i)
      exact (hF i).comp ((continuous_const.prodMk continuous_id).continuousOn)
        (fun h hh => ⟨ht, hh⟩)
    exact hcont.integrableOn_of_subset_isCompact hS hD hDS hνD.ne

end DedekindZetaZeroFree
