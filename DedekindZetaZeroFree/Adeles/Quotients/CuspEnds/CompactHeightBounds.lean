module

public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Topology
noncomputable section
namespace DedekindZetaZeroFree.KPRadialTail

theorem compact_embedding_height_bounds
    {Y B : Type*} [TopologicalSpace Y] [TopologicalSpace B]
    (T : ℝ) (e : Y × Set.Ioi T → B) (he : Topology.IsEmbedding e)
    (K : Set B) (hK : IsCompact K) (hKr : K ⊆ Set.range e) :
    ∃ a b : ℝ, T < a ∧
      ∀ z, e z ∈ K → a ≤ z.2.val ∧ z.2.val ≤ b := by
  have himage : e '' (e ⁻¹' K) = K := Set.image_preimage_eq_of_subset hKr
  have hc : IsCompact (e ⁻¹' K) := he.isCompact_iff.mpr (by rw [himage]; exact hK)
  have hcont : Continuous (fun z : Y × Set.Ioi T => z.2.val) :=
    continuous_subtype_val.comp continuous_snd
  by_cases hn : (e ⁻¹' K).Nonempty
  · obtain ⟨zmin, hzmin, hmin⟩ := hc.exists_isMinOn hn hcont.continuousOn
    obtain ⟨zmax, hzmax, hmax⟩ := hc.exists_isMaxOn hn hcont.continuousOn
    refine ⟨zmin.2.val, zmax.2.val, zmin.2.property, ?_⟩
    intro z hz
    exact ⟨hmin hz, hmax hz⟩
  · refine ⟨T + 1, T + 1, by linarith, ?_⟩
    intro z hz
    exact (hn ⟨z, hz⟩).elim

end DedekindZetaZeroFree.KPRadialTail

end
