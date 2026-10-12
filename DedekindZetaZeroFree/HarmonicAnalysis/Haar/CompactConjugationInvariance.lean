module

public import Mathlib.MeasureTheory.Group.ModularCharacter

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel.CompactHaar
open MeasureTheory Set Filter Topology
open scoped NNReal

private theorem continuous_translated_integral
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (f : G → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous (fun g => ∫ x, f (x * g) ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro g
  obtain ⟨s, hsc, hsn⟩ := exists_compact_mem_nhds g
  let t : Set G := (fun p : G × G => p.1 * p.2⁻¹) '' (tsupport f ×ˢ s)
  have htc : IsCompact t := (hfc.prod hsc).image (by fun_prop)
  have hc : ContinuousOn (fun p : G × G => f (p.2 * p.1)) (s ×ˢ univ) :=
    (hf.comp (by fun_prop)).continuousOn
  have hz : ∀ p x, p ∈ s → x ∉ t → f (x * p) = 0 := by
    intro p x hp hx
    by_contra hh
    apply hx
    refine ⟨(x * p, p), ⟨subset_tsupport _ hh, hp⟩, ?_⟩
    simp
  exact (continuousOn_integral_of_compact_support htc hc hz).continuousAt hsn

theorem continuous_modularCharacter
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] :
    Continuous (Measure.modularCharacter (G := G)) := by
  borelize G
  let μ : Measure G := Measure.haar
  obtain ⟨⟨f, hf⟩, hfc, hfn, hf1⟩ :
      ∃ f : C(G, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0 :=
    exists_continuous_nonneg_pos 1
  have hi : (∫ x, f x ∂μ) ≠ 0 := ne_of_gt
    (hf.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hfn hf1)
  have he (g : G) : (Measure.modularCharacter g : ℝ) =
      (∫ x, f (x * g) ∂μ) / ∫ x, f x ∂μ := by
    change (Measure.modularCharacterFun g : ℝ) = _
    rw [Measure.modularCharacterFun_eq_haarScalarFactor μ g,
      Measure.haarScalarFactor_eq_integral_div _ _ hf hfc hi,
      integral_map (continuous_mul_const g).aemeasurable hf.aestronglyMeasurable]
  apply NNReal.isEmbedding_coe.continuous_iff.mpr
  have heq : (fun g : G => (Measure.modularCharacter g : ℝ)) =
      (fun g => (∫ x, f (x * g) ∂μ) / ∫ x, f x ∂μ) := funext he
  change Continuous (fun g : G => (Measure.modularCharacter g : ℝ))
  rw [heq]
  exact (continuous_translated_integral μ f hf hfc).div_const _

theorem compact_character_eq_one
    {K : Type*} [Group K] [TopologicalSpace K] [CompactSpace K]
    (χ : K →* ℝ≥0) (hχ : Continuous χ) (k : K) : χ k = 1 := by
  have hb : BddAbove (Set.range χ) :=
    (isCompact_range hχ).bddAbove
  obtain ⟨M, hM⟩ := hb
  have hle (a : K) : χ a ≤ 1 := by
    by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (lt_of_not_ge h)
    have hp : χ a ^ n ≤ M := by
      rw [← map_pow]
      exact hM (Set.mem_range_self _)
    exact (not_lt_of_ge hp) hn
  have hp : χ k * χ k⁻¹ = 1 := by rw [← map_mul]; simp
  have hlow : 1 ≤ χ k := by
    calc
      1 = χ k * χ k⁻¹ := hp.symm
      _ ≤ χ k * 1 := by gcongr; exact hle k⁻¹
      _ = χ k := mul_one _
  exact le_antisymm (hle k) hlow

theorem map_mul_right_compact
    {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [Group K] [TopologicalSpace K] [CompactSpace K]
    (π : K →* G) (hπ : Continuous π)
    (μ : Measure G) [μ.IsHaarMeasure] [Measure.InnerRegular μ] (k : K) :
    Measure.map (fun a : G => a * π k) μ = μ := by
  have he := compact_character_eq_one ((Measure.modularCharacter (G := G)).comp π)
    (continuous_modularCharacter.comp hπ) k
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul]
  change Measure.modularCharacter (π k) • μ = μ
  rw [show Measure.modularCharacter (π k) = 1 from he, one_smul]

theorem map_conjugation_compact
    {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [Group K] [TopologicalSpace K] [CompactSpace K]
    (π : K →* G) (hπ : Continuous π)
    (μ : Measure G) [μ.IsHaarMeasure] [Measure.InnerRegular μ] (k : K) :
    Measure.map (fun a : G => (π k)⁻¹ * a * π k) μ = μ := by
  have hc : (fun a : G => (π k)⁻¹ * a * π k) =
      (fun a : G => a * π k) ∘ (fun a : G => (π k)⁻¹ * a) := rfl
  rw [hc, ← Measure.map_map (continuous_mul_const _).measurable
    (continuous_const_mul _).measurable, map_mul_left_eq_self,
    map_mul_right_compact π hπ μ k]

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel.CompactHaar

namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel
open MeasureTheory Set

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel

end
