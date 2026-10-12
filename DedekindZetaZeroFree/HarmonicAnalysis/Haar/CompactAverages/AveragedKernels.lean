module

public import Mathlib

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel
open MeasureTheory Set Filter Topology

private theorem conjugation_saturation_compact
    {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace K] [CompactSpace K] (π : K → G) (hπ : Continuous π)
    {f : G → ℝ} (hf : HasCompactSupport f) :
    IsCompact ((fun p : K × G => π p.1 * p.2 * (π p.1)⁻¹) ''
      (univ ×ˢ tsupport f)) :=
  (isCompact_univ.prod hf).image (by fun_prop)

theorem averaged_support_subset
    {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
    (π : K → G) (hπ : Continuous π) (μ : Measure K)
    {f : G → ℝ} (hf : HasCompactSupport f) :
    tsupport (fun a : G => ∫ k, f ((π k)⁻¹ * a * π k) ∂μ) ⊆
      (fun p : K × G => π p.1 * p.2 * (π p.1)⁻¹) '' (univ ×ˢ tsupport f) := by
  apply closure_minimal
  · intro a ha
    by_contra h
    apply ha
    apply integral_eq_zero_of_ae
    filter_upwards with k
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    exact h ⟨(k, (π k)⁻¹ * a * π k), ⟨mem_univ _, ht⟩, by simp [mul_assoc]⟩
  · exact (conjugation_saturation_compact π hπ hf).isClosed

theorem averaged_hasCompactSupport
    {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
    (π : K → G) (hπ : Continuous π) (μ : Measure K)
    {f : G → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun a : G => ∫ k, f ((π k)⁻¹ * a * π k) ∂μ) :=
  (conjugation_saturation_compact π hπ hf).of_isClosed_subset isClosed_closure
    (averaged_support_subset π hπ μ hf)

theorem averaged_continuous
    {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (π : K → G) (hπ : Continuous π) (μ : Measure K) [IsFiniteMeasure μ]
    {f : G → ℝ} (hf : Continuous f) :
    Continuous (fun a : G => ∫ k, f ((π k)⁻¹ * a * π k) ∂μ) := by
  rw [← continuousOn_univ]
  exact continuousOn_integral_of_compact_support isCompact_univ
    (by exact (hf.comp (((hπ.comp continuous_snd).inv.mul continuous_fst).mul
      (hπ.comp continuous_snd))).continuousOn)
    (by simp)

theorem conjugation_saturation_shrinks
    {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace K] [CompactSpace K]
    (π : K → G) (hπ : Continuous π) {O : Set G} (hO : O ∈ 𝓝 (1 : G)) :
    ∃ U ∈ 𝓝 (1 : G), ∀ k a, a ∈ U → π k * a * (π k)⁻¹ ∈ O := by
  have hc : Continuous (fun p : G × K => π p.2 * p.1 * (π p.2)⁻¹) := by fun_prop
  have he : ∀ᶠ a in 𝓝 (1 : G), ∀ k ∈ (univ : Set K), π k * a * (π k)⁻¹ ∈ O :=
    isCompact_univ.eventually_forall_of_forall_eventually (by
      intro k _
      have ht := (hc.continuousAt (x := (1, k))).preimage_mem_nhds
        (show O ∈ 𝓝 (π k * 1 * (π k)⁻¹) by simpa using hO)
      exact ht)
  refine ⟨_, he, ?_⟩
  intro k a ha
  exact ha k (mem_univ k)

theorem averaged_integrable_parameter
    {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (π : K → G) (hπ : Continuous π) (μ : Measure K) [IsFiniteMeasure μ]
    {f : G → ℝ} (hf : Continuous f) (a : G) :
    Integrable (fun k => f ((π k)⁻¹ * a * π k)) μ := by
  apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
  exact HasCompactSupport.of_compactSpace _

theorem averaged_conjugation_invariant
    {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [MeasurableSpace K] [BorelSpace K]
    (π : K →* G) (μ : Measure K) [μ.IsMulLeftInvariant]
    (f : G → ℝ) (k : K) (a : G) :
    (∫ u, f ((π u)⁻¹ * ((π k)⁻¹ * a * π k) * π u) ∂μ) =
      ∫ u, f ((π u)⁻¹ * a * π u) ∂μ := by
  have he (u : K) : (π u)⁻¹ * ((π k)⁻¹ * a * π k) * π u =
      (π (k * u))⁻¹ * a * π (k * u) := by simp [mul_assoc]
  simp_rw [he]
  exact integral_mul_left_eq_self (μ := μ)
    (fun u => f ((π u)⁻¹ * a * π u)) k

theorem averaged_mass
    {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (π : K → G) (hπ : Continuous π)
    (μG : Measure G) [μG.IsHaarMeasure]
    (μK : Measure K) [IsProbabilityMeasure μK]
    (hmap : ∀ k, Measure.map (fun a => (π k)⁻¹ * a * π k) μG = μG)
    {f : G → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) :
    (∫ a, (∫ k, f ((π k)⁻¹ * a * π k) ∂μK) ∂μG) = ∫ a, f a ∂μG := by
  let S : Set G := (fun p : K × G => π p.1 * p.2 * (π p.1)⁻¹) ''
    (univ ×ˢ tsupport f)
  have hS : IsCompact S := conjugation_saturation_compact π hπ hs
  have hc : Continuous (fun p : G × K => f ((π p.2)⁻¹ * p.1 * π p.2)) := by fun_prop
  have hsup : HasCompactSupport (fun p : G × K => f ((π p.2)⁻¹ * p.1 * π p.2)) := by
    apply (hS.prod isCompact_univ).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (hS.prod isCompact_univ).isClosed
    intro p hp
    refine ⟨?_, mem_univ _⟩
    exact ⟨(p.2, (π p.2)⁻¹ * p.1 * π p.2),
      ⟨mem_univ _, subset_tsupport _ hp⟩, by simp [mul_assoc]⟩
  have hi := hc.integrable_of_hasCompactSupport (μ := μG.prod μK) hsup
  rw [integral_integral_swap hi]
  have he (k : K) : (∫ a, f ((π k)⁻¹ * a * π k) ∂μG) = ∫ a, f a ∂μG := by
    rw [← integral_map (by fun_prop : AEMeasurable (fun a : G => (π k)⁻¹ * a * π k) μG)
      hf.aestronglyMeasurable, hmap k]
  simp_rw [he]
  simp

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel

end
