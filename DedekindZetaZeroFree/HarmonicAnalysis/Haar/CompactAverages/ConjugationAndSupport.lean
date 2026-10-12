module

public import Mathlib.MeasureTheory.Group.ModularCharacter

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel.CompactModular
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped NNReal Topology

private theorem continuous_modular_character
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] :
    Continuous (Measure.modularCharacter (G := G)) := by
  borelize G
  let μ : Measure G := Measure.haar
  obtain ⟨f, hf, hn, hp⟩ :
      ∃ f : C(G, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0 :=
    exists_continuous_nonneg_pos 1
  have hI : (∫ x, f x ∂μ) ≠ 0 :=
    ne_of_gt (f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hf hn hp)
  have hc : Continuous (fun g : G => ∫ x, f (x * g) ∂μ) := by
    have h := continuous_integral_apply_inv_mul (μ := μ.inv) f.continuous hf
    have he (g : G) : (∫ y, f (y⁻¹ * g) ∂μ.inv) = ∫ x, f (x * g) ∂μ := by
      change (∫ y, f (y⁻¹ * g) ∂Measure.map Inv.inv μ) = _
      have hm : AEStronglyMeasurable (fun y : G => f (y⁻¹ * g)) (Measure.map Inv.inv μ) :=
        (f.continuous.comp (continuous_inv.mul continuous_const)).aestronglyMeasurable
      simpa only [inv_inv] using integral_map (μ := μ) measurable_inv.aemeasurable hm
    simpa only [he] using h
  have he : (fun g : G => (Measure.modularCharacter g : ℝ)) =
      (fun g : G => (∫ x, f (x * g) ∂μ) / ∫ x, f x ∂μ) := by
    funext g
    change (Measure.modularCharacterFun g : ℝ) = _
    rw [Measure.modularCharacterFun_eq_haarScalarFactor μ g,
      Measure.haarScalarFactor_eq_integral_div _ _ f.continuous hf hI,
      integral_map (by fun_prop) f.continuous.aestronglyMeasurable]
  apply NNReal.isEmbedding_coe.continuous_iff.2
  change Continuous (fun g : G => (Measure.modularCharacter g : ℝ))
  rw [he]
  exact hc.div_const _

private theorem compact_character_eq_one
    {K : Type*} [TopologicalSpace K] [Group K] [CompactSpace K]
    (χ : K →* ℝ≥0) (hχ : Continuous χ) (hp : ∀ k, 0 < χ k) (k : K) : χ k = 1 := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty)
    hχ.continuousOn
  have hle (j : K) : χ j ≤ 1 := by
    have hh : χ x * χ j ≤ χ x * 1 := by
      have hm : χ (x * j) ≤ χ x := hx (Set.mem_univ (x * j))
      simpa only [map_mul, mul_one] using hm
    exact (mul_le_mul_iff_right₀ (hp x)).mp hh
  apply le_antisymm (hle k)
  have hh := mul_le_mul_left (hle k⁻¹) (χ k)
  simpa only [← map_mul, inv_mul_cancel, map_one, one_mul] using hh

theorem modular_character_compact_image
    {G K : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G]
    [TopologicalSpace K] [Group K] [CompactSpace K]
    (π : K →* G) (hπ : Continuous π) (k : K) :
    Measure.modularCharacter (π k) = 1 := by
  exact compact_character_eq_one ((Measure.modularCharacter).comp π)
    (continuous_modular_character.comp hπ) (fun j => Measure.modularCharacterFun_pos (π j)) k

theorem map_compact_conjugation
    {G K : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace K] [Group K] [CompactSpace K]
    (π : K →* G) (hπ : Continuous π)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegular] (k : K) :
    Measure.map (fun a : G => (π k)⁻¹ * a * π k) μ = μ := by
  have h : Measure.modularCharacterFun (π k) = 1 :=
    modular_character_compact_image π hπ k
  rw [show (fun a : G => (π k)⁻¹ * a * π k) =
    (fun a : G => a * π k) ∘ (fun a : G => (π k)⁻¹ * a) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), map_mul_left_eq_self,
    Measure.map_right_mul_eq_modularCharacterFun_smul, h, one_smul]

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel.CompactModular

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel.AverageBasic
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology Pointwise

variable {G K : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace K] [Group K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] [MeasurableSpace K] [BorelSpace K]

def average (π : K →* G) (ν : Measure K) (f : G → ℝ) (a : G) : ℝ :=
  ∫ k, f ((π k)⁻¹ * a * π k) ∂ν

theorem continuous_integrand (π : K →* G) (hπ : Continuous π)
    (f : G → ℝ) (hf : Continuous f) :
    Continuous (fun p : G × K => f ((π p.2)⁻¹ * p.1 * π p.2)) :=
  hf.comp (((hπ.comp continuous_snd).inv.mul continuous_fst).mul
    (hπ.comp continuous_snd))

theorem continuous_average (π : K →* G) (hπ : Continuous π)
    (ν : Measure K) [IsFiniteMeasureOnCompacts ν]
    (f : G → ℝ) (hf : Continuous f) : Continuous (average π ν f) := by
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support (k := univ) isCompact_univ
  · exact (continuous_integrand π hπ f hf).continuousOn
  · intro p x _ hx
    exact False.elim (hx (mem_univ x))

theorem average_nonneg (π : K →* G) (ν : Measure K)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (a : G) : 0 ≤ average π ν f a :=
  integral_nonneg (fun _ => hf _)

theorem tsupport_average_subset (π : K →* G) (hπ : Continuous π)
    (ν : Measure K) (f : G → ℝ) (hf : HasCompactSupport f) :
    tsupport (average π ν f) ⊆
      (fun p : K × G => π p.1 * p.2 * (π p.1)⁻¹) '' (univ ×ˢ tsupport f) := by
  have hc : IsCompact ((fun p : K × G => π p.1 * p.2 * (π p.1)⁻¹) ''
      (univ ×ˢ tsupport f)) :=
    (isCompact_univ.prod hf).image
      (((hπ.comp continuous_fst).mul continuous_snd).mul (hπ.comp continuous_fst).inv)
  apply closure_minimal _ hc.isClosed
  intro a ha
  by_contra hmem
  have hz (k : K) : f ((π k)⁻¹ * a * π k) = 0 := by
    by_contra hn
    apply hmem
    refine ⟨(k, (π k)⁻¹ * a * π k), ⟨mem_univ _, subset_tsupport f hn⟩, ?_⟩
    dsimp
    group
  exact ha (by simp only [average, hz, integral_zero])

theorem compact_support_average (π : K →* G) (hπ : Continuous π)
    (ν : Measure K) (f : G → ℝ) (hf : HasCompactSupport f) :
    HasCompactSupport (average π ν f) := by
  have hc : IsCompact ((fun p : K × G => π p.1 * p.2 * (π p.1)⁻¹) ''
      (univ ×ˢ tsupport f)) :=
    (isCompact_univ.prod hf).image
      (((hπ.comp continuous_fst).mul continuous_snd).mul (hπ.comp continuous_fst).inv)
  exact hc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_average_subset π hπ ν f hf)

theorem compact_support_integrand (π : K →* G) (hπ : Continuous π)
    (f : G → ℝ) (hf : HasCompactSupport f) :
    HasCompactSupport (fun p : G × K => f ((π p.2)⁻¹ * p.1 * π p.2)) := by
  let S := (fun p : K × G => π p.1 * p.2 * (π p.1)⁻¹) '' (univ ×ˢ tsupport f)
  have hc : IsCompact S :=
    (isCompact_univ.prod hf).image
      (((hπ.comp continuous_fst).mul continuous_snd).mul (hπ.comp continuous_fst).inv)
  apply (hc.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (hc.isClosed.prod isClosed_univ)
  intro p hp
  refine ⟨?_, mem_univ _⟩
  refine ⟨(p.2, (π p.2)⁻¹ * p.1 * π p.2), ⟨mem_univ _, subset_tsupport f hp⟩, ?_⟩
  dsimp
  group

theorem integral_average [LocallyCompactSpace G]
    (π : K →* G) (hπ : Continuous π)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegular]
    (ν : Measure K) [IsFiniteMeasureOnCompacts ν] [IsProbabilityMeasure ν]
    (f : G → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    (∫ a, average π ν f a ∂μ) = ∫ a, f a ∂μ := by
  unfold average
  have hs := integral_integral_swap_of_hasCompactSupport
    (f := fun a : G => fun k : K => f ((π k)⁻¹ * a * π k)) (μ := μ) (ν := ν)
    (continuous_integrand π hπ f hf) (compact_support_integrand π hπ f hfc)
  rw [hs]
  have he (k : K) : (∫ a, f ((π k)⁻¹ * a * π k) ∂μ) = ∫ a, f a ∂μ := by
    have hm : Measurable (fun a : G => (π k)⁻¹ * a * π k) :=
      (continuous_const.mul continuous_id |>.mul continuous_const).measurable
    have hi := integral_map (μ := μ) hm.aemeasurable hf.aestronglyMeasurable
    rw [CompactModular.map_compact_conjugation π hπ μ k] at hi
    exact hi.symm
  simp [he]

theorem uniform_conjugation_neighborhood (π : K →* G) (hπ : Continuous π)
    (O : Set G) (hO : O ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 (1 : G), ∀ k : K, ∀ a ∈ V, π k * a * (π k)⁻¹ ∈ O := by
  have hc : Continuous (fun p : G × K => π p.2 * p.1 * (π p.2)⁻¹) :=
    ((hπ.comp continuous_snd).mul continuous_fst).mul (hπ.comp continuous_snd).inv
  have hu : ∀ᶠ a in 𝓝 (1 : G), ∀ k ∈ (univ : Set K), π k * a * (π k)⁻¹ ∈ O := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro k _
    have ho : O ∈ 𝓝 (π k * (1 : G) * (π k)⁻¹) := by simpa using hO
    exact hc.continuousAt.eventually_mem ho
  refine ⟨{a | ∀ k ∈ (univ : Set K), π k * a * (π k)⁻¹ ∈ O}, hu, ?_⟩
  intro k a ha
  exact ha k (mem_univ k)

theorem average_support_shrinks (π : K →* G) (hπ : Continuous π)
    (ν : Measure K) (f : ℕ → G → ℝ) (hf : ∀ m, HasCompactSupport (f m))
    (hs : ∀ O ∈ 𝓝 (1 : G), ∀ᶠ m in atTop, tsupport (f m) ⊆ O) :
    ∀ O ∈ 𝓝 (1 : G), ∀ᶠ m in atTop, tsupport (average π ν (f m)) ⊆ O := by
  intro O hO
  obtain ⟨V, hV, hu⟩ := uniform_conjugation_neighborhood π hπ O hO
  filter_upwards [hs V hV] with m hm
  intro a ha
  obtain ⟨⟨k, x⟩, ⟨_, hx⟩, rfl⟩ := tsupport_average_subset π hπ ν (f m) (hf m) ha
  exact hu k x (hm hx)

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel.AverageBasic

end

end
