/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

module

public import DedekindZetaZeroFree.RepresentationTheory.Compact.Convolution

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RepresentationTheory/Compact/ApproximateIdentity.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: retain only the generic compact-group density slice; adapt imports and visibility.
The selected declarations are adapted to the current module interface.
License: repository root LICENSE (Apache-2.0).
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ComplexOrder Topology

namespace DedekindZetaZeroFree.TauCeti

section CompactGroup

variable {𝕜 E G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

noncomputable def leftTranslateCM (f : C(G, E)) : C(G, C(G, E)) :=
  ContinuousMap.curry
    (f.comp ⟨fun p : G × G => p.1⁻¹ * p.2, continuous_fst.inv.mul continuous_snd⟩)

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem leftTranslateCM_apply (f : C(G, E)) (z x : G) :
    leftTranslateCM f z x = f (z⁻¹ * x) :=
  (rfl)

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem leftTranslateCM_one (f : C(G, E)) : leftTranslateCM f 1 = f := by
  ext x
  rw [leftTranslateCM_apply, inv_one, one_mul]

omit [MeasurableSpace G] [BorelSpace G] in

theorem exists_mem_nhds_one_norm_sub_le (f : C(G, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (1 : G), ∀ z ∈ V, ∀ x : G, ‖f (z⁻¹ * x) - f x‖ ≤ ε := by
  have htendsto : Tendsto (leftTranslateCM (E := E) (G := G) f) (𝓝 1) (𝓝 f) := by
    simpa only [leftTranslateCM_one] using (leftTranslateCM f).continuous.tendsto 1
  refine ⟨leftTranslateCM f ⁻¹' Metric.closedBall f ε,
    htendsto (Metric.closedBall_mem_nhds f hε), fun z hz x => ?_⟩
  have hz' : ‖leftTranslateCM f z - f‖ ≤ ε := by
    simpa only [mem_preimage, Metric.mem_closedBall, dist_eq_norm] using hz
  calc ‖f (z⁻¹ * x) - f x‖
      = ‖(leftTranslateCM f z - f) x‖ := by rw [ContinuousMap.sub_apply, leftTranslateCM_apply]
    _ ≤ ‖leftTranslateCM f z - f‖ := (leftTranslateCM f z - f).norm_coe_le_norm x
    _ ≤ ε := hz'

structure IsMollifier (U : Set G) (k : C(G, 𝕜)) : Prop where

  nonneg : ∀ g, 0 ≤ k g

  inv_apply : ∀ g, k g⁻¹ = k g

  integral_eq_one : ∫ g, k g ∂(haarProb G) = 1

  eq_zero_of_notMem : ∀ g ∉ U, k g = 0

namespace IsMollifier

variable {U U' : Set G} {k : C(G, 𝕜)}

theorem mono (h : IsMollifier U k) (hUU' : U ⊆ U') : IsMollifier U' k :=
  { h with eq_zero_of_notMem := fun g hg => h.eq_zero_of_notMem g fun hg' => hg (hUU' hg') }

theorem apply_eq_norm (h : IsMollifier U k) (g : G) : k g = (‖k g‖ : 𝕜) :=
  (RCLike.norm_of_nonneg' (h.nonneg g)).symm

theorem inv_apply_eq_conj (h : IsMollifier U k) (g : G) : k g⁻¹ = (starRingEnd 𝕜) (k g) := by
  rw [h.inv_apply]
  exact (RCLike.conj_eq_iff_im.2 (RCLike.nonneg_iff.1 (h.nonneg g)).2).symm

theorem integral_norm_eq_one (h : IsMollifier U k) : ∫ g, ‖k g‖ ∂(haarProb G) = 1 := by
  have hcast : ((∫ g, ‖k g‖ ∂(haarProb G) : ℝ) : 𝕜) = 1 := by
    rw [← integral_ofReal, ← h.integral_eq_one]
    exact integral_congr_ae (Eventually.of_forall fun g => (h.apply_eq_norm g).symm)
  exact_mod_cast hcast

end IsMollifier

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in

private theorem exists_symmetric_bump [LocallyCompactSpace G] {W : Set G} (hWopen : IsOpen W)
    (hW1 : (1 : G) ∈ W) (hWsymm : ∀ g ∈ W, g⁻¹ ∈ W) :
    ∃ ψ : C(G, ℝ), (∀ g, 0 ≤ ψ g) ∧ (∀ g, ψ g⁻¹ = ψ g) ∧ (∀ g ∉ W, ψ g = 0) ∧ 0 < ψ 1 := by
  obtain ⟨φ, hφ1, hφ0, -, hφIcc⟩ :=
    exists_continuous_one_zero_of_isCompact (X := G) isCompact_singleton hWopen.isClosed_compl
      (disjoint_compl_right_iff_subset.2 (singleton_subset_iff.2 hW1))

  refine ⟨φ + φ.comp ⟨Inv.inv, continuous_inv⟩, fun g => ?_, fun g => ?_, fun g hg => ?_, ?_⟩
  · simpa only [ContinuousMap.add_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk] using
      add_nonneg (hφIcc g).1 (hφIcc g⁻¹).1
  · simp only [ContinuousMap.add_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk, inv_inv]
    exact add_comm _ _
  · have hg' : g⁻¹ ∉ W := fun hc => hg (by simpa using hWsymm _ hc)
    simp only [ContinuousMap.add_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      hφ0 hg, hφ0 hg', Pi.zero_apply, add_zero]
  · simp only [ContinuousMap.add_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk, inv_one,
      hφ1 rfl]
    norm_num

variable (𝕜) in

theorem exists_isMollifier {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ k : C(G, 𝕜), IsMollifier U k := by
  obtain ⟨V, hVU, hVopen, hV1⟩ := mem_nhds_iff.1 hU

  set W : Set G := V ∩ V⁻¹
  have hWopen : IsOpen W := hVopen.inter hVopen.inv
  have hW1 : (1 : G) ∈ W := ⟨hV1, by simpa using hV1⟩
  have hWU : W ⊆ U := inter_subset_left.trans hVU
  have hWsymm : ∀ g : G, g ∈ W → g⁻¹ ∈ W := by
    rintro g ⟨h1, h2⟩
    exact ⟨by simpa using h2, by simpa using h1⟩
  obtain ⟨ψ, hψ_nonneg, hψ_inv, hψ_zero, hψ_one⟩ := exists_symmetric_bump hWopen hW1 hWsymm

  have hψ_int : Integrable ψ (haarProb G) := integrable_continuousMap G ψ
  have hmass : 0 < ∫ g, ψ g ∂(haarProb G) := by
    refine (integral_pos_iff_support_of_nonneg hψ_nonneg hψ_int).2 ?_
    exact ψ.continuous.isOpen_support.measure_pos _
      ⟨1, by simp [Function.mem_support, hψ_one.ne']⟩
  set c : ℝ := ∫ g, ψ g ∂(haarProb G) with hcdef
  refine ⟨⟨fun g => ((c⁻¹ * ψ g : ℝ) : 𝕜),
    RCLike.continuous_ofReal.comp (continuous_const.mul ψ.continuous)⟩, ?_, ?_, ?_, ?_⟩
  · exact fun g => RCLike.ofReal_nonneg.2 (mul_nonneg (inv_nonneg.2 hmass.le) (hψ_nonneg g))
  · exact fun g => by simp only [ContinuousMap.coe_mk, hψ_inv]
  · simp only [ContinuousMap.coe_mk]
    rw [integral_ofReal, integral_const_mul, ← hcdef, inv_mul_cancel₀ hmass.ne',
      RCLike.ofReal_one]
  · exact fun g hg => by
      simp only [ContinuousMap.coe_mk, hψ_zero g fun hc => hg (hWU hc), mul_zero,
        RCLike.ofReal_zero]

theorem IsMollifier.norm_convolutionCLM_toLp_sub_le {U : Set G} {k : C(G, 𝕜)}
    (h : IsMollifier U k) (f : C(G, 𝕜)) {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ z ∈ U, ∀ x : G, ‖f (z⁻¹ * x) - f x‖ ≤ ε) :
    ‖convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f) - f‖ ≤ ε := by
  refine (ContinuousMap.norm_le _ hε).2 fun x => ?_
  have hval : (convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f) - f) x
      = ∫ z, k z * (f (z⁻¹ * x) - f x) ∂(haarProb G) := by
    rw [ContinuousMap.sub_apply]
    exact convolutionCLM_toLp_sub_apply k f h.integral_eq_one x
  have hbound : ∀ z : G, ‖k z * (f (z⁻¹ * x) - f x)‖ ≤ ‖k z‖ * ε := by
    intro z
    by_cases hz : z ∈ U
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf z hz x) (norm_nonneg _)
    · simp [h.eq_zero_of_notMem z hz]
  rw [hval]
  calc ‖∫ z, k z * (f (z⁻¹ * x) - f x) ∂(haarProb G)‖
      ≤ ∫ z, ‖k z‖ * ε ∂(haarProb G) :=
        norm_integral_le_of_norm_le ((integrable_continuousMap G k).norm.mul_const ε)
          (Eventually.of_forall hbound)
    _ = ε := by rw [integral_mul_const, h.integral_norm_eq_one, one_mul]

variable (𝕜) in

theorem exists_isMollifier_norm_convolutionCLM_toLp_sub_le (f : C(G, 𝕜)) {ε : ℝ}
    (hε : 0 < ε) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ k : C(G, 𝕜), IsMollifier U k ∧
      ‖convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f) - f‖ ≤ ε := by
  obtain ⟨V, hV, hfV⟩ := exists_mem_nhds_one_norm_sub_le f hε
  obtain ⟨k, hk⟩ := exists_isMollifier 𝕜 (Filter.inter_mem hU hV)
  exact ⟨k, hk.mono inter_subset_left,
    hk.norm_convolutionCLM_toLp_sub_le f hε.le fun z hz => hfV z hz.2⟩

end CompactGroup

end DedekindZetaZeroFree.TauCeti
