/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ContinuousAveraging
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RepresentationTheory/Compact/Convolution.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: retain only the generic compact-group density slice; adapt imports and visibility.
The selected declarations are adapted to the current module interface.
License: repository root LICENSE (Apache-2.0).
-/

@[expose] public section

open MeasureTheory
open scoped BoundedContinuousFunction InnerProductSpace

namespace DedekindZetaZeroFree.TauCeti

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

private theorem norm_toLp_le (F : C(G, 𝕜)) :
    ‖ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜 F‖ ≤ ‖F‖ := by
  have hmass : measureUnivNNReal (haarProb G) = 1 :=
    ENNReal.coe_inj.1 (by simp [coe_measureUnivNNReal])
  have hop : ‖(ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜)‖ ≤ 1 := by
    simpa [hmass] using ContinuousMap.toLp_norm_le (E := 𝕜) (p := 2) (𝕜 := 𝕜) (haarProb G)
  calc ‖ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜 F‖
      ≤ ‖(ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜)‖ * ‖F‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg F)
    _ = ‖F‖ := one_mul _

private theorem inner_toLp_left (F : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    ⟪ContinuousMap.toLp 2 (haarProb G) 𝕜 F, f⟫_𝕜
      = ∫ x, (starRingEnd 𝕜) (F x) * f x ∂(haarProb G) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜) F] with x hx
  rw [hx, RCLike.inner_apply]
  ring

noncomputable def convSectionCM (k : C(G, 𝕜)) : C(G, C(G, 𝕜)) :=
  ContinuousMap.curry
    (star (k.comp ⟨fun p : G × G => p.1 * p.2⁻¹, continuous_fst.mul continuous_snd.inv⟩))

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem convSectionCM_apply (k : C(G, 𝕜)) (x y : G) :
    convSectionCM k x y = (starRingEnd 𝕜) (k (x * y⁻¹)) :=
  (rfl)

omit [MeasurableSpace G] [BorelSpace G] in
private theorem norm_convSectionCM_le (k : C(G, 𝕜)) (x : G) : ‖convSectionCM k x‖ ≤ ‖k‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg k)).2 fun y => by
    rw [convSectionCM_apply, RCLike.norm_conj]
    exact k.norm_coe_le_norm _

noncomputable def convSection (k : C(G, 𝕜)) : C(G, Lp 𝕜 2 (haarProb G)) :=
  ⟨fun x => ContinuousMap.toLp 2 (haarProb G) 𝕜 (convSectionCM k x),
    (ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜).continuous.comp (convSectionCM k).continuous⟩

private theorem convSection_apply (k : C(G, 𝕜)) (x : G) :
    convSection k x = ContinuousMap.toLp 2 (haarProb G) 𝕜 (convSectionCM k x) :=
  (rfl)

private theorem norm_convSection_le (k : C(G, 𝕜)) (x : G) : ‖convSection k x‖ ≤ ‖k‖ :=
  (norm_toLp_le _).trans (norm_convSectionCM_le k x)

noncomputable def convolutionₗ (k : C(G, 𝕜)) : Lp 𝕜 2 (haarProb G) →ₗ[𝕜] C(G, 𝕜) where
  toFun f := ⟨fun x => ⟪convSection k x, f⟫_𝕜, (convSection k).continuous.inner continuous_const⟩
  map_add' f₁ f₂ := by ext x; exact inner_add_right (convSection k x) f₁ f₂
  map_smul' c f := by ext x; exact inner_smul_right (convSection k x) f c

theorem norm_convolutionₗ_le (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    ‖convolutionₗ k f‖ ≤ ‖k‖ * ‖f‖ :=
  (ContinuousMap.norm_le _ (by positivity)).2 fun x =>
    (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_convSection_le k x) (norm_nonneg f))

noncomputable def convolutionCLM (k : C(G, 𝕜)) : Lp 𝕜 2 (haarProb G) →L[𝕜] C(G, 𝕜) :=
  LinearMap.mkContinuous (convolutionₗ k) ‖k‖ (norm_convolutionₗ_le k)

private theorem convolutionCLM_apply_apply' (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) (x : G) :
    convolutionCLM k f x = ⟪convSection k x, f⟫_𝕜 :=
  (rfl)

theorem convolutionCLM_apply_apply (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) (x : G) :
    convolutionCLM k f x = ∫ y, k (x * y⁻¹) * f y ∂(haarProb G) := by
  rw [convolutionCLM_apply_apply', convSection_apply, inner_toLp_left]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [convSectionCM_apply, RCLike.conj_conj]

theorem convolutionCLM_toLp_apply (k f : C(G, 𝕜)) (x : G) :
    convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f) x
      = ∫ z, k z * f (z⁻¹ * x) ∂(haarProb G) := by
  set F : G → 𝕜 := fun y => k (x * y⁻¹) * f y with hFdef
  have hcoe : convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f) x
      = ∫ y, F y ∂(haarProb G) := by
    rw [convolutionCLM_apply_apply]
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜) f] with y hy
    rw [hy]
  rw [hcoe]
  calc ∫ y, F y ∂(haarProb G)
      = ∫ z, F (z * x) ∂(haarProb G) := (integral_mul_right_eq_self F x).symm
    _ = ∫ z, F (z⁻¹ * x) ∂(haarProb G) :=
        (integral_inv_eq_self (fun w => F (w * x)) (haarProb G)).symm
    _ = ∫ z, k z * f (z⁻¹ * x) ∂(haarProb G) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        have hz : x * (z⁻¹ * x)⁻¹ = z := by group
        rw [hFdef]
        simp only [hz]

theorem convolutionCLM_toLp_sub_apply (k f : C(G, 𝕜))
    (hk : ∫ g, k g ∂(haarProb G) = 1) (x : G) :
    convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f) x - f x
      = ∫ z, k z * (f (z⁻¹ * x) - f x) ∂(haarProb G) := by
  have h₁ : Integrable (fun z : G => k z * f (z⁻¹ * x)) (haarProb G) :=
    integrable_continuousMap G
      (⟨fun z => k z * f (z⁻¹ * x),
        k.continuous.mul (f.continuous.comp (continuous_id.inv.mul continuous_const))⟩ :
        C(G, 𝕜))
  have h₂ : Integrable (fun z : G => k z * f x) (haarProb G) :=
    (integrable_continuousMap G k).mul_const _
  rw [convolutionCLM_toLp_apply]
  have hsplit : ∫ z, k z * (f (z⁻¹ * x) - f x) ∂(haarProb G)
      = (∫ z, k z * f (z⁻¹ * x) ∂(haarProb G)) - ∫ z, k z * f x ∂(haarProb G) := by
    simp_rw [mul_sub]
    exact integral_sub h₁ h₂
  rw [hsplit, integral_mul_const, hk, one_mul]

theorem norm_convolutionCLM_apply_le (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    ‖convolutionCLM k f‖ ≤ ‖k‖ * ‖f‖ :=
  norm_convolutionₗ_le k f

noncomputable def convolutionOperator (k : C(G, 𝕜)) :
    Lp 𝕜 2 (haarProb G) →L[𝕜] Lp 𝕜 2 (haarProb G) :=
  (ContinuousMap.toLp 2 (haarProb G) 𝕜).comp (convolutionCLM k)

theorem convolutionOperator_apply (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    convolutionOperator k f = ContinuousMap.toLp 2 (haarProb G) 𝕜 (convolutionCLM k f) :=
  (rfl)

theorem coeFn_convolutionOperator (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    convolutionOperator k f =ᵐ[haarProb G] convolutionCLM k f :=
  ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜) _

noncomputable def weightedSectionsCM (k H : C(G, 𝕜)) : C(G, C(G, 𝕜)) :=
  ⟨fun x => H x • convSectionCM k x, H.continuous.smul (convSectionCM k).continuous⟩

noncomputable def weightedSections (k H : C(G, 𝕜)) : C(G, Lp 𝕜 2 (haarProb G)) :=
  ⟨fun x => H x • convSection k x, H.continuous.smul (convSection k).continuous⟩

private theorem integrable_weightedSectionsCM (k H : C(G, 𝕜)) :
    Integrable (fun x => H x • convSectionCM k x) (haarProb G) :=
  integrable_continuousMap G (weightedSectionsCM k H)

private theorem integrable_weightedSections (k H : C(G, 𝕜)) :
    Integrable (fun x => H x • convSection k x) (haarProb G) :=
  integrable_continuousMap G (weightedSections k H)

private theorem integral_weightedSections (k H : C(G, 𝕜)) :
    ∫ x, H x • convSection k x ∂(haarProb G)
      = ContinuousMap.toLp 2 (haarProb G) 𝕜
          (∫ x, H x • convSectionCM k x ∂(haarProb G)) := by
  rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_weightedSectionsCM k H)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_smul, convSection_apply]

private theorem integral_weightedSectionsCM_apply (k H : C(G, 𝕜)) (y : G) :
    (∫ x, H x • convSectionCM k x ∂(haarProb G)) y
      = ∫ x, H x * (starRingEnd 𝕜) (k (x * y⁻¹)) ∂(haarProb G) := by
  have hcomm := (ContinuousMap.evalCLM (R := 𝕜) (M := 𝕜) y).integral_comp_comm
    (integrable_weightedSectionsCM k H)
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, convSectionCM_apply,
    smul_eq_mul] at hcomm
  exact hcomm.symm

private theorem inner_convolutionOperator_toLp (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G))
    (H : C(G, 𝕜)) :
    ⟪convolutionOperator k f, ContinuousMap.toLp 2 (haarProb G) 𝕜 H⟫_𝕜
      = ⟪f, ∫ x, H x • convSection k x ∂(haarProb G)⟫_𝕜 := by
  rw [convolutionOperator_apply, inner_toLp_left,
    ← integral_inner (integrable_weightedSections k H) f]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜) H] with x hx
  rw [hx, convolutionCLM_apply_apply', inner_smul_right, ← inner_conj_symm f (convSection k x),
    mul_comm]

theorem isSelfAdjoint_convolutionOperator (k : C(G, 𝕜))
    (hk : ∀ g : G, k g⁻¹ = (starRingEnd 𝕜) (k g)) :
    IsSelfAdjoint (convolutionOperator k) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f h
  have key : ∀ H : C(G, 𝕜),
      ⟪convolutionOperator k f, ContinuousMap.toLp 2 (haarProb G) 𝕜 H⟫_𝕜
        = ⟪f, convolutionOperator k (ContinuousMap.toLp 2 (haarProb G) 𝕜 H)⟫_𝕜 := by
    intro H
    rw [inner_convolutionOperator_toLp, integral_weightedSections, convolutionOperator_apply]
    congr 2
    ext y
    rw [integral_weightedSectionsCM_apply, convolutionCLM_apply_apply]
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜) H] with x hx
    have hsym : (starRingEnd 𝕜) (k (x * y⁻¹)) = k (y * x⁻¹) := by
      rw [← hk (x * y⁻¹), mul_inv_rev, inv_inv]
    rw [hx, hsym, mul_comm]
  have hcont₁ : Continuous fun u : Lp 𝕜 2 (haarProb G) => ⟪convolutionOperator k f, u⟫_𝕜 :=
    continuous_const.inner continuous_id
  have hcont₂ : Continuous fun u : Lp 𝕜 2 (haarProb G) => ⟪f, convolutionOperator k u⟫_𝕜 :=
    continuous_const.inner (convolutionOperator k).continuous
  exact congrFun
    ((ContinuousMap.toLp_denseRange (E := 𝕜) (p := 2) (haarProb G) 𝕜
      (by simp)).equalizer hcont₁ hcont₂ (funext key)) h

theorem convolutionCLM_compMeasurePreserving_mul_right (k : C(G, 𝕜))
    (f : Lp 𝕜 2 (haarProb G)) (g₀ x : G) :
    convolutionCLM k
        (Lp.compMeasurePreserving (· * g₀) (measurePreserving_mul_right (haarProb G) g₀) f) x
      = convolutionCLM k f (x * g₀) := by
  have hg : ∀ y : G, x * g₀ * (y * g₀)⁻¹ = x * y⁻¹ := fun y => by group
  rw [convolutionCLM_apply_apply, convolutionCLM_apply_apply,
    ← integral_mul_right_eq_self (fun y => k (x * g₀ * y⁻¹) * (f : G → 𝕜) y) g₀]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving (E := 𝕜) (p := 2) f
    (measurePreserving_mul_right (haarProb G) g₀)] with y hy
  rw [hy, hg y]
  rfl

theorem convolutionOperator_compMeasurePreserving_mul_right (k : C(G, 𝕜))
    (f : Lp 𝕜 2 (haarProb G)) (g₀ : G) :
    convolutionOperator k
        (Lp.compMeasurePreserving (· * g₀) (measurePreserving_mul_right (haarProb G) g₀) f)
      = Lp.compMeasurePreserving (· * g₀) (measurePreserving_mul_right (haarProb G) g₀)
          (convolutionOperator k f) := by
  have hqmp := (measurePreserving_mul_right (haarProb G) g₀).quasiMeasurePreserving
  rw [Lp.ext_iff]
  refine (coeFn_convolutionOperator k _).trans ?_
  refine Filter.EventuallyEq.symm (((Lp.coeFn_compMeasurePreserving (E := 𝕜) (p := 2)
    (convolutionOperator k f) (measurePreserving_mul_right (haarProb G) g₀)).trans
      (hqmp.ae_eq_comp (coeFn_convolutionOperator k f))).trans ?_)
  exact Filter.Eventually.of_forall fun y =>
    (convolutionCLM_compMeasurePreserving_mul_right k f g₀ y).symm

private theorem norm_convolutionCLM_apply_sub_apply_le (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G))
    (x y : G) :
    ‖convolutionCLM k f x - convolutionCLM k f y‖
      ≤ ‖convSection k x - convSection k y‖ * ‖f‖ := by
  rw [convolutionCLM_apply_apply', convolutionCLM_apply_apply', ← inner_sub_left]
  exact norm_inner_le_norm _ _

noncomputable def convolutionUnitBallImage (k : C(G, 𝕜)) : Set (G →ᵇ 𝕜) :=
  (fun f : Lp 𝕜 2 (haarProb G) =>
      ContinuousMap.isometryEquivBoundedOfCompact G 𝕜 (convolutionCLM k f)) ''
    Metric.closedBall 0 1

private theorem convolutionUnitBallImage_apply_mem_closedBall (k : C(G, 𝕜)) (F : G →ᵇ 𝕜) (x : G)
    (hF : F ∈ convolutionUnitBallImage k) : F x ∈ Metric.closedBall (0 : 𝕜) ‖k‖ := by
  obtain ⟨f, hf, rfl⟩ := hF
  rw [Metric.mem_closedBall, dist_zero_right] at hf ⊢
  rw [ContinuousMap.isometryEquivBoundedOfCompact_apply,
    BoundedContinuousFunction.mkOfCompact_apply]
  refine ((convolutionCLM k f).norm_coe_le_norm x).trans ?_
  calc ‖convolutionCLM k f‖ ≤ ‖k‖ * ‖f‖ := norm_convolutionCLM_apply_le k f
    _ ≤ ‖k‖ * 1 := by gcongr
    _ = ‖k‖ := mul_one _

private theorem equicontinuous_convolutionUnitBallImage (k : C(G, 𝕜)) :
    Equicontinuous ((↑) : convolutionUnitBallImage k → G → 𝕜) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.1 ((convSection k).continuous.tendsto x₀) ε hε] with x hx
  rintro ⟨-, f, hf, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hf
  rw [dist_eq_norm] at hx ⊢
  calc ‖convolutionCLM k f x₀ - convolutionCLM k f x‖
      ≤ ‖convSection k x₀ - convSection k x‖ * ‖f‖ :=
        norm_convolutionCLM_apply_sub_apply_le k f x₀ x
    _ ≤ ‖convSection k x₀ - convSection k x‖ * 1 := by gcongr
    _ = ‖convSection k x - convSection k x₀‖ := by rw [mul_one, norm_sub_rev]
    _ < ε := hx

private theorem isCompact_closure_convolutionUnitBallImage (k : C(G, 𝕜)) :
    IsCompact (closure (convolutionUnitBallImage k)) :=
  BoundedContinuousFunction.arzela_ascoli _ (isCompact_closedBall (0 : 𝕜) ‖k‖) _
    (convolutionUnitBallImage_apply_mem_closedBall k) (equicontinuous_convolutionUnitBallImage k)

theorem isCompactOperator_convolutionCLM (k : C(G, 𝕜)) :
    IsCompactOperator (convolutionCLM (G := G) k) := by
  refine (isCompactOperator_iff_image_closedBall_subset_compact
    (convolutionCLM (G := G) k).toLinearMap one_pos).2
    ⟨(ContinuousMap.isometryEquivBoundedOfCompact G 𝕜).symm ''
        closure (convolutionUnitBallImage k),
      (isCompact_closure_convolutionUnitBallImage k).image
        (ContinuousMap.isometryEquivBoundedOfCompact G 𝕜).symm.continuous, ?_⟩
  rintro - ⟨f, hf, rfl⟩
  exact ⟨_, subset_closure ⟨f, hf, rfl⟩,
    (ContinuousMap.isometryEquivBoundedOfCompact G 𝕜).symm_apply_apply _⟩

theorem isCompactOperator_convolutionOperator (k : C(G, 𝕜)) :
    IsCompactOperator (convolutionOperator (G := G) k) :=
  (isCompactOperator_convolutionCLM k).clm_comp (ContinuousMap.toLp 2 (haarProb G) 𝕜)

theorem finiteDimensional_eigenspace_convolutionOperator (k : C(G, 𝕜)) {μ : 𝕜} (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (isCompactOperator_convolutionOperator k) μ hμ

theorem convolutionCLM_eq_zero_of_mem_eigenspace_zero (k : C(G, 𝕜))
    {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap 0) :
    convolutionCLM k f = 0 := by
  rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, zero_smul] at hf
  refine ContinuousMap.toLp_injective (E := 𝕜) (𝕜 := 𝕜) (p := 2) (haarProb G) ?_
  rw [← convolutionOperator_apply, hf, map_zero]

theorem compMeasurePreserving_mul_right_mem_eigenspace_convolutionOperator (k : C(G, 𝕜)) (μ : 𝕜)
    (g₀ : G) {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :
    Lp.compMeasurePreserving (· * g₀) (measurePreserving_mul_right (haarProb G) g₀) f ∈
      Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ := by
  rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe] at hf ⊢
  rw [convolutionOperator_compMeasurePreserving_mul_right, hf]
  exact (Lp.compMeasurePreservingₗ 𝕜 (· * g₀)
    (measurePreserving_mul_right (haarProb G) g₀)).map_smul μ f

theorem orthogonalComplement_iSup_eigenspaces_convolutionOperator_eq_bot (k : C(G, 𝕜))
    (hk : ∀ g : G, k g⁻¹ = (starRingEnd 𝕜) (k g)) :
    (⨆ μ : 𝕜, Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (isCompactOperator_convolutionOperator k)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1
      (isSelfAdjoint_convolutionOperator k hk))

end CompactGroup

end DedekindZetaZeroFree.TauCeti
