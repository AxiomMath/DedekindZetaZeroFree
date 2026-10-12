module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Distribution.TestFunction

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCplxOpenCellDistributionsInfinitesimal

open scoped Topology

theorem compactly_supported_directional_quotient_tendstoUniformly
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (v : E) :
    TendstoUniformly (fun t : ℝ => fun x : E =>
      t⁻¹ • (f (x + t • v) - f x))
      (fun x : E => fderiv ℝ f x v) (𝓝[≠] 0) := by
  have hu : UniformContinuous (fderiv ℝ f) :=
    (hc.fderiv ℝ).uniformContinuous_of_continuous (hf.continuous_fderiv one_ne_zero)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  let C : ℝ := ε / (‖v‖ + 1)
  have hC : 0 < C := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.uniformContinuous_iff.mp hu C hC
  have htend : Filter.Tendsto (fun t : ℝ => ‖t • v‖) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (((continuous_id : Continuous (fun t : ℝ => t)).smul (continuous_const : Continuous (fun _ : ℝ => v))).norm.tendsto (0 : ℝ)).mono_left
      nhdsWithin_le_nhds
  filter_upwards [htend.eventually (gt_mem_nhds hδ), self_mem_nhdsWithin] with t ht htne
  have ht0 : t ≠ 0 := htne
  intro x
  have hb : ∀ y ∈ segment ℝ x (x + t • v), ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ C := by
    intro y hy
    apply le_of_lt
    rw [← dist_eq_norm]
    apply hδbound
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (norm_sub_le_of_mem_segment hy) (by simpa using ht)
  have hm := (convex_segment x (x + t • v)).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => (hf.differentiable one_ne_zero).differentiableAt) hb
    (left_mem_segment ℝ x (x + t • v)) (right_mem_segment ℝ x (x + t • v))
  have heq : t⁻¹ • (f (x + t • v) - f x) - fderiv ℝ f x v =
      t⁻¹ • (f (x + t • v) - f x - fderiv ℝ f x (t • v)) := by
    simp [smul_sub, smul_smul, ht0]
  rw [dist_comm, dist_eq_norm, heq, norm_smul]
  calc
    ‖t⁻¹‖ * ‖f (x + t • v) - f x - fderiv ℝ f x (t • v)‖
        ≤ ‖t⁻¹‖ * (C * ‖t • v‖) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          simpa using hm
    _ = C * ‖v‖ := by
      rw [norm_smul, norm_inv]
      have hn : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht0
      field_simp
    _ < ε := by
      dsimp [C]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (show 0 < ‖v‖ + 1 by positivity)).2
      nlinarith [norm_nonneg v]

end DedekindZetaZeroFree.KPCplxOpenCellDistributionsInfinitesimal

end

section

namespace DedekindZetaZeroFree.KPCplxOpenCellDistributionsInfinitesimal

theorem iteratedFDeriv_directional_derivative
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : E) (i : ℕ) (x : E) :
    iteratedFDeriv ℝ i (fun y => fderiv ℝ f y v) x =
      fderiv ℝ (iteratedFDeriv ℝ i f) x v := by
  induction i generalizing x with
  | zero =>
    ext m
    rw [← fderiv_continuousMultilinear_apply_const_apply
      ((hf.iteratedFDeriv_right (m := (⊤ : ℕ∞)) (i := 0) (by simp)).differentiable
        (by simp) x)]
    simp only [iteratedFDeriv_zero_apply]
  | succ i ih =>
    let J := iteratedFDeriv ℝ i f
    have hJ : ContDiff ℝ (⊤ : ℕ∞) J :=
      hf.iteratedFDeriv_right (by simp)
    have hdJ := (hJ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
      (by simp) x
    have heq : iteratedFDeriv ℝ i (fun y => fderiv ℝ f y v) =
        (fun y => fderiv ℝ J y v) := funext ih
    ext m
    rw [iteratedFDeriv_succ_apply_left, heq]
    rw [← fderiv_continuousMultilinear_apply_const_apply
      ((hf.iteratedFDeriv_right (m := (⊤ : ℕ∞)) (i := i+1) (by simp)).differentiable
        (by simp) x)]
    have heq' : (fun y => iteratedFDeriv ℝ (i+1) f y m) =
        (fun y => fderiv ℝ J y (m 0) (Fin.tail m)) := rfl
    rw [heq', fderiv_continuousMultilinear_apply_const_apply
      (((hJ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
        contDiff_const).differentiable (by simp) x)]
    rw [fderiv_clm_apply hdJ (differentiableAt_const v),
      fderiv_clm_apply hdJ (differentiableAt_const (m 0))]
    simpa using congrArg (fun c => c (Fin.tail m))
      (hJ.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness]) (m 0) v)

end DedekindZetaZeroFree.KPCplxOpenCellDistributionsInfinitesimal

end

section

namespace DedekindZetaZeroFree.KPCplxOpenCellTranslationInvariance

open scoped Distributions Topology
open Set Filter

noncomputable def translationForDifferenceQuotient (t : ℂ)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) :
    𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ) where
  toFun x := φ (x + t)
  contDiff' := φ.contDiff.comp (contDiff_id.add contDiff_const)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight t)
  tsupport_subset' := by simp

theorem invariant_annihilates_translation_difference
    (D : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ) →L[ℂ] ℂ)
    (hD : ∀ (t : ℂ) (φ χ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)),
      (∀ x : ℂ, χ x = φ (x + t)) → D χ = D φ)
    (t : ℂ) (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) :
    D (translationForDifferenceQuotient t φ - φ) = 0 := by
  have ht : D (translationForDifferenceQuotient t φ) = D φ := hD t φ (translationForDifferenceQuotient t φ) (fun _ => rfl)
  rw [map_sub, ht, sub_self]

noncomputable def translationDifferenceQuotient (t : ℝ) (v : ℂ)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) :
    𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ) :=
  (↑(t⁻¹) : ℂ) • (translationForDifferenceQuotient (t • v) φ - φ)

theorem invariant_annihilates_translation_difference_quotient
    (D : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ) →L[ℂ] ℂ)
    (hD : ∀ (t : ℂ) (φ χ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)),
      (∀ x : ℂ, χ x = φ (x + t)) → D χ = D φ)
    (t : ℝ) (v : ℂ) (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) :
    D (translationDifferenceQuotient t v φ) = 0 := by
  simp only [translationDifferenceQuotient, map_smul]
  rw [invariant_annihilates_translation_difference D hD]
  simp

noncomputable def differenceQuotientCompact (v : ℂ)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) : TopologicalSpace.Compacts ℂ :=
  ⟨Metric.cthickening ‖v‖ (tsupport φ), φ.hasCompactSupport.cthickening⟩

lemma translation_support_subset_differenceQuotientCompact (t : ℝ) (v : ℂ)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) (ht : ‖t‖ ≤ 1) :
    tsupport (translationForDifferenceQuotient (t • v) φ) ⊆
      differenceQuotientCompact v φ := by
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  have hy : x + t • v ∈ tsupport φ := subset_tsupport φ (by
    simpa [Function.mem_support, translationForDifferenceQuotient] using hx)
  apply Metric.mem_cthickening_of_dist_le x (x + t • v) ‖v‖ (tsupport φ) hy
  simpa [dist_eq_norm, norm_smul] using mul_le_of_le_one_left (norm_nonneg v) ht

lemma quotient_support_subset_differenceQuotientCompact (t : ℝ) (v : ℂ)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) (ht : ‖t‖ ≤ 1) :
    tsupport (translationDifferenceQuotient t v φ) ⊆ differenceQuotientCompact v φ := by
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  have hdiff : (translationForDifferenceQuotient (t • v) φ - φ) x ≠ 0 := by
    intro h
    apply hx
    change (↑(t⁻¹) : ℂ) • ((translationForDifferenceQuotient (t • v) φ - φ) x) = 0
    rw [h, smul_zero]
  by_cases hφ : φ x = 0
  · apply translation_support_subset_differenceQuotientCompact t v φ ht
    apply subset_tsupport
    simpa [Function.mem_support, hφ] using hdiff
  · exact Metric.self_subset_cthickening (δ := ‖v‖) (tsupport φ) (subset_tsupport φ hφ)

lemma derivative_support_subset_differenceQuotientCompact (v : ℂ)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) :
    tsupport (TestFunction.lineDerivCLM ℂ v φ :
      𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) ⊆ differenceQuotientCompact v φ := by
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  apply Metric.self_subset_cthickening (δ := ‖v‖) (tsupport φ)
  apply support_fderiv_subset ℝ
  intro hzero
  apply hx
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp),
    (φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv, hzero]
  rfl

noncomputable def supportedDifferenceQuotient (t : ℝ) (v : ℂ)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) (ht : ‖t‖ ≤ 1) :
    𝓓_{differenceQuotientCompact v φ}(ℂ, ℂ) :=
  ContDiffMapSupportedIn.of_support_subset
    (translationDifferenceQuotient t v φ).contDiff
    (subset_tsupport _ |>.trans (quotient_support_subset_differenceQuotientCompact t v φ ht))

noncomputable def supportedDirectionalDerivative (v : ℂ)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) :
    𝓓_{differenceQuotientCompact v φ}(ℂ, ℂ) :=
  ContDiffMapSupportedIn.of_support_subset
    (TestFunction.lineDerivCLM ℂ v φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)).contDiff
    (subset_tsupport _ |>.trans (derivative_support_subset_differenceQuotientCompact v φ))

lemma supported_smooth_tendsto_of_all_jets
    {K : TopologicalSpace.Compacts ℂ} {ι : Type*} {l : Filter ι}
    (f : ι → 𝓓_{K}(ℂ, ℂ)) (g : 𝓓_{K}(ℂ, ℂ))
    (h : ∀ i : ℕ, TendstoUniformly (fun a => iteratedFDeriv ℝ i (f a))
      (iteratedFDeriv ℝ i g) l) : Tendsto f l (𝓝 g) := by
  change Tendsto f l (@nhds _ (⨅ i : ℕ,
    TopologicalSpace.induced (ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i)
      inferInstance) g)
  rw [nhds_iInf]
  apply tendsto_iInf.mpr
  intro i
  rw [nhds_induced, tendsto_comap_iff]
  apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
  simpa only [Function.comp_apply, ContDiffMapSupportedIn.structureMapLM_top_apply] using h i

noncomputable def supportedDifferenceQuotientFamily (v : ℂ)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ))
    (t : ℝ) : 𝓓_{differenceQuotientCompact v φ}(ℂ, ℂ) :=
  if ht : ‖t‖ ≤ 1 then supportedDifferenceQuotient t v φ ht else 0

lemma translationDifferenceQuotient_tendsto_of_all_jets (v : ℂ)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ))
    (h : ∀ i : ℕ, TendstoUniformly
      (fun t : ℝ => iteratedFDeriv ℝ i (supportedDifferenceQuotientFamily v φ t))
      (iteratedFDeriv ℝ i (supportedDirectionalDerivative v φ)) (𝓝[≠] 0)) :
    Tendsto (fun t : ℝ => translationDifferenceQuotient t v φ) (𝓝[≠] 0)
      (𝓝 (TestFunction.lineDerivCLM ℂ v φ :
        𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ))) := by
  have hs := supported_smooth_tendsto_of_all_jets
    (supportedDifferenceQuotientFamily v φ) (supportedDirectionalDerivative v φ) h
  have hi := (TestFunction.ofSupportedInCLM ℂ
    (show (differenceQuotientCompact v φ : Set ℂ) ⊆
      (⊤ : TopologicalSpace.Opens ℂ) from fun _ _ => Set.mem_univ _)).continuous.tendsto
    (supportedDirectionalDerivative v φ)
  have hlim := hi.comp hs
  have he : ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖t‖ ≤ 1 := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    have := Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)
    filter_upwards [this] with t ht
    exact (show ‖t‖ < 1 by simpa [Metric.mem_ball, dist_zero_right] using ht).le
  apply hlim.congr'
  filter_upwards [he] with t ht
  ext x
  change supportedDifferenceQuotientFamily v φ t x = translationDifferenceQuotient t v φ x
  rw [supportedDifferenceQuotientFamily, dif_pos ht]
  rfl

lemma invariant_annihilates_directional_derivatives_of_all_jets
    (D : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ) →L[ℂ] ℂ)
    (hD : ∀ (t : ℂ) (φ χ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)),
      (∀ x : ℂ, χ x = φ (x + t)) → D χ = D φ)
    (v : ℂ) (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ))
    (h : ∀ i : ℕ, TendstoUniformly
      (fun t : ℝ => iteratedFDeriv ℝ i (supportedDifferenceQuotientFamily v φ t))
      (iteratedFDeriv ℝ i (supportedDirectionalDerivative v φ)) (𝓝[≠] 0)) :
    D (TestFunction.lineDerivCLM ℂ v φ :
      𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) = 0 := by
  have hl := D.continuous.tendsto _ |>.comp
    (translationDifferenceQuotient_tendsto_of_all_jets v φ h)
  have hz : (fun t : ℝ => D (translationDifferenceQuotient t v φ)) = fun _ => 0 :=
    funext fun t => invariant_annihilates_translation_difference_quotient D hD t v φ
  simp only [Function.comp_def] at hl
  rw [hz] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds

lemma translationDifferenceQuotient_iteratedFDeriv (t : ℝ) (v : ℂ)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) (i : ℕ) (x : ℂ) :
    iteratedFDeriv ℝ i (translationDifferenceQuotient t v φ) x =
      t⁻¹ • (iteratedFDeriv ℝ i φ (x + t • v) - iteratedFDeriv ℝ i φ x) := by
  have he : (translationDifferenceQuotient t v φ : ℂ → ℂ) =
      t⁻¹ • (fun y : ℂ => φ (y + t • v) - φ y) := by
    funext y
    simp [translationDifferenceQuotient, translationForDifferenceQuotient,
      Complex.real_smul]
  have hf : ContDiff ℝ (i : ℕ) (φ : ℂ → ℂ) := φ.contDiff.of_le (by simp)
  have htr : ContDiff ℝ (i : ℕ) (fun y : ℂ => φ (y + t • v)) :=
    hf.comp (contDiff_id.add contDiff_const)
  have hsub : ContDiff ℝ (i : ℕ) (fun y : ℂ => φ (y + t • v) - φ y) := htr.sub hf
  rw [he, iteratedFDeriv_const_smul_apply hsub.contDiffAt,
    fun_iteratedFDeriv_sub_apply htr.contDiffAt hf.contDiffAt,
    iteratedFDeriv_comp_add_right]

theorem invariant_annihilates_directional_derivatives
    (D : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ) →L[ℂ] ℂ)
    (hD : ∀ (t : ℂ) (φ χ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)),
      (∀ x : ℂ, χ x = φ (x + t)) → D χ = D φ)
    (v : ℂ) (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) :
    D (TestFunction.lineDerivCLM ℂ v φ :
      𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) = 0 := by
  apply invariant_annihilates_directional_derivatives_of_all_jets D hD v φ
  intro i
  have hjet : ContDiff ℝ 1 (iteratedFDeriv ℝ i φ) :=
    φ.contDiff.iteratedFDeriv_right (by simp)
  have hlim := DedekindZetaZeroFree.KPCplxOpenCellDistributionsInfinitesimal.compactly_supported_directional_quotient_tendstoUniformly
      (iteratedFDeriv ℝ i φ) hjet (φ.hasCompactSupport.iteratedFDeriv i) v
  have hder : (supportedDirectionalDerivative v φ : ℂ → ℂ) =
      fun x => fderiv ℝ φ x v := by
    funext x
    change (TestFunction.lineDerivCLM ℂ v φ :
      𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) x = _
    rw [TestFunction.lineDerivCLM_apply_of_le (by simp),
      (φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
  have hderjet : iteratedFDeriv ℝ i (supportedDirectionalDerivative v φ) =
      fun x => fderiv ℝ (iteratedFDeriv ℝ i φ) x v := by
    rw [hder]
    funext x
    exact DedekindZetaZeroFree.KPCplxOpenCellDistributionsInfinitesimal.iteratedFDeriv_directional_derivative φ φ.contDiff v i x
  rw [hderjet]
  apply (tendstoUniformly_congr (F := fun t : ℝ =>
    iteratedFDeriv ℝ i (supportedDifferenceQuotientFamily v φ t))
    (F' := fun t : ℝ => fun x : ℂ =>
      t⁻¹ • (iteratedFDeriv ℝ i φ (x + t • v) - iteratedFDeriv ℝ i φ x))
    (p := 𝓝[≠] 0) ?_).mpr hlim
  have he : ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖t‖ ≤ 1 := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)]
      with t ht
    exact (show ‖t‖ < 1 by
      simpa [Metric.mem_ball, dist_zero_right] using ht).le
  filter_upwards [he] with t ht
  have hquot : (supportedDifferenceQuotientFamily v φ t : ℂ → ℂ) =
      translationDifferenceQuotient t v φ := by
    rw [supportedDifferenceQuotientFamily, dif_pos ht]
    rfl
  rw [hquot]
  funext x
  exact translationDifferenceQuotient_iteratedFDeriv t v φ i x

end DedekindZetaZeroFree.KPCplxOpenCellTranslationInvariance

end
