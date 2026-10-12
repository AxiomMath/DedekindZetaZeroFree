module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ComplexExceptionalFunctional
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ClosedCellJetsAndEigenDistributions
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.TranslationInvariantDistributions

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCplxOpenCellTranslationInvariance

open KPCplxCharacterHaar MeasureTheory Set
open scoped Distributions Convolution

theorem smooth_interval_primitive (f : ℝ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ t in a..x, f t) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨intervalIntegral.differentiable_integral_of_continuous hf.continuous, ?_⟩
  have hd : deriv (fun x => ∫ t in a..x, f t) = f := by
    funext x
    exact hf.continuous.deriv_integral f a x
  rw [hd]
  exact hf

theorem mean_zero_real_test_has_primitive
    (f : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ))
    (hf : ∫ t : ℝ, f t = 0) :
    ∃ g : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ),
      ∀ x, deriv (g : ℝ → ℂ) x = f x := by
  obtain ⟨R, hR, hbound⟩ := f.hasCompactSupport.isBounded.subset_ball_lt 0 0
  have hz (x : ℝ) (hx : x ≤ -R ∨ R ≤ x) : f x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hb := hbound hmem
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt] at hb
    rcases hx with hx | hx <;> linarith
  let p : ℝ → ℂ := fun x => ∫ t in (-R)..x, f t
  have hpzero (x : ℝ) (hx : x ∉ Icc (-R) R) : p x = 0 := by
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · dsimp [p]
      apply intervalIntegral.integral_zero_ae
      filter_upwards [] with t ht
      simp only [uIoc_of_ge (le_of_lt hx), mem_Ioc] at ht
      exact hz t (Or.inl ht.2)
    · dsimp [p]
      rw [intervalIntegral.integral_of_le (by linarith : -R ≤ x)]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact hf
      · intro t ht
        simp only [mem_Ioc, not_and_or, not_lt, not_le] at ht
        rcases ht with ht | ht
        · exact hz t (Or.inl ht)
        · exact hz t (Or.inr (by linarith))
  let g : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ) :=
    ⟨p, smooth_interval_primitive f f.contDiff (-R),
      (HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-R) R)) hpzero),
      by simp⟩
  refine ⟨g, ?_⟩
  intro x
  exact f.continuous.deriv_integral f (-R) x

 theorem smooth_fiber_convolution (F : ℝ × ℝ → ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (R : ℝ)
    (hzero : ∀ x y, x ∉ Icc (-R) R → F (x,y) = 0)
    (u : ℝ → ℝ) (hu : LocallyIntegrable u volume) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => ∫ t : ℝ, u t • F (p.1-t,p.2)) := by
  let g : (ℝ × ℝ) → ℝ → ℂ := fun p t => F (t,p.2)
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ => g q.1 q.2) :=
    hF.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
  have hc := contDiffOn_convolution_right_with_param_comp
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)
    (s := (univ : Set (ℝ × ℝ))) (v := fun p : ℝ × ℝ => p.1)
    contDiff_fst.contDiffOn isOpen_univ isCompact_Icc
    (g := g) (k := Icc (-R) R) (fun p t _ ht => hzero t p.2 ht) hu
    (by convert hg.contDiffOn using 1
        · funext q
          rcases q with ⟨p,t⟩
          rfl)
  simpa [convolution_def, g, contDiffOn_univ] using hc

 theorem smooth_fiber_integral (F : ℝ × ℝ → ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (R : ℝ)
    (hzero : ∀ x y, x ∉ Icc (-R) R → F (x,y) = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => ∫ t : ℝ, F (t,y)) := by
  have hc := smooth_fiber_convolution F hF R hzero (fun _ => 1)
    (locallyIntegrable_const (1 : ℝ))
  have hc' := hc.comp (contDiff_const.prodMk contDiff_id :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => ((0 : ℝ), y)))
  have heq : (fun y : ℝ => ∫ t : ℝ, (1 : ℝ) • F (0-t,y)) =
      (fun y : ℝ => ∫ t : ℝ, F (t,y)) := by
    funext y
    simp only [zero_sub, one_smul]
    exact integral_neg_eq_self (fun t : ℝ => F (t,y)) volume
  simpa only [Function.comp_def, heq] using hc'

 theorem smooth_fiber_lower_integral (F : ℝ × ℝ → ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (R : ℝ)
    (hzero : ∀ x y, x ∉ Icc (-R) R → F (x,y) = 0) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => ∫ t in Iio p.1, F (t,p.2)) := by
  classical
  have hc := smooth_fiber_convolution F hF R hzero
    ((Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)))
    ((locallyIntegrable_const (1 : ℝ)).indicator measurableSet_Ioi)
  have heq : (fun p : ℝ × ℝ => ∫ t : ℝ,
      (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) t • F (p.1-t,p.2)) =
      (fun p : ℝ × ℝ => ∫ t in Iio p.1, F (t,p.2)) := by
    funext p
    rw [← integral_indicator measurableSet_Iio]
    rw [← integral_sub_left_eq_self
      ((Iio p.1).indicator (fun t : ℝ => F (t,p.2))) volume p.1]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : 0 < t
    · simp [ht, show p.1 - t < p.1 by linarith]
    · simp [ht, show ¬ p.1 - t < p.1 by linarith]
  rw [← heq]
  exact hc

 theorem hasDerivAt_lower_integral (f : ℝ → ℂ) (hf : Continuous f)
    (hfi : Integrable f) (x : ℝ) :
    HasDerivAt (fun s => ∫ t in Iio s, f t) (f x) x := by
  have heq : (fun s => ∫ t in Iio s, f t) =
      (fun s => (∫ t in (0 : ℝ)..s, f t) + ∫ t in Iic (0 : ℝ), f t) := by
    funext s
    rw [← integral_Iic_eq_integral_Iio]
    rw [← intervalIntegral.integral_Iic_sub_Iic hfi.integrableOn hfi.integrableOn]
    abel
  rw [heq]
  have hd := (intervalIntegral.differentiable_integral_of_continuous (a := 0) hf x).hasDerivAt
  rw [hf.deriv_integral f 0 x] at hd
  exact hd.add_const _

 theorem compactSupport_fiber_lower_integral (F : ℝ × ℝ → ℂ) (R : ℝ)
    (hzero : ∀ x y, x ∉ Icc (-R) R ∨ y ∉ Icc (-R) R → F (x,y) = 0)
    (hmean : ∀ y, ∫ t : ℝ, F (t,y) = 0) :
    HasCompactSupport (fun p : ℝ × ℝ => ∫ t in Iio p.1, F (t,p.2)) := by
  apply HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (-R) R ×ˢ Icc (-R) R))
  intro p hp
  simp only [mem_prod, not_and_or] at hp
  rcases hp with hx | hy
  · simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      apply hzero t p.2
      left
      simp only [mem_Icc, not_and_or, not_le]
      exact Or.inl (by have := ht; simp only [mem_Iio] at this; linarith)
    · rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact hmean p.2
      · intro t ht
        apply hzero t p.2
        left
        simp only [mem_Iio, not_lt] at ht
        simp only [mem_Icc, not_and_or, not_le]
        exact Or.inr (by linarith)
  · apply setIntegral_eq_zero_of_forall_eq_zero
    intro t _
    exact hzero t p.2 (Or.inr hy)

 theorem horizontal_mean_zero_has_primitive (F : ℝ × ℝ → ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (R : ℝ)
    (hzero : ∀ x y, x ∉ Icc (-R) R ∨ y ∉ Icc (-R) R → F (x,y) = 0)
    (hmean : ∀ y, ∫ t : ℝ, F (t,y) = 0) :
    ∃ g : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ), ∀ z : ℂ,
      (TestFunction.lineDerivCLM ℂ (1 : ℂ) g :
        𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) z = F (z.re,z.im) := by
  let P : ℝ × ℝ → ℂ := fun p => ∫ t in Iio p.1, F (t,p.2)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P :=
    smooth_fiber_lower_integral F hF R (fun x y hx => hzero x y (Or.inl hx))
  have hPc : HasCompactSupport P := compactSupport_fiber_lower_integral F R hzero hmean
  have hQ : ContDiff ℝ (⊤ : ℕ∞) (P ∘ Complex.equivRealProdCLM) :=
    hP.comp Complex.equivRealProdCLM.contDiff
  have hQc : HasCompactSupport (P ∘ Complex.equivRealProdCLM) :=
    hPc.comp_homeomorph Complex.equivRealProdCLM.toHomeomorph
  let g : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ) :=
    ⟨P ∘ Complex.equivRealProdCLM, hQ, hQc, subset_univ _⟩
  refine ⟨g, ?_⟩
  intro z
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  have hs (y : ℝ) : HasCompactSupport (fun t : ℝ => F (t,y)) := by
    apply HasCompactSupport.intro isCompact_Icc
    intro t ht
    exact hzero t y (Or.inl ht)
  have hc (y : ℝ) : Continuous (fun t : ℝ => F (t,y)) :=
    hF.continuous.comp (continuous_id.prodMk continuous_const)
  have hd := hasDerivAt_lower_integral (fun t => F (t,z.im)) (hc z.im)
    ((hc z.im).integrable_of_hasCompactSupport (hs z.im)) z.re
  have hd' := (by simpa using hd :
    HasDerivAt (fun s => ∫ t in Iio s, F (t,z.im)) (F (z.re,z.im)) (z.re + id 0)).scomp
    0 ((hasDerivAt_id (0 : ℝ)).const_add z.re)
  have heq : (fun t : ℝ => g (z + t • (1 : ℂ))) =
      (fun t : ℝ => ∫ s in Iio (z.re + t), F (s,z.im)) := by
    funext t
    change (∫ s in Iio (z + t • (1 : ℂ)).re, F (s,(z+t • (1 : ℂ)).im)) = _
    simp
  rw [lineDeriv, heq]
  simpa only [Function.comp_def, add_zero, one_smul] using hd'.deriv

theorem mean_zero_is_divergence
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ))
    (hφ : ∫ x : ℂ, φ x ∂euclideanArea = 0) :
    ∃ g h : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ),
      φ = (TestFunction.lineDerivCLM ℂ (1 : ℂ) g :
        𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) +
        (TestFunction.lineDerivCLM ℂ Complex.I h :
          𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) := by
  let F : ℝ × ℝ → ℂ := φ ∘ Complex.equivRealProdCLM.symm
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := φ.contDiff.comp
    Complex.equivRealProdCLM.symm.contDiff
  have hFc : HasCompactSupport F := φ.hasCompactSupport.comp_homeomorph
    Complex.equivRealProdCLM.symm.toHomeomorph
  obtain ⟨R₀, hR₀, hbound⟩ := hFc.isBounded.subset_ball_lt 0 0
  let R : ℝ := max R₀ 2
  have hzero (x y : ℝ) (h : x ∉ Icc (-R) R ∨ y ∉ Icc (-R) R) : F (x,y) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hb := hbound hm
    simp only [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
      max_lt_iff, abs_lt] at hb
    have hle : R₀ ≤ R := le_max_left _ _
    rcases h with hx | hy
    · simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx <;> linarith
    · simp only [mem_Icc, not_and_or, not_le] at hy
      rcases hy with hy | hy <;> linarith
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let ρ : ℝ → ℂ := fun x => (b.normed volume x : ℂ)
  have hρ : ContDiff ℝ (⊤ : ℕ∞) ρ := Complex.ofRealCLM.contDiff.comp b.contDiff_normed
  have hρc : HasCompactSupport ρ := b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  have hρint : ∫ x : ℝ, ρ x = 1 := by
    change (∫ x : ℝ, (b.normed volume x : ℂ)) = 1
    rw [integral_complex_ofReal, b.integral_normed, Complex.ofReal_one]
  have hρzero (x : ℝ) (hx : x ∉ Icc (-R) R) : ρ x = 0 := by
    have hd : 2 ≤ dist x 0 := by
      simp only [dist_zero_right, Real.norm_eq_abs]
      simp only [mem_Icc, not_and_or, not_le] at hx
      have hle : 2 ≤ R := le_max_right _ _
      rcases hx with hx | hx
      · exact le_trans hle (le_trans (by linarith : R ≤ -x) (neg_le_abs x))
      · exact le_trans hle (le_trans hx.le (le_abs_self x))
    simp [ρ, ContDiffBump.normed, b.zero_of_le_dist hd]
  let m : ℝ → ℂ := fun y => ∫ t : ℝ, F (t,y)
  have hm : ContDiff ℝ (⊤ : ℕ∞) m := smooth_fiber_integral F hF R
    (fun x y hx => hzero x y (Or.inl hx))
  have hmzero (y : ℝ) (hy : y ∉ Icc (-R) R) : m y = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with t
    exact hzero t y (Or.inr hy)
  have hmc : HasCompactSupport m := HasCompactSupport.intro isCompact_Icc hmzero
  have hFi : Integrable F (volume.prod volume) :=
    hF.continuous.integrable_of_hasCompactSupport hFc
  have hmint : ∫ y : ℝ, m y = 0 := by
    rw [← integral_prod_symm F hFi]
    have heq := Complex.volume_preserving_equiv_real_prod.integral_comp' F
    have heq' : (∫ z : ℂ, φ z ∂euclideanArea) = ∫ p : ℝ × ℝ, F p := by
      simpa [F, euclideanArea, Complex.equivRealProdCLM_symm_apply] using heq
    exact heq'.symm.trans hφ
  let mt : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ) := ⟨m, hm, hmc, subset_univ _⟩
  obtain ⟨k, hk⟩ := mean_zero_real_test_has_primitive mt hmint
  let A : ℝ × ℝ → ℂ := fun p => F p - ρ p.1 * m p.2
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := hF.sub
    ((hρ.comp contDiff_fst).mul (hm.comp contDiff_snd))
  have hAzero (x y : ℝ) (h : x ∉ Icc (-R) R ∨ y ∉ Icc (-R) R) : A (x,y) = 0 := by
    dsimp [A]
    rw [hzero x y h]
    rcases h with hx | hy
    · rw [hρzero x hx]; simp
    · rw [hmzero y hy]; simp
  have hAmean (y : ℝ) : ∫ t : ℝ, A (t,y) = 0 := by
    have hslice : HasCompactSupport (fun t : ℝ => F (t,y)) :=
      HasCompactSupport.intro isCompact_Icc (fun t ht => hzero t y (Or.inl ht))
    have hcont : Continuous (fun t : ℝ => F (t,y)) :=
      hF.continuous.comp (continuous_id.prodMk continuous_const)
    have hi : Integrable (fun t : ℝ => ρ t * m y) :=
      (hρ.continuous.integrable_of_hasCompactSupport hρc).mul_const _
    dsimp [A]
    rw [integral_sub (hcont.integrable_of_hasCompactSupport hslice) hi,
      integral_mul_const, hρint, one_mul]
    exact sub_self _
  obtain ⟨g, hg⟩ := horizontal_mean_zero_has_primitive A hA R hAzero hAmean
  let H : ℝ × ℝ → ℂ := fun p => ρ p.1 * k p.2
  have hH : ContDiff ℝ (⊤ : ℕ∞) H :=
    (hρ.comp contDiff_fst).mul (k.contDiff.comp contDiff_snd)
  have hHc : HasCompactSupport H := by
    apply HasCompactSupport.intro (hρc.prod k.hasCompactSupport)
    intro p hp
    simp only [mem_prod, not_and_or] at hp
    dsimp [H]
    rcases hp with hp | hp
    · rw [image_eq_zero_of_notMem_tsupport hp, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport hp, mul_zero]
  let h : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ) :=
    ⟨H ∘ Complex.equivRealProdCLM, hH.comp Complex.equivRealProdCLM.contDiff,
      hHc.comp_homeomorph Complex.equivRealProdCLM.toHomeomorph, subset_univ _⟩
  refine ⟨g, h, ?_⟩
  ext z
  change φ z = ((TestFunction.lineDerivCLM ℂ 1) g) z +
    ((TestFunction.lineDerivCLM ℂ Complex.I) h) z
  rw [hg]
  have hh : (TestFunction.lineDerivCLM ℂ Complex.I h :
      𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)) z = ρ z.re * m z.im := by
    rw [TestFunction.lineDerivCLM_apply_of_le (by simp), lineDeriv]
    have heq : (fun t : ℝ => h (z + t • Complex.I)) =
        (fun t : ℝ => ρ z.re * k (z.im + t)) := by
      funext t
      change ρ (z + t • Complex.I).re * k (z + t • Complex.I).im = _
      simp
    rw [heq]
    have hd := ((k.contDiff.differentiable (by simp) z.im).hasDerivAt)
    rw [hk] at hd
    have hd0 : HasDerivAt (k : ℝ → ℂ) (mt z.im) (z.im + id 0) := by
      simpa using hd
    have hd' := hd0.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_add z.im)
    simpa [Function.comp_def, mt] using (hd'.const_mul (ρ z.re)).deriv
  rw [hh]
  change φ z = F (z.re,z.im) - ρ z.re * m z.im + ρ z.re * m z.im
  simp [F, Complex.equivRealProdCLM_symm_apply]

end DedekindZetaZeroFree.KPCplxOpenCellTranslationInvariance

end

section

namespace DedekindZetaZeroFree.KPCplxOpenCellTranslationInvariance

open KPCplxCharacterHaar MeasureTheory
open scoped Distributions

theorem exists_integral_one_test :
    ∃ ρ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ),
      ∫ x : ℂ, ρ x ∂euclideanArea = 1 := by
  haveI : euclideanArea.IsAddHaarMeasure := by
    unfold euclideanArea
    infer_instance
  haveI : euclideanArea.IsOpenPosMeasure := by
    unfold euclideanArea
    infer_instance
  let f : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hg : ∫ x : ℂ, f.normed euclideanArea x ∂euclideanArea = 1 := f.integral_normed
  let ρ0 : ℂ → ℂ := fun x => (f.normed euclideanArea x : ℂ)
  have hcd : ContDiff ℝ (⊤ : ℕ∞) ρ0 := Complex.ofRealCLM.contDiff.comp f.contDiff_normed
  have hcs : HasCompactSupport ρ0 :=
    HasCompactSupport.comp_left f.hasCompactSupport_normed Complex.ofReal_zero
  refine ⟨⟨ρ0, hcd, hcs, Set.subset_univ _⟩, ?_⟩
  change ∫ x : ℂ, (f.normed euclideanArea x : ℂ) ∂euclideanArea = 1
  rw [integral_complex_ofReal, hg, Complex.ofReal_one]

end DedekindZetaZeroFree.KPCplxOpenCellTranslationInvariance

end

section

namespace DedekindZetaZeroFree.KPCplxOpenCellTranslationInvariance

open KPCplxPrincipalSeriesCharts Set Filter TopologicalSpace
open scoped Distributions Topology ContDiff

private theorem compact_derivative_bound (f : ℂ → ℂ) (U A : Set ℂ)
    (hU : IsOpen U) (hA : IsCompact A) (hAU : A ⊆ U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i ≤ n, ∀ x ∈ A, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  have hc : ContinuousOn (fun x => ∑ i ∈ Finset.range (n+1),
      ‖iteratedFDeriv ℝ i f x‖) A := by
    apply continuousOn_finset_sum
    intro i hi
    exact ((ContinuousOn.continuousOn_iteratedFDeriv hf hU (by simp)).norm).mono hAU
  obtain ⟨C, hC⟩ := hA.exists_bound_of_continuousOn hc
  refine ⟨max 1 C, le_max_left _ _, fun i hi x hx => ?_⟩
  calc
    ‖iteratedFDeriv ℝ i f x‖ ≤ ∑ j ∈ Finset.range (n+1), ‖iteratedFDeriv ℝ j f x‖ :=
      Finset.single_le_sum (fun j hj => norm_nonneg (iteratedFDeriv ℝ j f x)) (show i ∈ Finset.range (n+1) from Finset.mem_range.mpr (by omega))
    _ ≤ C := (Real.le_norm_self _).trans (hC x hx)
    _ ≤ max 1 C := le_max_right _ _

private theorem infinity_zero_near (s : ℝ)
    (E : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ) →ₗ[ℂ] PrincipalSeries s)
    (hE : ∀ φ, openCoordinate (E φ) = φ)
    (K : Compacts ℂ) (R : ℝ) (hR : 0 < R)
    (hK : (K : Set ℂ) ⊆ Metric.ball 0 R)
    (φ : 𝓓_{K}(ℂ, ℂ)) :
    ∀ u, ‖u‖ < R⁻¹ → infinityCoordinate (E (TestFunction.ofSupportedIn (show (K : Set ℂ) ⊆ ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) from Set.subset_univ _) φ)) u = 0 := by
  let ψ := TestFunction.ofSupportedIn (show (K : Set ℂ) ⊆ ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) from Set.subset_univ _) φ
  have hz : ∀ u, u ≠ 0 → ‖u‖ < R⁻¹ → infinityCoordinate (E ψ) u = 0 := by
    intro u hu hnorm
    rw [coordinate_transition s (E ψ) u hu, hE]
    have hnot : u⁻¹ ∉ (K : Set ℂ) := by
      intro hin
      have hb : ‖u⁻¹‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hK hin
      rw [norm_inv] at hb
      have := (lt_inv_comm₀ (norm_pos_iff.mpr hu) hR).mp hnorm
      linarith
    change (transitionWeight s u : ℂ) * φ u⁻¹ = 0
    simp [φ.zero_on_compl hnot]
  intro u hu
  by_cases h : u = 0
  · subst u
    have heq : infinityCoordinate (E ψ) =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => (0 : ℂ) := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) (inv_pos.mpr hR))] with u hu huR
      exact hz u (by simpa using hu) (by simpa [Metric.mem_ball, dist_zero_right] using huR)
    exact tendsto_nhds_unique ((E ψ).2.2.2.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (Filter.Tendsto.congr' heq.symm tendsto_const_nhds)
  · exact hz u h hu

private theorem weighted_comp_bound (s : ℝ) (K : Compacts ℂ) (r : ℝ) (hr : 0 < r)
    (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : 𝓓_{K}(ℂ, ℂ), ∀ u : ℂ,
      u ∈ Metric.closedBall 0 1 → r ≤ ‖u‖ →
      ‖iteratedFDeriv ℝ n (fun v => (transitionWeight s v : ℂ) * φ v⁻¹) u‖ ≤
        C * (ContDiffMapSupportedIn.supSeminorm ℂ ℂ ℂ ⊤ K n) φ := by
  let U : Set ℂ := {0}ᶜ
  let A : Set ℂ := Metric.closedBall 0 1 ∩ {u : ℂ | r ≤ ‖u‖}
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  have hA : IsCompact A := (isCompact_closedBall (0 : ℂ) 1).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hAU : A ⊆ U := by
    intro u hu
    have : u ≠ 0 := by
      intro h
      have ht := hu.2
      simp only [Set.mem_setOf_eq, h, norm_zero] at ht
      linarith
    simpa [U] using this
  have hw : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : ℂ => (transitionWeight s v : ℂ)) U := by
    intro u hu
    have hu0 : u ≠ 0 := by simpa [U] using hu
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp u
      ((contDiffAt_norm ℂ hu0).rpow_const_of_ne (norm_ne_zero_iff.mpr hu0))).contDiffWithinAt
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : ℂ => v⁻¹) U := by
    intro u hu
    exact (contDiffAt_inv ℝ (by simpa [U] using hu)).contDiffWithinAt
  obtain ⟨B, hB, hb⟩ := compact_derivative_bound _ U A hU hA hAU hw n
  obtain ⟨D, hD, hd⟩ := compact_derivative_bound _ U A hU hA hAU hv n
  refine ⟨∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * B * ((n-i).factorial * D ^ (n-i)),
    by positivity, fun φ u hu hur => ?_⟩
  have huA : u ∈ A := ⟨hu, hur⟩
  have huU := hAU huA
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) ((φ : ℂ → ℂ) ∘ (fun v : ℂ => v⁻¹)) U :=
    φ.contDiff.comp_contDiffOn hv
  have hn : (n : ℕ∞ω) ≤ (⊤ : ℕ∞) := by simp
  have heq (i : ℕ) (f : ℂ → ℂ) :
      iteratedFDerivWithin ℝ i f U u = iteratedFDeriv ℝ i f u :=
    iteratedFDerivWithin_of_isOpen i hU huU
  calc
    ‖iteratedFDeriv ℝ n (fun v => (transitionWeight s v : ℂ) * φ v⁻¹) u‖
      ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun v : ℂ => (transitionWeight s v : ℂ)) u‖ *
        ‖iteratedFDeriv ℝ (n-i) ((φ : ℂ → ℂ) ∘ (fun v : ℂ => v⁻¹)) u‖ := by
          simpa only [heq, Function.comp_apply] using norm_iteratedFDerivWithin_mul_le hw hφ
            hU.uniqueDiffOn huU hn
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * B *
        (((n-i).factorial : ℝ) * ((ContDiffMapSupportedIn.supSeminorm ℂ ℂ ℂ ⊤ K n) φ) * D^(n-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := by simpa using Finset.mem_range_succ_iff.mp hi
      have hc : ‖iteratedFDeriv ℝ (n-i) ((φ : ℂ → ℂ) ∘ (fun v : ℂ => v⁻¹)) u‖ ≤
          (n-i).factorial * ((ContDiffMapSupportedIn.supSeminorm ℂ ℂ ℂ ⊤ K n) φ) * D ^ (n-i) := by
        have h := norm_iteratedFDerivWithin_comp_le (n := n-i)
          (C := (ContDiffMapSupportedIn.supSeminorm ℂ ℂ ℂ ⊤ K n) φ) (D := D)
          φ.contDiff.contDiffOn hv (by simp)
          uniqueDiffOn_univ hU.uniqueDiffOn (mapsTo_univ _ _) huU
          (fun j hj => ?_) (fun j hj1 hj => ?_)
        · simpa only [iteratedFDerivWithin_univ, heq] using h
        · rw [iteratedFDerivWithin_univ]
          exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ).trans
            (Seminorm.le_finset_sup_apply (Finset.mem_Iic.mpr (hj.trans (Nat.sub_le _ _))))
        · rw [heq]
          exact (hd j (hj.trans (Nat.sub_le _ _)) u huA).trans (le_self_pow₀ hD (by omega))
      gcongr
      exact hb i hin u huA
    _ = _ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring

private theorem fixed_support_bound (s : ℝ)
    (E : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ) →ₗ[ℂ] PrincipalSeries s)
    (hE : ∀ φ, openCoordinate (E φ) = φ)
    (K : Compacts ℂ) (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : 𝓓_{K}(ℂ, ℂ),
      chartSeminorm s n (E (TestFunction.ofSupportedIn (Set.subset_univ _) φ)) ≤
        C * (ContDiffMapSupportedIn.supSeminorm ℂ ℂ ℂ ⊤ K n) φ := by
  obtain ⟨R, hR, hK⟩ := K.isCompact.isBounded.subset_ball_lt 0 (0 : ℂ)
  obtain ⟨C, hC, hb⟩ := weighted_comp_bound s K R⁻¹ (inv_pos.mpr hR) n
  refine ⟨max 1 C, le_trans zero_le_one (le_max_left _ _), fun φ => ?_⟩
  let ψ := TestFunction.ofSupportedIn (show (K : Set ℂ) ⊆ ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) from Set.subset_univ _) φ
  let P := (ContDiffMapSupportedIn.supSeminorm ℂ ℂ ℂ ⊤ K n) φ
  have hP : 0 ≤ P := apply_nonneg _ φ
  have hopen : ∀ x : ℂ, ‖iteratedFDeriv ℝ n (openCoordinate (E ψ)) x‖ ≤ max 1 C * P := by
    intro x
    rw [hE]
    change ‖iteratedFDeriv ℝ n φ x‖ ≤ max 1 C * P
    calc
      _ ≤ P := (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ).trans
        (Seminorm.le_finset_sup_apply (Finset.mem_Iic.mpr le_rfl))
      _ = 1 * P := (one_mul P).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hP
  have hinf : ∀ u ∈ Metric.closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ n (infinityCoordinate (E ψ)) u‖ ≤ max 1 C * P := by
    intro u hu
    by_cases hur : ‖u‖ < R⁻¹
    · have hz := infinity_zero_near s E hE K R hR hK φ
      have heq : infinityCoordinate (E ψ) =ᶠ[𝓝 u] fun _ => (0 : ℂ) := by
        filter_upwards [((isOpen_lt continuous_norm continuous_const).mem_nhds hur)] with v hv
        exact hz v hv
      rw [(heq.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hP
    · have hu0 : u ≠ 0 := by intro h; simp [h] at hur; linarith [inv_pos.mpr hR]
      have heq : infinityCoordinate (E ψ) =ᶠ[𝓝 u]
          fun v => (transitionWeight s v : ℂ) * φ v⁻¹ := by
        filter_upwards [eventually_ne_nhds hu0] with v hv
        rw [coordinate_transition s (E ψ) v hv, hE]
        rfl
      rw [(heq.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds]
      exact (hb φ u hu (le_of_not_gt hur)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hP)
  change max (sSup _) (sSup _) ≤ max 1 C * P
  apply max_le
  · apply csSup_le
    · exact (Metric.nonempty_closedBall.mpr zero_le_one).image _
    · rintro _ ⟨x, hx, rfl⟩; exact hopen x
  · apply csSup_le
    · exact (Metric.nonempty_closedBall.mpr zero_le_one).image _
    · rintro _ ⟨u, hu, rfl⟩; exact hinf u hu

theorem affine_extension_continuous (s : ℝ)
    (E : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ) →ₗ[ℂ] PrincipalSeries s)
    (hE : ∀ φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ),
      openCoordinate (E φ) = φ) :
    Continuous E := by
  have hs : WithSeminorms (chartSeminorm s) := ⟨rfl⟩
  letI : ContinuousSMul ℂ (PrincipalSeries s) := hs.continuousSMul
  letI : ContinuousSMul ℝ (PrincipalSeries s) := IsScalarTower.continuousSMul ℂ
  letI : LocallyConvexSpace ℝ (PrincipalSeries s) := principalSeries_locallyConvex s
  rw [TestFunction.continuous_iff_continuous_comp]
  intro K hK
  let F := E.comp (TestFunction.ofSupportedInCLM ℂ hK).toLinearMap
  apply hs.continuous_of_continuous_comp F
  intro n
  obtain ⟨C, hC, hb⟩ := fixed_support_bound s E hE K n
  apply Seminorm.continuous_of_le (q := C.toNNReal • ContDiffMapSupportedIn.supSeminorm ℂ ℂ ℂ ⊤ K n)
    ((ContDiffMapSupportedIn.withSeminorms' ℂ ℂ ℂ ⊤ K).continuous_seminorm n |>.const_smul C.toNNReal)
  intro φ
  simp only [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal C hC]
  change chartSeminorm s n (E (TestFunction.ofSupportedIn hK φ)) ≤ _
  exact hb φ

end DedekindZetaZeroFree.KPCplxOpenCellTranslationInvariance

end

section

namespace DedekindZetaZeroFree.KPCplxOpenCellDistributions

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxJacquetFunctional
  KPCplxClosedCellJets MeasureTheory
open scoped Distributions ContDiff Topology

abbrev OpenCellTestFunction := 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)

noncomputable def translateTestFunction (t : ℂ)
    (φ : OpenCellTestFunction) : OpenCellTestFunction where
  toFun x := φ (x + t)
  contDiff' := φ.contDiff.comp (contDiff_id.add contDiff_const)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight t)
  tsupport_subset' := by simp

@[simp] theorem translateTestFunction_apply (t x : ℂ) (φ : OpenCellTestFunction) :
    translateTestFunction t φ x = φ (x + t) := rfl

theorem supportedAwayInfinity_iff_hasCompactSupport (s : ℝ) (f : PrincipalSeries s) :
    SupportedAwayInfinity s f ↔ HasCompactSupport (openCoordinate f) := by
  constructor
  · rintro ⟨ε, hε, hf⟩
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ε⁻¹)
    intro x hx
    have hnorm : ε⁻¹ < ‖x‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hx0 : x ≠ 0 := by
      intro h
      have : ε⁻¹ < 0 := by simpa only [h, norm_zero] using hnorm
      exact (not_lt_of_ge (le_of_lt (inv_pos.mpr hε))) this
    have hinv : ‖x⁻¹‖ < ε := by
      rw [norm_inv]
      exact (inv_lt_comm₀ (norm_pos_iff.mpr hx0) hε).mpr hnorm
    have hweight : (transitionWeight s x⁻¹ : ℂ) ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      exact (Real.rpow_pos_of_pos (norm_pos_iff.mpr (inv_ne_zero hx0)) _).ne'
    have h := hf x⁻¹ hinv
    rw [coordinate_transition s f x⁻¹ (inv_ne_zero hx0), inv_inv] at h
    exact (mul_eq_zero.mp h).resolve_left hweight
  · intro hf
    obtain ⟨R, hR, hbound⟩ := hf.exists_pos_le_norm
    have hz : ∀ u : ℂ, u ≠ 0 → ‖u‖ < R⁻¹ → infinityCoordinate f u = 0 := by
      intro u hu hnorm
      rw [coordinate_transition s f u hu, hbound u⁻¹, mul_zero]
      rw [norm_inv]
      exact le_of_lt ((lt_inv_comm₀ (norm_pos_iff.mpr hu) hR).mp hnorm)
    refine ⟨R⁻¹, inv_pos.mpr hR, fun u hu => ?_⟩
    by_cases hu0 : u = 0
    · subst u
      have heq : infinityCoordinate f =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => (0 : ℂ) := by
        filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) (inv_pos.mpr hR))] with u hu huR
        exact hz u (by simpa using hu) (by simpa [Metric.mem_ball, dist_zero_right] using huR)
      exact tendsto_nhds_unique (f.2.2.2.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (Filter.Tendsto.congr' heq.symm tendsto_const_nhds)
    · exact hz u hu0 hu

theorem testFunction_extendsSmoothly (s : ℝ) (φ : OpenCellTestFunction) :
    ExtendsSmoothly s φ := by
  obtain ⟨R, hR, hbound⟩ := φ.hasCompactSupport.exists_pos_le_norm
  let H : ℂ → ℂ := fun u => if u = 0 then 0 else (transitionWeight s u : ℂ) * φ u⁻¹
  have hzero : ∀ u : ℂ, ‖u‖ < R⁻¹ → H u = 0 := by
    intro u hu
    by_cases hu0 : u = 0
    · subst u
      simp [H, transitionWeight]
    · simp only [H, if_neg hu0]
      rw [hbound u⁻¹, mul_zero]
      rw [norm_inv]
      exact le_of_lt ((lt_inv_comm₀ (norm_pos_iff.mpr hu0) hR).mp hu)
  refine ⟨φ.contDiff, H, contDiff_iff_contDiffAt.mpr (fun u => ?_),
    fun u hu => by simp only [H, if_neg hu]⟩
  by_cases hu : u = 0
  · subst u
    apply contDiffAt_const.congr_of_eventuallyEq
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨R⁻¹, inv_pos.mpr hR, fun u hu => ?_⟩
    exact hzero u (by simpa only [dist_zero_right] using hu)
  · have hw : ContDiffAt ℝ ∞ (fun u : ℂ => (transitionWeight s u : ℂ)) u := by
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp u
        ((contDiffAt_norm ℂ hu).rpow_const_of_ne (norm_ne_zero_iff.mpr hu))
    apply (hw.mul (φ.contDiff.contDiffAt.comp u (contDiffAt_inv ℝ hu))).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hu] with v hv
    simp only [H, if_neg hv, Function.comp_apply]

noncomputable def testFunctionSection (s : ℝ) (φ : OpenCellTestFunction) : PrincipalSeries s :=
  Classical.choose ((openCoordinate_range s φ).mpr (testFunction_extendsSmoothly s φ))

@[simp] theorem testFunctionSection_coordinate (s : ℝ) (φ : OpenCellTestFunction) :
    openCoordinate (testFunctionSection s φ) = φ :=
  Classical.choose_spec ((openCoordinate_range s φ).mpr (testFunction_extendsSmoothly s φ))

noncomputable def testFunctionSectionLinear (s : ℝ) :
    OpenCellTestFunction →ₗ[ℂ] PrincipalSeries s where
  toFun := testFunctionSection s
  map_add' φ χ := by
    apply openCoordinate_injective s
    funext x
    change openCoordinate (testFunctionSection s (φ + χ)) x =
      openCoordinate (testFunctionSection s φ) x + openCoordinate (testFunctionSection s χ) x
    simp only [testFunctionSection_coordinate]
    rfl
  map_smul' c φ := by
    apply openCoordinate_injective s
    funext x
    change openCoordinate (testFunctionSection s (c • φ)) x =
      c * openCoordinate (testFunctionSection s φ) x
    simp only [testFunctionSection_coordinate]
    rfl

private theorem upperUnipotent_add (x t : ℂ) :
    upperUnipotent x * upperUnipotent t = upperUnipotent (x + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent] <;> ring

theorem testFunctionSection_translate (s : ℝ) (t : ℂ) (φ : OpenCellTestFunction) :
    testFunctionSection s (translateTestFunction t φ) =
      pi s (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) (testFunctionSection s φ) := by
  apply openCoordinate_injective s
  funext x
  change openCoordinate (testFunctionSection s (translateTestFunction t φ)) x =
    testFunctionSection s φ ((weyl * upperUnipotent x) * upperUnipotent t)
  rw [testFunctionSection_coordinate]
  change φ (x + t) = testFunctionSection s φ ((weyl * upperUnipotent x) * upperUnipotent t)
  rw [mul_assoc, upperUnipotent_add]
  exact (congrFun (testFunctionSection_coordinate s φ) (x + t)).symm

theorem translation_invariant_distribution (D : OpenCellTestFunction →L[ℂ] ℂ)
    (hD : ∀ (t : ℂ) (φ : OpenCellTestFunction), D (translateTestFunction t φ) = D φ) :
    ∃ a : ℂ, ∀ φ : OpenCellTestFunction,
      D φ = a * ∫ x : ℂ, φ x ∂euclideanArea := by
  have hpoint : ∀ (t : ℂ) (φ χ : OpenCellTestFunction),
      (∀ x : ℂ, χ x = φ (x + t)) → D χ = D φ := by
    intro t φ χ hχ
    have heq : χ = translateTestFunction t φ := by
      apply TestFunction.ext
      intro x
      exact hχ x
    rw [heq]
    exact hD t φ
  obtain ⟨ρ, hρ⟩ := KPCplxOpenCellTranslationInvariance.exists_integral_one_test
  refine ⟨D ρ, fun φ => ?_⟩
  have hintφ : Integrable (fun x : ℂ => φ x) euclideanArea := by
    change Integrable (fun x : ℂ => φ x) (volume : Measure ℂ)
    exact φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hintρ : Integrable (fun x : ℂ => ρ x) euclideanArea := by
    change Integrable (fun x : ℂ => ρ x) (volume : Measure ℂ)
    exact ρ.contDiff.continuous.integrable_of_hasCompactSupport ρ.hasCompactSupport
  let ψ : OpenCellTestFunction := φ - (∫ x : ℂ, φ x ∂euclideanArea) • ρ
  have hzero : ∫ x : ℂ, ψ x ∂euclideanArea = 0 := by
    change ∫ x : ℂ, (φ x - (∫ x : ℂ, φ x ∂euclideanArea) * ρ x) ∂euclideanArea = 0
    rw [integral_sub hintφ (hintρ.const_mul _), integral_const_mul, hρ]
    ring
  obtain ⟨g, h, hψ⟩ := KPCplxOpenCellTranslationInvariance.mean_zero_is_divergence ψ hzero
  have hDψ : D ψ = 0 := by
    rw [hψ, map_add,
      KPCplxOpenCellTranslationInvariance.invariant_annihilates_directional_derivatives
        D hpoint (1 : ℂ) g,
      KPCplxOpenCellTranslationInvariance.invariant_annihilates_directional_derivatives
        D hpoint Complex.I h, add_zero]
  have hψD : D ψ = D φ - (∫ x : ℂ, φ x ∂euclideanArea) * D ρ := by
    change D (φ - (∫ x : ℂ, φ x ∂euclideanArea) • ρ) = _
    rw [map_sub, map_smul]
    rfl
  rw [hψD] at hDψ
  simpa only [mul_comm] using sub_eq_zero.mp hDψ

private theorem character_contDiff (β : ℂ) :
    ContDiff ℝ ∞ (fun x : ℂ => (character β x : ℂ)) := by
  simp only [character, AddChar.coe_mk, Circle.coe_exp]
  exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
    (Complex.reCLM.contDiff.comp (contDiff_const.mul contDiff_id))).mul contDiff_const)

theorem equivariant_test_distribution (β : ℂˣ)
    (D : OpenCellTestFunction →L[ℂ] ℂ)
    (hD : ∀ (t : ℂ) (φ : OpenCellTestFunction),
      D (translateTestFunction t φ) = (character (β : ℂ) t : ℂ) * D φ) :
    ∃ a : ℂ, ∀ φ : OpenCellTestFunction,
      D φ = a * ∫ x : ℂ, φ x * (character (β : ℂ) (-x) : ℂ) ∂characterHaar β := by
  let M : OpenCellTestFunction →L[ℂ] OpenCellTestFunction :=
    TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (character_contDiff (β : ℂ))
  have hM (φ : OpenCellTestFunction) (x : ℂ) : M φ x = φ x * (character (β : ℂ) x : ℂ) := rfl
  have hcancel (x : ℂ) : (character (β : ℂ) (-x) : ℂ) * (character (β : ℂ) x : ℂ) = 1 := by
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
  have htrans (t : ℂ) (φ : OpenCellTestFunction) :
      M (translateTestFunction t φ) =
        (character (β : ℂ) (-t) : ℂ) • translateTestFunction t (M φ) := by
    apply TestFunction.ext
    intro x
    change φ (x + t) * (character (β : ℂ) x : ℂ) =
      (character (β : ℂ) (-t) : ℂ) * (φ (x + t) * (character (β : ℂ) (x + t) : ℂ))
    rw [AddChar.map_add_eq_mul, Circle.coe_mul]
    calc
      _ = φ (x + t) * (character (β : ℂ) x : ℂ) *
        ((character (β : ℂ) (-t) : ℂ) * (character (β : ℂ) t : ℂ)) := by rw [hcancel, mul_one]
      _ = _ := by ring
  obtain ⟨a, ha⟩ := translation_invariant_distribution (D.comp M) (by
    intro t φ
    change D (M (translateTestFunction t φ)) = D (M φ)
    rw [htrans, map_smul, hD]
    change (character (β : ℂ) (-t) : ℂ) * ((character (β : ℂ) t : ℂ) * D (M φ)) = _
    rw [← mul_assoc, hcancel, one_mul])
  let N : OpenCellTestFunction →L[ℂ] OpenCellTestFunction :=
    TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
      ((character_contDiff (β : ℂ)).comp contDiff_neg)
  have hN (φ : OpenCellTestFunction) (x : ℂ) : N φ x = φ x * (character (β : ℂ) (-x) : ℂ) := rfl
  have hMN (φ : OpenCellTestFunction) : M (N φ) = φ := by
    apply TestFunction.ext
    intro x
    rw [hM, hN, mul_assoc, hcancel, mul_one]
  have hscalePos : 0 < characterScale β / (2 * Real.pi) :=
    div_pos (characterScale_pos β) (mul_pos (by norm_num) Real.pi_pos)
  have hscale : ((characterScale β / (2 * Real.pi) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hscalePos.ne'
  refine ⟨a / ((characterScale β / (2 * Real.pi) : ℝ) : ℂ), fun φ => ?_⟩
  have h := ha (N φ)
  change D (M (N φ)) = a * ∫ x : ℂ, N φ x ∂euclideanArea at h
  rw [hMN] at h
  rw [h]
  simp only [characterHaar, integral_smul_measure, ENNReal.toReal_ofReal hscalePos.le,
    hN, Complex.real_smul]
  field_simp

theorem equivariant_functional_open_cell (β : ℂˣ)
    (L : PrincipalSeries positiveParameter →L[ℂ] ℂ)
    (hL : IsEigenDistribution positiveParameter (character (β : ℂ)) L) :
    ∃ a : ℂ,
      (∀ f : PrincipalSeries positiveParameter,
        SupportedAwayInfinity positiveParameter f →
          L f = a * jacquetFunctional β f) ∧
      SupportedAtInfinity positiveParameter (L - a • jacquetFunctional β) := by
  let E : OpenCellTestFunction →L[ℂ] PrincipalSeries positiveParameter :=
    ⟨testFunctionSectionLinear positiveParameter,
      KPCplxOpenCellTranslationInvariance.affine_extension_continuous positiveParameter
        (testFunctionSectionLinear positiveParameter)
        (testFunctionSection_coordinate positiveParameter)⟩
  have hE (φ : OpenCellTestFunction) : E φ = testFunctionSection positiveParameter φ := rfl
  obtain ⟨a, ha⟩ := equivariant_test_distribution β (L.comp E) (by
    intro t φ
    change L (E (translateTestFunction t φ)) = (character (β : ℂ) t : ℂ) * L (E φ)
    rw [hE, hE, testFunctionSection_translate]
    exact hL t (testFunctionSection positiveParameter φ))
  have hprescribed : ∀ f : PrincipalSeries positiveParameter,
      SupportedAwayInfinity positiveParameter f → L f = a * jacquetFunctional β f := by
    intro f hf
    let φ : OpenCellTestFunction :=
      { toFun := openCoordinate f
        contDiff' := f.2.2.1
        hasCompactSupport' :=
          (supportedAwayInfinity_iff_hasCompactSupport positiveParameter f).mp hf
        tsupport_subset' := by simp }
    have heq : E φ = f := by
      apply openCoordinate_injective positiveParameter
      change openCoordinate (E φ) = openCoordinate f
      rw [hE, testFunctionSection_coordinate]
      rfl
    have h := ha φ
    change L (E φ) = a * ∫ x : ℂ, φ x * (character (β : ℂ) (-x) : ℂ)
      ∂characterHaar β at h
    rw [heq] at h
    exact h
  refine ⟨a, hprescribed, ?_⟩
  intro f hf
  change L f - a * jacquetFunctional β f = 0
  rw [hprescribed f hf, sub_self]

end DedekindZetaZeroFree.KPCplxOpenCellDistributions

end
