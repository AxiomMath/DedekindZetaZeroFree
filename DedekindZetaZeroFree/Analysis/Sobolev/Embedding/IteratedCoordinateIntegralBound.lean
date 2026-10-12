module

public import DedekindZetaZeroFree.Analysis.SmoothFunctions.CompactOpenHolomorphyAndMeromorphy

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPLocalCubeSobolevJets

open MeasureTheory KPContLocalNorm
open scoped ENNReal

private theorem smooth_list {n : ℕ} (g : Space n → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (l : List (Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivativeList l g) := by
  induction l with
  | nil => exact hg
  | cons i l ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const
private theorem support_list {n : ℕ} (g : Space n → ℂ)
    (hg : HasCompactSupport g) (l : List (Fin n)) :
    HasCompactSupport (coordinateDerivativeList l g) := by
  induction l with
  | nil => exact hg
  | cons i l ih => exact ih.fderiv_apply ℝ _
private theorem line_bound {n : ℕ} (g : Space n → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hs : HasCompactSupport g)
    (i : Fin n) (x : Fin n → ℝ) :
    ‖g ((EuclideanSpace.equiv (Fin n) ℝ).symm x)‖ₑ ≤
      ∫⁻ t, ‖coordinateDerivativeList [i] g
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (Function.update x i t))‖ₑ := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  let a : ℝ → Space n := fun t => e (Function.update x i t)
  have ha : ContDiff ℝ (⊤ : ℕ∞) a := e.contDiff.comp (contDiff_update _ x i)
  have hs' : HasCompactSupport (g ∘ a) :=
    hs.comp_isClosedEmbedding (e.toHomeomorph.isClosedEmbedding.comp (isClosedEmbedding_update x i))
  have hda (t : ℝ) : HasDerivAt a (EuclideanSpace.single i 1) t := by
    have he : (e : (Fin n → ℝ) → Space n) ∘ Function.update x i = a := rfl
    rw [← he]
    convert e.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update x i t) using 1
    simpa [e] using (EuclideanSpace.toLp_single i (1 : ℝ)).symm
  have heq (t : ℝ) : deriv (g ∘ a) t =
      coordinateDerivativeList [i] g (a t) := by
    exact ((hg.differentiable (by simp) (a t)).hasFDerivAt.comp_hasDerivAt t (hda t)).deriv
  have hb := HasCompactSupport.enorm_le_lintegral_Ici_deriv
    ((hg.comp ha).of_le (by simp)) hs' (x i)
  have hx : a (x i) = e x := by simp [a]
  rw [Function.comp_apply, hx] at hb
  exact hb.trans ((lintegral_mono' Measure.restrict_le_self
    (fun t => le_of_eq (congrArg (fun z : ℂ => ‖z‖ₑ) (heq t)))))
private theorem marginal_bound {n : ℕ} (l : List (Fin n)) (hl : l.Nodup)
    (g : Space n → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hs : HasCompactSupport g) (x : Fin n → ℝ) :
    ‖g ((EuclideanSpace.equiv (Fin n) ℝ).symm x)‖ₑ ≤
      (∫⋯∫⁻_l.toFinset,
        (fun y : Fin n → ℝ => ‖coordinateDerivativeList l g
          ((EuclideanSpace.equiv (Fin n) ℝ).symm y)‖ₑ)) x := by
  induction l generalizing g x with
  | nil =>
      simp [coordinateDerivativeList]
  | cons i l ih =>
      have hi : i ∉ l.toFinset := by simpa using (List.nodup_cons.mp hl).1
      have hl' : l.Nodup := hl.tail
      have h0 := ih hl' g hg hs x
      let f : (Fin n → ℝ) → ℝ≥0∞ := fun y =>
        ‖coordinateDerivativeList (i :: l) g
          ((EuclideanSpace.equiv (Fin n) ℝ).symm y)‖ₑ
      have hf : Measurable f := by
        exact ((smooth_list g hg (i :: l)).continuous.comp
          (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous).enorm.measurable
      have h1 :
        (∫⋯∫⁻_l.toFinset, (fun y : Fin n → ℝ =>
          ‖coordinateDerivativeList l g
            ((EuclideanSpace.equiv (Fin n) ℝ).symm y)‖ₑ)) x ≤
        (∫⋯∫⁻_l.toFinset, (fun y : Fin n → ℝ =>
          ∫⁻ t, f (Function.update y i t))) x := by
        apply lmarginal_mono
        intro y
        simpa only [f, coordinateDerivativeList] using
          line_bound (coordinateDerivativeList l g) (smooth_list g hg l)
            (support_list g hs l) i y
      have h2 := lmarginal_insert' (μ := fun _ : Fin n => (volume : Measure ℝ)) f hf hi
      simpa only [List.toFinset_cons, f] using h0.trans (h1.trans_eq (congrFun h2 x).symm)
theorem norm_le_integral_full_mixed_derivative {n : ℕ} (hn : 0 < n)
    (g : Space n → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hsupp : HasCompactSupport g) (x : Space n) :
    ‖g x‖ ≤ ∫ y, ‖coordinateDerivativeList (List.finRange n) g y‖ := by
  let f := coordinateDerivativeList (List.finRange n) g
  have hf : Integrable f :=
    (smooth_list g hg _).continuous.integrable_of_hasCompactSupport
      (support_list g hsupp _)
  have hb := marginal_bound (List.finRange n) (List.nodup_finRange n) g hg hsupp
    ((EuclideanSpace.equiv (Fin n) ℝ) x)
  have hl : (List.finRange n).toFinset = Finset.univ := by
    ext i
    simp
  rw [hl, lmarginal_univ] at hb
  have hm := (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
    (fun y => ‖f y‖ₑ)
  have hb' : ‖g x‖ₑ ≤ ∫⁻ y : Space n, ‖f y‖ₑ := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply, ← volume_pi] using hb.trans_eq hm
  have hnorm : (∫⁻ y : Space n, ‖f y‖ₑ).toReal = ∫ y : Space n, ‖f y‖ := by
    simpa only [← ofReal_norm] using
      (integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun y => norm_nonneg (f y))) hf.norm.aestronglyMeasurable).symm
  have h := ENNReal.toReal_mono hf.hasFiniteIntegral.ne hb'
  rw [hnorm] at h
  simpa only [enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm, f] using h

end DedekindZetaZeroFree.KPLocalCubeSobolevJets

end
