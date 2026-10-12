module

public import DedekindZetaZeroFree.Analysis.Sobolev.WeakDerivatives.CompactInteriorZeroExtension

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPCompactInteriorH1

open MeasureTheory Function
open scoped ContDiff Convolution Pointwise

theorem allTests_weak_derivative_mollification
    {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (C : Set (E n)) (hC : IsCompact C)
    (F : E n → V r) (G : Fin n → E n → V r)
    (hF : MemLp F 2 volume) (hG : ∀ j, MemLp (G j) 2 volume)
    (hF_zero : ∀ x, x ∉ C → F x = 0)
    (hG_zero : ∀ j x, x ∉ C → G j x = 0)
    (hweak : ∀ (j : Fin n) (ψ : E n → ℂ), ContDiff ℝ ∞ ψ →
      ∀ a : Fin r,
        (∫ x, (F x) a * coordinatePartial j ψ x ∂volume) =
          -(∫ x, (G j x) a * ψ x ∂volume))
    (φ : ContDiffBump (0 : E n)) :
    let ρ := φ.normed volume
    let u := convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume
    ContDiff ℝ ∞ u ∧
      HasCompactSupport u ∧
      tsupport u ⊆ Metric.cthickening φ.rOut C ∧
      ∀ (x : E n) (j : Fin n),
        fderiv ℝ u x (coordinateDirection j) =
          convolution ρ (G j) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  have hρ_cd : ContDiff ℝ ∞ (φ.normed volume) := φ.contDiff_normed
  have hρ_cs : HasCompactSupport (φ.normed volume) := φ.hasCompactSupport_normed
  have hρ_cont : Continuous (φ.normed volume) := hρ_cd.continuous
  have hF_li : LocallyIntegrable F volume := hF.locallyIntegrable (by norm_num)
  have hF_supp : support F ⊆ C := fun x hx => by_contra fun h => hx (hF_zero x h)
  have hF_cs : HasCompactSupport F :=
    hC.of_isClosed_subset isClosed_closure (closure_minimal hF_supp hC.isClosed)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hρ_cs.contDiff_convolution_left _ (hρ_cd.of_le (by simp)) hF_li
  · exact hρ_cs.convolution _ hF_cs
  · apply closure_minimal _ Metric.isClosed_cthickening
    intro x hx
    have hs := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hx
    rcases Set.mem_add.mp hs with ⟨a, ha, b, hb, rfl⟩
    have ha' : ‖a‖ ≤ φ.rOut := by
      rw [φ.support_normed_eq, Metric.mem_ball, dist_zero_right] at ha
      exact ha.le
    exact Metric.mem_cthickening_of_dist_le (a + b) b φ.rOut C (hF_supp hb)
      (by simpa [dist_eq_norm] using ha')
  · intro x j
    have hDρ_cont : Continuous (fderiv ℝ (φ.normed volume)) :=
      hρ_cd.continuous_fderiv (by simp)
    have hderiv : fderiv ℝ (convolution (φ.normed volume) F (ContinuousLinearMap.lsmul ℝ ℝ)
          volume) x =
        (fderiv ℝ (φ.normed volume) ⋆[ContinuousLinearMap.precompL (E n)
          (ContinuousLinearMap.lsmul ℝ ℝ), volume] F) x :=
      (hρ_cs.hasFDerivAt_convolution_left _ (hρ_cd.of_le (by simp)) hF_li x).fderiv
    rw [hderiv]
    have hi : Integrable (fun t => ContinuousLinearMap.precompL (E n)
        (ContinuousLinearMap.lsmul ℝ ℝ) (fderiv ℝ (φ.normed volume) t) (F (x - t))) volume :=
      (hρ_cs.fderiv ℝ).convolutionExists_left _ hDρ_cont hF_li x
    have key : ((fderiv ℝ (φ.normed volume) ⋆[ContinuousLinearMap.precompL (E n)
          (ContinuousLinearMap.lsmul ℝ ℝ), volume] F) x) (coordinateDirection j) =
        ((fun t => fderiv ℝ (φ.normed volume) t (coordinateDirection j))
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) x := by
      rw [convolution_def, convolution_def, ContinuousLinearMap.integral_apply hi]
      simp only [ContinuousLinearMap.precompL_apply]
    rw [key, convolution_lsmul_swap, convolution_lsmul_swap]
    have hψ_cd : ContDiff ℝ ∞ (fun y : E n => (φ.normed volume (x - y) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hρ_cd.comp (by fun_prop))
    have hcoord : ∀ y : E n,
        coordinatePartial j (fun y : E n => (φ.normed volume (x - y) : ℂ)) y =
          -(((fderiv ℝ (φ.normed volume) (x - y) (coordinateDirection j)) : ℝ) : ℂ) := by
      intro y
      have hd : Differentiable ℝ (φ.normed volume) := hρ_cd.differentiable (by simp)
      have h1 : HasFDerivAt (fun z : E n => φ.normed volume (x - z))
          ((fderiv ℝ (φ.normed volume) (x - y)).comp (-ContinuousLinearMap.id ℝ (E n))) y :=
        (hd (x - y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
      have h2 : HasFDerivAt (fun z : E n => (φ.normed volume (x - z) : ℂ))
          (Complex.ofRealCLM.comp ((fderiv ℝ (φ.normed volume) (x - y)).comp
            (-ContinuousLinearMap.id ℝ (E n)))) y :=
        Complex.ofRealCLM.hasFDerivAt.comp y h1
      rw [coordinatePartial, h2.fderiv]
      simp [ContinuousLinearMap.comp_apply]
    apply WithLp.ofLp_injective
    funext a
    show EuclideanSpace.proj a (∫ t,
          (fderiv ℝ (φ.normed volume) (x - t) (coordinateDirection j)) • F t) =
        EuclideanSpace.proj a (∫ t, (φ.normed volume) (x - t) • G j t)
    have hi1 : Integrable (fun t =>
        (fderiv ℝ (φ.normed volume) t (coordinateDirection j)) • F (x - t)) volume := by
      simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.precompL_apply,
        ContinuousLinearMap.lsmul_apply] using
        ContinuousLinearMap.integrable_comp
          (ContinuousLinearMap.apply ℝ (V r) (coordinateDirection j)) hi
    have h1int : Integrable (fun t =>
        (fderiv ℝ (φ.normed volume) (x - t) (coordinateDirection j)) • F t) volume :=
      by simpa only [sub_sub_cancel] using
        (integrable_comp_sub_left (fun s =>
          (fderiv ℝ (φ.normed volume) s (coordinateDirection j)) • F (x - s)) x).mpr hi1
    have hi2 : Integrable (fun t => (φ.normed volume) t • G j (x - t)) volume :=
      hρ_cs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ_cont
        ((hG j).locallyIntegrable (by norm_num)) x
    have h2int : Integrable (fun t => (φ.normed volume) (x - t) • G j t) volume :=
      by simpa only [sub_sub_cancel] using
        (integrable_comp_sub_left (fun s => (φ.normed volume) s • G j (x - s)) x).mpr hi2
    rw [← ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj a) h1int,
      ← ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj a) h2int]
    have hL : (fun t => EuclideanSpace.proj a
          ((fderiv ℝ (φ.normed volume) (x - t) (coordinateDirection j)) • F t)) =
        fun t => (F t) a *
          ((fderiv ℝ (φ.normed volume) (x - t) (coordinateDirection j)) : ℂ) := by
      funext t; simp [mul_comm]
    have hR : (fun t => EuclideanSpace.proj a ((φ.normed volume) (x - t) • G j t)) =
        fun t => (G j t) a * ((φ.normed volume) (x - t) : ℂ) := by
      funext t; simp [mul_comm]
    rw [hL, hR]
    have hw := hweak j (fun y : E n => (φ.normed volume (x - y) : ℂ)) hψ_cd a
    simp_rw [hcoord] at hw
    rw [show (∫ y, (F y) a *
          (-(((fderiv ℝ (φ.normed volume) (x - y) (coordinateDirection j)) : ℝ) : ℂ))) =
        -(∫ y, (F y) a *
          (((fderiv ℝ (φ.normed volume) (x - y) (coordinateDirection j)) : ℝ) : ℂ)) by
      simp_rw [mul_neg, integral_neg]] at hw
    exact neg_injective hw

end DedekindZetaZeroFree.KPCompactInteriorH1

end
