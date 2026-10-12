module

import DedekindZetaZeroFree.Analysis.HolomorphicKernels.RectangularCauchyOperators
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs

public section

noncomputable section
open scoped Topology
open Complex
namespace DedekindZetaZeroFree.ComplexAnalysis
open KernelTaylor.CauchyOperators
variable {X : Type*} [TopologicalSpace X]

private theorem continuous_ball_of_continuous_sphere
    (f : ℂ → X → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : ∀ x, DifferentiableOn ℂ (fun z => f z x) (Metric.closedBall c R))
    (hc : Continuous (fun p : Metric.sphere c R × X => f p.1 p.2)) :
    Continuous (fun p : Metric.ball c R × X => f p.1 p.2) := by
  let weighted : Metric.ball c R × X → C(Metric.sphere c R, ℂ) := fun p =>
    ⟨fun z => ((z : ℂ) - c) / ((z : ℂ) - p.1.val) * f z p.2, by
      have hn : ∀ z : Metric.sphere c R, (z : ℂ) - p.1.val ≠ 0 := by
        intro z hz
        have he : (z : ℂ) = p.1.val := sub_eq_zero.mp hz
        have hs := z.property
        rw [he] at hs
        exact (ne_of_lt p.1.property) hs
      exact ((continuous_subtype_val.sub continuous_const).div
        (continuous_subtype_val.sub continuous_const) hn).mul
        (hc.comp (continuous_id.prodMk continuous_const))⟩
  have hweighted : Continuous weighted := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hn : ∀ p : (Metric.ball c R × X) × Metric.sphere c R,
        (p.2 : ℂ) - p.1.1.val ≠ 0 := by
      intro p hz
      have he : (p.2 : ℂ) = p.1.1.val := sub_eq_zero.mp hz
      have hs := p.2.property
      rw [he] at hs
      exact (ne_of_lt p.1.1.property) hs
    exact (((continuous_subtype_val.comp continuous_snd).sub continuous_const).div
      ((continuous_subtype_val.comp continuous_snd).sub
        (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))) hn).mul
      (hc.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
  have heq (p : Metric.ball c R × X) :
      circleCoeffCLM c R hR 0 (weighted p) = f p.1 p.2 := by
    have hC := (hf p.2).circleIntegral_sub_inv_smul p.1.property
    change circleCoeff c R 0 (weighted p) = _
    unfold circleCoeff
    have he : (∮ z in C(c, R), (z - c)⁻¹ ^ 0 * (z - c)⁻¹ *
        circleLift c R (weighted p) z) =
        ∮ z in C(c, R), (z - p.1.val)⁻¹ • f z p.2 := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      dsimp only
      rw [show circleLift c R (weighted p) z = (weighted p) ⟨z, hz⟩ from
        circleLift_eq c R (weighted p) ⟨z, hz⟩]
      have hzc : z - c ≠ 0 := by
        intro he
        have hz' : z = c := sub_eq_zero.mp he
        subst z
        exact hR.ne' (by simpa using hz.symm)
      simp only [weighted, pow_zero, one_mul, smul_eq_mul, ContinuousMap.coe_mk,
        div_eq_mul_inv]
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hzc, one_mul]
    rw [he, hC]
    simp only [smul_eq_mul]
    exact inv_mul_cancel_left₀ (by
      exact mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) _
  exact ((circleCoeffCLM c R hR 0).continuous.comp hweighted).congr heq

theorem continuousOn_ball_of_continuous_sphere
    (f : ℂ → X → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : ∀ x, DifferentiableOn ℂ (fun z => f z x) (Metric.closedBall c R))
    (hc : Continuous (fun p : Metric.sphere c R × X => f p.1 p.2)) :
    ContinuousOn (fun p : ℂ × X => f p.1 p.2) (Metric.ball c R ×ˢ Set.univ) := by
  have hj := continuous_ball_of_continuous_sphere f c R hR hf hc
  apply continuousOn_iff_continuous_domRestrict.mpr
  let k : (Metric.ball c R ×ˢ (Set.univ : Set X)) → Metric.ball c R × X :=
    fun p => (⟨p.val.1, p.property.1⟩, p.val.2)
  have hk : Continuous k :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk (fun p => p.property.1)).prodMk
      (continuous_snd.comp continuous_subtype_val)
  exact hj.comp hk

end DedekindZetaZeroFree.ComplexAnalysis
