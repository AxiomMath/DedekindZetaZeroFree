module

public import DedekindZetaZeroFree.Analysis.HolomorphicKernels.RectangularCauchyOperators

@[expose] public section

noncomputable section
open scoped Topology
open Complex
namespace DedekindZetaZeroFree.ResidueContinuity
open ComplexAnalysis.KernelTaylor.CauchyOperators

variable {X : Type*} [TopologicalSpace X]

theorem continuous_center_of_continuous_circle
    (N : ℂ → X → ℂ) (r t : ℝ) (ht : 0 < t) (htr : t < r)
    (hN : ∀ x, AnalyticOnNhd ℂ (fun z => N z x) (Metric.ball 0 r))
    (hc : Continuous (fun p : Metric.sphere (0 : ℂ) t × X => N p.1 p.2)) :
    Continuous (N 0) := by
  let boundary : X → C(Metric.sphere (0 : ℂ) t, ℂ) := fun x =>
    ⟨fun z => N z x, hc.comp (continuous_id.prodMk continuous_const)⟩
  have hboundary : Continuous boundary := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hc.comp continuous_swap
  have heq (x : X) : circleCoeffCLM 0 t ht 0 (boundary x) = N 0 x := by
    have hi := (kernel_continuousOn 0 t ht (boundary x) 0).circleIntegrable ht.le
    have hd : DifferentiableOn ℂ (fun z => N z x) (Metric.closedBall 0 t) :=
      (hN x).differentiableOn.mono (Metric.closedBall_subset_ball htr)
    have hC := hd.circleIntegral_sub_inv_smul (Metric.mem_ball_self ht)
    change circleCoeff 0 t 0 (boundary x) = _
    unfold circleCoeff
    have he : (∮ z in C(0, t), (z - 0)⁻¹ ^ 0 * (z - 0)⁻¹ *
        circleLift 0 t (boundary x) z) =
        ∮ z in C(0, t), (z - 0)⁻¹ • N z x := by
      apply circleIntegral.integral_congr ht.le
      intro z hz
      dsimp only
      rw [show circleLift 0 t (boundary x) z = (boundary x) ⟨z, hz⟩ from
        circleLift_eq 0 t (boundary x) ⟨z, hz⟩]
      simp only [pow_zero, one_mul, smul_eq_mul]
      rfl
    rw [he, hC]
    simp only [smul_eq_mul]
    exact inv_mul_cancel_left₀ (by
      exact mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) _
  exact ((circleCoeffCLM 0 t ht 0).continuous.comp hboundary).congr heq

end DedekindZetaZeroFree.ResidueContinuity

end
