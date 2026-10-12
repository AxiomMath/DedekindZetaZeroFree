module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.GaussianLattice
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.PolynomialGaussianAbsorption

@[expose] public section

noncomputable section

open scoped ContDiff

namespace DedekindZetaZeroFree.AbelianQuotient.Theta.GaussianSchwartz

private theorem real_gaussian_decay
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a : ℝ) (ha : 0 < a) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : E ↦ Real.exp (-a * ‖x‖ ^ 2)) x‖ ≤ C := by
  have ht : Function.HasTemperateGrowth (fun x : E ↦ -a * ‖x‖ ^ 2) := by fun_prop
  obtain ⟨m, C, hC, hb⟩ := ht.norm_iteratedFDeriv_le_uniform n
  have hc1 : 1 ≤ max C 1 := le_max_right _ _
  obtain ⟨P, hP, hbound⟩ := DedekindZetaZeroFree.thetaPolynomialGaussianAbsorption
    (k + m * n) a ha
  refine ⟨(n.factorial : ℝ) * (max C 1) ^ n * P, ?_⟩
  intro x
  have hu : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hD1 : 1 ≤ max C 1 * (1 + ‖x‖) ^ m := one_le_mul_of_one_le_of_one_le hc1 (one_le_pow₀ hu)
  have hderiv : ‖iteratedFDeriv ℝ n (fun x : E ↦ Real.exp (-a * ‖x‖ ^ 2)) x‖ ≤
      (n.factorial : ℝ) * Real.exp (-a * ‖x‖ ^ 2) *
        (max C 1 * (1 + ‖x‖) ^ m) ^ n := by
    apply norm_iteratedFDeriv_comp_le (N := ∞) Real.contDiff_exp ht.1 (by simp) x
    · intro i hi
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
        Real.iter_deriv_exp, Real.norm_of_nonneg (Real.exp_pos _).le]
    · intro i hi hin
      calc ‖iteratedFDeriv ℝ i (fun x : E ↦ -a * ‖x‖ ^ 2) x‖
        ≤ C * (1 + ‖x‖) ^ m := hb i hin x
        _ ≤ max C 1 * (1 + ‖x‖) ^ m := by gcongr; exact le_max_left _ _
        _ ≤ (max C 1 * (1 + ‖x‖) ^ m) ^ i := by
          simpa using pow_le_pow_right₀ hD1 hi
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : E ↦ Real.exp (-a * ‖x‖ ^ 2)) x‖
    ≤ ‖x‖ ^ k * ((n.factorial : ℝ) * Real.exp (-a * ‖x‖ ^ 2) *
        (max C 1 * (1 + ‖x‖) ^ m) ^ n) := mul_le_mul_of_nonneg_left hderiv (by positivity)
    _ ≤ (1 + ‖x‖) ^ k * ((n.factorial : ℝ) * Real.exp (-a * ‖x‖ ^ 2) *
        (max C 1 * (1 + ‖x‖) ^ m) ^ n) := by gcongr; linarith
    _ = (n.factorial : ℝ) * (max C 1) ^ n *
        ((1 + ‖x‖) ^ (k + m * n) * Real.exp (-a * ‖x‖ ^ 2)) := by
      rw [mul_pow, ← pow_mul, pow_add]; ring
    _ ≤ (n.factorial : ℝ) * (max C 1) ^ n *
        (P * Real.exp (-(a / 2) * ‖x‖ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (hbound ‖x‖ (norm_nonneg _)) (by positivity)
    _ ≤ (n.factorial : ℝ) * (max C 1) ^ n * P := by
      have he : Real.exp (-(a / 2) * ‖x‖ ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
      calc _ ≤ (n.factorial : ℝ) * (max C 1) ^ n * (P * 1) := by gcongr
           _ = _ := by ring

theorem exists_gaussian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (a : ℝ) (ha : 0 < a) :
    ∃ f : SchwartzMap E ℂ, ∀ x, f x = latticeGaussian a x := by
  let g : SchwartzMap E ℝ := {
    toFun := fun x ↦ Real.exp (-a * ‖x‖ ^ 2)
    smooth' := Real.contDiff_exp.comp
      (show Function.HasTemperateGrowth (fun x : E ↦ -a * ‖x‖ ^ 2) from by fun_prop).1
    decay' := real_gaussian_decay a ha }
  refine ⟨SchwartzMap.postcompCLM Complex.ofRealCLM g, ?_⟩
  intro x
  change (Real.exp (-a * ‖x‖ ^ 2) : ℂ) = latticeGaussian a x
  simp [latticeGaussian]

end DedekindZetaZeroFree.AbelianQuotient.Theta.GaussianSchwartz

end
