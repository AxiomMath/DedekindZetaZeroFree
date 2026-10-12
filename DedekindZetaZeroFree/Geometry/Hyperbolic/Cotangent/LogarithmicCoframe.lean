module

public import DedekindZetaZeroFree.Geometry.HyperbolicActionMetricAndVolume
public import DedekindZetaZeroFree.Geometry.Hyperbolic.Laplacian.ChartGreenIdentities

@[expose] public section

noncomputable section

open scoped ContDiff

namespace DedekindZetaZeroFree.CotangentLogCoframe

abbrev Index (d : ℕ) := Fin d × Fin 3

abbrev RealCoefficients (d : ℕ) := EuclideanSpace ℝ (Index d)

abbrev ComplexCoefficients (d : ℕ) := EuclideanSpace ℂ (Index d)

def C (d : ℕ) (p : HyperbolicChart.Space d) :
    HyperbolicChart.Space d ≃L[ℝ] RealCoefficients d :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u => WithLp.toLp 2 (fun ik =>
        ![u (ik.1, 2), Real.exp (-p (ik.1, 2)) * u (ik.1, 0),
          Real.exp (-p (ik.1, 2)) * u (ik.1, 1)] ik.2)
      invFun := fun v => WithLp.toLp 2 (fun ik =>
        ![Real.exp (p (ik.1, 2)) * v (ik.1, 1),
          Real.exp (p (ik.1, 2)) * v (ik.1, 2), v (ik.1, 0)] ik.2)
      map_add' := by
        intro u w
        ext ik
        obtain ⟨i, k⟩ := ik
        fin_cases k <;> simp [mul_add]
      map_smul' := by
        intro a u
        ext ik
        obtain ⟨i, k⟩ := ik
        fin_cases k <;> simp [mul_assoc, mul_comm, mul_left_comm]
      left_inv := by
        intro v
        ext ik
        obtain ⟨i, k⟩ := ik
        fin_cases k <;> simp [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
          one_mul]
      right_inv := by
        intro u
        ext ik
        obtain ⟨i, k⟩ := ik
        fin_cases k <;> simp [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
          one_mul] }

def H (d : ℕ) (p : HyperbolicChart.Space d) :
    RealCoefficients d ≃L[ℝ] HyperbolicChart.Space d :=
  (C d p).symm

theorem C_apply (d : ℕ) (p u : HyperbolicChart.Space d) (i : Fin d) :
    (C d p u) (i, 0) = u (i, 2) ∧
    (C d p u) (i, 1) = Real.exp (-p (i, 2)) * u (i, 0) ∧
    (C d p u) (i, 2) = Real.exp (-p (i, 2)) * u (i, 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [C]

theorem H_apply (d : ℕ) (p : HyperbolicChart.Space d)
    (v : RealCoefficients d) (i : Fin d) :
    (H d p v) (i, 0) = Real.exp (p (i, 2)) * v (i, 1) ∧
    (H d p v) (i, 1) = Real.exp (p (i, 2)) * v (i, 2) ∧
    (H d p v) (i, 2) = v (i, 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [H, C]

theorem contDiff_C (d : ℕ) :
    ContDiff ℝ ∞ (fun p : HyperbolicChart.Space d =>
      (C d p).toContinuousLinearMap) := by
  rw [contDiff_clm_apply_iff]
  intro u
  rw [show (fun p : HyperbolicChart.Space d => (C d p).toContinuousLinearMap u) =
      fun p => WithLp.toLp 2 (fun ik : Index d =>
        ![u (ik.1, 2), Real.exp (-p (ik.1, 2)) * u (ik.1, 0),
          Real.exp (-p (ik.1, 2)) * u (ik.1, 1)] ik.2) from rfl]
  rw [contDiff_piLp]
  intro ik
  obtain ⟨i, k⟩ := ik
  fin_cases k <;> simp <;> fun_prop

theorem contDiff_H (d : ℕ) :
    ContDiff ℝ ∞ (fun p : HyperbolicChart.Space d =>
      (H d p).toContinuousLinearMap) := by
  rw [contDiff_clm_apply_iff]
  intro v
  rw [show (fun p : HyperbolicChart.Space d => (H d p).toContinuousLinearMap v) =
      fun p => WithLp.toLp 2 (fun ik : Index d =>
        ![Real.exp (p (ik.1, 2)) * v (ik.1, 1),
          Real.exp (p (ik.1, 2)) * v (ik.1, 2), v (ik.1, 0)] ik.2) from rfl]
  rw [contDiff_piLp]
  intro ik
  obtain ⟨i, k⟩ := ik
  fin_cases k <;> simp <;> fun_prop

private lemma exp_mul_exp (t a b : ℝ) :
    (Real.exp (-t) * a) * (Real.exp (-t) * b) = Real.exp (-2 * t) * (a * b) := by
  have h : Real.exp (-t) * Real.exp (-t) = Real.exp (-2 * t) := by
    rw [← Real.exp_add]
    ring_nf
  calc (Real.exp (-t) * a) * (Real.exp (-t) * b)
      = (Real.exp (-t) * Real.exp (-t)) * (a * b) := by ring
    _ = Real.exp (-2 * t) * (a * b) := by rw [h]

theorem inner_C (d : ℕ) (p u w : HyperbolicChart.Space d) :
    inner ℝ (C d p u) (C d p w) = HyperbolicChart.metric d p u w := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, HyperbolicChart.metric]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_three]
  obtain ⟨hu0, hu1, hu2⟩ := C_apply d p u i
  obtain ⟨hw0, hw1, hw2⟩ := C_apply d p w i
  rw [hu0, hu1, hu2, hw0, hw1, hw2]
  simp only [RCLike.inner_apply', Real.ringHom_apply]
  rw [exp_mul_exp, exp_mul_exp]
  ring

def A (d : ℕ) : HyperbolicChart.Space d ≃L[ℝ] KPArch.Space d :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p i =>
        ((p (i, 0) : ℂ) + Complex.I * (p (i, 1) : ℂ), p (i, 2))
      invFun := fun z => WithLp.toLp 2 (fun ik =>
        ![(z ik.1).1.re, (z ik.1).1.im, (z ik.1).2] ik.2)
      map_add' := by
        intro p q
        ext i <;> simp [Complex.ofReal_add] <;> ring
      map_smul' := by
        intro a p
        ext i <;> simp [Complex.ofReal_mul] <;> ring
      left_inv := by
        intro z
        ext ik
        obtain ⟨i, k⟩ := ik
        fin_cases k <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      right_inv := by
        intro z
        ext i
        · simp [Complex.re_add_im, mul_comm Complex.I]
        · simp }

theorem A_apply (d : ℕ) (p : HyperbolicChart.Space d) (i : Fin d) :
    A d p i = ((p (i, 0) : ℂ) + Complex.I * (p (i, 1) : ℂ), p (i, 2)) := by
  rfl

theorem metric_A (d : ℕ) (p u : HyperbolicChart.Space d) :
    KPArch.metric d (A d p) (A d u) = HyperbolicChart.metric d p u u := by
  rw [KPArch.metric, HyperbolicChart.metric]
  apply Finset.sum_congr rfl
  intro i _
  rw [A_apply d p i, A_apply d u i]
  have he : ((Real.exp (p (i, 2)))⁻¹) ^ 2 = Real.exp (-2 * p (i, 2)) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  simp only [KPArch.height, he, Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

def j (d : ℕ) : HyperbolicChart.Cotangent d ≃ₗ[ℂ] ComplexCoefficients d where
  toFun W := WithLp.toLp 2 (fun ik => W ik.1 ik.2)
  invFun v := fun i k => v (i, k)
  map_add' := by
    intro U W
    ext ik
    simp
  map_smul' := by
    intro a W
    ext ik
    simp
  left_inv := by
    intro W
    ext i k
    simp
  right_inv := by
    intro v
    ext ik
    simp

theorem j_apply (d : ℕ) (W : HyperbolicChart.Cotangent d)
    (i : Fin d) (k : Fin 3) :
    j d W (i, k) = W i k := by
  rfl

theorem inner_j (d : ℕ) (U W : HyperbolicChart.Cotangent d) :
    inner ℂ (j d U) (j d W) = HyperbolicChart.pairing d U W := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, HyperbolicChart.pairing]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [j_apply, j_apply, RCLike.inner_apply']
  rfl

end DedekindZetaZeroFree.CotangentLogCoframe

end
