module

public import DedekindZetaZeroFree.Eisenstein.Induction.Height.ArchimedeanFactorization

@[expose] public section

noncomputable section
open scoped Classical Matrix Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.HeightGeometry

def complexMatrixLogNorm (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Real.log ((‖A.det‖ / (‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2)) ^ 2)
 def ratio (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ‖A.det‖ / (‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2)
private lemma ratio_denom_pos (A : Matrix (Fin 2) (Fin 2) ℂ) (h : A.det ≠ 0) :
    0 < ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2 := by
  have hr : A 1 0 ≠ 0 ∨ A 1 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (by rw [Matrix.det_fin_two]; simp [hc.1, hc.2])
  rcases hr with h0 | h1
  · have : 0 < ‖A 1 0‖ := norm_pos_iff.mpr h0
    nlinarith [sq_nonneg ‖A 1 1‖, sq_nonneg ‖A 1 0‖]
  · have : 0 < ‖A 1 1‖ := norm_pos_iff.mpr h1
    nlinarith [sq_nonneg ‖A 1 1‖, sq_nonneg ‖A 1 0‖]
private lemma ratio_pos (A : Matrix (Fin 2) (Fin 2) ℂ) (h : A.det ≠ 0) : 0 < ratio A :=
  div_pos (norm_pos_iff.mpr h) (ratio_denom_pos A h)
private lemma ratio_mul_scalar (c : ℂ) (hc : c ≠ 0) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ratio (A * Matrix.scalar (Fin 2) c) = ratio A := by
  have hc2 : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  have hent : ∀ i j, (A * Matrix.scalar (Fin 2) c) i j = A i j * c := by
    intro i j
    rw [Matrix.scalar_apply, Matrix.mul_diagonal]
  have hdet : (A * Matrix.scalar (Fin 2) c).det = A.det * c ^ 2 := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two, hent 0 0, hent 0 1, hent 1 0, hent 1 1]
    ring
  have hnum : ‖(A * Matrix.scalar (Fin 2) c).det‖ = ‖A.det‖ * ‖c‖ ^ 2 := by
    rw [hdet, norm_mul, norm_pow]
  have hden : ‖(A * Matrix.scalar (Fin 2) c) 1 0‖ ^ 2 +
      ‖(A * Matrix.scalar (Fin 2) c) 1 1‖ ^ 2 =
      (‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) * ‖c‖ ^ 2 := by
    rw [hent 1 0, hent 1 1, norm_mul, norm_mul]; ring
  unfold ratio
  rw [hnum, hden, mul_comm (‖A.det‖) (‖c‖ ^ 2),
    mul_comm (‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) (‖c‖ ^ 2)]
  exact mul_div_mul_left _ _ hc2

theorem complexMatrixLogNorm_eq_of_mk_eq
    (A B : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    complexMatrixLogNorm (A : Matrix (Fin 2) (Fin 2) ℂ) =
      complexMatrixLogNorm (B : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have hcoe : (B : Matrix (Fin 2) (Fin 2) ℂ) =
      (A : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.scalar (Fin 2) (u : ℂ) := by
    rw [← hu, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar]
  change Real.log ((ratio _) ^ 2) = Real.log ((ratio _) ^ 2)
  rw [hcoe, ratio_mul_scalar _ (Units.ne_zero u) _]

def complexProjectiveLogNorm (a : Matrix.ProjGenLinGroup (Fin 2) ℂ) : ℝ :=
  complexMatrixLogNorm (a.out : Matrix (Fin 2) (Fin 2) ℂ)
theorem complexProjectiveLogNorm_mk (A : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    complexProjectiveLogNorm (Matrix.ProjGenLinGroup.mk A) =
      complexMatrixLogNorm (A : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold complexProjectiveLogNorm
  exact complexMatrixLogNorm_eq_of_mk_eq _ _ (Quotient.out_eq _)

theorem complexMatrixLogNorm_contDiffOn :
    ContDiffOn ℝ ⊤ complexMatrixLogNorm
      {A : Matrix (Fin 2) (Fin 2) ℂ | A.det ≠ 0} := by
  have hdet : ContDiff ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℂ => A.det) := by
    have h : (fun A : Matrix (Fin 2) (Fin 2) ℂ => A.det) =
        fun A => A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
      funext A; rw [Matrix.det_fin_two]
    rw [h]; fun_prop
  have hnum : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℂ => ‖A.det‖)
      {A : Matrix (Fin 2) (Fin 2) ℂ | A.det ≠ 0} :=
    ContDiffOn.norm ℂ hdet.contDiffOn (fun A hA => hA)
  have hd0 : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 0)
      {A : Matrix (Fin 2) (Fin 2) ℂ | A.det ≠ 0} := by fun_prop
  have hd1 : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1)
      {A : Matrix (Fin 2) (Fin 2) ℂ | A.det ≠ 0} := by fun_prop
  have hden : ContDiffOn ℝ ⊤
      (fun A : Matrix (Fin 2) (Fin 2) ℂ => ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2)
      {A : Matrix (Fin 2) (Fin 2) ℂ | A.det ≠ 0} :=
    (ContDiffOn.norm_sq ℂ hd0).add (ContDiffOn.norm_sq ℂ hd1)
  have hratio : ContDiffOn ℝ ⊤ ratio
      {A : Matrix (Fin 2) (Fin 2) ℂ | A.det ≠ 0} :=
    hnum.div hden (fun A hA => ne_of_gt (ratio_denom_pos A hA))
  exact (hratio.pow 2).log (fun A hA => pow_ne_zero 2 (ne_of_gt (ratio_pos A hA)))
end DedekindZetaZeroFree.HeightGeometry

end
