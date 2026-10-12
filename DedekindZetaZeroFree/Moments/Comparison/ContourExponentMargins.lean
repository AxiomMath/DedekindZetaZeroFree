module

public import DedekindZetaZeroFree.Moments.Comparison.TripleMellinKernel

@[expose] public section

namespace DedekindZetaZeroFree

theorem comparisonE_shifted_z_margin :
    comparisonE comparisonSigma₁ (19 / 20) comparisonZeta₁ ≤ 7 / 15 - 1 / 2000 := by
  simp only [comparisonE, comparisonA, comparisonB, comparisonH₀, comparisonSigma₁,
    comparisonZeta₁, comparisonDelta]
  norm_num

theorem comparisonE_w_residue_margin :
    comparisonE comparisonSigma₁ 1 (4 / 25) ≤ 7 / 15 - 1 / 2000 := by
  simp only [comparisonE, comparisonA, comparisonB, comparisonH₀, comparisonSigma₁,
    comparisonDelta]
  norm_num

theorem comparisonE_first_dyadic_margin :
    comparisonE comparisonSigma₁ (3 / 1000) (2 / 5) +
      (9 / 100) * (11 / 10) ≤ 7 / 15 - 1 / 1000 := by
  simp only [comparisonE, comparisonA, comparisonB, comparisonH₀, comparisonSigma₁,
    comparisonDelta]
  norm_num

theorem comparisonE_second_dyadic_margin :
    comparisonE comparisonSigma₁ (3 / 1000) (2 / 5) +
      (10001 / 100000) * (3 / 5) ≤ 7 / 15 - 1 / 1000 := by
  simp only [comparisonE, comparisonA, comparisonB, comparisonH₀, comparisonSigma₁,
    comparisonDelta]
  norm_num

theorem comparisonE_left_contour_margin :
    comparisonE (499 / 500) (3 / 1000) (2 / 5) +
      (10001 / 100000) * (11 / 10) = 7 / 15 - 377 / 300000 := by
  simp only [comparisonE, comparisonA, comparisonB, comparisonH₀]
  norm_num

end DedekindZetaZeroFree
