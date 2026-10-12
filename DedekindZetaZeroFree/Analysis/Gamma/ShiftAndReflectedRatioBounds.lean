module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import DedekindZetaZeroFree.Analysis.Gamma.ElementaryNormBounds

@[expose] public section

/- The beta comparison proofs below are adapted (namespace and explicit shift
binder changed) from openai/math, adc7f1241b42e322a6451854ab7e4b4c146bf78a,
lean/OAI/NumberTheory/CubicMoment/Estimates/GammaBetaComparison.lean.
Apache-2.0; the full upstream license is included in the imported elementary
vendor module. -/

open MeasureTheory Set

namespace DedekindZetaZeroFree

private lemma beta_real_integral_eq (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ in (0:ℝ)..1, t^(x-1)*(1-t)^(y-1)) =
      Real.Gamma x*Real.Gamma y/Real.Gamma (x+y) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have he : (∫ t : ℝ in (0:ℝ)..1, ((t^(x-1)*(1-t)^(y-1):ℝ):ℂ)) =
      Complex.betaIntegral (x:ℂ) (y:ℂ) := by
    unfold Complex.betaIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    simp only [Complex.ofReal_mul,Complex.ofReal_cpow ht.1,
      Complex.ofReal_cpow (sub_nonneg.mpr ht.2),Complex.ofReal_sub,Complex.ofReal_one]
  rw [he,Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using hx) (by simpa using hy)]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,← Complex.ofReal_add,Complex.Gamma_ofReal]

private lemma beta_norm_le_real (s : ℂ) {d : ℝ} (hs : 0 < s.re) (hd : 0 < d) :
    ‖Complex.betaIntegral s (d:ℂ)‖ ≤
      Real.Gamma s.re*Real.Gamma d/Real.Gamma (s.re+d) := by
  rw [← beta_real_integral_eq s.re d hs hd]
  unfold Complex.betaIntegral
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ) ≤ 1)).trans_eq
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
  have hp : 0 < 1-t := sub_pos.mpr ht.2
  rw [show (1:ℂ)-(t:ℂ) = ((1-t:ℝ):ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hp]
  simp

theorem gamma_real_shift_ratio_bound (s : ℂ) (d : ℝ)
    (hs : 0 < s.re) (hd : 0 < d) :
    ‖Complex.Gamma s‖ / ‖Complex.Gamma (s + (d : ℂ))‖ ≤
      Real.Gamma s.re / Real.Gamma (s.re + d) := by
  have h := beta_norm_le_real s hs hd
  have hg : 0 < Real.Gamma d := Real.Gamma_pos_of_pos hd
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hs (by simpa using hd),
    norm_div,norm_mul,Complex.Gamma_ofReal,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hg] at h
  apply (mul_le_mul_iff_right₀ hg).mp
  convert h using 1 <;> ring

theorem gammaC_reflected_ratio_left_bound (δ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 10) :
    ∃ Kδ : ℝ, 0 < Kδ ∧ ∀ s : ℂ, s.re = -δ →
      ‖Complex.Gammaℂ (1 - s) * (Complex.Gammaℂ s)⁻¹‖ ≤
        Kδ * (2 + |s.im|) ^ 2 := by
  have hgap : 0 < 1 - 2 * δ := by linarith
  have hx : 0 < 1 + δ := by linarith
  have hy : 0 < 2 - δ := by linarith
  let A : ℝ := Real.Gamma (1 + δ) / Real.Gamma (2 - δ)
  let B : ℝ := (2 * Real.pi) ^ (- (1 + δ)) / (2 * Real.pi) ^ δ
  have hA : 0 < A := div_pos (Real.Gamma_pos_of_pos hx) (Real.Gamma_pos_of_pos hy)
  have hbase : 0 < 2 * Real.pi := by positivity
  have hB : 0 < B := div_pos (Real.rpow_pos_of_pos hbase _) (Real.rpow_pos_of_pos hbase _)
  refine ⟨B * A, mul_pos hB hA, ?_⟩
  intro s hs
  have hw : (1 - s).re = 1 + δ := by simp [hs]
  have hshift : 1 - s + ((1 - 2 * δ : ℝ) : ℂ) = star (s + 2) := by
    apply Complex.ext <;> simp [hs] <;> ring
  have hb := gamma_real_shift_ratio_bound (1 - s) (1 - 2 * δ) (by rw [hw]; exact hx) hgap
  rw [hshift] at hb
  change ‖Complex.Gamma (1 - s)‖ / ‖Complex.Gamma ((starRingEnd ℂ) (s + 2))‖ ≤ _ at hb
  rw [Complex.Gamma_conj, Complex.norm_conj, hw] at hb
  have hb' : ‖Complex.Gamma (1 - s)‖ / ‖Complex.Gamma (s + 2)‖ ≤ A := by
    convert hb using 1 <;> dsimp [A] <;> congr 2 <;> ring
  have hn : ‖s‖ ≤ 2 + |s.im| := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 2 + |s.im| := by rw [hs, abs_neg, abs_of_pos hδ]; linarith
  have hn1 : ‖s + 1‖ ≤ 2 + |s.im| := by
    calc
      ‖s + 1‖ ≤ |(s + 1).re| + |(s + 1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 2 + |s.im| := by
        simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, add_zero, hs]
        rw [abs_of_pos (by linarith : 0 < -δ + 1)]
        linarith
  have hpoly : ‖s‖ * ‖s + 1‖ ≤ (2 + |s.im|) ^ 2 := by
    simpa [pow_two] using mul_le_mul hn hn1 (norm_nonneg _) (by positivity)
  have hrec : (Complex.Gamma s)⁻¹ = s * (s + 1) * (Complex.Gamma (s + 2))⁻¹ := by
    rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s,
      Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s + 1)]
    ring_nf
  have hg : ‖Complex.Gamma (1 - s) * (Complex.Gamma s)⁻¹‖ ≤ A * (2 + |s.im|) ^ 2 := by
    rw [hrec, norm_mul, norm_mul, norm_mul, norm_inv]
    calc
      _ = (‖Complex.Gamma (1 - s)‖ / ‖Complex.Gamma (s + 2)‖) *
          (‖s‖ * ‖s + 1‖) := by ring
      _ ≤ A * (2 + |s.im|) ^ 2 :=
        mul_le_mul hb' hpoly (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hA.le
  have hnorm : ‖Complex.Gammaℂ (1 - s) * (Complex.Gammaℂ s)⁻¹‖ =
      B * ‖Complex.Gamma (1 - s) * (Complex.Gamma s)⁻¹‖ := by
    simp only [Complex.Gammaℂ_def, norm_mul, norm_inv]
    have he1 : ‖(2 * (Real.pi : ℂ)) ^ (-(1 - s))‖ = (2 * Real.pi) ^ (-(1 + δ)) := by
      rw [show 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase]
      simp [hs]
      congr 1 <;> ring
    have he2 : ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ = (2 * Real.pi) ^ δ := by
      rw [show 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase]
      simp [hs]
    rw [he1, he2]
    norm_num
    dsimp [B]
    ring
  rw [hnorm]
  calc
    B * ‖Complex.Gamma (1 - s) * (Complex.Gamma s)⁻¹‖ ≤
        B * (A * (2 + |s.im|) ^ 2) := mul_le_mul_of_nonneg_left hg hB.le
    _ = _ := by ring

end DedekindZetaZeroFree
