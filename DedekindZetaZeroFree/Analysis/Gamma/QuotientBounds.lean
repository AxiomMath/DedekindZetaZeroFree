module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Reference only; no source code copied.
-/

noncomputable section
open scoped NumberField Classical
open scoped Real
open scoped ComplexConjugate
open MeasureTheory

namespace DedekindZetaZeroFree.LargeSieve.Vendor

def gammaQuotient (r : ℕ) (s : ℂ) : ℂ :=
  Complex.Gammaℂ s ^ r * (Complex.Gammaℂ (1 - s))⁻¹ ^ r

theorem gammaQuotient_eq_div (r : ℕ) (s : ℂ) :
    gammaQuotient r s = (Complex.Gammaℂ s / Complex.Gammaℂ (1 - s)) ^ r := by
  simp [gammaQuotient, div_eq_mul_inv, mul_pow]

theorem gammaQuotient_differentiableOn (r : ℕ) :
    DifferentiableOn ℂ (gammaQuotient r) {s : ℂ | 0 < s.re} := by
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  refine DifferentiableAt.differentiableWithinAt ?_
  have hGam : DifferentiableAt ℂ Complex.Gamma s := by
    refine Complex.differentiableAt_Gamma s fun m h => ?_
    have h2 : s.re = -(m:ℝ) := by rw [h]; simp
    have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    rw [h2] at hs
    linarith
  have hnum : DifferentiableAt ℂ (fun s : ℂ => Complex.Gammaℂ s) s := by
    have heq : (fun s : ℂ => Complex.Gammaℂ s)
        = fun s : ℂ => (2:ℂ) * (2 * (Real.pi:ℂ)) ^ (-s) * Complex.Gamma s := by
      funext s; rw [Complex.Gammaℂ_def]
    rw [heq]
    exact ((differentiableAt_const (2:ℂ)).mul (differentiableAt_id.neg.const_cpow
      (Or.inl (by norm_num : (2 * (Real.pi:ℂ)) ≠ 0)))).mul hGam
  have hden : DifferentiableAt ℂ (fun s : ℂ => (Complex.Gammaℂ (1 - s))⁻¹) s :=
    Complex.differentiable_Gammaℂ_inv.differentiableAt.comp s
      ((differentiableAt_const (1:ℂ)).sub differentiableAt_id)
  exact ((hnum.pow r).mul (hden.pow r))

private lemma norm_cpow_ofReal_le_one {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) {w : ℂ}
    (hw : 0 ≤ w.re) : ‖(y:ℂ)^w‖ ≤ 1 := by
  rcases hy0.lt_or_eq with h | h
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos h]
    exact Real.rpow_le_one hy0 hy1 hw
  · subst h
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    · rw [Complex.ofReal_zero, Complex.zero_cpow hw0]; simp

private lemma norm_betaIntegral_le {u : ℂ} {d a : ℝ} (hu : 0 < u.re) (ha : 0 < a)
    (hau : a ≤ u.re) (hd : 1 ≤ d) :
    ‖Complex.betaIntegral u (d:ℂ)‖ ≤ 1 / a := by
  rw [Complex.betaIntegral]
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  have hg : IntervalIntegrable (fun x : ℝ => x ^ (a - 1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith)
  refine (intervalIntegral.norm_integral_le_of_norm_le h01 ?_ hg).trans ?_
  · refine Filter.Eventually.of_forall fun x hx => ?_
    rw [norm_mul]
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have h1 : ‖(x:ℂ)^(u-1)‖ ≤ x ^ (a - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      have : a - 1 ≤ (u - 1).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
      exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 this
    have h2 : ‖(1 - (x:ℂ))^((d:ℂ)-1)‖ ≤ 1 := by
      have hcast : (1 - (x:ℂ)) = ((1 - x : ℝ):ℂ) := by push_cast; ring
      rw [hcast]
      refine norm_cpow_ofReal_le_one (by linarith) (by linarith) ?_
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]; linarith
    calc ‖(x:ℂ)^(u-1)‖ * ‖(1 - (x:ℂ))^((d:ℂ)-1)‖ ≤ x ^ (a-1) * 1 := by gcongr
      _ = x ^ (a-1) := by ring
  · have h1 : a - 1 + 1 = a := by ring
    rw [integral_rpow (Or.inl (by linarith : -1 < a - 1)), h1, Real.one_rpow,
      Real.zero_rpow ha.ne']
    simp

private lemma norm_ofReal_eq_abs (x : ℝ) : ‖(x:ℂ)‖ = |x| := by
  have h : ‖(x:ℂ)‖^2 = x^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h2 : |‖(x:ℂ)‖| = |x| := by rw [← sq_eq_sq_iff_abs_eq_abs, h]
  rwa [abs_of_nonneg (norm_nonneg _)] at h2

private lemma ascPochhammer_eval_prod (N : ℕ) (z : ℂ) :
    (ascPochhammer ℂ N).eval z = ∏ j ∈ Finset.range N, (z + (j:ℂ)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_right, Polynomial.eval_mul, ih, Finset.prod_range_succ]
    congr 1
    simp

private lemma norm_ascPochhammer_eval_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (N : ℕ) (s : ℂ)
    (hs : a ≤ s.re) (hsb : s.re ≤ b) :
    ‖(ascPochhammer ℂ N).eval (1 - s)‖ ≤ ((b + 1 + N) * (1 + |s.im|))^N := by
  rw [ascPochhammer_eval_prod]
  have hprod : ‖∏ j ∈ Finset.range N, ((1 - s) + (j:ℂ))‖
      = ∏ j ∈ Finset.range N, ‖((1 - s) + (j:ℂ))‖ := norm_prod _ _
  rw [hprod]
  calc ∏ j ∈ Finset.range N, ‖((1 - s) + (j:ℂ))‖
      ≤ ∏ j ∈ Finset.range N, ((b + 1 + N) * (1 + |s.im|)) := by
        gcongr with j hj
        have hjN : (j:ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hj)
        have hre : |1 - s.re + (j:ℝ)| ≤ b + 1 + N := by
          have hb1 : |1 - s.re| ≤ b + 1 := by
            rw [abs_le]; constructor <;> linarith
          have hjabs : |(j:ℝ)| = (j:ℝ) := abs_of_nonneg (Nat.cast_nonneg j)
          calc |1 - s.re + (j:ℝ)| ≤ |1 - s.re| + |(j:ℝ)| := abs_add_le _ _
            _ = |1 - s.re| + (j:ℝ) := by rw [hjabs]
            _ ≤ (b + 1) + N := by linarith
        have hre' : ((1 - s) + (j:ℂ)).re = 1 - s.re + (j:ℝ) := by
          simp [Complex.add_re, Complex.sub_re]
        have him' : ((1 - s) + (j:ℂ)).im = -s.im := by
          simp [Complex.add_im, Complex.sub_im]
        calc ‖((1 - s) + (j:ℂ))‖ ≤ |((1 - s) + (j:ℂ)).re| + |((1 - s) + (j:ℂ)).im| :=
              Complex.norm_le_abs_re_add_abs_im _
          _ = |1 - s.re + (j:ℝ)| + |s.im| := by rw [hre', him', abs_neg]
          _ ≤ (b + 1 + N) + |s.im| := by linarith
          _ ≤ (b + 1 + N) * (1 + |s.im|) := by
              have h1 : (1:ℝ) ≤ b + 1 + N := by
                have h2 : (0:ℝ) ≤ b := le_trans ha.le hab
                push_cast; linarith
              nlinarith [abs_nonneg s.im]
    _ = ((b + 1 + N) * (1 + |s.im|))^N := by
        rw [Finset.prod_const, Finset.card_range]

private lemma gamma_ratio_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖Complex.Gamma s / Complex.Gamma (1 - s)‖ ≤
        C * (1 + |s.im|) ^ (Nat.ceil (2 * b) + 1) := by
  set N : ℕ := Nat.ceil (2 * b) + 1 with hNdef
  have hN : 2 * b + 1 ≤ (N:ℝ) := by
    have h := Nat.le_ceil (2 * b)
    rw [hNdef]; push_cast; linarith
  have hCval : 0 < (1/a) * (b + 1 + N)^N + 1 := by
    have h1 : (0:ℝ) < 1/a := by positivity
    have h2 : (0:ℝ) ≤ (b + 1 + N)^N :=
      pow_nonneg (by linarith [ha, hab] : (0:ℝ) ≤ b + 1 + N) N
    have h3 : (0:ℝ) ≤ 1/a * (b + 1 + N)^N := mul_nonneg h1.le h2
    linarith
  refine ⟨(1/a) * (b + 1 + N)^N + 1, hCval, ?_⟩
  intro s hs hsb
  by_cases hpole : ∃ k : ℕ, 1 - s = -(k:ℂ)
  · obtain ⟨k, hk⟩ := hpole
    have hz : Complex.Gamma (1 - s) = 0 := by rw [hk, Complex.Gamma_neg_nat_eq_zero]
    rw [hz, div_zero, norm_zero]
    exact mul_nonneg hCval.le (by positivity)
  · push Not at hpole
    have hPne : (ascPochhammer ℂ N).eval (1 - s) ≠ 0 := by
      rw [ascPochhammer_eval_prod]
      refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
      exact fun h => hpole j ((eq_neg_iff_add_eq_zero).mpr h)
    have hGne : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero hpole
    have hG1N : Complex.Gamma (1 - s + N) ≠ 0 := by
      refine Complex.Gamma_ne_zero_of_re_pos ?_
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.natCast_re]
      linarith [hs, hN, hab]
    have hG1 : Complex.Gamma (1 - s)
        = Complex.Gamma (1 - s + N) / (ascPochhammer ℂ N).eval (1 - s) := by
      rw [eq_div_iff hPne, mul_comm]
      rw [← Complex.Gamma_add_nat_div_Gamma_eq (1 - s) hpole]
      rw [div_mul_cancel₀ _ hGne]
    have hratio : Complex.Gamma s / Complex.Gamma (1 - s)
        = Complex.Gamma s / Complex.Gamma (1 - s + N) * (ascPochhammer ℂ N).eval (1 - s) := by
      rw [hG1]
      field_simp
    set d : ℝ := 1 - 2 * s.re + N with hddef
    have hd1 : 1 ≤ d := by rw [hddef]; push_cast; linarith [hsb, hN]
    have hd2 : 2 ≤ d := by rw [hddef]; push_cast; linarith [hsb, hN]
    have hd0 : 0 < d := by linarith
    have hs0 : 0 < s.re := lt_of_lt_of_le ha hs
    have hconj : conj (1 - s + N) = s + (d:ℂ) := by
      rw [hddef]
      apply Complex.ext <;>
        simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
          Complex.conj_im] <;> ring
    have hnormG : ‖Complex.Gamma (1 - s + N)‖ = ‖Complex.Gamma (s + (d:ℂ))‖ := by
      rw [← Complex.norm_conj (Complex.Gamma (1 - s + N)),
        ← Complex.Gamma_conj (1 - s + N), hconj]
    have hGsd : Complex.Gamma (s + (d:ℂ)) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
      simp only [Complex.add_re, Complex.ofReal_re]; linarith)
    have hGd : Complex.Gamma (d:ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hd0)
    have hkey : Complex.Gamma s / Complex.Gamma (s + (d:ℂ))
        = Complex.betaIntegral s (d:ℂ) / Complex.Gamma (d:ℂ) := by
      rw [eq_div_iff hGd, div_mul_eq_mul_div, Complex.Gamma_mul_Gamma_eq_betaIntegral hs0 hd0,
        mul_div_cancel_left₀ _ hGsd]
    have hratio2 : ‖Complex.Gamma s / Complex.Gamma (1 - s + N)‖ ≤ 1 / a := by
      have h1 : ‖Complex.Gamma s / Complex.Gamma (1 - s + N)‖
          = ‖Complex.Gamma s / Complex.Gamma (s + (d:ℂ))‖ := by
        rw [norm_div, norm_div, hnormG]
      rw [h1, hkey, norm_div]
      have hB : ‖Complex.betaIntegral s (d:ℂ)‖ ≤ 1 / a := norm_betaIntegral_le hs0 ha hs hd1
      have hGd1 : 1 ≤ ‖Complex.Gamma (d:ℂ)‖ := by
        rw [Complex.Gamma_ofReal, norm_ofReal_eq_abs, abs_of_pos (Real.Gamma_pos_of_pos hd0)]
        have hmono : Real.Gamma 2 ≤ Real.Gamma d :=
          Real.Gamma_strictMonoOn_Ici.monotoneOn (show (2:ℝ) ∈ Set.Ici 2 by norm_num)
            (show d ∈ Set.Ici 2 from hd2) hd2
        exact le_trans (le_of_eq Real.Gamma_two.symm) hmono
      rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖Complex.Gamma (d:ℂ)‖)]
      calc ‖Complex.betaIntegral s (d:ℂ)‖ ≤ 1 / a := hB
        _ ≤ 1 / a * ‖Complex.Gamma (d:ℂ)‖ := by
            have : (0:ℝ) ≤ 1/a := by positivity
            nlinarith [hGd1]
    calc ‖Complex.Gamma s / Complex.Gamma (1 - s)‖
        = ‖Complex.Gamma s / Complex.Gamma (1 - s + N)‖
            * ‖(ascPochhammer ℂ N).eval (1 - s)‖ := by rw [hratio, norm_mul]
      _ ≤ (1/a) * ((b + 1 + N) * (1 + |s.im|))^N :=
          mul_le_mul hratio2 (norm_ascPochhammer_eval_le ha hab N s hs hsb)
            (norm_nonneg _) (by positivity)
      _ = (1/a) * (b + 1 + N)^N * (1 + |s.im|)^N := by rw [mul_pow]; ring
      _ ≤ ((1/a) * (b + 1 + N)^N + 1) * (1 + |s.im|)^N := by
          have h1 : (0:ℝ) ≤ (1 + |s.im|)^N := by positivity
          nlinarith [h1]

theorem gammaQuotient_polynomial_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (r : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖(Complex.Gammaℂ s / Complex.Gammaℂ (1 - s)) ^ r‖ ≤
        C * (1 + |s.im|) ^ k := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := gamma_ratio_bound ha hab
  refine ⟨(C₀ * (2*π)^(1-2*a) + 1)^r, (Nat.ceil (2*b)+1) * r, by positivity, ?_⟩
  intro s hs hsb
  have hne : (2*π:ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact_mod_cast (ne_of_gt (by positivity : (0:ℝ) < π))
  have hcpow : (2*π:ℂ)^(-s) / (2*π:ℂ)^(-(1-s)) = (2*π:ℂ)^(1-2*s) := by
    rw [div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hne]
    congr 1
    ring
  have hdecomp : Complex.Gammaℂ s / Complex.Gammaℂ (1 - s)
      = (2*π:ℂ)^(1-2*s) * (Complex.Gamma s / Complex.Gamma (1 - s)) := by
    rw [Complex.Gammaℂ_def, Complex.Gammaℂ_def, ← div_mul_div_comm,
      mul_div_mul_left _ _ (by norm_num : (2:ℂ) ≠ 0), hcpow]
  have hnormx : ‖Complex.Gammaℂ s / Complex.Gammaℂ (1 - s)‖ ≤
      (C₀ * (2*π)^(1-2*a)) * (1 + |s.im|)^(Nat.ceil (2*b)+1) := by
    rw [hdecomp, norm_mul]
    have h2 : ‖(2*π:ℂ)^(1-2*s)‖ ≤ (2*π)^(1-2*a) := by
      have hbase : (2:ℂ) * (π:ℂ) = ((2*π : ℝ):ℂ) := by push_cast; ring
      rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ) < 2*π)]
      have hre : (1 - 2*s).re = 1 - 2*s.re := by
        simp [Complex.sub_re, Complex.one_re, Complex.mul_re]
      rw [hre]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ 2*π)
        (by linarith)
    calc ‖(2*π:ℂ)^(1-2*s)‖ * ‖Complex.Gamma s / Complex.Gamma (1 - s)‖
        ≤ (2*π)^(1-2*a) * (C₀ * (1 + |s.im|)^(Nat.ceil (2*b)+1)) :=
          mul_le_mul h2 (hC₀ s hs hsb) (norm_nonneg _) (by positivity)
      _ = C₀ * (2*π)^(1-2*a) * (1 + |s.im|)^(Nat.ceil (2*b)+1) := by ring
  rw [norm_pow]
  calc ‖Complex.Gammaℂ s / Complex.Gammaℂ (1 - s)‖ ^ r
      ≤ ((C₀ * (2*π)^(1-2*a)) * (1 + |s.im|)^(Nat.ceil (2*b)+1))^r :=
        pow_le_pow_left₀ (norm_nonneg _) hnormx r
    _ = (C₀ * (2*π)^(1-2*a))^r * ((1 + |s.im|)^(Nat.ceil (2*b)+1))^r := by rw [mul_pow]
    _ = (C₀ * (2*π)^(1-2*a))^r * (1 + |s.im|)^((Nat.ceil (2*b)+1) * r) := by rw [← pow_mul]
    _ ≤ (C₀ * (2*π)^(1-2*a) + 1)^r * (1 + |s.im|)^((Nat.ceil (2*b)+1) * r) := by
        have h1 : (0:ℝ) ≤ (1 + |s.im|)^((Nat.ceil (2*b)+1) * r) := by positivity
        have h2 : (0:ℝ) ≤ C₀ * (2*π)^(1-2*a) := by positivity
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ h2 (by linarith : C₀ * (2*π)^(1-2*a) ≤ C₀ * (2*π)^(1-2*a) + 1) r) h1

end DedekindZetaZeroFree.LargeSieve.Vendor

end
