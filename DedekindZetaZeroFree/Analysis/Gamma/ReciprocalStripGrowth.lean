module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Vendor

open scoped NumberField Classical
open Complex MeasureTheory

private theorem norm_Gamma_le_Gamma_re (z : ℂ) (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, Real.Gamma_eq_integral hz]
  calc ‖∫ x in Set.Ioi (0:ℝ), (↑(Real.exp (-x)) : ℂ) * (↑x : ℂ) ^ (z - 1)‖
      ≤ ∫ x in Set.Ioi (0:ℝ), ‖(↑(Real.exp (-x)) : ℂ) * (↑x : ℂ) ^ (z - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x in Set.Ioi (0:ℝ), Real.exp (-x) * x ^ (z.re - 1) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
          norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hx), sub_re, one_re]

private theorem norm_sin_le_exp_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h1 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; simp [Complex.mul_I_re, Complex.neg_im]
  have h2 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; simp [Complex.mul_I_re]
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one, show ‖(2:ℂ)‖ = 2 by norm_num]
  have h6 : Real.exp z.im + Real.exp (-z.im) ≤ 2 * Real.exp |z.im| := by
    have h4 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
    have h5 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
    linarith
  linarith [norm_sub_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I)), h1, h2]

private theorem sin_ne_zero_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) : Complex.sin z ≠ 0 := by
  intro h
  have h2 : (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * (Complex.I / 2) = 0 := by
    rw [show (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * (Complex.I / 2)
          = (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I / 2 by ring]
    exact h
  have hsub : Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I) = 0 :=
    (mul_eq_zero.mp h2).resolve_right (by simp)
  have h1 : Complex.exp (-z * Complex.I) = Complex.exp (z * Complex.I) := sub_eq_zero.mp hsub
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
  have hre : (-z * Complex.I).re = (z * Complex.I + (n:ℂ) * (2 * (Real.pi:ℂ) * Complex.I)).re := by
    rw [hn]
  simp [Complex.mul_I_re, Complex.neg_re, Complex.neg_im] at hre
  exact hz (by linarith)

private theorem Gamma_one_sub_add_nat (s : ℂ) (n : ℕ) (h : ∀ k < n, s ≠ ((k:ℂ) + 1)) :
    Complex.Gamma (1 - s + n) = (∏ k ∈ Finset.range n, (((k:ℂ) + 1) - s)) * Complex.Gamma (1 - s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h' : ∀ k < n, s ≠ ((k:ℂ) + 1) := fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hn : s ≠ ((n:ℂ) + 1) := h n (Nat.lt_succ_self n)
    have hw : (1 - s + n) ≠ 0 := by
      intro hc
      exact hn (by linear_combination -hc)
    have hcast : (1 - s + ((n:ℂ) + 1)) = (1 - s + n) + 1 := by ring
    rw [Nat.cast_succ, hcast, Complex.Gamma_add_one _ hw, ih h', Finset.prod_range_succ]
    ring

private theorem inv_Gamma_eq (s : ℂ) (hs : Complex.sin ((Real.pi:ℂ) * s) ≠ 0) :
    (Complex.Gamma s)⁻¹ = Complex.Gamma (1 - s) * Complex.sin ((Real.pi:ℂ) * s) / (Real.pi:ℂ) := by
  have h := Complex.Gamma_mul_Gamma_one_sub s
  have h1 : Complex.Gamma s * (Complex.Gamma (1 - s) * Complex.sin ((Real.pi:ℂ) * s) / (Real.pi:ℂ)) = 1 := by
    have e : Complex.Gamma s * (Complex.Gamma (1 - s) * Complex.sin ((Real.pi:ℂ) * s) / (Real.pi:ℂ))
        = (Complex.Gamma s * Complex.Gamma (1 - s)) * (Complex.sin ((Real.pi:ℂ) * s) / (Real.pi:ℂ)) := by
      ring
    rw [e, h]
    field_simp
  exact inv_eq_of_mul_eq_one_right h1

private theorem continuousOn_RealGamma_Icc {l u : ℝ} (hl : 0 < l) :
    ContinuousOn Real.Gamma (Set.Icc l u) := by
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le hl hx.1
  have hc : ContinuousAt (fun y : ℝ => Complex.Gamma ((y:ℝ):ℂ)) x :=
    (Complex.continuousAt_Gamma (x:ℂ) (fun m hm => by
      have := congrArg Complex.re hm
      simp at this
      linarith)).comp (continuous_ofReal.continuousAt)
  exact (Complex.continuous_re.continuousAt.comp hc).continuousWithinAt

private theorem inverse_Gamma_strip_bound (a b : ℝ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ s : ℂ, s.re ∈ Set.Icc a b →
      ‖(Complex.Gamma s)⁻¹‖ ≤ C * Real.exp (A * |s.im|) := by
  let n : ℕ := ⌈b⌉₊
  have hbn : b ≤ (n:ℝ) := Nat.le_ceil b
  have hb1n : (0:ℝ) < 1 - b + (n:ℝ) := by linarith
  have hcont : ContinuousOn Real.Gamma (Set.Icc (1 - b + n) (1 - a + n)) :=
    continuousOn_RealGamma_Icc hb1n
  obtain ⟨D0, hD0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let D : ℝ := max D0 0 / Real.pi
  have hDnonneg : 0 ≤ D := div_nonneg (le_max_right _ _) Real.pi_pos.le
  have hlarge : ∀ s : ℂ, s.re ∈ Set.Icc a b → 1 ≤ |s.im| →
      ‖(Complex.Gamma s)⁻¹‖ ≤ D * Real.exp (Real.pi * |s.im|) := by
    intro s hs ht
    have hsim : s.im ≠ 0 := by intro h; rw [h] at ht; exact absurd ht (by norm_num)
    have hsin : Complex.sin ((Real.pi:ℂ) * s) ≠ 0 := by
      apply sin_ne_zero_of_im_ne_zero
      show ((Real.pi:ℂ) * s).im ≠ 0
      rw [Complex.mul_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_ne_zero Real.pi_ne_zero hsim
    have hfac : ∀ k : ℕ, (1:ℝ) ≤ ‖((k:ℂ) + 1) - s‖ := by
      intro k
      have h1 : |s.im| ≤ ‖((k:ℂ) + 1) - s‖ := by
        have := Complex.abs_im_le_norm (((k:ℂ) + 1) - s)
        simpa [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.one_im] using this
      linarith
    have hPnorm : (1:ℝ) ≤ ‖∏ k ∈ Finset.range n, (((k:ℂ) + 1) - s)‖ := by
      rw [norm_prod]
      induction n with
      | zero => simp
      | succ m ih => rw [Finset.prod_range_succ]; exact one_le_mul_of_one_le_of_one_le ih (hfac m)
    have hrec := Gamma_one_sub_add_nat s n (fun k _ => by
      intro hc
      have h2 : s.im = 0 := by rw [hc]; simp
      exact hsim h2)
    have hG1 : ‖Complex.Gamma (1 - s)‖ ≤ ‖Complex.Gamma (1 - s + n)‖ := by
      have hnorms : ‖Complex.Gamma (1 - s + n)‖
          = ‖∏ k ∈ Finset.range n, (((k:ℂ) + 1) - s)‖ * ‖Complex.Gamma (1 - s)‖ := by
        rw [hrec, norm_mul]
      rw [hnorms]
      calc ‖Complex.Gamma (1 - s)‖ = 1 * ‖Complex.Gamma (1 - s)‖ := by ring
        _ ≤ ‖∏ k ∈ Finset.range n, (((k:ℂ) + 1) - s)‖ * ‖Complex.Gamma (1 - s)‖ :=
            mul_le_mul_of_nonneg_right hPnorm (norm_nonneg (Complex.Gamma (1 - s)))
    have hGn : ‖Complex.Gamma (1 - s + n)‖ ≤ max D0 0 := by
      have hre_pos : 0 < (1 - s + n).re := by
        have h2 : (1:ℝ) ≤ (1 - s + n).re := by
          simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.natCast_re,
            Complex.ofReal_re]
          linarith [hs.2, hbn]
        linarith
      have hle := norm_Gamma_le_Gamma_re (1 - s + n) hre_pos
      have hmem : (1 - s + n).re ∈ Set.Icc (1 - b + n) (1 - a + n) := by
        simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.natCast_re,
          Complex.ofReal_re]
        exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hb := hD0 _ hmem
      rw [Real.norm_eq_abs] at hb
      linarith [le_max_left D0 0, (abs_le.mp hb).2]
    have hGbound : ‖Complex.Gamma (1 - s)‖ ≤ max D0 0 := hG1.trans hGn
    rw [inv_Gamma_eq s hsin, norm_div, norm_mul]
    have hsinb : ‖Complex.sin ((Real.pi:ℂ) * s)‖ ≤ Real.exp (Real.pi * |s.im|) := by
      have := norm_sin_le_exp_im ((Real.pi:ℂ) * s)
      rwa [show ((Real.pi:ℂ) * s).im = Real.pi * s.im by
            simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im],
          abs_mul, abs_of_pos Real.pi_pos] at this
    have hpinorm : ‖(Real.pi:ℂ)‖ = Real.pi := Complex.norm_of_nonneg Real.pi_pos.le
    rw [hpinorm]
    have hexp1 : (1:ℝ) ≤ Real.exp (Real.pi * |s.im|) := Real.one_le_exp (by positivity)
    calc ‖Complex.Gamma (1 - s)‖ * ‖Complex.sin ((Real.pi:ℂ) * s)‖ / Real.pi
        ≤ (max D0 0) * Real.exp (Real.pi * |s.im|) / Real.pi := by
          apply div_le_div_of_nonneg_right _ Real.pi_pos.le
          exact mul_le_mul hGbound hsinb (norm_nonneg _) (le_max_right _ _)
      _ = D * Real.exp (Real.pi * |s.im|) := by ring
  have hK : IsCompact ((fun p : ℝ × ℝ => (p.1:ℂ) + (p.2:ℂ) * Complex.I) ''
      (Set.Icc a b ×ˢ Set.Icc (-1:ℝ) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn
    (Complex.differentiable_one_div_Gamma.continuous.norm.continuousOn)
  refine ⟨max (max C0 D) 0, Real.pi, le_max_right _ _, Real.pi_pos.le, ?_⟩
  intro s hs
  have hexp1 : (1:ℝ) ≤ Real.exp (Real.pi * |s.im|) := Real.one_le_exp (by positivity)
  by_cases ht : |s.im| ≤ 1
  · have hmem : s ∈ (fun p : ℝ × ℝ => (p.1:ℂ) + (p.2:ℂ) * Complex.I) ''
        (Set.Icc a b ×ˢ Set.Icc (-1:ℝ) 1) := by
      refine ⟨(s.re, s.im), ⟨hs, ?_⟩, ?_⟩
      · rw [Set.mem_Icc]; exact abs_le.mp ht
      · exact Complex.re_add_im s
    have hb := hC0 s hmem
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hb
    calc ‖(Complex.Gamma s)⁻¹‖ ≤ C0 := hb
      _ ≤ max (max C0 D) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
      _ ≤ max (max C0 D) 0 * Real.exp (Real.pi * |s.im|) :=
          le_mul_of_one_le_right (le_max_right _ _) hexp1
  · rw [not_le] at ht
    have hb := hlarge s hs ht.le
    calc ‖(Complex.Gamma s)⁻¹‖ ≤ D * Real.exp (Real.pi * |s.im|) := hb
      _ ≤ max (max C0 D) 0 * Real.exp (Real.pi * |s.im|) :=
          mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _))
            (Real.exp_nonneg _)

theorem inverse_Gammaℂ_strip_exp_bound (a b : ℝ) (r : ℕ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ s : ℂ, s.re ∈ Set.Icc a b →
        ‖(Complex.Gammaℂ s)⁻¹‖ ^ r ≤ C * Real.exp (A * |s.im|) := by
  obtain ⟨C, A, hC, hA, hbound⟩ := inverse_Gamma_strip_bound a b
  have hbase1 : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hbasenn : (0:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_pos]
  refine ⟨(C * (2 * Real.pi) ^ (max a b)) ^ r, (r:ℝ) * A,
    pow_nonneg (mul_nonneg hC (Real.rpow_nonneg hbasenn _)) r,
    mul_nonneg (Nat.cast_nonneg r) hA, ?_⟩
  intro s hs
  have hkey : (Complex.Gammaℂ s)⁻¹
      = (1/2 : ℂ) * (2 * (Real.pi : ℂ)) ^ s * (Complex.Gamma s)⁻¹ := by
    rw [Complex.Gammaℂ_def, mul_inv, mul_inv, Complex.cpow_neg, inv_inv]
    ring_nf
  have hnorm : ‖(Complex.Gammaℂ s)⁻¹‖ ≤ C * (2 * Real.pi) ^ (max a b) * Real.exp (A * |s.im|) := by
    rw [hkey, norm_mul, norm_mul]
    have hhalf : ‖(1/2 : ℂ)‖ = 1/2 := by
      rw [show (1/2 : ℂ) = (((1/2 : ℝ)) : ℂ) by norm_num]
      exact Complex.norm_of_nonneg (by norm_num)
    have hcpow : ‖(2 * (Real.pi : ℂ)) ^ s‖ = (2 * Real.pi) ^ s.re := by
      rw [show (2 * (Real.pi:ℂ)) = ((2*Real.pi:ℝ):ℂ) by push_cast; ring]
      exact norm_cpow_eq_rpow_re_of_pos (by positivity) s
    have hle : (2 * Real.pi) ^ s.re ≤ (2 * Real.pi) ^ (max a b) :=
      Real.rpow_le_rpow_of_exponent_le hbase1 (hs.2.trans (le_max_right _ _))
    rw [hhalf, hcpow]
    calc (1/2) * (2 * Real.pi) ^ s.re * ‖(Complex.Gamma s)⁻¹‖
        ≤ (1/2) * (2 * Real.pi) ^ (max a b) * (C * Real.exp (A * |s.im|)) := by
          apply mul_le_mul
          · apply mul_le_mul_of_nonneg_left hle (by norm_num)
          · exact hbound s hs
          · exact norm_nonneg _
          · positivity
      _ ≤ (2 * Real.pi) ^ (max a b) * (C * Real.exp (A * |s.im|)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_of_le_one_left (by positivity)
          norm_num
      _ = C * (2 * Real.pi) ^ (max a b) * Real.exp (A * |s.im|) := by ring
  calc ‖(Complex.Gammaℂ s)⁻¹‖ ^ r
      ≤ (C * (2 * Real.pi) ^ (max a b) * Real.exp (A * |s.im|)) ^ r :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm r
    _ = (C * (2 * Real.pi) ^ (max a b)) ^ r * Real.exp (A * |s.im|) ^ r := by rw [mul_pow]
    _ = (C * (2 * Real.pi) ^ (max a b)) ^ r * Real.exp (((r:ℝ) * A) * |s.im|) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring_nf

end DedekindZetaZeroFree.LargeSieve.Vendor
