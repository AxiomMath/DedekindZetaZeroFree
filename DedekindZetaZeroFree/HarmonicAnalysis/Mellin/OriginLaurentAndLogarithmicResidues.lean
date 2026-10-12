module

public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.PositiveSideJetSeminorms

@[expose] public section

noncomputable section

open scoped Topology

namespace DedekindZetaZeroFree.LargeSieve.Vendor

def originLaurentCoeff (A : ℂ → ℂ) (r m : ℕ) : ℂ :=
  iteratedDeriv (r - m) A 0 / ((r - m).factorial : ℂ)

def originLogResiduePolynomial (A : ℂ → ℂ) (r : ℕ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range r,
    Polynomial.C (((-1 : ℂ) ^ n * originLaurentCoeff A r (n + 1)) /
      (n.factorial : ℂ)) * Polynomial.X ^ n

private lemma originLogResiduePolynomial_coeff_eq (A : ℂ → ℂ) (r n : ℕ) (hn : n < r) :
    (originLogResiduePolynomial A r).coeff n =
      (-1 : ℂ) ^ n * originLaurentCoeff A r (n + 1) / (n.factorial : ℂ) := by
  rw [originLogResiduePolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single n]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro b hb hbn
    rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hbn)]
  · intro h
    exact absurd (Finset.mem_range.mpr hn) h

theorem originLogResiduePolynomial_natDegree_le (A : ℂ → ℂ) (r : ℕ)
    (hr : 1 ≤ r) : (originLogResiduePolynomial A r).natDegree ≤ r - 1 := by
  rw [originLogResiduePolynomial]
  refine Polynomial.natDegree_sum_le_of_forall_le (Finset.range r)
    (fun n => Polynomial.C (((-1 : ℂ) ^ n * originLaurentCoeff A r (n + 1)) /
      (n.factorial : ℂ)) * Polynomial.X ^ n) fun n hn => ?_
  have hn' : n ≤ r - 1 := by
    have := Finset.mem_range.mp hn; omega
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans hn'

theorem origin_exists_analytic_laurent (U : Set ℂ) (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (A : ℂ → ℂ) (hA : AnalyticOnNhd ℂ A U) (r : ℕ) (hr : 1 ≤ r) :
    ∃ G₀ : ℂ → ℂ, AnalyticOnNhd ℂ G₀ U ∧
      ∀ s ∈ U, s ≠ 0 →
        A s / s ^ r = G₀ s +
          ∑ m ∈ Finset.Icc 1 r, originLaurentCoeff A r m / s ^ m := by
  obtain ⟨F, hFa, hF⟩ := (hA 0 h0).exists_eventuallyEq_sum_add_pow_mul r
  set Pfun : ℂ → ℂ := fun t =>
    ∑ i ∈ Finset.range r, (t ^ i / (i.factorial : ℂ)) * iteratedDeriv i A 0 with hPfun
  have hPana : AnalyticOnNhd ℂ Pfun U := by
    intro t ht
    rw [hPfun]
    exact Finset.analyticAt_fun_sum _ (fun i hi => by fun_prop)
  refine ⟨fun s => if s = 0 then F 0 else (A s - Pfun s) / s ^ r, ?_, ?_⟩
  · intro s hs
    by_cases hs0 : s = 0
    · subst hs0
      refine hFa.congr ?_
      filter_upwards [hF] with z hz
      show F z = (if z = 0 then F 0 else (A z - Pfun z) / z ^ r)
      by_cases hz0 : z = 0
      · rw [if_pos hz0, hz0]
      · rw [if_neg hz0]
        have hz' : A z - Pfun z = z ^ r * F z := by
          rw [hz, hPfun]
          simp only [smul_eq_mul]
          ring
        rw [hz']
        field_simp
    · have hquot : AnalyticAt ℂ (fun t => (A t - Pfun t) / t ^ r) s :=
        AnalyticAt.div ((hA s hs).sub (hPana s hs)) (by fun_prop)
          (pow_ne_zero r hs0)
      refine hquot.congr ?_
      filter_upwards [compl_singleton_mem_nhds hs0] with t ht
      show (A t - Pfun t) / t ^ r = (if t = 0 then F 0 else (A t - Pfun t) / t ^ r)
      rw [if_neg (by simpa using ht)]
  · intro s hs hs0
    show A s / s ^ r = (if s = 0 then F 0 else (A s - Pfun s) / s ^ r) +
      ∑ m ∈ Finset.Icc 1 r, originLaurentCoeff A r m / s ^ m
    rw [if_neg hs0]
    have hreindex : Pfun s / s ^ r =
        ∑ m ∈ Finset.Icc 1 r, originLaurentCoeff A r m / s ^ m := by
      rw [hPfun, Finset.sum_div]
      refine Finset.sum_bij (fun i _ => r - i) ?_ ?_ ?_ ?_
      · intro i hi
        have hi' : i < r := Finset.mem_range.mp hi
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro i₁ h₁ i₂ h₂ h
        have h₁' := Finset.mem_range.mp h₁
        have h₂' := Finset.mem_range.mp h₂
        omega
      · intro m hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
        exact ⟨r - m, Finset.mem_range.mpr (by omega), by omega⟩
      · intro i hi
        have hi' : i < r := Finset.mem_range.mp hi
        simp only [originLaurentCoeff, show r - (r - i) = i by omega]
        rw [show r = i + (r - i) by omega, pow_add]
        field_simp
        rw [show i + (r - i) - i = r - i by omega]
    rw [← hreindex, ← add_div, sub_add_cancel]

private lemma pow_mul_zero (n j : ℕ) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    iteratedDeriv n (fun s => s^j * f s) 0 =
    if j ≤ n then (n.choose j : ℂ) * (j.factorial : ℂ) * iteratedDeriv (n-j) f 0 else 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf.contDiffAt]
  simp_rw [iteratedDeriv_fun_pow_zero]
  by_cases h : j ≤ n
  · rw [if_pos h, Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      simp [hbj]
    · intro hj
      exact (hj (Finset.mem_range.mpr (by omega))).elim
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b hb
    have hbj : b ≠ j := by have := Finset.mem_range.mp hb; omega
    simp [hbj]

private lemma fac_ratio (n k : ℕ) (h : k ≤ n) :
    (n.choose k : ℂ) * (k.factorial : ℂ) / (n.factorial : ℂ) =
      1 / ((n-k).factorial : ℂ) := by
  have hh : (n.choose k : ℂ) * (k.factorial : ℂ) * ((n-k).factorial : ℂ) =
      (n.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h2 : ((n-k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-k)
  field_simp
  exact hh

private lemma twist_coeff (n j : ℕ) (c : ℂ) (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0) :
    iteratedDeriv n (fun s => (-s)^j * Complex.exp (c*s) * A s) 0 / (n.factorial : ℂ) =
    if j ≤ n then (-1:ℂ)^j *
      ∑ i ∈ Finset.range (n-j+1), c^i * iteratedDeriv (n-j-i) A 0 /
        ((i.factorial : ℂ) * ((n-j-i).factorial : ℂ)) else 0 := by
  have he : AnalyticAt ℂ (fun s => Complex.exp (c*s) * A s) 0 := by
    exact (by fun_prop : AnalyticAt ℂ (fun s => Complex.exp (c*s)) 0).fun_mul hA
  have hfun : (fun s : ℂ => (-s)^j * Complex.exp (c*s) * A s) =
      fun s => (-1:ℂ)^j * (s^j * (Complex.exp (c*s) * A s)) := by
    ext s; rw [neg_eq_neg_one_mul, mul_pow]; ring
  rw [hfun]
  rw [iteratedDeriv_const_mul_field, pow_mul_zero n j _ he]
  by_cases hj : j ≤ n
  · rw [if_pos hj, if_pos hj]
    rw [show (-1:ℂ)^j * ((n.choose j : ℂ) * (j.factorial : ℂ) *
        iteratedDeriv (n-j) (fun s => Complex.exp (c*s) * A s) 0) / (n.factorial : ℂ) =
        (-1:ℂ)^j * ((n.choose j : ℂ) * (j.factorial : ℂ) / (n.factorial : ℂ)) *
          iteratedDeriv (n-j) (fun s => Complex.exp (c*s) * A s) 0 by ring]
    rw [fac_ratio n j hj, iteratedDeriv_fun_mul (by fun_prop) hA.contDiffAt]
    simp_rw [iteratedDeriv_cexp_const_mul, mul_zero, Complex.exp_zero, mul_one]
    rw [mul_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ n-j := by have := Finset.mem_range.mp hi; omega
    have h := fac_ratio (n-j) i hi'
    have hfac : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    field_simp at h ⊢
    linear_combination c^i * iteratedDeriv (n-j-i) A 0 * h
  · simp [hj]

private lemma df_ratio (n j : ℕ) (h : j ≤ n) :
    (n.descFactorial j : ℂ) / (n.factorial : ℂ) =
      1 / ((n-j).factorial : ℂ) := by
  have hh : ((n-j).factorial : ℂ) * (n.descFactorial j : ℂ) =
      (n.factorial : ℂ) := by exact_mod_cast Nat.factorial_mul_descFactorial h
  have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h2 : ((n-j).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-j)
  field_simp
  linear_combination hh

private lemma poly_eval (A : ℂ → ℂ) (r j : ℕ) (L : ℂ) :
    Polynomial.eval L ((Polynomial.derivative^[j]) (originLogResiduePolynomial A r)) =
    ∑ n ∈ Finset.range r, if j ≤ n then
      (-1:ℂ)^n * originLaurentCoeff A r (n+1) * L^(n-j) / ((n-j).factorial : ℂ)
      else 0 := by
  rw [originLogResiduePolynomial, Polynomial.iterate_derivative_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_X_pow_eq_C_mul]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  by_cases hj : j ≤ n
  · rw [if_pos hj]
    calc
      _ = (-1:ℂ)^n * originLaurentCoeff A r (n+1) * L^(n-j) *
          ((n.descFactorial j : ℂ) / (n.factorial : ℂ)) := by ring
      _ = _ := by rw [df_ratio n j hj]; ring
  · rw [if_neg hj, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

private lemma coeff_identity (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0)
    (r j : ℕ) (hr : 1 ≤ r) (L : ℂ) :
    originLaurentCoeff (fun s => (-s)^j * Complex.exp (-s*L) * A s) r 1 =
      Polynomial.eval L ((Polynomial.derivative^[j]) (originLogResiduePolynomial A r)) := by
  have hf : (fun s : ℂ => (-s)^j * Complex.exp (-s*L) * A s) =
      fun s => (-s)^j * Complex.exp ((-L)*s) * A s := by
        ext s
        rw [show -s * L = -L * s by ring]
  rw [originLaurentCoeff, hf, twist_coeff (r-1) j (-L) A hA, poly_eval]
  by_cases hj : j ≤ r-1
  · rw [if_pos hj]
    conv_rhs =>
      arg 1
      rw [show r = j + (r-j) by omega]
    rw [Finset.sum_range_add (fun n => if j ≤ n then
      (-1:ℂ)^n * originLaurentCoeff A r (n+1) * L^(n-j) / ((n-j).factorial : ℂ)
      else 0) j (r-j)]
    have hz : (∑ n ∈ Finset.range j,
        if j ≤ n then (-1:ℂ)^n * originLaurentCoeff A r (n+1) *
          L^(n-j) / ((n-j).factorial : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      rw [if_neg (by have := Finset.mem_range.mp hn; omega)]
    rw [hz, zero_add, show r-1-j+1 = r-j by omega, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (by omega : j ≤ j+i)]
    simp only [Nat.add_sub_cancel_left]
    rw [originLaurentCoeff]
    have hi' : i < r-j := Finset.mem_range.mp hi
    rw [show r - (j+i+1) = r-1-j-i by omega]
    rw [neg_eq_neg_one_mul, mul_pow, pow_add]
    ring
  · rw [if_neg hj]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    rw [if_neg (by have := Finset.mem_range.mp hn; omega)]

theorem origin_exists_analytic_twisted_laurent (U : Set ℂ) (hU : IsOpen U)
    (h0 : (0 : ℂ) ∈ U) (A : ℂ → ℂ) (hA : AnalyticOnNhd ℂ A U)
    (r : ℕ) (hr : 1 ≤ r) (L : ℝ) (j : ℕ) :
    ∃ (c : ℕ → ℂ) (G : ℂ → ℂ), AnalyticOnNhd ℂ G U ∧
      (∀ s ∈ U, s ≠ 0 →
        (-s) ^ j * Complex.exp (-s * (L : ℂ)) * A s / s ^ r =
          G s + ∑ m ∈ Finset.Icc 1 r, c m / s ^ m) ∧
      c 1 = Polynomial.eval (L : ℂ)
        ((Polynomial.derivative^[j]) (originLogResiduePolynomial A r)) := by
  let B : ℂ → ℂ := fun s => (-s)^j * Complex.exp (-s*(L:ℂ)) * A s
  have hB : AnalyticOnNhd ℂ B U := by
    intro s hs
    exact (by fun_prop : AnalyticAt ℂ (fun s : ℂ => (-s)^j *
      Complex.exp (-s*(L:ℂ))) s).fun_mul (hA s hs)
  obtain ⟨G, hG, hGeq⟩ := origin_exists_analytic_laurent U hU h0 B hB r hr
  refine ⟨originLaurentCoeff B r, G, hG, hGeq, ?_⟩
  exact coeff_identity A (hA 0 h0) r j hr (L:ℂ)

private lemma hasDerivAt_poly_log (Q : Polynomial ℂ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => Q.eval (Real.log y : ℂ))
      (Q.derivative.eval (Real.log x : ℂ) * ((x : ℂ))⁻¹) x := by
  have h1 : HasDerivAt (⇑Complex.ofRealCLM) (1 : ℂ) (Real.log x) :=
    Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun z : ℂ => Q.eval z)
      (Q.derivative.eval (Real.log x : ℂ)) (Real.log x : ℂ) :=
    Q.hasDerivAt _
  have h3 : HasDerivAt (fun y : ℝ => Q.eval (y : ℂ))
      (Q.derivative.eval (Real.log x : ℂ)) (Real.log x) := by
    convert h2.scomp (Real.log x) h1 using 1
    · ext y; rfl
    · simp
  have h4 : HasDerivAt Real.log (x⁻¹) x := Real.hasDerivAt_log hx
  have h5 := h3.scomp x h4
  convert h5 using 1
  · ext y; rfl
  · simp [Complex.ofReal_inv, mul_comm]

theorem EulerIter_eval_log_polynomial (P : Polynomial ℂ) (j : ℕ)
    (x : ℝ) (hx : 0 < x) :
    EulerIter j (fun y : ℝ => Polynomial.eval (Real.log y : ℂ) P) x =
      Polynomial.eval (Real.log x : ℂ) ((Polynomial.derivative^[j]) P) := by
  have key : ∀ j : ℕ, Set.EqOn
      (EulerIter j (fun y : ℝ => Polynomial.eval (Real.log y : ℂ) P))
      (fun y : ℝ => Polynomial.eval (Real.log y : ℂ) ((Polynomial.derivative^[j]) P))
      (Set.Ioi 0) := by
    intro j
    induction j with
    | zero => intro y _; simp [EulerIter_zero]
    | succ j ih =>
      intro y hy
      rw [EulerIter_succ_of_pos j _ y hy]
      have hyn : y ≠ 0 := ne_of_gt hy
      have hev : EulerIter j (fun y : ℝ => Polynomial.eval (Real.log y : ℂ) P)
          =ᶠ[𝓝 y]
          (fun z : ℝ => Polynomial.eval (Real.log z : ℂ) ((Polynomial.derivative^[j]) P)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
        exact ih hz
      rw [hev.deriv_eq, (hasDerivAt_poly_log ((Polynomial.derivative^[j]) P) hyn).deriv]
      rw [Function.iterate_succ_apply']
      have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hyn
      field_simp
  exact key j hx

theorem originLaurentCoeff_norm_le (U : Set ℂ) (hU : IsOpen U)
    (h0 : (0 : ℂ) ∈ U) (A : ℂ → ℂ) (hA : AnalyticOnNhd ℂ A U)
    (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) (hmr : m ≤ r)
    (M : ℝ) (hM : 0 ≤ M)
    (hdisk : Metric.closedBall (0 : ℂ) (1 / 2 : ℝ) ⊆ U)
    (hbound : ∀ s ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ), ‖A s‖ ≤ M) :
    ‖originLaurentCoeff A r m‖ ≤ 2 ^ (r - m) * M := by
  have hball : Metric.ball (0 : ℂ) (1 / 2 : ℝ) ⊆ U := fun z hz =>
    hdisk (Metric.ball_subset_closedBall hz)
  have hcl : closure (Metric.ball (0 : ℂ) (1 / 2 : ℝ)) ⊆ U :=
    Metric.closure_ball_subset_closedBall.trans hdisk
  have hf : DiffContOnCl ℂ A (Metric.ball (0 : ℂ) (1 / 2 : ℝ)) :=
    ⟨(hA.mono hball).differentiableOn, (hA.mono hcl).continuousOn⟩
  have hC : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2 : ℝ), ‖A z‖ ≤ M := fun z hz =>
    hbound z (Metric.sphere_subset_closedBall hz)
  have hCauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (c := (0 : ℂ)) (R := (1 / 2 : ℝ)) (C := M) (r - m) (by norm_num) hf hC
  have hfac : (0 : ℝ) < ((r - m).factorial : ℝ) := by positivity
  rw [originLaurentCoeff, norm_div, Complex.norm_natCast]
  calc ‖iteratedDeriv (r - m) A 0‖ / ((r - m).factorial : ℝ)
      ≤ (((r - m).factorial : ℝ) * M / (1 / 2 : ℝ) ^ (r - m)) /
          ((r - m).factorial : ℝ) :=
        div_le_div_of_nonneg_right hCauchy hfac.le
    _ = M / (1 / 2 : ℝ) ^ (r - m) := by field_simp
    _ = 2 ^ (r - m) * M := by
        rw [div_eq_mul_inv, one_div, inv_pow]
        field_simp

theorem originLogResiduePolynomial_coeff_norm_le (U : Set ℂ) (hU : IsOpen U)
    (h0 : (0 : ℂ) ∈ U) (A : ℂ → ℂ) (hA : AnalyticOnNhd ℂ A U)
    (r n : ℕ) (hr : 1 ≤ r) (hn : n < r) (M : ℝ) (hM : 0 ≤ M)
    (hdisk : Metric.closedBall (0 : ℂ) (1 / 2 : ℝ) ⊆ U)
    (hbound : ∀ s ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ), ‖A s‖ ≤ M) :
    ‖(originLogResiduePolynomial A r).coeff n‖ ≤
      2 ^ (r - n - 1) * M / (n.factorial : ℝ) := by
  rw [originLogResiduePolynomial_coeff_eq A r n hn, norm_div, norm_mul]
  have hneg : ‖(-1 : ℂ) ^ n‖ = 1 := by rw [norm_pow]; norm_num
  rw [hneg, one_mul, Complex.norm_natCast]
  have ha := originLaurentCoeff_norm_le U hU h0 A hA r (n + 1) hr (by omega) (by omega)
    M hM hdisk hbound
  have hk : r - (n + 1) = r - n - 1 := by omega
  rw [hk] at ha
  exact div_le_div_of_nonneg_right ha (by positivity)

theorem originLaurentCoeff_top (A : ℂ → ℂ) (r : ℕ) :
    originLaurentCoeff A r r = A 0 := by
  simp [originLaurentCoeff]

theorem originLogResiduePolynomial_coeff_top (A : ℂ → ℂ) (r : ℕ) (hr : 1 ≤ r) :
    (originLogResiduePolynomial A r).coeff (r - 1) =
      (-1 : ℂ) ^ (r - 1) * A 0 / ((r - 1).factorial : ℂ) := by
  rw [originLogResiduePolynomial_coeff_eq A r (r - 1) (by omega),
    show r - 1 + 1 = r by omega, originLaurentCoeff_top]

end DedekindZetaZeroFree.LargeSieve.Vendor

end
