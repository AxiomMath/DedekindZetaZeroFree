module

public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.LatitudeDisintegration
public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.SmoothPolynomialDensity

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke.CircleAverage
open MeasureTheory KPCplxIntertwinerEigenvalues
open scoped BigOperators

private lemma shift (f : ℝ → ℂ) (hf : Function.Periodic f (2 * Real.pi)) (θ : ℝ) :
    (∫ t, f (θ + t) ∂angleMeasure) = ∫ t, f t ∂angleMeasure := by
  rw [angleMeasure, integral_smul_measure, integral_smul_measure]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity),
    ← intervalIntegral.integral_of_le (by positivity)]
  simp_rw [add_comm θ]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm θ] using hf.intervalIntegral_add_eq θ 0
noncomputable def moment (i j : ℕ) : ℂ :=
  ∫ θ : ℝ, (Real.cos θ : ℂ)^i * (Real.sin θ : ℂ)^j ∂angleMeasure
private lemma moment_odd (i j : ℕ) (h : Odd (i+j)) : moment i j = 0 := by
  let f : ℝ → ℂ := fun θ => (Real.cos θ : ℂ)^i * (Real.sin θ : ℂ)^j
  have hp : Function.Periodic f (2*Real.pi) := by
    intro θ
    dsimp only [f]
    rw [Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hn (θ : ℝ) : f (Real.pi + θ) = - f θ := by
    dsimp only [f]
    rw [add_comm Real.pi, Real.cos_add_pi, Real.sin_add_pi]
    simp only [Complex.ofReal_neg]
    rw [neg_eq_neg_one_mul (Real.cos θ : ℂ), neg_eq_neg_one_mul (Real.sin θ : ℂ),
      mul_pow, mul_pow]
    calc
      (-1 : ℂ)^i * (Real.cos θ : ℂ)^i * ((-1 : ℂ)^j * (Real.sin θ : ℂ)^j) =
          (-1 : ℂ)^(i+j) * ((Real.cos θ : ℂ)^i * (Real.sin θ : ℂ)^j) := by rw [pow_add]; ring
      _ = - ((Real.cos θ : ℂ)^i * (Real.sin θ : ℂ)^j) := by rw [h.neg_one_pow]; ring
  have he := shift f hp Real.pi
  simp_rw [hn] at he
  rw [integral_neg] at he
  change -moment i j = moment i j at he
  linear_combination -he / 2
private lemma mono_formula (d : Fin 3 →₀ ℕ) (a : ℂ) (u θ : ℝ)
    (hu : u ∈ Set.Icc (0:ℝ) 1) :
    polynomialSphere (MvPolynomial.monomial d a) (latitudePoint (.refl ℝ Ambient) u θ) =
      a * ((1-2*u : ℝ):ℂ)^(d 0) * (Real.sqrt (4*u*(1-u)) : ℂ)^(d 1+d 2) *
        ((Real.cos θ : ℂ)^(d 1) * (Real.sin θ : ℂ)^(d 2)) := by
  rw [polynomialSphere, MvPolynomial.eval_monomial, latitudePoint_val _ _ _ hu]
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp [latitudeAmbient, Fin.prod_univ_succ, mul_pow, pow_add]
  ring
private lemma mono_integral (d : Fin 3 →₀ ℕ) (a : ℂ) (u : ℝ)
    (hu : u ∈ Set.Icc (0:ℝ) 1) :
    (∫ θ : ℝ, polynomialSphere (MvPolynomial.monomial d a)
      (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) =
      a * ((1-2*u : ℝ):ℂ)^(d 0) * (Real.sqrt (4*u*(1-u)) : ℂ)^(d 1+d 2) * moment (d 1) (d 2) := by
  simp_rw [mono_formula d a u _ hu]
  exact integral_const_mul _ _
private lemma poly_integrable (p : MvPolynomial (Fin 3) ℂ) (u : ℝ)
    (hu : u ∈ Set.Icc (0:ℝ) 1) :
    Integrable (fun θ => polynomialSphere p (latitudePoint (.refl ℝ Ambient) u θ)) angleMeasure := by
  have hc : Continuous (fun θ => polynomialSphere p (latitudePoint (.refl ℝ Ambient) u θ)) := by
    simp only [polynomialSphere, latitudePoint_val _ _ _ hu]
    apply (MvPolynomial.continuous_eval p).comp
    apply continuous_pi
    intro i
    fin_cases i <;> change Continuous _ <;> dsimp [latitudeAmbient]
    all_goals fun_prop
  exact (hc.integrableOn_Icc).smul_measure (by simp [ENNReal.inv_ne_top]; positivity)
private lemma exists_profile (p : MvPolynomial (Fin 3) ℂ) :
    ∃ Q : Polynomial ℂ, ∀ u : ℝ, u ∈ Set.Icc (0:ℝ) 1 →
      (∫ θ : ℝ, polynomialSphere p (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) = Q.eval (u:ℂ) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    rcases Nat.even_or_odd (d 1 + d 2) with he | ho
    · obtain ⟨k, hk⟩ := he
      refine ⟨Polynomial.C (a * moment (d 1) (d 2)) *
        (1 - Polynomial.C 2 * Polynomial.X)^(d 0) *
        (Polynomial.C 4 * Polynomial.X * (1-Polynomial.X))^k, ?_⟩
      intro u hu
      rw [mono_integral d a u hu]
      have hs : (Real.sqrt (4*u*(1-u)) : ℂ)^(d 1+d 2) = ((4*u*(1-u) : ℝ):ℂ)^k := by
        rw [hk, ← two_mul, pow_mul]
        rw [← Complex.ofReal_pow, Real.sq_sqrt (by nlinarith [hu.1, hu.2])]
      rw [hs]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
        Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
      ring
    · refine ⟨0, ?_⟩
      intro u hu
      rw [mono_integral d a u hu, moment_odd _ _ ho]
      simp
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨Q, hQ⟩ := hq
    refine ⟨P+Q, ?_⟩
    intro u hu
    simp only [polynomialSphere, map_add]
    change (∫ θ : ℝ, polynomialSphere p (latitudePoint (.refl ℝ Ambient) u θ) +
      polynomialSphere q (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) = _
    rw [integral_add (poly_integrable p u hu) (poly_integrable q u hu)]
    exact (congrArg₂ (· + ·) (hP u hu) (hQ u hu)).trans (Polynomial.eval_add).symm

theorem latitude_average_polynomial (p : MvPolynomial (Fin 3) ℂ) :
    ∃ Q : Polynomial ℂ,
      (∀ (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
        (∫ θ : ℝ, polynomialSphere p
          (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) = Q.eval (u : ℂ)) ∧
      Q.eval 0 = polynomialSphere p
        ⟨north, mem_sphere_zero_iff_norm.mpr north_norm⟩ := by
  obtain ⟨Q,hQ⟩ := exists_profile p
  refine ⟨Q,hQ,?_⟩
  have hm : angleMeasure Set.univ = 1 := by
    rw [angleMeasure, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Icc]
    simp only [sub_zero, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)
  have hz (θ : ℝ) : latitudePoint (.refl ℝ Ambient) 0 θ =
      ⟨north, mem_sphere_zero_iff_norm.mpr north_norm⟩ := by
    apply Subtype.ext
    rw [latitudePoint_val _ _ _ (by constructor <;> norm_num)]
    ext i
    fin_cases i <;> simp [latitudeAmbient, north, PiLp.single_apply]
  have he := hQ 0 (by constructor <;> norm_num)
  simp only [hz, Complex.ofReal_zero, integral_const, Measure.real, hm,
    ENNReal.toReal_one, one_smul] at he
  exact he.symm

end DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke.CircleAverage
