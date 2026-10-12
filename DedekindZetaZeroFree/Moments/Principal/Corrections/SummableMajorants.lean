module

public import DedekindZetaZeroFree.Arithmetic.Ideals.PrimeNormSummability
public import DedekindZetaZeroFree.Moments.Principal.Corrections.LocalNonvanishing

@[expose] public section

namespace DedekindZetaZeroFree

open NumberField IsDedekindDomain

private lemma exp_norm_bound (Q t u : ℝ) (hQ : 2 ≤ Q) (htu : t ≤ u)
    (a : ℂ) (ha : ‖a‖ = 1) (z : ℂ) (hz : z.re = t) :
    ‖a * Complex.exp (z * (Real.log Q : ℂ))‖ ≤ Real.rpow Q u := by
  rw [norm_mul, ha, one_mul, Complex.norm_exp]
  have hpos : 0 < Q := by linarith
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hpos]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hz]
  apply Real.exp_le_exp.mpr
  simpa [mul_comm] using mul_le_mul_of_nonneg_right htu (Real.log_nonneg (show 1 ≤ Q by linarith))

private lemma numerator_bound (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1/2)
    (D E : ℂ) (hD : ‖D‖ ≤ 1) :
    ‖-(r : ℂ)^2 + ((r : ℂ)+(r : ℂ)^2-(r : ℂ)^3)*D +
      (1-(r : ℂ)+(r : ℂ)^3)*E-E*D‖ ≤
      r^2 + 2*r*‖D‖ + 3*‖E‖ := by
  have hc : ‖(r : ℂ)+(r : ℂ)^2-(r : ℂ)^3‖ ≤ 2*r := by
    have he : (r : ℂ)+(r : ℂ)^2-(r : ℂ)^3 = ((r+r^2-r^3 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    have hr2 : r^2 ≤ r := by nlinarith
    have hr3 : 0 ≤ r^3 := by positivity
    have hr32 : r^3 ≤ r^2 := by nlinarith [mul_nonneg (sq_nonneg r) (by linarith : 0 ≤ 1-r)]
    rw [abs_of_nonneg (by linarith)]
    nlinarith
  have hc' : ‖1-(r : ℂ)+(r : ℂ)^3‖ ≤ 2 := by
    have he : 1-(r : ℂ)+(r : ℂ)^3 = ((1-r+r^3 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith [show 0 ≤ r^3 by positivity]) ]
    have hr2 : r^2 ≤ r := by nlinarith
    have hr32 : r^3 ≤ r^2 := by nlinarith [mul_nonneg (sq_nonneg r) (by linarith : 0 ≤ 1-r)]
    linarith
  calc
    _ ≤ ‖-(r : ℂ)^2 + ((r : ℂ)+(r : ℂ)^2-(r : ℂ)^3)*D +
        (1-(r : ℂ)+(r : ℂ)^3)*E‖ + ‖E*D‖ := norm_sub_le _ _
    _ ≤ (‖-(r : ℂ)^2 + ((r : ℂ)+(r : ℂ)^2-(r : ℂ)^3)*D‖ +
        ‖(1-(r : ℂ)+(r : ℂ)^3)*E‖) + ‖E*D‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖-(r : ℂ)^2‖ + ‖((r : ℂ)+(r : ℂ)^2-(r : ℂ)^3)*D‖) +
        ‖(1-(r : ℂ)+(r : ℂ)^3)*E‖) + ‖E*D‖ := by gcongr; exact norm_add_le _ _
    _ = r^2 + ‖(r : ℂ)+(r : ℂ)^2-(r : ℂ)^3‖*‖D‖ +
        ‖1-(r : ℂ)+(r : ℂ)^3‖*‖E‖ + ‖E‖*‖D‖ := by
      simp [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    _ ≤ r^2 + (2*r)*‖D‖ + 2*‖E‖ + ‖E‖*1 := by gcongr
    _ = _ := by ring

theorem principal_local_majorant (σ₀ : ℝ) (hσ₀ : (2 : ℝ) / 3 < σ₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ), 2 ≤ Q →
      ∀ (α β : ℂ), ‖α‖ = 1 → ‖β‖ = 1 → ∀ (s : ℂ), σ₀ ≤ s.re →
        let D := α * Complex.exp (-s * (Real.log Q : ℂ))
        let E := β * Complex.exp ((3 - 6 * s) * (Real.log Q : ℂ))
        let h := Audit.Euler.principalCorrection (Q : ℂ)⁻¹ D E
        ‖h - 1‖ ≤ C * (Real.rpow Q (-2) + Real.rpow Q (-1 - σ₀) +
          Real.rpow Q (3 - 6 * σ₀)) ∧
        ‖h⁻¹ - 1‖ ≤ C * (Real.rpow Q (-2) + Real.rpow Q (-1 - σ₀) +
          Real.rpow Q (3 - 6 * σ₀)) := by
  let δ := CorrectionFactors.principalGap σ₀
  have hδ : 0 < δ := CorrectionFactors.principalGap_pos σ₀ (by linarith)
  let K := 3 / δ^2
  let L := 3 * δ / 16
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨K + K / L, by positivity, ?_⟩
  intro Q hQ α β hα hβ s hs
  dsimp only
  let D := α * Complex.exp (-s * (Real.log Q : ℂ))
  let E := β * Complex.exp ((3 - 6 * s) * (Real.log Q : ℂ))
  let r : ℝ := Q⁻¹
  let h := Audit.Euler.principalCorrection (Q : ℂ)⁻¹ D E
  let M := Real.rpow Q (-2) + Real.rpow Q (-1 - σ₀) + Real.rpow Q (3 - 6 * σ₀)
  have hQpos : 0 < Q := by linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr' : r ≤ 1/2 := by dsimp [r]; exact (inv_le_comm₀ hQpos (by norm_num)).mpr (by norm_num; exact hQ)
  have hD : ‖D‖ ≤ Real.rpow Q (-σ₀) :=
    exp_norm_bound Q (-s.re) (-σ₀) hQ (by linarith) α hα (-s) (by simp)
  have hE : ‖E‖ ≤ Real.rpow Q (3 - 6 * σ₀) :=
    exp_norm_bound Q (3 - 6*s.re) (3 - 6*σ₀) hQ (by linarith) β hβ (3 - 6*s) (by simp)
  have hD1 : ‖D‖ ≤ 1 := by
    apply hD.trans
    rw [Real.rpow_eq_pow]
    simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ Q by linarith) (show -σ₀ ≤ 0 by linarith)
  have hb := CorrectionFactors.principalModel_uniform_lower_bounds σ₀ (by linarith) Q hQ α β hα hβ s hs
  change L ≤ ‖h‖ ∧ δ ≤ ‖1-E‖ ∧ δ ≤ ‖1-D‖ at hb
  have hDne : 1-D ≠ 0 := by intro hz; rw [hz, norm_zero] at hb; linarith [hb.2.2]
  have hEne : 1-E ≠ 0 := by intro hz; rw [hz, norm_zero] at hb; linarith [hb.2.1]
  have hne : h ≠ 0 := by intro hz; rw [hz, norm_zero] at hb; linarith [hb.1]
  have hn : ((1-E)*(1-D))*(h-1) =
      -(r : ℂ)^2 + ((r : ℂ)+(r : ℂ)^2-(r : ℂ)^3)*D +
        (1-(r : ℂ)+(r : ℂ)^3)*E-E*D := by
    dsimp [h]
    unfold Audit.Euler.principalCorrection
    rw [div_sub_one (mul_ne_zero hEne hDne), mul_div_cancel₀ _ (mul_ne_zero hEne hDne)]
    simpa [r, Complex.ofReal_inv] using Audit.Euler.principalCorrection_numerator_subtraction (Q : ℂ)⁻¹ D E
  have hnum : ‖((1-E)*(1-D))*(h-1)‖ ≤ 3*M := by
    rw [hn]
    apply (numerator_bound r hr hr' D E hD1).trans
    have he1 : r^2 = Real.rpow Q (-2) := by
      rw [Real.rpow_eq_pow]
      simpa [r, Real.rpow_neg_one] using (Real.rpow_mul_natCast hQpos.le (-1) 2).symm
    have he2 : r * Real.rpow Q (-σ₀) = Real.rpow Q (-1-σ₀) := by
      simp only [Real.rpow_eq_pow]
      rw [show -1-σ₀ = (-1)+(-σ₀) by ring, Real.rpow_add hQpos, Real.rpow_neg_one]
    have he3 : r*‖D‖ ≤ Real.rpow Q (-1-σ₀) := by rw [← he2]; gcongr
    have hm2 : 0 ≤ Real.rpow Q (-2) := Real.rpow_nonneg hQpos.le _
    have hm1 : 0 ≤ Real.rpow Q (-1-σ₀) := Real.rpow_nonneg hQpos.le _
    change r^2 + 2*r*‖D‖ + 3*‖E‖ ≤ 3*(Real.rpow Q (-2) + Real.rpow Q (-1-σ₀) + Real.rpow Q (3-6*σ₀))
    nlinarith
  have hden : δ^2 ≤ ‖(1-E)*(1-D)‖ := by
    rw [norm_mul, pow_two]
    exact mul_le_mul hb.2.1 hb.2.2 hδ.le (norm_nonneg _)
  have hh : ‖h-1‖ ≤ K*M := by
    have he : δ^2 * ‖h-1‖ ≤ 3*M := by
      calc
        _ ≤ ‖(1-E)*(1-D)‖*‖h-1‖ := mul_le_mul_of_nonneg_right hden (norm_nonneg _)
        _ = ‖((1-E)*(1-D))*(h-1)‖ := (norm_mul _ _).symm
        _ ≤ _ := hnum
    have he' : ‖h-1‖ ≤ (3*M)/δ^2 := (le_div_iff₀ (sq_pos_of_pos hδ)).mpr (by simpa [mul_comm] using he)
    simpa [K, div_mul_eq_mul_div] using he'
  have hinv : ‖h⁻¹-1‖ ≤ (K/L)*M := by
    have he : h*(h⁻¹-1) = -(h-1) := by field_simp; ring
    have hn := congrArg norm he
    rw [norm_mul, norm_neg] at hn
    have he' : L*‖h⁻¹-1‖ ≤ K*M := by
      calc
        _ ≤ ‖h‖*‖h⁻¹-1‖ := mul_le_mul_of_nonneg_right hb.1 (norm_nonneg _)
        _ = ‖h-1‖ := hn
        _ ≤ _ := hh
    have : ‖h⁻¹-1‖ ≤ (K*M)/L := (le_div_iff₀ hL).mpr (by simpa [mul_comm] using he')
    simpa [div_mul_eq_mul_div] using this
  have hM : 0 ≤ M := by dsimp [M]; positivity
  constructor
  · exact hh.trans (by nlinarith [show 0 ≤ K/L by positivity])
  · exact hinv.trans (by nlinarith)

theorem principal_majorant_summable
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (σ₀ : ℝ) (hσ₀ : (2 : ℝ) / 3 < σ₀) :
    Summable (fun p : {p : HeightOneSpectrum (RingOfIntegers F) // p ∉ S} =>
      Real.rpow (idealNorm p.val.asIdeal) (-2) +
      Real.rpow (idealNorm p.val.asIdeal) (-1 - σ₀) +
      Real.rpow (idealNorm p.val.asIdeal) (3 - 6 * σ₀)) := by
  have h₂ := summable_exterior_prime_norm_rpow F S 2 (by norm_num)
  have h₁ := summable_exterior_prime_norm_rpow F S (1 + σ₀) (by linarith)
  have h₃ := summable_exterior_prime_norm_rpow F S (6 * σ₀ - 3) (by linarith)
  have he : -(1 + σ₀) = -1 - σ₀ := by ring
  convert (h₂.add h₁).add h₃ using 1 <;>
    simp only [idealNorm, he, neg_sub, neg_neg, Real.rpow_eq_pow]

end DedekindZetaZeroFree
