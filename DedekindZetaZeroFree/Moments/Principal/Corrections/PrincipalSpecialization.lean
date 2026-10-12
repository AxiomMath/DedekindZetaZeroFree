module

public import DedekindZetaZeroFree.Moments.Principal.EulerCorrectionAlgebra
public import DedekindZetaZeroFree.Moments.Principal.Corrections.NormalProductConvergence

@[expose] public section

open scoped NumberField Classical

noncomputable section
namespace DedekindZetaZeroFree.CorrectionFactors
set_option autoImplicit false

def principalRational (Q : ℝ) (d e : ℂ) : ℂ :=
  let r : ℂ := (Q : ℂ)⁻¹
  1 / (1 - r) + r / (1 - r) +
    e / (1 - e) * ((1 - r) / (1 - r) + r) -
    d / (1 - e) * (1 + ((Q : ℂ) - 1) * r * r / (1 - r))

def principalCorrection (Q : ℝ) (d e : ℂ) : ℂ :=
  (1 - (Q : ℂ)⁻¹) ^ 2 * principalRational Q d e / (1 - d)

theorem principal_rational_specialization (Q : ℝ) (hQ : 2 ≤ Q)
    (d e : ℂ) (hd : d ≠ 1) (he : e ≠ 1) :
    let r : ℂ := (Q : ℂ)⁻¹
    principalRational Q d e =
      (1 + r) / (1 - r) + (1 + r) * (e - d) / (1 - e) := by
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by linarith)
  have hr : 1 - (Q : ℂ)⁻¹ ≠ 0 := sub_ne_zero.mpr
    (Ne.symm (inv_ne_one.mpr (by exact_mod_cast (show Q ≠ 1 by linarith))))
  have he' : 1 - e ≠ 0 := sub_ne_zero.mpr he.symm
  dsimp [principalRational]
  have hQ1 : (Q : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr
    (by exact_mod_cast (show Q ≠ 1 by linarith))
  field_simp [hQ0, hr, he', hQ1]
  <;> field_simp [hQ1]
  <;> ring

theorem principal_correction_formula (Q : ℝ) (hQ : 2 ≤ Q)
    (d e : ℂ) (hd : d ≠ 1) (he : e ≠ 1) :
    let r : ℂ := (Q : ℂ)⁻¹
    principalCorrection Q d e =
      (1 - r ^ 2) * (1 - (1 - r) * d - r * e) /
        ((1 - e) * (1 - d)) := by
  have hr : 1 - (Q : ℂ)⁻¹ ≠ 0 := sub_ne_zero.mpr
    (Ne.symm (inv_ne_one.mpr (by exact_mod_cast (show Q ≠ 1 by linarith))))
  have hd' : 1 - d ≠ 0 := sub_ne_zero.mpr hd.symm
  have he' : 1 - e ≠ 0 := sub_ne_zero.mpr he.symm
  unfold principalCorrection
  rw [principal_rational_specialization Q hQ d e hd he]
  exact Audit.Euler.principalCorrection_identity (Q : ℂ)⁻¹ d e hr hd' he'

open LocalFiniteSums

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private lemma principal_Q_ge_two (p : ExteriorPrime A) : 2 ≤ Q p := by
  change (2 : ℝ) ≤ (Ideal.absNorm p.val.asIdeal : ℝ)
  exact_mod_cast (show 2 ≤ Ideal.absNorm p.val.asIdeal from
    NumberField.HeightOneSpectrum.one_lt_absNorm p.val)

private lemma principal_qPower_mul (p : ExteriorPrime A) (s t : ℂ) :
    qPower p s * qPower p t = qPower p (s + t) := by
  simp only [qPower, add_mul, Complex.exp_add]

private lemma principal_qPower_neg_one (p : ExteriorPrime A) :
    qPower p (-1) = (Q p : ℂ)⁻¹ := by
  have hQ : 0 < Q p := by have := principal_Q_ge_two p; linarith
  simp only [qPower, neg_one_mul, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hQ]

private lemma principal_denominators (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (s : ℂ) (hs : (2 / 3 : ℝ) < s.re) :
    η p.val.asIdeal * qPower p (-s) ≠ 1 ∧
      vartheta C p ^ 6 * qPower p (3 - 6 * s) ≠ 1 := by
  have hlog : 0 < Real.log (Q p) := Real.log_pos (by
    have := principal_Q_ge_two p; linarith)
  have hn (t : ℂ) : ‖qPower p t‖ = Real.exp (t.re * Real.log (Q p)) := by
    simp [qPower, Complex.norm_exp]
  have hη := RayUnitary.ray_character_norm_le_one F A.modulus A.modulus_ne_zero η p.val.asIdeal
  have hd : ‖η p.val.asIdeal * qPower p (-s)‖ < 1 := by
    rw [norm_mul, hn]
    calc
      ‖η p.val.asIdeal‖ * Real.exp ((-s).re * Real.log (Q p)) ≤
          1 * Real.exp ((-s).re * Real.log (Q p)) :=
        mul_le_mul_of_nonneg_right hη (Real.exp_pos _).le
      _ < 1 := by
        simp only [one_mul, Complex.neg_re]
        exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith) hlog)
  have he : ‖vartheta C p ^ 6 * qPower p (3 - 6 * s)‖ < 1 := by
    rw [norm_mul, norm_pow, show ‖vartheta C p‖ = 1 from Circle.norm_coe _, hn]
    simp only [one_pow, one_mul]
    apply Real.exp_lt_one_iff.mpr
    apply mul_neg_of_neg_of_pos _ hlog
    norm_num [Complex.sub_re, Complex.mul_re]
    linarith
  constructor
  · intro h; simpa [h] using hd
  · intro h; simpa [h] using he

theorem principal_correction_eq_h_p (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (s : ℂ) (hs : (2 / 3 : ℝ) < s.re) :
    principalCorrection (Q p) (η p.val.asIdeal * qPower p (-s))
      (vartheta C p ^ 6 * qPower p (3 - 6 * s)) = h_p C p s := by
  obtain ⟨hd, he⟩ := principal_denominators C p s hs
  rw [principal_correction_formula (Q p) (principal_Q_ge_two p) _ _ hd he]
  have h2 : qPower p (-2) = (Q p : ℂ)⁻¹ ^ 2 := by
    rw [pow_two, ← principal_qPower_neg_one, principal_qPower_mul]
    congr 1
    ring
  have he2 : (Q p : ℂ)⁻¹ * qPower p (3 - 6 * s) = qPower p (2 - 6 * s) := by
    rw [← principal_qPower_neg_one, principal_qPower_mul]
    congr 1
    ring
  unfold h_p
  rw [h2, principal_qPower_neg_one]
  congr 2
  calc
    _ = 1 - (1 - (Q p : ℂ)⁻¹) * η p.val.asIdeal * qPower p (-s) -
        vartheta C p ^ 6 * ((Q p : ℂ)⁻¹ * qPower p (3 - 6 * s)) := by ring
    _ = _ := by rw [he2]

theorem principal_goodFactor_eq_h_p (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (s : ℂ) (hs : (2 / 3 : ℝ) < s.re) :
    goodFactor C p (1 : A.R) s 1 (1 / 6) = h_p C p s := by
  have hv : V p (1 / 6) = (Q p : ℂ)⁻¹ := by
    unfold V
    norm_num
    exact principal_qPower_neg_one p
  have hw : W (σ := σ) p (1 : A.R) 1 = (Q p : ℂ)⁻¹ := by
    simp [W, principal_qPower_neg_one]
  have hd : D (σ := σ) (η := η) p (1 : A.R) s =
      η p.val.asIdeal * qPower p (-s) := by simp [D]
  have he : E C p s (1 / 6) = vartheta C p ^ 6 * qPower p (3 - 6 * s) := by
    unfold E
    rw [hv, ← principal_qPower_neg_one, mul_assoc, principal_qPower_mul]
    congr 2
    ring
  rw [← principal_correction_eq_h_p C p s hs]
  simp only [goodFactor, goodRational, hv, hw, hd, he, principalCorrection,
    principalRational]
  ring

theorem principal_localFactor_eq_h_p (C : A.GeneralArithmeticContext σ η hS)
    (U : Frequency C) (hU : U.u = 1) (p : ExteriorPrime A)
    (s : ℂ) (hs : (2 / 3 : ℝ) < s.re) :
    localFactor C U p s 1 (1 / 6) = h_p C p s := by
  have hext : A.extendIdeal U.ideal = ⊤ := by
    rw [← U.generates.2, hU, Ideal.span_singleton_one]
  have hcard : Ideal.absNorm U.ideal.val = 1 := by
    rw [← A.exteriorResidue_card U.ideal]
    letI : Subsingleton (A.R ⧸ A.extendIdeal U.ideal) :=
      Ideal.Quotient.subsingleton_iff.mpr hext
    exact Nat.card_unique
  have hideal : U.ideal.val = ⊤ := Ideal.absNorm_eq_one_iff.mp hcard
  have hj : (U.j p).val = 0 := by
    simp [Frequency.j, idealPrimeExponent, hideal, ← Ideal.one_eq_top]
  simp only [localFactor, hj, if_true, hU]
  exact principal_goodFactor_eq_h_p C p s hs

theorem principal_product_specialization (C : A.GeneralArithmeticContext σ η hS)
    (U : Frequency C) (hU : U.u = 1) (s : ℂ)
    (hs : (499 / 500 : ℝ) - 1 / 100000 < s.re) :
    ∃ hm : Multipliable (fun p : ExteriorPrime A => localFactor C U p s 1 (1 / 6)),
      H_u C U s 1 (1 / 6) hm = H_eta C s := by
  have hx : (s, (1 : ℂ), (1 / 6 : ℂ)) ∈ Omega := by
    apply Or.inr
    change (499 / 500 : ℝ) - 1 / 100000 < s.re ∧
      (19 / 20 : ℝ) - 1 / 100000 < (1 : ℂ).re ∧
      (4 / 25 : ℝ) - 1 / 100000 < (1 / 6 : ℂ).re
    refine ⟨hs, ?_, ?_⟩ <;> norm_num
  refine ⟨multipliable_localFactor C U (s, 1, 1 / 6) hx, ?_⟩
  unfold H_u H_eta
  apply tprod_congr
  intro p
  apply principal_localFactor_eq_h_p C U hU p s
  linarith

end DedekindZetaZeroFree.CorrectionFactors

end
