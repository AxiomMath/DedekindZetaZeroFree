module

public import DedekindZetaZeroFree.Moments.Probes.PrincipalProbeAndSeparatedMellinSeries

@[expose] public section

namespace DedekindZetaZeroFree.ProbePoissonGaussianRowBound

noncomputable section
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

theorem gaussian_power_bound (L x : ℝ) (hx : 0 < x) :
    x ^ L * |thetaReflectionGaussian x| ≤
      Real.exp (L ^ 2) / (2 * Real.sqrt Real.pi) := by
  rw [thetaReflectionGaussian_of_pos x hx,
    abs_of_pos (div_pos (Real.exp_pos _) (mul_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos))),
    Real.rpow_def_of_pos hx, ← mul_div_assoc, ← Real.exp_add]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.log x - 2 * L)]

def rowMass (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (σ Z : ℝ) (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) : ℝ :=
  ‖ThetaReflectionData.forwardArithmeticWeight A D c n‖ /
      (Real.sqrt (A.exteriorNorm c.val) * A.exteriorNorm n) *
    (A.exteriorNorm c.val * A.exteriorNorm n ^ 3) ^ σ *
    |thetaReflectionGaussian (A.exteriorNorm c.val * A.exteriorNorm n ^ 3 / Z)|

private theorem mulChar_bound {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (r : R) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    exact (Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)).le
  · simp [χ.map_nonunit hr]
private theorem phase_norm (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (x : SLocalProduct F A.Sf) : ‖ProbeAdditive.phase F A.Sf e x‖ = 1 := by
  simp [ProbeAdditive.phase, ProbeAdditive.archPhase, norm_mul, norm_prod,
    Complex.norm_exp]
private theorem gamma_bound (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (c : ExteriorSquarefreeIdeal A.cS) :
    ‖P.coefficients.gammaTwo c‖ ≤ Real.sqrt (A.exteriorNorm c.val) := by
  let D := P.coefficients
  letI := D.finiteResidue (D.generator c.val) (D.generates c.val).1
  have hc : (Fintype.card (FiniteTransform.Residue A.R.toSubring (D.generator c.val)) : ℝ) =
      A.exteriorNorm c.val := by
    rw [Fintype.card_eq_nat_card]
    change (Nat.card (A.R ⧸ Ideal.span {D.generator c.val}) : ℝ) = _
    rw [(D.generates c.val).2, A.exteriorResidue_card]
    rfl
  have hsum : ‖FiniteTransform.gaussSum A.R.toSubring (D.generator c.val)
      (D.character (D.generator c.val) ^ 2) D.additiveCharacter 1‖ ≤ A.exteriorNorm c.val := by
    unfold FiniteTransform.gaussSum FiniteTransform.gaussSumWithLifts
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _ : FiniteTransform.Residue A.R.toSubring (D.generator c.val), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [norm_mul, P.sameTrace, phase_norm, mul_one]
        exact mulChar_bound _ _
      _ = _ := by simpa using hc
  rw [P.gammaTwo_recipe c]
  change ‖(Real.sqrt (A.exteriorNorm c.val) : ℂ)⁻¹ * _‖ ≤ _
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hq := A.exteriorNorm_pos c.val
  have hsq := Real.sqrt_pos.mpr hq
  calc
    _ ≤ (Real.sqrt (A.exteriorNorm c.val))⁻¹ * A.exteriorNorm c.val :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hsq.le)
    _ = _ := by
      apply (inv_mul_eq_iff_eq_mul₀ hsq.ne').mpr
      exact (Real.sq_sqrt hq.le).symm.trans (by ring)
private theorem numeric_bound (σ Z qc qn : ℝ) (hZ : 0 < Z)
    (hc : 1 ≤ qc) (hn : 1 ≤ qn) :
    (1 / qn) * (qc * qn ^ 3) ^ σ *
      |thetaReflectionGaussian (qc * qn ^ 3 / Z)| ≤
    (Real.exp ((σ + 3) ^ 2) / (2 * Real.sqrt Real.pi) * Z ^ (σ + 3)) *
      qc ^ (-(5 / 2 : ℝ)) * qn ^ (-(7 : ℝ)) := by
  have hc0 : 0 < qc := by linarith
  have hn0 : 0 < qn := by linarith
  have hq : 0 < qc * qn ^ 3 := by positivity
  have hg := gaussian_power_bound (σ + 3) (qc * qn ^ 3 / Z) (div_pos hq hZ)
  have hb : |thetaReflectionGaussian (qc * qn ^ 3 / Z)| ≤
      (Real.exp ((σ + 3) ^ 2) / (2 * Real.sqrt Real.pi) * Z ^ (σ + 3)) /
        (qc * qn ^ 3) ^ (σ + 3) := by
    rw [Real.div_rpow hq.le hZ.le] at hg
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hq _)).mpr
    have hh := (mul_le_mul_of_nonneg_right hg (Real.rpow_pos_of_pos hZ (σ + 3)).le)
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hZ (σ + 3)).ne'] at hh
    simpa [mul_comm] using hh
  let C := Real.exp ((σ + 3) ^ 2) / (2 * Real.sqrt Real.pi) * Z ^ (σ + 3)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ (1 / qn) * (qc * qn ^ 3) ^ σ * (C / (qc * qn ^ 3) ^ (σ + 3)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C * qc ^ (-(3 : ℝ)) * qn ^ (-(10 : ℝ)) := by
      rw [show (1 / qn) * (qc * qn ^ 3) ^ σ * (C / (qc * qn ^ 3) ^ (σ + 3)) =
        C * ((qc * qn ^ 3) ^ σ / (qc * qn ^ 3) ^ (σ + 3)) / qn by ring,
        ← Real.rpow_sub hq, show σ - (σ + 3) = (-3 : ℝ) by ring,
        Real.mul_rpow hc0.le (by positivity)]
      rw [← Real.rpow_natCast qn 3, ← Real.rpow_mul hn0.le,
        show ((3 : ℕ) : ℝ) * -3 = -9 by norm_num,
        show C * (qc ^ (-3 : ℝ) * qn ^ (-9 : ℝ)) / qn =
          C * qc ^ (-3 : ℝ) * (qn ^ (-9 : ℝ) / qn ^ (1 : ℝ)) by rw [Real.rpow_one]; ring,
        ← Real.rpow_sub hn0]
      norm_num
    _ ≤ _ := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hc (by norm_num)) hC
      · exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
      · positivity
      · positivity
private theorem row_bound (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (σ Z : ℝ) (hZ : 0 < Z) (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) :
    rowMass A P.coefficients σ Z c n ≤
      (Real.exp ((σ + 3) ^ 2) / (2 * Real.sqrt Real.pi) * Z ^ (σ + 3)) *
        (A.exteriorNorm c.val) ^ (-(5 / 2 : ℝ)) * (A.exteriorNorm n) ^ (-(7 : ℝ)) := by
  have htheta : ‖P.coefficients.theta (ThetaReflectionData.forwardModulus A P.coefficients c n)‖ = 1 := by
    let m : ThetaReflectionData.Row A :=
      ⟨ThetaReflectionData.forwardModulus A P.coefficients c n,
        mul_ne_zero (P.coefficients.generates c.val).1 (pow_ne_zero _ (P.coefficients.generates n).1)⟩
    exact (congrArg norm (P.theta_principal m)).trans (Circle.norm_coe _)
  have hw : ‖ThetaReflectionData.forwardArithmeticWeight A P.coefficients c n‖ ≤
      Real.sqrt (A.exteriorNorm c.val) := by
    rw [ThetaReflectionData.forwardArithmeticWeight, norm_mul, htheta, mul_one]
    exact gamma_bound A ι η hS P c
  have hc := A.exteriorNorm_pos c.val
  have hn := A.exteriorNorm_pos n
  have hd : ‖ThetaReflectionData.forwardArithmeticWeight A P.coefficients c n‖ /
      (Real.sqrt (A.exteriorNorm c.val) * A.exteriorNorm n) ≤ 1 / A.exteriorNorm n := by
    apply (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hc) hn)).mpr
    convert hw using 1 <;> field_simp
  calc
    _ ≤ (1 / A.exteriorNorm n) *
        (A.exteriorNorm c.val * A.exteriorNorm n ^ 3) ^ σ *
        |thetaReflectionGaussian (A.exteriorNorm c.val * A.exteriorNorm n ^ 3 / Z)| := by
      unfold rowMass
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (by positivity)) (abs_nonneg _)
    _ ≤ _ := numeric_bound σ Z _ _ hZ
      (idealNorm_ge_one _ c.val.property.1) (idealNorm_ge_one _ n.property.1)

theorem gaussian_row_domination
    (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (σ Z : ℝ) (hσ : 1 < σ) (hZ : 0 < Z) :
    ∃ C : ℝ, 0 < C ∧
      ∀ P : NormalizedProbe.PrincipalData A ι η hS,
        (∀ (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior),
          rowMass A P.coefficients σ Z c n ≤
            C * (A.exteriorNorm c.val) ^ (-(5 / 2 : ℝ)) *
              (A.exteriorNorm n) ^ (-(7 : ℝ))) ∧
        Summable (fun c : ExteriorSquarefreeIdeal A.cS =>
          (A.exteriorNorm c.val) ^ (-(5 / 2 : ℝ))) ∧
        Summable (fun n : A.Exterior => (A.exteriorNorm n) ^ (-(7 : ℝ))) ∧
        Summable (fun i : ExteriorSquarefreeIdeal A.cS × A.Exterior =>
          rowMass A P.coefficients σ Z i.1 i.2) ∧
        (∑' i : ExteriorSquarefreeIdeal A.cS × A.Exterior,
          rowMass A P.coefficients σ Z i.1 i.2) ≤
          C * (∑' c : ExteriorSquarefreeIdeal A.cS,
            (A.exteriorNorm c.val) ^ (-(5 / 2 : ℝ))) *
            (∑' n : A.Exterior, (A.exteriorNorm n) ^ (-(7 : ℝ))) := by
  let C := Real.exp ((σ + 3) ^ 2) / (2 * Real.sqrt Real.pi) * Z ^ (σ + 3)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro P
  have hb := row_bound A ι η hS P σ Z hZ
  let f : ExteriorSquarefreeIdeal A.cS → ℝ := fun c => (A.exteriorNorm c.val) ^ (-(5 / 2 : ℝ))
  let g : A.Exterior → ℝ := fun n => (A.exteriorNorm n) ^ (-(7 : ℝ))
  have hf : Summable f :=
    (ProbeExteriorIdealCount.ideal_norm_summable F A.cS (5 / 2) (by norm_num)).comp_injective
      Subtype.val_injective
  have hg : Summable g := ProbeExteriorIdealCount.ideal_norm_summable F A.cS 7 (by norm_num)
  have hf0 : ∀ c, 0 ≤ f c := fun c => Real.rpow_nonneg (A.exteriorNorm_pos c.val).le _
  have hg0 : ∀ n, 0 ≤ g n := fun n => Real.rpow_nonneg (A.exteriorNorm_pos n).le _
  have hfg : Summable (fun i : ExteriorSquarefreeIdeal A.cS × A.Exterior => f i.1 * g i.2) :=
    summable_mul_of_summable_norm
      (by simpa only [Real.norm_of_nonneg (hf0 _)] using hf)
      (by simpa only [Real.norm_of_nonneg (hg0 _)] using hg)
  have hmajor : Summable (fun i : ExteriorSquarefreeIdeal A.cS × A.Exterior => C * f i.1 * g i.2) := by
    simpa only [mul_assoc] using hfg.mul_left C
  have hm0 : ∀ i : ExteriorSquarefreeIdeal A.cS × A.Exterior,
      0 ≤ rowMass A P.coefficients σ Z i.1 i.2 := by
    intro i
    unfold rowMass
    have hc := A.exteriorNorm_pos i.1.val
    have hn := A.exteriorNorm_pos i.2
    positivity
  have hm := hmajor.of_nonneg_of_le hm0 (fun i => hb i.1 i.2)
  refine ⟨hb, hf, hg, hm, ?_⟩
  calc
    _ ≤ ∑' i : ExteriorSquarefreeIdeal A.cS × A.Exterior, C * f i.1 * g i.2 :=
      hm.tsum_le_tsum (fun i => hb i.1 i.2) hmajor
    _ = _ := by
      simp_rw [mul_assoc, tsum_mul_left]
      rw [← hf.tsum_mul_tsum hg hfg]

end
end DedekindZetaZeroFree.ProbePoissonGaussianRowBound
