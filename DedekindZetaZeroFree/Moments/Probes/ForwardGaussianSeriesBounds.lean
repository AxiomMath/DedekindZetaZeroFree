module

public import DedekindZetaZeroFree.Moments.Probes.PrincipalArithmeticEnlargement
public import DedekindZetaZeroFree.CharacterSums.Gauss.Squarefree.PrincipalNormBound
public import DedekindZetaZeroFree.Moments.Probes.GaussianRowDomination

@[expose] public section

section

namespace DedekindZetaZeroFree.PoissonProbeDyadicMomentTransfer.ActualDyadicMomentSource
noncomputable section
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]

private theorem finite_mulChar_norm_le_one {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (r : R) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    exact (Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)).le
  · simp [χ.map_nonunit hr]

private theorem gaussian_square_norm_bound (qc qn Z : ℝ)
    (hc : 0 < qc) (hn : 0 < qn) (hZ : 0 < Z) :
    |thetaReflectionGaussian (qc * qn ^ 3 / Z)| / (Real.sqrt qc * qn) ≤
      (Real.exp 4 / (2 * Real.sqrt Real.pi) * Z ^ 2) *
        qc ^ (-(5 / 2 : ℝ)) * qn ^ (-(7 : ℝ)) := by
  have hq : 0 < qc * qn ^ 3 := by positivity
  have hg := ProbePoissonGaussianRowBound.gaussian_power_bound 2
    (qc * qn ^ 3 / Z) (div_pos hq hZ)
  rw [Real.rpow_two] at hg
  have hb : |thetaReflectionGaussian (qc * qn ^ 3 / Z)| ≤
      (Real.exp 4 / (2 * Real.sqrt Real.pi) * Z ^ 2) / (qc ^ 2 * qn ^ 6) := by
    apply (le_div_iff₀ (by positivity : 0 < qc ^ 2 * qn ^ 6)).mpr
    have hh := mul_le_mul_of_nonneg_right hg (sq_nonneg Z)
    have he : (qc * qn ^ 3 / Z) ^ 2 *
        |thetaReflectionGaussian (qc * qn ^ 3 / Z)| * Z ^ 2 =
        |thetaReflectionGaussian (qc * qn ^ 3 / Z)| * (qc ^ 2 * qn ^ 6) := by
      field_simp
    rw [he] at hh
    norm_num at hh ⊢
    exact hh
  calc
    _ ≤ ((Real.exp 4 / (2 * Real.sqrt Real.pi) * Z ^ 2) /
        (qc ^ 2 * qn ^ 6)) / (Real.sqrt qc * qn) :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = _ := by
      rw [show -(5 / 2 : ℝ) = -(2 + 1 / 2 : ℝ) by norm_num,
        Real.rpow_neg hc.le, Real.rpow_add hc, Real.rpow_two, ← Real.sqrt_eq_rpow,
        show -(7 : ℝ) = -((7 : ℕ) : ℝ) by norm_num, Real.rpow_neg hn.le,
        Real.rpow_natCast]
      field_simp

theorem forwardSummand_norm_summable_of_weight
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (hw : ∀ c n, ‖ThetaReflectionData.forwardArithmeticWeight A D c n‖ ≤ 1)
    (m : ThetaReflectionData.Row A) (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun i : ExteriorSquarefreeIdeal A.cS × A.Exterior =>
      ‖ThetaReflectionData.forwardSummand A D m Z i.1 i.2‖) := by
  have hb (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) :
      ‖ThetaReflectionData.forwardSummand A D m Z c n‖ ≤
        (Real.exp 4 / (2 * Real.sqrt Real.pi) * Z ^ 2) *
          (A.exteriorNorm c.val) ^ (-(5 / 2 : ℝ)) *
          (A.exteriorNorm n) ^ (-(7 : ℝ)) := by
    have hc := A.exteriorNorm_pos c.val
    have hn := A.exteriorNorm_pos n
    have hchar : ‖ThetaReflectionData.forwardRowCharacter A D c n m.val‖ ≤ 1 := by
      let a := ThetaReflectionData.forwardModulus A D c n
      have ha : a ≠ 0 := mul_ne_zero (D.generates c.val).1 (pow_ne_zero _ (D.generates n).1)
      letI := D.finiteResidue a ha
      exact finite_mulChar_norm_le_one _ _
    apply le_trans (b := |thetaReflectionGaussian
      (A.exteriorNorm c.val * A.exteriorNorm n ^ 3 / Z)| /
        (Real.sqrt (A.exteriorNorm c.val) * A.exteriorNorm n))
    · unfold ThetaReflectionData.forwardSummand
      rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.norm_of_nonneg hn.le, Real.norm_eq_abs]
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        ((mul_le_mul (hw c n) hchar (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))
        (abs_nonneg _)
    · exact gaussian_square_norm_bound _ _ _ hc hn hZ
  let f : ExteriorSquarefreeIdeal A.cS → ℝ := fun c =>
    (A.exteriorNorm c.val) ^ (-(5 / 2 : ℝ))
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
  have hmajor : Summable (fun i : ExteriorSquarefreeIdeal A.cS × A.Exterior =>
      (Real.exp 4 / (2 * Real.sqrt Real.pi) * Z ^ 2) * f i.1 * g i.2) := by
    convert hfg.mul_left (Real.exp 4 / (2 * Real.sqrt Real.pi) * Z ^ 2) using 1
    ext i
    ring
  exact hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hb i.1 i.2)

end
end DedekindZetaZeroFree.PoissonProbeDyadicMomentTransfer.ActualDyadicMomentSource

end
