module

public import DedekindZetaZeroFree.Moments.Probes.PrincipalProbeAndSeparatedMellinSeries

@[expose] public section

namespace DedekindZetaZeroFree
namespace NormalizedProbe

noncomputable section
open scoped NumberField

variable {F : Type} [Field F] [NumberField F]

def gaussianDoubleMomentSummand (A : SArithmeticData F) (β Z : ℝ)
    (i : ExteriorSquarefreeIdeal A.cS × A.Exterior) : ℝ :=
  (A.exteriorNorm i.1.val).rpow (β - 1 / 2) *
    (A.exteriorNorm i.2).rpow (3 * β - 1) *
    thetaReflectionGaussian (A.exteriorNorm i.1.val * A.exteriorNorm i.2 ^ 3 / Z)

private theorem thetaReflectionGaussian_nonneg (x : ℝ) : 0 ≤ thetaReflectionGaussian x := by
  unfold thetaReflectionGaussian
  split
  · positivity
  · exact le_refl 0

private theorem gauss_pow_bound (B Z x : ℝ) (hZ : 0 < Z) (hx : 0 < x) :
    thetaReflectionGaussian (x / Z) ≤
      Real.exp (B ^ 2) * Z ^ B / (2 * Real.sqrt Real.pi) * x ^ (-B) := by
  rw [thetaReflectionGaussian_of_pos _ (div_pos hx hZ)]
  have hnum : Real.exp (-(Real.log (x / Z)) ^ 2 / 4) ≤
      Real.exp (B ^ 2) * Z ^ B * x ^ (-B) := by
    rw [Real.log_div hx.ne' hZ.ne']
    have e1 : Real.exp (-(Real.log x - Real.log Z) ^ 2 / 4) ≤
        Real.exp (B ^ 2) * Real.exp (-B * (Real.log x - Real.log Z)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (B - (Real.log x - Real.log Z) / 2)]
    have hxa : Real.exp ((-B) * Real.log x) = x ^ (-B) := by
      rw [show (-B) * Real.log x = Real.log x * (-B) by ring,
        ← Real.rpow_def_of_pos hx (-B)]
    have hZb : Real.exp (B * Real.log Z) = Z ^ B := by
      rw [show B * Real.log Z = Real.log Z * B by ring,
        ← Real.rpow_def_of_pos hZ B]
    have e2 : Real.exp (-B * (Real.log x - Real.log Z)) = Z ^ B * x ^ (-B) := by
      rw [show -B * (Real.log x - Real.log Z) = (-B) * Real.log x + B * Real.log Z by ring]
      rw [Real.exp_add, hxa, hZb]
      ring
    calc Real.exp (-(Real.log x - Real.log Z) ^ 2 / 4)
        ≤ Real.exp (B ^ 2) * Real.exp (-B * (Real.log x - Real.log Z)) := e1
      _ = Real.exp (B ^ 2) * (Z ^ B * x ^ (-B)) := by rw [e2]
      _ = Real.exp (B ^ 2) * Z ^ B * x ^ (-B) := by ring
  calc Real.exp (-(Real.log (x / Z)) ^ 2 / 4) / (2 * Real.sqrt Real.pi)
      ≤ (Real.exp (B ^ 2) * Z ^ B * x ^ (-B)) / (2 * Real.sqrt Real.pi) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = Real.exp (B ^ 2) * Z ^ B / (2 * Real.sqrt Real.pi) * x ^ (-B) := by ring

private theorem rpow_three {x B : ℝ} (hx : 0 ≤ x) :
    (x ^ 3) ^ (-B) = x ^ (-(3 * B)) := by
  rw [← Real.rpow_natCast_mul hx 3 (-B)]
  congr 1
  ring

private theorem summand_le (A : SArithmeticData F) (β Z B : ℝ) (hZ : 0 < Z)
    (i : ExteriorSquarefreeIdeal A.cS × A.Exterior) :
    gaussianDoubleMomentSummand A β Z i ≤
      Real.exp (B ^ 2) * Z ^ B / (2 * Real.sqrt Real.pi) *
        (A.exteriorNorm i.1.val) ^ (β - 1 / 2 - B) *
        (A.exteriorNorm i.2) ^ (3 * β - 1 - 3 * B) := by
  have hqc : 0 < A.exteriorNorm i.1.val :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ i.1.val.property.1)
  have hqn : 0 < A.exteriorNorm i.2 :=
    lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ i.2.property.1)
  have hx : 0 < A.exteriorNorm i.1.val * A.exteriorNorm i.2 ^ 3 := by positivity
  have hg := gauss_pow_bound B Z (A.exteriorNorm i.1.val * A.exteriorNorm i.2 ^ 3) hZ hx
  have hab : 0 ≤ (A.exteriorNorm i.1.val) ^ (β - 1 / 2) *
      (A.exteriorNorm i.2) ^ (3 * β - 1) :=
    mul_nonneg (Real.rpow_nonneg hqc.le _) (Real.rpow_nonneg (by positivity) _)
  have hsplit : (A.exteriorNorm i.1.val * A.exteriorNorm i.2 ^ 3) ^ (-B) =
      (A.exteriorNorm i.1.val) ^ (-B) * (A.exteriorNorm i.2) ^ (-(3 * B)) := by
    rw [Real.mul_rpow hqc.le (by positivity : (0:ℝ) ≤ A.exteriorNorm i.2 ^ 3),
      rpow_three hqn.le]
  calc gaussianDoubleMomentSummand A β Z i
      = (A.exteriorNorm i.1.val) ^ (β - 1 / 2) * (A.exteriorNorm i.2) ^ (3 * β - 1) *
          thetaReflectionGaussian (A.exteriorNorm i.1.val * A.exteriorNorm i.2 ^ 3 / Z) :=
        rfl
    _ ≤ (A.exteriorNorm i.1.val) ^ (β - 1 / 2) * (A.exteriorNorm i.2) ^ (3 * β - 1) *
          (Real.exp (B ^ 2) * Z ^ B / (2 * Real.sqrt Real.pi) *
            (A.exteriorNorm i.1.val * A.exteriorNorm i.2 ^ 3) ^ (-B)) :=
        mul_le_mul_of_nonneg_left hg hab
    _ = Real.exp (B ^ 2) * Z ^ B / (2 * Real.sqrt Real.pi) *
          ((A.exteriorNorm i.1.val) ^ (β - 1 / 2) * (A.exteriorNorm i.1.val) ^ (-B)) *
          ((A.exteriorNorm i.2) ^ (3 * β - 1) * (A.exteriorNorm i.2) ^ (-(3 * B))) := by
        rw [hsplit]; ring
    _ = Real.exp (B ^ 2) * Z ^ B / (2 * Real.sqrt Real.pi) *
          (A.exteriorNorm i.1.val) ^ (β - 1 / 2 - B) *
          (A.exteriorNorm i.2) ^ (3 * β - 1 - 3 * B) := by
        rw [← Real.rpow_add hqc (β - 1 / 2) (-B),
          ← Real.rpow_add hqn (3 * β - 1) (-(3 * B))]
        rw [show β - 1 / 2 + -B = β - 1 / 2 - B by ring,
          show 3 * β - 1 + -(3 * B) = 3 * β - 1 - 3 * B by ring]

theorem gaussianDoubleMomentSummand_nonneg (A : SArithmeticData F)
    (β Z : ℝ) (hZ : 0 < Z)
    (i : ExteriorSquarefreeIdeal A.cS × A.Exterior) :
    0 ≤ gaussianDoubleMomentSummand A β Z i := by
  have hqc : 0 ≤ A.exteriorNorm i.1.val :=
    le_of_lt (lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ i.1.val.property.1))
  have hqn : 0 ≤ A.exteriorNorm i.2 :=
    le_of_lt (lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ i.2.property.1))
  unfold gaussianDoubleMomentSummand
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hqc _) (Real.rpow_nonneg hqn _))
    (thetaReflectionGaussian_nonneg _)

theorem gaussian_double_moments_summable (A : SArithmeticData F)
    (β Z : ℝ) (hZ : 0 < Z) :
    Summable (gaussianDoubleMomentSummand A β Z) := by
  set B := β + 2 with hB
  have hαc : β - 1 / 2 - B = -(5 / 2) := by rw [hB]; ring
  have hαn : 3 * β - 1 - 3 * B = -(7) := by rw [hB]; ring
  have hqc : ∀ c : ExteriorSquarefreeIdeal A.cS, 0 ≤ A.exteriorNorm c.val :=
    fun c => le_of_lt (lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ c.val.property.1))
  have hqn : ∀ n : A.Exterior, 0 ≤ A.exteriorNorm n :=
    fun n => le_of_lt (lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ n.property.1))
  have hfc : Summable (fun c : ExteriorSquarefreeIdeal A.cS =>
      (A.exteriorNorm c.val) ^ (β - 1 / 2 - B)) := by
    have hbase : Summable (fun c : ExteriorSquarefreeIdeal A.cS =>
        (A.exteriorNorm c.val) ^ (-(5 / 2) : ℝ)) :=
      (ideal_norm_rpow_summable F (5 / 2) (by norm_num)).comp_injective
        (i := fun c : ExteriorSquarefreeIdeal A.cS =>
          (⟨c.val.val, c.val.property.1⟩ : NonzeroIdeal F))
        (fun c d he => by
          have h1 : c.val.val = d.val.val := by
            simpa using congrArg (fun x : NonzeroIdeal F => x.val) he
          exact Subtype.ext (Subtype.ext h1))
    simpa only [hαc] using hbase
  have hgn : Summable (fun n : A.Exterior =>
      (A.exteriorNorm n) ^ (3 * β - 1 - 3 * B)) := by
    have hbase : Summable (fun n : A.Exterior =>
        (A.exteriorNorm n) ^ (-(7) : ℝ)) :=
      (ideal_norm_rpow_summable F 7 (by norm_num)).comp_injective
        (i := fun n : A.Exterior => (⟨n.val, n.property.1⟩ : NonzeroIdeal F))
        (fun n m he => by
          have h1 : n.val = m.val := by
            simpa using congrArg (fun x : NonzeroIdeal F => x.val) he
          exact Subtype.ext h1)
    simpa only [hαn] using hbase
  have hprod : Summable (fun i : ExteriorSquarefreeIdeal A.cS × A.Exterior =>
      (A.exteriorNorm i.1.val) ^ (β - 1 / 2 - B) *
        (A.exteriorNorm i.2) ^ (3 * β - 1 - 3 * B)) :=
    Summable.mul_of_nonneg hfc hgn
      (fun c => Real.rpow_nonneg (hqc c) _) (fun n => Real.rpow_nonneg (hqn n) _)
  have hmaj : Summable (fun i : ExteriorSquarefreeIdeal A.cS × A.Exterior =>
      Real.exp (B ^ 2) * Z ^ B / (2 * Real.sqrt Real.pi) *
        ((A.exteriorNorm i.1.val) ^ (β - 1 / 2 - B) *
          (A.exteriorNorm i.2) ^ (3 * β - 1 - 3 * B))) :=
    hprod.mul_left _
  refine Summable.of_nonneg_of_le
    (fun i => gaussianDoubleMomentSummand_nonneg A β Z hZ i) (fun i => ?_) hmaj
  simpa only [mul_assoc] using summand_le A β Z B hZ i

end
end NormalizedProbe
end DedekindZetaZeroFree
