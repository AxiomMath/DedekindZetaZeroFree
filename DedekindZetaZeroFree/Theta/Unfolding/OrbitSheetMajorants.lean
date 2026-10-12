module

public import DedekindZetaZeroFree.Theta.Unfolding.OrbitExtractionDefinitions

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open ThetaExpansion.SignedExpansion
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem branch_norm_one {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (y : R.A.G) : ‖P.branch v y‖ = 1 := by
  rw [P.branch_global]
  have hp : (R.σ (((R.A.H_S (R.A.diagonal
      (R.probe.unitReps.representative v).val) y : Fˣ) : F))) ^ 6 = 1 := by
    rw [← map_pow]
    have hr := (R.A.H_S (R.A.diagonal
      (R.probe.unitReps.representative v).val) y).property
    simpa only [mem_rootsOfUnity, Units.val_pow_eq_pow_val, Units.val_one, map_one]
      using congrArg (fun u : Fˣ => R.σ (u : F)) hr
  have hn : ‖R.σ (((R.A.H_S (R.A.diagonal
      (R.probe.unitReps.representative v).val) y : Fˣ) : F))‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 6 ≠ 0)).mp
    rw [← norm_pow, hp, norm_one]
  simp only [norm_mul, Circle.norm_coe, hn, mul_one]

theorem orbitSheet_norm_le {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (i : OrbitIndex R) (l : PositiveAxis) (z : Sheet R.A l) :
    ‖orbitSheet R C v m b i l z‖ ≤
      ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
        ‖digitWeight R m d * orbitFrequencyValue R C.sources C.realization v i
          (signedArgument R m b z.val d)‖ := by
  unfold orbitSheet
  split_ifs
  · simp only [one_mul, norm_mul, norm_inv, branch_norm_one, inv_one]
    simpa only [one_mul, norm_mul] using norm_sum_le Finset.univ (fun d : ThetaDigitAverage.Dig
      (ThetaDigitAverage.rowPrimes R.A m.val m.property) =>
      digitWeight R m d * orbitFrequencyValue R C.sources C.realization v i
        (signedArgument R m b z.val d))
  · simp only [zero_mul, norm_zero]
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

end DedekindZetaZeroFree.OrbitExpansion

end
