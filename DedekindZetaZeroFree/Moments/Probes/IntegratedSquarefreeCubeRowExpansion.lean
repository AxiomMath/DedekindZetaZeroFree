module

public import DedekindZetaZeroFree.Moments.Probes.PoissonJointAbsoluteMass

@[expose] public section

namespace DedekindZetaZeroFree
namespace NormalizedProbe
noncomputable section
open scoped NumberField Classical ENNReal
open MeasureTheory

variable {F : Type} [Field F] [NumberField F]

local instance (A : SArithmeticData F) : MeasurableSpace A.G1 := borel _

local instance (A : SArithmeticData F) : BorelSpace A.G1 := ⟨rfl⟩

def originalRow (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (W0 : SLocalProduct F A.Sf → ℂ) (X : ℝ)
    (s : A.Exterior) (a : A.R) (t : A.G1) : ℂ :=
  (Real.sqrt (A.exteriorNorm s * X) : ℂ)⁻¹ * ∑' m : A.R,
    gaussRow A D s m *
      D.character a (FiniteTransform.residueMap A.R.toSubring a m) *
      W0 (sLocalDiagonal F A.Sf (m : F) *
        asLocalPoint A (((t : A.G) * radialSection A (A.exteriorNorm s * X))⁻¹))

theorem forwardSummand_eq_lambda_mul_character (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (m : ThetaReflectionData.Row A)
    (Z : ℝ) (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) :
    ThetaReflectionData.forwardSummand A D m Z c n =
      ProbeJointAbsoluteMass.lambda A D c n Z *
        ThetaReflectionData.forwardRowCharacter A D c n m.val := by
  simp only [ThetaReflectionData.forwardSummand, ProbeJointAbsoluteMass.lambda,
    ProbeJointAbsoluteMass.modulusNorm]
  ring

private theorem original_tsum_expanded (A : SArithmeticData F)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (hS : A.ContainsTraceBadPlaces) (P : PrincipalData A σ η hS)
    (X Y Z : ℝ) (s : A.Exterior)
    (i : ExteriorSquarefreeIdeal A.cS × A.Exterior) (t : A.G1) :
    (∑' m : A.R, expandedProbeSummand A P.coefficients P.W0 P.W1 X Y Z t s m i) =
      (Y⁻¹ : ℂ) * (P.W1 (A.exteriorNorm s / Y) : ℂ) *
        ProbeJointAbsoluteMass.lambda A P.coefficients i.1 i.2 Z *
        originalRow A P.coefficients P.W0 X s
          (ThetaReflectionData.forwardModulus A P.coefficients i.1 i.2) t := by
  unfold originalRow
  simp only [← mul_assoc, ← tsum_mul_left]
  apply tsum_congr
  intro m
  by_cases hm : m = 0
  · subst m
    have hz := original_zero_row A P.W0 P.supportUnits t (A.exteriorNorm s * X)
    simp only [expandedProbeSummand, ZeroMemClass.coe_zero, dite_true, hz, mul_zero]
  · rw [expandedProbeSummand, dif_neg hm, forwardSummand_eq_lambda_mul_character]
    unfold ThetaReflectionData.forwardRowCharacter
    ring

theorem principal_original_integrated_row_expansion (A : SArithmeticData F)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (hS : A.ContainsTraceBadPlaces) (P : PrincipalData A σ η hS)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    probe A P.coefficients P.domain P.W0 P.W1 X Y Z =
      (Y⁻¹ : ℂ) * ∑' s : A.Exterior,
        (P.W1 (A.exteriorNorm s / Y) : ℂ) *
        ∑' c : ExteriorSquarefreeIdeal A.cS, ∑' n : A.Exterior,
          ProbeJointAbsoluteMass.lambda A P.coefficients c n Z *
            ∫ t in P.domain.domain,
              originalRow A P.coefficients P.W0 X s
                (ThetaReflectionData.forwardModulus A P.coefficients c n) t
              ∂P.domain.measure := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let f := fun (j : A.Exterior × A.R × (ExteriorSquarefreeIdeal A.cS × A.Exterior))
    (t : A.G1) => expandedProbeSummand A P.coefficients P.W0 P.W1 X Y Z t
      j.1 j.2.1 j.2.2
  have hf := (principal_expansion_valid A σ η hS P X Y Z hX hY hZ).1
  have hs : Summable (fun j => ∫ t in P.domain.domain, ‖f j t‖ ∂P.domain.measure) := by
    have he := ENNReal.summable_toReal
      (principal_integrated_absolutely_convergent A σ η hS P X Y Z hX hY hZ).ne
    simpa only [f, integral_norm_eq_lintegral_enorm (hf _).aestronglyMeasurable,
      ofReal_norm_eq_enorm] using he
  have hv : Summable (fun j => ∫ t in P.domain.domain, f j t ∂P.domain.measure) :=
    hs.of_norm_bounded (fun j => norm_integral_le_integral_norm _)
  rw [(principal_expansion_valid A σ η hS P X Y Z hX hY hZ).2.2]
  change (∑' j, ∫ t in P.domain.domain, f j t ∂P.domain.measure) = _
  rw [hv.tsum_prod]
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro s
  rw [(hv.prod_factor s).tsum_prod]
  rw [← (hv.prod_factor s).tsum_comm]
  have hp := ((hv.prod_factor s).prod_symm.prod).tsum_prod
  simp only [Prod.swap_prod_mk] at hp
  rw [hp]
  apply tsum_congr
  intro c
  apply tsum_congr
  intro n
  have hm := hasSum_integral_of_summable_integral_norm
    (fun m => hf (s, m, (c, n))) (((hs.prod_factor s).prod_symm).prod_factor (c, n))
  rw [hm.tsum_eq]
  change (∫ t in P.domain.domain,
    (∑' m, expandedProbeSummand A P.coefficients P.W0 P.W1 X Y Z t s m (c,n))
    ∂P.domain.measure) = _
  simp only [original_tsum_expanded A σ η hS P, integral_const_mul, mul_assoc]

end
end NormalizedProbe
end DedekindZetaZeroFree
