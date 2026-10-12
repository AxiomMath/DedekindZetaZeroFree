module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.ReflectedSquareResidueData
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LogarithmicIdealInterchange

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped NumberField Classical Topology ContDiff
open Filter

namespace DedekindZetaZeroFree.LargeSieve

def principalMellinIntegrand {F : Type} [Field F] [NumberField F]
    (data : PrincipalHeckeData F) (Q : ℂ → ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  (X : ℂ) ^ s * (principalDiscriminant F : ℂ) ^ (-s / 2) *
    (Complex.Gammaℂ s)⁻¹ ^ (principalComplexPlaces F - 1) * Q s * data.E s /
      (s * (s - 1))

def principalMellinResidueOne {F : Type} [Field F] [NumberField F]
    (data : PrincipalHeckeData F) (Q : ℂ → ℂ) (X : ℝ) : ℂ :=
  (X : ℂ) * (Complex.Gammaℂ 1 * Q 1) * data.E 1 /
    ((Real.sqrt (principalDiscriminant F) : ℂ) *
      Complex.Gammaℂ 1 ^ principalComplexPlaces F)

def principalMellinResidueZero {F : Type} [Field F] [NumberField F]
    (data : PrincipalHeckeData F) (h : ℝ → ℂ) : ℂ :=
  if principalComplexPlaces F = 1 then -(data.E 1) * h 0 / 2 else 0

 def principalNumerator {F : Type} [Field F] [NumberField F]
    (data : PrincipalHeckeData F) (Q : ℂ → ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  (X : ℂ) ^ s * (principalDiscriminant F : ℂ) ^ (-s / 2) *
    (Complex.Gammaℂ s)⁻¹ ^ (principalComplexPlaces F - 1) * Q s * data.E s

private lemma numerator_diff {F : Type} [Field F] [NumberField F]
    (data : PrincipalHeckeData F) (Q : ℂ → ℂ) (hQ : Differentiable ℂ Q)
    (X : ℝ) (hX : 0 < X) : Differentiable ℂ (principalNumerator data Q X) := by
  have hD : (principalDiscriminant F : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (principalDiscriminant_pos F))
  have h1 := differentiable_id.const_cpow (c := (X : ℂ))
    (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  have h2 := (differentiable_neg.div_const (2 : ℂ)).const_cpow (Or.inl hD)
  exact (((h1.mul h2).mul (Complex.differentiable_Gammaℂ_inv.pow _)).mul hQ).mul
    data.E_differentiable

private lemma numerator_zero {F : Type} [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (data : PrincipalHeckeData F)
    (h : ℝ → ℂ) (Q : ℂ → ℂ) (hQ0 : Q 0 = h 0 / 2) (X : ℝ) :
    principalNumerator data Q X 0 / ((0 : ℂ) - 1) =
      principalMellinResidueZero data h := by
  have hr := principalComplexPlaces_pos F hF
  by_cases hr1 : principalComplexPlaces F = 1
  · simp [principalNumerator, principalMellinResidueZero, hr1, hQ0,
      data.E_zero_eq_one]; ring
  · have hp : principalComplexPlaces F - 1 ≠ 0 := by omega
    simp [principalNumerator, principalMellinResidueZero, hr1,
      Complex.Gammaℂ_def, Complex.Gamma_zero, zero_pow hp]

private lemma numerator_one {F : Type} [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (data : PrincipalHeckeData F)
    (Q : ℂ → ℂ) (X : ℝ) :
    principalNumerator data Q X 1 / (1 : ℂ) = principalMellinResidueOne data Q X := by
  have hr := principalComplexPlaces_pos F hF
  have hD := principalDiscriminant_pos F
  have hG : Complex.Gammaℂ 1 ≠ 0 := by simp [Real.pi_ne_zero]
  have hS : (Real.sqrt (principalDiscriminant F) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hD).ne'
  have hpow : (principalDiscriminant F : ℂ) ^ (-(1 : ℂ) / 2) =
      (Real.sqrt (principalDiscriminant F) : ℂ)⁻¹ := by
    rw [show -(1 : ℂ) / 2 = -((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.cpow_neg, ← Complex.ofReal_cpow hD.le, ← Real.sqrt_eq_rpow]
  have hgpow : (Complex.Gammaℂ 1)⁻¹ ^ (principalComplexPlaces F - 1) *
      Complex.Gammaℂ 1 ^ principalComplexPlaces F = Complex.Gammaℂ 1 := by
    have he : principalComplexPlaces F = (principalComplexPlaces F - 1) + 1 := by omega
    conv_rhs => rw [← one_mul (Complex.Gammaℂ 1)]
    nth_rw 2 [he]
    rw [pow_succ, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hG, one_pow]
  simp only [principalNumerator, principalMellinResidueOne, Complex.cpow_one,
    hpow, div_one]
  apply (eq_div_iff (mul_ne_zero hS (pow_ne_zero _ hG))).mpr
  calc
    _ = (X : ℂ) * Q 1 * data.E 1 *
        ((Real.sqrt (principalDiscriminant F) : ℂ)⁻¹ *
          (Real.sqrt (principalDiscriminant F) : ℂ)) *
        ((Complex.Gammaℂ 1)⁻¹ ^ (principalComplexPlaces F - 1) *
          Complex.Gammaℂ 1 ^ principalComplexPlaces F) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hS, hgpow]; ring

theorem principalMellinIntegrand_residue_zero
    {F : Type} [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (data : PrincipalHeckeData F) (h : ℝ → ℂ) (Q : ℂ → ℂ)
    (hQ : Differentiable ℂ Q) (hQ0 : Q 0 = h 0 / 2) (X : ℝ) (hX : 0 < X) :
    Tendsto (fun s : ℂ => s * principalMellinIntegrand data Q X s)
      (𝓝[≠] (0 : ℂ)) (𝓝 (principalMellinResidueZero data h)) := by
  have hlim := ((numerator_diff data Q hQ X hX).continuous.continuousAt.tendsto).div
    (tendsto_id.sub_const (1 : ℂ)) (show (0 : ℂ) - 1 ≠ 0 by norm_num)
  rw [numerator_zero hF data h Q hQ0 X] at hlim
  apply (hlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin,
    eventually_ne_nhdsWithin (show (0 : ℂ) ≠ 1 by norm_num)] with s hs0 hs1
  have hs0' : s ≠ 0 := hs0
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  change principalNumerator data Q X s / (s - 1) =
    s * (principalNumerator data Q X s / (s * (s - 1)))
  field_simp

theorem principalMellinIntegrand_residue_one
    {F : Type} [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (data : PrincipalHeckeData F) (Q : ℂ → ℂ)
    (hQ : Differentiable ℂ Q) (X : ℝ) (hX : 0 < X) :
    Tendsto (fun s : ℂ => (s - 1) * principalMellinIntegrand data Q X s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (principalMellinResidueOne data Q X)) := by
  have hlim := ((numerator_diff data Q hQ X hX).continuous.continuousAt.tendsto).div
    tendsto_id (show (1 : ℂ) ≠ 0 by norm_num)
  rw [numerator_one hF data Q X] at hlim
  apply (hlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [eventually_ne_nhdsWithin (show (1 : ℂ) ≠ 0 by norm_num),
    self_mem_nhdsWithin] with s hs0 hs1
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  change principalNumerator data Q X s / s =
    (s - 1) * (principalNumerator data Q X s / (s * (s - 1)))
  field_simp

end DedekindZetaZeroFree.LargeSieve

end
