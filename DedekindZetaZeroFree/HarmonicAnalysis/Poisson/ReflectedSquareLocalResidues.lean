module

public import DedekindZetaZeroFree.LFunctions.Dedekind.PrincipalHeckeData
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.UniformOriginRemainder
public import DedekindZetaZeroFree.Nonvanishing.Mellin.ReflectedSquareSpectrum

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped NumberField Classical Topology ContDiff
open Filter

namespace DedekindZetaZeroFree.LargeSieve

def PrincipalHeckeData.zetaOriginFactor {F : Type} [Field F] [NumberField F]
    (data : PrincipalHeckeData F) (s : ℂ) : ℂ :=
  (principalDiscriminant F : ℂ) ^ (-s / 2) *
    ((Complex.Gammaℂ (s + 1))⁻¹ / (2 * (Real.pi : ℂ))) ^ principalComplexPlaces F *
    data.E s / (s - 1)

def principalZetaContinuation
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (s : ℂ) : ℂ :=
  s ^ (principalComplexPlaces F - 1) *
    (principalHeckeData F hF).zetaOriginFactor s

def principalZetaResidueCoefficient
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F) : ℂ :=
  principalPoleCoefficient F hF /
    ((Real.sqrt (principalDiscriminant F) : ℂ) *
      Complex.Gammaℂ 1 ^ principalComplexPlaces F)

variable
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)

private lemma gammaℂ_ne_zero_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    Complex.Gammaℂ s ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by simp [Real.pi_ne_zero]))
  · exact Complex.Gamma_ne_zero_of_re_pos hs

private lemma zetaOrigin_key (s : ℂ) (hs : s ≠ 0) (r : ℕ) (hr : 1 ≤ r) :
    s ^ (r - 1) * ((Complex.Gammaℂ (s + 1))⁻¹ / (2 * (Real.pi : ℂ))) ^ r =
      (Complex.Gammaℂ s)⁻¹ ^ r / s := by
  have hrec := DedekindZetaZeroFree.LargeSieve.Vendor.inverse_Gammaℂ_recurrence s
  have hbase : (Complex.Gammaℂ (s + 1))⁻¹ / (2 * (Real.pi : ℂ)) =
      (Complex.Gammaℂ s)⁻¹ / s := by
    rw [hrec]
    field_simp
  rw [hbase, div_pow, mul_div]
  rw [div_eq_div_iff (pow_ne_zero _ hs) hs]
  have hspow : s ^ (r - 1) * s = s ^ r := by
    rw [← pow_succ, Nat.sub_add_cancel hr]
  rw [mul_right_comm, hspow, mul_comm]

variable
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)

theorem principalZetaContinuation_eq_decompleted (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    principalZetaContinuation F hF s =
      (principalDiscriminant F : ℂ) ^ (-s / 2) *
        (Complex.Gammaℂ s)⁻¹ ^ principalComplexPlaces F *
          (principalHeckeData F hF).Lambda s := by
  have hr := principalComplexPlaces_pos F hF
  have key := zetaOrigin_key s hs0 (principalComplexPlaces F) hr
  rw [principalZetaContinuation, PrincipalHeckeData.zetaOriginFactor,
    (principalHeckeData F hF).Lambda_eq_div s hs0 hs1]
  have hshape :
      s ^ (principalComplexPlaces F - 1) *
          ((principalDiscriminant F : ℂ) ^ (-s / 2) *
            ((Complex.Gammaℂ (s + 1))⁻¹ / (2 * (Real.pi : ℂ))) ^ principalComplexPlaces F *
            (principalHeckeData F hF).E s / (s - 1)) =
        (principalDiscriminant F : ℂ) ^ (-s / 2) *
          (s ^ (principalComplexPlaces F - 1) *
            ((Complex.Gammaℂ (s + 1))⁻¹ / (2 * (Real.pi : ℂ))) ^ principalComplexPlaces F) *
          ((principalHeckeData F hF).E s / (s - 1)) := by ring
  rw [hshape, key]
  field_simp

theorem principalZetaContinuation_eq_dirichlet (s : ℂ) (hs : 1 < s.re) :
    principalZetaContinuation F hF s =
      ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else (Ideal.absNorm I : ℂ) ^ (-s) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp only [Complex.zero_re] at hs; linarith
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; norm_num at hs
  rw [principalZetaContinuation_eq_decompleted F hF s hs0 hs1,
    (principalHeckeData F hF).Lambda_dirichlet s hs]
  have hD : (principalDiscriminant F : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (principalDiscriminant_pos F)
  have hG : Complex.Gammaℂ s ≠ 0 := gammaℂ_ne_zero_of_re_pos s (by linarith)
  have hDc : (principalDiscriminant F : ℂ) ^ (-s / 2) *
      (principalDiscriminant F : ℂ) ^ (s / 2) = 1 := by
    rw [← Complex.cpow_add _ _ hD, show -s / 2 + s / 2 = 0 by ring, Complex.cpow_zero]
  have hGc : (Complex.Gammaℂ s)⁻¹ ^ principalComplexPlaces F *
      Complex.Gammaℂ s ^ principalComplexPlaces F = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hG, one_pow]
  rw [show (principalDiscriminant F : ℂ) ^ (-s / 2) *
        (Complex.Gammaℂ s)⁻¹ ^ principalComplexPlaces F *
        ((principalDiscriminant F : ℂ) ^ (s / 2) * Complex.Gammaℂ s ^ principalComplexPlaces F *
          (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else (Ideal.absNorm I : ℂ) ^ (-s))) =
      ((principalDiscriminant F : ℂ) ^ (-s / 2) * (principalDiscriminant F : ℂ) ^ (s / 2)) *
        ((Complex.Gammaℂ s)⁻¹ ^ principalComplexPlaces F * Complex.Gammaℂ s ^ principalComplexPlaces F) *
        (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else (Ideal.absNorm I : ℂ) ^ (-s)) by ring,
    hDc, hGc]
  ring

end DedekindZetaZeroFree.LargeSieve

end
