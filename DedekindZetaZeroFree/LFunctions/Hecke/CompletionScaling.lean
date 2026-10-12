module

public import DedekindZetaZeroFree.LFunctions.Hecke.IdealSeriesAndContinuationWitnesses

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

noncomputable section
open scoped NumberField Classical

def heckeCompletionLogScale (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] (f : Ideal (𝓞 F)) : ℝ :=
  (Real.log ((NumberField.discr E).natAbs : ℝ) -
    2 * Real.log ((NumberField.discr F).natAbs : ℝ) -
    Real.log (Ideal.absNorm f : ℝ)) / 2

theorem heckeCompletionFactor_scaling
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (hcomplex : NumberField.InfinitePlace.nrComplexPlaces E =
      2 * NumberField.InfinitePlace.nrComplexPlaces F) :
    ∀ s : ℂ, heckeCompletionFactor E ⊤ s =
      Complex.exp ((heckeCompletionLogScale F E f : ℂ) * s) *
        heckeCompletionFactor F ⊤ s * heckeCompletionFactor F f s := by
  intro s
  have hdE : NumberField.discr E ≠ 0 := NumberField.discr_ne_zero E
  have hdF : NumberField.discr F ≠ 0 := NumberField.discr_ne_zero F
  have hN : Ideal.absNorm f ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hf
  have hxE : (0 : ℝ) < ((NumberField.discr E).natAbs : ℝ) :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hdE)
  have hxF : (0 : ℝ) < ((NumberField.discr F).natAbs : ℝ) :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hdF)
  have hxN : (0 : ℝ) < (Ideal.absNorm f : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hbaseE : ((|NumberField.discr E| : ℤ) : ℂ) =
      (((NumberField.discr E).natAbs : ℝ) : ℂ) := by
    rw [Int.abs_eq_natAbs]; simp only [Int.cast_natCast, Complex.ofReal_natCast]
  have hbaseF : ((|NumberField.discr F| : ℤ) : ℂ) =
      (((NumberField.discr F).natAbs : ℝ) : ℂ) := by
    rw [Int.abs_eq_natAbs]; simp only [Int.cast_natCast, Complex.ofReal_natCast]
  have hbaseN : (Ideal.absNorm f : ℂ) = ((Ideal.absNorm f : ℝ) : ℂ) := by
    norm_num

  have hcore : ((|NumberField.discr E| : ℤ) : ℂ) ^ (s / 2) =
      Complex.exp ((heckeCompletionLogScale F E f : ℂ) * s) *
        ((|NumberField.discr F| : ℤ) : ℂ) ^ (s / 2) *
        (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm f : ℂ)) ^ (s / 2) := by
    rw [hbaseE, hbaseF, hbaseN, ← Complex.ofReal_mul]
    have hxFN : (0 : ℝ) < (NumberField.discr F).natAbs * (Ideal.absNorm f : ℝ) :=
      mul_pos hxF hxN
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hxE.ne'),
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hxF.ne'),
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hxFN.ne'),
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold heckeCompletionLogScale
    rw [← Complex.ofReal_log hxE.le, ← Complex.ofReal_log hxF.le,
      ← Complex.ofReal_log hxFN.le, Real.log_mul hxF.ne' hxN.ne']
    push_cast
    ring
  have hgam : Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces E =
      Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F *
        Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F := by
    rw [hcomplex, two_mul, pow_add]
  have htopE : (Ideal.absNorm (⊤ : Ideal (𝓞 E)) : ℂ) = 1 := by
    rw [Ideal.absNorm_top]; norm_num
  have htopF : (Ideal.absNorm (⊤ : Ideal (𝓞 F)) : ℂ) = 1 := by
    rw [Ideal.absNorm_top]; norm_num
  simp only [heckeCompletionFactor]
  rw [htopE, htopF, mul_one, mul_one, hgam, hcore]
  ring

end

end DedekindZetaZeroFree.LargeSieve
