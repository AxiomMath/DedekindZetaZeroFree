module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyData
public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyCount
public import DedekindZetaZeroFree.Analysis.GaussianWeightConvolution

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawKernelNorm

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

theorem norm_exp_sq (ξ z : ℂ) :
    ‖Complex.exp ((ξ + z - 1) ^ 2)‖ =
      Real.exp ((ξ.re + z.re - 1) ^ 2) * Real.exp (-(ξ.im + z.im) ^ 2) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp only [pow_two, Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.one_re,
    Complex.add_im, Complex.sub_im, Complex.one_im]
  ring

theorem norm_exp_sq_line (ξ : ℂ) (v s : ℝ) :
    ‖Complex.exp ((ξ + ((v : ℂ) + (s : ℂ) * Complex.I) - 1) ^ 2)‖ =
      Real.exp ((ξ.re + v - 1) ^ 2) * Real.exp (-(ξ.im + s) ^ 2) := by
  rw [norm_exp_sq]
  simp

theorem weightModulus_eq (ξ : ℂ) (v y : ℝ) (p : ℝ × ℝ) :
    WeightConvolution.weightModulus D ξ v y p =
      Real.exp ((ξ.re + v - 1) ^ 2) * Real.exp (-(ξ.im + p.1) ^ 2) *
        ‖D.M ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ *
        ‖D.W1Hat ((y : ℂ) + (p.2 : ℂ) * Complex.I)‖ := by
  unfold WeightConvolution.weightModulus
  rw [norm_mul, norm_mul, norm_exp_sq_line]

theorem frequencyNorm_pos (u : Frequency D.recipe) : 0 < frequencyNorm D.recipe u :=
  lt_of_lt_of_le one_pos (RawFrequencyCount.one_le_frequencyNorm D.recipe u)

theorem norm_rawFactor (u : Frequency D.recipe) (ξ w z : ℂ) :
    ‖RawFixed.FixedData.rawFactor D u ξ w z‖ =
      ‖D.recipe.L (6 * z)‖ * ‖(RawFixed.FixedData.pkg D).plus u w‖ *
        ‖AllRowEuler.InitialSeparation.correctionProduct D.context
          (RawFixed.FixedData.rawFrequency D u) ξ w z‖ *
        ‖(RawFixed.FixedData.pkg D).minus u ξ‖⁻¹ := by
  unfold RawFixed.FixedData.rawFactor
  rw [norm_div, norm_mul, norm_mul, div_eq_mul_inv]

theorem norm_rawKernel (u : Frequency D.recipe) (ξ : ℂ) (v y : ℝ) (p : ℝ × ℝ) (Z : ℝ)
    (hZ : 0 < Z) :
    ‖RawFixed.FixedData.rawKernel D u ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I)
        ((v : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ =
      Z ^ (Scales.kernelExponent ξ.re y v) * frequencyNorm D.recipe u ^ (-v) *
        WeightConvolution.weightModulus D ξ v y p *
        ‖RawFixed.FixedData.rawFactor D u ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I)
          ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ := by
  have hqc : (0 : ℝ) < frequencyNorm D.recipe u := frequencyNorm_pos D u
  unfold RawFixed.FixedData.rawKernel
  have hre : ∀ A B C X E R : ℂ, A * B * C * X * E * R = A * E * (B * C * X) * R := by
    intro A B C X E R; ring
  have hkey : ∀ A E X R : ℂ, ‖A * E * X * R‖ = ‖A‖ * ‖E‖ * ‖X‖ * ‖R‖ := by
    intro A E X R; simp only [norm_mul]
  rw [hre, hkey]
  unfold WeightConvolution.weightModulus
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ, Complex.norm_cpow_eq_rpow_re_of_pos hqc]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.sub_im,
    Complex.mul_im, Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, Complex.ofReal_natCast]
  simp only [zero_mul, mul_zero, sub_zero, add_zero, zero_add, zero_sub]
  unfold Scales.kernelExponent
  try ring_nf

theorem norm_rawKernel_le (u : Frequency D.recipe) (ξ : ℂ) (v y : ℝ) (p : ℝ × ℝ) (Z : ℝ)
    (hZ : 0 < Z) (B : ℝ)
    (hB : ‖RawFixed.FixedData.rawFactor D u ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I)
          ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ ≤ B) :
    ‖RawFixed.FixedData.rawKernel D u ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I)
        ((v : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
      Z ^ (Scales.kernelExponent ξ.re y v) * WeightConvolution.weightModulus D ξ v y p *
        frequencyNorm D.recipe u ^ (-v) * B := by
  have hqc : (0 : ℝ) < frequencyNorm D.recipe u := frequencyNorm_pos D u
  rw [norm_rawKernel D u ξ v y p Z hZ]
  have h1 : 0 ≤ Z ^ (Scales.kernelExponent ξ.re y v) := (Real.rpow_pos_of_pos hZ _).le
  have h2 : 0 ≤ frequencyNorm D.recipe u ^ (-v) := (Real.rpow_pos_of_pos hqc _).le
  have h3 : 0 ≤ WeightConvolution.weightModulus D ξ v y p := norm_nonneg _
  calc _ = Z ^ (Scales.kernelExponent ξ.re y v) * WeightConvolution.weightModulus D ξ v y p *
        frequencyNorm D.recipe u ^ (-v) * ‖RawFixed.FixedData.rawFactor D u ξ _ _‖ := by ring
    _ ≤ _ := by gcongr

end

end DedekindZetaZeroFree.Quantitative.RawKernelNorm
