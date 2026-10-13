module

public import DedekindZetaZeroFree.Moments.Comparison.QuantitativePoissonComparison
public import DedekindZetaZeroFree.Moments.Reflected.FixedProbeBound

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.Spectral

open DedekindZetaZeroFree NumberField

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem f_growth (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 < Cε ∧ ∀ Z : ℝ, 2 ≤ Z → ‖f D Z‖ ≤ Cε * Z ^ ((287 / 800 : ℝ) + ε) := by
  obtain ⟨C1, hC1, h1⟩ := DedekindZetaZeroFree.Quantitative.Compare.Iscale_sub_main_le D
  obtain ⟨C2, hC2, h2⟩ := DedekindZetaZeroFree.Quantitative.FixedData.Iscale_bound D ε hε
  have hc : 0 < ‖c₀ D‖ := norm_pos_iff.mpr (DedekindZetaZeroFree.Quantitative.Compare.c₀_ne_zero D)
  refine ⟨(C1 + C2) / ‖c₀ D‖, div_pos (by linarith) hc, ?_⟩
  intro Z hZ
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hexp : (717 / 2000 : ℝ) ≤ 287 / 800 + ε := by linarith
  have hpow : Z ^ (717 / 2000 : ℝ) ≤ Z ^ ((287 / 800 : ℝ) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hZ1 hexp
  have hnonneg : 0 ≤ Z ^ ((287 / 800 : ℝ) + ε) := Real.rpow_nonneg hZ0.le _
  have hI : ‖D.Iscale Z‖ ≤ C2 * Z ^ ((287 / 800 : ℝ) + ε) := h2 Z hZ
  have hM := h1 Z hZ
  have key := norm_sub_le (D.Iscale Z) (D.Iscale Z - c₀ D * f D Z)
  have e : D.Iscale Z - (D.Iscale Z - c₀ D * f D Z) = c₀ D * f D Z := by ring
  rw [e] at key
  rw [norm_mul] at key
  have hC1' : C1 * Z ^ (717 / 2000 : ℝ) ≤ C1 * Z ^ ((287 / 800 : ℝ) + ε) :=
    mul_le_mul_of_nonneg_left hpow hC1.le
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith

theorem g_growth (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 < Cε ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖((Z : ℂ) ^ (((61 / 100 : ℝ)) : ℂ)) * f D Z‖ ≤ Cε * Z ^ (31 / 32 + ε) := by
  obtain ⟨C, hC, h⟩ := f_growth D ε hε
  refine ⟨C, hC, fun Z hZ => ?_⟩
  have hZ0 : 0 < Z := by linarith
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hZ0]
  simp only [Complex.ofReal_re]
  have hfz := h Z hZ
  have e : Z ^ (31 / 32 + ε) = Z ^ (61 / 100 : ℝ) * Z ^ ((287 / 800 : ℝ) + ε) := by
    rw [← Real.rpow_add hZ0]
    congr 1
    ring
  have hw : 0 ≤ Z ^ (61 / 100 : ℝ) := Real.rpow_nonneg hZ0.le _
  calc Z ^ (61 / 100 : ℝ) * ‖f D Z‖ ≤ Z ^ (61 / 100 : ℝ) * (C * Z ^ ((287 / 800 : ℝ) + ε)) :=
        mul_le_mul_of_nonneg_left hfz hw
    _ = C * Z ^ (31 / 32 + ε) := by rw [e]; ring

end DedekindZetaZeroFree.Quantitative.Spectral
