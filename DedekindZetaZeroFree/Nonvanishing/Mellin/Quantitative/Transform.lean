module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.SpectralFunction

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.MellinTransform

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def g (Z : ℝ) : ℂ :=
  if 0 < Z then (Z : ℂ) ^ (61 / 100 : ℂ) * Spectral.f D Z else 0

def T (s : ℂ) : ℂ := mellin (g D) (-s)

theorem T_eq (s : ℂ) :
    T D s = ∫ Z : ℝ in Set.Ioi 0,
      Spectral.f D Z * (Z : ℂ) ^ (-s + 61 / 100) / (Z : ℂ) := by
  unfold T mellin
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro Z hZ
  have hZ' : (0 : ℝ) < Z := hZ
  have hne : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ'.ne'
  have h1 : (Z : ℂ) ^ (-s - 1) = (Z : ℂ) ^ (-s) / (Z : ℂ) := by
    rw [Complex.cpow_sub _ _ hne, Complex.cpow_one]
  have h2 : (Z : ℂ) ^ (-s + 61 / 100) = (Z : ℂ) ^ (-s) * (Z : ℂ) ^ (61 / 100 : ℂ) :=
    Complex.cpow_add _ _ hne
  simp only [g, if_pos hZ', smul_eq_mul]
  rw [h1, h2]
  ring

theorem g_of_nonpos (Z : ℝ) (hZ : Z ≤ 0) : g D Z = 0 := by
  simp [g, not_lt.mpr hZ]

end

end DedekindZetaZeroFree.Quantitative.MellinTransform
