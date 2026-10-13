module

public import DedekindZetaZeroFree.Moments.Principal.Contour.ZResidueBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalZShift

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel DedekindZetaZeroFree.Quantitative.PrincipalWShift
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def Rz (Z : ℝ) : ℂ :=
  ∑ᶠ u ∈ principalRows D, comparisonVerticalIntegral Scales.rightLine (fun ξ =>
    comparisonVerticalIntegral (1 / 20) (fun z => wResidue D u ξ z Z))

theorem E_remainder :
    Scales.kernelExponent Scales.rightLine 1 (1 / 20) = Scales.mainExponent - 384999 / 10000000 := by
  unfold Scales.kernelExponent Scales.rightLine Scales.contourOffset Scales.xExponent Scales.smoothingExponent Scales.yExponent Scales.mainExponent
  norm_num

theorem Jwres_eq (Z : ℝ) (hZ : 2 ≤ Z) :
    Jwres D Z = Spectral.c₀ D * Spectral.f D Z + Rz D Z := by
  have h1 := PrincipalZShiftAux.Jwres_sub_Rz D Z hZ
  rw [PrincipalZShiftAux.zResidue_sum_eq D Z hZ] at h1
  unfold Rz
  linear_combination h1

theorem Rz_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖Rz D Z‖ ≤ C * Z ^ (Scales.mainExponent - 384999 / 10000000) := by
  unfold Rz
  exact PrincipalZShiftAux.Rz_integral_bound D

end

end DedekindZetaZeroFree.Quantitative.PrincipalZShift
