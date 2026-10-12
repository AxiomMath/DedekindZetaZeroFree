module

public import DedekindZetaZeroFree.Metaplectic.Torus.NormalizedResidueCharacterExtensions
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.VanishingAndCompactCoefficients

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry
open scoped NumberField
open NumberField IsDedekindDomain KPLocalExceptionalConstruction
variable (F : Type) [Field F] [NumberField F]
 (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
local notation "W" => KPPGLLocalCover.W F ζ hζ (Sum.inr q)
local notation "N" => KPPGLLocalCover.N F ζ hζ (Sum.inr q)
local notation "L" => KPPGLLocalCover.LowerN F ζ hζ (Sum.inr q)
local notation "A" => KPPGLLocalCover.A F ζ hζ (Sum.inr q)

private theorem w_upper (t : LocalField F q) : W * N t = L t * W := by
  exact (mul_inv_eq_iff_eq_mul).mp
    (KPRankOneJacquetZeroCompactCoefficients.weyl_conjugates_upper F ζ hζ q t)

private theorem lower_diagonal (t : LocalField F q) (p : (LocalField F q)ˣ) :
    L t * A p = A p * L ((p : LocalField F q) * t) := by
  have hw : W * W = 1 := by simpa only [pow_two] using KPPGLLocalCover.W_sq F ζ hζ (Sum.inr q)
  have hl (z : LocalField F q) : L z = W * N z * W := by
    rw [w_upper, mul_assoc, hw, mul_one]
  rw [hl t, hl ((p : LocalField F q) * t)]
  simp only [mul_assoc]
  rw [KPCorrectedBruhatLifts.quotient_weyl_diagonal F ζ hζ (Sum.inr q) p]
  rw [← mul_assoc (N t) (A p⁻¹) W, KPCorrectedBruhatLifts.quotient_upper_diagonal]
  have he : t / (p⁻¹ : (LocalField F q)ˣ) = (p : LocalField F q) * t := by
    simp [div_eq_mul_inv, mul_comm]
  rw [he]
  simp only [← mul_assoc]
  rw [KPCorrectedBruhatLifts.quotient_weyl_diagonal, inv_inv]

private theorem diagonal_upper (p : (LocalField F q)ˣ) (t : LocalField F q) :
    A p * N t = N ((p : LocalField F q) * t) * A p := by
  rw [KPCorrectedBruhatLifts.quotient_upper_diagonal]
  congr 2
  field_simp

private theorem minus_diagonal (z : (LocalField F q)ˣ) :
    A (-1) * A (-z) = A z := by
  have hc (a b : (LocalField F q)ˣ) : (KPHilbert.B3 F ζ hζ (Sum.inr q) a b)^3 = 1 := by
    apply Subtype.ext
    exact (KPHilbert.B3 F ζ hζ (Sum.inr q) a b).property
  have hneg := KubotaDefectSymbolAlgebra.neg_one_left _ _ _
    (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1 hc (-z)
  rw [KPPGLLocalCover.A_mul, hneg]
  simp

theorem signed_double_kernel_same_diagonal
    (S : CanonicalFiniteInducingData F ζ hζ q)
    (p u : (LocalField F q)ˣ) (x : LocalField F q) :
    KPRankOneShellContinuation.kernelW (LocalField F q) S.borel .minus *
      N (u : LocalField F q) * (A p * W * N x) =
    N (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
      A (u⁻¹ ^ (2 : ℕ)) * A p * L (x + (p : LocalField F q) / u) * W := by
  have hk : KPRankOneShellContinuation.kernelW (LocalField F q) S.borel .minus = A (-1) * W :=
    (S.openCell S.polarization).weyl_eq
  rw [hk]
  simp only [mul_assoc]
  rw [← mul_assoc W (N (u : LocalField F q)), KPCorrectedBruhatLifts.quotient_weyl_upper]
  simp only [mul_assoc]
  rw [← mul_assoc (A (-1)) (N _), diagonal_upper]
  simp only [Units.val_neg, Units.val_one, neg_one_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (A (-1)) (A _), minus_diagonal]
  rw [← mul_assoc (L _) (A p), lower_diagonal]
  simp only [mul_assoc]
  rw [w_upper]
  rw [← mul_assoc (L _) (L _), ← KPPGLLocalCover.LowerN_add]
  simp only [div_eq_mul_inv, Units.val_inv_eq_inv_val, add_comm, mul_assoc]

theorem diagonalLift_index_zero_eq_eta (π : (LocalField F q)ˣ) (i : Fin 3) :
    KPTameTransposeKernelUnfolding.diagonalLift F ζ hζ q π ((i.val : ℤ), 0) =
      KPTameJacquetTestDuality.eta F ζ hζ q π i := by
  simp [KPTameTransposeKernelUnfolding.diagonalLift, KPTameJacquetTestDuality.eta,
    KPPGLLocalCover.A, KPStandardLocalRootLifts.A]

theorem signed_double_kernel_diagonal_index
    (S : CanonicalFiniteInducingData F ζ hζ q)
    (π u : (LocalField F q)ˣ) (i : Fin 3) (x : LocalField F q) :
    KPRankOneShellContinuation.kernelW (LocalField F q) S.borel .minus *
      N (u : LocalField F q) * (KPTameJacquetTestDuality.eta F ζ hζ q π i * W * N x) =
    N (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
      A (u⁻¹ ^ (2 : ℕ)) *
      KPTameTransposeKernelUnfolding.diagonalLift F ζ hζ q π ((i.val : ℤ), 0) *
      L (x + (π ^ i.val : (LocalField F q)ˣ) / u) * W := by
  rw [diagonalLift_index_zero_eq_eta]
  exact signed_double_kernel_same_diagonal F ζ hζ q S (π ^ i.val) u x

end DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry

end
