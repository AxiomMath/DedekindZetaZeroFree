module

public import DedekindZetaZeroFree.Theta.Whittaker.Residues.NonzeroFourierCoefficient
public import DedekindZetaZeroFree.Eisenstein.Residues.FlatApproximationAndPeriods
public import DedekindZetaZeroFree.Eisenstein.Residues.TensorProducts.CoreCompactCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages ThetaExpansion TensorActionSource
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

include P C in
theorem exists_owned_flat_standard_fourier_ne_zero :
    ∃ b : Flat F ζ hζ (fullProductCompact R),
      Automorphic F ζ hζ ((ownedLiteralResidueFamily (full_product_compact_iwasawa R)).cleared b 0) ∧
      MomentSources.fourier R (KPWildKernelUpperBound.quotientHaar F)
        ((ownedLiteralResidueFamily (full_product_compact_iwasawa R)).cleared b 0) 1 ≠ 0 := by
  obtain ⟨x,g,hg⟩ := exists_coreResidue_period_ne_zero R P C
    (PrincipalOfKP.standardCharacter F) (PrincipalOfKP.standardCharacter_nontrivial F)
    (KPWildKernelUpperBound.quotientHaar F) inferInstance
  obtain ⟨M,HR,HP,HH,hrest⟩ := core_residue_hilbert_orthogonal_centers R P C x
  have hauto : Automorphic F ζ hζ
      ((ownedLiteralResidueFamily (full_product_compact_iwasawa R)).cleared
        (asLiteralFlat (coreFlatInsertion R P C x)) 0) := by
    rw [← coreResidue_eq_owned_cleared R P C x]
    exact coreResidue_raw_automorphic R P C x
  rw [coreResidue_eq_owned_cleared R P C x] at hg
  obtain ⟨b,hb,hne⟩ := ResidualOwnedDensity.exists_flat_period_ne_zero F ζ hζ M HR HP HH
    (fullProductCompact R) (full_product_compact_iwasawa R)
    (ownedLiteralResidueFamily (full_product_compact_iwasawa R))
    (asLiteralFlat (coreFlatInsertion R P C x)) hauto
    (PrincipalOfKP.standardCharacter F) (PrincipalOfKP.standardCharacter_nontrivial F)
    (KPWildKernelUpperBound.quotientHaar F) inferInstance g hg
  refine ⟨b,hb,?_⟩
  have hp : KPLiteralRaw.period F ζ hζ (PrincipalOfKP.standardCharacter F)
      (KPWildKernelUpperBound.quotientHaar F)
      ((ownedLiteralResidueFamily (full_product_compact_iwasawa R)).cleared b 0) =
      MomentSources.fourier R (KPWildKernelUpperBound.quotientHaar F)
      ((ownedLiteralResidueFamily (full_product_compact_iwasawa R)).cleared b 0) 1 := by
    unfold KPLiteralRaw.period MomentSources.fourier
    simp only [mul_one]
    rfl
  exact hp ▸ hne

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
