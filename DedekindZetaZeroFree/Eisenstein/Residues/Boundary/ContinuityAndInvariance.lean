module

public import DedekindZetaZeroFree.Eisenstein.Residues.UpperConstantTerm.UnipotentDescent

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open ResidualBoundaryInvariance
open _root_.DedekindZetaZeroFree.KPMsRationalCompactCrossPairing renaming compact_core_scalar_continuous → compact_core_scalar_continuous
open _root_.DedekindZetaZeroFree.KPMsRationalCompactCrossPairing renaming compact_source_core_smooth → compact_source_core_smooth
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "G" => KPGlobalTorusFunctionData.G F ζ hζ
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
local notation "Source" => KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ)

theorem boundaryProduct_continuous (f : Source) (x : V) :
    Continuous (boundaryProduct R P C f x) := by
  have hf : Continuous f.val.val := compact_core_scalar_continuous _ f.val
    (compact_source_core_smooth f.property)
  have hx := upper_continuous (coreResidue R P C x)
    (coreResidue_raw_automorphic R P C x).1.1 (coreResidue_rational_subgroup R P C x)
  unfold boundaryProduct
  rw [KPContFlatSourceRecipe.flatR_zero]
  exact hf.mul hx.star

theorem boundaryProduct_unipotent (f : Source) (x : V)
    (a : KPGlobalTorusFunctionData.Adeles F) (g : G) :
    boundaryProduct R P C f x (KPGlobalTorusFunctionData.N F ζ hζ a*g) =
      boundaryProduct R P C f x g := by
  unfold boundaryProduct
  rw [source_unipotent]
  change _ * star (KPGlobalResidualConstruction.upperConstantTerm F ζ hζ
    (KPWildKernelUpperBound.quotientHaar F) (coreResidue R P C x) (_*g)) = _
  rw [upper_unipotent _ (coreResidue_rational_subgroup R P C x)]
  rfl

theorem coreResidue_upper_central (x : V) (ε : rootsOfUnity 3 F) (g : G) :
    KPGlobalResidualConstruction.upperConstantTerm F ζ hζ
      (KPWildKernelUpperBound.quotientHaar F) (coreResidue R P C x)
      (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε*g) =
    (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
    KPGlobalResidualConstruction.upperConstantTerm F ζ hζ
      (KPWildKernelUpperBound.quotientHaar F) (coreResidue R P C x) g := by
  unfold KPGlobalResidualConstruction.upperConstantTerm
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with q
  have hz (a : G) : a * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε =
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * a :=
    Subgroup.mem_center_iff.mp
      (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε,rfl⟩) a
  rw [← mul_assoc,hz,mul_assoc]
  exact (coreResidue_raw_automorphic R P C x).2.2 ε _

theorem boundaryProduct_central (f : Source) (x : V)
    (ε : rootsOfUnity 3 F) (g : G) :
    boundaryProduct R P C f x (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε*g) =
      boundaryProduct R P C f x g := by
  unfold boundaryProduct
  rw [source_central]
  change _ * star (KPGlobalResidualConstruction.upperConstantTerm F ζ hζ
    (KPWildKernelUpperBound.quotientHaar F) (coreResidue R P C x) (_*g)) = _
  rw [coreResidue_upper_central,star_mul]
  have hχ : star (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) = 1 := by
    rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Circle.normSq_coe,Complex.ofReal_one]
  calc
    _ = (star (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ)) * boundaryProduct R P C f x g := by
      unfold boundaryProduct KPGlobalResidualConstruction.upperConstantTerm
      ring
    _ = _ := by rw [hχ,one_mul]; rfl

theorem boundaryProduct_right_level
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (f : Source) (x : V)
    (hf : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ U → f.val.val (g*u)=f.val.val g)
    (hx : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ U →
      coreResidue R P C x (g*u)=coreResidue R P C x g)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U) (g : G) :
    boundaryProduct R P C f x (g*u.val)=boundaryProduct R P C f x g := by
  unfold boundaryProduct
  rw [KPContFlatSourceRecipe.flatR_zero,hf g u.val u.property]
  congr 2
  apply integral_congr_ae
  filter_upwards with q
  rw [← mul_assoc,hx _ u.val u.property]
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
