module

public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.FlatSectionExtension
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AdelicCharts.TraceBoxFubini

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open KPLocalPrincipalSeries
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def chamberRaw (F : Type) [Field F] [NumberField F] (zeta : F) (hzeta : IsPrimitiveRoot zeta 12)
    (x : KPGlobalTorusFunctionData.Adeles F) :
    KPAdelicCoverRestrictedProduct.RestrictedCover F zeta hzeta :=
  KPRationalAdelicSplitting.WTuple F zeta hzeta * KPGlobalTorusFunctionData.rootTuple F zeta hzeta x

theorem chamberRaw_arch_epsilon (x : KPGlobalTorusFunctionData.Adeles F) (w : InfinitePlace F) :
    (chamberRaw F ζ hζ x (Sum.inl w)).epsilon = 1 := by
  simp [chamberRaw, KPGlobalTorusFunctionData.rootTuple,
    KPStandardLocalRootLifts.W, KPStandardLocalRootLifts.N,
    KPLocalCover.mul_epsilon, KPLocalCover.sectionMap, KPLocalCover.sigmaTwo,
    KubotaElementaryLastArgument.tau, KPHilbert.B3, KPHilbert.B6_infinite]

theorem chamberRaw_complexMatrix (x : KPGlobalTorusFunctionData.Adeles F) (w : InfinitePlace F) :
    LiteralSource.complexMatrix R.A w
      (chamberRaw F ζ hζ x (Sum.inl w)) =
      KPCplxCharacterHaar.weyl * KPCplxCharacterHaar.upperUnipotent
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w) (x.1 w)) := by
  simp only [LiteralSource.complexMatrix,
    chamberRaw, RestrictedProduct.mul_apply,
    KPRationalAdelicSplitting.WTuple_eval, KPGlobalTorusFunctionData.rootTuple,
    KPLocalCover.mul_g, KPStandardLocalRootLifts.W, KPStandardLocalRootLifts.N,
    KPLocalCover.sectionMap_g, map_mul]
  apply congrArg₂ (· * ·)
  · apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [KPStandardLocalRootLifts.weylSwap, KPCplxCharacterHaar.weyl]
  · apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [KubotaRankTwo.n, KPCplxCharacterHaar.upperUnipotent,
        KPAdelicCoverRestrictedProduct.adeleEval]
    rfl

theorem chamberRaw_archCylinder (s : ℂ) (x : KPGlobalTorusFunctionData.Adeles F) :
    (∏ w : InfinitePlace F,
      (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ
        (chamberRaw F ζ hζ x (Sum.inl w)).epsilon : ℂ) *
          KPComplexIntertwinerParameterMajorant.forwardSection s
            KPComplexStandardIntertwinerGerm.compactSpherical
            (LiteralSource.complexMatrix R.A w
              (chamberRaw F ζ hζ x (Sum.inl w)))) =
        TraceBox.archCylinder F s x.1 := by
  simp only [chamberRaw_arch_epsilon R, map_one, Units.val_one,
    one_mul, chamberRaw_complexMatrix R]
  let := primitive12_totallyComplex F ζ hζ
  simp only [TraceBox.archCylinder, TateTensorProfile.archTensor,
    PoissonArch.infiniteAdeleToSpace_coordinates, InfiniteAdeleRing.ringEquiv_mixedSpace_apply,
    TraceBox.complexIntegrand, mul_one]
  let e : {w : InfinitePlace F // w.IsComplex} ≃ InfinitePlace F :=
    Equiv.subtypeUnivEquiv (fun w => NumberField.IsTotallyComplex.isComplex w)
  exact (Fintype.prod_equiv e (fun w =>
    KPComplexIntertwinerParameterMajorant.forwardSection s
      KPComplexStandardIntertwinerGerm.compactSpherical
      (KPCplxCharacterHaar.weyl * KPCplxCharacterHaar.upperUnipotent
        (InfinitePlace.Completion.extensionEmbedding w.val (x.1 w.val)))) _
    (fun w => by rfl)).symm

end DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber

end
