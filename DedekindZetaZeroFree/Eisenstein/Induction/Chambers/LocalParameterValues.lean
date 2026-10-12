module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSections.GlobalScalarEvaluation
public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.ArchimedeanChamber
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.SignedWeylCellSections

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open NumberField MomentSources KPGlobalTorusFiniteStages FaithfulSource.RepairedInducing
open KPLocalPrincipalSeries KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open LiteralSource.CofactorChamber
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def rootCoordinate (y : KPAdeles F) : (p : KPHilbert.Place F) → FaithfulSource.RootPoint R p
  | .inl w => InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w) (y.1 w)
  | .inr q => y.2 q

theorem chamber_parameterValue_finite (q : KPFinitePlace F) (y : KPAdeles F)
    (a : Raw R) (z : ℂ) (f : Plus R N P C (.inr q)) :
    parameterValue R N P C (chamberRaw F ζ hζ y * a) z (.inr q) f =
      parameterKernel R N P C (fullCompact R P C) (.inr q) (a (.inr q)) z
        (rootCoordinate R y (.inr q)) f := by
  rw [parameterValue_finite]
  let h := finiteParameterInput R N P C q (fullCompact R P C q) z f
  have hg : KPPGLLocalCover.coverQuotient F ζ hζ (.inr q)
      ((chamberRaw F ζ hζ y * a) (.inr q)) =
      KPPGLLocalCover.W F ζ hζ (.inr q) *
        ((C.canonical q).borel.upperRoot (Multiplicative.ofAdd (y.2 q)) *
          KPPGLLocalCover.coverQuotient F ζ hζ (.inr q) (a (.inr q))) := by
    simp only [chamberRaw, RestrictedProduct.mul_apply,
      KPRationalAdelicSplitting.WTuple_eval, KPGlobalTorusFunctionData.rootTuple, map_mul]
    rw [KPForwardHomRepair.canonicalUpperRoot_eq F ζ hζ q (C.canonical q) (C.polarization q)]
    exact mul_assoc _ _ _
  rw [hg]
  change h.val (KPPGLLocalCover.W F ζ hζ (.inr q) * _) =
    h.val ((C.canonical q).borel.liftedW⁻¹ * (C.canonical q).borel.upperRoot
      (Multiplicative.ofAdd (y.2 q)) * _)
  rw [mul_assoc]
  exact LocalSignedChamber.section_unsigned_eq_signed F ζ hζ q
    (C.canonical q) (C.polarization q) z h _

theorem chamber_parameterValue_complex (w : InfinitePlace F) (y : KPAdeles F)
    (a : Raw R) (z : ℂ) (f : Plus R N P C (.inl w)) :
    parameterValue R N P C (chamberRaw F ζ hζ y * a) z (.inl w) f =
      parameterKernel R N P C (fullCompact R P C) (.inl w) (a (.inl w)) z
        (rootCoordinate R y (.inl w)) f := by
  rw [parameterValue_complex]
  have he : ((chamberRaw F ζ hζ y * a) (.inl w)).epsilon = (a (.inl w)).epsilon := by
    simp [RestrictedProduct.mul_apply, KPLocalCover.mul_epsilon,
      chamberRaw_arch_epsilon R, KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau,
      KPHilbert.B3, KPHilbert.B6_infinite]
  rw [he]
  apply congrArg (fun g => (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ
    (a (.inl w)).epsilon : ℂ) *
      KPComplexIntertwinerParameterMajorant.forwardSection z (complexInput f.val) g)
  change LiteralSource.complexMatrix R.A w ((chamberRaw F ζ hζ y * a) (.inl w)) = _
  simp only [RestrictedProduct.mul_apply, LiteralSource.complexMatrix, KPLocalCover.mul_g, map_mul]
  change LiteralSource.complexMatrix R.A w (chamberRaw F ζ hζ y (.inl w)) * _ = _
  rw [chamberRaw_complexMatrix R]
  rfl

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
