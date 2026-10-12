module

public import DedekindZetaZeroFree.Theta.Whittaker.SphericalFactorizationForms

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources KPAdelicCoverRestrictedProduct KPLiteralChamber
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming sectionTuple_insertion → sectionTuple_insertion
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def actualArchDiagonal (y : R.A.G) (w : InfinitePlace F) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).toRingHom
      (KubotaRankTwo.d _ (y.1 w) 1)

theorem diagonal_arch_insertion (y : R.A.G) :
    diagonal R (y.1,1) = KPSmoothActualFlowData.archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12
      (fun w => Matrix.ProjGenLinGroup.mk (actualArchDiagonal R y w)) := by
  rw [←sectionTuple_insertion]
  unfold diagonal KPRationalAdelicSplitting.pglA KPRationalAdelicSplitting.A
  apply congrArg (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12)
  apply congrArg (amalgamation F R.A.zeta12 R.A.primitive_zeta12)
  apply RestrictedProduct.ext
  intro p
  cases p with
  | inl w =>
    change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
      (Units.map (adeleEval F (Sum.inl w)).toMonoidHom (MomentSources.localIdele R (y.1,1))) = _
    rw [selected_localIdele_arch]
    unfold KPStandardLocalRootLifts.A sectionTuple actualArchDiagonal
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).symm_apply_apply _).symm
  | inr q =>
    change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)
      (Units.map (adeleEval F (Sum.inr q)).toMonoidHom (MomentSources.localIdele R (y.1,1))) = 1
    by_cases hq:q∈R.A.Sf
    · rw [selected_localIdele_finite R (y.1,1) ⟨q,hq⟩]
      exact KPStandardLocalRootLifts.A_one _ _ _ _
    · rw [selected_localIdele_exterior R (y.1,1) q hq]
      exact KPStandardLocalRootLifts.A_one _ _ _ _

theorem diagonal_standard_action (y:R.A.G) (w:InfinitePlace F)
    (v:KPCplxActualImage.Theta KPReferenceChange.StandardComplexImage.frequency) :
    KPReferenceChange.StandardComplexImage.action R.A w
      (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) (y.1 w)) v =
      KPCplxActualImage.imageAction KPReferenceChange.StandardComplexImage.frequency
        (Matrix.ProjGenLinGroup.mk (actualArchDiagonal R y w)) v := by
  unfold KPReferenceChange.StandardComplexImage.action
  have hc : KPReferenceChange.StandardComplexImage.centralCharacter R.A w
      (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) (y.1 w))=1 := by
    change KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12 1=1
    exact map_one _
  rw [hc,Units.val_one,one_smul]
  rfl

end DedekindZetaZeroFree.RootDerivatives

end
