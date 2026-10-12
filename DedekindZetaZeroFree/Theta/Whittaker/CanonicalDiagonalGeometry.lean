module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.WordGeometry
public import DedekindZetaZeroFree.Metaplectic.Torus.SixthPowerDiagonalLifts

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open MomentSources NumberField KPAdelicCoverRestrictedProduct
open KPCplxCharacterHaar KPLiteralScalarHCCompactOrbit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def finiteDiagonalTuple (y : R.A.G) (q : KPFinitePlace F) :
    KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) :=
  if h : q ∈ R.A.Sf then
    KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12
      (Sum.inr q) (y.2 ⟨q, h⟩)
  else 1

@[simp] theorem finiteDiagonalTuple_at (y : R.A.G) (q : KPFinitePlace F)
    (hq : q ∈ R.A.Sf) :
    finiteDiagonalTuple R y q =
      KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12
        (Sum.inr q) (y.2 ⟨q, hq⟩) := by
  simp [finiteDiagonalTuple, hq]

@[simp] theorem finiteDiagonalTuple_off (y : R.A.G) (q : KPFinitePlace F)
    (hq : q ∉ R.A.Sf) : finiteDiagonalTuple R y q = 1 := by
  simp [finiteDiagonalTuple, hq]

def archDiagonalTuple (y : R.A.G) (w : InfinitePlace F) : ComplexGL2 :=
  KPCplxCharacterHaar.diagonal
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (R.A.complex_place w)).toMonoidHom (y.1 w))

theorem diagonalTuple_eq_finite_arch (y : R.A.G) :
    KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12
      (localIdele R y) =
    finiteTuple (R := R) (finiteDiagonalTuple R y) *
      KPLiteralChamber.sectionTuple F R.A.zeta12 R.A.primitive_zeta12
        (archDiagonalTuple R y) := by
  apply RestrictedProduct.ext
  intro p
  change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 p
    (Units.map (adeleEval F p) (localIdele R y)) =
    finiteTuple (R := R) (finiteDiagonalTuple R y) p *
      KPLiteralChamber.sectionTuple F R.A.zeta12 R.A.primitive_zeta12
        (archDiagonalTuple R y) p
  cases p with
  | inl w =>
    rw [DigitMasks.localIdele_arch R y w,
      finiteTuple_off (R := R) (finiteDiagonalTuple R y)
        (Sum.inl w) (fun _ => Sum.inl_ne_inr), one_mul]
    change KPLocalCover.sectionMap F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) _ =
      KPLocalCover.sectionMap F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) _
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [archDiagonalTuple, KPCplxCharacterHaar.diagonal,
        KPStandardLocalRootLifts.A, KubotaRankTwo.d, Matrix.GeneralLinearGroup.map]
    change (y.1 w : w.Completion) =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)) (y.1 w : w.Completion))
    exact ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm_apply_apply _).symm
  | inr q =>
    change _ = finiteTuple (R := R) (finiteDiagonalTuple R y) (Sum.inr q) * 1
    rw [mul_one]
    by_cases hq : q ∈ R.A.Sf
    · rw [DigitMasks.localIdele_finite R y q hq,
        finiteTuple_at (R := R) (finiteDiagonalTuple R y) ⟨q, hq⟩,
        finiteDiagonalTuple_at R y q hq]
    · have he : Units.map (adeleEval F (Sum.inr q)).toMonoidHom (localIdele R y) = 1 :=
        DigitMasks.localIdele_exterior R y q hq
      have hh := congrArg (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) he
      change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)
        (Units.map (adeleEval F (Sum.inr q)).toMonoidHom (localIdele R y)) = _
      rw [hh, KPStandardLocalRootLifts.A_one,
        finiteTuple_off (R := R) (finiteDiagonalTuple R y) (Sum.inr q)
          (fun p h => hq (Sum.inr.inj h ▸ p.property))]

theorem diagonal_eq_finite_arch (y : R.A.G) :
    MomentSources.diagonal R y =
      (finiteBase (R := R) (finiteDiagonalTuple R y)).val *
        KPLiteralScalarHCCompactOrbit.archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
          (archDiagonalTuple R y) := by
  rw [finiteBase_val]
  change scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (amalgamation F R.A.zeta12 R.A.primitive_zeta12
      (KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12
        (localIdele R y))) =
    scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (amalgamation F R.A.zeta12 R.A.primitive_zeta12
        (finiteTuple (R := R) (finiteDiagonalTuple R y))) *
    scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (amalgamation F R.A.zeta12 R.A.primitive_zeta12
        (KPLiteralChamber.sectionTuple F R.A.zeta12 R.A.primitive_zeta12
          (archDiagonalTuple R y)))
  rw [diagonalTuple_eq_finite_arch R y, map_mul, map_mul]

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
