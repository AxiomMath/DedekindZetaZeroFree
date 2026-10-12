module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.GlobalProduct
public import DedekindZetaZeroFree.Theta.Digits.ExteriorCongruences

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open MomentSources NumberField MeasureTheory KPAdelicCoverRestrictedProduct KPLiteralScalarHCCompactOrbit
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

abbrev tupleLift : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 →* Group R :=
  (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12).comp
    (amalgamation F R.A.zeta12 R.A.primitive_zeta12)

def sWeylTuple : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 :=
  ⟨fun w => match w with
    | Sum.inl u => KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl u)
    | Sum.inr p => if p ∈ R.A.Sf then KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) else 1, by
      have h := KPRationalAdelicSplitting.WCoordinates_restricted F R.A.zeta12 R.A.primitive_zeta12
      filter_upwards [h] with w hw
      cases w with
      | inl w => exact hw
      | inr p => dsimp only; split_ifs <;> first | exact hw | exact Subgroup.one_mem _⟩

def exteriorWeylTuple : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 :=
  (sWeylTuple R)⁻¹ * KPRationalAdelicSplitting.WTuple F R.A.zeta12 R.A.primitive_zeta12

theorem exteriorWeylTuple_mem (w : KPHilbert.Place F) :
    exteriorWeylTuple R w ∈ DigitMasks.exteriorFactor R w := by
  cases w with
  | inl w =>
    change (KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w))⁻¹ * _ ∈ (⊥ : Subgroup _)
    simp
  | inr p =>
    by_cases hp : p ∈ R.A.Sf
    · simp [exteriorWeylTuple,sWeylTuple,DigitMasks.exteriorFactor,hp]
    · change (if p ∈ R.A.Sf then KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) else 1)⁻¹ *
        KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) ∈ _
      rw [if_neg hp,inv_one,one_mul]
      simp only [DigitMasks.exteriorFactor,dif_pos hp]
      refine ⟨KPStandardLocalRootLifts.integralW F p, ?_⟩
      change KPLocalCover.CubicGL2Raw.mk _ _ = _
      exact (KPStandardLocalRootLifts.W_eq_compact F R.A.zeta12 R.A.primitive_zeta12 p
        (fun h3 => DigitMasks.exterior_not_bad R p hp (Or.inr h3))).symm

theorem fourier_right_sWeyl {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (g : Group R) :
    fourier R Q.dq (T.theta v) (g * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12) =
      fourier R Q.dq (T.theta v) (g * tupleLift R (sWeylTuple R)) := by
  have hi (q : KPAdditiveQuotient F) := DigitMasks.theta_full_exterior R T v
    (exteriorWeylTuple R) (exteriorWeylTuple_mem R)
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) *
      (g * tupleLift R (sWeylTuple R)))
  have he : tupleLift R (sWeylTuple R) * tupleLift R (exteriorWeylTuple R) =
      KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 := by
    rw [← map_mul]
    simp only [exteriorWeylTuple,mul_inv_cancel_left]
    rfl
  have hint := SheetRescaling.selected_cleared_fourier_integrable T v 0
    (Metric.mem_ball_self T.radius_pos) (g * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)
  unfold MomentSources.fourier
  apply integral_congr_ae
  filter_upwards with q
  have h := hi q
  change T.theta v ((_ * (g * tupleLift R (sWeylTuple R))) * tupleLift R (exteriorWeylTuple R)) = _ at h
  rw [mul_assoc,mul_assoc,he] at h
  rw [h]

def finiteWeylRaw (z : R.A.G) (q : KPFinitePlace F) :
    KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) :=
  KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)
    (Units.map (adeleEval F (Sum.inr q)) (localIdele R z)) *
      KPRationalAdelicSplitting.WCoordinates F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)

def archWeylMatrix (z : R.A.G) (w : InfinitePlace F) : ComplexGL2 :=
  diagonal (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).toMonoidHom (z.1 w)) * weyl

theorem diagonal_sWeyl_geometry (z : R.A.G) :
    diagonal R z * tupleLift R (sWeylTuple R) =
      (finiteBase (R := R) (finiteWeylRaw R z)).val *
        archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12 (archWeylMatrix R z) := by
  rw [finiteBase_val]
  change tupleLift R (KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 (localIdele R z)) *
    tupleLift R (sWeylTuple R) = tupleLift R (finiteTuple (R := R) (finiteWeylRaw R z)) *
      tupleLift R (KPLiteralChamber.sectionTuple F R.A.zeta12 R.A.primitive_zeta12 (archWeylMatrix R z))
  rw [← map_mul,← map_mul]
  apply congrArg (tupleLift R)
  apply RestrictedProduct.ext
  intro p
  cases p with
  | inl w =>
    change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
      (Units.map (adeleEval F (Sum.inl w)) (localIdele R z)) *
      KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) =
      finiteTuple (R := R) (finiteWeylRaw R z) (Sum.inl w) * _
    rw [SheetRescaling.localIdele_eval_arch R z w,
      finiteTuple_off (finiteWeylRaw R z) (Sum.inl w) (fun _ => Sum.inl_ne_inr),one_mul]
    change KPLocalCover.sectionMap F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) _ *
      KPLocalCover.sectionMap F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) _ =
      KPLocalCover.sectionMap F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) _
    change KPLocalCover.CubicGL2Raw.mk _ _ = KPLocalCover.CubicGL2Raw.mk _ _
    simp only [KPLocalChartTopology.complex_sigmaTwo_eq_one,mul_one,KPLocalCover.sectionMap]
    congr 1
    change KubotaRankTwo.d (KPHilbert.Completion F (Sum.inl w)) (z.1 w) 1 *
      KPStandardLocalRootLifts.weylSwap (KPHilbert.Completion F (Sum.inl w)) = _
    rw [archWeylMatrix,map_mul]
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [archWeylMatrix,KPCplxCharacterHaar.diagonal,weyl,KubotaRankTwo.d,KPStandardLocalRootLifts.weylSwap,
        Matrix.mul_apply,Fin.sum_univ_two,Matrix.GeneralLinearGroup.map]
    change (z.1 w : w.Completion) =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)) (z.1 w : w.Completion))
    exact ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm_apply_apply _).symm
  | inr q =>
    change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)
      (Units.map (adeleEval F (Sum.inr q)) (localIdele R z)) *
      (if q ∈ R.A.Sf then KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) else 1) =
      finiteTuple (R := R) (finiteWeylRaw R z) (Sum.inr q) * 1
    rw [mul_one]
    by_cases hq : q ∈ R.A.Sf
    · rw [if_pos hq,finiteTuple_at (finiteWeylRaw R z) ⟨q,hq⟩]
      rfl
    · have he : Units.map (adeleEval F (Sum.inr q)).toMonoidHom (localIdele R z) = 1 :=
        DigitMasks.localIdele_exterior R z q hq
      rw [if_neg hq]
      have hh := congrArg (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) he
      change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)
        (Units.map (adeleEval F (Sum.inr q)).toMonoidHom (localIdele R z)) * 1 = _
      rw [hh,KPStandardLocalRootLifts.A_one,one_mul,
        finiteTuple_off (finiteWeylRaw R z) (Sum.inr q) (fun p h => hq (Sum.inr.inj h ▸ p.property))]

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
