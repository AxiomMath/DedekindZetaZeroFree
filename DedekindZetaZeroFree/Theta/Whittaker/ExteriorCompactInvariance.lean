module

public import DedekindZetaZeroFree.Theta.Whittaker.RankOneSlotPeriods

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory KPAdelicCoverRestrictedProduct
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

abbrev rawToGroup : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 →* Group R :=
  (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12).comp
    (amalgamation F R.A.zeta12 R.A.primitive_zeta12)

lemma raw_commute_single (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (p : KPHilbert.Place F) (hp : a p = 1)
    (b : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p) :
    Commute a (localToRestricted F R.A.zeta12 R.A.primitive_zeta12 p b) := by
  apply RestrictedProduct.ext
  intro w
  by_cases hw : w = p
  · subst w
    simp [RestrictedProduct.mul_apply, hp, localToRestricted]
  · simp [RestrictedProduct.mul_apply, localToRestricted,
      RestrictedProduct.mulSingle_eq_of_ne, hw]

lemma group_commute_single (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (p : KPFinitePlace F) (hp : a (Sum.inr p) = 1)
    (b : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)) :
    Commute (rawToGroup R a) (finiteLift R p b) :=
  (raw_commute_single R a (Sum.inr p) hp b).map (rawToGroup R)

lemma diagonal_commute_exterior (y : R.A.G) (p : ThetaBranch.ExteriorPrime R.A)
    (b : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)) :
    Commute (diagonal R y) (finiteLift R p.val b) := by
  apply group_commute_single R
    (KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 (MomentSources.localIdele R y)) p.val
  change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
    (Units.map (adeleEval F (Sum.inr p.val)) (MomentSources.localIdele R y)) = 1
  have he := DigitMasks.localIdele_exterior R y p.val p.property
  change Units.map (adeleEval F (Sum.inr p.val)).toMonoidHom (MomentSources.localIdele R y) = 1 at he
  exact (congrArg (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)) he).trans
    (KPStandardLocalRootLifts.A_one F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))

lemma diagonal_commute_exterior_root (y : R.A.G) (p : ThetaBranch.ExteriorPrime R.A)
    (t : p.val.adicCompletion F) :
    Commute (diagonal R y) (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (KPRationalAdelicSplitting.localAdele F (Sum.inr p.val) t)) := by
  rw [← ExteriorWhittakerValues.StoredWhittaker.finite_root_injection R p.val t]
  exact diagonal_commute_exterior R y p (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12
    (Sum.inr p.val) t)

lemma fourier_full_exterior {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (k : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (hk : ∀ w, k w ∈ DigitMasks.exteriorFactor R w) (g : Group R) :
    fourier R Q.dq (T.theta v) (g * rawToGroup R k) = fourier R Q.dq (T.theta v) g := by
  unfold MomentSources.fourier
  apply integral_congr_ae
  filter_upwards [] with q
  rw [← mul_assoc]
  exact congrArg (fun z : ℂ => z * star (adelicTraceQuotientCharacter F q : ℂ))
    (DigitMasks.theta_full_exterior R T v k hk _)

end DedekindZetaZeroFree.OrbitExpansion

end
