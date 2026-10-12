module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteExteriorProduct

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical NumberField
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_rationalUnit → eval_rationalUnit
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_localIdele → eval_localIdele
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def restrictTuple (E : Set (KPHilbert.Place F)) :
    KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 →*
    KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 where
  toFun a := ⟨fun w => if w ∈ E then a w else 1, by
    filter_upwards [a.property] with w hw
    change (if w ∈ E then a w else 1) ∈ _
    split_ifs
    · exact hw
    · exact (KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 w).one_mem⟩
  map_one' := by apply RestrictedProduct.ext; intro w; simp
  map_mul' a b := by
    apply RestrictedProduct.ext
    intro w
    change (if w ∈ E then a w * b w else 1) = (if w ∈ E then a w else 1) * (if w ∈ E then b w else 1)
    split_ifs <;> simp

def exteriorPlaces : Set (KPHilbert.Place F) := {w | ∃ p : ThetaBranch.ExteriorPrime R.A, w = Sum.inr p.val}
abbrev exteriorRestriction := restrictTuple R (exteriorPlaces R)
abbrev sRestriction := restrictTuple R (exteriorPlaces R)ᶜ

@[simp] theorem restrictTuple_eval (E : Set (KPHilbert.Place F))
    (a : KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (w : KPHilbert.Place F) : restrictTuple R E a w = if w ∈ E then a w else 1 := rfl

@[simp] theorem exteriorPlaces_arch (w : InfinitePlace F) : Sum.inl w ∉ exteriorPlaces R := by
  rintro ⟨p, h⟩; cases h
@[simp] theorem exteriorPlaces_finite (p : KPFinitePlace F) : Sum.inr p ∈ exteriorPlaces R ↔ p ∉ R.A.Sf := by
  constructor
  · rintro ⟨q, h⟩
    have he : p = q.val := Sum.inr_injective h
    exact he.symm ▸ q.property
  · intro hp; exact ⟨⟨p, hp⟩, rfl⟩

theorem splitTuple (a : KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12) :
    a = sRestriction R a * exteriorRestriction R a := by
  apply RestrictedProduct.ext
  intro w
  rw [RestrictedProduct.mul_apply]
  simp only [sRestriction, exteriorRestriction, restrictTuple_eval]
  by_cases hw : w ∈ exteriorPlaces R <;> simp [hw]

def reverseTuple (x : Fˣ) (y : R.A.G) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :=
  KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom x) *
    (KPRationalAdelicSplitting.WTuple F R.A.zeta12 R.A.primitive_zeta12 *
      KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 (localIdele R y) *
      KPRationalAdelicSplitting.NTuple F R.A.zeta12 R.A.primitive_zeta12 (digitParameter R m d))

theorem reverseTuple_exterior (x : Fˣ) (y : R.A.G) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : ThetaBranch.ExteriorPrime R.A) :
    reverseTuple R x y m d (Sum.inr p.val) =
      KPRationalAdelicSplitting.ACoordinates F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.localIdele F (Sum.inr p.val)
          (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)) (Sum.inr p.val) *
        KPRationalAdelicSplitting.WCoordinates F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
        KPRationalAdelicSplitting.NCoordinates F R.A.zeta12 R.A.primitive_zeta12 (digitParameter R m d) (Sum.inr p.val) := by
  unfold reverseTuple
  simp only [RestrictedProduct.mul_apply]
  rw [sDiagonal_exterior R y p.val p.property, mul_one]
  rw [← mul_assoc]
  congr 2
  change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) _ =
    KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) _
  have hr := eval_rationalUnit F (Sum.inr p.val) x
  have hl := eval_localIdele F (Sum.inr p.val) (Sum.inr p.val)
    (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)
  simp only [Pi.mulSingle_eq_same] at hl
  exact congrArg (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)) (hr.trans hl.symm)

theorem reverseTuple_period {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (x : Fˣ) (y : R.A.G) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    Function.HasFiniteMulSupport (ThetaExpansion.SignedExpansion.exteriorDigitFactor R C m x d) ∧
    fourier R C.sources.dq (C.realization.theta v) (restrictedLift R (reverseTuple R x y m d)) =
      (∏ᶠ p : ThetaBranch.ExteriorPrime R.A, ThetaExpansion.SignedExpansion.exteriorDigitFactor R C m x d p) *
      fourier R C.sources.dq (C.realization.theta v)
        (restrictedLift R (sRestriction R (reverseTuple R x y m d))) := by
  let b := reverseTuple R x y m d
  let a := exteriorRestriction R b
  let g := sRestriction R b
  obtain ⟨P, hP⟩ := exterior_tuple_finite_exceptional R a
  have h := fourier_exterior_tuple R C.factorization v a g
    (by intro p; simp [g, sRestriction, p.property])
    (by intro w hw; exact if_neg hw) P hP
  have he (p : ThetaBranch.ExteriorPrime R.A) : exteriorSlotValue R C.factorization p.val (a (Sum.inr p.val)) =
      ThetaExpansion.SignedExpansion.exteriorDigitFactor R C m x d p := by
    have ha : a (Sum.inr p.val) = b (Sum.inr p.val) := by simp [a, p.property]
    rw [ha]
    change exteriorSlotValue R C.factorization p.val (reverseTuple R x y m d (Sum.inr p.val)) = _
    rw [reverseTuple_exterior]
    rfl
  simp_rw [he] at h
  refine ⟨h.1, ?_⟩
  have hb := congrArg (restrictedLift R) (splitTuple R b)
  rw [map_mul] at hb
  rw [hb]
  exact h.2

end DedekindZetaZeroFree.OrbitExpansion

end
