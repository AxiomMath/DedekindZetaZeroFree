module

public import DedekindZetaZeroFree.Theta.Periods.SPlaceWeylRestriction

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical NumberField
open _root_.DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw renaming centralSingle → centralSingle
open _root_.DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw renaming centralProduct_single → centralProduct_single
open _root_.DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw renaming centralTupleMap_single → centralTupleMap_single
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem restrictedLift_centralTuple (e : KPAdelicCoverRestrictedProduct.CentralTuples F) :
    restrictedLift R (KPAdelicCoverRestrictedProduct.centralTupleMap F R.A.zeta12 R.A.primitive_zeta12 e) =
      KPAdelicCoverRestrictedProduct.pglCentralInjection F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.centralProduct F e) := by
  let s := centralSingle F (KPAdelicCoverRestrictedProduct.distinguishedPlace F)
    (KPAdelicCoverRestrictedProduct.centralProduct F e)
  have he : KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.centralTupleMap F R.A.zeta12 R.A.primitive_zeta12 s) =
      KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.centralTupleMap F R.A.zeta12 R.A.primitive_zeta12 e) := by
    apply div_eq_one.mp
    rw [← map_div, ← map_div]
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨s / e, ?_, rfl⟩
    change KPAdelicCoverRestrictedProduct.centralProduct F (s / e) = 1
    rw [map_div]
    change KPAdelicCoverRestrictedProduct.centralProduct F
      (centralSingle F _ (KPAdelicCoverRestrictedProduct.centralProduct F e)) / _ = 1
    change KPAdelicCoverCertificatesRaw.centralProduct F
      (centralSingle F _ (KPAdelicCoverRestrictedProduct.centralProduct F e)) / _ = 1
    rw [centralProduct_single]
    exact div_self' _
  have hs : KPAdelicCoverRestrictedProduct.centralTupleMap F R.A.zeta12 R.A.primitive_zeta12 s =
      KPAdelicCoverRestrictedProduct.localToRestricted F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.distinguishedPlace F)
        (KPLocalCover.centralInjection F R.A.zeta12 R.A.primitive_zeta12
          (KPAdelicCoverRestrictedProduct.distinguishedPlace F) (KPAdelicCoverRestrictedProduct.centralProduct F e)) :=
    centralTupleMap_single F R.A.zeta12 R.A.primitive_zeta12 _ _
  rw [hs] at he
  exact (congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12) he).symm

def sDiagonalDefect (x y : R.A.G) : KPAdelicCoverRestrictedProduct.CentralTuples F :=
  ∏ p : R.A.Sf, centralSingle F (Sum.inr p.val)
    (KPHilbert.B3 F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (x.2 p) (y.2 p) ^ 2)

theorem sDiagonalDefect_finite (x y : R.A.G) (p : KPFinitePlace F) (hp : p ∈ R.A.Sf) :
    sDiagonalDefect R x y (Sum.inr p) =
      KPHilbert.B3 F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) (x.2 ⟨p,hp⟩) (y.2 ⟨p,hp⟩) ^ 2 := by
  unfold sDiagonalDefect
  change (RestrictedProduct.evalMonoidHom _ (Sum.inr p)) _ = _
  rw [map_prod]
  simp only [RestrictedProduct.evalMonoidHom_apply]
  rw [Finset.prod_eq_single (⟨p,hp⟩ : R.A.Sf)]
  · exact RestrictedProduct.mulSingle_eq_same _ _ _
  · intro q _ hq
    apply RestrictedProduct.mulSingle_eq_of_ne
    exact fun he => hq (Subtype.ext (Sum.inr_injective he.symm))
  · simp

theorem sDiagonalDefect_off (x y : R.A.G) (w : KPHilbert.Place F)
    (hw : ∀ p : R.A.Sf, w ≠ Sum.inr p.val) : sDiagonalDefect R x y w = 1 := by
  unfold sDiagonalDefect
  change (RestrictedProduct.evalMonoidHom _ w) _ = 1
  rw [map_prod]
  simp only [RestrictedProduct.evalMonoidHom_apply]
  apply Finset.prod_eq_one
  intro p _
  exact RestrictedProduct.mulSingle_eq_of_ne _ _ (hw p)

theorem sDiagonalTuple_mul (x y : R.A.G) :
    sDiagonalTuple R x * sDiagonalTuple R y =
      KPAdelicCoverRestrictedProduct.centralTupleMap F R.A.zeta12 R.A.primitive_zeta12 (sDiagonalDefect R x y) *
        sDiagonalTuple R (x * y) := by
  apply RestrictedProduct.ext
  intro w
  change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 w
      (Units.map (KPAdelicCoverRestrictedProduct.adeleEval F w).toMonoidHom (localIdele R x)) *
    KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 w
      (Units.map (KPAdelicCoverRestrictedProduct.adeleEval F w).toMonoidHom (localIdele R y)) =
    KPLocalCover.centralInjection F R.A.zeta12 R.A.primitive_zeta12 w (sDiagonalDefect R x y w) *
    KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 w
      (Units.map (KPAdelicCoverRestrictedProduct.adeleEval F w).toMonoidHom (localIdele R (x * y)))
  rw [IdeleInsertion.localIdele_mul, map_mul, KPStandardLocalRootLifts.A_mul]
  congr 2
  cases w with
  | inl w =>
    rw [sDiagonalDefect_off R x y _ (by intro p h; cases h)]
    simp [KPHilbert.B3, KPHilbert.B6_infinite]
  | inr p =>
    by_cases hp : p ∈ R.A.Sf
    · rw [sDiagonalDefect_finite R x y p hp]
      have hx := DigitMasks.localIdele_finite R x p hp
      have hy := DigitMasks.localIdele_finite R y p hp
      change Units.map (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p)).toMonoidHom (localIdele R x) = _ at hx
      change Units.map (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p)).toMonoidHom (localIdele R y) = _ at hy
      rw [hx, hy]
    · rw [sDiagonalDefect_off R x y _ (by
        intro q he
        exact hp ((Sum.inr_injective he : p = q.val).symm ▸ q.property)),
        DigitMasks.localIdele_exterior R x p hp, DigitMasks.localIdele_exterior R y p hp]
      have he := (KPHilbert.B6_laws F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)).2.2.2.2.1 (1 : (p.adicCompletion F)ˣ) 1
      simp only [one_pow] at he
      simp only [KPHilbert.B3, he.1, map_one, one_pow]

theorem sDiagonalDefect_scalar {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N) (x y : R.A.G) :
    (KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.centralProduct F (sDiagonalDefect R x y)) : ℂ) =
      (R.σ ((R.A.H_S x y : Fˣ) : F) ^ 2)⁻¹ := by
  have hp : KPAdelicCoverRestrictedProduct.centralProduct F (sDiagonalDefect R x y) =
      ∏ p : R.A.Sf, KPHilbert.B3 F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (x.2 p) (y.2 p) ^ 2 := by
    unfold sDiagonalDefect
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro p _
    change KPAdelicCoverCertificatesRaw.centralProduct F (centralSingle F _ _) = _
    exact centralProduct_single F _ _
  rw [hp, map_prod, Units.coe_prod]
  change (∏ p : R.A.Sf, KPSourceConvention.sourceC F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (x.2 p) (y.2 p)) = _
  rw [KPSourceConvention.prod_sourceC_arithmetic]
  have heq_aux : ∀ (a s : F) (ha : IsPrimitiveRoot a 12) (hs : IsPrimitiveRoot s 12),
      a = s → KPLocalCover.coefficientEmbedding F a ha = KPLocalCover.coefficientEmbedding F s hs := by
    intro a s ha hs h
    subst a
    rfl
  rw [heq_aux R.A.zeta12 S.zeta12 R.A.primitive_zeta12 S.primitive_zeta12 R.sameRoot,
    ← C.aligned (R.A.H_S x y)]
  simp [zpow_neg, zpow_ofNat]

theorem fourier_left_central {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (e : rootsOfUnity 3 F) (g : Group R) :
    fourier R Q.dq (T.theta v)
      (KPAdelicCoverRestrictedProduct.pglCentralInjection F R.A.zeta12 R.A.primitive_zeta12 e * g) =
      (KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12 e : ℂ) * fourier R Q.dq (T.theta v) g := by
  have hc (a : Group R) : Commute a
      (KPAdelicCoverRestrictedProduct.pglCentralInjection F R.A.zeta12 R.A.primitive_zeta12 e) := by
    exact ((Subgroup.mem_center_iff.mp (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F R.A.zeta12 R.A.primitive_zeta12 ⟨e,rfl⟩)) a)
  unfold MomentSources.fourier
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [← mul_assoc, (hc _).eq, mul_assoc]
  have h := (T.automorphic v).2.2 e
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)
  change T.theta v (_ * _) = _ at h
  rw [h, mul_assoc]
  rfl

theorem fourier_diagonal_mul {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (x y : R.A.G) (g : Group R) :
    fourier R C.sources.dq (C.realization.theta v) (diagonal R x * diagonal R y * g) =
      (R.σ ((R.A.H_S x y : Fˣ) : F) ^ 2)⁻¹ *
        fourier R C.sources.dq (C.realization.theta v) (diagonal R (x * y) * g) := by
  have he := congrArg (restrictedLift R) (sDiagonalTuple_mul R x y)
  simp only [map_mul, restrictedLift_centralTuple] at he
  change diagonal R x * diagonal R y =
    KPAdelicCoverRestrictedProduct.pglCentralInjection F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.centralProduct F (sDiagonalDefect R x y)) * diagonal R (x * y) at he
  rw [he, mul_assoc, fourier_left_central, sDiagonalDefect_scalar R C]

end DedekindZetaZeroFree.OrbitExpansion

end
