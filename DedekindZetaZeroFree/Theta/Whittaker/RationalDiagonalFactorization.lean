module

public import DedekindZetaZeroFree.Metaplectic.Torus.DiagonalMultiplicationPeriods

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory KPAdelicCoverRestrictedProduct
open scoped NumberField Classical
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_localIdele → eval_localIdele
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def rationalLocalA (a : Fˣ) (w : KPHilbert.Place F) :=
  KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 w
    (Units.map (algebraMap F (KPHilbert.Completion F w)).toMonoidHom a)

def exteriorAList (a : Fˣ) (L : List (ThetaBranch.ExteriorPrime R.A)) :=
  (L.map (fun p => localToRestricted F R.A.zeta12 R.A.primitive_zeta12
    (.inr p.val) (rationalLocalA R a (.inr p.val)))).prod

lemma list_single_value {I G : Type*} [DecidableEq I] [Group G]
    (L : List I) (hL : L.Nodup) (p : I) (a : G) :
    (L.map (fun q => if q = p then a else 1)).prod = if p ∈ L then a else 1 := by
  induction L with
  | nil => simp
  | cons q L ih =>
    obtain ⟨hq, hn⟩ := List.nodup_cons.mp hL
    rw [List.map_cons, List.prod_cons, ih hn]
    by_cases h : q = p
    · subst q
      simp [hq]
    · simp [h, Ne.symm h]

lemma exteriorAList_eval (a : Fˣ) (L : List (ThetaBranch.ExteriorPrime R.A))
    (hL : L.Nodup) (w : KPHilbert.Place F) :
    exteriorAList R a L w =
      if ∃ p ∈ L, w = Sum.inr p.val then rationalLocalA R a w else 1 := by
  change (RestrictedProduct.evalMonoidHom _ w) _ = _
  rw [exteriorAList, map_list_prod]
  simp only [List.map_map, Function.comp_def, RestrictedProduct.evalMonoidHom_apply]
  by_cases hw : ∃ p ∈ L, w = Sum.inr p.val
  · obtain ⟨p, hp, rfl⟩ := hw
    have he (q : ThetaBranch.ExteriorPrime R.A) :
        localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (.inr q.val)
          (rationalLocalA R a (.inr q.val)) (.inr p.val) =
        if q = p then rationalLocalA R a (.inr p.val) else 1 := by
      by_cases h : q = p
      · subst q; simp [localToRestricted]
      · rw [if_neg h]
        exact RestrictedProduct.mulSingle_eq_of_ne _ _
          (by intro he; exact h (Subtype.ext (Sum.inr.inj he).symm))
    simp_rw [he]
    rw [list_single_value L hL, if_pos hp, if_pos ⟨p, hp, rfl⟩]
  · rw [if_neg hw]
    apply List.prod_eq_one
    intro b hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    exact RestrictedProduct.mulSingle_eq_of_ne _ _ (fun he => hw ⟨p, hp, he⟩)

lemma rationalATuple_eval (a : Fˣ) (w : KPHilbert.Place F) :
    KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a) w = rationalLocalA R a w := by
  change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 w _ = _
  congr 1
  apply Units.ext
  cases w <;> rfl

lemma sATuple_eval (a : Fˣ) (w : KPHilbert.Place F) :
    KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12
      (localIdele R (R.A.diagonal a)) w =
      match w with
      | .inl w => rationalLocalA R a (.inl w)
      | .inr p => if p ∈ R.A.Sf then rationalLocalA R a (.inr p) else 1 := by
  cases w with
  | inl w =>
    change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 _ _ = _
    rw [DigitMasks.localIdele_arch]
    rfl
  | inr p =>
    dsimp only
    by_cases hp : p ∈ R.A.Sf
    · rw [if_pos hp]
      change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 _ _ = _
      rw [DigitMasks.localIdele_finite R _ p hp]
      rfl
    · rw [if_neg hp]
      change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 _
        (Units.map (adeleEval F (.inr p)).toMonoidHom (localIdele R (R.A.diagonal a))) = _
      rw [DigitMasks.localIdele_exterior R _ p hp, KPStandardLocalRootLifts.A_one]

def rationalTail (a : Fˣ) (L : List (ThetaBranch.ExteriorPrime R.A)) :=
  (KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12
      (localIdele R (R.A.diagonal a)) * exteriorAList R a L)⁻¹ *
    KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)

lemma rationalTail_mem (a : Fˣ) (L : List (ThetaBranch.ExteriorPrime R.A))
    (hL : L.Nodup)
    (ha : ∀ p : ThetaBranch.ExteriorPrime R.A, p ∉ L → p.val.valuation F (a : F) = 1) :
    ∀ w, rationalTail R a L w ∈ DigitMasks.exteriorFactor R w := by
  intro w
  simp only [rationalTail, RestrictedProduct.mul_apply, RestrictedProduct.inv_apply,
    rationalATuple_eval, sATuple_eval, exteriorAList_eval R a L hL]
  cases w with
  | inl w =>
    simp [DigitMasks.exteriorFactor, Sum.inl_ne_inr]
  | inr p =>
    dsimp only
    by_cases hp : p ∈ R.A.Sf
    · have hn : ¬ ∃ q ∈ L, (Sum.inr p : KPHilbert.Place F) = Sum.inr q.val := by
        rintro ⟨q, hq, he⟩
        exact q.property (Sum.inr.inj he ▸ hp)
      simp [if_pos hp, if_neg hn, DigitMasks.exteriorFactor, hp]
    · by_cases hl : (⟨p, hp⟩ : ThetaBranch.ExteriorPrime R.A) ∈ L
      · have he : ∃ q ∈ L, (Sum.inr p : KPHilbert.Place F) = Sum.inr q.val := ⟨⟨p, hp⟩, hl, rfl⟩
        rw [if_neg hp, if_pos he]
        simp only [one_mul, inv_mul_cancel]
        exact Subgroup.one_mem _
      · have he : ¬ ∃ q ∈ L, (Sum.inr p : KPHilbert.Place F) = Sum.inr q.val := by
          rintro ⟨q, hq, hq'⟩
          have hqp : q = (⟨p, hp⟩ : ThetaBranch.ExteriorPrime R.A) :=
            Subtype.ext (Sum.inr.inj hq').symm
          exact hl (hqp ▸ hq)
        simp only [if_neg hp, if_neg he, one_mul, inv_one]
        let p' : ThetaBranch.ExteriorPrime R.A := ⟨p, hp⟩
        have hu : ∃ u : KPHilbert.LocalIntegerUnits F p,
            KPHilbert.integerUnitInclusion F p u =
              Units.map (algebraMap F (p.adicCompletion F)).toMonoidHom a := by
          let x := Units.map (algebraMap F (p.adicCompletion F)).toMonoidHom a
          have hv : ValuativeRel.valuation (p.adicCompletion F) (x : p.adicCompletion F) = 1 := by
            letI : (Valued.v : Valuation (p.adicCompletion F)
                (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
            rw [← (ValuativeRel.isEquiv (Valued.v : Valuation (p.adicCompletion F)
              (WithZero (Multiplicative ℤ))) (ValuativeRel.valuation (p.adicCompletion F))).eq_one_iff_eq_one]
            change Valued.v (algebraMap F (p.adicCompletion F) (a : F)) = 1
            exact (p.valuedAdicCompletion_eq_valuation' (K := F) (a : F)).trans (ha p' hl)
          let o : (ValuativeRel.valuation (p.adicCompletion F)).integer := ⟨x, hv.le⟩
          have ho : IsUnit o := (Valuation.integer.integers
            (ValuativeRel.valuation (p.adicCompletion F))).isUnit_iff_valuation_eq_one.mpr hv
          refine ⟨ho.unit, ?_⟩
          apply Units.ext
          exact congrArg Subtype.val ho.unit_spec
        obtain ⟨u, hu⟩ := hu
        rw [rationalLocalA, ← hu]
        rw [DigitMasks.exteriorFactor, dif_pos hp]
        exact ⟨KPStandardLocalRootLifts.integralA F p u,
          (KPStandardLocalRootLifts.A_eq_compact F R.A.zeta12 R.A.primitive_zeta12 p
            (fun h3 => DigitMasks.exterior_not_bad R p hp (Or.inr h3)) u).symm⟩

lemma raw_s_commute (y : R.A.G)
    (e : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (he : ∀ w, e w ∈ DigitMasks.exteriorFactor R w) :
    Commute (KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 (localIdele R y)) e := by
  apply RestrictedProduct.ext
  intro w
  change _ * e w = e w * _
  cases w with
  | inl w =>
    have hh : e (.inl w) = 1 := he (.inl w)
    rw [hh, mul_one, one_mul]
  | inr p =>
    by_cases hp : p ∈ R.A.Sf
    · have hh : e (.inr p) = 1 := by
        simpa only [DigitMasks.exteriorFactor, dif_neg (not_not.mpr hp), Subgroup.mem_bot] using he (.inr p)
      rw [hh, mul_one, one_mul]
    · have hh : KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12
          (localIdele R y) (.inr p) = 1 := by
        change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (.inr p)
          (Units.map (adeleEval F (.inr p)).toMonoidHom (localIdele R y)) = _
        rw [DigitMasks.localIdele_exterior R y p hp, KPStandardLocalRootLifts.A_one]
      rw [hh, mul_one, one_mul]

lemma rationalLift_decomposition (a : Fˣ) (L : List (ThetaBranch.ExteriorPrime R.A)) :
    KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a) =
      diagonal R (R.A.diagonal a) *
        (L.map (fun p => finiteLift R p.val (rationalLocalA R a (.inr p.val)))).prod *
        rawToGroup R (rationalTail R a L) := by
  have ht : KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a) =
      (KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12
        (localIdele R (R.A.diagonal a)) * exteriorAList R a L) * rationalTail R a L := by
    unfold rationalTail
    group
  have h := congrArg (rawToGroup R) ht
  rw [map_mul, map_mul] at h
  have hl : rawToGroup R (exteriorAList R a L) =
      (L.map (fun p => finiteLift R p.val (rationalLocalA R a (.inr p.val)))).prod := by
    rw [exteriorAList, map_list_prod, List.map_map]
    rfl
  rw [hl] at h
  exact h

lemma exteriorLiftValue_rational {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (D : SourceFactorization R Q T) (a : Fˣ) (p : ThetaBranch.ExteriorPrime R.A) :
    exteriorLiftValue R D p (rationalLocalA R a (.inr p.val)) = D.exteriorValue R p a := by
  unfold exteriorLiftValue SourceFactorization.exteriorValue
  congr 4
  change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (.inr p.val) _ = _
  congr 1
  have he := eval_localIdele F (.inr p.val) (.inr p.val)
    (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom a)
  simp only [Pi.mulSingle_eq_same] at he
  refine (show Units.map (algebraMap F (KPHilbert.Completion F (.inr p.val))).toMonoidHom a =
    Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom a from ?_).trans he.symm
  apply Units.ext
  rfl

lemma fourier_rational_diagonal {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (a : Fˣ) (y : R.A.G)
    (L : List (ThetaBranch.ExteriorPrime R.A)) (hL : L.Nodup)
    (ha : ∀ p : ThetaBranch.ExteriorPrime R.A, p ∉ L → p.val.valuation F (a : F) = 1) :
    fourier R C.sources.dq (C.realization.theta v)
      (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
        (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a) * diagonal R y) =
      (L.map (fun p => C.factorization.exteriorValue R p a)).prod *
        (R.σ ((R.A.H_S (R.A.diagonal a) y : Fˣ) : F) ^ 2)⁻¹ *
        C.packet.forwardProfile v (R.A.diagonal a * y) := by
  have ht := rationalTail_mem R a L hL ha
  have htc := (raw_s_commute R y _ ht).map (rawToGroup R)
  change Commute (diagonal R y) (rawToGroup R (rationalTail R a L)) at htc
  have hlc : Commute (diagonal R y)
      (L.map (fun p => finiteLift R p.val (rationalLocalA R a (.inr p.val)))).prod := by
    apply (commute_list_product _ _ _).symm
    intro b hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    exact (diagonal_commute_exterior R y p _).symm
  rw [rationalLift_decomposition, mul_assoc, ← htc.eq, ← mul_assoc,
    fourier_full_exterior R C.realization v _ ht,
    mul_assoc, ← hlc.eq, ← mul_assoc]
  rw [fourier_exterior_list R C.factorization v L hL _ _]
  · simp_rw [exteriorLiftValue_rational]
    rw [fourier_diagonal_mul_actual]
    exact (mul_assoc _ _ _).symm
  · intro p hp t
    exact (diagonal_commute_exterior_root R _ p t).mul_left
      (diagonal_commute_exterior_root R _ p t)

end DedekindZetaZeroFree.OrbitExpansion

end
