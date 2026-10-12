module

public import DedekindZetaZeroFree.Theta.Whittaker.ExteriorSlotExtraction

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)

abbrev exteriorSlotValue (p : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)) : ℂ :=
  D.ell (Sum.inr p)
    (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
      p (D.finiteData p).inducing (D.finiteData p).inducing.polarization
      (D.finiteData p).haar (D.finiteData p).haar_integer
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) a)
      (D.references (Sum.inr p)))

def exteriorFiniteTuple (P : Finset (ThetaBranch.ExteriorPrime R.A))
    (a : ∀ p : ThetaBranch.ExteriorPrime R.A,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)) :
    KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 :=
  ⟨fun w => match w with
    | Sum.inl _ => 1
    | Sum.inr p => if hp : p ∉ R.A.Sf then
        if (⟨p, hp⟩ : ThetaBranch.ExteriorPrime R.A) ∈ P then a ⟨p, hp⟩ else 1
      else 1,
    by
      have he : ∀ᶠ w : KPHilbert.Place F in Filter.cofinite,
          w ∉ P.image (fun p => Sum.inr p.val) := (P.image _).finite_toSet.compl_mem_cofinite
      filter_upwards [he] with w hw
      cases w with
      | inl w => exact (KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)).one_mem
      | inr p =>
        dsimp only
        by_cases hp : p ∉ R.A.Sf
        · rw [dif_pos hp, if_neg (fun hm => hw (Finset.mem_image.mpr ⟨⟨p, hp⟩, hm, rfl⟩))]
          exact (KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)).one_mem
        · rw [dif_neg hp]
          exact (KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)).one_mem⟩

theorem exteriorFiniteTuple_off (P : Finset (ThetaBranch.ExteriorPrime R.A))
    (a : ∀ p : ThetaBranch.ExteriorPrime R.A,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
    (w : KPHilbert.Place F) (hw : ∀ p ∈ P, w ≠ Sum.inr p.val) :
    exteriorFiniteTuple R P a w = 1 := by
  cases w with
  | inl w => rfl
  | inr p =>
    change (if hp : p ∉ R.A.Sf then if (⟨p, hp⟩ : ThetaBranch.ExteriorPrime R.A) ∈ P then a ⟨p, hp⟩ else 1 else 1) = (1 : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    by_cases hp : p ∉ R.A.Sf
    · rw [dif_pos hp, if_neg (fun hm => hw ⟨p, hp⟩ hm rfl)]
    · rw [dif_neg hp]

theorem fourier_exterior_finite (v : R.A.UnitQuotient)
    (P : Finset (ThetaBranch.ExteriorPrime R.A))
    (a : ∀ p : ThetaBranch.ExteriorPrime R.A,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
    (g : KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (hg : ∀ p : ThetaBranch.ExteriorPrime R.A, g (Sum.inr p.val) = 1) :
    fourier R Q.dq (T.theta v) (restrictedLift R g * restrictedLift R (exteriorFiniteTuple R P a)) =
      (∏ p ∈ P, exteriorSlotValue R D p.val (a p)) * fourier R Q.dq (T.theta v) (restrictedLift R g) := by
  induction P using Finset.induction_on with
  | empty =>
    have he : exteriorFiniteTuple R ∅ a = 1 := by
      apply RestrictedProduct.ext
      intro w
      cases w <;> simp [exteriorFiniteTuple]
    rw [he, map_one, mul_one, Finset.prod_empty, one_mul]
  | @insert p P hp ih =>
    have hc : Commute (KPAdelicCoverRestrictedProduct.localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (a p))
        (exteriorFiniteTuple R P a) := by
      apply Commute.symm
      change exteriorFiniteTuple R P a * _ = _ * exteriorFiniteTuple R P a
      apply RestrictedProduct.ext
      intro w
      change exteriorFiniteTuple R P a w * Pi.mulSingle (Sum.inr p.val) (a p) w =
        Pi.mulSingle (Sum.inr p.val) (a p) w * exteriorFiniteTuple R P a w
      by_cases hw : w = Sum.inr p.val
      · subst w
        rw [exteriorFiniteTuple_off R P a _ (by
          intro q hq he
          apply hp
          have he' : p = q := Subtype.ext (Sum.inr_injective he)
          exact he' ▸ hq)]
        simp
      · change _ = Pi.mulSingle (Sum.inr p.val) (a p) w * exteriorFiniteTuple R P a w
        simp [Pi.mulSingle_eq_of_ne hw]
    have ho : exteriorFiniteTuple R P a (Sum.inr p.val) = 1 :=
      exteriorFiniteTuple_off R P a _ (by
        intro q hq he
        exact hp ((Subtype.ext (Sum.inr_injective he) : p = q) ▸ hq))
    have hroot (t : p.val.adicCompletion F) : Commute
        (restrictedLift R g * restrictedLift R (exteriorFiniteTuple R P a))
        (finitePeriodLift R p.val (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) t)) := by
      rw [← map_mul]
      apply restrictedLift_commute_single
      rw [RestrictedProduct.mul_apply, hg, ho, one_mul]
    have htuple : exteriorFiniteTuple R (insert p P) a = exteriorFiniteTuple R P a *
        KPAdelicCoverRestrictedProduct.localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (a p) := by
      apply RestrictedProduct.ext
      intro w
      change exteriorFiniteTuple R (insert p P) a w = exteriorFiniteTuple R P a w * Pi.mulSingle (Sum.inr p.val) (a p) w
      cases w with
      | inl w => simp [exteriorFiniteTuple]
      | inr q =>
        by_cases hq : q = p.val
        · subst q
          rw [ho]
          simp only [Pi.mulSingle_eq_same, one_mul]
          change (if h : p.val ∉ R.A.Sf then if (⟨p.val, h⟩ : ThetaBranch.ExteriorPrime R.A) ∈ insert p P then a ⟨p.val, h⟩ else 1 else 1) = a p
          simp [p.property]
        · have hqp : (Sum.inr q : KPHilbert.Place F) ≠ Sum.inr p.val := Sum.inr_injective.ne hq
          rw [Pi.mulSingle_eq_of_ne hqp, mul_one]
          change (if h : q ∉ R.A.Sf then if (⟨q, h⟩ : ThetaBranch.ExteriorPrime R.A) ∈ insert p P then a ⟨q, h⟩ else 1 else 1) =
            ((if h : q ∉ R.A.Sf then if (⟨q, h⟩ : ThetaBranch.ExteriorPrime R.A) ∈ P then a ⟨q, h⟩ else 1 else 1) : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
          by_cases h : q ∉ R.A.Sf
          · rw [dif_pos h, dif_pos h]
            have hn : (⟨q, h⟩ : ThetaBranch.ExteriorPrime R.A) ≠ p := fun he => hq (congrArg Subtype.val he)
            simp only [Finset.mem_insert, hn, false_or]
          · rw [dif_neg h, dif_neg h]
    rw [htuple, map_mul, ← mul_assoc]
    change fourier R Q.dq (T.theta v) ((_ * _) * finitePeriodLift R p.val (a p)) = _
    rw [fourier_exterior_single R D v p.val p.property (a p) _ hroot, ih, Finset.prod_insert hp]
    rw [mul_assoc]

theorem exteriorFiniteTuple_at (P : Finset (ThetaBranch.ExteriorPrime R.A))
    (a : ∀ p : ThetaBranch.ExteriorPrime R.A,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
    (p : ThetaBranch.ExteriorPrime R.A) :
    exteriorFiniteTuple R P a (Sum.inr p.val) = if p ∈ P then a p else 1 := by
  change (if hp : p.val ∉ R.A.Sf then if (⟨p.val, hp⟩ : ThetaBranch.ExteriorPrime R.A) ∈ P then a ⟨p.val, hp⟩ else 1 else 1) = (if p ∈ P then a p else 1)
  rw [dif_pos p.property]

theorem exteriorSlotValue_compact (p : ThetaBranch.ExteriorPrime R.A)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
    (ha : a ∈ DigitMasks.exteriorFactor R (Sum.inr p.val)) :
    exteriorSlotValue R D p.val a = 1 := by
  unfold exteriorSlotValue
  rw [(D.spherical_reference p.val p.property).2 a
    (DigitMasks.exteriorFactor_le_compact R _ ha)]
  apply D.reference_value
  rw [D.bad_exact]
  simp only [Sum.inr_ne_inl, false_and, exists_false, Sum.inr.injEq, false_or]
  rintro ⟨q, hq, hmem⟩
  subst q
  exact p.property hmem

theorem fourier_exterior_tuple (v : R.A.UnitQuotient)
    (a g : KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (hg : ∀ p : ThetaBranch.ExteriorPrime R.A, g (Sum.inr p.val) = 1)
    (ha : ∀ w, (¬ ∃ p : ThetaBranch.ExteriorPrime R.A, w = Sum.inr p.val) → a w = 1)
    (P : Finset (ThetaBranch.ExteriorPrime R.A))
    (hP : ∀ p : ThetaBranch.ExteriorPrime R.A, p ∉ P → a (Sum.inr p.val) ∈ DigitMasks.exteriorFactor R (Sum.inr p.val)) :
    Function.HasFiniteMulSupport (fun p : ThetaBranch.ExteriorPrime R.A => exteriorSlotValue R D p.val (a (Sum.inr p.val))) ∧
    fourier R Q.dq (T.theta v) (restrictedLift R g * restrictedLift R a) =
      (∏ᶠ p : ThetaBranch.ExteriorPrime R.A, exteriorSlotValue R D p.val (a (Sum.inr p.val))) *
        fourier R Q.dq (T.theta v) (restrictedLift R g) := by
  let b := exteriorFiniteTuple R P (fun p => a (Sum.inr p.val))
  let k := b⁻¹ * a
  have hk (w : KPHilbert.Place F) : k w ∈ DigitMasks.exteriorFactor R w := by
    change (b⁻¹ * a) w ∈ _
    rw [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply]
    by_cases hw : ∃ p : ThetaBranch.ExteriorPrime R.A, w = Sum.inr p.val
    · obtain ⟨p, rfl⟩ := hw
      change (exteriorFiniteTuple R P (fun p => a (Sum.inr p.val)) (Sum.inr p.val))⁻¹ * a (Sum.inr p.val) ∈ _
      rw [exteriorFiniteTuple_at]
      by_cases hp : p ∈ P
      · rw [if_pos hp, inv_mul_cancel]
        exact (DigitMasks.exteriorFactor R _).one_mem
      · rw [if_neg hp, inv_one, one_mul]
        exact hP p hp
    · rw [ha w hw]
      have hb : b w = 1 := exteriorFiniteTuple_off R P _ w (fun p _ he => hw ⟨p, he⟩)
      rw [hb, inv_one, one_mul]
      exact (DigitMasks.exteriorFactor R _).one_mem
  have hsupport : Function.mulSupport (fun p : ThetaBranch.ExteriorPrime R.A => exteriorSlotValue R D p.val (a (Sum.inr p.val))) ⊆ P := by
    intro p hp
    by_contra hn
    exact hp (exteriorSlotValue_compact R D p _ (hP p hn))
  have hs : Function.HasFiniteMulSupport (fun p : ThetaBranch.ExteriorPrime R.A => exteriorSlotValue R D p.val (a (Sum.inr p.val))) :=
    P.finite_toSet.subset hsupport
  refine ⟨hs, ?_⟩
  have he : b * k = a := mul_inv_cancel_left b a
  have hi (q : KPAdditiveQuotient F) := DigitMasks.theta_full_exterior R T v k hk
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * (restrictedLift R g * restrictedLift R b))
  have hfourier : fourier R Q.dq (T.theta v) (restrictedLift R g * restrictedLift R a) =
      fourier R Q.dq (T.theta v) (restrictedLift R g * restrictedLift R b) := by
    unfold MomentSources.fourier
    apply integral_congr_ae
    filter_upwards [] with q
    have h := hi q
    change T.theta v ((_ * (restrictedLift R g * restrictedLift R b)) * restrictedLift R k) = _ at h
    rw [mul_assoc, mul_assoc, ← map_mul, he] at h
    rw [h]
  rw [hfourier, fourier_exterior_finite R D v P _ g hg]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupport]

theorem exterior_tuple_finite_exceptional
    (a : KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12) :
    ∃ P : Finset (ThetaBranch.ExteriorPrime R.A), ∀ p ∉ P,
      a (Sum.inr p.val) ∈ DigitMasks.exteriorFactor R (Sum.inr p.val) := by
  have hf : {w : KPHilbert.Place F | a w ∉ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 w}.Finite := by
    have h := a.property
    rw [Filter.eventually_cofinite] at h
    exact h
  have he : Function.Injective (fun p : ThetaBranch.ExteriorPrime R.A => (Sum.inr p.val : KPHilbert.Place F)) := by
    intro p q h
    exact Subtype.ext (Sum.inr_injective h)
  have hp := hf.preimage he.injOn
  refine ⟨hp.toFinset, ?_⟩
  intro p hn
  have hmem : a (Sum.inr p.val) ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq, not_not] using hn
  simpa only [DigitMasks.exteriorFactor, dif_pos p.property,
    KPAdelicCoverRestrictedProduct.compact, KPAdelicCoverRestrictedProduct.finiteCompact,
    dif_neg (DigitMasks.exterior_not_bad R p.val p.property)] using hmem

end DedekindZetaZeroFree.OrbitExpansion

end
