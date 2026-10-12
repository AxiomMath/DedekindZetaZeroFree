module

public import DedekindZetaZeroFree.Theta.Whittaker.DisjointPlaceWeylCommutation

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical NumberField
open _root_.DedekindZetaZeroFree.RestrictedTensorSimple renaming inclusion_insert → inclusion_insert
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)
local notation "V" => actualLocal R D.finiteData

theorem exterior_three_unit (p : KPFinitePlace F) (hp : p ∉ R.A.Sf) :
    (3 : (ValuativeRel.valuation (p.adicCompletion F)).integer) ∉
      IsLocalRing.maximalIdeal (ValuativeRel.valuation (p.adicCompletion F)).integer := by
  have h6 : IsUnit (6 : KPTameCompact.O F p) :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (ValuativeRel.valuation (p.adicCompletion F)))).mpr
        (by rw [map_ofNat]; exact ExteriorWhittakerValues.exterior_good_six (R := R) ⟨p, hp⟩)
  have h3 : IsUnit (3 : KPTameCompact.O F p) := by
    apply isUnit_of_mul_isUnit_right (x := (2 : KPTameCompact.O F p))
    convert h6 using 1 <;> norm_num
  exact fun h => (IsLocalRing.mem_maximalIdeal _).mp h h3

theorem selected_stage_with_exterior (v : R.A.UnitQuotient)
    (p : KPFinitePlace F) (hp : p ∉ R.A.Sf) :
    ∃ (s : RestrictedTensorSimple.Level D.bad) (hq : Sum.inr p ∈ s.val)
      (x : ∀ w : s.val, V w),
      D.coreMap (RestrictedTensorSimple.stageInclusion V D.references D.bad s
        (PiTensorProduct.tprod ℂ x)) = T.theta v ∧
      x ⟨Sum.inr p, hq⟩ = D.references (Sum.inr p) := by
  obtain ⟨s, x, hs, hx⟩ := D.selected_frozen_stage v
  have hn : Sum.inr p ∉ s.val := by
    rw [hs, D.bad_exact]
    simp only [Sum.inr_ne_inl, false_and, exists_false, Sum.inr.injEq, false_or]
    rintro ⟨q, hq, hmem⟩
    subst q
    exact hp hmem
  let t : RestrictedTensorSimple.Level D.bad :=
    ⟨insert (Sum.inr p) s.val, s.property.trans (Finset.subset_insert _ _)⟩
  let y : ∀ w : t.val, V w := fun w =>
    if h : w.val ∈ s.val then x ⟨w.val, h⟩ else D.references w
  have he : RestrictedTensorSimple.stageInclusion V D.references D.bad t (PiTensorProduct.tprod ℂ y) =
      RestrictedTensorSimple.stageInclusion V D.references D.bad s (PiTensorProduct.tprod ℂ x) := by
    have h := LinearMap.congr_fun (inclusion_insert V D.references D.bad s t (Finset.subset_insert _ _))
      (PiTensorProduct.tprod ℂ x)
    simp only [LinearMap.comp_apply, RestrictedTensorSimple.insert_pure] at h
    refine Eq.trans ?_ h
    congr 2
    funext w
    dsimp only [y]
    split_ifs <;> rfl
  refine ⟨t, Finset.mem_insert_self _ _, y, ?_, ?_⟩
  · rw [he, ← hx, D.selected_eq]
  · simp [y, hn]

theorem fourier_exterior_single (v : R.A.UnitQuotient) (p : KPFinitePlace F)
    (hp : p ∉ R.A.Sf)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (g : Group R)
    (hg : ∀ t : p.adicCompletion F, Commute g (finitePeriodLift R p
      (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) t))) :
    fourier R Q.dq (T.theta v) (g * finitePeriodLift R p a) =
      D.ell (Sum.inr p)
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
          p (D.finiteData p).inducing (D.finiteData p).inducing.polarization
          (D.finiteData p).haar (D.finiteData p).haar_integer
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) a)
          (D.references (Sum.inr p))) * fourier R Q.dq (T.theta v) g := by
  obtain ⟨s, hq, x, hx, href⟩ := selected_stage_with_exterior R D v p hp
  have hn : Sum.inr p ∉ D.bad := by
    rw [D.bad_exact]
    simp only [Sum.inr_ne_inl, false_and, exists_false, Sum.inr.injEq, false_or]
    rintro ⟨q, hq, hmem⟩
    subst q
    exact hp hmem
  let b := KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
    p (D.finiteData p).inducing (D.finiteData p).inducing.polarization
    (D.finiteData p).haar (D.finiteData p).haar_integer
    (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) a)
    (D.references (Sum.inr p))
  have he := finiteSlotPeriod_exterior R D s x p hq (exterior_three_unit R p hp)
    (D.reference_value _ hn) g hg b
  have hu : Function.update x ⟨Sum.inr p, hq⟩ (D.references (Sum.inr p)) = x := by
    rw [← href, Function.update_eq_self]
  have ht := tensor_finite_translate R D s x p hq a g
  rw [href, hx] at ht
  rw [← ht]
  change finiteSlotPeriod R D s x p hq g b = _
  rw [he]
  simp only [finiteSlotPeriod, LinearMap.comp_apply, tensorPeriod, LinearMap.coe_mk,
    AddHom.coe_mk, MultilinearMap.toLinearMap_apply, hu, hx]
  rfl

end DedekindZetaZeroFree.OrbitExpansion

end
