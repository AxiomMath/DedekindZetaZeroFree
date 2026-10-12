module

public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarSections.FlatInsertion
public import DedekindZetaZeroFree.Eisenstein.Residues.TensorProducts.ResidueFamiliesAndPeriods

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct
open TensorActionSource ThetaExpansion
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def localFiniteAction (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :
    Plus R.A P C (Sum.inr q) →ₗ[ℂ] Plus R.A P C (Sum.inr q) :=
  KPLocalPrincipalSeries.IPlus (C.canonical q).borel (C.polarization q)
    (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) a)

 theorem localFiniteAction_value (q : KPFinitePlace F)
    (a g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (f : Plus R.A P C (Sum.inr q)) :
    localValue R.A P C (Sum.inr q) g (localFiniteAction R P C q a f) =
      localValue R.A P C (Sum.inr q) (g * a) f := by
  change f.val (_ * _) = f.val (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (g*a))
  rw [map_mul]

 theorem transition_update_finite (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (s t : RestrictedTensorSimple.Level (bad R.A P C)) (hst : s ≤ t)
    (hq : Sum.inr q ∈ s.val) (x : ∀ j : s.val, Plus R.A P C j.val) :
    RestrictedTensorSimple.transition (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) s t hst
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q, hq⟩
        (localFiniteAction R P C q a (x ⟨Sum.inr q, hq⟩)))) =
    PiTensorProduct.tprod ℂ (Function.update
      (fun j : t.val => if h : j.val ∈ s.val then x ⟨j.val, h⟩ else plusReference R.A P C j.val)
      ⟨Sum.inr q, hst hq⟩ (localFiniteAction R P C q a (x ⟨Sum.inr q, hq⟩))) := by
  rw [RestrictedTensorSimple.transition, RestrictedTensorSimple.insert_pure]
  congr 1
  funext j
  by_cases hj : j.val = Sum.inr q
  · have hjs : j.val ∈ s.val := hj ▸ hq
    have hji : j = ⟨Sum.inr q, hst hq⟩ := Subtype.ext hj
    subst j
    simp [hq]
  · have hji : j ≠ ⟨Sum.inr q, hst hq⟩ := fun h => hj (congrArg Subtype.val h)
    rw [Function.update_of_ne hji]
    split_ifs with hjs
    · rw [Function.update_of_ne (show (⟨j.val, hjs⟩ : s.val) ≠ ⟨Sum.inr q, hq⟩ from
        fun h => hj (congrArg Subtype.val h))]
    · rfl

 theorem rawStageValue_update_finite (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (s : RestrictedTensorSimple.Level (bad R.A P C)) (hq : Sum.inr q ∈ s.val)
    (x : ∀ j : s.val, Plus R.A P C j.val) (g : Raw R.A) :
    rawStageValue R.A P C s g (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q, hq⟩
      (localFiniteAction R P C q a (x ⟨Sum.inr q, hq⟩)))) =
    rawStageValue R.A P C s (g * localToRestricted F ζ hζ (Sum.inr q) a)
      (PiTensorProduct.tprod ℂ x) := by
  have he : (fun j : s.val => localValue R.A P C j.val (g j.val)
      ((Function.update x ⟨Sum.inr q, hq⟩
        (localFiniteAction R P C q a (x ⟨Sum.inr q, hq⟩))) j)) =
      (fun j : s.val => localValue R.A P C j.val
        ((g * localToRestricted F ζ hζ (Sum.inr q) a) j.val) (x j)) := by
    funext j
    by_cases hj : j.val = Sum.inr q
    · have hji : j = ⟨Sum.inr q, hq⟩ := Subtype.ext hj
      subst j
      rw [Function.update_self]
      simpa only [RestrictedProduct.mul_apply, localToRestricted,
        RestrictedProduct.mulSingleMonoidHom_apply, RestrictedProduct.coe_mulSingle_apply,
        Pi.mulSingle_eq_same] using localFiniteAction_value R P C q a (g (Sum.inr q)) (x ⟨Sum.inr q,hq⟩)
    · rw [Function.update_of_ne (fun h => hj (congrArg Subtype.val h))]
      simp only [RestrictedProduct.mul_apply, localToRestricted,
        RestrictedProduct.mulSingleMonoidHom_apply, RestrictedProduct.coe_mulSingle_apply,
        Pi.mulSingle_eq_of_ne hj, mul_one]
  simp only [rawStageValue, LinearMap.comp_apply, PiTensorProduct.map_tprod]
  exact congrArg (fun z => rationalEvaluation R.A (comparison R.A P C
    (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ z)))) he

set_option maxHeartbeats 8000000 in
 theorem rawCoreInsertion_update_finite (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (s : RestrictedTensorSimple.Level (bad R.A P C)) (hq : Sum.inr q ∈ s.val)
    (x : ∀ j : s.val, Plus R.A P C j.val) (g : Raw R.A) :
    rawCoreInsertion R.A P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q, hq⟩
        (localFiniteAction R P C q a (x ⟨Sum.inr q, hq⟩))))) g =
    rawCoreInsertion R.A P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (PiTensorProduct.tprod ℂ x)) (g * localToRestricted F ζ hζ (Sum.inr q) a) := by
  obtain ⟨u, hu⟩ := exists_reference_stage R.A P C g
  obtain ⟨v, hv⟩ := exists_reference_stage R.A P C (g * localToRestricted F ζ hζ (Sum.inr q) a)
  let t : RestrictedTensorSimple.Level (bad R.A P C) := ⟨s.val ∪ u.val ∪ v.val,
    (s.property.trans Finset.subset_union_left).trans Finset.subset_union_left⟩
  have hst : s ≤ t := Finset.subset_union_left.trans Finset.subset_union_left
  have ht : ∀ j, j ∉ t.val → localValue R.A P C j (g j) (plusReference R.A P C j) = reference R.A P C j :=
    fun j hj => hu j (fun h => hj (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
  have ht' : ∀ j, j ∉ t.val → localValue R.A P C j
      ((g * localToRestricted F ζ hζ (Sum.inr q) a) j)
      (plusReference R.A P C j) = reference R.A P C j :=
    fun j hj => hv j (fun h => hj (Finset.mem_union_right _ h))
  have hstep (y : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
      RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) s y =
      RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) t
        (RestrictedTensorSimple.transition (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) s t hst y) :=
    Module.DirectLimit.of_f.symm
  let xp := PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q,hq⟩
    (localFiniteAction R P C q a (x ⟨Sum.inr q,hq⟩)))
  let x0 := PiTensorProduct.tprod ℂ x
  let trans := RestrictedTensorSimple.transition (Plus R.A P C) (plusReference R.A P C)
    (bad R.A P C) s t hst
  have hleft := congrArg (fun z => rawCoreInsertion R.A P C z g) (hstep xp)
  have hright := congrArg (fun z => rawCoreInsertion R.A P C z
    (g * localToRestricted F ζ hζ (Sum.inr q) a)) (hstep x0)
  have hl := rawCoreInsertion_stage R.A P C t (trans xp) g ht
  have hr := rawCoreInsertion_stage R.A P C t (trans x0)
    (g * localToRestricted F ζ hζ (Sum.inr q) a) ht'
  apply hleft.trans
  apply hl.trans
  apply Eq.trans (b := rawStageValue R.A P C t
    (g * localToRestricted F ζ hζ (Sum.inr q) a) (trans x0))
  · let y : ∀ j : t.val, Plus R.A P C j.val :=
      fun j => if h : j.val ∈ s.val then x ⟨j.val,h⟩ else plusReference R.A P C j.val
    have hy : y ⟨Sum.inr q,hst hq⟩ = x ⟨Sum.inr q,hq⟩ := dif_pos hq
    have hp : trans xp = PiTensorProduct.tprod ℂ (Function.update y ⟨Sum.inr q,hst hq⟩
      (localFiniteAction R P C q a (y ⟨Sum.inr q,hst hq⟩))) := by
      rw [hy]
      exact transition_update_finite R P C q a s t hst hq x
    have h0 : trans x0 = PiTensorProduct.tprod ℂ y := by
      change (RestrictedTensorSimple.transition (Plus R.A P C) (plusReference R.A P C)
        (bad R.A P C) s t hst) (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ y
      rw [RestrictedTensorSimple.transition, RestrictedTensorSimple.insert_pure]
      congr 1
      funext j
      dsimp only [y]
      split_ifs <;> rfl
    rw [hp, h0]
    exact rawStageValue_update_finite R P C q a t (hst hq) y g
  · exact hr.symm.trans hright.symm

 theorem quotientCoreEvaluator_update_finite (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (s : RestrictedTensorSimple.Level (bad R.A P C)) (hq : Sum.inr q ∈ s.val)
    (x : ∀ j : s.val, Plus R.A P C j.val) (g : KPLiteralRaw.G F ζ hζ) :
    quotientCoreEvaluator R.A P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q, hq⟩
        (localFiniteAction R P C q a (x ⟨Sum.inr q, hq⟩))))) g =
    quotientCoreEvaluator R.A P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (PiTensorProduct.tprod ℂ x))
      (g * scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inr q) a)) := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H g =>
      change quotientCoreValue R.A P C
        (RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) s
          (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q, hq⟩
            (localFiniteAction R P C q a (x ⟨Sum.inr q, hq⟩)))))
        (scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) =
        quotientCoreValue R.A P C
          (RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) s
            (PiTensorProduct.tprod ℂ x))
          (scalarQuotient F ζ hζ (amalgamation F ζ hζ g) *
            scalarQuotient F ζ hζ (amalgamation F ζ hζ (localToRestricted F ζ hζ (Sum.inr q) a)))
      rw [← map_mul, ← map_mul, quotientCoreValue_raw, quotientCoreValue_raw]
      exact rawCoreInsertion_update_finite R P C q a s hq x g

def coreZeroProfile :
    RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) →ₗ[ℂ]
      literalZeroProfiles (fullProductCompact R) :=
  (literalZeroProfileEquiv (full_product_compact_iwasawa R)).toLinearMap.comp (coreFlatInsertion R P C)

@[simp] theorem coreZeroProfile_val (x) :
    (coreZeroProfile R P C x).val = quotientCoreEvaluator R.A P C x :=
  coreFlatInsertion_zero R P C x

def coreResidue :
    RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) →ₗ[ℂ]
      KPLiteralRaw.Functions F ζ hζ :=
  (ownedLiteralResidueFamily (full_product_compact_iwasawa R)).residue.comp (coreZeroProfile R P C)

 theorem coreZeroProfile_update_finite (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (s : RestrictedTensorSimple.Level (bad R.A P C)) (hq : Sum.inr q ∈ s.val)
    (x : ∀ j : s.val, Plus R.A P C j.val) :
    coreZeroProfile R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q, hq⟩
        (localFiniteAction R P C q a (x ⟨Sum.inr q, hq⟩))))) =
    literalZeroProfileFinite (full_product_compact_iwasawa R) q a
      (coreZeroProfile R P C (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ x))) := by
  apply Subtype.ext
  funext g
  change (coreZeroProfile R P C _).val g =
    (coreZeroProfile R P C _).val (g * scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inr q) a))
  simp only [coreZeroProfile_val]
  exact quotientCoreEvaluator_update_finite R P C q a s hq x g

 theorem coreResidue_update_finite (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (s : RestrictedTensorSimple.Level (bad R.A P C)) (hq : Sum.inr q ∈ s.val)
    (x : ∀ j : s.val, Plus R.A P C j.val) (g : KPLiteralRaw.G F ζ hζ) :
    coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q, hq⟩
        (localFiniteAction R P C q a (x ⟨Sum.inr q, hq⟩))))) g =
    coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ x))
      (g * scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inr q) a)) := by
  unfold coreResidue
  simp only [LinearMap.comp_apply]
  rw [coreZeroProfile_update_finite]
  exact (ownedLiteralResidueFamily (full_product_compact_iwasawa R)).residue_finite q a _ g

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
