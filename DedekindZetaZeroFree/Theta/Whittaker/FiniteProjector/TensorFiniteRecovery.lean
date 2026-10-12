module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.HCRecovery
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FiniteCyclicity
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FiniteSourceGeometry

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology TensorProduct
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
local notation "ρ" => KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12
local notation "FinG" => KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12

theorem finiteInjection_mem_finitePart (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    finiteInjection R q a ∈ KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12 := by
  refine Subgroup.mem_map.mpr ⟨KPAdelicCoverRestrictedProduct.localToRestricted
    F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a, ?_, rfl⟩
  apply Subgroup.mem_iInf.mpr
  intro w
  change KPAdelicCoverRestrictedProduct.localToRestricted F R.A.zeta12
    R.A.primitive_zeta12 (Sum.inr q) a (Sum.inl w) = 1
  simp [KPAdelicCoverRestrictedProduct.localToRestricted]

theorem finiteTranslateSpan_stable {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (a : FinG) {f : Functions R} (hf : f ∈ finiteTranslateSpan R T) :
    ρ a.val f ∈ finiteTranslateSpan R T := by
  change f ∈ Submodule.span ℂ _ at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v,b,rfl⟩ := hf
    rw [← Module.End.mul_apply, ← map_mul]
    exact Submodule.subset_span ⟨v,a*b,rfl⟩
  | zero => simpa using (Submodule.zero_mem (finiteTranslateSpan R T))
  | add f g hf hg ihf ihg => simpa only [map_add] using Submodule.add_mem _ ihf ihg
  | smul c f hf ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

variable {Q Q' : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T) (T' : Realization R Q')

theorem tensor_slot_recovery (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (hx : x ⟨Sum.inr q,hq⟩ ≠ 0)
    (hm : tensorFunction R D s x ∈ finiteTranslateSpan R T')
    (z : actualLocal R D.finiteData (Sum.inr q)) :
    tensorFunction R D s (Function.update x ⟨Sum.inr q,hq⟩ z) ∈ finiteTranslateSpan R T' := by
  let m := (D.coreMap.comp (RestrictedTensorSimple.stageInclusion _ D.references D.bad s)).compMultilinearMap
    (PiTensorProduct.tprod ℂ)
  let j : s.val := ⟨Sum.inr q,hq⟩
  let L := m.toLinearMap x j
  have hz : z ∈ Submodule.span ℂ (Set.range (fun a => actualFiniteAction R D q a (x j))) := by
    rw [actualFinite_orbit_span R D q (x j) hx]
    trivial
  change L z ∈ finiteTranslateSpan R T'
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a,rfl⟩ := hz
    obtain ⟨b,hb⟩ := QuotientGroup.mk'_surjective
      (KPPGLLocalCover.splitScalarSubgroup F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) a
    change KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) b = a at hb
    rw [← hb]
    change tensorFunction R D s (Function.update x j _) ∈ _
    have hi := fun g => D.finite_intertwining q b s hq x g
    have he : tensorFunction R D s (Function.update x j _) =
        ρ (finiteInjection R q b) (tensorFunction R D s x) := funext hi
    rw [he]
    exact finiteTranslateSpan_stable R T' ⟨_,finiteInjection_mem_finitePart R q b⟩ hm
  | zero => simpa using (Submodule.zero_mem (finiteTranslateSpan R T'))
  | add z w hz hw ihz ihw => simpa only [map_add] using Submodule.add_mem _ ihz ihw
  | smul c z hz ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

theorem tensor_slots_recovery (s : RestrictedTensorSimple.Level D.bad)
    (x y : ∀ p : s.val, actualLocal R D.finiteData p)
    (C : Finset s.val) (hC : ∀ p ∈ C, ∃ q : KPFinitePlace F, p.val = Sum.inr q)
    (hy : ∀ p ∈ C, y p ≠ 0)
    (hm : tensorFunction R D s y ∈ finiteTranslateSpan R T') :
    tensorFunction R D s (fun p => if p ∈ C then x p else y p) ∈ finiteTranslateSpan R T' := by
  induction C using Finset.induction_on with
  | empty => simpa using hm
  | @insert j C hj ih =>
    obtain ⟨q,hq⟩ := hC j (Finset.mem_insert_self _ _)
    have hqmem : Sum.inr q ∈ s.val := hq ▸ j.property
    have hjq : j = ⟨Sum.inr q,hqmem⟩ := Subtype.ext hq
    let u := fun p : s.val => if p ∈ C then x p else y p
    have hu := ih (fun p hp => hC p (Finset.mem_insert_of_mem hp))
      (fun p hp => hy p (Finset.mem_insert_of_mem hp))
    subst j
    have hj0 : u ⟨Sum.inr q,hqmem⟩ ≠ 0 := by
      simpa [u,hj] using hy ⟨Sum.inr q,hqmem⟩ (Finset.mem_insert_self _ _)
    have he : (fun p : s.val => if p ∈ insert ⟨Sum.inr q,hqmem⟩ C then x p else y p) =
        Function.update u ⟨Sum.inr q,hqmem⟩ (x ⟨Sum.inr q,hqmem⟩) := by
      funext p
      by_cases hp : p = ⟨Sum.inr q,hqmem⟩
      · subst p; simp
      · simp [u,hp,Function.update_of_ne hp]
    rw [he]
    exact tensor_slot_recovery R D T' s u q hqmem hj0 hu _
end DedekindZetaZeroFree.FiniteWhittakerProjectors

end
