module

public import DedekindZetaZeroFree.Eisenstein.Induction.CompactOpenLevels
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.CentralDescent

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField IsDedekindDomain KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
attribute [local instance] KPAdelicCoverRestrictedProduct.pglLocalTopology
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology

private theorem local_compact_level (q : KPFinitePlace F) (f : Plus A P C (Sum.inr q)) :
    ∃ L : CompactOpenLevel (KPLocalExceptionalConstruction.ActualCover F A.zeta12 A.primitive_zeta12 q),
      ∀ (k : L.toOpenSubgroup) g, f.val (g * k.val) = f.val g := by
  obtain ⟨U, hU⟩ := f.property.2
  obtain ⟨L, hL⟩ := KPLocalPrincipalSeriesCuspidalExclusion.actual_cover_compact_open_basis
    F A.zeta12 A.primitive_zeta12 q (depth F A.zeta12 A.primitive_zeta12 q)
    (depth_admissible F A.zeta12 A.primitive_zeta12 q) (U : Set _) U.mem_nhds_one
  exact ⟨L, fun k g => congrFun (hU k.val (hL k.property)) g⟩

 def pureComponent (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (v : KPHilbert.Place F) : Plus A P C v :=
  if h : v ∈ s.val then x ⟨v, h⟩ else plusReference A P C v

 theorem exists_pure_product_level (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) :
    ∃ D : ActualFiniteFactor.ProductLevelData F A.zeta12 A.primitive_zeta12,
      ∀ q (k : (D.localLevel q).toOpenSubgroup) g,
        (pureComponent A P C s x (Sum.inr q)).val (g * k.val) =
          (pureComponent A P C s x (Sum.inr q)).val g := by
  choose L hL using fun q => local_compact_level A P C q (pureComponent A P C s x (Sum.inr q))
  have hfin : ∀ᶠ q in Filter.cofinite, Sum.inr q ∉ s.val := by
    apply Filter.eventually_cofinite.mpr
    convert s.val.finite_toSet.preimage Sum.inr_injective.injOn using 1
    ext q
    simp
  let D : ActualFiniteFactor.ProductLevelData F A.zeta12 A.primitive_zeta12 :=
    ⟨fun q => if h : Sum.inr q ∈ s.val then L q else (C.canonical q).iwasawa.compact, by
      filter_upwards [hfin, (bad_finite F).eventually_cofinite_notMem] with q hq hb
      simp only [dif_neg hq]
      have hnot : q ∉ C.exceptional := by
        intro h
        apply hq
        apply s.property
        simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad, h]
      obtain ⟨ht, hc⟩ := C.actual_compact q hnot
      rw [hc]
      change (KPLocalExceptionalConstruction.actualGoodCompactSplit F A.zeta12 A.primitive_zeta12 q ht).range =
        (finiteCompact F A.zeta12 A.primitive_zeta12 q).map
          (KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q))
      simp only [finiteCompact, dif_neg hb]
      rw [KPLocalExceptionalConstruction.actualGoodCompactSplit, MonoidHom.range_comp]⟩
  refine ⟨D, ?_⟩
  intro q k g
  by_cases hq : Sum.inr q ∈ s.val
  · have hk : k.val ∈ (L q).toOpenSubgroup := by simpa only [D, dif_pos hq] using k.property
    exact hL q ⟨k.val, hk⟩ g
  · have hk : k.val ∈ (C.canonical q).iwasawa.compact.toOpenSubgroup := by
      simpa only [D, dif_neg hq] using k.property
    have hnot : q ∉ C.exceptional := by
      intro h
      apply hq
      apply s.property
      simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad, h]
    have hf := congrArg (fun f : Plus A P C (Sum.inr q) => f.val g)
      (plusReference_fixed A P C q hnot ⟨k.val, hk⟩)
    change (plusReference A P C (Sum.inr q)).val (g * k.val) =
      (plusReference A P C (Sum.inr q)).val g at hf
    simpa only [pureComponent, dite_eq_right hq] using hf

 theorem pure_raw_fixed (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (g u : Raw A)
    (harch : ∀ w, u (Sum.inl w) = 1)
    (hfinite : ∀ q, (pureComponent A P C s x (Sum.inr q)).val
      (KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) (g (Sum.inr q) * u (Sum.inr q))) =
      (pureComponent A P C s x (Sum.inr q)).val
        (KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) (g (Sum.inr q)))) :
    rawCoreInsertion A P C (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ x)) (g * u) =
      rawCoreInsertion A P C (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ x)) g := by
  obtain ⟨v, hv⟩ := exists_reference_stage A P C g
  let t : RestrictedTensorSimple.Level (bad A P C) := ⟨s.val ∪ v.val, s.property.trans Finset.subset_union_left⟩
  have hst : s ≤ t := Finset.subset_union_left
  let y : ∀ j : t.val, Plus A P C j.val := fun j => pureComponent A P C s x j.val
  have he : RestrictedTensorSimple.stageInclusion (Plus A P C) (plusReference A P C) (bad A P C) t
      (PiTensorProduct.tprod ℂ y) =
      RestrictedTensorSimple.stageInclusion (Plus A P C) (plusReference A P C) (bad A P C) s
        (PiTensorProduct.tprod ℂ x) := by
    change RestrictedTensorSimple.stageInclusion (Plus A P C) (plusReference A P C) (bad A P C) t
      (PiTensorProduct.tprod ℂ (fun j : t.val => if h : j.val ∈ s.val then x ⟨j.val, h⟩
        else plusReference A P C j.val)) = _
    have hi := RestrictedTensorSimple.insert_pure (Plus A P C) (plusReference A P C) s.val t.val hst x
    have hi' := congrArg (RestrictedTensorSimple.stageInclusion (Plus A P C)
      (plusReference A P C) (bad A P C) t) hi
    convert hi'.symm.trans Module.DirectLimit.of_f using 1
    · congr 2
      funext j
      split_ifs <;> rfl
    · rfl
  have hloc (j : KPHilbert.Place F) :
      localValue A P C j ((g * u) j) (pureComponent A P C s x j) =
      localValue A P C j (g j) (pureComponent A P C s x j) := by
    cases j with
    | inl w => change localValue A P C _ (g _ * u _) _ = _; rw [harch, mul_one]
    | inr q => exact hfinite q
  have ht : ∀ j, j ∉ t.val → localValue A P C j (g j) (plusReference A P C j) = reference A P C j :=
    fun j hj => hv j (fun h => hj (Finset.mem_union_right _ h))
  have ht' : ∀ j, j ∉ t.val → localValue A P C j ((g * u) j) (plusReference A P C j) = reference A P C j := by
    intro j hj
    have hjs : j ∉ s.val := fun h => hj (Finset.mem_union_left _ h)
    simpa only [pureComponent, dif_neg hjs] using (hloc j).trans (by
      simpa only [pureComponent, dif_neg hjs] using ht j hj)
  rw [← he, rawCoreInsertion_stage A P C t _ (g * u) ht', rawCoreInsertion_stage A P C t _ g ht]
  have hm : (fun j : t.val => localValueMap A P C j.val ((g * u) j.val) (y j)) =
      (fun j : t.val => localValueMap A P C j.val (g j.val) (y j)) := by
    funext j
    exact hloc j.val
  simp only [rawStageValue, LinearMap.comp_apply, PiTensorProduct.map_tprod, hm]

 theorem pure_quotientCoreValue_uniform_level (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F A.zeta12 A.primitive_zeta12,
      ∀ g (j : KPGlobalTorusFunctionData.globalLevel F A.zeta12 A.primitive_zeta12 J),
        quotientCoreValue A P C (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ x))
          (g * j.val) =
        quotientCoreValue A P C (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ x)) g := by
  obtain ⟨D, hD⟩ := exists_pure_product_level A P C s x
  have hc := ActualFiniteFactor.productSubgroup_compact_open F A.zeta12 A.primitive_zeta12 D
  rw [EisensteinReferenceSections.SourceLevels.finite_eq F A.zeta12 A.primitive_zeta12] at hc
  let J : KPGlobalTorusFunctionData.FiniteLevel F A.zeta12 A.primitive_zeta12 :=
    ⟨⟨(ActualFiniteFactor.productSubgroup F A.zeta12 A.primitive_zeta12 D).comap
      (KPGlobalTorusFunctionData.finitePart F A.zeta12 A.primitive_zeta12).subtype, hc.2⟩, hc.1⟩
  refine ⟨J, ?_⟩
  intro g j
  obtain ⟨u, hu, heu⟩ := j.property
  obtain ⟨raw, hr, he⟩ := hu
  have hj : scalarQuotient F A.zeta12 A.primitive_zeta12
      (amalgamation F A.zeta12 A.primitive_zeta12 raw) = j.val := he.trans heu
  rw [← hj]
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H g =>
      change quotientCoreValue A P C _
        (scalarQuotient F A.zeta12 A.primitive_zeta12 (amalgamation F A.zeta12 A.primitive_zeta12 g) *
        scalarQuotient F A.zeta12 A.primitive_zeta12 (amalgamation F A.zeta12 A.primitive_zeta12 raw)) = _
      rw [← map_mul, ← map_mul, quotientCoreValue_raw]
      apply pure_raw_fixed A P C s x g raw hr.1
      intro q
      rw [map_mul]
      exact hD q ⟨_, Subgroup.mem_iInf.mp hr.2 q⟩ _

 def commonLevel (J L : KPGlobalTorusFunctionData.FiniteLevel F A.zeta12 A.primitive_zeta12) :
    KPGlobalTorusFunctionData.FiniteLevel F A.zeta12 A.primitive_zeta12 :=
  ⟨J.toOpenSubgroup ⊓ L.toOpenSubgroup, J.isCompact.inter_right L.toOpenSubgroup.isClosed⟩

 theorem stage_quotientCoreValue_uniform_level (s : RestrictedTensorSimple.Level (bad A P C))
    (x : RestrictedTensorSimple.Stage (Plus A P C) s.val) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F A.zeta12 A.primitive_zeta12,
      ∀ g (j : KPGlobalTorusFunctionData.globalLevel F A.zeta12 A.primitive_zeta12 J),
        quotientCoreValue A P C (RestrictedTensorSimple.stageInclusion _ _ _ s x) (g * j.val) =
          quotientCoreValue A P C (RestrictedTensorSimple.stageInclusion _ _ _ s x) g := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    obtain ⟨J, hJ⟩ := pure_quotientCoreValue_uniform_level A P C s x
    refine ⟨J, ?_⟩
    intro g j
    change (quotientCoreEvaluator A P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (c • PiTensorProduct.tprod ℂ x))) _ = (quotientCoreEvaluator A P C
        (RestrictedTensorSimple.stageInclusion _ _ _ s (c • PiTensorProduct.tprod ℂ x))) g
    simp only [map_smul, Pi.smul_apply]
    exact congrArg (fun a : ℂ => c • a) (hJ g j)
  | add x y hx hy =>
    obtain ⟨J, hJ⟩ := hx
    obtain ⟨L, hL⟩ := hy
    refine ⟨commonLevel A J L, ?_⟩
    intro g j
    change (quotientCoreEvaluator A P C (RestrictedTensorSimple.stageInclusion _ _ _ s (x + y))) _ =
      (quotientCoreEvaluator A P C (RestrictedTensorSimple.stageInclusion _ _ _ s (x + y))) g
    simp only [map_add, Pi.add_apply]
    exact congrArg₂ (fun a b : ℂ => a + b)
      (hJ g ⟨j.val, Subgroup.map_mono inf_le_left j.property⟩)
      (hL g ⟨j.val, Subgroup.map_mono inf_le_right j.property⟩)

theorem quotientCoreValue_uniform_level
    (x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C)) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F A.zeta12 A.primitive_zeta12,
      ∀ g u, u ∈ KPGlobalTorusFunctionData.globalLevel F A.zeta12 A.primitive_zeta12 J →
        quotientCoreEvaluator A P C x (g * u) = quotientCoreEvaluator A P C x g := by
  letI : Nonempty (RestrictedTensorSimple.Level (bad A P C)) := ⟨⟨bad A P C, le_rfl⟩⟩
  induction x using Module.DirectLimit.induction_on with
  | ih s x =>
    obtain ⟨J, hJ⟩ := stage_quotientCoreValue_uniform_level A P C s x
    exact ⟨J, fun g u hu => hJ g ⟨u, hu⟩⟩
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
