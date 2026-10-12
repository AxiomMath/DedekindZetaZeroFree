module

public import DedekindZetaZeroFree.Eisenstein.Induction.CompactOpenLevels
public import DedekindZetaZeroFree.Eisenstein.Induction.Borel.TorusEvaluationAndFiberRecovery

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

theorem finitePlus_has_level (q : KPFinitePlace F) (f : Plus R N P C (Sum.inr q)) :
    ∃ J : CompactOpenLevel (KPLocalExceptionalConstruction.ActualCover F R.A.zeta12 R.A.primitive_zeta12 q),
      J.toOpenSubgroup.toSubgroup ≤ (C.canonical q).iwasawa.compact.toOpenSubgroup.toSubgroup ∧
      ∀ (k : J.toOpenSubgroup) g, f.val (g * k.val) = f.val g := by
  obtain ⟨U, hU⟩ := f.property.2
  let J : CompactOpenLevel (KPLocalExceptionalConstruction.ActualCover F R.A.zeta12 R.A.primitive_zeta12 q) :=
    ⟨(C.canonical q).iwasawa.compact.toOpenSubgroup ⊓ U,
      (C.canonical q).iwasawa.compact.isCompact.inter_right U.isClosed⟩
  exact ⟨J, inf_le_left, fun k g => congrFun (hU k.val k.property.2) g⟩

def extendedPlus (s : RestrictedTensorSimple.Level (bad R P C))
    (f : ∀ p : s.val, Plus R N P C p) (p : KPHilbert.Place F) : Plus R N P C p :=
  if h : p ∈ s.val then f ⟨p, h⟩ else plusReference R N P C p

def pureProductLevel (s : RestrictedTensorSimple.Level (bad R P C))
    (f : ∀ p : s.val, Plus R N P C p) : ActualFiniteFactor.ProductLevelData F R.A.zeta12 R.A.primitive_zeta12 where
  localLevel q := if h : Sum.inr q ∈ s.val then
    (finitePlus_has_level R N P C q (f ⟨Sum.inr q, h⟩)).choose
    else (C.canonical q).iwasawa.compact
  cofinally_standard := by
    filter_upwards [s.val.toRight.eventually_cofinite_notMem,
      (bad_finite F).eventually_cofinite_notMem] with q hq hb
    have hqs : Sum.inr q ∉ s.val := fun h => hq (Finset.mem_toRight.mpr h)
    have hqc : q ∉ C.exceptional := finite_not_bad R P C q (fun h => hqs (s.property h))
    rw [dif_neg hqs, (C.actual_compact q hqc).choose_spec]
    change (KPLocalExceptionalConstruction.actualGoodCompactSplit F R.A.zeta12 R.A.primitive_zeta12 q _).range = _
    change (KPLocalExceptionalConstruction.actualGoodCompactSplit F R.A.zeta12 R.A.primitive_zeta12 q _).range =
      (finiteCompact F R.A.zeta12 R.A.primitive_zeta12 q).map
        (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    simp only [finiteCompact, dif_neg hb]
    rw [KPLocalExceptionalConstruction.actualGoodCompactSplit, MonoidHom.range_comp]

theorem extendedPlus_right_level (s : RestrictedTensorSimple.Level (bad R P C))
    (f : ∀ p : s.val, Plus R N P C p) (q : KPFinitePlace F)
    (k : (pureProductLevel R N P C s f).localLevel q |>.toOpenSubgroup)
    (g : KPLocalExceptionalConstruction.ActualCover F R.A.zeta12 R.A.primitive_zeta12 q) :
    (extendedPlus R N P C s f (Sum.inr q)).val (g * k.val) =
      (extendedPlus R N P C s f (Sum.inr q)).val g := by
  by_cases h : Sum.inr q ∈ s.val
  · simp only [extendedPlus, dif_pos h]
    exact (finitePlus_has_level R N P C q (f ⟨Sum.inr q, h⟩)).choose_spec.2
      ⟨k.val, by simpa only [pureProductLevel, dif_pos h] using k.property⟩ g
  · have hqc : q ∉ C.exceptional := finite_not_bad R P C q (fun hp => h (s.property hp))
    have hk : k.val ∈ (C.canonical q).iwasawa.compact.toOpenSubgroup := by
      simpa only [pureProductLevel, dif_neg h] using k.property
    simp only [extendedPlus, dif_neg h, plusReference, dif_pos hqc]
    exact congrArg (fun u : Plus R N P C (Sum.inr q) => u.val g)
      ((normalized_section R N P C q hqc).choose_spec.1 ⟨k.val, hk⟩)

theorem rawCoreVector_pure_congr (s : RestrictedTensorSimple.Level (bad R P C))
    (f : ∀ p : s.val, Plus R N P C p) (g h : Raw R)
    (he : ∀ p, localValue R N P C p (g p) (extendedPlus R N P C s f p) =
      localValue R N P C p (h p) (extendedPlus R N P C s f p)) :
    rawCoreVector R N P C g (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ f)) =
      rawCoreVector R N P C h (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ f)) := by
  obtain ⟨G, hG⟩ := exists_reference_stage R N P C g
  obtain ⟨H, hH⟩ := exists_reference_stage R N P C h
  let t : RestrictedTensorSimple.Level (bad R P C) :=
    ⟨s.val ∪ G.val ∪ H.val, s.property.trans (Finset.subset_union_left.trans Finset.subset_union_left)⟩
  have hst : s ≤ t := Finset.subset_union_left.trans Finset.subset_union_left
  have htG : ∀ p, p ∉ t.val → localValue R N P C p (g p) (plusReference R N P C p) = reference R P C p :=
    fun p hp => hG p (fun h => hp (by simp [t, h]))
  have htH : ∀ p, p ∉ t.val → localValue R N P C p (h p) (plusReference R N P C p) = reference R P C p :=
    fun p hp => hH p (fun h => hp (by simp [t, h]))
  have hins : RestrictedTensorSimple.stageInclusion _ _ _ t
      (RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C) (bad R P C) s t hst
        (PiTensorProduct.tprod ℂ f)) =
      RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ f) := Module.DirectLimit.of_f
  rw [← hins, rawCoreVector_stage R N P C t g htG, rawCoreVector_stage R N P C t h htH]
  rw [RestrictedTensorSimple.transition, RestrictedTensorSimple.insert_pure,
    stageVector_pure, stageVector_pure]
  congr 2
  funext p
  exact he p

theorem rawCoreVector_pure_right_level (s : RestrictedTensorSimple.Level (bad R P C))
    (f : ∀ p : s.val, Plus R N P C p) (g u : Raw R)
    (hu : u ∈ ActualFiniteFactor.productTuples F R.A.zeta12 R.A.primitive_zeta12
      (pureProductLevel R N P C s f)) :
    rawCoreVector R N P C (g * u) (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ f)) =
      rawCoreVector R N P C g (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ f)) := by
  apply rawCoreVector_pure_congr R N P C s f
  intro p
  cases p with
  | inl w =>
    have hgu : (g * u) (Sum.inl w) = g (Sum.inl w) := by
      change g (Sum.inl w) * u (Sum.inl w) = _
      rw [hu.1 w, mul_one]
    rw [hgu]
  | inr q =>
    change (extendedPlus R N P C s f (Sum.inr q)).val
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) ((g * u) (Sum.inr q))) = _
    rw [show (g * u) (Sum.inr q) = g (Sum.inr q) * u (Sum.inr q) from rfl, map_mul]
    exact extendedPlus_right_level R N P C s f q
      ⟨_, Subgroup.mem_iInf.mp hu.2 q⟩ _

theorem quotientCoreVector_pure_right_level (s : RestrictedTensorSimple.Level (bad R P C))
    (f : ∀ p : s.val, Plus R N P C p) (g u : Group R)
    (hu : u ∈ ActualFiniteFactor.productSubgroup F R.A.zeta12 R.A.primitive_zeta12
      (pureProductLevel R N P C s f)) :
    quotientCoreVector R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ f)) (g * u) =
      quotientCoreVector R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ f)) g := by
  obtain ⟨v, hv, rfl⟩ := hu
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H g =>
      change quotientCoreVector R N P C _
        (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12 (amalgamation F R.A.zeta12 R.A.primitive_zeta12 g) *
          scalarQuotient F R.A.zeta12 R.A.primitive_zeta12 (amalgamation F R.A.zeta12 R.A.primitive_zeta12 v)) = _
      rw [← map_mul, ← map_mul, quotientCoreVector_raw]
      change rawCoreVector R N P C (g * v) _ = quotientCoreVector R N P C _
        (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12 (amalgamation F R.A.zeta12 R.A.primitive_zeta12 g))
      rw [quotientCoreVector_raw]
      exact rawCoreVector_pure_right_level R N P C s f g v hv

theorem scalarSource_pure_right_level (s : RestrictedTensorSimple.Level (bad R P C))
    (f : ∀ p : s.val, Plus R N P C p) (g u : Group R)
    (hu : u ∈ ActualFiniteFactor.productSubgroup F R.A.zeta12 R.A.primitive_zeta12
      (pureProductLevel R N P C s f)) :
    scalarSourceEvaluator R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ f)) (g * u) =
      scalarSourceEvaluator R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ f)) g := by
  change (comparisonSmooth R P C (quotientCoreVector R N P C _ (g * u))).val.val 1 = _
  rw [quotientCoreVector_pure_right_level R N P C s f g u hu]
  rfl

def productFiniteLevel (J : ActualFiniteFactor.ProductLevelData F R.A.zeta12 R.A.primitive_zeta12) :
    KPGlobalTorusFunctionData.FiniteLevel F R.A.zeta12 R.A.primitive_zeta12 := by
  have hc := ActualFiniteFactor.productSubgroup_compact_open F R.A.zeta12 R.A.primitive_zeta12 J
  rw [EisensteinReferenceSections.SourceLevels.finite_eq F R.A.zeta12 R.A.primitive_zeta12] at hc
  exact ⟨⟨(ActualFiniteFactor.productSubgroup F R.A.zeta12 R.A.primitive_zeta12 J).comap
    (KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12).subtype, hc.2⟩, hc.1⟩

theorem productFiniteLevel_global (J : ActualFiniteFactor.ProductLevelData F R.A.zeta12 R.A.primitive_zeta12) :
    KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 (productFiniteLevel R J) =
      ActualFiniteFactor.productSubgroup F R.A.zeta12 R.A.primitive_zeta12 J := by
  change ((ActualFiniteFactor.productSubgroup F R.A.zeta12 R.A.primitive_zeta12 J).comap
    (KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12).subtype).map
      (KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12).subtype = _
  rw [Subgroup.map_comap_eq]
  apply inf_eq_right.mpr
  rw [Subgroup.range_subtype, ← EisensteinReferenceSections.SourceLevels.finite_eq F R.A.zeta12 R.A.primitive_zeta12]
  exact ActualFiniteFactor.productSubgroup_le_finite F R.A.zeta12 R.A.primitive_zeta12 J

theorem scalarSource_has_level (x : PlusCore R N P C) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F R.A.zeta12 R.A.primitive_zeta12,
      ∀ g u, u ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 U →
        scalarSourceEvaluator R N P C x (g * u) = scalarSourceEvaluator R N P C x g := by
  letI : Nonempty (RestrictedTensorSimple.Level (bad R P C)) := ⟨⟨bad R P C, le_rfl⟩⟩
  obtain ⟨s, z, rfl⟩ := Module.DirectLimit.exists_of x
  change ∃ U, ∀ g u, u ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 U →
    scalarSourceEvaluator R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s z) (g * u) =
      scalarSourceEvaluator R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s z) g
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    refine ⟨productFiniteLevel R (pureProductLevel R N P C s f), ?_⟩
    intro g u hu
    rw [productFiniteLevel_global] at hu
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    rw [scalarSource_pure_right_level R N P C s f g u hu]
  | add x y hx hy =>
    obtain ⟨U, hU⟩ := hx
    obtain ⟨V, hV⟩ := hy
    let W : KPGlobalTorusFunctionData.FiniteLevel F R.A.zeta12 R.A.primitive_zeta12 :=
      ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup, U.isCompact.inter_right V.toOpenSubgroup.isClosed⟩
    refine ⟨W, ?_⟩
    intro g u hu
    obtain ⟨v, hv, rfl⟩ := hu
    have huU : v.val ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 U :=
      Subgroup.mem_map.mpr ⟨v, hv.1, rfl⟩
    have huV : v.val ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 V :=
      Subgroup.mem_map.mpr ⟨v, hv.2, rfl⟩
    simp only [map_add, Pi.add_apply]
    exact congrArg₂ (· + ·) (hU g v.val huU) (hV g v.val huV)

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
