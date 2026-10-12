module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalTensorEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField IsDedekindDomain KPLocalPrincipalSeries KPLocalStoneVonNeumann
open KPLocalGoodSphericalImage KPGlobalTorusFiniteStages
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

 theorem normalized_reference (q : KPFinitePlace F) (hq : q ∉ C.exceptional) :
    ∃ f : Plus A P C (Sum.inr q),
      f ∈ fixedSubmodule (IPlus (C.canonical q).borel (C.polarization q))
        (C.canonical q).iwasawa.compact.toOpenSubgroup ∧
      f.val 1 = localReference F A.zeta12 A.primitive_zeta12 P C q := by
  obtain ⟨f, hf, _⟩ := normalized_plus_spherical_vector (C.canonical q).borel
    (C.polarization q) (C.canonical q).iwasawa (C.unramified q hq)
  refine ⟨f, hf.1, ?_⟩
  apply (referenceGoodSpherical F A.zeta12 A.primitive_zeta12 P C q hq).2.2
  · intro j
    have hj : ((C.canonical q).borel.torus j.val : KPLocalExceptionalConstruction.ActualCover
        F A.zeta12 A.primitive_zeta12 q) ∈ (C.canonical q).iwasawa.compact.toOpenSubgroup := j.property
    have hfix := congrArg (fun u : Plus A P C (Sum.inr q) => u.val 1)
      (hf.1 ⟨(C.canonical q).borel.torus j.val, hj⟩)
    have hcov := f.property.1 ((C.canonical q).borel.torus j.val) 1
    have hs : inducingScalar (C.canonical q).borel 0 ((C.canonical q).borel.torus j.val) = 1 := by
      simp [inducingScalar, deltaHalf, normPower, (C.canonical q).iwasawa.intersection_norm _ hj]
    change f.val (1 * (C.canonical q).borel.torus j.val) = f.val 1 at hfix
    rw [mul_one] at hcov
    rw [one_mul] at hfix
    change f.val ((C.canonical q).borel.torus j.val) =
      inducingScalar (C.canonical q).borel 0 ((C.canonical q).borel.torus j.val) •
        tau (C.polarization q) ((C.canonical q).borel.retract ((C.canonical q).borel.torus j.val))
          (f.val 1) at hcov
    rw [hs, one_smul, (C.canonical q).borel.retract_torus] at hcov
    exact hcov.symm.trans hfix
  · exact hf.2

def plusReference (v : KPHilbert.Place F) : Plus A P C v :=
  match v with
  | Sum.inl _ => ⟨KPCplxPrincipalSeriesCharts.sphericalSection
      KPCplxPrincipalSeriesCharts.positiveParameter, by
      apply (le_iSup (KPCplxIntertwinerEigenvalues.harmonicKType
        KPCplxPrincipalSeriesCharts.positiveParameter) 0)
      rw [KPCplxIntertwinerEigenvalues.harmonicKType_zero_eq_span]
      exact Submodule.subset_span (Set.mem_singleton _)⟩
  | Sum.inr q => if hq : q ∉ C.exceptional then (normalized_reference A P C q hq).choose else 0

theorem plusReference_fixed (q : KPFinitePlace F) (hq : q ∉ C.exceptional)
    (k : (C.canonical q).iwasawa.compact.toOpenSubgroup) :
    IPlus (C.canonical q).borel (C.polarization q) k.val (plusReference A P C (Sum.inr q)) =
      plusReference A P C (Sum.inr q) := by
  simpa only [plusReference, dite_eq_left hq] using
    (normalized_reference A P C q hq).choose_spec.1 k

theorem plusReference_compact_value (q : KPFinitePlace F) (hq : q ∉ C.exceptional)
    (k : KPTameCompact.K0 F q) :
    localValue A P C (Sum.inr q)
      (KPGoodCompactSplitting.kStar F A.zeta12 A.primitive_zeta12 q
        (C.actual_compact q hq).choose k) (plusReference A P C (Sum.inr q)) =
      reference A P C (Sum.inr q) := by
  have hk : KPLocalExceptionalConstruction.actualGoodCompactSplit F A.zeta12 A.primitive_zeta12 q
      (C.actual_compact q hq).choose k ∈ (C.canonical q).iwasawa.compact.toOpenSubgroup := by
    change _ ∈ ((C.canonical q).iwasawa.compact.toOpenSubgroup :
      Subgroup (KPLocalExceptionalConstruction.ActualCover F A.zeta12 A.primitive_zeta12 q))
    have hm : KPLocalExceptionalConstruction.actualGoodCompactSplit F A.zeta12 A.primitive_zeta12 q
        (C.actual_compact q hq).choose k ∈
        (KPLocalExceptionalConstruction.actualGoodCompactSplit F A.zeta12 A.primitive_zeta12 q
          (C.actual_compact q hq).choose).range := MonoidHom.mem_range.mpr ⟨k, rfl⟩
    exact Eq.mpr (congrArg (fun K : Subgroup
      (KPLocalExceptionalConstruction.ActualCover F A.zeta12 A.primitive_zeta12 q) =>
        KPLocalExceptionalConstruction.actualGoodCompactSplit F A.zeta12 A.primitive_zeta12 q
          (C.actual_compact q hq).choose k ∈ K) (C.actual_compact q hq).choose_spec) hm
  have h := congrArg (fun f : Plus A P C (Sum.inr q) => f.val 1)
    ((normalized_reference A P C q hq).choose_spec.1 ⟨_, hk⟩)
  change (normalized_reference A P C q hq).choose.val (1 * _) =
    (normalized_reference A P C q hq).choose.val 1 at h
  rw [one_mul, (normalized_reference A P C q hq).choose_spec.2] at h
  simpa only [localValue, plusReference, dite_eq_left hq, reference,
    KPGlobalResidualConstruction.ScalarAbsorption.fullReference,
    KPLocalExceptionalConstruction.actualGoodCompactSplit, MonoidHom.comp_apply] using h

theorem exists_reference_stage (g : Raw A) :
    ∃ s : RestrictedTensorSimple.Level (bad A P C),
      ∀ v, v ∉ s.val → localValue A P C v (g v) (plusReference A P C v) = reference A P C v := by
  let E : Finset (KPHilbert.Place F) :=
    (KPAdelicCoverRestrictedProduct.bad_finite F).toFinset.image Sum.inr
  let Gbad : Finset (KPHilbert.Place F) := (Filter.eventually_cofinite.mp g.eventually).toFinset
  let s : RestrictedTensorSimple.Level (bad A P C) := ⟨bad A P C ∪ E ∪ Gbad, by simp⟩
  refine ⟨s, fun v hv => ?_⟩
  have hvb : v ∉ bad A P C := fun h => hv (by simp [s, h])
  have hvE : v ∉ E := fun h => hv (by simp [s, h])
  have hvG : v ∉ Gbad := fun h => hv (by simp [s, h])
  have hcompact : g v ∈ KPAdelicCoverRestrictedProduct.compact F A.zeta12 A.primitive_zeta12 v := by
    change g v ∈ (KPAdelicCoverRestrictedProduct.compact F A.zeta12 A.primitive_zeta12 v : Set _)
    simpa only [Gbad, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hvG
  cases v with
  | inl w => simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad] at hvb
  | inr q =>
    have hq : ¬ KPAdelicCoverRestrictedProduct.Bad F q := by
      intro h
      exact hvE (Finset.mem_image.mpr ⟨q, (Set.Finite.mem_toFinset _).mpr h, rfl⟩)
    have hC : q ∉ C.exceptional := by
      simpa [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad] using hvb
    change g (Sum.inr q) ∈ KPAdelicCoverRestrictedProduct.finiteCompact F A.zeta12 A.primitive_zeta12 q at hcompact
    simp only [KPAdelicCoverRestrictedProduct.finiteCompact, dite_eq_right hq, MonoidHom.mem_range] at hcompact
    obtain ⟨k, hk⟩ := hcompact
    rw [← hk]
    exact plusReference_compact_value A P C q hC k

private theorem rawStageValue_transition (s t : RestrictedTensorSimple.Level (bad A P C))
    (hst : s ≤ t) (g : Raw A)
    (hnew : ∀ v ∈ t.val, v ∉ s.val →
      localValue A P C v (g v) (plusReference A P C v) = reference A P C v)
    (x : PiTensorProduct ℂ (fun j : s.val => Plus A P C j.val)) :
    rawStageValue A P C t g (RestrictedTensorSimple.transition (Plus A P C)
      (plusReference A P C) (bad A P C) s t hst x) = rawStageValue A P C s g x := by
  have hm : PiTensorProduct.map (fun j : t.val => localValueMap A P C j.val (g j.val))
      (RestrictedTensorSimple.insert (Plus A P C) (plusReference A P C) s.val t.val hst x) =
      RestrictedTensorSimple.insert (Fiber A P C) (reference A P C) s.val t.val hst
        (PiTensorProduct.map (fun j : s.val => localValueMap A P C j.val (g j.val)) x) := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c x =>
      simp only [map_smul]
      congr 1
      rw [RestrictedTensorSimple.insert_pure, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod, RestrictedTensorSimple.insert_pure]
      congr 1
      funext j
      by_cases hj : j.val ∈ s.val
      · simp [hj, localValueMap]
      · simpa [hj, localValueMap] using hnew j.val j.property hj
    | add x y hx hy => simp only [map_add, hx, hy]
  unfold rawStageValue
  simp only [LinearMap.comp_apply, RestrictedTensorSimple.transition]
  rw [hm]
  exact congrArg (fun y => rationalEvaluation A (comparison A P C y)) Module.DirectLimit.of_f

 def referenceStage (g : Raw A) : RestrictedTensorSimple.Level (bad A P C) :=
  (exists_reference_stage A P C g).choose
 def expand (s : RestrictedTensorSimple.Level (bad A P C)) (g : Raw A) :
    RestrictedTensorSimple.Level (bad A P C) :=
  ⟨s.val ∪ (referenceStage A P C g).val, s.property.trans Finset.subset_union_left⟩
 theorem le_expand (s : RestrictedTensorSimple.Level (bad A P C)) (g : Raw A) :
    s ≤ expand A P C s g := Finset.subset_union_left
 theorem expand_mono {s t : RestrictedTensorSimple.Level (bad A P C)} (hst : s ≤ t)
    (g : Raw A) : expand A P C s g ≤ expand A P C t g :=
  Finset.union_subset_union hst (Finset.Subset.refl _)
 theorem expand_tail (s : RestrictedTensorSimple.Level (bad A P C)) (g : Raw A)
    (v : KPHilbert.Place F) (hv : v ∉ (expand A P C s g).val) :
    localValue A P C v (g v) (plusReference A P C v) = reference A P C v :=
  (exists_reference_stage A P C g).choose_spec v
    (fun h => hv (Finset.mem_union_right _ h))
 def stageLift (s : RestrictedTensorSimple.Level (bad A P C)) (g : Raw A) :
    PiTensorProduct ℂ (fun j : s.val => Plus A P C j.val) →ₗ[ℂ] ℂ :=
  (rawStageValue A P C (expand A P C s g) g).comp
    (RestrictedTensorSimple.transition (Plus A P C) (plusReference A P C)
      (bad A P C) s (expand A P C s g) (le_expand A P C s g))
 theorem stageLift_transition (s t : RestrictedTensorSimple.Level (bad A P C))
    (hst : s ≤ t) (g : Raw A)
    (x : PiTensorProduct ℂ (fun j : s.val => Plus A P C j.val)) :
    stageLift A P C t g (RestrictedTensorSimple.transition (Plus A P C)
      (plusReference A P C) (bad A P C) s t hst x) = stageLift A P C s g x := by
  dsimp only [stageLift, LinearMap.comp_apply]
  rw [(RestrictedTensorSimple.directedSystem (Plus A P C) (plusReference A P C)
    (bad A P C)).map_map hst (le_expand A P C t g)]
  rw [← (RestrictedTensorSimple.directedSystem (Plus A P C) (plusReference A P C)
    (bad A P C)).map_map (le_expand A P C s g) (expand_mono A P C hst g)]
  exact rawStageValue_transition A P C _ _ (expand_mono A P C hst g) g
    (fun v _ hv => expand_tail A P C s g v hv) _

def rawCoreValue (g : Raw A) :
    RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C) →ₗ[ℂ] ℂ :=
  Module.DirectLimit.lift ℂ (RestrictedTensorSimple.Level (bad A P C))
    (fun s => RestrictedTensorSimple.Stage (Plus A P C) s.val)
    (RestrictedTensorSimple.transition (Plus A P C) (plusReference A P C) (bad A P C))
    (fun s => stageLift A P C s g) (fun s t hst x => stageLift_transition A P C s t hst g x)
def rawCoreInsertion :
    RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C) →ₗ[ℂ] (Raw A → ℂ) where
  toFun x g := rawCoreValue A P C g x
  map_add' := by intro x y; funext g; exact map_add _ x y
  map_smul' := by intro c x; funext g; exact map_smul _ c x

theorem rawCoreInsertion_stage (s : RestrictedTensorSimple.Level (bad A P C))
    (x : PiTensorProduct ℂ (fun j : s.val => Plus A P C j.val)) (g : Raw A)
    (htail : ∀ v, v ∉ s.val → localValue A P C v (g v) (plusReference A P C v) = reference A P C v) :
    rawCoreInsertion A P C (RestrictedTensorSimple.stageInclusion (Plus A P C)
      (plusReference A P C) (bad A P C) s x) g = rawStageValue A P C s g x := by
  change rawCoreValue A P C g (RestrictedTensorSimple.stageInclusion (Plus A P C)
    (plusReference A P C) (bad A P C) s x) = _
  unfold rawCoreValue RestrictedTensorSimple.stageInclusion
  rw [Module.DirectLimit.lift_of]
  exact rawStageValue_transition A P C s _ (le_expand A P C s g) g (fun v _ hv => htail v hv) x

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
