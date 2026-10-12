module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RationalPeriodization.SphericalReferences
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RestrictedTensorProduct

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

abbrev Raw := KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12
abbrev Plus := plusLocal R (imageData R N P C)
abbrev PlusCore := RestrictedTensorSimple.Core (Plus R N P C)
  (plusReference R N P C) (bad R P C)
abbrev FiberCore := RestrictedTensorSimple.Core (Fiber R P C) (reference R P C) (bad R P C)

def complexMatrix (w : InfinitePlace F)
    (g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)) :
    KPCplxCharacterHaar.ComplexGL2 :=
  Matrix.GeneralLinearGroup.map
    (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).toRingHom g.g

def localValue : ∀ p, KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p →
    Plus R N P C p →ₗ[ℂ] Fiber R P C p
  | Sum.inl w, g =>
    { toFun := fun f => (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
        R.A.primitive_zeta12 g.epsilon : ℂ) * f.val
          (complexMatrix R w g)
      map_add' := by intros; exact mul_add _ _ _
      map_smul' := by intros; exact mul_left_comm _ _ _ }
  | Sum.inr q, g =>
    { toFun := fun f => f.val (KPPGLLocalCover.coverQuotient F R.A.zeta12
        R.A.primitive_zeta12 (Sum.inr q) g)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

theorem reference_value_good_compact (q : KPFinitePlace F)
    (hq : Sum.inr q ∉ bad R P C) (k : KPTameCompact.K0 F q) :
    localValue R N P C (Sum.inr q)
      (KPGoodCompactSplitting.kStar F R.A.zeta12 R.A.primitive_zeta12 q
        (tame R P C q hq) k) (plusReference R N P C (Sum.inr q)) =
      reference R P C (Sum.inr q) := by
  have h := congrArg (fun f : Plus R N P C (Sum.inr q) => f.val 1)
    (plusReference_spherical R N P C q hq k)
  change (plusReference R N P C (Sum.inr q)).val
    (1 * KPLocalExceptionalConstruction.actualGoodCompactSplit F R.A.zeta12
      R.A.primitive_zeta12 q (tame R P C q hq) k) = _ at h
  simpa only [localValue, LinearMap.coe_mk, AddHom.coe_mk, one_mul,
    KPLocalExceptionalConstruction.actualGoodCompactSplit, MonoidHom.comp_apply,
    plusReference_one R N P C q hq] using h

theorem arch_bad (w : InfinitePlace F) : Sum.inl w ∈ bad R P C := by
  simp [bad, PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.badSet]

theorem exists_reference_stage (g : Raw R) :
    ∃ s : RestrictedTensorSimple.Level (bad R P C), ∀ p, p ∉ s.val →
      localValue R N P C p (g p) (plusReference R N P C p) = reference R P C p := by
  let E : Finset (KPHilbert.Place F) :=
    (KPAdelicCoverRestrictedProduct.bad_finite F).toFinset.image Sum.inr
  let Gbad : Finset (KPHilbert.Place F) :=
    (Filter.eventually_cofinite.mp g.eventually).toFinset
  let s : RestrictedTensorSimple.Level (bad R P C) := ⟨bad R P C ∪ E ∪ Gbad, by simp⟩
  refine ⟨s, fun p hp => ?_⟩
  have hpI : p ∉ bad R P C := fun h => hp (by simp [s, h])
  have hpE : p ∉ E := fun h => hp (by simp [s, h])
  have hpG : p ∉ Gbad := fun h => hp (by simp [s, h])
  have hcompact : g p ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12
      R.A.primitive_zeta12 p := by
    change g p ∈ (KPAdelicCoverRestrictedProduct.compact F R.A.zeta12
      R.A.primitive_zeta12 p : Set _)
    simpa only [Gbad, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] using hpG
  cases p with
  | inl w => exact False.elim (hpI (arch_bad R P C w))
  | inr q =>
    have hq : ¬ KPAdelicCoverRestrictedProduct.Bad F q := by
      intro h
      exact hpE (Finset.mem_image.mpr ⟨q, (Set.Finite.mem_toFinset _).mpr h, rfl⟩)
    change g (Sum.inr q) ∈ KPAdelicCoverRestrictedProduct.finiteCompact F R.A.zeta12
      R.A.primitive_zeta12 q at hcompact
    simp only [KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hq,
      MonoidHom.mem_range] at hcompact
    obtain ⟨k, hk⟩ := hcompact
    rw [← hk]
    exact reference_value_good_compact R N P C q hpI k

def stageVector (s : RestrictedTensorSimple.Level (bad R P C)) (g : Raw R) :
    RestrictedTensorSimple.Stage (Plus R N P C) s.val →ₗ[ℂ] FiberCore R P C :=
  (RestrictedTensorSimple.stageInclusion (Fiber R P C) (reference R P C) (bad R P C) s).comp
    (PiTensorProduct.map (fun p : s.val => localValue R N P C p (g p)))

@[simp] theorem stageVector_pure (s : RestrictedTensorSimple.Level (bad R P C))
    (g : Raw R) (x : ∀ p : s.val, Plus R N P C p) :
    stageVector R N P C s g (PiTensorProduct.tprod ℂ x) =
      RestrictedTensorSimple.stageInclusion (Fiber R P C) (reference R P C) (bad R P C) s
        (PiTensorProduct.tprod ℂ (fun p : s.val => localValue R N P C p (g p) (x p))) := by
  simp [stageVector, PiTensorProduct.map_tprod]

theorem stageVector_transition (s t : RestrictedTensorSimple.Level (bad R P C))
    (hst : s ≤ t) (g : Raw R)
    (hnew : ∀ p ∈ t.val, p ∉ s.val → localValue R N P C p (g p)
      (plusReference R N P C p) = reference R P C p)
    (x : RestrictedTensorSimple.Stage (Plus R N P C) s.val) :
    stageVector R N P C t g
      (RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
        (bad R P C) s t hst x) = stageVector R N P C s g x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul]
    congr 1
    rw [RestrictedTensorSimple.transition, RestrictedTensorSimple.insert_pure,
      stageVector_pure, stageVector_pure]
    have hvec : (fun p : t.val => localValue R N P C p (g p)
        (if h : p.val ∈ s.val then x ⟨p.val, h⟩ else plusReference R N P C p.val)) =
        (fun p : t.val => if h : p.val ∈ s.val then
          localValue R N P C p (g p) (x ⟨p.val, h⟩) else reference R P C p.val) := by
      funext p
      split_ifs with h
      · rfl
      · exact hnew p p.property h
    have he := congrArg (PiTensorProduct.tprod ℂ) hvec
    have hi := RestrictedTensorSimple.insert_pure (Fiber R P C) (reference R P C)
      s.val t.val hst (fun p : s.val => localValue R N P C p (g p) (x p))
    have hi' : PiTensorProduct.tprod ℂ (fun p : t.val => if h : p.val ∈ s.val then
        localValue R N P C p (g p) (x ⟨p.val, h⟩) else reference R P C p.val) =
        RestrictedTensorSimple.insert (Fiber R P C) (reference R P C) s.val t.val hst
          (PiTensorProduct.tprod ℂ (fun p : s.val => localValue R N P C p (g p) (x p))) := by
      exact hi.symm
    exact (congrArg (RestrictedTensorSimple.stageInclusion (Fiber R P C)
      (reference R P C) (bad R P C) t) (he.trans hi')).trans Module.DirectLimit.of_f
  | add x y hx hy => simp only [map_add, hx, hy]

 def expanded (s : RestrictedTensorSimple.Level (bad R P C)) (g : Raw R) :
    RestrictedTensorSimple.Level (bad R P C) :=
  ⟨s.val ∪ (exists_reference_stage R N P C g).choose.val,
    s.property.trans Finset.subset_union_left⟩
 theorem expanded_ge (s : RestrictedTensorSimple.Level (bad R P C)) (g : Raw R) :
    s ≤ expanded R N P C s g := Finset.subset_union_left
private theorem expanded_tail (s : RestrictedTensorSimple.Level (bad R P C)) (g : Raw R) :
    ∀ p, p ∉ (expanded R N P C s g).val → localValue R N P C p (g p)
      (plusReference R N P C p) = reference R P C p := by
  intro p hp
  exact (exists_reference_stage R N P C g).choose_spec p
    (fun h => hp (Finset.mem_union_right _ h))

def rawStageVector (s : RestrictedTensorSimple.Level (bad R P C)) (g : Raw R) :
    RestrictedTensorSimple.Stage (Plus R N P C) s.val →ₗ[ℂ] FiberCore R P C :=
  (stageVector R N P C (expanded R N P C s g) g).comp
    (RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
      (bad R P C) s (expanded R N P C s g) (expanded_ge R N P C s g))

theorem rawStageVector_enlarge (s t : RestrictedTensorSimple.Level (bad R P C))
    (hst : s ≤ t) (g : Raw R)
    (htail : ∀ p, p ∉ t.val → localValue R N P C p (g p)
      (plusReference R N P C p) = reference R P C p) :
    rawStageVector R N P C s g = (stageVector R N P C t g).comp
      (RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
        (bad R P C) s t hst) := by
  let u : RestrictedTensorSimple.Level (bad R P C) :=
    ⟨(expanded R N P C s g).val ∪ t.val,
      (expanded R N P C s g).property.trans Finset.subset_union_left⟩
  have hsu : expanded R N P C s g ≤ u := Finset.subset_union_left
  have htu : t ≤ u := Finset.subset_union_right
  apply LinearMap.ext
  intro x
  change stageVector R N P C (expanded R N P C s g) g _ = stageVector R N P C t g _
  rw [← stageVector_transition R N P C _ u hsu g
      (fun p _ hp => expanded_tail R N P C s g p hp),
    ← stageVector_transition R N P C t u htu g (fun p _ hp => htail p hp)]
  congr 1
  exact ((RestrictedTensorSimple.directedSystem (Plus R N P C)
    (plusReference R N P C) (bad R P C)).map_map _ _ x).trans
      ((RestrictedTensorSimple.directedSystem (Plus R N P C)
        (plusReference R N P C) (bad R P C)).map_map _ _ x).symm

theorem rawStageVector_transition (s t : RestrictedTensorSimple.Level (bad R P C))
    (hst : s ≤ t) (g : Raw R) (x : RestrictedTensorSimple.Stage (Plus R N P C) s.val) :
    rawStageVector R N P C t g
      (RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
        (bad R P C) s t hst x) = rawStageVector R N P C s g x := by
  let u := expanded R N P C t g
  have htu : t ≤ u := expanded_ge R N P C t g
  rw [rawStageVector_enlarge R N P C t u htu g (expanded_tail R N P C t g),
    rawStageVector_enlarge R N P C s u (hst.trans htu) g (expanded_tail R N P C t g)]
  simp only [LinearMap.comp_apply]
  congr 1
  exact (RestrictedTensorSimple.directedSystem (Plus R N P C)
    (plusReference R N P C) (bad R P C)).map_map _ _ x

def rawCoreVector (g : Raw R) : PlusCore R N P C →ₗ[ℂ] FiberCore R P C :=
  Module.DirectLimit.lift ℂ (RestrictedTensorSimple.Level (bad R P C))
    (fun s => RestrictedTensorSimple.Stage (Plus R N P C) s.val)
    (RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C) (bad R P C))
    (fun s => rawStageVector R N P C s g)
    (fun s t hst x => rawStageVector_transition R N P C s t hst g x)

theorem rawCoreVector_stage (s : RestrictedTensorSimple.Level (bad R P C)) (g : Raw R)
    (htail : ∀ p, p ∉ s.val → localValue R N P C p (g p)
      (plusReference R N P C p) = reference R P C p)
    (x : RestrictedTensorSimple.Stage (Plus R N P C) s.val) :
    rawCoreVector R N P C g (RestrictedTensorSimple.stageInclusion
      (Plus R N P C) (plusReference R N P C) (bad R P C) s x) =
      stageVector R N P C s g x := by
  rw [rawCoreVector, RestrictedTensorSimple.stageInclusion, Module.DirectLimit.lift_of]
  rw [rawStageVector_enlarge R N P C s s le_rfl g htail]
  change stageVector R N P C s g (RestrictedTensorSimple.insert
    (Plus R N P C) (plusReference R N P C) s.val s.val le_rfl x) = _
  have he : RestrictedTensorSimple.insert (Plus R N P C) (plusReference R N P C)
      s.val s.val le_rfl = LinearMap.id := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro y
    simp only [LinearMap.compMultilinearMap_apply, RestrictedTensorSimple.insert_pure,
      LinearMap.id_apply]
    congr 1
    funext p
    simp [p.property]
  rw [he, LinearMap.id_apply]

theorem rawCoreVector_congr (s : RestrictedTensorSimple.Level (bad R P C))
    (g h : Raw R) (x : RestrictedTensorSimple.Stage (Plus R N P C) s.val)
    (he : ∀ p f, localValue R N P C p (g p) f = localValue R N P C p (h p) f) :
    rawCoreVector R N P C g (RestrictedTensorSimple.stageInclusion
      (Plus R N P C) (plusReference R N P C) (bad R P C) s x) =
    rawCoreVector R N P C h (RestrictedTensorSimple.stageInclusion
      (Plus R N P C) (plusReference R N P C) (bad R P C) s x) := by
  let u := expanded R N P C s g
  let y := RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
    (bad R P C) s u (expanded_ge R N P C s g) x
  have hins : RestrictedTensorSimple.stageInclusion (Plus R N P C) (plusReference R N P C)
      (bad R P C) u y = RestrictedTensorSimple.stageInclusion (Plus R N P C)
        (plusReference R N P C) (bad R P C) s x := Module.DirectLimit.of_f
  rw [← hins, rawCoreVector_stage R N P C u g (expanded_tail R N P C s g),
    rawCoreVector_stage R N P C u h (fun p hp =>
      (he p (plusReference R N P C p)).symm.trans (expanded_tail R N P C s g p hp))]
  have hm : ∀ p, localValue R N P C p (g p) = localValue R N P C p (h p) :=
    fun p => LinearMap.ext (he p)
  simp only [stageVector, hm]

def rawRationalVector (g : Raw R) : PlusCore R N P C →ₗ[ℂ]
    KPGlobalResidualConstruction.smoothRationalFiber F R.A.zeta12 R.A.primitive_zeta12 :=
  (comparisonSmooth R P C).comp (rawCoreVector R N P C g)

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
