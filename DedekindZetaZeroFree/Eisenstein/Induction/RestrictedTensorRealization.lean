module

public import DedekindZetaZeroFree.Metaplectic.Weil.LocalSectionCovariance
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.FiniteCompactOpenLevels
public import DedekindZetaZeroFree.Eisenstein.Induction.TorusTensorFormula
public import DedekindZetaZeroFree.Metaplectic.Torus.PeriodizationAndAveraging

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.SourceTensor
open KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

abbrev Core := RestrictedTensorSimple.Core (LocalFiber F ζ hζ P C)
  (localReference F ζ hζ P C) C.exceptional

def realization : Core F ζ hζ P C →ₗ[ℂ]
    KPGlobalTorusPeriodizationInverse.ProductUnitary F ζ hζ P :=
  Module.DirectLimit.lift ℂ (RestrictedTensorSimple.Level C.exceptional)
    (fun s => TensorStage F ζ hζ P C s.val)
    (RestrictedTensorSimple.transition (LocalFiber F ζ hζ P C)
      (localReference F ζ hζ P C) C.exceptional)
    (fun s => finiteTensorRealization F ζ hζ P C s.val s.property)
    (by
      intro s t hst x
      exact congrArg (fun l => l x)
        (tensor_insertion_compatible F ζ hζ P C s.val t.val s.property hst))

@[simp] theorem realization_stage (s : RestrictedTensorSimple.Level C.exceptional)
    (x : TensorStage F ζ hζ P C s.val) :
    realization F ζ hζ P C
      (RestrictedTensorSimple.stageInclusion (LocalFiber F ζ hζ P C)
        (localReference F ζ hζ P C) C.exceptional s x) =
      finiteTensorRealization F ζ hζ P C s.val s.property x := by
  unfold realization RestrictedTensorSimple.stageInclusion
  rw [Module.DirectLimit.lift_of]

theorem evaluated_tail (raw : RestrictedCover F ζ hζ) :
    ∀ᶠ q in Filter.cofinite,
      (LocalSeed.finite F ζ hζ P C q).val
        (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) =
          localReference F ζ hζ P C q := by
  have hraw : ∀ᶠ q in Filter.cofinite,
      raw (Sum.inr q) ∈ finiteCompact F ζ hζ q := by
    exact Sum.inr_injective.tendsto_cofinite.eventually raw.property
  filter_upwards [hraw, C.exceptional.finite_toSet.eventually_cofinite_notMem,
    (bad_finite F).eventually_cofinite_notMem] with q hr hq hb
  obtain ⟨ht, hc⟩ := C.actual_compact q hq
  have hk : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q)) ∈
      (C.canonical q).iwasawa.compact.toOpenSubgroup := by
    change _ ∈ (C.canonical q).iwasawa.compact.toOpenSubgroup.toSubgroup
    rw [hc]
    rw [finiteCompact, dif_neg hb] at hr
    obtain ⟨k, hk⟩ := hr
    exact ⟨k, by rw [← hk]; rfl⟩
  have hf := LocalSeed.finite_right_fixed F ζ hζ P C q hq ⟨_, hk⟩ 1
  rw [one_mul, LocalSeed.finite_one] at hf
  exact hf

def evaluatedStage (raw : RestrictedCover F ζ hζ) :
    RestrictedTensorSimple.Level C.exceptional :=
  ⟨C.exceptional ∪ (Filter.eventually_cofinite.mp (evaluated_tail F ζ hζ P C raw)).toFinset,
    Finset.subset_union_left⟩

def evaluatedTensor (raw : RestrictedCover F ζ hζ) : Core F ζ hζ P C :=
  RestrictedTensorSimple.stageInclusion (LocalFiber F ζ hζ P C)
    (localReference F ζ hζ P C) C.exceptional (evaluatedStage F ζ hζ P C raw)
    (PiTensorProduct.tprod ℂ (fun q => (LocalSeed.finite F ζ hζ P C q.val).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val) (raw (Sum.inr q.val)))))

theorem evaluatedTensor_one :
    realization F ζ hζ P C (evaluatedTensor F ζ hζ P C 1) =
      TorusReference.finiteReference F ζ hζ P C C.exceptional le_rfl := by
  rw [evaluatedTensor, realization_stage]
  change finiteTensorRealization F ζ hζ P C _ _
    (PiTensorProduct.tprod ℂ (fun q => (LocalSeed.finite F ζ hζ P C q.val).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val) 1))) = _
  simp only [map_one, LocalSeed.finite_one]
  have hi := LinearMap.congr_fun (tensor_insertion_compatible F ζ hζ P C C.exceptional
    (evaluatedStage F ζ hζ P C 1).val le_rfl (evaluatedStage F ζ hζ P C 1).property)
    (PiTensorProduct.tprod ℂ (fun q : C.exceptional => localReference F ζ hζ P C q.val))
  simp only [LinearMap.comp_apply, RestrictedTensorSimple.insert_pure, dite_eq_ite, ite_self] at hi
  exact hi

theorem evaluatedStage_tail (raw : RestrictedCover F ζ hζ)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ (evaluatedStage F ζ hζ P C raw).val) :
    (LocalSeed.finite F ζ hζ P C q).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) =
        localReference F ζ hζ P C q := by
  by_contra h
  apply hq
  apply Finset.mem_union_right
  exact (Filter.eventually_cofinite.mp (evaluated_tail F ζ hζ P C raw)).mem_toFinset.mpr h

theorem evaluatedTensor_stage (raw : RestrictedCover F ζ hζ)
    (s : RestrictedTensorSimple.Level C.exceptional)
    (hs : ∀ q, q ∉ s.val → (LocalSeed.finite F ζ hζ P C q).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) =
        localReference F ζ hζ P C q) :
    evaluatedTensor F ζ hζ P C raw =
      RestrictedTensorSimple.stageInclusion (LocalFiber F ζ hζ P C)
        (localReference F ζ hζ P C) C.exceptional s
        (PiTensorProduct.tprod ℂ (fun q => (LocalSeed.finite F ζ hζ P C q.val).val
          (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val) (raw (Sum.inr q.val))))) := by
  let t := evaluatedStage F ζ hζ P C raw
  let u : RestrictedTensorSimple.Level C.exceptional :=
    ⟨t.val ∪ s.val, t.property.trans Finset.subset_union_left⟩
  have htu : t ≤ u := Finset.subset_union_left
  have hsu : s ≤ u := Finset.subset_union_right
  have hins (v : RestrictedTensorSimple.Level C.exceptional) (hv : v ≤ u)
      (htail : ∀ q, q ∉ v.val → (LocalSeed.finite F ζ hζ P C q).val
        (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) =
          localReference F ζ hζ P C q) :
      RestrictedTensorSimple.stageInclusion (LocalFiber F ζ hζ P C)
        (localReference F ζ hζ P C) C.exceptional v
        (PiTensorProduct.tprod ℂ (fun q => (LocalSeed.finite F ζ hζ P C q.val).val
          (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val) (raw (Sum.inr q.val))))) =
      RestrictedTensorSimple.stageInclusion (LocalFiber F ζ hζ P C)
        (localReference F ζ hζ P C) C.exceptional u
        (PiTensorProduct.tprod ℂ (fun q => (LocalSeed.finite F ζ hζ P C q.val).val
          (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val) (raw (Sum.inr q.val))))) := by
    have hi : RestrictedTensorSimple.stageInclusion (LocalFiber F ζ hζ P C)
        (localReference F ζ hζ P C) C.exceptional u
        (RestrictedTensorSimple.transition (LocalFiber F ζ hζ P C)
          (localReference F ζ hζ P C) C.exceptional v u hv
          (PiTensorProduct.tprod ℂ (fun q => (LocalSeed.finite F ζ hζ P C q.val).val
            (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val) (raw (Sum.inr q.val)))))) =
        RestrictedTensorSimple.stageInclusion (LocalFiber F ζ hζ P C)
          (localReference F ζ hζ P C) C.exceptional v
          (PiTensorProduct.tprod ℂ (fun q => (LocalSeed.finite F ζ hζ P C q.val).val
            (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val) (raw (Sum.inr q.val))))) :=
      Module.DirectLimit.of_f
    rw [← hi]
    change RestrictedTensorSimple.stageInclusion _ _ _ u
      (RestrictedTensorSimple.insert _ _ v.val u.val hv _) = _
    rw [RestrictedTensorSimple.insert_pure]
    congr 2
    funext q
    split_ifs with h
    · rfl
    · exact (htail q.val h).symm
  exact (hins t htu (evaluatedStage_tail F ζ hζ P C raw)).trans (hins s hsu hs).symm

theorem evaluatedTensor_congr (g h : RestrictedCover F ζ hζ)
    (he : ∀ q, (LocalSeed.finite F ζ hζ P C q).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (g (Sum.inr q))) =
      (LocalSeed.finite F ζ hζ P C q).val
        (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (h (Sum.inr q)))) :
    evaluatedTensor F ζ hζ P C g = evaluatedTensor F ζ hζ P C h := by
  have ht : ∀ q, q ∉ (evaluatedStage F ζ hζ P C g).val →
      (LocalSeed.finite F ζ hζ P C q).val
        (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (h (Sum.inr q))) =
          localReference F ζ hζ P C q := by
    intro q hq
    rw [← he]
    exact evaluatedStage_tail F ζ hζ P C g q hq
  rw [evaluatedTensor_stage F ζ hζ P C h (evaluatedStage F ζ hζ P C g) ht]
  unfold evaluatedTensor
  congr 2
  funext q
  exact he q.val

theorem evaluatedTensor_upper (raw : RestrictedCover F ζ hζ)
    (y : KPAdelicCoverRestrictedProduct.Adeles F) :
    evaluatedTensor F ζ hζ P C (KPGlobalTorusFunctionData.rootTuple F ζ hζ y * raw) =
      evaluatedTensor F ζ hζ P C raw := by
  apply evaluatedTensor_congr
  intro q
  exact LocalCovariance.finite_upper F ζ hζ P C q _ _

theorem evaluatedTensor_scalar (raw : RestrictedCover F ζ hζ)
    (z : KPAdelicCoverRestrictedProduct.Ideles F) :
    evaluatedTensor F ζ hζ P C (scalarTuple F ζ hζ z * raw) =
      evaluatedTensor F ζ hζ P C raw := by
  apply evaluatedTensor_congr
  intro q
  exact LocalCovariance.finite_scalar F ζ hζ P C q _ _

theorem evaluatedTensor_right_level (raw u : RestrictedCover F ζ hζ)
    (hu : u ∈ ActualFiniteFactor.productTuples F ζ hζ
      (FiniteLevels.productLevel F ζ hζ P C)) :
    evaluatedTensor F ζ hζ P C (raw * u) = evaluatedTensor F ζ hζ P C raw := by
  apply evaluatedTensor_congr
  intro q
  change (LocalSeed.finite F ζ hζ P C q).val
    (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q) * u (Sum.inr q))) = _
  rw [map_mul]
  exact FiniteLevels.raw_local_fixed F ζ hζ P C u hu q _

end DedekindZetaZeroFree.EisensteinReferenceSections.SourceTensor

end
