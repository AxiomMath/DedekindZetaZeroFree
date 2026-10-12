module

public import DedekindZetaZeroFree.Adeles.Characters.SIntegerTraceAnnihilation
public import DedekindZetaZeroFree.Adeles.Characters.TraceCharacterNondegeneracy
public import DedekindZetaZeroFree.Adeles.Approximation.FiniteAdeleDensity

@[expose] public section

noncomputable section

open scoped NumberField Classical ENNReal
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPAdditiveFundamentalDomain

variable (F : Type) [Field F] [NumberField F]

def archParallelepiped : Set (InfiniteAdeleRing F) :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F) ⁻¹'
    ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)

def domain : Set (AdeleRing (𝓞 F) F) :=
  archParallelepiped F ×ˢ
    (KPAdelicTopology.integralAdeles F : Set (FiniteAdeleRing (𝓞 F) F))

scoped instance principalTranslation : AddAction F (AdeleRing (𝓞 F) F) where
  vadd a x := algebraMap F (AdeleRing (𝓞 F) F) a + x
  zero_vadd x := by
    change algebraMap F (AdeleRing (𝓞 F) F) 0 + x = x
    simp
  add_vadd a b x := by
    change algebraMap F (AdeleRing (𝓞 F) F) (a + b) + x =
      algebraMap F (AdeleRing (𝓞 F) F) a +
        (algebraMap F (AdeleRing (𝓞 F) F) b + x)
    simp [add_assoc]

open scoped DedekindZetaZeroFree.KPAdditiveFundamentalDomain

theorem principalTranslation_apply (a : F) (x : AdeleRing (𝓞 F) F) :
    a +ᵥ x = algebraMap F (AdeleRing (𝓞 F) F) a + x := rfl

 def archHomeo : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace F => v.IsReal)
    (fun v => v.Completion)).trans
    (Homeomorph.prodCongr
      (Homeomorph.piCongrRight (fun v =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph))
      ((Homeomorph.piCongrRight (fun v =>
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp v.2)).toHomeomorph)).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight (fun _ => InfinitePlace.not_isReal_iff_isComplex)))))

private theorem archHomeo_apply (x : InfiniteAdeleRing F) :
    archHomeo F x = InfiniteAdeleRing.ringEquiv_mixedSpace F x := rfl

private theorem exists_reduction (a : AdeleRing (𝓞 F) F) :
    ∃ z : F, a - algebraMap F (AdeleRing (𝓞 F) F) z ∈ domain F := by
  let b := mixedEmbedding.latticeBasis F
  let e := archHomeo F
  obtain ⟨r, hrem⟩ := KPAdelicTopology.exists_integral_remainder F a.2
  let y := e (a.1 - algebraMap F (InfiniteAdeleRing F) r)
  have hf : (ZSpan.floor b y : mixedEmbedding.mixedSpace F) ∈
      mixedEmbedding.integerLattice F :=
    (mixedEmbedding.mem_span_latticeBasis F).mp (ZSpan.floor b y).property
  obtain ⟨s, hs⟩ := hf
  let z : F := r + (s : F)
  refine ⟨z, ⟨?_, ?_⟩⟩
  · change InfiniteAdeleRing.ringEquiv_mixedSpace F
      (a.1 - algebraMap F (InfiniteAdeleRing F) z) ∈ ZSpan.fundamentalDomain b
    rw [← archHomeo_apply]
    have hs' : mixedEmbedding F (s : F) =
        (ZSpan.floor b y : mixedEmbedding.mixedSpace F) := hs
    have hmap (x : InfiniteAdeleRing F) (t : F) :
        e (x - algebraMap F (InfiniteAdeleRing F) t) = e x - mixedEmbedding F t := by
      simp only [e, archHomeo_apply, map_sub,
        ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    have hfrac : e (a.1 - algebraMap F (InfiniteAdeleRing F) z) = ZSpan.fract b y := by
      rw [ZSpan.fract_apply, ← hs']
      change e (a.1 - algebraMap F (InfiniteAdeleRing F) (r + (s : F))) =
        e (a.1 - algebraMap F (InfiniteAdeleRing F) r) - mixedEmbedding F (s : F)
      rw [hmap, hmap, map_add]
      abel
    rw [hfrac]
    exact ZSpan.fract_mem_fundamentalDomain b y
  · change a.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) z ∈
      KPAdelicTopology.integralAdeles F
    have hsfin : algebraMap F (FiniteAdeleRing (𝓞 F) F) (s : F) ∈
        KPAdelicTopology.integralAdeles F := by
      intro v
      exact HeightOneSpectrum.coe_algebraMap_mem (RingOfIntegers F) F v s
    dsimp [z]
    rw [map_add, ← sub_sub]
    exact (KPAdelicTopology.integralAdeles F).sub_mem hrem hsfin

theorem projection_surjective :
    (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)) ''
      domain F = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
    (AdeleRing.principalSubgroup (𝓞 F) F) q
  obtain ⟨z, hz⟩ := exists_reduction F a
  refine ⟨a - algebraMap F (AdeleRing (𝓞 F) F) z, hz, ?_⟩
  change QuotientAddGroup.mk (a - algebraMap F (AdeleRing (𝓞 F) F) z) =
    QuotientAddGroup.mk a
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  have h : algebraMap F (AdeleRing (𝓞 F) F) z ∈
      AdeleRing.principalSubgroup (𝓞 F) F := ⟨z, rfl⟩
  simpa only [sub_sub_cancel_left] using
    (AdeleRing.principalSubgroup (𝓞 F) F).neg_mem h

theorem projection_injective :
    Set.InjOn (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F))
      (domain F) := by
  intro x hx y hy hxy
  have hsub : x - y ∈ AdeleRing.principalSubgroup (𝓞 F) F :=
    QuotientAddGroup.eq_iff_sub_mem.mp hxy
  obtain ⟨c, hc⟩ := hsub
  have hfin : algebraMap F (FiniteAdeleRing (𝓞 F) F) c ∈
      KPAdelicTopology.integralAdeles F := by
    have h := (KPAdelicTopology.integralAdeles F).sub_mem hx.2 hy.2
    have heq := congrArg Prod.snd hc
    change algebraMap F (FiniteAdeleRing (𝓞 F) F) c = x.2 - y.2 at heq
    rwa [← heq] at h
  have hfinite : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F c ≤ 1 := by
    intro v
    have hv := hfin v
    change (c : v.adicCompletion F) ∈ v.adicCompletionIntegers F at hv
    simpa only [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.adicCompletion.valued_coe] using hv
  obtain ⟨s, hs⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F c hfinite
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have harch : e x.1 - e y.1 = mixedEmbedding F c := by
    have heq := congrArg Prod.fst hc
    change algebraMap F (InfiniteAdeleRing F) c = x.1 - y.1 at heq
    rw [← map_sub, ← heq, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  have hspan : -e y.1 + e x.1 ∈
      Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F)) := by
    rw [add_comm, ← sub_eq_add_neg, harch]
    apply (mixedEmbedding.mem_span_latticeBasis F).mpr
    exact ⟨s, congrArg (mixedEmbedding F) hs⟩
  have harchEq : e y.1 = e x.1 := by
    have h := (ZSpan.fract_eq_fract (mixedEmbedding.latticeBasis F) (e y.1) (e x.1)).mpr hspan
    rw [ZSpan.fract_eq_self.mpr hy.1, ZSpan.fract_eq_self.mpr hx.1] at h
    exact h
  have hc0 : c = 0 := by
    apply mixedEmbedding_injective
    simpa [harchEq] using harch.symm
  have heq : x - y = 0 := by simpa [hc0] using hc.symm
  exact sub_eq_zero.mp heq

theorem compact_closed_cover :
    IsCompact (closure (archParallelepiped F) ×ˢ
      (KPAdelicTopology.integralAdeles F : Set (FiniteAdeleRing (𝓞 F) F))) := by
  have hC : IsCompact ((archHomeo F) ⁻¹'
      ((mixedEmbedding.latticeBasis F).parallelepiped : Set _)) :=
    (archHomeo F).isCompact_preimage.mpr
      (mixedEmbedding.latticeBasis F).parallelepiped.isCompact
  have hP : archParallelepiped F ⊆ (archHomeo F) ⁻¹'
      ((mixedEmbedding.latticeBasis F).parallelepiped : Set _) := by
    intro x hx
    rw [Set.mem_preimage, archHomeo_apply]
    exact ZSpan.fundamentalDomain_subset_parallelepiped _ hx
  exact (hC.closure_of_subset hP).prod (KPAdelicTopology.integralAdeles_isCompact F)

theorem quotient_compactSpace :
    CompactSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) := by
  let q := QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)
  have hq : Continuous q := QuotientAddGroup.continuous_mk
  have hC : IsCompact (q '' (closure (archParallelepiped F) ×ˢ
      (KPAdelicTopology.integralAdeles F : Set (FiniteAdeleRing (𝓞 F) F)))) :=
    (compact_closed_cover F).image hq
  apply isCompact_univ_iff.mp
  apply hC.of_isClosed_subset isClosed_univ
  rw [← projection_surjective F]
  apply Set.image_mono
  exact Set.prod_mono subset_closure (Set.Subset.refl _)

theorem domain_measurableSet : MeasurableSet (domain F) := by
  letI : MeasurableSpace (InfiniteAdeleRing F) := borel _
  letI : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩
  have hc : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    have he : (archHomeo F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
        InfiniteAdeleRing.ringEquiv_mixedSpace F := funext (archHomeo_apply F)
    rw [← he]
    exact (archHomeo F).continuous
  have hP : MeasurableSet (archParallelepiped F) :=
    (ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis F)).preimage
      hc.measurable
  have hO := (KPAdelicTopology.integralAdeles_isOpen F).measurableSet
  have hcfst : Continuous (fun x : AdeleRing (𝓞 F) F => x.1) := continuous_fst
  have hcsnd : Continuous (fun x : AdeleRing (𝓞 F) F => x.2) := continuous_snd
  have hfst : Measurable (fun x : AdeleRing (𝓞 F) F => x.1) := hcfst.measurable
  have hsnd : Measurable (fun x : AdeleRing (𝓞 F) F => x.2) := hcsnd.measurable
  exact (hP.preimage hfst).inter (hO.preimage hsnd)

theorem isAddFundamentalDomain (μ : Measure (AdeleRing (𝓞 F) F))
    [μ.IsAddHaarMeasure] :
    IsAddFundamentalDomain F (domain F) μ := by
  apply IsAddFundamentalDomain.mk' (domain_measurableSet F).nullMeasurableSet
  intro x
  obtain ⟨z, hz⟩ := exists_reduction F x
  have hz' : (-z) +ᵥ x ∈ domain F := by
    simpa only [principalTranslation_apply, map_neg, sub_eq_add_neg, add_comm] using hz
  refine ⟨-z, hz', ?_⟩
  intro w hw
  have hq (a : F) :
      QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F) (a +ᵥ x) =
        QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F) x := by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simpa only [principalTranslation_apply, add_sub_cancel_right] using
      (show algebraMap F (AdeleRing (𝓞 F) F) a ∈
        AdeleRing.principalSubgroup (𝓞 F) F from ⟨a, rfl⟩)
  have heq := projection_injective F hw hz' ((hq w).trans (hq (-z)).symm)
  apply (algebraMap F (AdeleRing (𝓞 F) F)).injective
  exact add_right_cancel heq

theorem domain_mass (μ : Measure (AdeleRing (𝓞 F) F))
    [μ.IsAddHaarMeasure] :
    0 < μ (domain F) ∧ μ (domain F) < ∞ := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : VAddInvariantMeasure F (AdeleRing (𝓞 F) F) μ := ⟨fun c s hs => by
    change μ ((fun x => algebraMap F (AdeleRing (𝓞 F) F) c + x) ⁻¹' s) = μ s
    exact measure_preimage_add μ _ s⟩
  refine ⟨pos_iff_ne_zero.mpr ((isAddFundamentalDomain F μ).measure_ne_zero (NeZero.ne μ)), ?_⟩
  letI : IsFiniteMeasureOnCompacts μ := inferInstance
  exact lt_of_le_of_lt
    (measure_mono (Set.prod_mono subset_closure (Set.Subset.refl _)))
    (@IsCompact.measure_lt_top (AdeleRing (𝓞 F) F) _ _ μ _ _ (compact_closed_cover F))

end DedekindZetaZeroFree.KPAdditiveFundamentalDomain

end
