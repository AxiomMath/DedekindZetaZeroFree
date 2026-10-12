module

public import DedekindZetaZeroFree.Adeles.Quotients.AdditiveFundamentalDomainMeasure

@[expose] public section

section

namespace DedekindZetaZeroFree.QuotientProbability
noncomputable section
open scoped NumberField Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory NumberField.InfinitePlace

local instance tilingInfiniteMeasurable (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (InfiniteAdeleRing F) := borel _

attribute [local instance] quotientProbability_finiteMeasurable
  quotientProbability_adeleMeasurable quotientProbability_quotientMeasurable

 def tilingMixedHomeo (F : Type) [Field F] [NumberField F] :
    InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace F => IsReal v)
    (fun v => v.Completion)).trans
    ((Homeomorph.prodCongr
      (Homeomorph.piCongrRight (fun v =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph))
      ((Homeomorph.piCongrRight (fun v =>
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          (not_isReal_iff_isComplex.mp v.2)).toHomeomorph)).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex))))))

 def tilingEquiv (F : Type) [Field F] [NumberField F] :
    mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F ≃ᵐ AdeleRing (𝓞 F) F :=
  let e : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F ≃ₜ AdeleRing (𝓞 F) F :=
    (tilingMixedHomeo F).symm.prodCongr (Homeomorph.refl _)
  e.toMeasurableEquiv

private theorem tilingEquiv_apply (F : Type) [Field F] [NumberField F]
    (x : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F) :
    tilingEquiv F x = ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x.1, x.2) := rfl

private theorem tilingEquiv_measure (F : Type) [Field F] [NumberField F]
    (μf : Measure (FiniteAdeleRing (𝓞 F) F)) :
    MeasurePreserving (tilingEquiv F) ((finiteLevelInfiniteHaar F).prod μf)
      (additiveProductHaar F μf) := ⟨(tilingEquiv F).measurable, rfl⟩

private theorem tilingEquiv_add (F : Type) [Field F] [NumberField F]
    (x y : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F) :
    tilingEquiv F (x + y) = tilingEquiv F x + tilingEquiv F y := by
  simp only [tilingEquiv_apply, Prod.fst_add, Prod.snd_add, map_add]
  rfl

theorem product_domain_tiles
    {F : Type} [Field F] [NumberField F]
    (μf : Measure (FiniteAdeleRing (𝓞 F) F)) [μf.IsAddHaarMeasure]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (D : Set (mixedEmbedding.mixedSpace F)) (hDmeas : MeasurableSet D)
    (hD : IsAddFundamentalDomain (finiteLevelLattice K).toAddSubgroup.op D
      (finiteLevelInfiniteHaar F)) :
    MeasurableSet (finiteLevelProductDomain K D) ∧
      IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F).op
        (finiteLevelProductDomain K D) (additiveProductHaar F μf) := by
  classical
  open scoped Pointwise in
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let E := mixedEmbedding.mixedSpace F
  let A := AdeleRing (𝓞 F) F
  let e := tilingEquiv F
  let ν := (finiteLevelInfiniteHaar F).prod μf
  haveI : (finiteLevelInfiniteHaar F).IsAddRightInvariant := by
    unfold finiteLevelInfiniteHaar
    infer_instance
  haveI : SFinite (finiteLevelInfiniteHaar F) := by
    unfold finiteLevelInfiniteHaar
    infer_instance
  have he := tilingEquiv_measure F μf
  have hes := (MeasurePreserving.symm e he)
  have hΩ : MeasurableSet (finiteLevelProductDomain K D) := by
    have hpre : finiteLevelProductDomain K D = e.symm ⁻¹' (D ×ˢ (K : Set _)) := by rfl
    rw [hpre]
    exact e.symm.measurable (hDmeas.prod hopen.measurableSet)
  refine ⟨hΩ, IsAddFundamentalDomain.mk'' hΩ.nullMeasurableSet ?_ ?_ ?_⟩
  · have hall : ∀ᵐ x ∂finiteLevelInfiniteHaar F, ∀ r : F,
        ∃ l : (finiteLevelLattice K).toAddSubgroup.op,
          l +ᵥ (x - mixedEmbedding F r) ∈ D := by
      apply ae_all_iff.mpr
      intro r
      exact (measurePreserving_add_right (finiteLevelInfiniteHaar F)
        (-mixedEmbedding F r)).quasiMeasurePreserving.ae hD.ae_covers
    have hprod := (Measure.quasiMeasurePreserving_fst (μ := finiteLevelInfiniteHaar F)
      (ν := μf)).ae hall
    apply e.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hprod] with x hx
    obtain ⟨r, k, hr⟩ := finiteAdele_strongApprox F K hopen hcompact x.2
    obtain ⟨l, hl⟩ := hx r
    obtain ⟨t, htK, ht⟩ := (mem_finiteLevelLattice_iff K _).mp l.property
    refine ⟨⟨AddOpposite.op (algebraMap F A (t - r)), ?_⟩, ?_⟩
    · exact ⟨t - r, rfl⟩
    · change InfiniteAdeleRing.ringEquiv_mixedSpace F
          ((e x).1 + (algebraMap F A (t - r)).1) ∈ D ∧
        (e x).2 + (algebraMap F A (t - r)).2 ∈ K
      constructor
      · change x.1 - mixedEmbedding F r + (AddOpposite.unop l : E) ∈ D at hl
        change InfiniteAdeleRing.ringEquiv_mixedSpace F
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x.1 +
            algebraMap F (InfiniteAdeleRing F) (t - r)) ∈ D
        rw [map_add, RingEquiv.apply_symm_apply,
          ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, map_sub, ht]
        simpa only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hl
      · change x.2 + algebraMap F (FiniteAdeleRing (𝓞 F) F) (t - r) ∈ K
        rw [hr, map_sub]
        convert K.add_mem k.property htK using 1 <;> abel
  · intro g hg
    obtain ⟨r, hr⟩ := g.property
    have hr0 : r ≠ 0 := by
      intro hz
      apply hg
      apply Subtype.ext
      change (g : Aᵃᵒᵖ) = 0
      apply AddOpposite.unop_injective
      simpa only [hz, map_zero, AddOpposite.unop_zero] using hr.symm
    by_cases hrK : algebraMap F (FiniteAdeleRing (𝓞 F) F) r ∈ K
    · let l : (finiteLevelLattice K).toAddSubgroup.op :=
        ⟨AddOpposite.op (mixedEmbedding F r),
          (mem_finiteLevelLattice_iff K _).mpr ⟨r, hrK, rfl⟩⟩
      have hl0 : l ≠ 0 := by
        intro hl
        apply hr0
        apply mixedEmbedding_injective
        have hh := congrArg (fun z : (finiteLevelLattice K).toAddSubgroup.op =>
          AddOpposite.unop z.val) hl
        change mixedEmbedding F r = 0 at hh
        simpa only [map_zero] using hh
      have hd : AEDisjoint (finiteLevelInfiniteHaar F) (l +ᵥ D) D := by
        simpa only [Function.onFun, zero_vadd] using hD.aedisjoint hl0
      have hn : ∀ᵐ x ∂finiteLevelInfiniteHaar F, x ∉ (l +ᵥ D) ∩ D := by
        simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hd.eq
      have hp := (Measure.quasiMeasurePreserving_fst (μ := finiteLevelInfiniteHaar F)
        (ν := μf)).ae hn
      suffices hnΩ : ∀ᵐ a ∂additiveProductHaar F μf,
          a ∉ (g +ᵥ finiteLevelProductDomain K D) ∩ finiteLevelProductDomain K D by
        simpa only [AEDisjoint, ae_iff, not_not, Set.setOf_mem_eq] using hnΩ
      apply e.measurableEmbedding.ae_map_iff.mpr
      filter_upwards [hp] with x hx
      intro hh
      obtain ⟨y, hy, hye⟩ := hh.1
      apply hx
      constructor
      · refine ⟨InfiniteAdeleRing.ringEquiv_mixedSpace F y.1, hy.1, ?_⟩
        have heq := congrArg (fun a : A => InfiniteAdeleRing.ringEquiv_mixedSpace F a.1) hye
        change InfiniteAdeleRing.ringEquiv_mixedSpace F
          (y.1 + (AddOpposite.unop g.val).1) =
          InfiniteAdeleRing.ringEquiv_mixedSpace F (e x).1 at heq
        rw [← hr] at heq
        change InfiniteAdeleRing.ringEquiv_mixedSpace F
          (y.1 + algebraMap F (InfiniteAdeleRing F) r) =
          InfiniteAdeleRing.ringEquiv_mixedSpace F
            ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x.1) at heq
        rw [RingEquiv.apply_symm_apply] at heq
        change InfiniteAdeleRing.ringEquiv_mixedSpace F y.1 + mixedEmbedding F r = x.1
        simpa only [map_add, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp] using heq
      · simpa only [e, tilingEquiv_apply, RingEquiv.apply_symm_apply] using hh.2.1
    · apply Disjoint.aedisjoint
      apply Set.disjoint_left.mpr
      intro a ha hb
      obtain ⟨y, hy, hya⟩ := ha
      apply hrK
      have heq := congrArg (fun a : A => a.2) hya
      change y.2 + (AddOpposite.unop g.val).2 = a.2 at heq
      rw [← hr] at heq
      change y.2 + algebraMap F (FiniteAdeleRing (𝓞 F) F) r = a.2 at heq
      have hm := K.sub_mem hb.2 hy.2
      rw [← heq, add_sub_cancel_left] at hm
      exact hm
  · intro g
    have hm := measurePreserving_add_right ν (e.symm (AddOpposite.unop g))
    have hc := he.comp (hm.comp hes)
    convert hc.quasiMeasurePreserving using 1
    funext x
    change x + AddOpposite.unop g = e (e.symm x + e.symm (AddOpposite.unop g))
    rw [tilingEquiv_add, e.apply_symm_apply, e.apply_symm_apply]

end
end DedekindZetaZeroFree.QuotientProbability

end

section

namespace DedekindZetaZeroFree.QuotientProbability
noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory
attribute [local instance] quotientProbability_finiteMeasurable
  quotientProbability_adeleMeasurable quotientProbability_quotientMeasurable

set_option backward.isDefEq.respectTransparency false in
 def archEquiv (F : Type) [Field F] [NumberField F] :
    InfiniteAdeleRing F ≃ₜ+ mixedEmbedding.mixedSpace F where
  toAddEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv
  continuous_toFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply v.1)
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply v.1)
  continuous_invFun := by
    apply continuous_pi
    intro v
    by_cases hv : v.IsReal
    · have he (x : mixedEmbedding.mixedSpace F) :
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x v =
            (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (x.1 ⟨v,hv⟩) := by
        apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).injective
        have hh := congrArg (fun y : mixedEmbedding.mixedSpace F => y.1 ⟨v,hv⟩)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply x)
        rw [IsometryEquiv.apply_symm_apply]
        exact hh
      convert (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
        ((continuous_apply (⟨v,hv⟩ : {w : InfinitePlace F // w.IsReal})).comp
          (continuous_fst : Continuous (Prod.fst : mixedEmbedding.mixedSpace F → _))) using 1
      funext x
      exact he x
    · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
      have he (x : mixedEmbedding.mixedSpace F) :
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x v =
            (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm (x.2 ⟨v,hv'⟩) := by
        apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').injective
        have hh := congrArg (fun y : mixedEmbedding.mixedSpace F => y.2 ⟨v,hv'⟩)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply x)
        rw [IsometryEquiv.apply_symm_apply]
        exact hh
      convert (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm.continuous.comp
        ((continuous_apply (⟨v,hv'⟩ : {w : InfinitePlace F // w.IsComplex})).comp
          (continuous_snd : Continuous (Prod.snd : mixedEmbedding.mixedSpace F → _))) using 1
      funext x
      exact he x

private theorem product_haar (F : Type) [Field F] [NumberField F]
    (μf : Measure (FiniteAdeleRing (𝓞 F) F)) [μf.IsAddHaarMeasure] :
    (additiveProductHaar F μf).IsAddHaarMeasure := by
  letI : (finiteLevelInfiniteHaar F).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul volume (ENNReal.ofReal_ne_zero_iff.mpr
      (PoissonArch.haarScalar_pos F)) ENNReal.ofReal_ne_top
  let e : (mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F) ≃ₜ+
      AdeleRing (𝓞 F) F :=
    { toAddEquiv := (archEquiv F).symm.toAddEquiv.prodCongr (AddEquiv.refl _)
      continuous_toFun := (archEquiv F).symm.continuous.prodMap continuous_id
      continuous_invFun := (archEquiv F).continuous.prodMap continuous_id }
  letI : SigmaFinite μf := inferInstance
  letI : SigmaFinite (finiteLevelInfiniteHaar F) := inferInstance
  change (Measure.map e ((finiteLevelInfiniteHaar F).prod μf)).IsAddHaarMeasure
  exact e.isAddHaarMeasure_map _

private theorem abstract_haar {G : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    [PolishSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (Γ : AddSubgroup G) [Countable Γ] [CompactSpace (G ⧸ Γ)] [T2Space (G ⧸ Γ)]
    [mQ : MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]
    (ν : Measure G) [ν.IsAddHaarMeasure]
    (Ω : Set G) (hΩ : IsAddFundamentalDomain Γ.op Ω ν) :
    (Measure.map (QuotientAddGroup.mk' Γ) (ν.restrict Ω)).IsAddHaarMeasure ∧
    ∀ Ω' : Set G, MeasurableSet Ω' → IsAddFundamentalDomain Γ.op Ω' ν →
      Measure.map (QuotientAddGroup.mk' Γ) (ν.restrict Ω) =
      Measure.map (QuotientAddGroup.mk' Γ) (ν.restrict Ω') := by
  have hm : mQ = (QuotientAddGroup.measurableSpace Γ) := by
    exact (BorelSpace.measurable_eq (α := G ⧸ Γ)).trans
      (@BorelSpace.measurable_eq _ _ (QuotientAddGroup.measurableSpace Γ)
        (AddCosetSpace.borelSpace (G := G))).symm
  cases hm
  letI : BorelSpace (G ⧸ Γ) := AddCosetSpace.borelSpace
  letI : HasAddFundamentalDomain Γ.op G ν := ⟨Ω, hΩ⟩
  let μ : Measure (G ⧸ Γ) := Measure.map (QuotientAddGroup.mk' Γ) (ν.restrict Ω)
  letI : AddQuotientMeasureEqMeasurePreimage ν μ :=
    hΩ.addQuotientMeasureEqMeasurePreimage rfl
  letI : μ.IsAddLeftInvariant :=
    AddQuotientMeasureEqMeasurePreimage.addInvariantMeasure_quotient ν
  letI : SigmaFinite μ := AddQuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient (ν := ν) μ
  have hscalar := Measure.addHaarMeasure_unique μ (⊤ : TopologicalSpace.PositiveCompacts (G ⧸ Γ))
  have hpos : μ Set.univ ≠ 0 := by
    dsimp [μ]
    rw [Measure.map_apply QuotientAddGroup.continuous_mk.measurable MeasurableSet.univ,
      Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    apply hΩ.measure_ne_zero
    intro hν
    have hp := Measure.IsOpenPosMeasure.open_pos (μ := ν) Set.univ isOpen_univ Set.univ_nonempty
    simpa [hν] using hp
  have hfin : μ Set.univ ≠ ⊤ := by
    intro ht
    obtain ⟨n, hn⟩ := (Measure.exists_measure_inter_spanningSets_pos (μ := μ) Set.univ).mpr
      (bot_lt_iff_ne_bot.mpr hpos)
    have hnfin : μ (Set.univ ∩ spanningSets μ n) < ⊤ := by
      simpa using measure_spanningSets_lt_top μ n
    have hz := congrArg (fun m : Measure (G ⧸ Γ) => m (Set.univ ∩ spanningSets μ n)) hscalar
    simp only [TopologicalSpace.PositiveCompacts.coe_top, ht, Measure.smul_apply,
      smul_eq_mul] at hz
    have hnotzero : Measure.addHaarMeasure (⊤ : TopologicalSpace.PositiveCompacts (G ⧸ Γ))
        (Set.univ ∩ spanningSets μ n) ≠ 0 := by
      intro hh
      rw [hh, mul_zero] at hz
      exact (ne_of_gt hn) hz
    rw [ENNReal.top_mul hnotzero] at hz
    exact hnfin.ne hz
  have hhaar : μ.IsAddHaarMeasure := by
    rw [hscalar]
    apply Measure.IsAddHaarMeasure.smul
    · simpa only [TopologicalSpace.PositiveCompacts.coe_top] using hpos
    · simpa only [TopologicalSpace.PositiveCompacts.coe_top] using hfin
  refine ⟨hhaar, ?_⟩
  intro Ω' _ hΩ'
  exact hΩ.addQuotientMeasure_eq ν hΩ'

theorem quotient_haar_and_domain_independence
    (F : Type) [Field F] [NumberField F]
    (μf : Measure (FiniteAdeleRing (𝓞 F) F)) [μf.IsAddHaarMeasure]
    (Ω : Set (AdeleRing (𝓞 F) F)) (hΩmeas : MeasurableSet Ω)
    (hΩ : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F).op Ω
      (additiveProductHaar F μf)) :
    (additiveQuotientMeasureFromDomain F μf Ω).IsAddHaarMeasure ∧
      ∀ Ω' : Set (AdeleRing (𝓞 F) F), MeasurableSet Ω' →
        IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F).op Ω'
          (additiveProductHaar F μf) →
        additiveQuotientMeasureFromDomain F μf Ω =
          additiveQuotientMeasureFromDomain F μf Ω' := by
  letI : (additiveProductHaar F μf).IsAddHaarMeasure := product_haar F μf
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
    have hs : Function.Surjective (fun x : F =>
        (⟨algebraMap F (AdeleRing (𝓞 F) F) x, ⟨x, rfl⟩⟩ :
          AdeleRing.principalSubgroup (𝓞 F) F)) := by
      rintro ⟨a, x, rfl⟩
      exact ⟨x,rfl⟩
    exact hs.countable
  letI := (additiveAdeleQuotient_compactHausdorff F).1
  letI := (additiveAdeleQuotient_compactHausdorff F).2
  letI : BorelSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) := ⟨rfl⟩
  letI : PolishSpace (AdeleRing (𝓞 F) F) := by
    letI := IsTopologicalAddGroup.rightUniformSpace (AdeleRing (𝓞 F) F)
    letI := isUniformAddGroup_of_addCommGroup (G := AdeleRing (𝓞 F) F)
    letI := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace (AdeleRing (𝓞 F) F)
    letI := IsUniformAddGroup.uniformity_countably_generated (α := AdeleRing (𝓞 F) F)
    infer_instance
  letI : HasAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F).op
      (AdeleRing (𝓞 F) F) (additiveProductHaar F μf) := ⟨Ω, hΩ⟩
  have hMeas : (quotientProbability_quotientMeasurable F) =
      (Quotient.instMeasurableSpace : MeasurableSpace
        (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F)) := by
    exact (@BorelSpace.measurable_eq _ _ (Quotient.instMeasurableSpace)
      (AddCosetSpace.borelSpace (G := AdeleRing (𝓞 F) F))).symm
  unfold additiveQuotientMeasureFromDomain
  exact
    abstract_haar (AdeleRing.principalSubgroup (𝓞 F) F) (additiveProductHaar F μf) Ω hΩ

end
end DedekindZetaZeroFree.QuotientProbability

end

section

namespace DedekindZetaZeroFree.QuotientProbability
noncomputable section
open scoped NumberField Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory
attribute [local instance] quotientProbability_finiteMeasurable
  quotientProbability_adeleMeasurable quotientProbability_quotientMeasurable

private lemma fd_op {A : Type*} [AddCommGroup A] [MeasurableSpace A] (L : AddSubgroup A)
    (D : Set A) (μ : Measure A) (h : IsAddFundamentalDomain L D μ) :
    IsAddFundamentalDomain L.op D μ := by
  have hv (g : L.op) (x : A) : g +ᵥ x = (L.equivOp.symm g) +ᵥ x := by
    change x + AddOpposite.unop g.val = AddOpposite.unop g.val + x
    exact add_comm _ _
  refine ⟨h.nullMeasurableSet, ?_, ?_⟩
  · filter_upwards [h.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    refine ⟨L.equivOp g, ?_⟩
    simpa only [hv, Equiv.symm_apply_apply] using hg
  · intro a b hab
    have hh := h.aedisjoint (show L.equivOp.symm a ≠ L.equivOp.symm b from
      fun he => hab (L.equivOp.symm.injective he))
    simpa only [← Set.image_vadd, hv] using hh

theorem real_domain_exists
    {F : Type} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F))) :
    ∃ D : Set (mixedEmbedding.mixedSpace F), MeasurableSet D ∧
      IsAddFundamentalDomain (finiteLevelLattice K).toAddSubgroup.op D
        (finiteLevelInfiniteHaar F) := by
  letI := finiteLevelLattice_discrete K hcompact hopen
  letI := (finiteLevelLattice_full_rank K hcompact hopen).1
  let b := Module.Free.chooseBasis ℤ (finiteLevelLattice K)
  refine ⟨ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ),
    ZSpan.fundamentalDomain_measurableSet _, ?_⟩
  exact fd_op _ _ _ (ZLattice.isAddFundamentalDomain b (finiteLevelInfiniteHaar F))

end
end DedekindZetaZeroFree.QuotientProbability

end

section

namespace DedekindZetaZeroFree.QuotientProbability
noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory
open NumberField.InfinitePlace
set_option allowUnsafeReducibility true in
attribute [local reducible] AdeleRing
attribute [local instance] quotientProbability_finiteMeasurable
  quotientProbability_adeleMeasurable quotientProbability_quotientMeasurable

end
end DedekindZetaZeroFree.QuotientProbability

end

section

namespace DedekindZetaZeroFree.QuotientProbability
noncomputable section
open scoped NumberField Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory
attribute [local instance] quotientProbability_finiteMeasurable
  quotientProbability_adeleMeasurable quotientProbability_quotientMeasurable

set_option backward.isDefEq.respectTransparency false in
 def massArchEquiv (F : Type) [Field F] [NumberField F] :
    InfiniteAdeleRing F ≃ₜ+ mixedEmbedding.mixedSpace F where
  toAddEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv
  continuous_toFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply v.1)
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply v.1)
  continuous_invFun := by
    apply continuous_pi
    intro v
    by_cases hv : v.IsReal
    · have he (x : mixedEmbedding.mixedSpace F) :
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x v =
            (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (x.1 ⟨v,hv⟩) := by
        apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).injective
        have hh := congrArg (fun y : mixedEmbedding.mixedSpace F => y.1 ⟨v,hv⟩)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply x)
        rw [IsometryEquiv.apply_symm_apply]
        exact hh
      convert (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
        ((continuous_apply (⟨v,hv⟩ : {w : InfinitePlace F // w.IsReal})).comp
          (continuous_fst : Continuous (Prod.fst : mixedEmbedding.mixedSpace F → _))) using 1
      funext x
      exact he x
    · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
      have he (x : mixedEmbedding.mixedSpace F) :
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x v =
            (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm (x.2 ⟨v,hv'⟩) := by
        apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').injective
        have hh := congrArg (fun y : mixedEmbedding.mixedSpace F => y.2 ⟨v,hv'⟩)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply x)
        rw [IsometryEquiv.apply_symm_apply]
        exact hh
      convert (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm.continuous.comp
        ((continuous_apply (⟨v,hv'⟩ : {w : InfinitePlace F // w.IsComplex})).comp
          (continuous_snd : Continuous (Prod.snd : mixedEmbedding.mixedSpace F → _))) using 1
      funext x
      exact he x

set_option backward.isDefEq.respectTransparency false in

theorem quotient_mass_eq_covolume_mul
    (F : Type) [Field F] [NumberField F]
    (μf : Measure (FiniteAdeleRing (𝓞 F) F)) [μf.IsAddHaarMeasure]
    (Ω : Set (AdeleRing (𝓞 F) F)) (hΩmeas : MeasurableSet Ω)
    (hΩ : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F).op Ω
      (additiveProductHaar F μf))
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (D : Set (mixedEmbedding.mixedSpace F)) (hDmeas : MeasurableSet D)
    (hD : IsAddFundamentalDomain (finiteLevelLattice K).toAddSubgroup.op D
      (finiteLevelInfiniteHaar F)) :
    additiveQuotientMeasureFromDomain F μf Ω Set.univ =
      ENNReal.ofReal (ZLattice.covolume (finiteLevelLattice K) (finiteLevelInfiniteHaar F) *
        μf.real (K : Set (FiniteAdeleRing (𝓞 F) F))) := by
  letI : MeasurableSpace (InfiniteAdeleRing F) := borel _
  letI : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩
  letI : MeasurableSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := borel _
  letI : BorelSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI : MeasurableSpace (Quotient (QuotientAddGroup.leftRel (AdeleRing.principalSubgroup (𝓞 F) F))) := borel _
  letI : BorelSpace (Quotient (QuotientAddGroup.leftRel (AdeleRing.principalSubgroup (𝓞 F) F))) := ⟨rfl⟩
  letI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI : BorelSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) := ⟨rfl⟩
  letI : (finiteLevelInfiniteHaar F).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul volume
      (ENNReal.ofReal_ne_zero_iff.mpr (PoissonArch.haarScalar_pos F)) ENNReal.ofReal_ne_top
  letI : DiscreteTopology (finiteLevelLattice K) := finiteLevelLattice_discrete K hcompact hopen
  letI : IsZLattice ℝ (finiteLevelLattice K) :=
    (finiteLevelLattice_full_rank K hcompact hopen).1
  have hDleft : IsAddFundamentalDomain (finiteLevelLattice K) D (finiteLevelInfiniteHaar F) := by
    refine ⟨hD.nullMeasurableSet, ?_, ?_⟩
    · filter_upwards [hD.ae_covers] with x hx
      obtain ⟨g, hg⟩ := hx
      refine ⟨⟨AddOpposite.unop g.1, g.2⟩, ?_⟩
      change AddOpposite.unop g.1 + x ∈ D
      change x + AddOpposite.unop g.1 ∈ D at hg
      simpa only [add_comm] using hg
    · intro g h hne
      have hn : (⟨AddOpposite.op g.1, g.2⟩ : (finiteLevelLattice K).toAddSubgroup.op) ≠
          ⟨AddOpposite.op h.1, h.2⟩ := by
        intro heq
        apply hne
        exact Subtype.ext (AddOpposite.op_injective (congrArg Subtype.val heq))
      have hd := hD.aedisjoint hn
      have hgset : g +ᵥ D = (⟨AddOpposite.op g.1, g.2⟩ : (finiteLevelLattice K).toAddSubgroup.op) +ᵥ D := by
        ext x
        simp only [Set.mem_vadd_set]
        constructor <;> rintro ⟨y, hy, heq⟩ <;> refine ⟨y, hy, ?_⟩
        · change y + g.1 = x
          change g.1 + y = x at heq
          simpa only [add_comm] using heq
        · change g.1 + y = x
          change y + g.1 = x at heq
          simpa only [add_comm] using heq
      have hhset : h +ᵥ D = (⟨AddOpposite.op h.1, h.2⟩ : (finiteLevelLattice K).toAddSubgroup.op) +ᵥ D := by
        ext x
        simp only [Set.mem_vadd_set]
        constructor <;> rintro ⟨y, hy, heq⟩ <;> refine ⟨y, hy, ?_⟩
        · change y + h.1 = x
          change h.1 + y = x at heq
          simpa only [add_comm] using heq
        · change h.1 + y = x
          change y + h.1 = x at heq
          simpa only [add_comm] using heq
      change AEDisjoint _ (g +ᵥ D) (h +ᵥ D)
      rw [hgset, hhset]
      exact hd
  have hcovol := ZLattice.covolume_eq_measure_fundamentalDomain
    (finiteLevelLattice K) (finiteLevelInfiniteHaar F) hDleft
  have hDfinite : (finiteLevelInfiniteHaar F) D ≠ ⊤ := by
    intro htop
    have hn := ZLattice.covolume_ne_zero (finiteLevelLattice K) (finiteLevelInfiniteHaar F)
    rw [hcovol] at hn
    exact hn (by simp [Measure.real_def, htop])
  have hKfinite : μf (K : Set (FiniteAdeleRing (𝓞 F) F)) ≠ ⊤ :=
    hcompact.measure_lt_top.ne
  obtain ⟨hPm, hP⟩ := product_domain_tiles μf K hcompact hopen D hDmeas hD
  rw [(quotient_haar_and_domain_independence F μf Ω hΩmeas hΩ).2
    (finiteLevelProductDomain K D) hPm hP]
  have hπ : Measurable (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)) :=
    (continuous_quotient_mk' : Continuous (QuotientAddGroup.mk : AdeleRing (𝓞 F) F →
      AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F)).measurable
  rw [additiveQuotientMeasureFromDomain, Measure.map_apply hπ MeasurableSet.univ]
  simp only [Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have he : Continuous (fun x : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F =>
      (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x.1, x.2) : AdeleRing (𝓞 F) F)) :=
    (massArchEquiv F).symm.continuous.prodMap continuous_id
  have hem : Measurable (fun x : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F =>
      (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x.1, x.2) : AdeleRing (𝓞 F) F)) := he.measurable
  unfold additiveProductHaar
  have hm := Measure.map_apply (μ := (finiteLevelInfiniteHaar F).prod μf) hem hPm
  change (Measure.map (fun x : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F =>
      (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x.1, x.2) : AdeleRing (𝓞 F) F))
        ((finiteLevelInfiniteHaar F).prod μf)) (finiteLevelProductDomain K D) = _
  rw [hm]
  have hpre : (fun x : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F =>
      (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x.1, x.2) : AdeleRing (𝓞 F) F)) ⁻¹'
        finiteLevelProductDomain K D = D ×ˢ (K : Set (FiniteAdeleRing (𝓞 F) F)) := by
    ext x
    change (InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x.1) ∈ D ∧ x.2 ∈ K) ↔
        (x.1 ∈ D ∧ x.2 ∈ K)
    rw [RingEquiv.apply_symm_apply]
  rw [hpre, Measure.prod_prod, hcovol, ENNReal.ofReal_mul (measureReal_nonneg)]
  rw [ofReal_measureReal hDfinite, ofReal_measureReal hKfinite]

end
end DedekindZetaZeroFree.QuotientProbability

end

section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

local instance quotientProbability_finiteMeasurable (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
local instance quotientProbability_adeleMeasurable (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
local instance quotientProbability_quotientMeasurable (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) := borel _

def finiteLevelInfiniteHaar (F : Type) [Field F] [NumberField F] :
    Measure (mixedEmbedding.mixedSpace F) :=
  ENNReal.ofReal (PoissonArch.haarScalar F) • volume

def additiveProductHaar (F : Type) [Field F] [NumberField F]
    (μf : Measure (FiniteAdeleRing (𝓞 F) F)) : Measure (AdeleRing (𝓞 F) F) :=
  Measure.map
    (fun x : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F =>
      (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x.1, x.2) :
        AdeleRing (𝓞 F) F))
    ((finiteLevelInfiniteHaar F).prod μf)

def additiveQuotientMeasureFromDomain (F : Type) [Field F] [NumberField F]
    (μf : Measure (FiniteAdeleRing (𝓞 F) F)) (Ω : Set (AdeleRing (𝓞 F) F)) :
    Measure (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) :=
  Measure.map (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F))
    ((additiveProductHaar F μf).restrict Ω)

def finiteLevelProductDomain {F : Type} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (D : Set (mixedEmbedding.mixedSpace F)) : Set (AdeleRing (𝓞 F) F) :=
  {a | InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 ∈ D ∧ a.2 ∈ K}

private theorem quotientProbability_integral_compact (F : Type) [Field F] [NumberField F] :
    IsCompact (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  let h : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ ⊤ := le_top
  letI (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (A v) :=
    Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance
  have hc : IsCompact (Set.univ : Set (Π v, A v)) := isCompact_univ
  have he := (RestrictedProduct.continuous_inclusion (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := A) h).comp
    (RestrictedProduct.homeoTop (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := A)).continuous
  have hi := hc.image he
  change IsCompact ((RestrictedProduct.inclusion (fun v => v.adicCompletion F) A h ∘
    RestrictedProduct.homeoTop) '' Set.univ) at hi
  have heq : (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) =
      (RestrictedProduct.inclusion (fun v => v.adicCompletion F) A h ∘
        RestrictedProduct.homeoTop) '' Set.univ := by
    ext x
    simp only [Set.image_univ, Set.mem_range]
    constructor
    · intro hx
      refine ⟨fun v => ⟨x v, hx v⟩, ?_⟩
      rfl
    · rintro ⟨y, rfl⟩ v
      exact (y v).property
  rw [heq]
  exact hi

private theorem quotientProbability_integral_open (F : Type) [Field F] [NumberField F] :
    IsOpen (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  exact RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set _))
    (fun v => Valued.isOpen_valuationSubring _)

theorem finiteLevel_exists_real_fundamentalDomain
    {F : Type} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F))) :
    ∃ D : Set (mixedEmbedding.mixedSpace F), MeasurableSet D ∧
      IsAddFundamentalDomain (finiteLevelLattice K).toAddSubgroup.op D
        (finiteLevelInfiniteHaar F) := by
  exact QuotientProbability.real_domain_exists K hcompact hopen

theorem finiteLevel_product_isFundamentalDomain
    {F : Type} [Field F] [NumberField F]
    (μf : Measure (FiniteAdeleRing (𝓞 F) F)) [μf.IsAddHaarMeasure]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (D : Set (mixedEmbedding.mixedSpace F)) (hDmeas : MeasurableSet D)
    (hD : IsAddFundamentalDomain (finiteLevelLattice K).toAddSubgroup.op D
      (finiteLevelInfiniteHaar F)) :
    MeasurableSet (finiteLevelProductDomain K D) ∧
      IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F).op
        (finiteLevelProductDomain K D) (additiveProductHaar F μf) := by
  exact QuotientProbability.product_domain_tiles μf K hcompact hopen D hDmeas hD

theorem additiveProductHaar_exists_fundamentalDomain
    (F : Type) [Field F] [NumberField F]
    (μf : Measure (FiniteAdeleRing (𝓞 F) F)) [μf.IsAddHaarMeasure] :
    ∃ Ω : Set (AdeleRing (𝓞 F) F), MeasurableSet Ω ∧
      IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F).op Ω
        (additiveProductHaar F μf) := by
  have hc : IsCompact (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    KPAdelicTopology.integralAdeles_isCompact F
  have ho : IsOpen (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    KPAdelicTopology.integralAdeles_isOpen F
  obtain ⟨D, hDm, hD⟩ := finiteLevel_exists_real_fundamentalDomain (integralFiniteAdeles F) hc ho
  exact ⟨finiteLevelProductDomain (integralFiniteAdeles F) D,
    finiteLevel_product_isFundamentalDomain μf (integralFiniteAdeles F) hc ho D hDm hD⟩

theorem additiveQuotientMeasureFromDomain_haar_probability
    (F : Type) [Field F] [NumberField F]
    (μf : Measure (FiniteAdeleRing (𝓞 F) F)) [μf.IsAddHaarMeasure]
    (hnorm : μf (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) =
      ENNReal.ofReal (1 / Real.sqrt |(NumberField.discr F : ℝ)|))
    (Ω : Set (AdeleRing (𝓞 F) F)) (hΩmeas : MeasurableSet Ω)
    (hΩ : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F).op Ω
      (additiveProductHaar F μf)) :
    (additiveQuotientMeasureFromDomain F μf Ω).IsAddHaarMeasure ∧
      IsProbabilityMeasure (additiveQuotientMeasureFromDomain F μf Ω) ∧
      additiveQuotientMeasureFromDomain F μf Ω Set.univ = 1 := by
  have hc := quotientProbability_integral_compact F
  have ho := quotientProbability_integral_open F
  obtain ⟨D, hDm, hD⟩ := finiteLevel_exists_real_fundamentalDomain
    (integralFiniteAdeles F) hc ho
  have hmass := QuotientProbability.quotient_mass_eq_covolume_mul
    F μf Ω hΩmeas hΩ (integralFiniteAdeles F) hc ho D hDm hD
  have hcancel := finiteLevel_covolume_mul_finiteHaar F μf hnorm
    (integralFiniteAdeles F) hc ho
  change ZLattice.covolume (finiteLevelLattice (integralFiniteAdeles F))
    (finiteLevelInfiniteHaar F) * μf.real (integralFiniteAdeles F : Set _) = 1 at hcancel
  change additiveQuotientMeasureFromDomain F μf Ω Set.univ =
    ENNReal.ofReal (ZLattice.covolume (finiteLevelLattice (integralFiniteAdeles F))
      (finiteLevelInfiniteHaar F) * μf.real (integralFiniteAdeles F : Set _)) at hmass
  rw [hcancel, ENNReal.ofReal_one] at hmass
  exact ⟨(QuotientProbability.quotient_haar_and_domain_independence
    F μf Ω hΩmeas hΩ).1, ⟨hmass⟩, hmass⟩

end
end DedekindZetaZeroFree

end

section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

attribute [local instance] quotientProbability_finiteMeasurable
  quotientProbability_adeleMeasurable quotientProbability_quotientMeasurable

set_option backward.isDefEq.respectTransparency false in
private def archEquiv (F : Type) [Field F] [NumberField F] :
    InfiniteAdeleRing F ≃ₜ+ mixedEmbedding.mixedSpace F where
  toAddEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv
  continuous_toFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply v.1)
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply v.1)
  continuous_invFun := by
    apply continuous_pi
    intro v
    by_cases hv : v.IsReal
    · have he (x : mixedEmbedding.mixedSpace F) :
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x v =
            (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (x.1 ⟨v,hv⟩) := by
        apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).injective
        have hh := congrArg (fun y : mixedEmbedding.mixedSpace F => y.1 ⟨v,hv⟩)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply x)
        rw [IsometryEquiv.apply_symm_apply]
        exact hh
      convert (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
        ((continuous_apply (⟨v,hv⟩ : {w : InfinitePlace F // w.IsReal})).comp
          (continuous_fst : Continuous (Prod.fst : mixedEmbedding.mixedSpace F → _))) using 1
      funext x
      exact he x
    · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
      have he (x : mixedEmbedding.mixedSpace F) :
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x v =
            (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm (x.2 ⟨v,hv'⟩) := by
        apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').injective
        have hh := congrArg (fun y : mixedEmbedding.mixedSpace F => y.2 ⟨v,hv'⟩)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply x)
        rw [IsometryEquiv.apply_symm_apply]
        exact hh
      convert (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm.continuous.comp
        ((continuous_apply (⟨v,hv'⟩ : {w : InfinitePlace F // w.IsComplex})).comp
          (continuous_snd : Continuous (Prod.snd : mixedEmbedding.mixedSpace F → _))) using 1
      funext x
      exact he x

theorem finiteLevel_torus_exists_haar_probability
    {F : Type} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F))) :
    ∃ ν : Measure (mixedEmbedding.mixedSpace F ⧸
        (finiteLevelLattice K).toAddSubgroup),
      ν.IsAddHaarMeasure ∧ IsProbabilityMeasure ν := by
  letI := finiteLevelLattice_discrete K hcompact hopen
  letI := (finiteLevelLattice_full_rank K hcompact hopen).1
  let L := (finiteLevelLattice K).toAddSubgroup
  have hcomp : CompactSpace (mixedEmbedding.mixedSpace F ⧸ L) := by
    apply isCompact_univ_iff.mp
    have hp := IsZLattice.isCompact_range_of_periodic (finiteLevelLattice K)
      (QuotientAddGroup.mk : mixedEmbedding.mixedSpace F → mixedEmbedding.mixedSpace F ⧸ L)
      QuotientAddGroup.continuous_mk (by
        intro z w hw
        rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero])
    simpa only [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] using hp
  letI := hcomp
  letI : DiscreteTopology L := inferInstanceAs (DiscreteTopology (finiteLevelLattice K))
  letI : IsClosed (L : Set (mixedEmbedding.mixedSpace F)) :=
    AddSubgroup.isClosed_of_discrete
  letI : BorelSpace (mixedEmbedding.mixedSpace F ⧸ L) := AddCosetSpace.borelSpace
  let ν : Measure (mixedEmbedding.mixedSpace F ⧸ L) :=
    Measure.addHaarMeasure (⊤ : PositiveCompacts (mixedEmbedding.mixedSpace F ⧸ L))
  refine ⟨ν, inferInstance, ?_⟩
  exact ⟨by simpa only [ν, PositiveCompacts.coe_top] using
    (Measure.addHaarMeasure_self (K₀ := (⊤ : PositiveCompacts (mixedEmbedding.mixedSpace F ⧸ L))))⟩

theorem finiteLevel_quotient_integral_torus_probability
    (F : Type) [Field F] [NumberField F]
    (μf : Measure (FiniteAdeleRing (𝓞 F) F)) [μf.IsAddHaarMeasure]
    (hnorm : μf (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) =
      ENNReal.ofReal (1 / Real.sqrt |(NumberField.discr F : ℝ)|))
    (Ω : Set (AdeleRing (𝓞 F) F)) (hΩmeas : MeasurableSet Ω)
    (hΩ : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F).op Ω
      (additiveProductHaar F μf))
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (g : (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) → ℂ)
    (hg : Continuous g)
    (hinv : ∀ q h, h ∈ finiteLevelImage K → g (q + h) = g q) :
    ∃ gK : (mixedEmbedding.mixedSpace F ⧸ (finiteLevelLattice K).toAddSubgroup) → ℂ,
      Continuous gK ∧
      (∀ x : mixedEmbedding.mixedSpace F,
        gK (QuotientAddGroup.mk x) =
          g ((QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F))
            (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x, 0) :
              AdeleRing (𝓞 F) F))) ∧
      ∀ ν : Measure (mixedEmbedding.mixedSpace F ⧸
          (finiteLevelLattice K).toAddSubgroup),
        ν.IsAddHaarMeasure → IsProbabilityMeasure ν →
          ∫ q, g q ∂(additiveQuotientMeasureFromDomain F μf Ω) = ∫ t, gK t ∂ν := by
  let Q := AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F
  let T := mixedEmbedding.mixedSpace F ⧸ (finiteLevelLattice K).toAddSubgroup
  let R := finiteLevelAdditiveQuotient K
  letI : MeasurableSpace R := borel _
  letI : BorelSpace R := ⟨rfl⟩
  letI : BorelSpace Q := ⟨rfl⟩
  letI : CompactSpace Q := (additiveAdeleQuotient_compactHausdorff F).1
  letI : T2Space Q := (additiveAdeleQuotient_compactHausdorff F).2
  letI := finiteLevelLattice_discrete K hcompact hopen
  letI := (finiteLevelLattice_full_rank K hcompact hopen).1
  let L := (finiteLevelLattice K).toAddSubgroup
  letI : DiscreteTopology L := inferInstanceAs (DiscreteTopology (finiteLevelLattice K))
  letI : IsClosed (L : Set (mixedEmbedding.mixedSpace F)) := AddSubgroup.isClosed_of_discrete
  letI : BorelSpace T := AddCosetSpace.borelSpace
  obtain ⟨e, he⟩ := finiteLevel_torus_homeomorph K hcompact hopen
  let gg : R → ℂ := Quotient.lift g (by
    intro a b hab
    have hab' : -a + b ∈ finiteLevelImage K := QuotientAddGroup.leftRel_apply.mp hab
    have hh := hinv a (-a + b) hab'
    simpa only [add_neg_cancel_left] using hh.symm)
  have hgg : Continuous gg := by
    apply (QuotientAddGroup.isQuotientMap_mk (finiteLevelImage K)).continuous_iff.mpr
    exact hg
  let gK : T → ℂ := gg ∘ e
  have hgK : Continuous gK := hgg.comp e.continuous
  refine ⟨gK, hgK, ?_, ?_⟩
  · intro x
    change gg (e (QuotientAddGroup.mk x)) = _
    rw [he]
    rfl
  · intro ν hν hpν
    let μQ := additiveQuotientMeasureFromDomain F μf Ω
    letI : μQ.IsAddHaarMeasure := (additiveQuotientMeasureFromDomain_haar_probability F μf hnorm Ω hΩmeas hΩ).1
    letI : IsProbabilityMeasure μQ := (additiveQuotientMeasureFromDomain_haar_probability F μf hnorm Ω hΩmeas hΩ).2.1
    let π : Q →+ R := QuotientAddGroup.mk' (finiteLevelImage K)
    have hπ : Continuous π := QuotientAddGroup.continuous_mk
    let μR := Measure.map π μQ
    letI : μR.IsAddHaarMeasure := Measure.isAddHaarMeasure_map_of_isFiniteMeasure μQ π hπ
      QuotientAddGroup.mk_surjective
    letI : IsProbabilityMeasure μR := inferInstance
    let μT := Measure.map e.symm μR
    letI : μT.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map μR
    letI : IsProbabilityMeasure μT := inferInstance
    letI := hν
    letI := hpν
    have hm : μT = ν := Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure μT ν
    rw [← hm]
    change (∫ q, g q ∂μQ) = ∫ t, gK t ∂Measure.map (e.symm : R → T) μR
    rw [integral_map (show AEMeasurable (e.symm : R → T) μR from e.symm.continuous.measurable.aemeasurable) hgK.aestronglyMeasurable]
    change (∫ q, g q ∂μQ) = ∫ r, gK (e.symm r) ∂μR
    have hfun : (fun r => gK (e.symm r)) = gg := by
      funext r
      exact congrArg gg (e.apply_symm_apply r)
    rw [hfun]
    change (∫ q, g q ∂μQ) = ∫ r, gg r ∂Measure.map π μQ
    rw [integral_map hπ.measurable.aemeasurable hgg.aestronglyMeasurable]
    rfl

end
end DedekindZetaZeroFree

end
