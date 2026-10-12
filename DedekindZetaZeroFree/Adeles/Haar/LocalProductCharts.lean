module

public import DedekindZetaZeroFree.Adeles.Haar.ReferenceMeasure

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

namespace DedekindZetaZeroFree.KPAdelicHaarLocalCharts

variable (F : Type) [Field F] [NumberField F]
variable (T : Finset (HeightOneSpectrum (𝓞 F)))

def chartSubgroup : AddSubgroup (KPAdelicTopology.FiniteAdeles F) where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 F), v ∉ T →
    a v ∈ v.adicCompletionIntegers F}
  zero_mem' := by intro v _; exact (v.adicCompletionIntegers F).zero_mem
  add_mem' := by
    intro a b ha hb v hv
    exact (v.adicCompletionIntegers F).toSubring.add_mem (ha v hv) (hb v hv)
  neg_mem' := by
    intro a ha v hv
    exact (v.adicCompletionIntegers F).toSubring.neg_mem (ha v hv)

@[simp] theorem mem_chartSubgroup (a : KPAdelicTopology.FiniteAdeles F) :
    a ∈ chartSubgroup F T ↔ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ T →
      a v ∈ v.adicCompletionIntegers F := Iff.rfl

theorem chartSubgroup_isOpen :
    IsOpen (chartSubgroup F T : Set (KPAdelicTopology.FiniteAdeles F)) := by
  exact RestrictedProduct.isOpen_forall_imp_mem
    (KPAdelicTopology.completionIntegers_isOpen F)

abbrev Head := (v : T) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F

abbrev Tail := (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ T}) →
  (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F

abbrev Coordinates := Head F T × Tail F T

instance tail_compactSpace : CompactSpace (Tail F T) := by
  letI : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ T},
      CompactSpace (v.1.adicCompletionIntegers F) := fun v =>
    isCompact_iff_compactSpace.mp (KPAdelicTopology.completionIntegers_isCompact F v)
  infer_instance

instance placesCountable : Countable (HeightOneSpectrum (𝓞 F)) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable (𝓞 F) := Function.Injective.countable RingOfIntegers.coe_injective
  letI : Countable (Ideal (𝓞 F)) := by
    have h : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (↑s : Set (𝓞 F))) :=
      fun I => IsNoetherian.noetherian I
    exact h.countable
  exact Function.Injective.countable (fun _ _ h => HeightOneSpectrum.ext h)

instance completionSecondCountable (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (v.adicCompletion F) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : SeparableSpace (v.adicCompletion F) :=
    ⟨⟨Set.range (algebraMap F (v.adicCompletion F)), Set.countable_range _,
      HeightOneSpectrum.denseRange_algebraMap F v⟩⟩
  infer_instance

instance tail_borelSpace : BorelSpace (Tail F T) := by
  infer_instance

instance tail_secondCountableTopology : SecondCountableTopology (Tail F T) := by
  infer_instance

def assemble (x : Coordinates F T) : KPAdelicTopology.FiniteAdeles F :=
  ⟨fun v => if hv : v ∈ T then x.1 ⟨v, hv⟩ else (x.2 ⟨v, hv⟩ : v.adicCompletion F),
    by
      apply Filter.eventually_cofinite.mpr
      apply T.finite_toSet.subset
      intro v hv
      by_contra h
      apply hv
      have h' : v ∉ T := h
      simp only [Set.mem_setOf_eq]
      rw [dif_neg h']
      exact (x.2 ⟨v, h'⟩).2⟩

private theorem assemble_apply (x : Coordinates F T) (v : HeightOneSpectrum (𝓞 F)) :
    assemble F T x v = if hv : v ∈ T then x.1 ⟨v, hv⟩ else
      (x.2 ⟨v, hv⟩ : v.adicCompletion F) := rfl

private theorem assemble_val_apply (x : Coordinates F T) (v : HeightOneSpectrum (𝓞 F)) :
    (assemble F T x).1 v = if hv : v ∈ T then x.1 ⟨v, hv⟩ else
      (x.2 ⟨v, hv⟩ : v.adicCompletion F) := rfl

theorem assemble_mem (x : Coordinates F T) : assemble F T x ∈ chartSubgroup F T := by
  intro v hv
  rw [assemble_apply, dif_neg hv]
  exact (x.2 ⟨v, hv⟩).2

theorem assemble_continuous : Continuous (assemble F T) := by
  let X := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v => (v.adicCompletionIntegers F : Set (X v))
  let g : Coordinates F T → RestrictedProduct X A (Filter.principal (T : Set _)ᶜ) :=
    fun x => ⟨(assemble F T x).1, assemble_mem F T x⟩
  have hg : Continuous g := by
    apply RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
    intro v
    by_cases hv : v ∈ T
    · have he : ((fun x => x v) ∘ g) = (fun x : Coordinates F T => x.1 ⟨v, hv⟩) := by
        funext x
        exact (assemble_val_apply F T x v).trans (dif_pos hv)
      rw [he]
      exact
        (show Continuous (fun x : Coordinates F T => x.1 ⟨v, hv⟩) from
          (continuous_apply _).comp continuous_fst)
    · have he : ((fun x => x v) ∘ g) = (fun x : Coordinates F T =>
          (x.2 ⟨v, hv⟩ : v.adicCompletion F)) := by
        funext x
        exact (assemble_val_apply F T x v).trans (dif_neg hv)
      rw [he]
      exact
        (show Continuous (fun x : Coordinates F T =>
            (x.2 ⟨v, hv⟩ : v.adicCompletion F)) from
          continuous_subtype_val.comp ((continuous_apply _).comp continuous_snd))
  exact (RestrictedProduct.continuous_inclusion
    (Filter.le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite)).comp hg

def chartHomeomorph : chartSubgroup F T ≃ₜ Coordinates F T where
  toFun a := (fun v => a.1 v, fun v => ⟨a.1 v, a.2 v v.2⟩)
  invFun x := ⟨assemble F T x, assemble_mem F T x⟩
  left_inv := by
    intro a
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    by_cases hv : v ∈ T <;> simp [assemble, hv]
  right_inv := by
    intro x
    apply Prod.ext
    · funext v
      change (assemble F T x).1 v.1 = _
      simp [assemble, v.2]
    · funext v
      apply Subtype.ext
      change (assemble F T x).1 v.1 = _
      simp [assemble, v.2]
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_pi fun v =>
        (RestrictedProduct.continuous_eval v.1).comp continuous_subtype_val
    · exact continuous_pi fun v =>
        ((RestrictedProduct.continuous_eval v.1).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (assemble_continuous F T).subtype_mk _

@[simp] theorem chartHomeomorph_head (a : chartSubgroup F T) (v : T) :
    (chartHomeomorph F T a).1 v = a.1 v := rfl

@[simp] theorem chartHomeomorph_tail (a : chartSubgroup F T)
    (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ T}) :
    ((chartHomeomorph F T a).2 v : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) =
      a.1 v := rfl

theorem chartHomeomorph_add (a b : chartSubgroup F T) :
    chartHomeomorph F T (a + b) = chartHomeomorph F T a + chartHomeomorph F T b := by
  apply Prod.ext
  · funext v; rfl
  · funext v; rfl

def tailPositiveCompacts : PositiveCompacts (Tail F T) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

def tailMeasure : Measure (Tail F T) := Measure.addHaarMeasure (tailPositiveCompacts F T)

instance tailMeasure_isProbabilityMeasure : IsProbabilityMeasure (tailMeasure F T) := by
  constructor
  exact Measure.addHaarMeasure_self (K₀ := tailPositiveCompacts F T)

instance tailMeasure_isAddHaarMeasure : (tailMeasure F T).IsAddHaarMeasure := by
  unfold tailMeasure
  infer_instance

def headMeasure : Measure (Head F T) :=
  Measure.pi (fun v : T => localNormalizedHaar F v)

def chartMeasure : Measure (Coordinates F T) :=
  (headMeasure F T).prod (tailMeasure F T)

def subgroupMeasure : Measure (chartSubgroup F T) :=
  Measure.comap Subtype.val (KPAdelicHaarReference.finiteMeasure F)

instance finiteAdeles_measurableAdd : MeasurableAdd (KPAdelicTopology.FiniteAdeles F) :=
  ContinuousAdd.measurableAdd

instance subgroupMeasure_isAddHaarMeasure : (subgroupMeasure F T).IsAddHaarMeasure := by
  exact Measure.IsAddHaarMeasure.comap (KPAdelicHaarReference.finiteMeasure F)
    (mH := finiteAdeles_measurableAdd F) (f := (chartSubgroup F T).subtype) (chartSubgroup_isOpen F T).isOpenEmbedding_subtypeVal

def chartAddEquiv : chartSubgroup F T ≃+ Coordinates F T where
  __ := (chartHomeomorph F T).toEquiv
  map_add' := chartHomeomorph_add F T

instance transported_isAddHaarMeasure :
    (Measure.map (chartHomeomorph F T) (subgroupMeasure F T)).IsAddHaarMeasure := by
  exact (chartAddEquiv F T).isAddHaarMeasure_map (subgroupMeasure F T)
    (chartHomeomorph F T).continuous (chartHomeomorph F T).symm.continuous

instance chartMeasure_isAddHaarMeasure : (chartMeasure F T).IsAddHaarMeasure := by
  unfold chartMeasure headMeasure
  infer_instance

def integerMeasure (v : HeightOneSpectrum (𝓞 F)) :
    Measure (v.adicCompletionIntegers F) := Measure.comap Subtype.val (localNormalizedHaar F v)

instance integerMeasure_isAddHaarMeasure (v : HeightOneSpectrum (𝓞 F)) :
    (integerMeasure F v).IsAddHaarMeasure := by
  exact Measure.IsAddHaarMeasure.comap (localNormalizedHaar F v)
    (mH := inferInstance) (f := (v.adicCompletionIntegers F).toAddSubgroup.subtype)
    (KPAdelicTopology.completionIntegers_isOpen F v).isOpenEmbedding_subtypeVal

instance coordinates_locallyCompactSpace : LocallyCompactSpace (Coordinates F T) := by
  infer_instance

instance chartMeasure_sigmaFinite : SigmaFinite (chartMeasure F T) := by
  unfold chartMeasure headMeasure
  infer_instance

end DedekindZetaZeroFree.KPAdelicHaarLocalCharts

end

section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

namespace DedekindZetaZeroFree.KPAdelicHaarLocalCharts

variable (F : Type) [Field F] [NumberField F]
variable (T : Finset (HeightOneSpectrum (𝓞 F)))

def tailCylinder
    (U : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ T})
    (s : (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ T}) →
      Set ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F)) : Set (Tail F T) :=
  {x | ∀ v ∈ U, x v ∈ s v}

private theorem integerMeasure_apply (v : HeightOneSpectrum (𝓞 F))
    (s : Set (v.adicCompletionIntegers F)) :
    integerMeasure F v s = localNormalizedHaar F v (Subtype.val '' s) :=
  (MeasurableEmbedding.subtype_coe (KPAdelicTopology.completionIntegers_isOpen F v).measurableSet).comap_apply _ _

private theorem integerMeasure_probability
    (hT : localDifferentSupport F ⊆ (T : Set (HeightOneSpectrum (𝓞 F))))
    (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ T}) :
    IsProbabilityMeasure (integerMeasure F v) := by
  constructor
  rw [integerMeasure_apply, Set.image_univ, Subtype.range_coe]
  exact localNormalizedHaar_integerRing_of_not_mem F T hT v v.2

private def tailProjection
    (U : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ T}) :
    Tail F T →+ ((v : U) → v.1.1.adicCompletionIntegers F) where
  toFun x v := x v.1
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem tailProjection_continuous
    (U : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ T}) :
    Continuous (tailProjection F T U) := continuous_pi fun v => continuous_apply v.1

private theorem tailProjection_surjective
    (U : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ T}) :
    Function.Surjective (tailProjection F T U) := by
  intro x
  refine ⟨fun v => if hv : v ∈ U then x ⟨v, hv⟩ else 0, ?_⟩
  funext v
  exact dif_pos v.2

theorem tailMeasure_cylinder
    (hT : localDifferentSupport F ⊆ (T : Set (HeightOneSpectrum (𝓞 F))))
    (U : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ T})
    (s : (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ T}) →
      Set ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F))
    (hs : ∀ v ∈ U, MeasurableSet (s v)) :
    tailMeasure F T (tailCylinder F T U s) =
      ∏ v ∈ U, localNormalizedHaar F v
        (Subtype.val '' s v) := by
  letI : ∀ v : U, IsProbabilityMeasure (integerMeasure F v.1) :=
    fun v => integerMeasure_probability F T hT v.1
  let μ := Measure.map (tailProjection F T U) (tailMeasure F T)
  let ν := Measure.pi (fun v : U => integerMeasure F v.1)
  haveI : μ.IsAddHaarMeasure := Measure.isAddHaarMeasure_map_of_isFiniteMeasure
    (tailMeasure F T) (tailProjection F T U) (tailProjection_continuous F T U)
    (tailProjection_surjective F T U)
  haveI : IsProbabilityMeasure μ := by
    constructor
    change Measure.map (tailProjection F T U) (tailMeasure F T) Set.univ = 1
    rw [Measure.map_apply (tailProjection_continuous F T U).measurable MeasurableSet.univ]
    simp
  haveI : IsProbabilityMeasure ν := by
    constructor
    simp [ν, Measure.pi_univ]
  haveI : ν.IsAddHaarMeasure := by unfold ν; infer_instance
  letI : ∀ v : U, CompactSpace (v.1.1.adicCompletionIntegers F) := fun v =>
    isCompact_iff_compactSpace.mp (KPAdelicTopology.completionIntegers_isCompact F v)
  have he : μ = ν := Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure μ ν
  have hc : (tailProjection F T U) ⁻¹' (Set.univ.pi fun v : U => s v.1) =
      tailCylinder F T U s := by
    ext x
    simp only [tailCylinder, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
      forall_const]
    exact ⟨fun h v hv => h ⟨v, hv⟩, fun h v => h v.1 v.2⟩
  rw [← hc, ← Measure.map_apply (tailProjection_continuous F T U).measurable
    (MeasurableSet.univ_pi fun v : U => hs v.1 v.2)]
  change μ _ = _
  rw [he, Measure.pi_pi]
  simp only [integerMeasure_apply]
  exact Finset.prod_coe_sort U (fun v => localNormalizedHaar F v (Subtype.val '' s v))

private def normSet : Set (Coordinates F T) :=
  (Set.univ.pi fun v : T => (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))) ×ˢ
    Set.univ

private theorem normSet_measurable : MeasurableSet (normSet F T) := by
  unfold normSet
  exact (MeasurableSet.univ_pi fun v : T =>
    (KPAdelicTopology.completionIntegers_isOpen F v).measurableSet).prod MeasurableSet.univ

private theorem normSet_chart_mass
    (hT : localDifferentSupport F ⊆ (T : Set (HeightOneSpectrum (𝓞 F)))) :
    chartMeasure F T (normSet F T) = ENNReal.ofReal (KPAdelicHaarReference.referenceMass F) := by
  rw [chartMeasure, normSet, Measure.prod_prod, measure_univ, mul_one,
    headMeasure, Measure.pi_pi]
  simp only [localNormalizedHaar_integerRing]
  rw [KPAdelicHaarReference.referenceMass_eq_prod F T hT, ENNReal.ofReal_prod_of_nonneg]
  · exact Finset.prod_coe_sort T (fun v => ENNReal.ofReal (localHalfDifferentFactor F v))
  · intro v hv
    exact (localHalfDifferentFactor_pos F v).le

private theorem normSet_inverse_image :
    Subtype.val '' ((chartHomeomorph F T) ⁻¹' normSet F T) =
      (KPAdelicTopology.integralAdeles F : Set _) := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    intro v
    by_cases hv : v ∈ T
    · exact hb.1 ⟨v, hv⟩ (Set.mem_univ _)
    · exact b.2 v hv
  · intro ha
    have hb : a ∈ chartSubgroup F T := fun v _ => ha v
    refine ⟨⟨a, hb⟩, ?_, rfl⟩
    exact ⟨fun v _ => ha v, Set.mem_univ _⟩

private theorem normSet_transported_mass :
    Measure.map (chartHomeomorph F T) (subgroupMeasure F T) (normSet F T) =
      ENNReal.ofReal (KPAdelicHaarReference.referenceMass F) := by
  rw [Measure.map_apply (chartHomeomorph F T).measurable (normSet_measurable F T),
    subgroupMeasure]
  exact ((MeasurableEmbedding.subtype_coe (chartSubgroup_isOpen F T).measurableSet).comap_apply
      (KPAdelicHaarReference.finiteMeasure F) ((chartHomeomorph F T) ⁻¹' normSet F T)).trans
    (by rw [normSet_inverse_image, KPAdelicHaarReference.finiteMeasure_integralAdeles])

theorem map_subgroupMeasure
    (hT : localDifferentSupport F ⊆ (T : Set (HeightOneSpectrum (𝓞 F)))) :
    Measure.map (chartHomeomorph F T) (subgroupMeasure F T) = chartMeasure F T := by
  let μ := Measure.map (chartHomeomorph F T) (subgroupMeasure F T)
  have h := Measure.isAddLeftInvariant_eq_smul μ (chartMeasure F T)
  have hh := congrArg (fun ν : Measure (Coordinates F T) => ν (normSet F T)) h
  rw [normSet_transported_mass, Measure.smul_apply, normSet_chart_mass F T hT,
    ENNReal.smul_def, smul_eq_mul] at hh
  have hc : Measure.addHaarScalarFactor μ (chartMeasure F T) = 1 := by
    apply ENNReal.coe_eq_one.mp
    apply (ENNReal.mul_eq_left
      (ne_of_gt (ENNReal.ofReal_pos.mpr (KPAdelicHaarReference.referenceMass_pos F)))
      (ne_of_lt (KPAdelicHaarReference.referenceMass_ofReal_lt_top F))).mp
    simpa only [mul_comm] using hh.symm
  simpa [hc] using h

theorem map_chartMeasure
    (hT : localDifferentSupport F ⊆ (T : Set (HeightOneSpectrum (𝓞 F)))) :
    Measure.map (assemble F T) (chartMeasure F T) =
      (KPAdelicHaarReference.finiteMeasure F).restrict
        (chartSubgroup F T : Set (KPAdelicTopology.FiniteAdeles F)) := by
  rw [← map_subgroupMeasure F T hT, Measure.map_map (assemble_continuous F T).measurable
    (chartHomeomorph F T).measurable]
  have he : assemble F T ∘ chartHomeomorph F T = Subtype.val := by
    funext a
    exact congrArg Subtype.val ((chartHomeomorph F T).symm_apply_apply a)
  rw [he, subgroupMeasure]
  exact map_comap_subtype_coe (chartSubgroup_isOpen F T).measurableSet _

end DedekindZetaZeroFree.KPAdelicHaarLocalCharts

end
end
