module

public import DedekindZetaZeroFree.Adeles.Haar.LocalProductCharts
public import DedekindZetaZeroFree.Arithmetic.LocalFields.DifferentDiscriminantNormalization
public import DedekindZetaZeroFree.Arithmetic.LocalFields.CompletionDifferentExponent

@[expose] public section

noncomputable section
open scoped NumberField Classical ENNReal
open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

namespace DedekindZetaZeroFree.KPAdditiveHaar

variable (F : Type) [Field F] [NumberField F]

local instance archMeasurable : MeasurableSpace (InfiniteAdeleRing F) := borel _
local instance archBorel : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩

def integralPositiveCompacts : PositiveCompacts (FiniteAdeleRing (𝓞 F) F) :=
  ⟨⟨(KPAdelicTopology.integralAdeles F : Set _),
    KPAdelicTopology.integralAdeles_isCompact F⟩, by
    rw [(KPAdelicTopology.integralAdeles_isOpen F).interior_eq]
    exact ⟨0, (KPAdelicTopology.integralAdeles F).zero_mem⟩⟩

def finiteMass : ℝ≥0∞ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F),
    localNormalizedHaar F v (v.adicCompletionIntegers F : Set (v.adicCompletion F))

private theorem mulSupport_localMass_subset :
    Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) =>
      localNormalizedHaar F v
        (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ⊆
      localDifferentSupport F := by
  intro v hv
  by_contra h
  exact hv (by
    have hS : localDifferentSupport F ⊆
        (((finite_localDifferentSupport F).toFinset :
          Finset (HeightOneSpectrum (𝓞 F))) : Set _) := by
      rw [Set.Finite.coe_toFinset]
    exact localNormalizedHaar_integerRing_of_not_mem F _ hS v (by
      rw [Set.Finite.mem_toFinset]; exact h))

theorem local_masses_finite_support :
    (fun v : HeightOneSpectrum (𝓞 F) =>
      localNormalizedHaar F v
        (v.adicCompletionIntegers F : Set (v.adicCompletion F))).HasFiniteMulSupport := by
  apply (finite_localDifferentSupport F).subset
  intro v hv
  by_contra h
  apply hv
  exact localNormalizedHaar_integerRing_of_not_mem F
    (finite_localDifferentSupport F).toFinset (by simp) v (by simpa using h)

theorem finiteMass_eq_discriminant :
    finiteMass F = ENNReal.ofReal (1 / Real.sqrt |(NumberField.discr F : ℝ)|) ∧
    finiteMass F = ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (-(1 : ℝ) / 2)) := by
  let S := (finite_localDifferentSupport F).toFinset
  have hS : PoissonS.ContainsDifferent F S := by
    intro v hv
    change v ∈ (finite_localDifferentSupport F).toFinset
    rw [Set.Finite.mem_toFinset]
    exact hv
  have hprod : finiteMass F = ENNReal.ofReal
      (∏ v ∈ S, localHalfDifferentFactor F v) := by
    rw [finiteMass, finprod_eq_prod_of_mulSupport_subset _ ?_]
    · simp_rw [localNormalizedHaar_integerRing]
      exact (ENNReal.ofReal_prod_of_nonneg
        (fun v _ => (localHalfDifferentFactor_pos F v).le)).symm
    · simpa [S] using mulSupport_localMass_subset F
  have hfactors : (∏ v ∈ S, localHalfDifferentFactor F v) =
      1 / Real.sqrt |(NumberField.discr F : ℝ)| := by
    rw [← Finset.prod_coe_sort]
    simp_rw [localHalfDifferentFactor_eq_inv_sqrt, localDifferentNorm, Nat.cast_pow,
      ← zpow_natCast,
      ← FiniteOscillatoryStabilization.globalDifferentExponent_eq_localDifferentExponent,
      one_div]
    rw [Finset.prod_inv_distrib,
      PoissonS.BallMeasureBalance.prod_sqrt_absNorm_pow_differentExponent F S hS]
  have hfirst := hprod.trans (congrArg ENNReal.ofReal hfactors)
  refine ⟨hfirst, ?_⟩
  rw [hfirst, show (-(1 : ℝ) / 2) = -(1 / 2) by ring,
    Real.rpow_neg (abs_nonneg _)]
  simp [Real.sqrt_eq_rpow, one_div]

def finiteMeasure : Measure (FiniteAdeleRing (𝓞 F) F) :=
  finiteMass F • Measure.addHaarMeasure (integralPositiveCompacts F)

theorem finiteMeasure_isAddHaarMeasure : (finiteMeasure F).IsAddHaarMeasure := by
  unfold finiteMeasure
  apply Measure.IsAddHaarMeasure.smul
  · apply finprod_ne_zero
    intro v
    rw [localNormalizedHaar_integerRing]
    exact (ENNReal.ofReal_pos.mpr (localHalfDifferentFactor_pos F v)).ne'
  · unfold finiteMass
    rw [finprod_eq_prod _ (local_masses_finite_support F)]
    apply ENNReal.prod_ne_top
    intro v hv
    rw [localNormalizedHaar_integerRing]
    exact ENNReal.ofReal_ne_top

theorem finiteMeasure_integral_mass :
    finiteMeasure F (KPAdelicTopology.integralAdeles F : Set _) = finiteMass F := by
  change finiteMass F * Measure.addHaarMeasure (integralPositiveCompacts F)
    (integralPositiveCompacts F : Set _) = _
  rw [Measure.addHaarMeasure_self, mul_one]

def archMeasure : Measure (InfiniteAdeleRing F) :=
  Measure.map (PoissonArch.infiniteAdeleToSpace F).symm (PoissonArch.traceMeasure F)

theorem archMeasure_isAddHaarMeasure : (archMeasure F).IsAddHaarMeasure := by
  haveI : (PoissonArch.traceMeasure F).IsAddHaarMeasure := by
    unfold PoissonArch.traceMeasure
    apply Measure.IsAddHaarMeasure.smul
    · exact (ENNReal.ofReal_pos.mpr (PoissonArch.haarScalar_pos F)).ne'
    · exact ENNReal.ofReal_ne_top
  exact (PoissonArch.infiniteAdeleToSpace F).symm.toContinuousAddEquiv.isAddHaarMeasure_map _

def adelicMeasure : Measure (AdeleRing (𝓞 F) F) :=
  Measure.map
    (fun x : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F =>
      (x : AdeleRing (𝓞 F) F))
    ((archMeasure F).prod (finiteMeasure F))

theorem adelicMeasure_isAddHaarMeasure : (adelicMeasure F).IsAddHaarMeasure := by
  letI := archMeasure_isAddHaarMeasure F
  letI := finiteMeasure_isAddHaarMeasure F
  letI : SigmaCompactSpace (InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  let e : (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) ≃+ AdeleRing (𝓞 F) F :=
    AddEquiv.refl _
  exact e.isAddHaarMeasure_map _ continuous_id continuous_id

end DedekindZetaZeroFree.KPAdditiveHaar

end

section

noncomputable section
open scoped NumberField Classical ENNReal
open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

namespace DedekindZetaZeroFree.KPAdditiveHaar

variable (F : Type) [Field F] [NumberField F]

def integerProbabilityMeasure (v : HeightOneSpectrum (𝓞 F)) :
    Measure (v.adicCompletionIntegers F) :=
  Measure.comap (fun x : v.adicCompletionIntegers F => (x : v.adicCompletion F))
    ((Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F v)).restrict
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)))

set_option backward.isDefEq.respectTransparency false in
theorem integerProbabilityMeasure_isProbabilityMeasure (v : HeightOneSpectrum (𝓞 F)) :
    IsProbabilityMeasure (integerProbabilityMeasure F v) := by
  have he : MeasurableEmbedding (fun x : v.adicCompletionIntegers F => (x : v.adicCompletion F)) :=
    (KPAdelicTopology.completionIntegers_isOpen F v).isOpenEmbedding_subtypeVal.measurableEmbedding
  apply isProbabilityMeasure_iff.mpr
  unfold integerProbabilityMeasure
  rw [he.comap_apply]
  have hr : Set.range (fun x : v.adicCompletionIntegers F => (x : v.adicCompletion F)) =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [Set.image_univ, hr, Measure.restrict_apply_self]
  exact Measure.addHaarMeasure_self

 theorem localNormalizedHaar_eq_addHaar_of_not_mem
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ localDifferentSupport F) :
    localNormalizedHaar F v =
      Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F v) := by
  have hS : localDifferentSupport F ⊆
      (((finite_localDifferentSupport F).toFinset :
        Finset (HeightOneSpectrum (𝓞 F))) : Set _) := by
    rw [Set.Finite.coe_toFinset]
  have hv' : v ∉ (finite_localDifferentSupport F).toFinset := by
    rw [Set.Finite.mem_toFinset]; exact hv
  have hzero : localHalfDifferentFactor F v = 1 := by
    rw [localHalfDifferentFactor,
      localDifferentExponent_eq_zero_of_not_mem F _ hS v hv']
    simp
  rw [localNormalizedHaar, hzero, ENNReal.ofReal_one, one_smul]

theorem integerProbabilityMeasure_eq_local (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ localDifferentSupport F) :
    integerProbabilityMeasure F v =
      Measure.comap (fun x : v.adicCompletionIntegers F => (x : v.adicCompletion F))
        ((localNormalizedHaar F v).restrict
          (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  unfold integerProbabilityMeasure localNormalizedHaar
  have he : localDifferentExponent F v = 0 :=
    localDifferentExponent_eq_zero_of_not_mem F
      (finite_localDifferentSupport F).toFinset (by simp) v (by simpa using hv)
  simp [localHalfDifferentFactor, he]

abbrev Chart (T : Finset (HeightOneSpectrum (𝓞 F))) :=
  ((v : T) → v.val.adicCompletion F) ×
    ((v : {v : HeightOneSpectrum (𝓞 F) // v ∉ T}) → v.val.adicCompletionIntegers F)

def chartMap (T : Finset (HeightOneSpectrum (𝓞 F)))
    (x : Chart F T) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if hv : v ∈ T then x.1 ⟨v, hv⟩ else (x.2 ⟨v, hv⟩ : v.adicCompletion F), by
    apply Filter.eventually_cofinite.mpr
    apply T.finite_toSet.subset
    intro v hv
    by_contra h
    have h' : v ∉ T := h
    apply hv
    change (if hv : v ∈ T then _ else _) ∈ _
    rw [dif_neg h']
    exact (x.2 ⟨v, h'⟩).property⟩

theorem chartMap_range (T : Finset (HeightOneSpectrum (𝓞 F))) :
    Set.range (chartMap F T) =
      {a : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ T → a v ∈ v.adicCompletionIntegers F} := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩ v hv
    change (if hv : v ∈ T then _ else _) ∈ _
    rw [dif_neg hv]
    exact (x.2 ⟨v, hv⟩).property
  · intro ha
    refine ⟨⟨fun v => a v.val, fun v => ⟨a v.val, ha v.val v.property⟩⟩, ?_⟩
    apply Subtype.ext
    funext v
    simp only [chartMap]
    split <;> rfl

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem chartMap_isOpenEmbedding (T : Finset (HeightOneSpectrum (𝓞 F))) :
    Topology.IsOpenEmbedding (chartMap F T) := by
  let X := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let C := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (X v))
  let e : Chart F T ≃ₜ RestrictedProduct X C (Filter.principal ((↑T : Set (HeightOneSpectrum (𝓞 F)))ᶜ)) :=
    { toFun := fun (x : Chart F T) => ⟨fun v => if hv : v ∈ T then x.1 ⟨v, hv⟩ else (x.2 ⟨v, hv⟩ : v.adicCompletion F), by
        apply Filter.eventually_principal.mpr
        intro v hv
        have hv' : v ∉ T := hv
        dsimp only
        rw [dif_neg hv']
        exact (x.2 ⟨v, hv'⟩).property⟩
      invFun := fun (a : RestrictedProduct X C (Filter.principal ((↑T : Set (HeightOneSpectrum (𝓞 F)))ᶜ))) => ⟨fun v => a v.val, fun v => ⟨a v.val, (Filter.eventually_principal.mp a.property) v.val v.property⟩⟩
      left_inv := fun x => by
        apply Prod.ext
        · funext v
          dsimp only [RestrictedProduct.instDFunLike, DFunLike.coe]
          simp [v.property]
        · funext v
          apply Subtype.ext
          dsimp only [RestrictedProduct.instDFunLike, DFunLike.coe]
          simp [v.property]
      right_inv := fun a => by
        apply Subtype.ext
        funext v
        dsimp
        split <;> rfl
      continuous_toFun := by
        apply RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
        intro v
        dsimp only [Function.comp_def, RestrictedProduct.instDFunLike, DFunLike.coe]
        by_cases hv : v ∈ T
        · simp only [dif_pos hv]
          exact
            (continuous_apply (⟨v, hv⟩ : T)).comp continuous_fst
        · simp only [dif_neg hv]
          exact
            (show Continuous (fun x : v.adicCompletionIntegers F => (x : v.adicCompletion F)) from
              continuous_subtype_val).comp ((continuous_apply
              (⟨v, hv⟩ : {v : HeightOneSpectrum (𝓞 F) // v ∉ T})).comp continuous_snd)
      continuous_invFun := by
        apply Continuous.prodMk
        · exact continuous_pi fun v => RestrictedProduct.continuous_eval v.val
        · exact continuous_pi fun v =>
            (RestrictedProduct.continuous_eval v.val).subtype_mk _ }
  have hT : Filter.cofinite ≤ Filter.principal ((↑T : Set (HeightOneSpectrum (𝓞 F)))ᶜ) :=
    Filter.le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite
  have hi := RestrictedProduct.isOpenEmbedding_inclusion_principal
    (KPAdelicTopology.completionIntegers_isOpen F) hT
  exact hi.comp e.isOpenEmbedding

def chartMeasure (T : Finset (HeightOneSpectrum (𝓞 F))) : Measure (Chart F T) :=
  (Measure.pi (fun v : T => localNormalizedHaar F v.val)).prod
    (Measure.infinitePi (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ T} =>
      integerProbabilityMeasure F v.val))

private theorem finiteMeasure_eq_reference :
    finiteMeasure F = KPAdelicHaarReference.finiteMeasure F := by
  have hm : finiteMass F = ENNReal.ofReal (KPAdelicHaarReference.referenceMass F) := by
    let S := (finite_localDifferentSupport F).toFinset
    rw [KPAdelicHaarReference.referenceMass_eq_prod F S (by simp [S])]
    rw [finiteMass, finprod_eq_prod_of_mulSupport_subset _ ?_]
    · simp_rw [localNormalizedHaar_integerRing]
      exact (ENNReal.ofReal_prod_of_nonneg
        (fun v _ => (localHalfDifferentFactor_pos F v).le)).symm
    · simpa [S] using mulSupport_localMass_subset F
  unfold finiteMeasure KPAdelicHaarReference.finiteMeasure
  rw [hm]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem integerProbabilityMeasure_apply_local (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ localDifferentSupport F) (s : Set (v.adicCompletionIntegers F)) :
    integerProbabilityMeasure F v s = localNormalizedHaar F v (Subtype.val '' s) := by
  have he : MeasurableEmbedding (fun x : v.adicCompletionIntegers F => (x : v.adicCompletion F)) :=
    (KPAdelicTopology.completionIntegers_isOpen F v).isOpenEmbedding_subtypeVal.measurableEmbedding
  rw [integerProbabilityMeasure_eq_local F v hv, he.comap_restrict]
  have hp : (fun x : v.adicCompletionIntegers F => (x : v.adicCompletion F)) ⁻¹'
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact x.property
  rw [hp, Measure.restrict_univ, he.comap_apply]

private theorem chartMeasure_eq_reference (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : localDifferentSupport F ⊆ (T : Set (HeightOneSpectrum (𝓞 F)))) :
    chartMeasure F T = KPAdelicHaarLocalCharts.chartMeasure F T := by
  letI : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ T},
      IsProbabilityMeasure (integerProbabilityMeasure F v.val) :=
    fun v => integerProbabilityMeasure_isProbabilityMeasure F v.val
  have ht : KPAdelicHaarLocalCharts.tailMeasure F T =
      Measure.infinitePi (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ T} =>
        integerProbabilityMeasure F v.val) := by
    apply Measure.eq_infinitePi
    intro U s hs
    have hh := KPAdelicHaarLocalCharts.tailMeasure_cylinder F T hT U s (fun v _ => hs v)
    change KPAdelicHaarLocalCharts.tailMeasure F T (Set.pi (U : Set _) s) = _
    rw [show Set.pi (U : Set _) s =
      KPAdelicHaarLocalCharts.tailCylinder F T U s from rfl, hh]
    apply Finset.prod_congr rfl
    intro v hv
    exact (integerProbabilityMeasure_apply_local F v.val
      (fun h => v.property (hT h)) (s v)).symm
  unfold chartMeasure KPAdelicHaarLocalCharts.chartMeasure KPAdelicHaarLocalCharts.headMeasure
  rw [ht]

theorem finiteMeasure_chart (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : localDifferentSupport F ⊆ (T : Set (HeightOneSpectrum (𝓞 F)))) :
    (finiteMeasure F).restrict (Set.range (chartMap F T)) =
      Measure.map (chartMap F T) (chartMeasure F T) := by
  rw [finiteMeasure_eq_reference, chartMeasure_eq_reference F T hT]
  have he : chartMap F T = KPAdelicHaarLocalCharts.assemble F T := rfl
  rw [he, KPAdelicHaarLocalCharts.map_chartMeasure F T hT]
  congr 1
  rw [← he, chartMap_range]
  rfl

end DedekindZetaZeroFree.KPAdditiveHaar

end
end
