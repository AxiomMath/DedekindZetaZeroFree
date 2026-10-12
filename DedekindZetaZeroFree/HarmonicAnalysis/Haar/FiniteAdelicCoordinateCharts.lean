module

public import DedekindZetaZeroFree.Adeles.Characters.CanonicalTraceCharacterSpecifications
public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceBaseChange.DifferentComparison
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.NormalizedFiniteAdelicMeasure

@[expose] public section

noncomputable section

open scoped NumberField BigOperators Classical WithZero
open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

namespace DedekindZetaZeroFree.FiniteHaarCharts

variable (F : Type) [Field F] [NumberField F]

abbrev Places := HeightOneSpectrum (𝓞 F)

def localMass (v : Places F) : ℝ :=
  (localNormalizedHaar F v
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))).toReal

 def ringEquiv (v : Places F) :
    (TraceBaseChange.targetRaw F v).valuationSubring ≃+* Valued.integer (v.adicCompletion F) where
  toFun x := ⟨x, (Set.ext_iff.mp (LocalConductor.target_integerRing_eq F v) x).mp x.property⟩
  invFun x := ⟨x, (Set.ext_iff.mp (LocalConductor.target_integerRing_eq F v) x).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
private theorem integers (v : Places F) :
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).Integers (TraceBaseChange.targetRaw F v).valuationSubring where
  hom_inj := Subtype.val_injective
  map_le_one x := (ringEquiv F v x).property
  exists_of_le_one {x} hx := ⟨(ringEquiv F v).symm ⟨x,hx⟩,rfl⟩
private theorem val_integerMap (v : Places F) (x : 𝓞 F) :
    Valued.v (TraceBaseChange.integerMap F v x : v.adicCompletion F) = v.intValuation x := by
  change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) x) = _
  exact (v.valuedAdicCompletion_eq_valuation (K := F) x).trans (v.valuation_of_algebraMap (K := F) x)
private theorem integerMap_irreducible (v : Places F) (x : 𝓞 F)
    (hx : v.intValuation x = WithZero.exp (-1)) :
    Irreducible (TraceBaseChange.integerMap F v x) := by
  letI := (TraceBaseChange.targetRaw F v).valuationSubring_isDiscreteValuationRing
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
  · intro h
    have hv := val_integerMap F v x
    rw [h] at hv
    change Valued.v (0 : v.adicCompletion F) = _ at hv
    rw [map_zero, hx] at hv
    exact WithZero.exp_ne_zero hv.symm
  · ext a
    rw [← SetLike.mem_coe (p := Ideal.span {TraceBaseChange.integerMap F v x}),
      Valuation.Integers.coe_span_singleton_eq_setOfPred_le_v_algebraMap (integers F v)]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, (integers F v).isUnit_iff_valuation_eq_one]
    change Valued.v (a : v.adicCompletion F) ≠ 1 ↔ Valued.v (a : v.adicCompletion F) ≤ Valued.v (TraceBaseChange.integerMap F v x : v.adicCompletion F)
    rw [val_integerMap F v x, hx]
    have ha : Valued.v (a : v.adicCompletion F) ≤ 1 := (integers F v).map_le_one a
    generalize Valued.v (a : v.adicCompletion F) = g at *
    induction g using WithZero.expRecOn with
    | zero => simp
    | exp i =>
      have hi : i ≤ 0 := by simpa using ha
      have hh : WithZero.exp i ≠ 1 ↔ i < 0 := by
        rw [ne_iff_lt_iff_le.mpr ha]
        simp
      rw [hh, WithZero.exp_le_exp]
      omega
private theorem map_prime (v : Places F) :
    Ideal.map (TraceBaseChange.integerMap F v) v.asIdeal =
      IsLocalRing.maximalIdeal (TraceBaseChange.targetRaw F v).valuationSubring := by
  letI := (TraceBaseChange.targetRaw F v).valuationSubring_isDiscreteValuationRing
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (integers F v).isUnit_iff_valuation_eq_one]
    change Valued.v (TraceBaseChange.integerMap F v x : v.adicCompletion F) ≠ 1
    rw [val_integerMap]
    exact ne_of_lt ((v.intValuation_lt_one_iff_mem x).mpr hx)
  · obtain ⟨x, hx⟩ := v.intValuation_exists_uniformizer
    rw [(integerMap_irreducible F v x hx).maximalIdeal_eq]
    apply Ideal.span_le.mpr
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    apply Ideal.mem_map_of_mem
    apply (v.intValuation_lt_one_iff_mem x).mp
    rw [hx]
    simpa using (show (-1 : ℤ) < 0 by omega)
private theorem map_other_prime (v w : Places F) (hvw : w ≠ v) :
    Ideal.map (TraceBaseChange.integerMap F v) w.asIdeal = ⊤ := by
  have hnot : ¬ w.asIdeal ≤ v.asIdeal := by
    intro h
    apply hvw
    apply HeightOneSpectrum.ext
    exact w.isMaximal.eq_of_le v.isPrime.ne_top h
  obtain ⟨x, hxw, hxv⟩ := SetLike.not_le_iff_exists.mp hnot
  have hxunit : IsUnit (TraceBaseChange.integerMap F v x) := by
    rw [(integers F v).isUnit_iff_valuation_eq_one]
    change Valued.v (TraceBaseChange.integerMap F v x : v.adicCompletion F) = 1
    rw [val_integerMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hxv
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hxw) hxunit
private theorem map_different_pow (v : Places F) :
    Ideal.map (TraceBaseChange.integerMap F v) (differentIdeal ℤ (𝓞 F)) =
      IsLocalRing.maximalIdeal (TraceBaseChange.targetRaw F v).valuationSubring ^ DifferentMass.exponent F v := by
  let s := (DifferentMass.exponent_finite_support F).toFinset
  have hs (w : Places F) (hw : DifferentMass.exponent F w ≠ 0) : w ∈ s :=
    (DifferentMass.exponent_finite_support F).mem_toFinset.mpr hw
  have hfactor : (∏ w ∈ s, w.asIdeal ^ DifferentMass.exponent F w) = differentIdeal ℤ (𝓞 F) := by
    rw [← Ideal.finprod_heightOneSpectrum_pow_multiplicity (DifferentMass.differentIdeal_ne_bot F)]
    symm
    apply finprod_eq_prod_of_mulSupport_subset
    intro w hw
    apply hs
    intro h
    exact hw (by simp [DifferentMass.exponent] at h ⊢; simp [h])
  rw [← hfactor]
  change (Ideal.mapHom (TraceBaseChange.integerMap F v)) _ = _
  rw [map_prod]
  change (∏ w ∈ s, Ideal.map (TraceBaseChange.integerMap F v) (w.asIdeal ^ DifferentMass.exponent F w)) = _
  simp_rw [Ideal.map_pow]
  by_cases hv : v ∈ s
  · rw [Finset.prod_eq_single v]
    · rw [map_prime]
    · intro w hw hwv
      rw [map_other_prime F v w hwv]
      simp
    · exact fun h => False.elim (h hv)
  · have he : DifferentMass.exponent F v = 0 := by
      by_contra h
      exact hv (hs v h)
    rw [he, pow_zero]
    apply Finset.prod_eq_one
    intro w hw
    rw [map_other_prime F v w (fun h => hv (h ▸ hw))]
    simp
private theorem exponent_comparison (v : Places F) :
    localDifferentExponent F v = DifferentMass.exponent F v := by
  letI := (TraceBaseChange.targetRaw F v).valuationSubring_isDiscreteValuationRing
  have h := (TraceBaseChange.map_globalDifferent_eq_localDifferent F v).symm.trans (map_different_pow F v)
  change localDifferent F v = _ at h
  rw [localDifferent_eq_maximalIdeal_pow] at h
  change IsLocalRing.maximalIdeal (TraceBaseChange.targetRaw F v).valuationSubring ^ localDifferentExponent F v = _ at h
  have hh := congrArg Order.coheight h
  rw [IsDiscreteValuationRing.coheight_pow_maximalIdeal, IsDiscreteValuationRing.coheight_pow_maximalIdeal] at hh
  exact_mod_cast hh

theorem localMass_eq_halfNormMass (v : Places F) :
    localMass F v = DifferentMass.halfNormMass F v := by
  rw [localMass, localNormalizedHaar_integerRing_toReal,
    localHalfDifferentFactor_eq_inv_sqrt, localDifferentNorm,
    exponent_comparison F v, Nat.cast_pow]
  rfl

theorem localMass_eq_inv_sqrt (v : Places F) :
    localMass F v =
      1 / Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^ DifferentMass.exponent F v) := by
  exact localMass_eq_halfNormMass F v

abbrev ExceptionalProduct (S : Finset (Places F)) :=
  (v : S) → v.1.adicCompletion F

abbrev Tail (S : Finset (Places F)) :=
  (v : {v : Places F // v ∉ S}) → v.1.adicCompletionIntegers F

abbrev ChartCoordinates (S : Finset (Places F)) := ExceptionalProduct F S × Tail F S

instance tail_compactSpace (S : Finset (Places F)) : CompactSpace (Tail F S) := by
  letI : ∀ v : {v : Places F // v ∉ S}, CompactSpace (v.1.adicCompletionIntegers F) :=
    fun v => isCompact_iff_compactSpace.mp (KPAdelicTopology.completionIntegers_isCompact F v.1)
  infer_instance

def tailPositiveCompact (S : Finset (Places F)) : PositiveCompacts (Tail F S) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by
    rw [interior_univ]
    exact Set.univ_nonempty⟩

def tailProbability (S : Finset (Places F)) : Measure (Tail F S) :=
  Measure.addHaarMeasure (tailPositiveCompact F S)

instance tailProbability_isAddHaarMeasure (S : Finset (Places F)) :
    (tailProbability F S).IsAddHaarMeasure := by
  unfold tailProbability
  infer_instance

instance tailProbability_isProbabilityMeasure (S : Finset (Places F)) :
    IsProbabilityMeasure (tailProbability F S) := by
  constructor
  exact Measure.addHaarMeasure_self (K₀ := tailPositiveCompact F S)

def tailMass (S : Finset (Places F)) : ℝ :=
  ∏ᶠ v : {v : Places F // v ∉ S}, localMass F v.1

def coordinateMeasure (S : Finset (Places F)) : Measure (ChartCoordinates F S) :=
  (Measure.pi (fun v : S => localNormalizedHaar F v.1)).prod
    (ENNReal.ofReal (tailMass F S) • tailProbability F S)

def integerProbability (v : Places F) : Measure (v.adicCompletionIntegers F) :=
  ENNReal.ofReal (1 / localMass F v) •
    ((localNormalizedHaar F v).restrict (v.adicCompletionIntegers F)).comap Subtype.val

instance integerProbability_isProbabilityMeasure (v : Places F) :
    IsProbabilityMeasure (integerProbability F v) := by
  have hv : MeasurableEmbedding
      (Subtype.val : v.adicCompletionIntegers F → v.adicCompletion F) :=
    MeasurableEmbedding.subtype_coe (KPAdelicTopology.completionIntegers_isOpen F v).measurableSet
  constructor
  rw [integerProbability, Measure.smul_apply, smul_eq_mul,
    Measure.comap_apply _ hv.injective (fun _ hs => hv.measurableSet_image.mpr hs) _ MeasurableSet.univ,
    Set.image_univ, Subtype.range_coe_subtype]
  change ENNReal.ofReal (1 / localMass F v) *
    ((localNormalizedHaar F v).restrict (v.adicCompletionIntegers F))
      (v.adicCompletionIntegers F) = 1
  rw [Measure.restrict_apply (KPAdelicTopology.completionIntegers_isOpen F v).measurableSet,
    Set.inter_self, localNormalizedHaar_integerRing]
  rw [localMass, localNormalizedHaar_integerRing_toReal]
  rw [← ENNReal.ofReal_mul (one_div_pos.mpr (localHalfDifferentFactor_pos F v)).le,
    one_div_mul_cancel (localHalfDifferentFactor_pos F v).ne', ENNReal.ofReal_one]

end DedekindZetaZeroFree.FiniteHaarCharts

end

section

noncomputable section

open scoped NumberField BigOperators Classical WithZero
open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

namespace DedekindZetaZeroFree.FiniteHaarCharts

variable (F : Type) [Field F] [NumberField F]

abbrev Adeles := FiniteHaarNormalization.Adeles F

theorem localMass_pos (v : Places F) : 0 < localMass F v := by
  rw [localMass, localNormalizedHaar_integerRing_toReal]
  exact localHalfDifferentFactor_pos F v

theorem localMass_finite_mulSupport : (Function.mulSupport (localMass F)).Finite := by
  refine (finite_localDifferentSupport F).subset ?_
  intro v hv
  by_contra hnot
  let S := (finite_localDifferentSupport F).toFinset
  have hS : localDifferentSupport F ⊆ (S : Set (Places F)) := by
    intro w hw
    exact (finite_localDifferentSupport F).mem_toFinset.mpr hw
  have hvS : v ∉ S := by
    exact fun h => hnot ((finite_localDifferentSupport F).mem_toFinset.mp h)
  apply hv
  rw [localMass, localNormalizedHaar_integerRing_of_not_mem F S hS v hvS,
    ENNReal.toReal_one]

def chartSubgroup (S : Finset (Places F)) : AddSubgroup (Adeles F) where
  carrier := {x | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F}
  zero_mem' := by intro v hv; exact (v.adicCompletionIntegers F).zero_mem
  add_mem' := by
    intro x y hx hy v hv
    exact (v.adicCompletionIntegers F).toSubring.add_mem (hx v hv) (hy v hv)
  neg_mem' := by
    intro x hx v hv
    exact (v.adicCompletionIntegers F).toSubring.neg_mem (hx v hv)

abbrev Chart (S : Finset (Places F)) := chartSubgroup F S

def split (S : Finset (Places F)) (x : Chart F S) : ChartCoordinates F S :=
  (fun v => x.1 v.1, fun v => ⟨x.1 v.1, x.2 v.1 v.2⟩)

def join (S : Finset (Places F)) (x : ChartCoordinates F S) : Chart F S := by
  let a : (v : Places F) → v.adicCompletion F := fun v =>
    if hv : v ∈ S then x.1 ⟨v, hv⟩ else (x.2 ⟨v, hv⟩ : v.adicCompletion F)
  have ha : ∀ᶠ v in Filter.cofinite, a v ∈ v.adicCompletionIntegers F := by
    filter_upwards [show ∀ᶠ v in Filter.cofinite, v ∉ S from
      Filter.eventually_cofinite.mpr (by simpa using S.finite_toSet)] with v hv
    dsimp only [a]
    rw [dif_neg hv]
    exact (x.2 ⟨v, hv⟩).2
  exact ⟨RestrictedProduct.mk a ha, by
    intro v hv
    change a v ∈ v.adicCompletionIntegers F
    dsimp only [a]
    rw [dif_neg hv]
    exact (x.2 ⟨v, hv⟩).2⟩

def chart (S : Finset (Places F)) : Chart F S ≃ₜ+ ChartCoordinates F S where
  toFun := split F S
  invFun := join F S
  left_inv := by
    intro x
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    change (if hv : v ∈ S then x.1 v else x.1 v) = x.1 v
    split <;> rfl
  right_inv := by
    intro x
    apply Prod.ext
    · funext v
      change (if hv : v.1 ∈ S then x.1 ⟨v.1, hv⟩ else
        (x.2 ⟨v.1, hv⟩ : v.1.adicCompletion F)) = x.1 v
      simp only [dif_pos v.2]
    · funext v
      apply Subtype.ext
      change (if hv : v.1 ∈ S then x.1 ⟨v.1, hv⟩ else
        (x.2 ⟨v.1, hv⟩ : v.1.adicCompletion F)) = (x.2 v : v.1.adicCompletion F)
      simp only [dif_neg v.2]
  map_add' := by
    intro x y
    rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_pi fun v => (RestrictedProduct.continuous_eval v.1).comp
        (continuous_subtype_val : Continuous (Subtype.val : Chart F S → Adeles F))
    · exact continuous_pi fun v =>
        ((RestrictedProduct.continuous_eval v.1).comp
          (continuous_subtype_val : Continuous (Subtype.val : Chart F S → Adeles F))).subtype_mk _
  continuous_invFun := by
    let P := RestrictedProduct
      (fun v : Places F => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (Filter.principal {v | v ∉ S})
    let j : ChartCoordinates F S → P := fun x => RestrictedProduct.mk
      (fun v => if hv : v ∈ S then x.1 ⟨v, hv⟩ else
        (x.2 ⟨v, hv⟩ : v.adicCompletion F))
      (Filter.eventually_principal.mpr (fun v hv => by
        rw [dif_neg hv]; exact (x.2 ⟨v, hv⟩).2))
    have hj : Continuous j := by
      apply RestrictedProduct.continuous_rng_of_principal.mpr
      apply continuous_pi
      intro v
      change @Continuous (ChartCoordinates F S) (v.adicCompletion F) _ _
        (fun x : ChartCoordinates F S => if hv : v ∈ S then (x.1 ⟨v, hv⟩ : v.adicCompletion F) else
          (x.2 ⟨v, hv⟩ : v.adicCompletion F))
      by_cases hv : v ∈ S
      · simpa only [Function.comp_def, j, dif_pos hv] using
          (continuous_apply (⟨v, hv⟩ : S)).comp
            (continuous_fst : Continuous (Prod.fst : ChartCoordinates F S → ExceptionalProduct F S))
      · simpa only [Function.comp_def, j, dif_neg hv] using
          (continuous_subtype_val : Continuous (Subtype.val : v.adicCompletionIntegers F → v.adicCompletion F)).comp
            ((continuous_apply (⟨v, hv⟩ : {v : Places F // v ∉ S})).comp
              (continuous_snd : Continuous (Prod.snd : ChartCoordinates F S → Tail F S)))
    have hfilter : Filter.cofinite ≤ Filter.principal {v : Places F | v ∉ S} :=
      Filter.le_principal_iff.mpr (Filter.eventually_cofinite.mpr
        (by simpa using S.finite_toSet))
    have hinc := RestrictedProduct.continuous_inclusion
      (R := fun v : Places F => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hfilter
    apply Continuous.subtype_mk
    exact hinc.comp hj

@[simp] theorem chart_apply (S : Finset (Places F)) (x : Chart F S) :
    chart F S x = split F S x := rfl

@[simp] theorem chart_symm_apply (S : Finset (Places F)) (x : ChartCoordinates F S) :
    (chart F S).symm x = join F S x := rfl

theorem chartSubgroup_isOpen (S : Finset (Places F)) :
    IsOpen (chartSubgroup F S : Set (Adeles F)) := by
  exact RestrictedProduct.isOpen_forall_imp_mem (KPAdelicTopology.completionIntegers_isOpen F)

theorem chartSubgroup_measurableSet (S : Finset (Places F)) :
    MeasurableSet (chartSubgroup F S : Set (Adeles F)) := by
  exact (chartSubgroup_isOpen F S).measurableSet

theorem chart_inclusion_measurableEmbedding (S : Finset (Places F)) :
    MeasurableEmbedding (Subtype.val : Chart F S → Adeles F) := by
  exact MeasurableEmbedding.subtype_coe (chartSubgroup_measurableSet F S)

theorem chart_measurable (S : Finset (Places F)) : Measurable (chart F S) := by
  exact (chart F S).continuous.measurable

theorem tailMass_pos (S : Finset (Places F)) : 0 < tailMass F S := by
  rw [tailMass, finprod_subtype_eq_finprod_cond]
  change 0 < ∏ᶠ v ∈ ({v : Places F | v ∉ S} : Set (Places F)), localMass F v
  rw [finprod_mem_eq_prod (s := {v : Places F | v ∉ S}) _
    ((localMass_finite_mulSupport F).inter_of_right _)]
  exact Finset.prod_pos (fun v _ => localMass_pos F v)

theorem tailMass_eq_kappa_div (S : Finset (Places F)) :
    tailMass F S = FiniteHaarNormalization.kappa F / ∏ v ∈ S, localMass F v := by
  have hprod : (∏ v ∈ S, localMass F v) * tailMass F S =
      ∏ᶠ v : Places F, localMass F v := by
    have h := finprod_mem_inter_mul_sdiff' (f := localMass F)
      (s := Set.univ) (↑S : Set (Places F))
      (by simpa using localMass_finite_mulSupport F)
    rw [Set.univ_inter, finprod_mem_coe_finset, finprod_mem_univ] at h
    have hs : (Set.univ \ ↑S : Set (Places F)) = {v | v ∉ S} := by ext; simp
    rw [hs] at h
    rw [tailMass, finprod_subtype_eq_finprod_cond]
    exact h
  have hk : (∏ᶠ v : Places F, localMass F v) = FiniteHaarNormalization.kappa F := by
    simpa only [funext (localMass_eq_halfNormMass F)] using
      FiniteHaarNormalization.finprod_halfNormMass_eq_kappa F
  apply (eq_div_iff (ne_of_gt (Finset.prod_pos fun v _ => localMass_pos F v))).mpr
  rw [mul_comm, hprod, hk]

def chartMeasure (S : Finset (Places F)) : Measure (Chart F S) :=
  (FiniteHaarNormalization.measure F).comap Subtype.val

theorem map_chartMeasure (S : Finset (Places F)) :
    Measure.map (chart F S) (chartMeasure F S) = coordinateMeasure F S := by
  let i : Chart F S →+ Adeles F := (chartSubgroup F S).subtype
  have hi : Topology.IsOpenEmbedding i := (chartSubgroup_isOpen F S).isOpenEmbedding_subtypeVal
  haveI : (chartMeasure F S).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.comap (mH := inferInstance) (FiniteHaarNormalization.measure F) hi
  haveI : (Measure.map (chart F S) (chartMeasure F S)).IsAddHaarMeasure :=
    (chart F S).isAddHaarMeasure_map _
  haveI : (ENNReal.ofReal (tailMass F S) • tailProbability F S).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul _
      (ENNReal.ofReal_ne_zero_iff.mpr (tailMass_pos F S)) ENNReal.ofReal_ne_top
  haveI : (coordinateMeasure F S).IsAddHaarMeasure := by
    unfold coordinateMeasure
    infer_instance
  let K : Set (ChartCoordinates F S) :=
    (Set.pi Set.univ (fun v : S => (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)))) ×ˢ Set.univ
  have hKcompact : IsCompact K :=
    (isCompact_univ_pi (fun v => KPAdelicTopology.completionIntegers_isCompact F v.1)).prod isCompact_univ
  have hKopen : IsOpen K :=
    (isOpen_set_pi (Set.toFinite Set.univ) (fun v _ => KPAdelicTopology.completionIntegers_isOpen F v.1)).prod isOpen_univ
  let K0 : PositiveCompacts (ChartCoordinates F S) :=
    ⟨⟨K, hKcompact⟩, by
      rw [hKopen.interior_eq]
      exact ⟨0, ⟨fun v _ => (v.1.adicCompletionIntegers F).zero_mem, Set.mem_univ _⟩⟩⟩
  have hmass : coordinateMeasure F S K = ENNReal.ofReal (FiniteHaarNormalization.kappa F) := by
    rw [coordinateMeasure, Measure.prod_prod, Measure.pi_pi, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    have he (v : S) : localNormalizedHaar F v.1 (v.1.adicCompletionIntegers F) =
        ENNReal.ofReal (localMass F v.1) := by
      rw [localMass, localNormalizedHaar_integerRing, ENNReal.toReal_ofReal (localHalfDifferentFactor_pos F v.1).le]
    simp_rw [he]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun v _ => (localMass_pos F v.1).le),
      ← ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => (localMass_pos F v.1).le)]
    congr 1
    rw [Finset.prod_coe_sort, tailMass_eq_kappa_div]
    have hpos : 0 < ∏ v ∈ S, localMass F v := Finset.prod_pos fun v _ => localMass_pos F v
    field_simp
  have hpre : (Subtype.val : Chart F S → Adeles F) '' ((chart F S) ⁻¹' K) =
      FiniteHaarNormalization.integralCompact F := by
    rw [FiniteHaarNormalization.integralCompact_eq_coordinatewise]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ v
      by_cases hv : v ∈ S
      · exact hy.1 ⟨v, hv⟩ (Set.mem_univ _)
      · exact y.2 v hv
    · intro hx
      refine ⟨⟨x, fun v _ => hx v⟩, ?_, rfl⟩
      exact ⟨fun v _ => hx v.1, Set.mem_univ _⟩
  have hmapmass : Measure.map (chart F S) (chartMeasure F S) K =
      ENNReal.ofReal (FiniteHaarNormalization.kappa F) := by
    rw [Measure.map_apply (chart_measurable F S) hKopen.measurableSet,
      chartMeasure, (chart_inclusion_measurableEmbedding F S).comap_apply,
      hpre, FiniteHaarNormalization.measure_integralCompact]
  rw [Measure.addHaarMeasure_unique (Measure.map (chart F S) (chartMeasure F S)) K0,
    Measure.addHaarMeasure_unique (coordinateMeasure F S) K0]
  change Measure.map (chart F S) (chartMeasure F S) K • _ = coordinateMeasure F S K • _
  rw [hmass, hmapmass]

def cylinder (S : Finset (Places F))
    (B : (v : S) → Set (v.1.adicCompletion F)) : Set (Adeles F) :=
  {x | (∀ v : S, x v.1 ∈ B v) ∧
    ∀ v : Places F, v ∉ S → x v ∈ v.adicCompletionIntegers F}

theorem measure_cylinder (S : Finset (Places F))
    (B : (v : S) → Set (v.1.adicCompletion F))
    (hB : ∀ v, MeasurableSet (B v)) :
    FiniteHaarNormalization.measure F (cylinder F S B) =
      ENNReal.ofReal (tailMass F S) * ∏ v : S, localNormalizedHaar F v.1 (B v) := by
  let D : Set (ChartCoordinates F S) := (Set.pi Set.univ B) ×ˢ Set.univ
  have hD : MeasurableSet D := (MeasurableSet.univ_pi hB).prod MeasurableSet.univ
  have hc : (Subtype.val : Chart F S → Adeles F) '' ((chart F S) ⁻¹' D) =
      cylinder F S B := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨fun v => hy.1 v (Set.mem_univ v), y.2⟩
    · rintro ⟨hx, hi⟩
      refine ⟨⟨x, hi⟩, ?_, rfl⟩
      exact ⟨fun v _ => hx v, Set.mem_univ _⟩
  have hin := chart_inclusion_measurableEmbedding F S
  rw [← hc, ← Measure.comap_apply _ hin.injective
      (fun _ hs => hin.measurableSet_image.mpr hs) _
      ((chart_measurable F S) hD)]
  change chartMeasure F S ((chart F S) ⁻¹' D) = _
  rw [← Measure.map_apply (chart_measurable F S) hD, map_chartMeasure,
    coordinateMeasure, Measure.prod_prod, Measure.pi_pi, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one, mul_comm]

def inclusion (S R : Finset (Places F)) (hSR : S ⊆ R) : Chart F S →+ Chart F R where
  toFun x := ⟨x.1, fun v hv => x.2 v (fun h => hv (hSR h))⟩
  map_zero' := rfl
  map_add' _ _ := rfl

end DedekindZetaZeroFree.FiniteHaarCharts

end
end
