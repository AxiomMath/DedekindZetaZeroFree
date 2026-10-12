module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceBaseChange.LocalDifferentData
public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceBaseChange.IntegralTraceDual

@[expose] public section

noncomputable section
open scoped NumberField ValuativeRel nonZeroDivisors
open NumberField IsDedekindDomain LocalFieldTheory WithZero
open ValuationTheory.DiscreteValuationField

namespace DedekindZetaZeroFree.TraceBaseChange

variable (F : Type) [Field F] [NumberField F]

 def placeAboveRaw (v : HeightOneSpectrum (𝓞 F)) : PlacesAbove F (PlaceTraceAdapter.prime F v) :=
 ⟨v, by simp [PlacesAbove, PlaceTraceAdapter.prime, PlaceTraceAdapter.rationalPlace]⟩
theorem fieldScalarMap_eq_padicMap (v : HeightOneSpectrum (𝓞 F)) : fieldScalarMap F (PlaceTraceAdapter.prime F v) (placeAboveRaw F v) = PlaceTraceAdapter.padicMap F v := by
  apply DFunLike.coe_injective
  apply DenseRange.equalizer (Padic.denseRange_ratCast (PlaceTraceAdapter.prime F v))
  · letI : Algebra ℚ ((Rat.HeightOneSpectrum.primesEquiv.symm (PlaceTraceAdapter.prime F v)).adicCompletion ℚ) := HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ _
    exact (finitePlaceAdicCompletionMap_continuous ℚ F _ _).comp (Padic.adicCompletionEquiv (𝓞 ℚ) (PlaceTraceAdapter.prime F v)).continuous
  · letI : Algebra ℚ ((PlaceTraceAdapter.rationalPlace F v).adicCompletion ℚ) := HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ _
    exact (finitePlaceAdicCompletionMap_continuous ℚ F _ _).comp (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (PlaceTraceAdapter.rationalPlace F v)).symm.continuous
  · funext x
    change fieldScalarMap F (PlaceTraceAdapter.prime F v) (placeAboveRaw F v) (x : ℚ_[PlaceTraceAdapter.prime F v]) = PlaceTraceAdapter.padicMap F v (x : ℚ_[PlaceTraceAdapter.prime F v])
    simp only [map_ratCast]
    rfl

private theorem base_ring (v : HeightOneSpectrum (𝓞 F)) (x : ℚ_[PlaceTraceAdapter.prime F v]) :
    x ∈ (baseRaw F v).valuation.valuationSubring ↔ ‖x‖ ≤ 1 := by
  change (baseRaw F v).valuation x ≤ 1 ↔ _
  simp only [baseRaw, localCompleteDVF_valuation_eq]
  exact (LocalFieldTheory.Padic.integer_mem_iff_norm_le_one _ x)
private theorem rational_ring (v : HeightOneSpectrum (𝓞 F)) (x : (PlaceTraceAdapter.rationalPlace F v).adicCompletion ℚ) :
    x ∈ (PlaceTraceAdapter.rationalPlace F v).adicCompletionIntegers ℚ ↔
    ‖PlaceTraceAdapter.rationalCompletionEquiv F v x‖ ≤ 1 := by
  have h := Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn (PlaceTraceAdapter.rationalPlace F v)
  constructor
  · intro hx
    exact h.mapsTo hx
  · intro hx
    obtain ⟨y, hy, heq⟩ := h.surjOn hx
    have hxy : y = x := (PlaceTraceAdapter.rationalCompletionEquiv F v).injective heq
    exact hxy ▸ hy

private theorem raw_integerRing_eq (v : HeightOneSpectrum (𝓞 F)) :
    ((targetRaw F v).valuation.valuationSubring : Set (v.adicCompletion F)) =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  letI : (baseRaw F v).valuation.HasExtension (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) := by
    apply Valuation.HasExtension.ofComapInteger
    ext x
    rw [Subring.mem_comap]
    change algebraMap ℚ_[PlaceTraceAdapter.prime F v] (v.adicCompletion F) x ∈ v.adicCompletionIntegers F ↔ _
    have hnorm := finitePlaceAdicCompletionMap_norm_le_one_iff ℚ F
      (PlaceTraceAdapter.rationalPlace F v) ⟨v, rfl⟩
      ((PlaceTraceAdapter.rationalCompletionEquiv F v).symm x)
    have hnorm' : (algebraMap ℚ_[PlaceTraceAdapter.prime F v] (v.adicCompletion F) x ∈ v.adicCompletionIntegers F) ↔
        ‖(PlaceTraceAdapter.rationalCompletionEquiv F v).symm x‖ ≤ 1 := by
      exact ⟨fun h => hnorm.mp (norm_le_one_of_mem_adicCompletionIntegers v h),
        fun h => mem_adicCompletionIntegers_of_norm_le_one v (hnorm.mpr h)⟩
    rw [hnorm']
    have hr := rational_ring F v ((PlaceTraceAdapter.rationalCompletionEquiv F v).symm x)
    rw [RingEquiv.apply_symm_apply] at hr
    exact ((⟨fun h => mem_adicCompletionIntegers_of_norm_le_one _ h,
      fun h => norm_le_one_of_mem_adicCompletionIntegers _ h⟩ :
      ‖(PlaceTraceAdapter.rationalCompletionEquiv F v).symm x‖ ≤ 1 ↔
      (PlaceTraceAdapter.rationalCompletionEquiv F v).symm x ∈
        (PlaceTraceAdapter.rationalPlace F v).adicCompletionIntegers ℚ).trans hr).trans
          (base_ring F v x).symm
  have heq := ValuedExtension.valuationSubring_eq_of_finite_separable
    (baseRaw F v) (targetRaw F v) (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)
  exact congrArg (fun R : ValuationSubring (v.adicCompletion F) => (R : Set (v.adicCompletion F))) heq

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem raw_mem (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
  x ∈ codifferentRaw F v ↔ x ∈ localTraceDual F (PlaceTraceAdapter.prime F v) (placeAboveRaw F v) := by
  let p := PlaceTraceAdapter.prime F v
  let w := placeAboveRaw F v
  have htrace (z : v.adicCompletion F) : localTraceAt F p w z = Algebra.trace ℚ_[p] (v.adicCompletion F) z := by
    exact @Algebra.trace_eq_of_ringEquiv ℚ_[p] ℚ_[p] (v.adicCompletion F) _ _ _
      (fieldAlgebra F p w) (PlaceTraceAdapter.padicAlgebra F v) (RingEquiv.refl _) (by
        change (PlaceTraceAdapter.padicMap F v).comp (RingHom.id _) = fieldScalarMap F p w
        rw [RingHom.comp_id]
        exact (fieldScalarMap_eq_padicMap F v).symm) z
  unfold codifferentRaw
  rw [RamificationTheory.DiscreteValuationField.ValuedExtension.mem_codifferentSubmodule_iff_trace_mul_integral_of_finite_separable]
  have ha (a : v.adicCompletion F) : a ∈ (1 : Submodule (targetRaw F v).valuationSubring (v.adicCompletion F)) ↔ a ∈ v.adicCompletionIntegers F := by
    rw [Submodule.mem_one]
    change (∃ z : (targetRaw F v).valuationSubring, (z : v.adicCompletion F) = a) ↔ a ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    rw [← raw_integerRing_eq F v]
    exact ⟨fun ⟨z,hz⟩ => hz ▸ z.property, fun h => ⟨⟨a,h⟩, rfl⟩⟩
  have hb (t : ℚ_[p]) : IsIntegral (baseRaw F v).valuationSubring t ↔ t ∈ padicIntegerLattice p := by
    rw [IsIntegrallyClosed.isIntegral_iff]
    change (∃ z : (baseRaw F v).valuationSubring, (z : ℚ_[p]) = t) ↔ ∃ z : ℤ_[p], (z : ℚ_[p]) = t
    exact ⟨fun ⟨z,hz⟩ => ⟨⟨z, (base_ring F v z).mp z.property⟩,hz⟩,
      fun ⟨z,hz⟩ => ⟨⟨z, (base_ring F v z).mpr z.property⟩,hz⟩⟩
  change (∀ a ∈ (1 : Submodule (targetRaw F v).valuationSubring (v.adicCompletion F)), IsIntegral (baseRaw F v).valuationSubring (Algebra.trace ℚ_[p] (v.adicCompletion F) (x * a))) ↔ x ∈ (⨅ y : v.adicCompletionIntegers F, (padicIntegerLattice p).comap (((localTraceAt F p w).comp (LinearMap.mulRight ℚ_[p] (y : v.adicCompletion F))).restrictScalars ℤ_[p]))
  letI : Algebra ℚ_[p] (v.adicCompletion F) := fieldAlgebra F p w
  letI : Algebra ℤ_[p] (v.adicCompletion F) := fieldIntegerAlgebra F p w
  have hi := @Submodule.mem_iInf ℤ_[p] (v.adicCompletion F) _ _ _ (v.adicCompletionIntegers F)
    (fun y => (padicIntegerLattice p).comap (((localTraceAt F p w).comp (LinearMap.mulRight ℚ_[p] (y : v.adicCompletion F))).restrictScalars ℤ_[p])) x
  exact Iff.trans (by
    simp only [ha, hb]
    constructor
    · intro h y
      change localTraceAt F p w (x * (y : v.adicCompletion F)) ∈ padicIntegerLattice p
      rw [htrace]
      exact h y y.property
    · intro h a ha
      rw [← htrace]
      exact h ⟨a,ha⟩) hi.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

theorem codifferentRaw_eq_span_global_traceDual (v : HeightOneSpectrum (𝓞 F)) :
    codifferentRaw F v =
      Submodule.span (targetRaw F v).valuationSubring
        ((algebraMap F (v.adicCompletion F)) ''
          (Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) : Set F)) := by
  let p := PlaceTraceAdapter.prime F v
  let w := placeAboveRaw F v
  have hset : (globalTraceDual F : Set F) = (Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) : Set F) :=
    congrArg (fun M : Submodule (𝓞 F) F => (M : Set F)) (FractionalIdeal.coe_dual_one ℤ ℚ F (𝓞 F))
  have hr : (targetRaw F v).valuation.valuationSubring.toSubring = (v.adicCompletionIntegers F).toSubring :=
    SetLike.coe_injective (raw_integerRing_eq F v)
  have hs (s : Set (v.adicCompletion F)) :
      (Submodule.span (targetRaw F v).valuationSubring s : Set (v.adicCompletion F)) =
        (Submodule.span (v.adicCompletionIntegers F) s : Set (v.adicCompletion F)) := by
    change (Submodule.span (targetRaw F v).valuation.valuationSubring.toSubring s : Set (v.adicCompletion F)) = _
    rw [hr]
    rfl
  apply SetLike.coe_injective
  calc
    (codifferentRaw F v : Set (v.adicCompletion F)) = ((localTraceDual F p w : Set (w.val.adicCompletion F)) : Set (v.adicCompletion F)) := Set.ext (raw_mem F v)
    _ = ((globalCodifferentIntegralSpan F p w : Set (w.val.adicCompletion F)) : Set (v.adicCompletion F)) := traceDual_localIntegralSpan F p w
    _ = (Submodule.span (targetRaw F v).valuationSubring (algebraMap F (v.adicCompletion F) '' (Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) : Set F)) : Set (v.adicCompletion F)) := by
      change (Submodule.span (v.adicCompletionIntegers F) (algebraMap F (v.adicCompletion F) '' (globalTraceDual F : Set F)) : Set (v.adicCompletion F)) = _
      rw [hset]
      exact (hs _).symm

theorem map_globalDifferent_eq_localDifferent (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.map (integerMap F v) (differentIdeal ℤ (𝓞 F)) = differentRaw F v := by
  let R := (targetRaw F v).valuationSubring
  let L := v.adicCompletion F
  letI : Algebra (𝓞 F) R := (integerMap F v).toAlgebra
  letI : IsScalarTower (𝓞 F) R L := IsScalarTower.of_algebraMap_eq (fun x => by exact (integerMap_coe F v x).symm)
  letI : IsIntegralClosure R (baseRaw F v).valuationSubring L :=
    chosenLocalExtensionCompleteDVF_isIntegralClosure _ _
  letI : Module.IsTorsionFree (baseRaw F v).valuationSubring R :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.moduleIsTorsionFree_target_valuationSubring_of_finite_separable (baseRaw F v) (targetRaw F v)
  have hinj : Function.Injective (integerMap F v) := by
    intro x y h
    apply RingOfIntegers.ext
    apply (algebraMap F L).injective
    exact (integerMap_coe F v x).symm.trans ((congrArg (fun z : R => (z : L)) h).trans (integerMap_coe F v y))
  let hf := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (integerMap F v) hinj
  let E := FractionalIdeal.extendedHom' (K := F) L hf
  have fieldmap : IsLocalization.map (S := F) L (integerMap F v) hf = algebraMap F L := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F))
    apply RingHom.ext
    intro x
    change IsLocalization.map L (integerMap F v) hf (algebraMap (𝓞 F) F x) = algebraMap F L (x : F)
    rw [IsLocalization.map_eq]
    exact integerMap_coe F v x
  have he (I : FractionalIdeal (𝓞 F)⁰ F) :
      (E I : Submodule R L) = Submodule.span R (algebraMap F L '' (I : Set F)) := by
    change (FractionalIdeal.extended L hf I : Submodule R L) = _
    rw [FractionalIdeal.coe_extended_eq_span, fieldmap]
  apply FractionalIdeal.coeIdeal_injective (K := L)
  change (Ideal.map (integerMap F v) (differentIdeal ℤ (𝓞 F)) : FractionalIdeal R⁰ L) = (differentRaw F v : FractionalIdeal R⁰ L)
  rw [← FractionalIdeal.extended_coeIdeal_eq_map (K := F) L hf]
  rw [coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)]
  change E ((FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F))⁻¹) = _
  rw [map_inv₀]
  unfold differentRaw
  rw [RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable_eq_differentIdeal]
  rw [coeIdeal_differentIdeal (baseRaw F v).valuationSubring ℚ_[PlaceTraceAdapter.prime F v] L R]
  congr 1
  apply FractionalIdeal.coeToSubmodule_injective
  change (E (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)) : Submodule R L) = (FractionalIdeal.dual (baseRaw F v).valuationSubring ℚ_[PlaceTraceAdapter.prime F v] (1 : FractionalIdeal R⁰ L) : Submodule R L)
  rw [he, FractionalIdeal.coe_dual_one]
  have hset : (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : Set F) = (Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) : Set F) := congrArg (fun M : Submodule (𝓞 F) F => (M : Set F)) (FractionalIdeal.coe_dual_one ℤ ℚ F (𝓞 F))
  rw [hset]
  exact (codifferentRaw_eq_span_global_traceDual F v).symm

end DedekindZetaZeroFree.TraceBaseChange

end
