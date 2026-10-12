module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceCharacters.LocalTraceCharacter

@[expose] public section

noncomputable section

open scoped NumberField ValuativeRel nonZeroDivisors
open NumberField IsDedekindDomain LocalFieldTheory WithZero
open ValuationTheory.DiscreteValuationField

namespace DedekindZetaZeroFree

namespace LocalConductor

variable (F : Type) [Field F] [NumberField F]

def base (v : HeightOneSpectrum (𝓞 F)) :
    CompleteDVF ℚ_[PlaceTraceAdapter.prime F v] :=
  localCompleteDVF ℚ_[PlaceTraceAdapter.prime F v]

def target (v : HeightOneSpectrum (𝓞 F)) : CompleteDVF (v.adicCompletion F) :=
  chosenLocalExtensionCompleteDVF ℚ_[PlaceTraceAdapter.prime F v]
    (v.adicCompletion F)

instance valuationHasExtension (v : HeightOneSpectrum (𝓞 F)) :
    (base F v).valuation.HasExtension (target F v).valuation :=
  chosenLocalExtensionCompleteDVF_hasExtension _ _

private theorem base_ring (v : HeightOneSpectrum (𝓞 F)) (x : ℚ_[PlaceTraceAdapter.prime F v]) :
    x ∈ (LocalConductor.base F v).valuation.valuationSubring ↔ ‖x‖ ≤ 1 := by
  change (LocalConductor.base F v).valuation x ≤ 1 ↔ _
  simp only [LocalConductor.base, localCompleteDVF_valuation_eq]
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

theorem target_integerRing_eq (v : HeightOneSpectrum (𝓞 F)) :
    ((target F v).valuation.valuationSubring : Set (v.adicCompletion F)) =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  letI : (base F v).valuation.HasExtension (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) := by
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
    (base F v) (target F v) (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)
  exact congrArg (fun R : ValuationSubring (v.adicCompletion F) => (R : Set (v.adicCompletion F))) heq

end LocalConductor

variable (F : Type) [Field F] [NumberField F]

def localCodifferent (v : HeightOneSpectrum (𝓞 F)) :
    Submodule (LocalConductor.target F v).valuationSubring (v.adicCompletion F) :=
  RamificationTheory.DiscreteValuationField.ValuedExtension.codifferentSubmodule
    (LocalConductor.base F v) (LocalConductor.target F v)

def localDifferent (v : HeightOneSpectrum (𝓞 F)) :
    Ideal (LocalConductor.target F v).valuationSubring :=
  RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
    (LocalConductor.base F v) (LocalConductor.target F v)

def localIntegerAnnihilator (v : HeightOneSpectrum (𝓞 F)) :
    Set (v.adicCompletion F) :=
  {y | ∀ a : v.adicCompletion F, a ∈ v.adicCompletionIntegers F →
    localFiniteCharacter F v (y * a) = 1}

theorem localIntegerAnnihilator_eq_codifferent (v : HeightOneSpectrum (𝓞 F)) :
    localIntegerAnnihilator F v =
      (localCodifferent F v : Set (v.adicCompletion F)) := by
  ext y
  change (∀ a, a ∈ v.adicCompletionIntegers F → localFiniteCharacter F v (y*a) = 1) ↔ _
  change (∀ a, a ∈ v.adicCompletionIntegers F → localFiniteCharacter F v (y*a) = 1) ↔ y ∈ localCodifferent F v
  unfold localCodifferent
  rw [RamificationTheory.DiscreteValuationField.ValuedExtension.mem_codifferentSubmodule_iff_trace_mul_integral_of_finite_separable
    (LocalConductor.base F v) (LocalConductor.target F v)]
  have ha (a : v.adicCompletion F) : a ∈ (1 : Submodule (LocalConductor.target F v).valuationSubring (v.adicCompletion F)) ↔
      a ∈ v.adicCompletionIntegers F := by
    rw [Submodule.mem_one]
    change (∃ z : (LocalConductor.target F v).valuationSubring, (z : v.adicCompletion F) = a) ↔ _
    change (∃ z : (LocalConductor.target F v).valuationSubring, (z : v.adicCompletion F) = a) ↔ a ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    rw [← LocalConductor.target_integerRing_eq F v]
    exact ⟨fun ⟨z, hz⟩ => hz ▸ z.property, fun h => ⟨⟨a,h⟩,rfl⟩⟩
  have hb (x : ℚ_[PlaceTraceAdapter.prime F v]) :
      IsIntegral (LocalConductor.base F v).valuationSubring x ↔
        x ∈ Set.range (fun z : ℤ_[PlaceTraceAdapter.prime F v] => (z : ℚ_[PlaceTraceAdapter.prime F v])) := by
    rw [IsIntegrallyClosed.isIntegral_iff]
    change (∃ z : (LocalConductor.base F v).valuationSubring, (z : ℚ_[PlaceTraceAdapter.prime F v]) = x) ↔ _
    have hmem : x ∈ (LocalConductor.base F v).valuation.valuationSubring ↔ ‖x‖ ≤ 1 := by
      change (LocalConductor.base F v).valuation x ≤ 1 ↔ _
      simp only [LocalConductor.base, localCompleteDVF_valuation_eq]
      exact LocalFieldTheory.Padic.integer_mem_iff_norm_le_one _ x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨⟨(z : ℚ_[PlaceTraceAdapter.prime F v]), hmem.mp z.property⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨⟨(z : ℚ_[PlaceTraceAdapter.prime F v]), hmem.mpr z.property⟩, rfl⟩
  simp only [ha, hb, localFiniteCharacter_eq_one_iff, PlaceTraceAdapter.trace]

theorem localDifferent_eq_one_div_codifferent (v : HeightOneSpectrum (𝓞 F)) :
    IsLocalization.coeSubmodule (v.adicCompletion F) (localDifferent F v) =
      1 / localCodifferent F v := by
  exact RamificationTheory.DiscreteValuationField.ValuedExtension.coeSubmodule_differentIdealOfFiniteSeparable_eq_one_div_codifferent
      (LocalConductor.base F v) (LocalConductor.target F v)

theorem localCodifferent_eq_inverse_different (v : HeightOneSpectrum (𝓞 F)) :
    localCodifferent F v =
      1 / IsLocalization.coeSubmodule (v.adicCompletion F) (localDifferent F v) := by
  let A := (LocalConductor.base F v).valuationSubring
  let B := (LocalConductor.target F v).valuationSubring
  letI : IsIntegralClosure B A (v.adicCompletion F) :=
    ValuedExtension.target_valuationSubring_isIntegralClosure_of_finite_separable (LocalConductor.base F v) (LocalConductor.target F v)
  let J : FractionalIdeal B⁰ (v.adicCompletion F) := FractionalIdeal.dual A ℚ_[PlaceTraceAdapter.prime F v] 1
  have hJ : J ≠ 0 := FractionalIdeal.dual_ne_zero _ _ one_ne_zero
  have hcoe : (J : Submodule B (v.adicCompletion F)) = localCodifferent F v :=
    FractionalIdeal.coe_dual_one _ _ _ _
  rw [localDifferent_eq_one_div_codifferent, ← hcoe]
  have h1 := FractionalIdeal.coe_inv_of_ne_zero (v.adicCompletion F) hJ
  rw [IsLocalization.coeSubmodule_top] at h1
  rw [← h1]
  have h2 := FractionalIdeal.coe_inv_of_ne_zero (v.adicCompletion F) (inv_ne_zero hJ)
  rw [IsLocalization.coeSubmodule_top, inv_inv] at h2
  exact h2

theorem localIntegerAnnihilator_eq_inverse_different
    (v : HeightOneSpectrum (𝓞 F)) :
    localIntegerAnnihilator F v =
      ((1 / IsLocalization.coeSubmodule (v.adicCompletion F) (localDifferent F v) :
        Submodule (LocalConductor.target F v).valuationSubring (v.adicCompletion F)) :
        Set (v.adicCompletion F)) := by
  rw [localIntegerAnnihilator_eq_codifferent, localCodifferent_eq_inverse_different]

def localDifferentSupport : Set (HeightOneSpectrum (𝓞 F)) :=
  {v | v.asIdeal ∣ differentIdeal ℤ (𝓞 F)}

theorem finite_localDifferentSupport : (localDifferentSupport F).Finite := by
  exact Ideal.finite_factors differentIdeal_ne_bot

namespace LocalConductorProof

variable (v : HeightOneSpectrum (𝓞 F))

private theorem val_prime (hv : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) ((PlaceTraceAdapter.prime F v).1 : v.adicCompletion F) = exp (-1) := by
  let p : ℕ := (PlaceTraceAdapter.prime F v).1
  change (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (p : v.adicCompletion F) = _
  let w := PlaceTraceAdapter.rationalPlace F v
  letI : v.asIdeal.LiesOver w.asIdeal := ⟨rfl⟩
  haveI : Algebra.IsUnramifiedAt ℤ v.asIdeal := not_dvd_differentIdeal_iff.mp hv
  haveI : Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal :=
    Algebra.IsUnramifiedAt.of_restrictScalars ℤ _
  have he : w.asIdeal.ramificationIdx' v.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx w.asIdeal v.asIdeal w.ne_bot]
    exact Ideal.ramificationIdx_eq_one v.asIdeal (𝓞 ℚ)
  have hw : w.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
    have hh := congrArg (Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm)
      (Rat.HeightOneSpectrum.span_natGenerator w)
    simp only [Ideal.map_span, Set.image_singleton, map_natCast] at hh
    rw [Ideal.map_symm (I := Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) w.asIdeal),
      Ideal.comap_map_of_bijective _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).bijective] at hh
    exact hh.symm
  have hr := w.intValuation_singleton (r := (p : 𝓞 ℚ))
    (by exact_mod_cast (PlaceTraceAdapter.prime F v).2.ne_zero) hw
  have hval := HeightOneSpectrum.intValuation_liesOver w v
    (p : 𝓞 ℚ)
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx w.asIdeal v.asIdeal w.ne_bot,
    he, pow_one, hr] at hval
  simp only [map_natCast] at hval
  have hcoe : (p : v.adicCompletion F) =
      ((p : F) : v.adicCompletion F) := by
    apply HeightOneSpectrum.adicCompletion.ext
    change _ = ((WithVal.toVal (v.valuation F) (p : F)) : (v.valuation F).Completion)
    change _ = (UniformSpace.Completion.coeRingHom.comp
      (WithVal.equiv (v.valuation F)).symm.toRingHom) (p : F)
    rw [map_natCast]
    exact map_natCast (HeightOneSpectrum.adicCompletion.equiv F v) p
  rw [hcoe, HeightOneSpectrum.adicCompletion.valued_coe]
  simpa using (v.valuation_of_algebraMap (K := F)
    (p : 𝓞 F)).trans hval.symm
 def baseEquiv : ℤ_[PlaceTraceAdapter.prime F v] ≃+*
    (LocalConductor.base F v).valuationSubring :=
  RingEquiv.restrict (RingEquiv.refl ℚ_[PlaceTraceAdapter.prime F v])
    (PadicInt.subring (PlaceTraceAdapter.prime F v))
    (LocalConductor.base F v).valuation.valuationSubring (by
      intro x
      change ‖x‖ ≤ 1 ↔ (LocalConductor.base F v).valuation x ≤ 1
      simp only [LocalConductor.base, localCompleteDVF_valuation_eq]
      exact (LocalFieldTheory.Padic.integer_mem_iff_norm_le_one _ x).symm)

private theorem target_span (hv : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    (LocalConductor.target F v).maximalIdeal = Ideal.span {algebraMap ℤ _ (PlaceTraceAdapter.prime F v).1} := by
  let e : (LocalConductor.target F v).valuationSubring ≃+* v.adicCompletionIntegers F :=
    RingEquiv.restrict (RingEquiv.refl (v.adicCompletion F)) _ _ (by
      intro x
      exact Set.ext_iff.mp (LocalConductor.target_integerRing_eq F v) x)
  have hmem : ((PlaceTraceAdapter.prime F v).1 : v.adicCompletion F) ∈
      v.adicCompletionIntegers F := by
    change (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)
      ((PlaceTraceAdapter.prime F v).1 : v.adicCompletion F) ≤ 1
    rw [val_prime F v hv]
    simp
  have hu := LocalFieldTheory.DiscreteValuationField.WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)
    ((PlaceTraceAdapter.prime F v).1 : v.adicCompletion F) (val_prime F v hv)
  have hg : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) =
      Ideal.span {((PlaceTraceAdapter.prime F v).1 : v.adicCompletionIntegers F)} := by
    exact hu.is_generator
  have hm := IsLocalRing.map_maximalIdeal_of_surjective e.symm.toRingHom e.symm.surjective
  rw [hg, Ideal.map_span, Set.image_singleton] at hm
  simpa only [map_natCast, map_intCast, Int.cast_natCast] using hm.symm

private theorem base_span : (LocalConductor.base F v).maximalIdeal =
    Ideal.span {((PlaceTraceAdapter.prime F v).1 : (LocalConductor.base F v).valuationSubring)} := by
  have h := IsLocalRing.map_maximalIdeal_of_surjective (baseEquiv F v).toRingHom
    (baseEquiv F v).surjective
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton] at h
  simpa only [map_natCast] using h.symm

end LocalConductorProof

theorem localDifferent_eq_top_of_not_dvd_different
    (v : HeightOneSpectrum (𝓞 F))
    (hv : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    localDifferent F v = ⊤ := by
  let A := (LocalConductor.base F v).valuationSubring
  let B := (LocalConductor.target F v).valuationSubring
  letI : Module.Finite A B :=
    ValuedExtension.moduleFinite_target_valuationSubring_of_finite_separable
      (LocalConductor.base F v) (LocalConductor.target F v)
  haveI : Finite (IsLocalRing.ResidueField A) := by
    exact Finite.of_equiv (IsLocalRing.ResidueField ℤ_[PlaceTraceAdapter.prime F v])
      (IsLocalRing.ResidueField.mapEquiv (LocalConductorProof.baseEquiv F v)).toEquiv
  haveI : PerfectField (IsLocalRing.ResidueField A) := inferInstance
  have hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B := by
    change (LocalConductor.base F v).maximalIdeal.map (algebraMap A B) =
      (LocalConductor.target F v).maximalIdeal
    rw [LocalConductorProof.base_span F v, Ideal.map_span, Set.image_singleton, LocalConductorProof.target_span F v hv]
    simp only [map_natCast, map_intCast, Int.cast_natCast]
    rfl
  haveI : Algebra.FormallyUnramified A B := Algebra.FormallyUnramified.of_map_maximalIdeal hmap
  haveI : Algebra.IsUnramifiedAt A (IsLocalRing.maximalIdeal B) := inferInstance
  exact (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable_eq_top_iff_isUnramifiedAt
    (LocalConductor.base F v) (LocalConductor.target F v)).mpr inferInstance

end DedekindZetaZeroFree

end
