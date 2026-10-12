module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.ResiduePhases.ResidueTracePhases
public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceCharacterConductor

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain LocalFieldTheory WithZero
open ValuationTheory.DiscreteValuationField
open scoped ValuativeRel nonZeroDivisors

namespace DedekindZetaZeroFree.ArithmeticContext
noncomputable section
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]

private theorem primeBelow_eq_adapter (v : HeightOneSpectrum (𝓞 F)) :
    ResidueTrace.rationalPrimeBelow v = PlaceTraceAdapter.prime F v := by
  apply Subtype.ext
  change ringChar (𝓞 F ⧸ v.asIdeal) = _
  apply CharP.ringChar_of_prime_eq_zero (PlaceTraceAdapter.prime F v).2
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have h : ((PlaceTraceAdapter.prime F v).1 : 𝓞 ℚ) ∈
      (PlaceTraceAdapter.rationalPlace F v).asIdeal := by
    have hgen := Rat.HeightOneSpectrum.natGenerator_dvd_iff
      (PlaceTraceAdapter.rationalPlace F v) (n := (PlaceTraceAdapter.prime F v).1)
    have hh := hgen.mp (dvd_refl _)
    rw [Ideal.mem_map_iff_of_surjective _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).surjective] at hh
    obtain ⟨x, hx, he⟩ := hh
    have he' : x = ((PlaceTraceAdapter.prime F v).1 : 𝓞 ℚ) :=
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).injective (by simpa using he)
    exact he' ▸ hx
  have h' : (algebraMap (𝓞 ℚ) (𝓞 F) ((PlaceTraceAdapter.prime F v).1 : 𝓞 ℚ)) ∈ v.asIdeal := h
  simpa using h'

private theorem character_eq_adapter (v : HeightOneSpectrum (𝓞 F)) :
    ResidueTrace.localTraceCharacter v = localFiniteCharacter F v := by
  letI (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩
  have hp := primeBelow_eq_adapter v
  have hgeneral (p : Nat.Primes) (m : ℚ_[p] →+* v.adicCompletion F)
      (hmc : Continuous m)
      (hmq : ∀ q : ℚ, m (q : ℚ_[p]) =
        algebraMap F (v.adicCompletion F) (algebraMap ℚ F q))
      (hp : p = PlaceTraceAdapter.prime F v) :
      (letI := m.toAlgebra
       (rationalPadicCharacter p).compAddMonoidHom
        (Algebra.trace ℚ_[p] (v.adicCompletion F)).toAddMonoidHom) = localFiniteCharacter F v := by
    subst p
    have hmap : m = PlaceTraceAdapter.padicMap F v := by
      apply DFunLike.coe_injective
      apply (Padic.denseRange_ratCast (PlaceTraceAdapter.prime F v)).equalizer hmc
      · letI : Algebra ℚ ((PlaceTraceAdapter.rationalPlace F v).adicCompletion ℚ) :=
          HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ _
        exact (finitePlaceAdicCompletionMap_continuous ℚ F _ _).comp
          (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (PlaceTraceAdapter.rationalPlace F v)).symm.continuous
      · funext q
        exact (hmq q).trans (by simp [PlaceTraceAdapter.padicMap, map_ratCast])
    subst m
    rfl
  exact hgeneral _ _ (ResidueTrace.baseEmbedding_spec v).1
    (ResidueTrace.baseEmbedding_spec v).2 hp

private theorem codifferent_eq_integers_of_good (v : HeightOneSpectrum (𝓞 F))
    (hv : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    (localCodifferent F v : Set (v.adicCompletion F)) =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  rw [localCodifferent_eq_inverse_different, localDifferent_eq_top_of_not_dvd_different F v hv,
    IsLocalization.coeSubmodule_top]
  have hdiv : (1 : Submodule (LocalConductor.target F v).valuationSubring (v.adicCompletion F)) / 1 = 1 := by
    ext x
    rw [Submodule.mem_div_iff_forall_mul_mem]
    constructor
    · intro h
      simpa using h 1 (by simp)
    · intro h y hy
      simpa using Submodule.mul_mem_mul h hy
  rw [hdiv]
  ext x
  change x ∈ (1 : Submodule (LocalConductor.target F v).valuationSubring (v.adicCompletion F)) ↔ _
  rw [Submodule.mem_one]
  change (∃ z : (LocalConductor.target F v).valuationSubring, (z : v.adicCompletion F) = x) ↔ _
  rw [← LocalConductor.target_integerRing_eq F v]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ z.property, fun h => ⟨⟨x,h⟩,rfl⟩⟩

private theorem actual_selfDual_of_good (v : HeightOneSpectrum (𝓞 F))
    (hv : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) : ResidueTrace.IsSelfDual v := by
  intro x
  rw [character_eq_adapter]
  change (∀ o : v.adicCompletionIntegers F, localFiniteCharacter F v (x * o) = 1) ↔ _
  have hcod := codifferent_eq_integers_of_good v hv
  change (∀ o : v.adicCompletionIntegers F, localFiniteCharacter F v (x * o) = 1) ↔ x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  rw [← hcod]
  change (∀ o : v.adicCompletionIntegers F, localFiniteCharacter F v (x * o) = 1) ↔ x ∈ localCodifferent F v
  unfold localCodifferent
  rw [RamificationTheory.DiscreteValuationField.ValuedExtension.mem_codifferentSubmodule_iff_trace_mul_integral_of_finite_separable]
  have ha (a : v.adicCompletion F) : a ∈ (1 : Submodule (LocalConductor.target F v).valuationSubring (v.adicCompletion F)) ↔
      a ∈ v.adicCompletionIntegers F := by
    rw [Submodule.mem_one]
    change (∃ z : (LocalConductor.target F v).valuationSubring, (z : v.adicCompletion F) = a) ↔ a ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    rw [← LocalConductor.target_integerRing_eq F v]
    exact ⟨fun ⟨z, hz⟩ => hz ▸ z.property, fun h => ⟨⟨a,h⟩,rfl⟩⟩
  have hb (t : ℚ_[PlaceTraceAdapter.prime F v]) :
      IsIntegral (LocalConductor.base F v).valuationSubring t ↔
        rationalPadicCharacter (PlaceTraceAdapter.prime F v) t = 1 := by
    rw [rationalPadicCharacter_eq_one_iff, IsIntegrallyClosed.isIntegral_iff]
    change (∃ z : (LocalConductor.base F v).valuationSubring, (z : ℚ_[PlaceTraceAdapter.prime F v]) = t) ↔ ∃ z : ℤ_[PlaceTraceAdapter.prime F v], (z : ℚ_[PlaceTraceAdapter.prime F v]) = t
    have hmem (z : ℚ_[PlaceTraceAdapter.prime F v]) : z ∈ (LocalConductor.base F v).valuation.valuationSubring ↔ ‖z‖ ≤ 1 := by
      change (LocalConductor.base F v).valuation z ≤ 1 ↔ _
      simp only [LocalConductor.base, localCompleteDVF_valuation_eq]
      exact LocalFieldTheory.Padic.integer_mem_iff_norm_le_one _ z
    exact ⟨fun ⟨z,hz⟩ => ⟨⟨z, (hmem z).mp z.property⟩,hz⟩,
      fun ⟨z,hz⟩ => ⟨⟨z, (hmem z).mpr z.property⟩,hz⟩⟩
  simp only [ha, hb]
  constructor
  · intro h a ha
    exact h ⟨a, ha⟩
  · intro h o
    exact h o o.property

theorem exists_trace_exclusion_set (F : Type) [Field F] [NumberField F] :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ v : HeightOneSpectrum (𝓞 F), v ∉ T → ResidueTrace.IsSelfDual v := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ differentIdeal ℤ (𝓞 F)}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  refine ⟨hfin.toFinset, ?_⟩
  intro v hv
  exact actual_selfDual_of_good v (by simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hv)

end
end DedekindZetaZeroFree.ArithmeticContext
