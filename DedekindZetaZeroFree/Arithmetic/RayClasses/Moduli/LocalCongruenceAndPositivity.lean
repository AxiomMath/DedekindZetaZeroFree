module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.FullModulusAndIntegralIdealUnits
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsRayCongruent
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayLocalHigherUnitOneAdd

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical WithZero
open WithZeroMulInt
open NumberField

variable {F : Type*} [Field F] [NumberField F]

private lemma maximalIdeal_pow_mem_iff_exp (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (n : ℕ) (y : v.adicCompletionIntegers F) :
    y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n ↔
      Valued.v (y : v.adicCompletion F) ≤ WithZero.exp (-(n : ℤ)) := by
  haveI : IsDiscreteValuationRing (v.adicCompletionIntegers F) := inferInstance
  haveI hw : ((Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).IsRankOneDiscrete := inferInstance
  let O := v.adicCompletionIntegers F
  let ϖ : O := Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal O)
  have hspan : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (Ideal.span_singleton_generator _).symm
  have hunif : Valuation.IsUniformizer (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) ϖ :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span
      (v := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)) hspan
  have hsurj : Function.Surjective (Valued.v : v.adicCompletion F → ℤᵐ⁰) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective F v
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hspan
  have hval : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [Valuation.IsUniformizer.iff.mp hunif,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (v := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)) hsurj, Units.val_mk0]
  have hvint := IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers F v
  rw [← SetLike.mem_coe,
    Valuation.Integers.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow
      (v := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)) hvint hirr n]
  simp only [Set.mem_setOf_eq]
  have hval' : (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)
      (algebraMap O (v.adicCompletion F) ϖ) = WithZero.exp (-1 : ℤ) := by
    simpa using hval
  rw [hval']
  have hpow : (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) ^ n = WithZero.exp (-(n : ℤ)) := by
    rw [← WithZero.exp_nsmul, nsmul_eq_mul]
    norm_num
  rw [hpow]
  simp

private lemma valued_algebraMap_eq_intValuation (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (a : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletion F) =
      v.intValuation a := by
  have h1 : (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletion F) =
      (algebraMap (𝓞 F) F a : v.adicCompletion F) :=
    IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply (𝓞 F) F v a
  rw [h1, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
      (algebraMap (𝓞 F) F a),
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap v a]

private lemma local_power_mem_iff
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (n : ℕ) (a : 𝓞 F) :
    algebraMap (𝓞 F) (v.adicCompletionIntegers F) a ∈
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ n ↔
      a ∈ v.asIdeal ^ n := by
  rw [maximalIdeal_pow_mem_iff_exp v n, valued_algebraMap_eq_intValuation]
  exact v.intValuation_le_pow_iff_mem a n

theorem ray_congruent_sub_mem (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (x : Fˣ) (hx : ClassFieldTheory.IsRayCongruent (fullModulus m hm) x)
    (a b : 𝓞 F) (hab : (a : F) = (x : F) * (b : F)) :
    a - b ∈ m := by
  rw [← Ideal.iInf_maxPowDividing_eq hm, Ideal.mem_iInf]
  intro v
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing]
  let n : ℕ := (Associates.mk v.asIdeal).count (Associates.mk m).factors
  change a - b ∈ v.asIdeal ^ n
  by_cases hn : n = 0
  · rw [hn, pow_zero]
    simp
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hfp : (fullModulus m hm).finitePart v = n := rfl
    have hsupp : v ∈ (fullModulus m hm).finitePart.support := by
      rw [Finsupp.mem_support_iff, hfp]
      exact hn
    have hlocal := hx.1 v hsupp
    rw [hfp] at hlocal
    obtain ⟨t, ht, hxeq⟩ :=
      (ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff_exists_one_add v n hn1
        (ClassFieldTheory.finitePlaceUnitEmbedding v x)).mp hlocal
    rw [← local_power_mem_iff v n (a - b)]
    have hxe : algebraMap F (v.adicCompletion F) (x : F) = 1 + (t : v.adicCompletion F) := by
      have h1 : algebraMap F (v.adicCompletion F) (x : F) =
          ((ClassFieldTheory.finitePlaceUnitEmbedding v x : (v.adicCompletion F)ˣ) :
            v.adicCompletion F) := by
        simp [ClassFieldTheory.finitePlaceUnitEmbedding]
      rw [h1, hxeq]
      simp
    have hG : (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (a - b) : v.adicCompletion F) =
        (algebraMap (𝓞 F) (v.adicCompletionIntegers F) b : v.adicCompletion F) *
          (t : v.adicCompletion F) := by
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
        IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
        map_sub (algebraMap (𝓞 F) F) a b]
      show algebraMap F (v.adicCompletion F) ((a : F) - (b : F)) =
        algebraMap F (v.adicCompletion F) (b : F) * (t : v.adicCompletion F)
      rw [hab, map_sub, map_mul, hxe]
      ring
    have hEq : algebraMap (𝓞 F) (v.adicCompletionIntegers F) (a - b) =
        algebraMap (𝓞 F) (v.adicCompletionIntegers F) b * t := by
      apply Subtype.ext
      rw [hG]
      simp
    rw [hEq]
    exact Ideal.mul_mem_left _ _ ht

theorem ray_congruent_pos (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (x : Fˣ) (hx : ClassFieldTheory.IsRayCongruent (fullModulus m hm) x) :
    ∀ φ : F →+* ℝ, 0 < φ (x : F) := by
  intro φ
  let ψ : F →+* ℂ := Complex.ofRealHom.comp φ
  have hψ : ComplexEmbedding.IsReal ψ := by
    rw [ComplexEmbedding.isReal_iff]
    ext s
    simp [RingHom.star_apply, ψ, Complex.conj_ofReal]
  let w : InfinitePlace F := InfinitePlace.mk ψ
  have hw : w.IsReal := ⟨ψ, hψ, rfl⟩
  have hpos := hx.2 ⟨w, hw⟩ (Finset.mem_univ _)
  have hconv : InfinitePlace.embedding_of_isReal hw (x : F) = φ (x : F) := by
    apply Complex.ofReal_injective
    rw [InfinitePlace.embedding_of_isReal_apply]
    have hwemb : w.embedding = ψ := InfinitePlace.embedding_mk_eq_of_isReal hψ
    rw [hwemb]
    rfl
  rwa [hconv] at hpos

end DedekindZetaZeroFree.LargeSieve.RayBridge

end
