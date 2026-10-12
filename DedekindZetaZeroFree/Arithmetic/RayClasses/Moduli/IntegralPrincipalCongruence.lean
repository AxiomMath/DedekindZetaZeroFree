module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.FullModulusAndIntegralIdealUnits
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsRayCongruent
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayLocalHigherUnitMembership

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

open scoped WithZero
open WithZeroMulInt

private lemma loc_maximalIdeal_pow_mem_iff_exp (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
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

private lemma loc_valued_algebraMap_eq_intValuation (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (a : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletion F) =
      v.intValuation a := by
  have h1 : (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletion F) =
      (algebraMap (𝓞 F) F a : v.adicCompletion F) :=
    IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply (𝓞 F) F v a
  rw [h1, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
      (algebraMap (𝓞 F) F a),
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap v a]

private lemma loc_local_power_mem_iff
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (n : ℕ) (a : 𝓞 F) :
    algebraMap (𝓞 F) (v.adicCompletionIntegers F) a ∈
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ n ↔
      a ∈ v.asIdeal ^ n := by
  rw [loc_maximalIdeal_pow_mem_iff_exp v n, loc_valued_algebraMap_eq_intValuation]
  exact v.intValuation_le_pow_iff_mem a n

theorem integral_isRayCongruent (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (a : 𝓞 F) (ha : a ≠ 0) (ha1 : a - 1 ∈ m)
    (hpos : ∀ φ : F →+* ℝ, 0 < φ (a : F)) :
    ClassFieldTheory.IsRayCongruent (fullModulus m hm)
      (Units.mk0 (a : F) (by exact_mod_cast ha)) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    set n : ℕ := (fullModulus m hm).finitePart v with hn
    have hn_eq : n = (Associates.mk v.asIdeal).count (Associates.mk m).factors :=
      hn.trans (fullModulus_finitePart m hm v)
    have hn_pos : n ≠ 0 := by
      rw [hn]
      exact Finsupp.mem_support_iff.mp hv
    have hle : m ≤ v.asIdeal ^ n := by
      have h1 : m ≤ v.maxPowDividing m := by
        conv_lhs => rw [← Ideal.iInf_maxPowDividing_eq hm]
        exact iInf_le _ v
      rwa [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, ← hn_eq] at h1
    have hmem : a - 1 ∈ v.asIdeal ^ n := hle ha1
    let b : v.adicCompletionIntegers F := algebraMap (𝓞 F) (v.adicCompletionIntegers F) a
    have hb1 : b - 1 ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n := by
      have h := (loc_local_power_mem_iff v n (a - 1)).mpr hmem
      simpa [b] using h
    have hb1' : b - 1 ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
      Ideal.pow_le_self hn_pos hb1
    have hunit : IsUnit b := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      intro hb
      have h1mem : (1 : v.adicCompletionIntegers F) ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
        have h := sub_mem hb hb1'
        rwa [sub_sub_cancel] at h
      exact absurd isUnit_one (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal 1).mp h1mem))
    refine (ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff v n _).mpr
      ⟨hunit.unit, ?_, ?_⟩
    · apply Units.ext
      rw [Submonoid.val_unitsEquivUnitsType_symm_apply_coe, ClassFieldTheory.finitePlaceUnitEmbedding,
        Units.coe_map, Units.val_mk0, IsUnit.unit_spec,
        IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
      exact (IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) a).symm
    · rw [IsUnit.unit_spec]
      exact hb1
  · intro v _
    simpa using hpos (v.1.embedding_of_isReal v.2)

theorem principal_integral_span (a : 𝓞 F) (ha : a ≠ 0) :
    toPrincipalIdeal (𝓞 F) F (Units.mk0 (a : F) (by exact_mod_cast ha)) =
      integralIdealUnit (Ideal.span {a}) (mt Ideal.span_singleton_eq_bot.mp ha) := by
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  simp only [integralIdealUnit, Units.val_mk0, FractionalIdeal.coeIdeal_span_singleton]

end DedekindZetaZeroFree.LargeSieve.RayBridge

end
