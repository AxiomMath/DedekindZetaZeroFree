module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

open scoped NumberField
open IsDedekindDomain HeightOneSpectrum WithZero

namespace DedekindZetaZeroFree.AbelianQuotient

private theorem irreducibleValuedAdicCompletion_eq
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ϖ : v.adicCompletionIntegers K)
    (h : Irreducible ϖ) :
    Valued.v (ϖ : v.adicCompletion K) = exp (-1 : ℤ) := by
  have hv := adicCompletionIntegers.integers (K := K) (v := v)
  have hlt : Valued.v (ϖ : v.adicCompletion K) < 1 := hv.valuation_irreducible_lt_one h
  have hpos : 0 < Valued.v (ϖ : v.adicCompletion K) := hv.valuation_irreducible_pos h
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have hy_val'' : v.valuation K (algebraMap (𝓞 K) K π) = exp (-1 : ℤ) := by
    rw [valuation_of_algebraMap, hπ]
  have hy_val' : Valued.v
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) π : v.adicCompletion K) = exp (-1 : ℤ) := by
    rw [algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation']
    exact hy_val''
  have hy_mem : algebraMap (𝓞 K) (v.adicCompletionIntegers K) π ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have h1 := hv.isUnit_iff_valuation_eq_one.mp hunit
    rw [show algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
          (algebraMap (𝓞 K) (v.adicCompletionIntegers K) π)
          = (algebraMap (𝓞 K) (v.adicCompletionIntegers K) π : v.adicCompletion K)
          from rfl] at h1
    rw [hy_val'] at h1
    have h2 : (-1 : ℤ) = 0 := exp_inj.mp (h1.trans exp_zero.symm)
    norm_num at h2
  have hmax := hv.maximalIdeal_eq_setOfPred_le_v_algebraMap h
  have hle1 : exp (-1 : ℤ) ≤ Valued.v (ϖ : v.adicCompletion K) := by
    have : algebraMap (𝓞 K) (v.adicCompletionIntegers K) π ∈
        {y : v.adicCompletionIntegers K |
          Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) y) ≤
            Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ)} := by
      rw [← hmax]
      exact hy_mem
    simpa [hy_val''] using this
  have hle2 : Valued.v (ϖ : v.adicCompletion K) ≤ exp (-1 : ℤ) := by
    have hne : Valued.v (ϖ : v.adicCompletion K) ≠ 0 := ne_of_gt hpos
    have hloglt : log (Valued.v (ϖ : v.adicCompletion K)) < 0 := by
      rw [← exp_lt_one_iff, exp_log hne]
      exact hlt
    have hlogle : log (Valued.v (ϖ : v.adicCompletion K)) ≤ -1 := by omega
    calc Valued.v (ϖ : v.adicCompletion K)
        = exp (log (Valued.v (ϖ : v.adicCompletion K))) := (exp_log hne).symm
      _ ≤ exp (-1 : ℤ) := by rw [exp_le_exp]; exact hlogle
  exact le_antisymm hle2 hle1

theorem completionIdealPowerPullback
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (n : ℕ) :
    algebraMap (𝓞 K) (v.adicCompletionIntegers K) r ∈
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n ↔
      r ∈ v.asIdeal ^ n := by
  have hv := adicCompletionIntegers.integers (K := K) (v := v)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hval : Valued.v (ϖ : v.adicCompletion K) = exp (-1 : ℤ) :=
    irreducibleValuedAdicCompletion_eq K v ϖ hϖ
  have hexp : exp (-1 : ℤ) ^ n = exp (-(n : ℤ)) := by
    rw [← exp_nsmul]
    congr 1
    simp
  have hL : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) r)) = v.intValuation r := by
    rw [show algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
          (algebraMap (𝓞 K) (v.adicCompletionIntegers K) r)
          = (algebraMap (𝓞 K) (v.adicCompletionIntegers K) r : v.adicCompletion K) from rfl,
      algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation',
      valuation_of_algebraMap]
  have hR : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) =
      exp (-1 : ℤ) := by
    rw [show algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ
          = (ϖ : v.adicCompletion K) from rfl]
    exact hval
  rw [← SetLike.mem_coe, hv.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow hϖ n]
  simp only [Set.mem_setOf_eq, hL, hR, hexp]
  exact intValuation_le_pow_iff_mem v r n

end DedekindZetaZeroFree.AbelianQuotient
