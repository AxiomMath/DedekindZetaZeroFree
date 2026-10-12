module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.CompletionIdealPowerPullback
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsRayCongruent
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayLocalHigherUnitOneAdd

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.AbelianQuotient

theorem localIntegralRayCongruence
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 1 ≤ n) (a : 𝓞 K) (ha : (a : K) ≠ 0) :
    ClassFieldTheory.finitePlaceUnitEmbedding v (Units.mk0 (a : K) ha) ∈
        ClassFieldTheory.rayLocalHigherUnitGroup v n ↔
      a - 1 ∈ v.asIdeal ^ n := by
  rw [ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff_exists_one_add v n hn]
  have himage :
      ((ClassFieldTheory.finitePlaceUnitEmbedding v (Units.mk0 (a : K) ha)) :
        v.adicCompletion K) =
      ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) : v.adicCompletion K) := by
    rfl
  constructor
  · rintro ⟨t, ht, heq⟩
    have heq' : algebraMap (𝓞 K) (v.adicCompletionIntegers K) a = 1 + t := by
      apply Subtype.ext
      exact himage.symm.trans heq
    have hsub : algebraMap (𝓞 K) (v.adicCompletionIntegers K) (a - 1) = t := by
      rw [map_sub, map_one, heq']
      ring
    apply (completionIdealPowerPullback K v (a - 1) n).mp
    rw [hsub]
    exact ht
  · intro ha'
    refine ⟨algebraMap (𝓞 K) (v.adicCompletionIntegers K) (a - 1),
      (completionIdealPowerPullback K v (a - 1) n).mpr ha', ?_⟩
    rw [himage]
    congr 1
    rw [map_sub, map_one]
    ring

theorem valuation_le_one_of_localRayCongruence
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ) (x : Kˣ)
    (hx : ClassFieldTheory.finitePlaceUnitEmbedding v x ∈
      ClassFieldTheory.rayLocalHigherUnitGroup v n) :
    v.valuation K (x : K) ≤ 1 := by
  obtain ⟨y, hxy, _⟩ :=
    (ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff v n
      (ClassFieldTheory.finitePlaceUnitEmbedding v x)).mp hx
  have hval := congrArg Units.val hxy
  change ((y : v.adicCompletionIntegers K) : v.adicCompletion K) =
    algebraMap K (v.adicCompletion K) (x : K) at hval
  have hmem : algebraMap K (v.adicCompletion K) (x : K) ∈
      v.adicCompletionIntegers K := by
    rw [← hval]
    exact (y : v.adicCompletionIntegers K).property
  have hle := (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
    (𝓞 K) K v).mp hmem
  change Valued.v ((x : K) : v.adicCompletion K) ≤ 1 at hle
  rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hle

end DedekindZetaZeroFree.AbelianQuotient
