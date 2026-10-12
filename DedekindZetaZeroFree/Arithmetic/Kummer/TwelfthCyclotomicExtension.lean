module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import DedekindZetaZeroFree.Arithmetic.Kummer.TwelfthRootsTotallyComplex

@[expose] public section

namespace DedekindZetaZeroFree

theorem cyclotomic12_context (K : Type) [Field K] [NumberField K] :
    IsGalois K (CyclotomicField 12 K) ∧
      (∀ σ τ : CyclotomicField 12 K ≃ₐ[K] CyclotomicField 12 K,
        σ * τ = τ * σ) ∧
      NumberField.IsTotallyComplex (CyclotomicField 12 K) ∧
      (∃ ζ : CyclotomicField 12 K, IsPrimitiveRoot ζ 12 ∧
        ∀ x : CyclotomicField 12 K, x ^ 12 = 1 →
          ∃ j : ℕ, j < 12 ∧ x = ζ ^ j) := by
  haveI : IsCyclotomicExtension {12} K (CyclotomicField 12 K) := inferInstance
  haveI : IsMulCommutative (CyclotomicField 12 K ≃ₐ[K] CyclotomicField 12 K) :=
    IsCyclotomicExtension.isMulCommutative {12} K (CyclotomicField 12 K)
  obtain ⟨ζ, hζ⟩ :=
    (inferInstance : IsCyclotomicExtension {12} K (CyclotomicField 12 K)).exists_isPrimitiveRoot
      (Set.mem_singleton 12) (by norm_num)
  refine ⟨IsCyclotomicExtension.isGalois (S := {12}) (K := K) (L := CyclotomicField 12 K),
    ?_, primitive12_totallyComplex (CyclotomicField 12 K) ζ hζ, ⟨ζ, hζ, ?_⟩⟩
  · intro σ τ
    exact mul_comm' σ τ
  · intro x hx
    obtain ⟨j, hj, hjx⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact ⟨j, hj, hjx.symm⟩

end DedekindZetaZeroFree
