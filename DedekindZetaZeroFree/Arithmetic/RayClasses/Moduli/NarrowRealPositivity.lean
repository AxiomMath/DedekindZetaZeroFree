module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.IntegralIdealClasses

@[expose] public section

open scoped NumberField
open NumberField

namespace DedekindZetaZeroFree.AbelianQuotient

theorem narrowRayRealPositivity
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (y : K) :
    (∀ v, v ∈ (narrowIdealModulus K m hm).infinitePart →
      0 < v.1.embedding_of_isReal v.2 y) ↔
    (∀ φ : K →+* ℝ, 0 < φ y) := by
  classical
  constructor
  · intro h φ
    let ψ : K →+* ℂ := Complex.ofRealHom.comp φ
    have hψ : ComplexEmbedding.IsReal ψ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      simp [ψ, ComplexEmbedding.conjugate_coe_eq]
    have hw : (InfinitePlace.mk ψ).IsReal := InfinitePlace.isReal_mk_iff.mpr hψ
    have hpos := h ⟨InfinitePlace.mk ψ, hw⟩
      (by rw [narrowIdealModulus_infinitePart]; exact Finset.mem_univ _)
    have hemb : (InfinitePlace.mk ψ).embedding_of_isReal hw = φ := by
      ext x
      apply Complex.ofReal_injective
      rw [InfinitePlace.embedding_of_isReal_apply,
        InfinitePlace.embedding_mk_eq_of_isReal hψ]
      rfl
    rwa [hemb] at hpos
  · intro h v _
    exact h (v.1.embedding_of_isReal v.2)

end DedekindZetaZeroFree.AbelianQuotient
