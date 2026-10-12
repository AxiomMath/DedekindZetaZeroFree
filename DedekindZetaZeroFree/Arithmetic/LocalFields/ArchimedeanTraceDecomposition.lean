module

public import DedekindZetaZeroFree.Adeles.Characters.ArchimedeanTraceCharacter

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

open NumberField

theorem archTrace_algebraMap {F : Type*} [Field F] [NumberField F]
    (v : InfinitePlace F) (t : F) :
    archTrace v (algebraMap F v.Completion t) =
      (v.mult : ℝ) * (v.embedding t).re := by
  rcases InfinitePlace.isReal_or_isComplex v with hv | hv
  · rw [archTrace_of_isReal v hv]
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    rw [InfinitePlace.Completion.algebraMap_apply]
    rw [show ((t : v.Completion)) =
        ((WithAbs.toAbs v.1 t : WithAbs v.1) : v.Completion) from rfl]
    rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
    simp only [WithAbs.equiv_apply, WithAbs.ofAbs_toAbs]
    rw [hv.mult_eq_one]
    rw [← InfinitePlace.embedding_of_isReal_apply hv t]
    simp only [Complex.ofReal_re]
    ring
  · rw [archTrace_of_isComplex v hv]
    rw [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
    rw [InfinitePlace.Completion.algebraMap_apply]
    rw [show ((t : v.Completion)) =
        ((WithAbs.toAbs v.1 t : WithAbs v.1) : v.Completion) from rfl]
    rw [InfinitePlace.Completion.extensionEmbedding_coe]
    simp only [WithAbs.equiv_apply, WithAbs.ofAbs_toAbs]
    rw [hv.mult_eq_two]
    ring

theorem trace_eq_sum_archTrace {F : Type*} [Field F] [NumberField F] (t : F) :
    (Algebra.trace ℚ F t : ℝ) =
      ∑ v : InfinitePlace F, archTrace v (algebraMap F v.Completion t) := by
  classical
  have htrace := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ) (x := t)
  have hre : (Algebra.trace ℚ F t : ℝ) = ∑ σ : F →ₐ[ℚ] ℂ, (σ t).re := by
    have := congrArg Complex.re htrace
    simpa using this
  rw [hre]

  have hsum : (∑ σ : F →ₐ[ℚ] ℂ, (σ t).re) = ∑ φ : F →+* ℂ, (φ t).re := by
    refine Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ).symm _ _ ?_
    intro σ
    simp
  rw [hsum]

  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := fun φ : F →+* ℂ => InfinitePlace.mk φ) (fun φ _ => Finset.mem_univ _)
      (fun φ : F →+* ℂ => (φ t).re)]
  apply Finset.sum_congr rfl
  intro v _

  have hfiber : ∀ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = v),
      (φ t).re = (v.embedding t).re := by
    intro φ hφ
    rw [Finset.mem_filter] at hφ
    have hmk : InfinitePlace.mk φ = InfinitePlace.mk (v.embedding) := by
      rw [InfinitePlace.mk_embedding]; exact hφ.2
    rcases (InfinitePlace.mk_eq_iff (K := F)).mp hmk with h | h
    · rw [h]
    · rw [← h, ComplexEmbedding.conjugate_coe_eq]
      simp [Complex.conj_re]
  have hcard : (Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = v)).card = v.mult :=
    InfinitePlace.card_filter_mk_eq v
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, hcard, nsmul_eq_mul]
  exact (archTrace_algebraMap v t).symm

end DedekindZetaZeroFree

end
