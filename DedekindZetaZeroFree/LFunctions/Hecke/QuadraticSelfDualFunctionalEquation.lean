module

public import DedekindZetaZeroFree.LFunctions.Hecke.IdealSeriesAndContinuationWitnesses

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {f : Ideal (𝓞 F)} {η : DedekindZetaZeroFree.RayClassCharacter F f}

private lemma conj_eq_self_of_cube_eq_self {z : ℂ} (h : z ^ 3 = z) :
    (starRingEnd ℂ) z = z := by
  have hfac : z * (z - 1) * (z + 1) = z ^ 3 - z := by ring
  have hzero : z * (z - 1) * (z + 1) = 0 := by rw [hfac, sub_eq_zero.mpr h]
  rcases mul_eq_zero.mp hzero with h' | h'
  · rcases mul_eq_zero.mp h' with h' | h'
    · rw [h']; simp
    · rw [sub_eq_zero.mp h']; simp
  · rw [add_eq_zero_iff_eq_neg.mp h']; simp

theorem rayClassCharacter_conj_of_cube_eq_self
    (hη : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I) :
    ∀ I : Ideal (𝓞 F), (starRingEnd ℂ) (η I) = η I :=
  fun I => conj_eq_self_of_cube_eq_self (hη I)

theorem EntireHeckeWitness.dual_eq_self (w : EntireHeckeWitness η)
    (hη : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I) :
    w.Λdual = w.Λ := by
  have hconj := rayClassCharacter_conj_of_cube_eq_self hη

  have hhalf : ∀ s : ℂ, 1 < s.re → w.Λdual s = w.Λ s := by
    intro s hs
    have hterms : (fun I : Ideal (𝓞 F) =>
        heckeCompletionFactor F f s *
          ((starRingEnd ℂ) (η I) * (Ideal.absNorm I : ℂ) ^ (-s)))
        = (fun I : Ideal (𝓞 F) =>
        heckeCompletionFactor F f s * (η I * (Ideal.absNorm I : ℂ) ^ (-s))) := by
      funext I
      rw [hconj I]
    exact (hterms ▸ w.hasSum_dual s hs).unique (w.hasSum s hs)

  funext s
  have hU : ∀ᶠ z in 𝓝 (2 : ℂ), 1 < z.re := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact hopen.mem_nhds (by norm_num [Complex.ofReal_re])
  have hfg : w.Λdual =ᶠ[𝓝 (2 : ℂ)] w.Λ := hU.mono (fun z hz => hhalf z hz)
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr w.differentiable_dual)
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr w.differentiable)
    isPreconnected_univ (Set.mem_univ 2) hfg
  exact heq (Set.mem_univ s)

theorem EntireHeckeWitness.selfdual_functionalEquation (w : EntireHeckeWitness η)
    (hη : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I) :
    ∀ s : ℂ, w.Λ s = w.W * w.Λ (1 - s) := by
  intro s
  rw [w.functionalEquation s, congrFun (w.dual_eq_self hη) (1 - s)]

end DedekindZetaZeroFree.LargeSieve
