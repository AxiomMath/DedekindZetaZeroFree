module

public import DedekindZetaZeroFree.LFunctions.Dedekind.HolomorphicContinuation
public import DedekindZetaZeroFree.LFunctions.Hecke.RayCharacterEntireContinuation
public import DedekindZetaZeroFree.LFunctions.Dedekind.AbelianRayCharacterFactorization

@[expose] public section

namespace DedekindZetaZeroFree

open scoped NumberField

theorem dedekindAbelianQuotient :
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) →
    ∃ fK fL g : ℂ → ℂ,
      DifferentiableOn ℂ fK ({1}ᶜ : Set ℂ) ∧ DifferentiableOn ℂ fL ({1}ᶜ : Set ℂ) ∧
      Differentiable ℂ g ∧
      (∀ s : ℂ, 1 < s.re → fK s = NumberField.dedekindZeta K s) ∧
      (∀ s : ℂ, 1 < s.re → fL s = NumberField.dedekindZeta L s) ∧
      ∀ s : ℂ, s ≠ 1 → fL s = g s * fK s := by
  intro K L _ _ _ _ _ _ hcomm
  obtain ⟨fK, hfK, hfKeq⟩ := AbelianQuotient.zetaContinuation K
  obtain ⟨fL, hfL, hfLeq⟩ := AbelianQuotient.zetaContinuation L
  obtain ⟨n, m, χ, hmχ, hfac⟩ := AbelianQuotient.abelianFactorization K L hcomm
  choose F hFdiff hFsum using fun i =>
    AbelianQuotient.rayCharacterEntire K (m i) (hmχ i).1 (χ i) (hmχ i).2
  let g : ℂ → ℂ := fun s => ∏ i, F i s
  have hg : Differentiable ℂ g := by
    simpa only [g] using
      (Differentiable.fun_finsetProd (u := Finset.univ) fun i _ => hFdiff i)
  refine ⟨fK, fL, g, hfK, hfL, hg, hfKeq, hfLeq, ?_⟩
  intro s hs
  have hmain : Set.EqOn fL (fun s => g s * fK s) ({1}ᶜ : Set ℂ) := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ) ?_ ?_ ?_ (z₀ := 2) ?_ ?_
    · exact hfL.analyticOnNhd isOpen_compl_singleton
    · exact (hg.differentiableOn.mul hfK).analyticOnNhd isOpen_compl_singleton
    · exact (isConnected_compl_singleton_of_one_lt_rank
        (by rw [Complex.rank_real_complex]; norm_num) (1 : ℂ)).isPreconnected
    · simp
    · refine Filter.eventually_of_mem
        ((Complex.continuous_re.isOpen_preimage (Set.Ioi 1) isOpen_Ioi).mem_nhds
          (by simp : 1 < (2 : ℂ).re)) fun s hs => ?_
      change fL s = g s * fK s
      have hg_eq : g s =
          ∏ i : Fin n, ∑' I : Ideal (𝓞 K), χ i I * (Ideal.absNorm I : ℂ) ^ (-s) := by
        simp only [g]
        exact Finset.prod_congr rfl fun i _ => (hFsum i s hs).tsum_eq.symm
      rw [hfLeq s hs, hfKeq s hs, hfac s hs, hg_eq]
  exact hmain (by simpa using hs)

end DedekindZetaZeroFree
