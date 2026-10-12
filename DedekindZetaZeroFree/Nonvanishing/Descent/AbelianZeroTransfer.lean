module

public import DedekindZetaZeroFree.LFunctions.Dedekind.EntireAbelianQuotient
public import DedekindZetaZeroFree.LFunctions.Dedekind.ContinuationUniqueness

@[expose] public section

namespace DedekindZetaZeroFree

theorem product_nonvanishing_transfer (U V : Set ℂ) (fK fL g fF : ℂ → ℂ)
    (hVU : V ⊆ U) (hident : Set.EqOn fL fF U)
    (hprod : ∀ s ∈ U, fL s = g s * fK s)
    (hnz : ∀ s ∈ V, fF s ≠ 0) : ∀ s ∈ V, fK s ≠ 0 := by
  intro s hs hzero
  have hmem : s ∈ U := hVU hs
  have hfFzero : fF s = 0 := by
    rw [← hident hmem, hprod s hmem, hzero, mul_zero]
  exact hnz s hs hfFzero

theorem dedekindZeta_zeroFree_of_abelian_extension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (hcomm : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ)
    (α : ℝ) (fF : ℂ → ℂ)
    (hfF : DifferentiableOn ℂ fF ({1}ᶜ : Set ℂ))
    (hagF : ∀ s : ℂ, 1 < s.re → fF s = NumberField.dedekindZeta L s)
    (hnzF : ∀ s : ℂ, α < s.re → s ≠ 1 → fF s ≠ 0) :
    ∃ fK : ℂ → ℂ, DifferentiableOn ℂ fK ({1}ᶜ : Set ℂ) ∧
      (∀ s : ℂ, 1 < s.re → fK s = NumberField.dedekindZeta K s) ∧
      ∀ s : ℂ, α < s.re → s ≠ 1 → fK s ≠ 0 := by
  obtain ⟨fK, fL, g, hfK, hfL, _hg, hagK, hagL, hprod⟩ := DedekindZetaZeroFree.dedekindAbelianQuotient K L hcomm

  have hagree : ∀ s : ℂ, 1 < s.re → fL s = fF s := by
    intro s hs
    rw [hagL s hs, hagF s hs]
  have hident : Set.EqOn fL fF ({1}ᶜ : Set ℂ) :=
    continuation_unique_off_one fL fF hfL hfF hagree
  refine ⟨fK, hfK, hagK, ?_⟩
  intro s hs hsne
  exact product_nonvanishing_transfer ({1}ᶜ : Set ℂ) {s : ℂ | α < s.re ∧ s ≠ 1}
    fK fL g fF (fun t ht => ht.2) hident
    (fun t ht => hprod t ht) (fun t ht => hnzF t ht.1 ht.2) s ⟨hs, hsne⟩

end DedekindZetaZeroFree
