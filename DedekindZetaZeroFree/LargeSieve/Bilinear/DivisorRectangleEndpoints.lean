module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.Errors.LargeDualRectangles
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Errors.MiddleDirectKernelBounds
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Errors.MiddleDualBounds

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

namespace RectangleEndpoints

theorem row_endpoints (C : Context Q) (hK : 1 ≤ C.K) (B : ℝ) :
    C.originalRows 1 true = {⊤} ∧
    C.reflectedCoreRows 1 true = {⊤} ∧
    C.reflectedRows 1 true = squarefreeBadPool c ∧
    C.reflectedTopRows = {⊤} ∧
    C.reflectedRows 1 true = C.reflectedTopRows ∪ C.reflectedSupportedUnitRows ∧
    Disjoint C.reflectedTopRows C.reflectedSupportedUnitRows ∧
    C.originalRows B false =
      (Sieve.paperShell F (c * C.d) B).filter (fun a => norm a ≤ C.K) ∧
    C.reflectedCoreRows B false =
      (Sieve.paperShell F c B).filter (fun a => norm a ≤ C.K) := by
  have hunit (m : Ideal (𝓞 F)) : ReflectedSigma4.unitRows c m C.K = {⊤} := by
    have hk : Sieve.squarefreeKernel (⊤ : Ideal (𝓞 F)) = ⊤ :=
      Sieve.squarefreeKernel_eq_self (by simpa only [← Ideal.one_eq_top] using squarefree_one)
    have hsc : sc c (⊤ : Ideal (𝓞 F)) = 1 := by
      unfold sc primeToSquarefreeKernel
      rw [hk, ← Ideal.one_eq_top, UniqueFactorizationMonoid.normalizedFactors_one]
      simp
    simp [ReflectedSigma4.unitRows, hsc, hK,
      show Squarefree (⊤ : Ideal (𝓞 F)) from by simpa only [← Ideal.one_eq_top] using squarefree_one]
  have hsf : ∀ a ∈ squarefreeBadPool c, a ≠ ⊥ ∧ Squarefree a := by
    intro a ha
    exact ((mem_squarefreeBadPool C.D.original_ne_bot).mp ha).imp_right (fun h => h.1)
  have hrows : C.reflectedRows 1 true = squarefreeBadPool c := by
    ext a
    simp only [Context.reflectedRows, Context.reflectedRowIndices, Context.reflectedCoreRows,
      Bool.true_eq, ↓reduceIte, hunit, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨t,r⟩, ⟨⟨ht, hr⟩, hrest⟩, he⟩
      dsimp at hr he
      subst r
      simpa only [Ideal.mul_top] using he ▸ (show t * ⊤ ∈ squarefreeBadPool c by simpa using ht)
    · intro ha
      obtain ⟨ha0, hasf⟩ := hsf a ha
      refine ⟨(a, ⊤), ⟨⟨ha, rfl⟩, ?_⟩, ?_⟩ <;> simp [hasf, ha0]
  have htop : (⊤ : Ideal (𝓞 F)) ∈ squarefreeBadPool c := by
    simp only [squarefreeBadPool, Finset.mem_image]
    exact ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _), by simp⟩
  have ht : C.reflectedTopRows = {⊤} := by
    ext a
    simp only [Context.reflectedTopRows, hrows, Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => by subst a; exact ⟨htop, rfl⟩⟩
  refine ⟨by simp [Context.originalRows, hunit], by simp [Context.reflectedCoreRows, hunit],
    hrows, ht, ?_, ?_, rfl, rfl⟩
  · ext a
    simp only [Context.reflectedTopRows, Context.reflectedSupportedUnitRows,
      Finset.mem_union, Finset.mem_filter]
    tauto
  · apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2

end RectangleEndpoints

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

end
