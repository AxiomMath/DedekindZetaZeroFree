module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleRangeBoundaryCases
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.ThetaDiagonalGramBound
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.SameClassOffDiagonalGram
public import DedekindZetaZeroFree.LargeSieve.Exponents.GramBoundsToExponentTwo

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

theorem initialBound (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (c : Ideal (𝓞 F))
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
     :
    HasSieveExponent F c Q (2 : ℝ) := by
  by_cases hc : c = ⊥
  ·

    subst hc
    intro ε hε
    refine ⟨0, le_refl 0, ?_⟩
    intro M N hM hN
    have hshellM : paperShell F ⊥ M = ∅ := paperShell_bot_eq_empty F M hM
    have hshellN : paperShell F ⊥ N = ∅ := paperShell_bot_eq_empty F N hN
    have hQ1 : ∀ lam : Ideal (𝓞 F) → ℂ, Q1 F ⊥ Q M N lam = 0 := by
      intro lam
      simp [Q1, hshellM]
    have henergy : ∀ lam : Ideal (𝓞 F) → ℂ, energy F ⊥ N lam = 0 := by
      intro lam
      simp [energy, hshellN]
    have hset : ({0} ∪ {x : ℝ | ∃ lam : Ideal (𝓞 F) → ℂ,
        energy F ⊥ N lam ≤ 1 ∧ x = Q1 F ⊥ Q M N lam}) = {0} := by
      ext x
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
      constructor
      · rintro (h | ⟨lam, -, rfl⟩)
        · exact h
        · rw [hQ1 lam]
      · exact Or.inl
    rw [B1, hset, csSup_singleton]
    simp
  ·

    obtain ⟨D, hD, hdiag⟩ := initialGram_diagonal_bound F
    refine initial_gram_to_exponent F c Q ⟨D, hD, ?_⟩ ?_
    · intro M N hM hN b hb
      rw [mem_paperShell] at hb
      exact hdiag c Q M hM b hb.1 hb.2.1
    · intro ε hε
      exact initial_same_class_gram F hF c hc Q ε hε

end DedekindZetaZeroFree.LargeSieve.Sieve
