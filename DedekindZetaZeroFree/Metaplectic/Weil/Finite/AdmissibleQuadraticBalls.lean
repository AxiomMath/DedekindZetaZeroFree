module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.LocalScaledBallDuality

@[expose] public section

noncomputable section

open scoped NumberField Classical nonZeroDivisors Topology
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

private theorem finiteBall_fractionalIdeal (v : HeightOneSpectrum (𝓞 F)) (m : ℤ) :
    ∃ I : FractionalIdeal (v.adicCompletionIntegers F)⁰ (v.adicCompletion F),
      I ≠ 0 ∧ (I : Set (v.adicCompletion F)) =
        (finiteCompletionBall F v m : Set (v.adicCompletion F)) := by
  refine ⟨FractionalIdeal.spanSingleton (v.adicCompletionIntegers F)⁰
    (finiteCompletionUniformizer F v ^ m), ?_, ?_⟩
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (zpow_ne_zero m (finiteCompletionUniformizer_ne_zero F v))
  · rw [finiteCompletionBall_eq_uniformizer_image F v _
      (finiteCompletionUniformizer_valuation F v) m]
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := (FractionalIdeal.mem_spanSingleton _).mp hx
      refine ⟨z, z.property, ?_⟩
      simpa [Algebra.smul_def, mul_comm] using hz
    · rintro ⟨z, hz, rfl⟩
      apply (FractionalIdeal.mem_spanSingleton _).mpr
      exact ⟨⟨z, hz⟩, by simp [Algebra.smul_def, mul_comm]⟩

theorem localScaledBallDual_compact_open_fractionalIdeals
    (v : HeightOneSpectrum (𝓞 F)) (b : (v.adicCompletion F)ˣ) (m : ℤ) :
    IsCompact (finiteCompletionBall F v m : Set (v.adicCompletion F)) ∧
    IsOpen (finiteCompletionBall F v m : Set (v.adicCompletion F)) ∧
    IsCompact (localScaledBallDual F v b m : Set (v.adicCompletion F)) ∧
    IsOpen (localScaledBallDual F v b m : Set (v.adicCompletion F)) ∧
    (∃ I : FractionalIdeal (v.adicCompletionIntegers F)⁰ (v.adicCompletion F),
      I ≠ 0 ∧ (I : Set (v.adicCompletion F)) =
        (finiteCompletionBall F v m : Set (v.adicCompletion F))) ∧
    (∃ I : FractionalIdeal (v.adicCompletionIntegers F)⁰ (v.adicCompletion F),
      I ≠ 0 ∧ (I : Set (v.adicCompletion F)) =
        (localScaledBallDual F v b m : Set (v.adicCompletion F))) := by
  rw [localScaledBallDual_eq_finiteCompletionBall]
  exact ⟨isCompact_finiteCompletionBall F v m, isOpen_finiteCompletionBall F v m,
    isCompact_finiteCompletionBall F v _, isOpen_finiteCompletionBall F v _,
    finiteBall_fractionalIdeal F v m, finiteBall_fractionalIdeal F v _⟩

theorem localScaledBallDual_eventually_le_expanding_ball
    (v : HeightOneSpectrum (𝓞 F)) (b : (v.adicCompletion F)ˣ) (m : ℤ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      finiteCompletionBall F v m ≤ finiteCompletionBall F v (-(n : ℤ)) ∧
      localScaledBallDual F v b m ≤ finiteCompletionBall F v (-(n : ℤ)) := by
  let k := -m - (localDifferentExponent F v : ℤ) - finiteCompletionUnitOrder F v b
  refine ⟨(max (-m) (-k)).toNat, ?_⟩
  intro n hn
  have hbound := Int.self_le_toNat (max (-m) (-k))
  have hn' : ((max (-m) (-k)).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  rw [localScaledBallDual_eq_finiteCompletionBall]
  constructor <;> apply (finiteCompletionBall_le_iff F v _ _).mpr <;> dsimp [k] at * <;> omega

end DedekindZetaZeroFree

end
