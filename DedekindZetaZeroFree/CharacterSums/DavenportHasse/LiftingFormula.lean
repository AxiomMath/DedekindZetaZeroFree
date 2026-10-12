module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import DedekindZetaZeroFree.CharacterSums.DavenportHasse.IrreduciblePolynomialSum
public import DedekindZetaZeroFree.CharacterSums.DavenportHasse.ExtensionFieldCharacterSum

@[expose] public section

namespace DedekindZetaZeroFree

theorem davenportHasse :
  ∀ (k E : Type) [Field k] [Fintype k] [Field E] [Fintype E] [Algebra k E]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (χE : MulChar E ℂ) (ψE : AddChar E ℂ),
    (∃ x : k, ψ x ≠ 1) →
    (∀ x : E, χE x = χ (Algebra.norm k x)) →
    (∀ x : E, ψE x = ψ (Algebra.trace k E x)) →
    gaussSum χE ψE = -(-gaussSum χ ψ) ^ Module.finrank k E := by
  intro k E _ _ _ _ _ χ ψ χE ψE hψ hχE hψE
  have hn : 0 < Module.finrank k E := Module.finrank_pos
  rw [← DavenportHasse.b_eq χ ψ hψ hn, ← DavenportHasse.sum_lifted_eq_b E χ ψ]
  simp only [gaussSum, hχE, hψE]

end DedekindZetaZeroFree
