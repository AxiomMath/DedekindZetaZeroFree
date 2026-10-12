module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleIdealRanges

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

noncomputable def idealDyadicBlock (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) : ℕ → Finset (Ideal (𝓞 F))
  | 0 => {⊤}
  | k + 1 => paperShell F c ((2 : ℝ) ^ k)

def dyadicScale : ℕ → ℝ
  | 0 => 1
  | k + 1 => (2 : ℝ) ^ k

noncomputable def clippedDyadicBlock (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (X : ℝ) (j : ℕ) : Finset (Ideal (𝓞 F)) :=
  idealDyadicBlock F c j ∩ idealAdmissibleFinset F c X

end DedekindZetaZeroFree.LargeSieve.Sieve
