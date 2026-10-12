module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.DetectorMaximalExpressions
noncomputable section
open scoped NumberField Classical

def dyadicPrefix (F : Type) [Field F] [NumberField F]
    (b ω : Ideal (𝓞 F) → ℂ) (N y t : ℝ) : ℂ :=
  ∑ᶠ J : Ideal (𝓞 F),
    if J ≠ ⊥ ∧ N < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ y then
      b J * ω J * (Ideal.absNorm J : ℂ) ^ (-Complex.I * (t : ℂ)) else 0

def support (F : Type) [Field F] [NumberField F]
    (b : Ideal (𝓞 F) → ℂ) (N : ℝ) : Prop :=
  ∀ J, ¬ (J ≠ ⊥ ∧ N < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N) → b J = 0

def mass (F : Type) [Field F] [NumberField F]
    (b : Ideal (𝓞 F) → ℂ) (N : ℝ) : ℝ :=
  ∑ᶠ J : Ideal (𝓞 F),
    if J ≠ ⊥ ∧ N < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N then
      ‖b J‖ ^ 2 else 0

def prefixMaximum (F : Type) [Field F] [NumberField F]
    (b ω : Ideal (𝓞 F) → ℂ) (N t : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ y ∈ Set.Icc N (2 * N), v = ‖dyadicPrefix F b ω N y t‖ ^ 2}

def heightMaximum (F : Type) [Field F] [NumberField F]
    (b ω : Ideal (𝓞 F) → ℂ) (N T : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ t ∈ Set.Icc (-T) T, v = prefixMaximum F b ω N t}

end
end DedekindZetaZeroFree.DetectorMaximalExpressions
