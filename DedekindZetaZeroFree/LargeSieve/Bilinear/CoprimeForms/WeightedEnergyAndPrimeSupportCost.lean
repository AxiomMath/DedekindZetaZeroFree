module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.QuadraticFormsAndSieveExponents

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.Sieve.GcdTail

open scoped NumberField Classical

def primeSupportCost {F : Type} [Field F] [NumberField F]
    (u : Ideal (𝓞 F)) : ℝ :=
  (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card

def maskedRowWeight {F : Type} [Field F] [NumberField F]
    (W : ℝ → ℝ) (q d : Ideal (𝓞 F)) (M : ℝ)
    (rowMask : Ideal (𝓞 F) → ℝ) (a : Ideal (𝓞 F)) : ℝ :=
  if a ⊔ (q * d) = ⊤ then W ((Ideal.absNorm a : ℝ) / M) * rowMask a else 0

def weightedEnergy {F : Type} [Field F] [NumberField F]
    {R : Type*} (rows : Finset R) (cols : Finset (Ideal (𝓞 F)))
    (w : R → ℝ) (A : R → Ideal (𝓞 F) → ℂ)
    (alpha : Ideal (𝓞 F) → ℂ) : ℝ :=
  ∑ r ∈ rows, w r * ‖∑ u ∈ cols, A r u * alpha u‖ ^ 2

def coprimeForm {F : Type} [Field F] [NumberField F]
    {R : Type*} (rows : Finset R) (cols : Finset (Ideal (𝓞 F)))
    (w : R → ℝ) (A : R → Ideal (𝓞 F) → ℂ)
    (alpha : Ideal (𝓞 F) → ℂ) : ℂ :=
  ∑ r ∈ rows, (w r : ℂ) *
    ∑ u ∈ cols, ∑ v ∈ cols,
      if u ⊔ v = ⊤ then (A r u * alpha u) * star (A r v * alpha v) else 0

end DedekindZetaZeroFree.LargeSieve.Sieve.GcdTail

end
