module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleIdealRanges

@[expose] public section

noncomputable section

open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve.Sieve

structure SieveWeight (W : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ W
  nonneg : ∀ t : ℝ, 0 ≤ W t
  one_le : ∀ t : ℝ, t ∈ Set.Icc (1 : ℝ) 2 → 1 ≤ W t
  zero_outside : ∀ t : ℝ, t ∉ Set.Icc (1 / 2 : ℝ) (5 / 2) → W t = 0

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}

def energy (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F))
    (N : ℝ) (lam : Ideal (𝓞 F) → ℂ) : ℝ :=
  ∑ b ∈ paperShell F c N, ‖lam b‖ ^ 2

def rowSum (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (N : ℝ) (lam : Ideal (𝓞 F) → ℂ) (a : Ideal (𝓞 F)) : ℂ :=
  ∑ b ∈ paperShell F c N, lam b * (Q.χ b) a

def Q1 (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F))
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (M N : ℝ) (lam : Ideal (𝓞 F) → ℂ) : ℝ :=
  ∑ a ∈ paperShell F c M, ‖rowSum Q N lam a‖ ^ 2

def smoothedRows (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (M : ℝ) : Finset (Ideal (𝓞 F)) :=
  (boundedNormIdeals F ((5 / 2) * M)).filter
    (fun a => a ≠ ⊥ ∧ Squarefree a ∧ a ⊔ c = ⊤)

def Q1w (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F))
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (M N : ℝ) (lam : Ideal (𝓞 F) → ℂ) : ℝ :=
  ∑ a ∈ smoothedRows F c M,
    W ((Ideal.absNorm a : ℝ) / M) * ‖rowSum Q N lam a‖ ^ 2

def B1 (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F))
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) (M N : ℝ) : ℝ :=
  sSup ({0} ∪ {x : ℝ | ∃ lam : Ideal (𝓞 F) → ℂ,
    energy F c N lam ≤ 1 ∧ x = Q1 F c Q M N lam})

def squarefreeKernel (a : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  if a = ⊥ then ⊤ else
    ∏ p ∈ (UniqueFactorizationMonoid.normalizedFactors a).toFinset.filter
      (fun p => (UniqueFactorizationMonoid.normalizedFactors a).count p % 2 = 1), p

def s (a : Ideal (𝓞 F)) : ℝ := (Ideal.absNorm (squarefreeKernel a) : ℝ)

def kernelRows (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (M K : ℝ) : Finset (Ideal (𝓞 F)) :=
  (boundedNormIdeals F ((5 / 2) * M)).filter
    (fun a => a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ K < s a)

def Q2 (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F))
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (M N K : ℝ) (lam : Ideal (𝓞 F) → ℂ) : ℝ :=
  ∑ a ∈ kernelRows F c M K,
    W ((Ideal.absNorm a : ℝ) / M) * ‖rowSum Q N lam a‖ ^ 2

def B2 (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F))
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (M N K : ℝ) : ℝ :=
  sSup ({0} ∪ {x : ℝ | ∃ lam : Ideal (𝓞 F) → ℂ,
    energy F c N lam ≤ 1 ∧ x = Q2 F c Q W M N K lam})

def T3 (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F))
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (M N K : ℝ) (d : Ideal (𝓞 F)) (g : Q.G)
    (lam : Ideal (𝓞 F) → ℂ) : ℂ :=
  ∑ b1 ∈ paperShell F c N, ∑ b2 ∈ paperShell F c N,
    if b1 ⊔ b2 = d ∧ Q.cls b1 = g ∧ Q.cls b2 = g then
      lam b1 * (starRingEnd ℂ) (lam b2) *
        (∑ a ∈ kernelRows F c M K,
          (W ((Ideal.absNorm a : ℝ) / M) : ℂ) *
            (Q.χ b1) a * (starRingEnd ℂ) ((Q.χ b2) a))
    else 0

def B3 (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F))
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (M N K : ℝ) (d : Ideal (𝓞 F)) : ℝ :=
  sSup ({0} ∪ {x : ℝ | ∃ (g : Q.G) (lam : Ideal (𝓞 F) → ℂ),
    energy F c N lam ≤ 1 ∧ x = ‖T3 F c Q W M N K d g lam‖})

def HasSieveExponent (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F))
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      B1 F c Q M N ≤ C * Real.rpow (M * N) ε * (M + Real.rpow N α)

end DedekindZetaZeroFree.LargeSieve.Sieve

end
