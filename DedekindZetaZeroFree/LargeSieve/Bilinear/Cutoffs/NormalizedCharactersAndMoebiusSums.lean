module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/QuadraticSieve/MainTermDifference.lean.
-/

open scoped NumberField Classical BigOperators NNReal

namespace DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference.SplitData

noncomputable section

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
  [Subsingleton Rˣ]

def divisors (g : R) : Finset R :=
  if g = 0 then ∅ else (UniqueFactorizationMonoid.factors g).powerset.toFinset.image
    Multiset.prod

def normalizedValue (n : R →* (ℝ≥0)) (χ : R →* ℂ) (b : R) : ℂ :=
  χ b / (Real.sqrt (n b : ℝ) : ℂ)

def cutoff (n : R →* (ℝ≥0)) (K : ℝ) (b : R) : ℤ :=
  if (n b : ℝ) ≤ K then 1 else 0

def moebiusDivisorSum (n : R →* (ℝ≥0)) (χ : R →* ℂ) (g : R) : ℂ :=
  ∑ e ∈ divisors g, (UniqueFactorizationMonoid.moebius e : ℂ) * normalizedValue n χ e

def density (n : R →* (ℝ≥0)) (g : R) : ℝ :=
  ∏ p ∈ (UniqueFactorizationMonoid.factors g).toFinset, (1 - 1 / (n p : ℝ))

def boundaryElements (H : Finset R) (g : R) : Finset R :=
  (H ×ˢ (divisors g ×ˢ divisors g)).image (fun x => x.1 * x.2.1 * x.2.2)

def boundaryCoefficient (n : R →* (ℝ≥0)) (K : ℝ) (H : Finset R) (g b : R) : ℤ :=
  ∑ h ∈ H, ∑ d ∈ divisors g, ∑ e ∈ divisors g,
    if h * d * e = b then
      UniqueFactorizationMonoid.moebius e * (cutoff n K (h * d) - cutoff n K h)
    else 0

theorem normalizedValue_mul (n : R →* ℝ≥0) (χ : R →* ℂ) (a b : R) :
    normalizedValue n χ (a * b) = normalizedValue n χ a * normalizedValue n χ b := by
  simp only [normalizedValue, map_mul, NNReal.coe_mul, Real.sqrt_mul (n a).coe_nonneg,
    Complex.ofReal_mul, div_mul_div_comm]

end
end DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference.SplitData
