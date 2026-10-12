module

public import Mathlib.Data.Finset.Sym
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace DedekindZetaZeroFree.SexticPairwiseExponent

theorem exponent (e₁ e₂ l₁ l₂ : ℕ) :
    2 * (e₁ + 3 * l₁) * (e₂ + 3 * l₂) + 4 * e₁ * e₂ =
      6 * (e₁ * e₂ + e₁ * l₂ + e₂ * l₁ + 3 * l₁ * l₂) := by
  ring

theorem raw_phase_cancel (β γ : ℂ) (hβγ : β = γ) (hβ : β ^ 6 = 1)
    (t₁ t₂ k₁ k₂ : ℕ) :
    β ^ ((t₁ : ℤ) * k₂ + ((t₁ : ℤ) - k₁) * t₂) *
      γ ^ ((t₂ : ℤ) * k₁ + ((t₂ : ℤ) - k₂) * t₁) =
        β ^ (2 * t₁ * t₂) := by
  subst hβγ
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h] at hβ
    norm_num at hβ
  rw [← zpow_add₀ hβ0]
  have hA : ((t₁ : ℤ) * k₂ + ((t₁ : ℤ) - k₁) * t₂) +
      ((t₂ : ℤ) * k₁ + ((t₂ : ℤ) - k₂) * t₁) = (2 * t₁ * t₂ : ℕ) := by
    push_cast
    ring
  rw [hA, zpow_natCast]

end DedekindZetaZeroFree.SexticPairwiseExponent
