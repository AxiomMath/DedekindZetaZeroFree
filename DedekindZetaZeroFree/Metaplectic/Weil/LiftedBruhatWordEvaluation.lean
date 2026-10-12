module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Data.Complex.Basic

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

theorem representation_bruhat {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (ell : V →ₗ[ℂ] ℂ) (b : V)
    (a w n n' a' l z a'' : G) (ψ c : ℂ)
    (hword : a * w * n = n' * (a * a') * l)
    (hl : ρ l b = b)
    (hroot : ∀ v, ell (ρ n' v) = ψ * ell v)
    (hprod : a * a' = z * a'')
    (hz : ∀ v, ρ z v = c • v) :
    ell (ρ (a * w * n) b) = ψ * c * ell (ρ a'' b) := by
  rw [hword, hprod]
  simp only [map_mul, Module.End.mul_apply, hl, hroot, hz, map_smul, smul_eq_mul]
  ring

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
