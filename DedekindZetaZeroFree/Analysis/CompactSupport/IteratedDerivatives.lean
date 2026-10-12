module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve.Vendor

theorem contDiff_iteratedDeriv (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n h) := by
  rw [iteratedDeriv_eq_iterate]
  exact hh.iterate_deriv n

theorem hasCompactSupport_iteratedDeriv (h : ℝ → ℂ) (hh : HasCompactSupport h)
    (n : ℕ) : HasCompactSupport (iteratedDeriv n h) := by
  induction n with
  | zero => simpa using hh
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

end DedekindZetaZeroFree.LargeSieve.Vendor
