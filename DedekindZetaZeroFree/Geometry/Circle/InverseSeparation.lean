module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/Topology/Circle/Basic.lean`. Original Apache-2.0 copyright and authors retained.
-/

@[expose] public section

namespace DedekindZetaZeroFree.TauCeti

theorem circle_sub_inv_ne_zero {z : Circle} (hz : (z : ℂ) ^ 2 ≠ 1) :
    (z : ℂ) - ((z : ℂ))⁻¹ ≠ 0 := by
  intro hc
  refine hz ?_
  rw [sub_eq_zero] at hc
  calc (z : ℂ) ^ 2 = (z : ℂ) * ((z : ℂ))⁻¹ := by rw [← hc, sq]
    _ = 1 := mul_inv_cancel₀ z.coe_ne_zero

end DedekindZetaZeroFree.TauCeti
