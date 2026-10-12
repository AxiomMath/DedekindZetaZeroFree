module

public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassGroupFinite

@[expose] public section

namespace DedekindZetaZeroFree.RayClassBridge.FiniteOrder

theorem norm_eq_one {G : Type*} [Group G] [Finite G]
    (χ : G →* ℂˣ) (g : G) : ‖(χ g : ℂ)‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := Nat.card G)
  · have h : χ g ^ Nat.card G = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) h
  · exact Nat.ne_of_gt Nat.card_pos

end DedekindZetaZeroFree.RayClassBridge.FiniteOrder
