module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterOperations
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.TotallyPositiveResidueRepresentatives

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve

variable {F : Type} [Field F] [NumberField F]

theorem rayCharacter_span_eq_of_residue {m : Ideal (𝓞 F)} (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) (a b : 𝓞 F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ∈ m)
    (ha_coprime : Ideal.span {a} ⊔ m = ⊤)
    (ha_pos : ∀ φ : F →+* ℝ, 0 < φ (a : F))
    (hb_pos : ∀ φ : F →+* ℝ, 0 < φ (b : F)) :
    η (Ideal.span {a}) = η (Ideal.span {b}) := by

  have hmem : (1 : 𝓞 F) ∈ Ideal.span {a} ⊔ m := by
    rw [ha_coprime]; exact Submodule.mem_top
  obtain ⟨c, d, hd, hcd⟩ := Ideal.mem_span_singleton_sup.mp hmem
  have hc : a * c - 1 ∈ m := by
    have h1 : a * c - 1 = -d := by linear_combination hcd
    rw [h1]; exact neg_mem hd

  obtain ⟨u, hu_ne, hu_mem, hu_pos⟩ := exists_totallyPositive_residue F m hm c

  have hau : a * u - 1 ∈ m := by
    have h1 : a * u - 1 = a * (u - c) + (a * c - 1) := by ring
    rw [h1]
    exact m.add_mem (m.mul_mem_left a hu_mem) hc
  have hbu : b * u - 1 ∈ m := by
    have h1 : b * u - 1 = (b - a) * u + (a * u - 1) := by ring
    rw [h1]
    exact m.add_mem (m.mul_mem_right u (by simpa using neg_mem hab)) hau

  have hAu : η (Ideal.span {a * u}) = 1 := by
    refine η.map_span' (a * u) (mul_ne_zero ha hu_ne) hau ?_
    intro φ
    have hcoe : ((a * u : 𝓞 F) : F) = (a : F) * (u : F) :=
      map_mul (algebraMap (𝓞 F) F) a u
    rw [hcoe, map_mul]; exact mul_pos (ha_pos φ) (hu_pos φ)
  have hBu : η (Ideal.span {b * u}) = 1 := by
    refine η.map_span' (b * u) (mul_ne_zero hb hu_ne) hbu ?_
    intro φ
    have hcoe : ((b * u : 𝓞 F) : F) = (b : F) * (u : F) :=
      map_mul (algebraMap (𝓞 F) F) b u
    rw [hcoe, map_mul]; exact mul_pos (hb_pos φ) (hu_pos φ)

  have hA : η (Ideal.span {a}) * η (Ideal.span {u}) = 1 := by
    rw [← RayOperations.map_mul, Ideal.span_singleton_mul_span_singleton]
    exact hAu
  have hB : η (Ideal.span {b}) * η (Ideal.span {u}) = 1 := by
    rw [← RayOperations.map_mul, Ideal.span_singleton_mul_span_singleton]
    exact hBu
  rw [eq_inv_of_mul_eq_one_left hA, eq_inv_of_mul_eq_one_left hB]

end DedekindZetaZeroFree.LargeSieve
