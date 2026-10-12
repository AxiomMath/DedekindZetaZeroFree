module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem exists_totallyPositive_residue (F : Type) [Field F] [NumberField F]
    (r : Ideal (𝓞 F)) (hr : r ≠ ⊥) (a : 𝓞 F) :
    ∃ b : 𝓞 F, b ≠ 0 ∧ b - a ∈ r ∧
      (∀ φ : F →+* ℝ, 0 < φ (b : F)) := by
  classical

  set d : ℕ := r.absNorm with hd
  have hd_ne : d ≠ 0 := by rw [hd, ne_eq, Ideal.absNorm_eq_zero_iff]; exact hr
  have hd_pos : 0 < d := Nat.pos_iff_ne_zero.mpr hd_ne
  have hd_mem : (d : 𝓞 F) ∈ r := by rw [hd]; exact Ideal.absNorm_mem r
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd_pos
  have hd_ne_ring : (d : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hd_ne

  have hcoe_add : ∀ x y : 𝓞 F, ((x + y : 𝓞 F) : F) = (x:F) + (y:F) :=
    fun x y => map_add (algebraMap (𝓞 F) F) x y
  have hcoe_mul : ∀ x y : 𝓞 F, ((x * y : 𝓞 F) : F) = (x:F) * (y:F) :=
    fun x y => map_mul (algebraMap (𝓞 F) F) x y
  have hcoe_nat : ∀ n : ℕ, ((n : 𝓞 F) : F) = (n:F) :=
    fun n => map_natCast (algebraMap (𝓞 F) F) n

  set C : ℝ := ∑ φ : F →+* ℝ, |φ (a : F)| with hC
  obtain ⟨N, hN⟩ := exists_nat_gt (C / (d:ℝ))
  have hN' : C < (N:ℝ) * (d:ℝ) := by
    have := (div_lt_iff₀ hdR).mp hN
    simpa [mul_comm] using this
  set b1 : 𝓞 F := a + (N : 𝓞 F) * (d : 𝓞 F) with hb1
  have hb1val : ∀ φ : F →+* ℝ, φ (b1 : F) = φ (a : F) + (N:ℝ) * (d:ℝ) := by
    intro φ
    have h1 : (b1 : F) = (a : F) + (N : F) * (d : F) := by
      rw [hb1, hcoe_add, hcoe_mul, hcoe_nat, hcoe_nat]
    rw [h1, map_add, map_mul, map_natCast, map_natCast]
  have hb1_pos : ∀ φ : F →+* ℝ, 0 < φ (b1 : F) := by
    intro φ
    have hle : |φ (a:F)| ≤ C := by
      rw [hC]
      exact Finset.single_le_sum (f := fun ψ => |ψ (a:F)|)
        (fun i _ => abs_nonneg _) (Finset.mem_univ φ)
    rw [hb1val φ]
    nlinarith [neg_le_abs (φ (a:F)), hle, hN']
  by_cases hb1z : b1 = 0
  ·
    refine ⟨b1 + (d : 𝓞 F), ?_, ?_, ?_⟩
    · rw [hb1z, zero_add]; exact hd_ne_ring
    · have hsub : b1 + (d : 𝓞 F) - a = (b1 - a) + (d : 𝓞 F) := by ring
      rw [hsub]
      refine r.add_mem ?_ hd_mem
      have : b1 - a = (N : 𝓞 F) * (d : 𝓞 F) := by rw [hb1]; ring
      rw [this]
      exact Ideal.mul_mem_left r _ hd_mem
    · intro φ
      have h2 : ((b1 + (d : 𝓞 F) : 𝓞 F) : F) = (b1 : F) + (d : F) := by
        rw [hcoe_add, hcoe_nat]
      have hz : φ (b1 : F) = 0 := by
        rw [hb1z, show ((0:𝓞 F) : F) = (0:F) from map_zero (algebraMap (𝓞 F) F),
          map_zero]
      rw [h2, map_add, hz, zero_add]
      simpa only [hcoe_nat d, map_natCast] using hdR
  · refine ⟨b1, hb1z, ?_, hb1_pos⟩
    have : b1 - a = (N : 𝓞 F) * (d : 𝓞 F) := by rw [hb1]; ring
    rw [this]
    exact Ideal.mul_mem_left r _ hd_mem

end DedekindZetaZeroFree.LargeSieve
