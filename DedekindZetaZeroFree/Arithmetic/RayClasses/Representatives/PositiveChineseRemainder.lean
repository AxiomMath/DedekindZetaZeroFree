module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

theorem exists_positive_mem_congruent_one
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (B : Ideal (𝓞 F)) (hB : B ≠ ⊥) (hBm : B ⊔ m = ⊤) :
    ∃ b : 𝓞 F, b ≠ 0 ∧ b ∈ B ∧ b - 1 ∈ m ∧
      ∀ φ : F →+* ℝ, 0 < φ (b : F) := by
  classical

  have h1 : (1 : 𝓞 F) ∈ B ⊔ m := by rw [hBm]; exact Submodule.mem_top
  obtain ⟨b0, hb0B, y, hym, hsum⟩ := Submodule.mem_sup.mp h1
  have hb0sub : b0 - 1 ∈ m := by
    have h : b0 - 1 = -y := by rw [← hsum]; ring
    rw [h]; exact m.neg_mem hym

  have hBm_ne : B * m ≠ ⊥ := by
    intro h
    rcases (Ideal.mul_eq_bot.mp h) with h | h
    · exact hB h
    · exact hm h
  set d : ℕ := (B * m).absNorm with hd
  have hd_ne : d ≠ 0 := by
    rw [hd, ne_eq, Ideal.absNorm_eq_zero_iff]; exact hBm_ne
  have hd_pos : 0 < d := Nat.pos_iff_ne_zero.mpr hd_ne
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
  have hd_ne_ring : (d : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hd_ne
  have hd_mem_mul : (d : 𝓞 F) ∈ B * m := by
    rw [hd]; exact Ideal.absNorm_mem _
  have hd_mem_B : (d : 𝓞 F) ∈ B := Ideal.mul_le_left hd_mem_mul
  have hd_mem_m : (d : 𝓞 F) ∈ m := Ideal.mul_le_right hd_mem_mul

  have hcoe_add : ∀ x y : 𝓞 F, ((x + y : 𝓞 F) : F) = (x : F) + (y : F) :=
    fun x y => map_add (algebraMap (𝓞 F) F) x y
  have hcoe_mul : ∀ x y : 𝓞 F, ((x * y : 𝓞 F) : F) = (x : F) * (y : F) :=
    fun x y => map_mul (algebraMap (𝓞 F) F) x y
  have hcoe_nat : ∀ n : ℕ, ((n : 𝓞 F) : F) = (n : F) :=
    fun n => map_natCast (algebraMap (𝓞 F) F) n

  set C : ℝ := ∑ φ : F →+* ℝ, |φ (b0 : F)| with hC
  obtain ⟨N, hN⟩ := exists_nat_gt (C / (d : ℝ))
  have hN' : C < (N : ℝ) * (d : ℝ) := by
    have := (div_lt_iff₀ hdR).mp hN
    simpa [mul_comm] using this
  set b1 : 𝓞 F := b0 + (N : 𝓞 F) * (d : 𝓞 F) with hb1
  have hb1val : ∀ φ : F →+* ℝ, φ (b1 : F) = φ (b0 : F) + (N : ℝ) * (d : ℝ) := by
    intro φ
    have h1' : (b1 : F) = (b0 : F) + (N : F) * (d : F) := by
      rw [hb1, hcoe_add, hcoe_mul, hcoe_nat, hcoe_nat]
    rw [h1', map_add, map_mul, map_natCast, map_natCast]
  have hb1_pos : ∀ φ : F →+* ℝ, 0 < φ (b1 : F) := by
    intro φ
    have hle : |φ (b0 : F)| ≤ C := by
      rw [hC]
      exact Finset.single_le_sum (f := fun ψ => |ψ (b0 : F)|)
        (fun i _ => abs_nonneg _) (Finset.mem_univ φ)
    rw [hb1val φ]
    nlinarith [neg_le_abs (φ (b0 : F)), hle, hN']
  have hb1B : b1 ∈ B := by
    rw [hb1]
    exact B.add_mem hb0B (B.mul_mem_left _ hd_mem_B)
  have hb1sub : b1 - 1 ∈ m := by
    have h : b1 - 1 = (b0 - 1) + (N : 𝓞 F) * (d : 𝓞 F) := by rw [hb1]; ring
    rw [h]
    exact m.add_mem hb0sub (m.mul_mem_left _ hd_mem_m)
  by_cases hb1z : b1 = 0
  ·
    refine ⟨b1 + (d : 𝓞 F), ?_, ?_, ?_, ?_⟩
    · rw [hb1z, zero_add]; exact hd_ne_ring
    · rw [hb1z, zero_add]; exact hd_mem_B
    · have h : b1 + (d : 𝓞 F) - 1 = (b1 - 1) + (d : 𝓞 F) := by ring
      rw [h]; exact m.add_mem hb1sub hd_mem_m
    · intro φ
      have h2 : ((b1 + (d : 𝓞 F) : 𝓞 F) : F) = (b1 : F) + (d : F) := by
        rw [hcoe_add, hcoe_nat]
      have hz : φ (b1 : F) = 0 := by
        rw [hb1z, show ((0 : 𝓞 F) : F) = (0 : F) from map_zero (algebraMap (𝓞 F) F),
          map_zero]
      rw [h2, map_add, hz, zero_add]
      simpa only [hcoe_nat d, map_natCast] using hdR
  · exact ⟨b1, hb1z, hb1B, hb1sub, hb1_pos⟩

end DedekindZetaZeroFree.LargeSieve.RayBridge
