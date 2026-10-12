module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.AbelianQuotient

private lemma exists_shift_totallyPositive
    (K : Type) [Field K] [NumberField K] (d₀ : 𝓞 K) (N : ℕ) (hN : 0 < N) :
    ∃ t : ℕ, d₀ + (t * N : 𝓞 K) ≠ 0 ∧
      ∀ φ : K →+* ℝ, 0 < φ ((d₀ + (t * N : 𝓞 K) : 𝓞 K) : K) := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hbound : ∀ φ : K →+* ℝ, ∃ t : ℕ, 0 < φ (d₀ : K) + (t : ℝ) * (N : ℝ) := by
    intro φ
    obtain ⟨t, ht⟩ := exists_nat_gt (- φ (d₀ : K) / (N : ℝ))
    refine ⟨t, ?_⟩
    have h1 : - φ (d₀ : K) / (N : ℝ) * (N : ℝ) < (t : ℝ) * (N : ℝ) :=
      mul_lt_mul_of_pos_right ht hNR
    have h2 : - φ (d₀ : K) / (N : ℝ) * (N : ℝ) = - φ (d₀ : K) := by
      field_simp
    linarith
  let T : ℕ := (Finset.univ.sum fun φ : K →+* ℝ => Classical.choose (hbound φ)) + 1
  have hT : ∀ φ : K →+* ℝ, 0 < φ (d₀ : K) + (T : ℝ) * (N : ℝ) := by
    intro φ
    have hch := Classical.choose_spec (hbound φ)
    have hle : Classical.choose (hbound φ) ≤ T := by
      have h1 : Classical.choose (hbound φ) ≤
          Finset.univ.sum fun φ : K →+* ℝ => Classical.choose (hbound φ) :=
        Finset.single_le_sum
          (f := fun φ : K →+* ℝ => Classical.choose (hbound φ))
          (fun i _ => Nat.zero_le _) (Finset.mem_univ φ)
      omega
    have hcast : ((Classical.choose (hbound φ) : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hle
    have hNn : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNR
    nlinarith [mul_le_mul_of_nonneg_right hcast hNn]
  have hTle : ∀ t : ℕ, T ≤ t → ∀ φ : K →+* ℝ,
      0 < φ ((d₀ + (t * N : 𝓞 K) : 𝓞 K) : K) := by
    intro t ht φ
    have hTφ := hT φ
    have hcast : (T : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    have hNn : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNR
    have hmul : (T : ℝ) * (N : ℝ) ≤ (t : ℝ) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hcast hNn
    have hcoeeq : ((d₀ + (t * N : 𝓞 K) : 𝓞 K) : K) = (d₀ : K) + (t : K) * (N : K) := by
      push_cast; ring
    rw [hcoeeq, map_add, map_mul, map_natCast, map_natCast]
    linarith
  have hNne : (N : 𝓞 K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  by_cases hzero : d₀ + (T * N : 𝓞 K) = 0
  · refine ⟨T + 1, ?_, hTle (T + 1) (Nat.le_succ T)⟩
    intro h
    apply hNne
    have h3 : (↑(T + 1) : 𝓞 K) * (N : 𝓞 K) = (T : 𝓞 K) * (N : 𝓞 K) := by
      have h2 : d₀ + (↑(T + 1) : 𝓞 K) * (N : 𝓞 K) = d₀ + (T : 𝓞 K) * (N : 𝓞 K) := by
        rw [h, hzero]
      exact add_left_cancel h2
    have hh : (↑(T + 1) : 𝓞 K) * (N : 𝓞 K) - (T : 𝓞 K) * (N : 𝓞 K) = 0 :=
      sub_eq_zero.mpr h3
    rw [show (↑(T + 1) : 𝓞 K) * (N : 𝓞 K) - (T : 𝓞 K) * (N : 𝓞 K) = (N : 𝓞 K) by
      rw [Nat.cast_add, Nat.cast_one]; ring] at hh
    exact hh
  · exact ⟨T, hzero, hTle T le_rfl⟩

theorem positiveIdealCRT
    (K : Type) [Field K] [NumberField K]
    (D m : Ideal (𝓞 K)) (hD : D ≠ ⊥) (hm : m ≠ ⊥)
    (hcop : D ⊔ m = ⊤) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d ∈ D ∧ d - 1 ∈ m ∧
      ∀ φ : K →+* ℝ, 0 < φ (d : K) := by
  classical
  have hcop' : IsCoprime D m := Ideal.isCoprime_iff_sup_eq.mpr hcop
  obtain ⟨d₀, hd₀D, j, hjm, hsum⟩ := hcop'.exists
  have hd₀m : d₀ - 1 ∈ m := by
    have heq : d₀ - 1 = -j := by rw [← hsum]; ring
    rw [heq]; exact m.neg_mem hjm
  have hDm : D ⊓ m ≠ ⊥ := Ideal.inf_ne_bot_of_ne_bot hD hm
  have hNpos : 0 < Ideal.absNorm (D ⊓ m) :=
    Nat.pos_of_ne_zero fun h => hDm (Ideal.absNorm_eq_zero_iff.mp h)
  have hNmem : (Ideal.absNorm (D ⊓ m) : 𝓞 K) ∈ D ⊓ m := Ideal.absNorm_mem _
  obtain ⟨t, htne, htpos⟩ :=
    exists_shift_totallyPositive K d₀ (Ideal.absNorm (D ⊓ m)) hNpos
  refine ⟨d₀ + (t * Ideal.absNorm (D ⊓ m) : 𝓞 K), htne, ?_, ?_, htpos⟩
  · apply D.add_mem hd₀D
    have hmul : (t * Ideal.absNorm (D ⊓ m) : 𝓞 K) =
        (Ideal.absNorm (D ⊓ m) : 𝓞 K) * (t : 𝓞 K) := by ring
    rw [hmul]
    exact D.mul_mem_right _ (Ideal.mem_inf.mp hNmem).1
  · have heq : d₀ + (t * Ideal.absNorm (D ⊓ m) : 𝓞 K) - 1 =
        (d₀ - 1) + (t * Ideal.absNorm (D ⊓ m) : 𝓞 K) := by ring
    rw [heq]
    apply m.add_mem hd₀m
    have hmul : (t * Ideal.absNorm (D ⊓ m) : 𝓞 K) =
        (Ideal.absNorm (D ⊓ m) : 𝓞 K) * (t : 𝓞 K) := by ring
    rw [hmul]
    exact m.mul_mem_right _ (Ideal.mem_inf.mp hNmem).2

end DedekindZetaZeroFree.AbelianQuotient
