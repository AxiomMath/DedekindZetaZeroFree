module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.QuadraticFormsAndSieveExponents
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.QuadraticHeckePairConductors
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.ImprimitiveSmoothIdealSums

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

theorem initial_same_class_gram
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (c : Ideal (𝓞 F)) (hc : c ≠ ⊥)
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
        ∀ b1 ∈ paperShell F c N, ∀ b2 ∈ paperShell F c N,
          Q.cls b1 = Q.cls b2 → b1 ≠ b2 →
            ‖initialGram F Q M b1 b2‖ ≤ H * Real.rpow N (1 + ε) := by
  have hδ : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨A, hA, hbound⟩ := initial_imprimitive_smooth_sum F hF (ε / 2) hδ
  obtain ⟨L, hL1, hLgrowth⟩ := initial_family_conductor_growth hc Q
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  refine ⟨A * (2 * L) ^ (1 + ε), mul_nonneg hA (Real.rpow_nonneg (by linarith) _), ?_⟩
  intro M N hM hN b1 hb1 b2 hb2 hcls hne
  rw [mem_paperShell] at hb1 hb2
  obtain ⟨hb1sf, hb1c, -, hb1hi⟩ := hb1
  obtain ⟨hb2sf, hb2c, -, hb2hi⟩ := hb2
  have hm1 : Q.cond b1 ≠ ⊥ := (Q.primitive b1 hb1sf hb1c).1
  have hm2 : Q.cond b2 ≠ ⊥ := (Q.primitive b2 hb2sf hb2c).1
  have hm : Q.cond b1 * Q.cond b2 ≠ ⊥ :=
    fun h => (Ideal.mul_eq_bot.mp h).elim hm1 hm2
  have hnonprin :
      ¬ (RayOperations.mul (Q.χ b1) (RayOperations.conjugate (Q.χ b2))).IsPrincipal :=
    initial_family_sameClass_nonprincipal hc Q b1 b2 hb1sf hb1c hb2sf hb2c hcls hne
  have hgram : initialGram F Q M b1 b2 =
      initialTheta F (RayOperations.mul (Q.χ b1) (RayOperations.conjugate (Q.χ b2))) M := rfl

  have hb1' : (Ideal.absNorm (Q.cond b1) : ℝ) ≤ 2 * L * N := by
    calc (Ideal.absNorm (Q.cond b1) : ℝ) ≤ L * (Ideal.absNorm b1 : ℝ) :=
          hLgrowth b1 hb1sf hb1c
      _ ≤ L * (2 * N) := mul_le_mul_of_nonneg_left hb1hi hL0
      _ = 2 * L * N := by ring
  have hb2' : (Ideal.absNorm (Q.cond b2) : ℝ) ≤ 2 * L * N := by
    calc (Ideal.absNorm (Q.cond b2) : ℝ) ≤ L * (Ideal.absNorm b2 : ℝ) :=
          hLgrowth b2 hb2sf hb2c
      _ ≤ L * (2 * N) := mul_le_mul_of_nonneg_left hb2hi hL0
      _ = 2 * L * N := by ring
  have hN0 : 0 ≤ N := by linarith
  have hC0 : 0 ≤ 2 * L * N := by nlinarith [hL0, hN0]
  have hprod : (Ideal.absNorm (Q.cond b1 * Q.cond b2) : ℝ) ≤ (2 * L * N) * (2 * L * N) := by
    rw [map_mul Ideal.absNorm]
    push_cast
    exact mul_le_mul hb1' hb2' (Nat.cast_nonneg _) hC0
  have hs : 0 ≤ (1 : ℝ) / 2 + ε / 2 := by linarith
  have hstep : (Ideal.absNorm (Q.cond b1 * Q.cond b2) : ℝ) ^ (1 / 2 + ε / 2) ≤
      (2 * L * N) ^ (1 + ε) := by
    have h1 := Real.rpow_le_rpow (Nat.cast_nonneg _) hprod hs
    rw [Real.mul_rpow hC0 hC0] at h1
    rw [← Real.rpow_add (by nlinarith [hL0, hN0] : (0 : ℝ) < 2 * L * N)
      (1 / 2 + ε / 2) (1 / 2 + ε / 2)] at h1
    have hexp : (1 : ℝ) / 2 + ε / 2 + (1 / 2 + ε / 2) = 1 + ε := by ring
    rwa [hexp] at h1
  rw [hgram]
  calc ‖initialTheta F (RayOperations.mul (Q.χ b1) (RayOperations.conjugate (Q.χ b2))) M‖
      ≤ A * (Ideal.absNorm (Q.cond b1 * Q.cond b2) : ℝ) ^ (1 / 2 + ε / 2) :=
        hbound (Q.cond b1 * Q.cond b2) hm _ hnonprin M (by linarith)
    _ ≤ A * (2 * L * N) ^ (1 + ε) := mul_le_mul_of_nonneg_left hstep hA
    _ = A * (2 * L) ^ (1 + ε) * N ^ (1 + ε) := by
        rw [Real.mul_rpow (by linarith : (0 : ℝ) ≤ 2 * L) hN0]
        ring

end DedekindZetaZeroFree.LargeSieve.Sieve
