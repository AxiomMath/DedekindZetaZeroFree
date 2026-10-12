module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.GcdReduction.CoreCoefficientEstimate
public import DedekindZetaZeroFree.LargeSieve.Bilinear.GcdReduction.ShellEnvelopeNonnegativity
public import DedekindZetaZeroFree.LargeSieve.Bilinear.OperatorBounds.HomogeneousUnitBallBound

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

theorem bilinear_gcd_reduction_core
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (hc : c ≠ ⊥)
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (hGood : CoreGood Q) (W : ℝ → ℝ) (hW : SieveWeight W)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ M N K H : ℝ, 1 ≤ M → 1 ≤ N → 0 < K → 1 ≤ H → H < N →
        ∃ N' : ℝ, 1 ≤ N' ∧ N' ≤ N / H ∧
          B2 F c Q W M N K ≤
            C * Real.rpow (M * N) δ *
              (B2 F c Q W M N' K + M +
                ∑ d ∈ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F H).filter (fun d => d ≠ ⊥),
                  B3 F c Q W M N K d) := by

  obtain ⟨C, hC0, hC⟩ :=
    GcdReduction.core_coefficient_estimate F c hc Q hGood W hW δ hδ
  refine ⟨2 * C, by linarith, ?_⟩
  intro M N K H hM hN hK hH hHN
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hMN : 0 ≤ M * N := by nlinarith [hM, hN]
  have hX1 : 1 ≤ N / H := by
    rw [le_div_iff₀ hHpos]
    simpa using le_of_lt hHN

  obtain ⟨N', hN'1, hN'X, hN'le⟩ : ∃ N' : ℝ, 1 ≤ N' ∧ N' ≤ N / H ∧
      B2env F c Q W M (N / H) K ≤ B2 F c Q W M N' K + M := by
    by_cases hle : B2env F c Q W M (N / H) K ≤ M
    · exact ⟨1, le_rfl, hX1, by linarith [B2_nonneg (F := F) (c := c) Q W M 1 K]⟩
    · rw [not_le] at hle
      have hmem0 : (0 : ℝ) ∈ ({0} ∪
          {x : ℝ | ∃ T : ℝ, 1 ≤ T ∧ T ≤ N / H ∧ x = B2 F c Q W M T K} ∪
          {x : ℝ | N / H < 1 ∧ 1 ≤ 2 * (N / H) ∧ x = B2unitColumn F c Q W M K}) :=
        Or.inl (Or.inl rfl)
      have hlt : B2env F c Q W M (N / H) K - M <
          sSup ({0} ∪
            {x : ℝ | ∃ T : ℝ, 1 ≤ T ∧ T ≤ N / H ∧ x = B2 F c Q W M T K} ∪
            {x : ℝ | N / H < 1 ∧ 1 ≤ 2 * (N / H) ∧ x = B2unitColumn F c Q W M K}) := by
        rw [B2env]
        linarith
      obtain ⟨b, hbS, hb⟩ := exists_lt_of_lt_csSup ⟨0, hmem0⟩ hlt
      have hcases : (b = 0 ∨
          (∃ T : ℝ, 1 ≤ T ∧ T ≤ N / H ∧ b = B2 F c Q W M T K)) ∨
          (N / H < 1 ∧ 1 ≤ 2 * (N / H) ∧ b = B2unitColumn F c Q W M K) := by
        simpa only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
          Set.mem_setOf_eq] using hbS
      rcases hcases with (hb0 | hb1) | hb2
      · exfalso
        rw [hb0] at hb
        linarith
      · obtain ⟨T, hT1, hTX, rfl⟩ := hb1
        exact ⟨T, hT1, hTX, by linarith⟩
      · exact absurd hb2.1 (not_lt.mpr hX1)
  refine ⟨N', hN'1, hN'X, ?_⟩
  set Sg : ℝ := ∑ d ∈ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F H).filter (fun d => d ≠ ⊥),
      B3 F c Q W M N K d with hSg
  have hSg0 : 0 ≤ Sg := by
    rw [hSg]
    exact Finset.sum_nonneg fun d _ => B3_nonneg Q W M N K d
  have hE0 : 0 ≤ B2env F c Q W M (N / H) K :=
    GcdReduction.envelope_nonneg F c Q W hW M (N / H) K hM hX1 hK
  have hA0 : 0 ≤ C * Real.rpow (M * N) δ * (B2env F c Q W M (N / H) K + M + Sg) :=
    mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg hMN δ)) (by linarith)
  have hlift : B2 F c Q W M N K ≤
      C * Real.rpow (M * N) δ * (B2env F c Q W M (N / H) K + M + Sg) :=
    GcdReduction.unit_ball_lift F c Q W M N K _ hA0
      (fun lam => hC M N K H hM hN hK hH hHN lam)
  have hB20 : 0 ≤ B2 F c Q W M N' K := B2_nonneg Q W M N' K
  calc B2 F c Q W M N K
      ≤ C * Real.rpow (M * N) δ * (B2env F c Q W M (N / H) K + M + Sg) := hlift
    _ ≤ C * Real.rpow (M * N) δ * ((B2 F c Q W M N' K + M + Sg) * 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC0 (Real.rpow_nonneg hMN δ))
    _ = 2 * C * Real.rpow (M * N) δ * (B2 F c Q W M N' K + M + Sg) := by ring

end DedekindZetaZeroFree.LargeSieve.Sieve

end
