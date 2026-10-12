module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.ConductorControlledGcdReduction
public import DedekindZetaZeroFree.LargeSieve.Bilinear.ConductorControlledCutoffEstimate

@[expose] public section

noncomputable section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Sieve

theorem oneStepWeightedDescent_core
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (c : Ideal (𝓞 F)) (hc : c ≠ ⊥)
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) (hGood : CoreGood Q)
    (W : ℝ → ℝ) (hW : SieveWeight W) (α : ℝ) (hα : 1 ≤ α)
    (hα₂ : α ≤ 2) (hExponent : HasSieveExponent F c Q α) :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 ≤ A ∧
      ∀ M N H K : ℝ, 1 ≤ M → 1 ≤ N → 1 ≤ H → H < N →
        0 < K → K < M / 2 →
        N ^ 2 / M * Real.rpow (M * N) δ ≤ K →
        K ≤ M * Real.rpow (M * N) (-δ) →
        ∃ n' : ℝ, 1 ≤ n' ∧ n' ≤ N / H ∧
          B2 F c Q W M N K ≤
            A * Real.rpow (M * N) δ * B2 F c Q W M n' K +
              A * H ^ 5 * Real.rpow (M * N) δ *
                (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                  Real.sqrt (M / K) * N) := by
  intro δ hδ
  have hhalf : 0 < δ / 2 := by linarith
  obtain ⟨Cg, hCg, hgcd⟩ :=
    bilinear_gcd_reduction_core F c hc Q hGood W hW (δ / 2) hhalf
  obtain ⟨Cp, hCp, hprop⟩ :=
    bilinear_prop51_core hF c hc Q hGood W hW hα hα₂ hExponent (δ / 2) hhalf
  obtain ⟨Ci, hCi, hcount⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound F
  let A : ℝ := max 1 (Cg * (1 + Cp * Ci))
  have hCi0 : 0 ≤ Ci := le_trans zero_le_one hCi
  have hprod : 0 ≤ Cp * Ci := mul_nonneg hCp hCi0
  have hCgA : Cg ≤ A :=
    (le_mul_of_one_le_right hCg (by linarith : 1 ≤ 1 + Cp * Ci)).trans
      (le_max_right _ _)
  have hCA : Cg * (1 + Cp * Ci) ≤ A := le_max_right _ _
  refine ⟨A, le_max_left _ _, ?_⟩
  intro M N H K hM hN hH hHN hK hKM hKlo hKhi
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hMN1 : 1 ≤ M * N := by nlinarith
  have hMNpos : 0 < M * N := lt_of_lt_of_le zero_lt_one hMN1
  have hlo : N ^ 2 / M * Real.rpow (M * N) (δ / 2) ≤ K := by
    apply le_trans _ hKlo
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hMN1 (by linarith))
      (div_nonneg (sq_nonneg N) hM0)
  have hhi : K ≤ M * Real.rpow (M * N) (-(δ / 2)) := by
    apply le_trans hKhi
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hMN1 (by linarith)) hM0
  obtain ⟨n', hn'1, hn'H, hred⟩ := hgcd M N K H hM hN hK hH hHN
  refine ⟨n', hn'1, hn'H, ?_⟩
  let p : ℝ := Real.rpow (M * N) (δ / 2)
  let E : ℝ := M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
    Real.sqrt (M / K) * N
  let s := (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F H).filter (fun d => d ≠ ⊥)
  have hp1 : 1 ≤ p := Real.one_le_rpow hMN1 (le_of_lt hhalf)
  have hp0 : 0 ≤ p := le_trans zero_le_one hp1
  have hpδ : p ≤ Real.rpow (M * N) δ :=
    Real.rpow_le_rpow_of_exponent_le hMN1 (by linarith)
  have hp2 : p * p = Real.rpow (M * N) δ := by
    dsimp [p]
    rw [← Real.rpow_add hMNpos]
    congr 1
    ring
  have hE : M ≤ E := by
    have h1 : 0 ≤ Real.sqrt M * Real.rpow K (α - 1 / 2) :=
      mul_nonneg (Real.sqrt_nonneg M) (Real.rpow_nonneg (le_of_lt hK) _)
    have h2 : 0 ≤ Real.sqrt (M / K) * N :=
      mul_nonneg (Real.sqrt_nonneg _) hN0
    change M ≤ M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
      Real.sqrt (M / K) * N
    linarith only [hN0, h1, h2]
  have hE0 : 0 ≤ E := hM0.trans hE
  have hH5 : 1 ≤ H ^ 5 := one_le_pow₀ hH
  have hS : (∑ d ∈ s, B3 F c Q W M N K d) ≤
      Cp * Ci * H ^ 5 * p * E := by
    have hd : ∀ d ∈ s, B3 F c Q W M N K d ≤ Cp * H ^ 4 * p * E := by
      intro d hd
      have hn : (Ideal.absNorm d : ℝ) ≤ H :=
        DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals.mp (Finset.mem_filter.mp hd).1
      have hn0 : (0 : ℝ) ≤ (Ideal.absNorm d : ℝ) := Nat.cast_nonneg _
      exact (hprop M N K hM hN hK hlo hhi d).trans (by
        dsimp [p, E]
        gcongr)
    have hcard : (s.card : ℝ) ≤ Ci * H := by
      have hc' : (s.card : ℝ) ≤ ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F H).card : ℝ) := by
        exact_mod_cast Finset.card_filter_le (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F H) _
      exact hc'.trans (hcount H hH)
    calc
      (∑ d ∈ s, B3 F c Q W M N K d) ≤ ∑ d ∈ s, Cp * H ^ 4 * p * E :=
        Finset.sum_le_sum hd
      _ = (s.card : ℝ) * (Cp * H ^ 4 * p * E) := by simp
      _ ≤ (Ci * H) * (Cp * H ^ 4 * p * E) := by
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = Cp * Ci * H ^ 5 * p * E := by ring
  have hres : M ≤ H ^ 5 * p * E := by
    calc
      M ≤ E := hE
      _ ≤ H ^ 5 * p * E := by
        have hh : 1 ≤ H ^ 5 * p := by nlinarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hh) hE0]
  have hB0 : 0 ≤ B2 F c Q W M n' K := B2_nonneg Q W M n' K
  have hA0 : 0 ≤ A := le_trans zero_le_one (le_max_left _ _)
  change B2 F c Q W M N K ≤
    A * Real.rpow (M * N) δ * B2 F c Q W M n' K +
      A * H ^ 5 * Real.rpow (M * N) δ * E
  calc
    B2 F c Q W M N K ≤ Cg * p *
        (B2 F c Q W M n' K + M + ∑ d ∈ s, B3 F c Q W M N K d) := hred
    _ ≤ Cg * p * (B2 F c Q W M n' K + H ^ 5 * p * E +
        Cp * Ci * H ^ 5 * p * E) := by
      gcongr
    _ = Cg * p * B2 F c Q W M n' K +
        (Cg * (1 + Cp * Ci)) * H ^ 5 * (p * p) * E := by ring
    _ ≤ A * Real.rpow (M * N) δ * B2 F c Q W M n' K +
        A * H ^ 5 * Real.rpow (M * N) δ * E := by
      rw [hp2]
      have hδ0 : 0 ≤ Real.rpow (M * N) δ := Real.rpow_nonneg (le_of_lt hMNpos) δ
      gcongr

end DedekindZetaZeroFree.LargeSieve.Sieve

end
