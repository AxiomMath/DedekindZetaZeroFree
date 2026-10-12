module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.SectorGramEstimate

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

theorem initial_gram_to_exponent
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (hdiag : ∃ D : ℝ, 0 ≤ D ∧
      ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
        ∀ b ∈ paperShell F c N, ‖initialGram F Q M b b‖ ≤ D * M)
    (hoffdiag : ∀ ε : ℝ, 0 < ε → ∃ H : ℝ, 0 ≤ H ∧
      ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
        ∀ b1 ∈ paperShell F c N, ∀ b2 ∈ paperShell F c N,
          Q.cls b1 = Q.cls b2 → b1 ≠ b2 →
            ‖initialGram F Q M b1 b2‖ ≤ H * Real.rpow N (1 + ε)) :
    HasSieveExponent F c Q (2 : ℝ) := by
  intro ε hε
  obtain ⟨D, hD, hDiag⟩ := hdiag
  obtain ⟨H, hH, hOff⟩ := hoffdiag ε hε
  obtain ⟨C₀, hC₀, hSect⟩ := initial_conditional_sector F ε D H hε hD hH
  letI : Finite Q.G := Q.instFinite
  letI : Fintype Q.G := Fintype.ofFinite Q.G
  refine ⟨(Fintype.card Q.G : ℝ) * C₀, by positivity, ?_⟩
  intro M N hM hN
  have hcs : ∀ z : Q.G → ℂ, ‖∑ g, z g‖ ^ 2 ≤ (Fintype.card Q.G : ℝ) * ∑ g, ‖z g‖ ^ 2 := by
    intro z
    have h1 : ‖∑ g, z g‖ ≤ ∑ g, ‖z g‖ := norm_sum_le _ _
    have h2 : (∑ g, ‖z g‖) ^ 2 ≤ (Fintype.card Q.G : ℝ) * ∑ g, ‖z g‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Q.G)) (f := fun g => ‖z g‖)
      simpa [Finset.card_univ] using this
    calc ‖∑ g, z g‖ ^ 2 ≤ (∑ g, ‖z g‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hQ1 : ∀ lam : Ideal (𝓞 F) → ℂ, energy F c N lam ≤ 1 →
      Q1 F c Q M N lam ≤ (Fintype.card Q.G : ℝ) * C₀ * (M + Real.rpow N (2 + ε)) := by
    intro lam hlam
    have hrow : ∀ a : Ideal (𝓞 F), rowSum Q N lam a =
        ∑ g : Q.G, ∑ b ∈ (paperShell F c N).filter (fun b => Q.cls b = g),
          lam b * (Q.χ b) a := by
      intro a
      rw [rowSum]
      exact (Finset.sum_fiberwise (paperShell F c N) Q.cls (fun b => lam b * (Q.χ b) a)).symm
    have hfib : ∑ g : Q.G, ∑ b ∈ (paperShell F c N).filter (fun b => Q.cls b = g), ‖lam b‖ ^ 2
        = energy F c N lam := by
      rw [energy]
      exact Finset.sum_fiberwise (paperShell F c N) Q.cls (fun b => ‖lam b‖ ^ 2)
    have hsec : ∀ g : Q.G,
        ∑ a ∈ paperShell F c M,
            ‖∑ b ∈ (paperShell F c N).filter (fun b => Q.cls b = g),
              lam b * (Q.χ b) a‖ ^ 2 ≤
          C₀ * (M + Real.rpow N (2 + ε)) *
            ∑ b ∈ (paperShell F c N).filter (fun b => Q.cls b = g), ‖lam b‖ ^ 2 :=
      fun g => hSect c Q hDiag hOff M N hM hN g lam
    have hfac : 0 ≤ C₀ * (M + Real.rpow N (2 + ε)) :=
      mul_nonneg hC₀ (add_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _))
    calc Q1 F c Q M N lam
        = ∑ a ∈ paperShell F c M,
            ‖∑ g : Q.G, ∑ b ∈ (paperShell F c N).filter (fun b => Q.cls b = g),
              lam b * (Q.χ b) a‖ ^ 2 := by
          rw [Q1]
          exact Finset.sum_congr rfl (fun a _ => by rw [hrow a])
      _ ≤ ∑ a ∈ paperShell F c M, (Fintype.card Q.G : ℝ) *
            ∑ g : Q.G, ‖∑ b ∈ (paperShell F c N).filter (fun b => Q.cls b = g),
              lam b * (Q.χ b) a‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro a _
          exact hcs _
      _ = (Fintype.card Q.G : ℝ) * ∑ a ∈ paperShell F c M,
            ∑ g : Q.G, ‖∑ b ∈ (paperShell F c N).filter (fun b => Q.cls b = g),
              lam b * (Q.χ b) a‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ = (Fintype.card Q.G : ℝ) * ∑ g : Q.G,
            ∑ a ∈ paperShell F c M, ‖∑ b ∈ (paperShell F c N).filter (fun b => Q.cls b = g),
              lam b * (Q.χ b) a‖ ^ 2 := by
          rw [Finset.sum_comm]
      _ ≤ (Fintype.card Q.G : ℝ) * ∑ g : Q.G,
            C₀ * (M + Real.rpow N (2 + ε)) *
              ∑ b ∈ (paperShell F c N).filter (fun b => Q.cls b = g), ‖lam b‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro g _
          exact hsec g
      _ = (Fintype.card Q.G : ℝ) * (C₀ * (M + Real.rpow N (2 + ε)) *
            ∑ g : Q.G, ∑ b ∈ (paperShell F c N).filter (fun b => Q.cls b = g), ‖lam b‖ ^ 2) := by
          rw [← Finset.mul_sum]
      _ = (Fintype.card Q.G : ℝ) * (C₀ * (M + Real.rpow N (2 + ε)) * energy F c N lam) := by
          rw [hfib]
      _ ≤ (Fintype.card Q.G : ℝ) * (C₀ * (M + Real.rpow N (2 + ε)) * 1) := by
          apply mul_le_mul_of_nonneg_left _
          · positivity
          · exact mul_le_mul_of_nonneg_left hlam hfac
      _ = (Fintype.card Q.G : ℝ) * (C₀ * (M + Real.rpow N (2 + ε))) := by rw [mul_one]
      _ = (Fintype.card Q.G : ℝ) * C₀ * (M + Real.rpow N (2 + ε)) := by ac_rfl
  have hB1 : B1 F c Q M N ≤ (Fintype.card Q.G : ℝ) * C₀ * (M + Real.rpow N (2 + ε)) := by
    rw [B1]
    apply csSup_le
    · exact ⟨0, by simp⟩
    · rintro x (rfl | ⟨lam, hlam, rfl⟩)
      · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC₀)
          (add_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _))
      · exact hQ1 lam hlam
  have hstep : (Fintype.card Q.G : ℝ) * C₀ * (M + Real.rpow N (2 + ε)) ≤
      (Fintype.card Q.G : ℝ) * C₀ * (Real.rpow (M * N) ε * (M + Real.rpow N 2)) := by
    have hcard : 0 ≤ (Fintype.card Q.G : ℝ) * C₀ := by positivity
    apply mul_le_mul_of_nonneg_left _ hcard
    have hMpos : 0 < M := by linarith
    have hNpos : 0 < N := by linarith
    have hMNpos : 0 < M * N := mul_pos hMpos hNpos
    have hMN1 : 1 ≤ M * N := by nlinarith
    have hA : M ≤ Real.rpow (M * N) ε * M := by
      have h1 : 1 ≤ Real.rpow (M * N) ε := Real.one_le_rpow hMN1 (le_of_lt hε)
      nlinarith [h1, le_of_lt hMpos, Real.rpow_nonneg (le_of_lt hMNpos) ε]
    have hB : Real.rpow N 2 * Real.rpow N ε ≤ Real.rpow (M * N) ε * Real.rpow N 2 := by
      have h1 : Real.rpow N ε ≤ Real.rpow (M * N) ε :=
        Real.rpow_le_rpow (le_of_lt hNpos) (by nlinarith) (le_of_lt hε)
      have h2 : 0 ≤ Real.rpow N 2 := Real.rpow_nonneg (le_of_lt hNpos) 2
      calc Real.rpow N 2 * Real.rpow N ε ≤ Real.rpow N 2 * Real.rpow (M * N) ε :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = Real.rpow (M * N) ε * Real.rpow N 2 := mul_comm _ _
    have hN2 : Real.rpow N (2 + ε) = Real.rpow N 2 * Real.rpow N ε := Real.rpow_add hNpos 2 ε
    calc M + Real.rpow N (2 + ε) = M + Real.rpow N 2 * Real.rpow N ε := by rw [hN2]
      _ ≤ Real.rpow (M * N) ε * M + Real.rpow (M * N) ε * Real.rpow N 2 := add_le_add hA hB
      _ = Real.rpow (M * N) ε * (M + Real.rpow N 2) := by rw [mul_add]
  calc B1 F c Q M N ≤ (Fintype.card Q.G : ℝ) * C₀ * (M + Real.rpow N (2 + ε)) := hB1
    _ ≤ (Fintype.card Q.G : ℝ) * C₀ * (Real.rpow (M * N) ε * (M + Real.rpow N 2)) := hstep
    _ = (Fintype.card Q.G : ℝ) * C₀ * Real.rpow (M * N) ε * (M + Real.rpow N 2) := by
        ac_rfl

end DedekindZetaZeroFree.LargeSieve.Sieve
