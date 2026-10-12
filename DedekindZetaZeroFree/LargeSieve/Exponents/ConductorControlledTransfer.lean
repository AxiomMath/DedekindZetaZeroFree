module

public import DedekindZetaZeroFree.LargeSieve.Exponents.ConductorControlledBandBootstrap
public import DedekindZetaZeroFree.LargeSieve.Bilinear.ExceptionalShellSharpBounds

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

theorem hasSieveExponent_one_from_core
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (hc : c ≠ ⊥)
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (H : ∀ b : Ideal (𝓞 F), Squarefree b → b ⊔ c = ⊤ →
      Q.cond b ∣ b * q ∧ b ∣ Q.cond b * q)
    (hCore : HasSieveExponent F q (restrictFamily Q q hcq) 1) :
    HasSieveExponent F c Q 1 := by
  intro ε hε

  obtain ⟨Ccore, hCcore, hBcore⟩ := hCore ε hε

  obtain ⟨A, hA1, hAcard, _⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound_finset F
  refine ⟨peelingSharpConstant F c Q q Ccore A, ?_, ?_⟩
  · exact peelingSharpConstant_nonneg Q q Ccore A hCcore hA1
  · intro M N hM hN

    have hcore : ∀ S T : ℝ, 1 ≤ S → 1 ≤ T → ∀ μ : Ideal (𝓞 F) → ℂ,
        (∑ v ∈ paperShell F q S, ‖∑ u ∈ paperShell F q T, μ u * (Q.χ u) v‖ ^ 2) ≤
          Ccore * (S * T) ^ ε * (S + T) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2 := by
      intro S T hS hT μ
      have h1 := Q1_le_B1_mul_energy (restrictFamily Q q hcq) S T μ
      simp only [Q1, rowSum, restrictFamily_χ] at h1
      have h2 : B1 F q (restrictFamily Q q hcq) S T ≤
          Ccore * (S * T) ^ ε * (S + T) := by
        simpa [Real.rpow_one] using hBcore S T hS hT
      have hE : 0 ≤ energy F q T μ := by
        rw [energy]
        exact Finset.sum_nonneg (fun b _ => by positivity)
      calc (∑ v ∈ paperShell F q S, ‖∑ u ∈ paperShell F q T, μ u * (Q.χ u) v‖ ^ 2)
          ≤ B1 F q (restrictFamily Q q hcq) S T * energy F q T μ := h1
        _ ≤ (Ccore * (S * T) ^ ε * (S + T)) * energy F q T μ :=
            mul_le_mul_of_nonneg_right h2 hE
        _ = Ccore * (S * T) ^ ε * (S + T) * energy F q T μ := by ring

    have hbound : B1 F c Q M N ≤
        peelingSharpConstant F c Q q Ccore A * (M * N) ^ ε * (M + N) := by
      rw [B1]
      apply csSup_le
      · exact ⟨0, Or.inl rfl⟩
      · rintro x (rfl | ⟨lam, hlam, rfl⟩)
        · have hP := peelingSharpConstant_nonneg Q q Ccore A hCcore hA1
          have hMN : 0 ≤ (M * N) ^ ε :=
            Real.rpow_nonneg (by nlinarith [hM, hN]) ε
          exact mul_nonneg (mul_nonneg hP hMN) (by linarith)
        · have hp := peeling_sharp_domination_bound Q q hq hcq H ε Ccore A
            (le_of_lt hε) hCcore hA1 hAcard hcore M N hM hN lam
          have hfac : 0 ≤ peelingSharpConstant F c Q q Ccore A * (M * N) ^ ε *
              (M + N) := by
            have hP := peelingSharpConstant_nonneg Q q Ccore A hCcore hA1
            have hMN : 0 ≤ (M * N) ^ ε :=
              Real.rpow_nonneg (by nlinarith [hM, hN]) ε
            exact mul_nonneg (mul_nonneg hP hMN) (by linarith)
          calc Q1 F c Q M N lam ≤
                peelingSharpConstant F c Q q Ccore A * (M * N) ^ ε * (M + N) *
                  energy F c N lam := hp
            _ ≤ peelingSharpConstant F c Q q Ccore A * (M * N) ^ ε * (M + N) * 1 :=
                mul_le_mul_of_nonneg_left hlam hfac
            _ = peelingSharpConstant F c Q q Ccore A * (M * N) ^ ε * (M + N) := by
                rw [mul_one]
    simpa [Real.rpow_one] using hbound

theorem hasSieveExponent_one_of_core_transfer
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) :
    HasSieveExponent F c Q 1 := by
  by_cases hc : c = ⊥
  · subst hc
    intro ε hε
    refine ⟨0, le_refl 0, ?_⟩
    intro M N hM hN
    rw [B1_bottom_eq_zero F Q M N hM]
    simp
  · obtain ⟨q, hq, hcq, H, hgood⟩ := exists_coreGood_restrictFamily hc Q
    exact hasSieveExponent_one_from_core F c hc Q q hq hcq H
      (hasSieveExponent_one_core F hF q hq (restrictFamily Q q hcq) hgood)

end DedekindZetaZeroFree.LargeSieve.Sieve
