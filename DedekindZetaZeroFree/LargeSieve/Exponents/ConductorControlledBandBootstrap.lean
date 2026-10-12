module

public import DedekindZetaZeroFree.LargeSieve.Exponents.ConductorControlledRecursiveEnvelope
public import DedekindZetaZeroFree.LargeSieve.Exponents.InitialExponentTwo
public import DedekindZetaZeroFree.LargeSieve.Bilinear.RationalPrimeInflationAndDyadicTransport
public import DedekindZetaZeroFree.LargeSieve.Exponents.FiniteBandImprovement
public import DedekindZetaZeroFree.LargeSieve.Exponents.BootstrapIteration

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Sieve

private theorem core_band_hypothesis
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (hc : c ≠ ⊥)
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) (hCore : CoreGood Q) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ (A : ℝ) (J : ℕ) (D : ℝ), 1 ≤ A ∧ 0 < D ∧
        ∀ M N V : ℝ, 1 ≤ M → 1 ≤ N → M ≤ V →
          B1 F c Q M N ≤ D * ∑ j ∈ Finset.range (J + 1),
            B1 F c Q ((2 : ℝ) ^ j * A * V * (2 * M * N) ^ δ) N := by
  intro δ hδ hδ1
  let d : ℕ := Module.finrank ℚ F
  let H : ℝ := max 2 (max ((NumberField.discr F).natAbs : ℝ) (Ideal.absNorm c : ℝ))
  refine ⟨H ^ d, (Nat.ceil (6 * (d : ℝ) / δ) + 1) * d, 4, ?_, by norm_num, ?_⟩
  · have hH : (1 : ℝ) ≤ H := by
      have : (2 : ℝ) ≤ H := le_max_left 2 _
      linarith
    exact one_le_pow₀ hH
  · intro M N V hM hN hV
    have h := rational_band_inflation F c hc Q c hc (dvd_refl c)
      (fun b hb hbq => (hCore b hb hbq).2) δ hδ hδ1 M N V hM hN hV
    simpa only [mul_assoc] using h

theorem hasSieveExponent_one_core
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (c : Ideal (𝓞 F)) (hc : c ≠ ⊥)
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (hCore : CoreGood Q) :
    HasSieveExponent F c Q 1 := by

  have hTwo : DedekindZetaZeroFree.LargeSieve.HasExponent (B1 F c Q) 2 :=
    DedekindZetaZeroFree.LargeSieve.exponent_initial F hF c Q

  have hImprove : ∀ α : ℝ, 1 < α → α ≤ 2 → DedekindZetaZeroFree.LargeSieve.HasExponent (B1 F c Q) α →
      DedekindZetaZeroFree.LargeSieve.HasExponent (B1 F c Q) (2 - 1 / α) := by
    intro α hα1 hα2 hExp

    have hCanon : HasSieveExponent F c Q α := by
      intro ε hε
      obtain ⟨C, hC, hb⟩ := hExp ε hε
      exact ⟨C, le_of_lt hC, hb⟩
    exact DedekindZetaZeroFree.LargeSieve.HasRecursiveEnvelope.improve_of_band
      (fun M N _ _ => B1_nonneg Q M N)
      (core_band_hypothesis F c hc Q hCore) (le_of_lt hα1) hα2
      (recursiveEnvelope_of_core F hF c hc Q hCore α (le_of_lt hα1) hα2 hCanon)

  have hOne : DedekindZetaZeroFree.LargeSieve.HasExponent (B1 F c Q) 1 :=
    DedekindZetaZeroFree.LargeSieve.hasExponent_one_of_improvement (B1 F c Q) hTwo hImprove
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hOne ε hε
  exact ⟨C, le_of_lt hC, hbound⟩

end DedekindZetaZeroFree.LargeSieve.Sieve
