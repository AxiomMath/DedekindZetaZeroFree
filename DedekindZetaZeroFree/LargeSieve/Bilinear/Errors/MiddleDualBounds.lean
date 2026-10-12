module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.Errors.TransformedOrigin
public import DedekindZetaZeroFree.LargeSieve.Bilinear.MiddleDivisorRectangles

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

open MiddleFinite

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

theorem bilinear_error_middle_dual
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : Sieve.AllIndexNormalizedFamilyData Q) (core : D.bad = c)
    (hF : NumberField.IsTotallyComplex F)
    (W : ℝ → ℝ) (hW : Sieve.SieveWeight W) :
    ∃ Cq : ℝ, 1 ≤ Cq ∧ ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 < Cε ∧
        ∀ (M N K δ : ℝ), 1 ≤ M → 1 ≤ N → 0 < δ → 1 ≤ K → K ≤ M →
        ∀ (d : Ideal (𝓞 F)) (hd0 : d ≠ ⊥) (hd : Squarefree d)
          (hdc : d ⊔ c = ⊤),
        1 ≤ (Ideal.absNorm d : ℝ) → (Ideal.absNorm d : ℝ) ≤ 2 * N →
        ∀ (g : Q.G) (lam : Ideal (𝓞 F) → ℂ),
        Function.support lam ⊆ (Sieve.paperShell F c N : Set (Ideal (𝓞 F))) →
        ∀ (B : ℝ) (unit : Bool), 1 ≤ B → B ≤ K → (unit = true → B = 1) →
        let C : Context Q := {
          D := D, core := core, hF := hF,
          M := M, N := N, K := K, δ := δ, W := W, hW := hW,
          d := d, hd0 := hd0, hd := hd, hdc := hdc, g := g, lam := lam }
        let n : ℝ := norm d
        let θ : ℝ := Real.rpow (M * N) δ
        let rhs : ℝ := Cε * Real.rpow (M * N * n) ε *
          Real.rpow (M * N) (C0 * δ) * (n * M / N) *
          MiddleFinite.R Q B M N n θ Cq * Sieve.energy F c N lam
        (‖E3 C B unit‖ ≤ rhs) ∧
        (∀ ρ : Ideal (𝓞 F) → ℂ,
          (∀ a ∈ C.reflectedRows B unit, ‖ρ a‖ ≤ 1) →
          ‖maskedE3 C B unit ρ‖ ≤ rhs) ∧
        (rectangles F B M N n θ Cq = ∅ →
          E3 C B unit = 0 ∧
          ∀ ρ : Ideal (𝓞 F) → ℂ,
            (∀ a ∈ C.reflectedRows B unit, ‖ρ a‖ ≤ 1) →
            maskedE3 C B unit ρ = 0) ∧
        (unit = true → ‖topE3 C‖ ≤ rhs ∧
          (rectangles F B M N n θ Cq = ∅ → topE3 C = 0)) := by
  obtain ⟨Cq, hCq, C0, hC0, h⟩ :=
    bilinear_middle_finite_application F c Q D core hF W hW
  refine ⟨Cq, hCq, C0, hC0, ?_⟩
  intro ε hε
  obtain ⟨Cε, hCε, hbound⟩ := h ε hε
  refine ⟨Cε, hCε, ?_⟩
  intro M N K δ hM hN hδ hK hKM d hd0 hd hdc hn hnN g lam hlam B unit hB hBK hu
  have hMN : 0 ≤ M * N := mul_nonneg (by linarith) (by linarith)
  have hpow : Real.rpow (Real.rpow (M * N) δ) C0 =
      Real.rpow (M * N) (C0 * δ) := by
    change ((M * N) ^ δ) ^ C0 = (M * N) ^ (C0 * δ)
    rw [← Real.rpow_mul hMN, mul_comm δ C0]
  simpa only [hpow] using
    hbound M N K δ hM hN hδ hK hKM d hd0 hd hdc hnN g lam hlam B unit hB hBK hu

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

end
