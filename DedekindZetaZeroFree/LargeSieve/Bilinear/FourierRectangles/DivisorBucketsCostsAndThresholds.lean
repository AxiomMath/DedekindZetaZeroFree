module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.MiddleLogarithmicKernelEnvelope
public import DedekindZetaZeroFree.LargeSieve.Bilinear.DivisorRectangleEnvelopes

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteFourierRectangles
open ExplicitTerms
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def divisorScale (j : ℕ) : ℝ := (2 : ℝ) ^ j

def divisorBucket (F : Type) [Field F] [NumberField F] (T : ℝ) (j : ℕ) :
    Finset (Ideal (𝓞 F)) :=
  (boundedNormIdeals F T).filter (fun f => f ≠ ⊥ ∧
    divisorScale j ≤ norm f ∧ norm f < 2 * divisorScale j)

def rectangles (F : Type) [Field F] [NumberField F]
    (B M N n θ Cq : ℝ) : Finset (ℕ × ℕ) :=
  let J := Finset.range (Vendor.dyadicLength (2 * N / n) + 1)
  (J ×ˢ J).filter (fun ij =>
    divisorScale ij.1 ≤ 2 * N / n ∧
    divisorScale ij.2 ≤ 2 * N / n ∧
    divisorScale ij.1 * divisorScale ij.2 ≤ Cq * N * θ / Real.sqrt (B * M) ∧
    (divisorBucket F (2 * N / n) ij.1).Nonempty ∧
    (divisorBucket F (2 * N / n) ij.2).Nonempty)

def U (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) (B X : ℝ) : ℝ :=
  ExplicitTerms.ErrorRectangles.U Q B X

def rectangleValue (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (B N n : ℝ) (ij : ℕ × ℕ) : ℝ :=
  Real.sqrt (divisorScale ij.1 * divisorScale ij.2 *
    U Q B (N / (n * divisorScale ij.1)) *
    U Q B (N / (n * divisorScale ij.2)))

def R (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (B M N n θ Cq : ℝ) : ℝ :=
  sSup ({0} ∪ {z : ℝ | ∃ ij ∈ rectangles F B M N n θ Cq,
    z = rectangleValue Q B N n ij})

def maskedE3 (C : Context Q) (B : ℝ) (unit : Bool)
    (ρ : Ideal (𝓞 F) → ℂ) : ℂ :=
  C.pairSum fun p hp => C.coefficient p *
    ∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
      ∑ a ∈ C.reflectedRows B unit,
        ρ a * C.primitive p hp a * Context.middle C.reflectedKernel (p.1 * p.2)
          (Real.sqrt (C.dualScale e p / norm a)) (C.Y1 B e) (C.Z1 B e) C.L1

def weightedColumn (C : Context Q) (u : Ideal (𝓞 F)) : ℂ :=
  C.lam (C.d * u) / (Real.sqrt (norm u) : ℂ)

def weightedEnergy (C : Context Q) : ℝ :=
  ∑ u ∈ C.columns, ‖weightedColumn C u‖ ^ 2

def frequencyPhase (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F))
    (t s : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi *
    (t * Real.log (norm p.1 / (C.N / norm C.d)) +
     s * Real.log (norm p.2 / (C.N / norm C.d))) : ℝ) : ℂ) * Complex.I)

def frequencyCell (C : Context Q) (e a f₁ f₂ : Ideal (𝓞 F)) (t s : ℝ) : ℂ :=
  C.pairSum fun p hp =>
    if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then
      weightedColumn C p.1 * star (weightedColumn C p.2) *
        C.primitive p hp e * C.primitive p hp a * frequencyPhase C p t s
    else 0

def rectangleCost (C : Context Q) (B : ℝ) (unit : Bool)
    (e : Ideal (𝓞 F)) (ij : ℕ × ℕ) (t s : ℝ) : ℝ :=
  ∑ f₁ ∈ divisorBucket F (2 * C.N / norm C.d) ij.1,
    ∑ f₂ ∈ divisorBucket F (2 * C.N / norm C.d) ij.2,
      ∑ a ∈ C.reflectedRows B unit, ‖frequencyCell C e a f₁ f₂ t s‖

def frequencyWeight (p : ℝ × ℝ) : ℝ :=
  ((1 + p.1 ^ 2) * (1 + p.2 ^ 2))⁻¹

def frequencyCost (C : Context Q) (B Cq : ℝ) (unit : Bool) (t s : ℝ) : ℝ :=
  ∑ e ∈ C.mobiusDivisors, (norm e)⁻¹ *
    ∑ ij ∈ rectangles F B C.M C.N (norm C.d) (Real.rpow (C.M * C.N) C.δ) Cq,
      rectangleCost C B unit e ij t s

def integratedCost (C : Context Q) (B Cq : ℝ) (unit : Bool) : ℝ :=
  ∫ p : ℝ × ℝ, frequencyWeight p * frequencyCost C B Cq unit p.1 p.2

def dualNormCost (C : Context Q) : ℝ :=
  ∑ b ∈ (boundedNormIdeals F C.L1).filter (fun b => b ≠ ⊥), (norm b)⁻¹ ^ 2

def Threshold (C : Context Q) (B Cq : ℝ) : Prop :=
  ∀ e ∈ C.mobiusDivisors,
    C.Z1 B e ≤ Cq * C.N * Real.rpow (C.M * C.N) C.δ / Real.sqrt (B * C.M)

end DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteFourierRectangles

end
