module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

namespace DedekindZetaZeroFree.Quantitative
namespace NormalizedFubiniMajorant

noncomputable def c : ℂ := (2 * (Real.pi : ℂ))⁻¹

lemma norm_c : ‖c‖ = (2 * Real.pi)⁻¹ := by
  simp [c, Real.pi_pos.le, abs_of_pos Real.pi_pos]

theorem integrable_of_majorant2 (Fn : ℝ × ℝ → ℂ) (hF : AEStronglyMeasurable Fn volume)
    (g : ℝ × ℝ → ℝ) (hg : Integrable g volume) (A : ℝ)
    (hb : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), ‖Fn p‖ ≤ A * g p) :
    Integrable Fn volume :=
  Integrable.mono' (hg.const_mul A) hF hb

theorem integrable_of_majorant2_continuous (Fn : ℝ × ℝ → ℂ) (hF : Continuous Fn)
    (g : ℝ × ℝ → ℝ) (hg : Integrable g volume) (A : ℝ)
    (hb : ∀ p, ‖Fn p‖ ≤ A * g p) :
    Integrable Fn volume :=
  integrable_of_majorant2 Fn hF.aestronglyMeasurable g hg A (Filter.Eventually.of_forall hb)

theorem outer_integrable2 (Fn : ℝ × ℝ → ℂ) (hF : AEStronglyMeasurable Fn volume)
    (g : ℝ × ℝ → ℝ) (hg : Integrable g volume) (A : ℝ)
    (hb : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), ‖Fn p‖ ≤ A * g p) :
    Integrable (fun t : ℝ => c * ∫ s : ℝ, Fn (t, s)) volume :=
  (integrable_of_majorant2 Fn hF g hg A hb).integral_prod_left.const_mul c

theorem norm_double_le (Fn : ℝ × ℝ → ℂ) (hF : AEStronglyMeasurable Fn volume)
    (g : ℝ × ℝ → ℝ) (hg : Integrable g volume) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), ‖Fn p‖ ≤ A * g p) :
    ‖c * ∫ t : ℝ, c * ∫ s : ℝ, Fn (t, s)‖
      ≤ ((2 * Real.pi)⁻¹) ^ 2 * A * ∫ p : ℝ × ℝ, g p := by
  have hI := integrable_of_majorant2 Fn hF g hg A hb
  have h1 : ∫ t : ℝ, c * ∫ s : ℝ, Fn (t, s) = c * ∫ p, Fn p := by
    rw [integral_const_mul, ← integral_prod (fun p : ℝ × ℝ => Fn p) hI]
    rfl
  rw [h1, ← mul_assoc, norm_mul, norm_mul, norm_c]
  have h2 : ‖∫ p, Fn p‖ ≤ A * ∫ p, g p := by
    calc ‖∫ p, Fn p‖ ≤ ∫ p, ‖Fn p‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ p, A * g p := integral_mono_ae hI.norm (hg.const_mul A) hb
      _ = A * ∫ p, g p := integral_const_mul _ _
  have := norm_nonneg c
  calc (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ‖∫ p, Fn p‖
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * (A * ∫ p, g p) := by
        gcongr
    _ = _ := by ring

private lemma reassoc_integrable (Fn : ℝ × ℝ × ℝ → ℂ) (hI : Integrable Fn volume) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => Fn (q.1.1, q.1.2, q.2)) volume := by
  have hm : MeasurePreserving (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ)
      (volume : Measure ((ℝ × ℝ) × ℝ)) volume :=
    MeasureTheory.measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
      (volume : Measure ℝ)
  exact hm.integrable_comp_of_integrable hI

theorem integrable_of_majorant3 (Fn : ℝ × ℝ × ℝ → ℂ) (hF : AEStronglyMeasurable Fn volume)
    (g : ℝ × ℝ × ℝ → ℝ) (hg : Integrable g volume) (A : ℝ)
    (hb : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ × ℝ)), ‖Fn p‖ ≤ A * g p) :
    Integrable Fn volume :=
  Integrable.mono' (hg.const_mul A) hF hb

theorem integrable_of_majorant3_continuous (Fn : ℝ × ℝ × ℝ → ℂ) (hF : Continuous Fn)
    (g : ℝ × ℝ × ℝ → ℝ) (hg : Integrable g volume) (A : ℝ)
    (hb : ∀ p, ‖Fn p‖ ≤ A * g p) :
    Integrable Fn volume :=
  integrable_of_majorant3 Fn hF.aestronglyMeasurable g hg A (Filter.Eventually.of_forall hb)

theorem outer_integrable3 (Fn : ℝ × ℝ × ℝ → ℂ) (hF : AEStronglyMeasurable Fn volume)
    (g : ℝ × ℝ × ℝ → ℝ) (hg : Integrable g volume) (A : ℝ)
    (hb : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ × ℝ)), ‖Fn p‖ ≤ A * g p) :
    Integrable (fun ξ : ℝ => c * ∫ w : ℝ, c * ∫ z : ℝ, Fn (ξ, w, z)) volume := by
  have hI := reassoc_integrable Fn (integrable_of_majorant3 Fn hF g hg A hb)
  have hG : Integrable (fun p : ℝ × ℝ => ∫ z : ℝ, Fn (p.1, p.2, z)) volume :=
    hI.integral_prod_left
  have hG2 : Integrable (fun p : ℝ × ℝ => c * ∫ z : ℝ, Fn (p.1, p.2, z)) volume :=
    hG.const_mul c
  exact hG2.integral_prod_left.const_mul c

theorem norm_triple_le (Fn : ℝ × ℝ × ℝ → ℂ) (hF : AEStronglyMeasurable Fn volume)
    (g : ℝ × ℝ × ℝ → ℝ) (hg : Integrable g volume) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ × ℝ)), ‖Fn p‖ ≤ A * g p) :
    ‖c * ∫ ξ : ℝ, c * ∫ w : ℝ, c * ∫ z : ℝ, Fn (ξ, w, z)‖
      ≤ ((2 * Real.pi)⁻¹) ^ 3 * A * ∫ p : ℝ × ℝ × ℝ, g p := by
  have hI0 := integrable_of_majorant3 Fn hF g hg A hb
  have hI := reassoc_integrable Fn hI0
  have h1 : ∫ ξ : ℝ, c * ∫ w : ℝ, c * ∫ z : ℝ, Fn (ξ, w, z) = c * c * ∫ p, Fn p := by
    have hG : Integrable (fun p : ℝ × ℝ => ∫ z : ℝ, Fn (p.1, p.2, z)) volume :=
      hI.integral_prod_left
    have hm : MeasurePreserving (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ)
        (volume : Measure ((ℝ × ℝ) × ℝ)) volume :=
      MeasureTheory.measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
        (volume : Measure ℝ)
    have h3 : ∫ q : (ℝ × ℝ) × ℝ, Fn (q.1.1, q.1.2, q.2) = ∫ p, Fn p :=
      (hm.integral_comp' Fn)
    have h4 : ∫ q : (ℝ × ℝ) × ℝ, Fn (q.1.1, q.1.2, q.2)
        = ∫ p : ℝ × ℝ, ∫ z : ℝ, Fn (p.1, p.2, z) :=
      integral_prod (fun q : (ℝ × ℝ) × ℝ => Fn (q.1.1, q.1.2, q.2)) hI
    have e1 : ∫ p : ℝ × ℝ, ∫ z : ℝ, Fn (p.1, p.2, z) = ∫ p, Fn p := h4.symm.trans h3
    have e2 : ∫ ξ : ℝ, ∫ w : ℝ, ∫ z : ℝ, Fn (ξ, w, z) = ∫ p, Fn p := by
      rw [← e1]
      exact (integral_prod (fun p : ℝ × ℝ => ∫ z : ℝ, Fn (p.1, p.2, z)) hG).symm
    simp only [integral_const_mul]
    rw [e2]; ring
  rw [h1, norm_mul, norm_mul, norm_mul, norm_c]
  have h2 : ‖∫ p, Fn p‖ ≤ A * ∫ p, g p := by
    calc ‖∫ p, Fn p‖ ≤ ∫ p, ‖Fn p‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ p, A * g p := integral_mono_ae hI0.norm (hg.const_mul A) hb
      _ = A * ∫ p, g p := integral_const_mul _ _
  have hc : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  calc (2 * Real.pi)⁻¹ * ((2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ‖∫ p, Fn p‖)
      = ((2 * Real.pi)⁻¹) ^ 3 * ‖∫ p, Fn p‖ := by ring
    _ ≤ ((2 * Real.pi)⁻¹) ^ 3 * (A * ∫ p, g p) := by gcongr
    _ = _ := by ring

end NormalizedFubiniMajorant
end DedekindZetaZeroFree.Quantitative
