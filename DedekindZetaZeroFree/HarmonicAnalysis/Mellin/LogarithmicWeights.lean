module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.EulerDerivativesAndDecay

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve.Vendor

structure LogMellinPhysical (f : ℝ → ℂ) (δ : ℝ) (P : Polynomial ℂ) : Prop where
  delta_pos : 0 < δ
  contDiffOn : ContDiffOn ℝ ∞ f (Set.Ioi 0)
  rapid_decay : ∀ j n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
    ‖EulerIter j f x‖ ≤ C * Real.rpow x (-(n : ℝ))
  origin_remainder : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
    ‖EulerIter j (fun y => f y - P.eval (Real.log y : ℂ)) x‖ ≤ C * Real.rpow x δ

def logPrincipalPart (P : Polynomial ℂ) (s : ℂ) : ℂ :=
  ∑ k ∈ P.support,
    ((-1 : ℂ) ^ k * (k.factorial : ℂ) * P.coeff k) / s ^ (k + 1)

structure LogMellinAdmissible (f : ℝ → ℂ) (δ : ℝ) (P : Polynomial ℂ)
    (H : ℂ → ℂ) : Prop where
  physical : LogMellinPhysical f δ P
  eq_mellin : ∀ s : ℂ, 0 < s.re → H s = mellin f s
  holomorphic_remainder : ∃ A : ℂ → ℂ,
    (∀ s : ℂ, -δ < s.re → DifferentiableAt ℂ A s) ∧
    ∀ s : ℂ, -δ < s.re → s ≠ 0 → H s = A s + logPrincipalPart P s
  rapid_vertical_decay : ∀ u v : ℝ, -δ < u → u ≤ v → ∀ N : ℕ,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, u ≤ σ → σ ≤ v → 1 ≤ |t| →
      (1 + |t|) ^ N * ‖H ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C

theorem logPrincipalPart_differentiableAt (P : Polynomial ℂ) (s : ℂ) (hs : s ≠ 0) :
    DifferentiableAt ℂ (logPrincipalPart P) s := by
  change DifferentiableAt ℂ (fun s => ∑ k ∈ P.support,
    ((-1 : ℂ) ^ k * (k.factorial : ℂ) * P.coeff k) / s ^ (k + 1)) s
  refine DifferentiableAt.fun_sum (fun k _ => ?_)
  have hne : s ^ (k + 1) ≠ 0 := pow_ne_zero _ hs
  exact (differentiableAt_const _).div (by fun_prop) hne

namespace LogMellinAdmissible

variable {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}

theorem delta_pos (h : LogMellinAdmissible f δ P H) : 0 < δ := h.physical.delta_pos

theorem contDiffOn (h : LogMellinAdmissible f δ P H) :
    ContDiffOn ℝ ∞ f (Set.Ioi 0) := h.physical.contDiffOn

theorem rapid_decay (h : LogMellinAdmissible f δ P H) (j n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖EulerIter j f x‖ ≤ C * Real.rpow x (-(n : ℝ)) := h.physical.rapid_decay j n

theorem origin_remainder (h : LogMellinAdmissible f δ P H) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖EulerIter j (fun y => f y - P.eval (Real.log y : ℂ)) x‖ ≤ C * Real.rpow x δ :=
  h.physical.origin_remainder j

theorem differentiableAt (h : LogMellinAdmissible f δ P H) (s : ℂ)
    (hs : -δ < s.re) (hs0 : s ≠ 0) : DifferentiableAt ℂ H s := by
  obtain ⟨A, hA, hHA⟩ := h.holomorphic_remainder
  have hopen : IsOpen {z : ℂ | -δ < z.re ∧ z ≠ 0} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have heq : H =ᶠ[nhds s] (fun z => A z + logPrincipalPart P z) := by
    filter_upwards [hopen.mem_nhds (show s ∈ {z : ℂ | -δ < z.re ∧ z ≠ 0} from ⟨hs, hs0⟩)]
      with z hz
    exact hHA z hz.1 hz.2
  exact ((hA s hs).add (logPrincipalPart_differentiableAt P s hs0)).congr_of_eventuallyEq heq

end LogMellinAdmissible
end DedekindZetaZeroFree.LargeSieve.Vendor

end
