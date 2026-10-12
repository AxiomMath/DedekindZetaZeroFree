module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

@[expose] public section

namespace DedekindZetaZeroFree.SourceSheet.Differentiation
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

structure TwoDerivativeData {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    (f : ℕ → ℝ → Y → ℂ) : Prop where
  measurable : ∀ j ≤ 2, ∀ t, AEStronglyMeasurable (f j t) μ
  derivative : ∀ j < 2, ∀ y t, HasDerivAt (fun u => f j u y) (f (j + 1) t y) t
  continuous_two : ∀ y, Continuous (fun t => f 2 t y)
  local_bound : ∀ t : ℝ, ∃ s ∈ 𝓝 t, ∃ B : Y → ℝ,
    Integrable B μ ∧ ∀ᵐ y ∂μ, ∀ u ∈ s, ∀ j ≤ 2, ‖f j u y‖ ≤ B y

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}
    {f : ℕ → ℝ → Y → ℂ}

lemma TwoDerivativeData.integrable (h : TwoDerivativeData μ f) (j : ℕ)
    (hj : j ≤ 2) (t : ℝ) : Integrable (f j t) μ := by
  obtain ⟨s, hs, B, hB, hb⟩ := h.local_bound t
  exact hB.mono' (h.measurable j hj t)
    (hb.mono fun y hy => hy t (mem_of_mem_nhds hs) j hj)

lemma TwoDerivativeData.hasDerivAt_integral (h : TwoDerivativeData μ f)
    (j : ℕ) (hj : j < 2) (t : ℝ) :
    HasDerivAt (fun u => ∫ y, f j u y ∂μ) (∫ y, f (j + 1) t y ∂μ) t := by
  obtain ⟨s, hs, B, hB, hb⟩ := h.local_bound t
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall (h.measurable j (by omega)))
    (h.integrable j (by omega) t) (h.measurable (j + 1) (by omega) t)
    (hb.mono fun y hy u hu => hy u hu (j + 1) (by omega)) hB
    (Eventually.of_forall fun y u _ => h.derivative j hj y u)).2

lemma TwoDerivativeData.continuous_integral_two (h : TwoDerivativeData μ f) :
    Continuous (fun t => ∫ y, f 2 t y ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨s, hs, B, hB, hb⟩ := h.local_bound t
  apply continuousAt_of_dominated
    (Eventually.of_forall (h.measurable 2 le_rfl))
    (mem_of_superset hs fun u hu => hb.mono fun y hy => hy u hu 2 le_rfl) hB
  exact Eventually.of_forall fun y => (h.continuous_two y).continuousAt

theorem TwoDerivativeData.integral_calculus (h : TwoDerivativeData μ f) :
    ContDiff ℝ 2 (fun t => ∫ y, f 0 t y ∂μ) ∧
    ∀ j ≤ 2, ∀ t, iteratedDeriv j (fun u => ∫ y, f 0 u y ∂μ) t =
      ∫ y, f j t y ∂μ := by
  have hd0 : deriv (fun u => ∫ y, f 0 u y ∂μ) =
      (fun u => ∫ y, f 1 u y ∂μ) :=
    funext fun t => (h.hasDerivAt_integral 0 (by omega) t).deriv
  have hd1 : deriv (fun u => ∫ y, f 1 u y ∂μ) =
      (fun u => ∫ y, f 2 u y ∂μ) :=
    funext fun t => (h.hasDerivAt_integral 1 (by omega) t).deriv
  constructor
  · rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    refine ⟨fun t => (h.hasDerivAt_integral 0 (by omega) t).differentiableAt, ?_, ?_⟩
    · simp
    · rw [hd0, contDiff_one_iff_deriv, hd1]
      exact ⟨fun t => (h.hasDerivAt_integral 1 (by omega) t).differentiableAt,
        h.continuous_integral_two⟩
  · intro j hj t
    interval_cases j <;> simp [iteratedDeriv_succ, hd0, hd1]
end
end DedekindZetaZeroFree.SourceSheet.Differentiation
