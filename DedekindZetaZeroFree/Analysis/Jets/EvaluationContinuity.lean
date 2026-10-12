module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxPrincipalSeriesEvaluationContinuity
open Set Filter Topology
open scoped ContDiff
section
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul ℝ E] [BarrelledSpace ℝ E]
    (A : E →ₗ[ℝ] (ℂ → ℂ)) (hA : ∀ f, ContDiff ℝ (⊤ : ℕ∞) (A f))

noncomputable def derivativeEvaluationLinearMap (n : ℕ) (x : ℂ) : E →ₗ[ℝ] (ℂ [×n]→L[ℝ] ℂ) where
  toFun f := iteratedFDeriv ℝ n (A f) x
  map_add' f g := by
    rw [A.map_add]
    exact congrFun (iteratedFDeriv_add ((hA f).of_le (by simp)) ((hA g).of_le (by simp))) x
  map_smul' c f := by
    rw [A.map_smul]
    exact iteratedFDeriv_const_smul_apply ((hA f).contDiffAt.of_le (by simp))

lemma derivativeEvaluation_continuous (hA : ∀ f, ContDiff ℝ (⊤ : ℕ∞) (A f))
    (hcont : ∀ x : ℂ, Continuous (fun f => A f x)) :
    ∀ n : ℕ, ∀ x : ℂ, Continuous (fun f => iteratedFDeriv ℝ n (A f) x) := by
  intro n
  induction n with
  | zero =>
    intro x
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ ℂ ℂ).symm.continuous.comp (hcont x)
  | succ n ih =>
    intro x
    have hc : Continuous (fun f => fderiv ℝ (iteratedFDeriv ℝ n (A f)) x) := by
      apply continuous_clm_apply.mpr
      intro v
      let D (t : ℝ) : E →L[ℝ] (ℂ [×n]→L[ℝ] ℂ) :=
        t⁻¹ • ((⟨derivativeEvaluationLinearMap A hA n (x + t • v), ih _⟩ : E →L[ℝ] _) -
          (⟨derivativeEvaluationLinearMap A hA n x, ih _⟩ : E →L[ℝ] _))
      have ht : Tendsto (fun t f => D t f) (𝓝[≠] (0 : ℝ))
          (𝓝 (fun f => fderiv ℝ (iteratedFDeriv ℝ n (A f)) x v)) := by
        rw [tendsto_pi_nhds]
        intro f
        have hd : Differentiable ℝ (iteratedFDeriv ℝ n (A f)) :=
          ContDiff.differentiable_iteratedFDeriv (m := n)
            (by exact_mod_cast (ENat.coe_lt_top n)) (hA f)
        have hinner := ((hasFDerivAt_const (𝕜 := ℝ) x (0 : ℝ)).add
          ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const v))
        have hh := (hd _).hasFDerivAt.comp (0 : ℝ) hinner
        have hder : HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ n (A f) (x + t • v))
            (fderiv ℝ (iteratedFDeriv ℝ n (A f)) x v) 0 := by
          convert hh.hasDerivAt using 1 <;> simp [Function.comp_def]
        change Tendsto (fun t : ℝ => t⁻¹ •
          (iteratedFDeriv ℝ n (A f) (x + t • v) - iteratedFDeriv ℝ n (A f) x)) _ _
        simpa only [zero_add, zero_smul, add_zero] using hder.tendsto_slope_zero
      exact (continuousLinearMapOfTendsto D ht).continuous
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => ℂ) ℂ).symm.continuous.comp hc

end

lemma closedDiscSup_lowerSemicontinuous {E : Type*} [TopologicalSpace E]
    (F : E → ℂ → ℝ) (hF : ∀ x : ℂ, Continuous (fun f => F f x))
    (hcont : ∀ f, Continuous (F f)) :
    LowerSemicontinuous (fun f => sSup (F f '' Metric.closedBall (0 : ℂ) 1)) := by
  let B := Metric.closedBall (0 : ℂ) 1
  letI : Nonempty B := ⟨⟨0, Metric.mem_closedBall_self (by norm_num)⟩⟩
  have he : (fun f => sSup (F f '' B)) = fun f => ⨆ x : B, F f x := by
    funext f
    rw [iSup]
    congr 1
    ext r
    simp [Set.mem_range]
  rw [he]
  apply lowerSemicontinuous_ciSup
  · intro f
    have hb := ((isCompact_closedBall (0 : ℂ) 1).image (hcont f)).bddAbove
    exact hb.mono (by rintro r ⟨x, rfl⟩; exact ⟨x, x.property, rfl⟩)
  · intro x
    exact (hF x).lowerSemicontinuous

end DedekindZetaZeroFree.KPCplxPrincipalSeriesEvaluationContinuity
