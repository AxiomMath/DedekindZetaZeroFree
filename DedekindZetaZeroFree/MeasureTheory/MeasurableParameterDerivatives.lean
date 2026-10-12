module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

namespace DedekindZetaZeroFree.SourceSheet.Differentiation.ParameterDerivatives
noncomputable section
open MeasureTheory Filter
open scoped Topology
variable {X : Type*} [MeasurableSpace X]

lemma measurable_derivative (f : X → ℝ → ℂ)
    (hf : Measurable f.uncurry) (hd : ∀ x t, DifferentiableAt ℝ (f x) t) :
    Measurable (fun p : X × ℝ => deriv (f p.1) p.2) := by
  let q : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hq : Tendsto q atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall ?_⟩
    intro n
    simp [q, Nat.cast_add, Nat.cast_one]
    positivity
  apply measurable_of_tendsto_metrizable
    (f := fun n (p : X × ℝ) => (q n)⁻¹ • (f p.1 (p.2 + q n) - f p.1 p.2))
  · intro n
    exact ((hf.comp (measurable_fst.prodMk (measurable_snd.add measurable_const))).sub hf).const_smul ((q n)⁻¹ : ℝ)
  · apply tendsto_pi_nhds.mpr
    intro p
    exact ((hd p.1 p.2).hasDerivAt.tendsto_slope_zero).comp hq

lemma iterated_two_measurable_of_measurable
    (f : X → ℝ → ℂ) (hm : Measurable f.uncurry)
    (hs : ∀ x, ContDiff ℝ 2 (f x)) (j : ℕ) (hj : j ≤ 2) :
    Measurable (fun p : X × ℝ => iteratedDeriv j (f p.1) p.2) := by
  have h1 : Measurable (fun p : X × ℝ => deriv (f p.1) p.2) :=
    measurable_derivative f hm (fun x t => (hs x).differentiable (by norm_num) t)
  have h2 : Measurable (fun p : X × ℝ => deriv (deriv (f p.1)) p.2) := by
    apply measurable_derivative (fun x t => deriv (f x) t) h1
    intro x t
    simpa only [iteratedDeriv_one] using
      (hs x).differentiable_iteratedDeriv 1 (by norm_num) t
  interval_cases j
  · exact hm
  · simpa only [iteratedDeriv_one] using h1
  · simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using h2

end
end DedekindZetaZeroFree.SourceSheet.Differentiation.ParameterDerivatives
