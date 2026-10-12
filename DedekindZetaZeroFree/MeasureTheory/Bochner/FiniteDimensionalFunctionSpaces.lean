module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import DedekindZetaZeroFree.Algebra.LinearAlgebra.FunctionInterpolation

public section

noncomputable section

open scoped Classical Topology

namespace DedekindZetaZeroFree.FiniteFunctionSpaces

open MeasureTheory Filter

private theorem integral_mem_finite_function_space
    {X Y : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ T]
    (f : X → Y → ℂ) (hf : ∀ᵐ x ∂μ, f x ∈ T)
    (hi : ∀ y, Integrable (fun x => f x y) μ) :
    (fun y => ∫ x, f x y ∂μ) ∈ T := by
  obtain ⟨n, p, b, hb⟩ := exists_finite_evaluation_interpolation T
  have he (y : Y) :
      (fun x => f x y) =ᵐ[μ] (fun x => ∑ i, f x (p i) * (b i).val y) := by
    filter_upwards [hf] with x hx
    exact hb ⟨f x, hx⟩ y
  have hrepr : (fun y => ∫ x, f x y ∂μ) =
      ∑ i, (∫ x, f x (p i) ∂μ) • (b i).val := by
    funext y
    rw [integral_congr_ae (he y), integral_finsetSum]
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_mul_const _ _
    · intro i _
      exact (hi (p i)).mul_const _
  rw [hrepr]
  exact T.sum_mem (fun i _ => T.smul_mem _ (b i).property)

theorem integral_mem_finite_linear_image
    {X Y V : Type*} [MeasurableSpace X] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (μ : Measure X) (J : V →ₗ[ℂ] (Y → ℂ))
    (f : X → Y → ℂ) (hf : ∀ᵐ x ∂μ, f x ∈ J.range)
    (hi : ∀ y, Integrable (fun x => f x y) μ) :
    (fun y => ∫ x, f x y ∂μ) ∈ J.range := by
  let : FiniteDimensional ℂ J.range := Module.Finite.range J
  exact integral_mem_finite_function_space μ J.range f hf hi

end DedekindZetaZeroFree.FiniteFunctionSpaces
