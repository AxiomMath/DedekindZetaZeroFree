module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open scoped Manifold ContDiff

namespace DedekindZetaZeroFree

structure HilbertOneParameterGroups
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : Type*) [Fintype B] where
  operator : B → ℝ → H ≃ₗᵢ[ℂ] H
  operator_zero : ∀ b : B, operator b 0 = 1
  operator_add : ∀ (b : B) (s t : ℝ), operator b (s + t) = operator b s * operator b t
  strongly_continuous : ∀ (b : B) (v : H), Continuous (fun t : ℝ => operator b t v)

section LieData

variable (G : Type*) [Group G] [TopologicalSpace G]
variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [ChartedSpace V G] [LieGroup (𝓘(ℝ, V)) ∞ G]
variable (B : Type*) [Fintype B]

structure HilbertLieExponentialData where
  basis : Module.Basis B ℝ V
  exponential : V → G
  exponential_zero : exponential 0 = 1
  exponential_add_ray : ∀ (X : V) (s t : ℝ),
    exponential ((s + t) • X) = exponential (s • X) * exponential (t • X)
  exponential_smooth : ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, V)) ∞ exponential
  exponentialChart : PartialDiffeomorph (𝓘(ℝ, V)) (𝓘(ℝ, V)) V G ∞
  zero_mem_source : (0 : V) ∈ exponentialChart.toPartialEquiv.source
  chart_eq_exponential : ∀ X ∈ exponentialChart.toPartialEquiv.source,
    exponentialChart X = exponential X
  adjoint : G → V ≃ₗ[ℝ] V
  adjoint_smooth : ∀ a b : B,
    ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, ℝ)) ∞
      (fun g : G => basis.equivFun (adjoint g (basis b)) a)
  exponential_conjugation : ∀ (g : G) (X : V),
    g * exponential X * g⁻¹ = exponential (adjoint g X)

end LieData

section Representation

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [ChartedSpace V G] [LieGroup (𝓘(ℝ, V)) ∞ G]
variable {B : Type*} [Fintype B]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure StronglyContinuousHilbertRepresentation where
  operator : G →* H ≃ₗᵢ[ℂ] H
  strongly_continuous : ∀ v : H, Continuous (fun g : G => operator g v)

variable (D : HilbertLieExponentialData G V B)
variable (π : StronglyContinuousHilbertRepresentation (G := G) (H := H))

noncomputable def hilbertLieOneParameterGroups : HilbertOneParameterGroups H B where
  operator b t := π.operator (D.exponential (t • D.basis b))
  operator_zero b := by simp [D.exponential_zero]
  operator_add b s t := by rw [D.exponential_add_ray, map_mul]
  strongly_continuous b v := by
    exact (π.strongly_continuous v).comp
      (D.exponential_smooth.continuous.comp (continuous_id.smul continuous_const))

end Representation

end DedekindZetaZeroFree
