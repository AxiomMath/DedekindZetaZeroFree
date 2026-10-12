module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree.KPCubeAverageError

open MeasureTheory

theorem integral_finite_ae_partition {α I : Type*} [MeasurableSpace α] [Fintype I]
    (μ : Measure α) (Q : Set α) (C : I → Set α)
    (hC : ∀ i, MeasurableSet (C i)) (hsub : ∀ i, C i ⊆ Q)
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : ∀ᵐ x ∂μ, x ∈ Q ↔ x ∈ ⋃ i, C i)
    (g : α → ℝ) (hg : Integrable g (μ.restrict Q)) :
    ∑ i, ∫ x in C i, g x ∂μ = ∫ x in Q, g x ∂μ := by
  classical
  have hUC : (⋃ i, C i) =ᵐ[μ] Q := by
    filter_upwards [hcover] with x hx using propext hx.symm
  have hunion := integral_iUnion_fintype (μ := μ) (s := C) (f := g) hC hdisj
    (fun i => IntegrableOn.mono_set (f := g) hg (hsub i))
  rw [← hunion, setIntegral_congr_set hUC]

end DedekindZetaZeroFree.KPCubeAverageError
