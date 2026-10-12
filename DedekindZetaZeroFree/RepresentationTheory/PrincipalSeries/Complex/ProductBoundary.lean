module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.PU2Boundary

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Topology Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.CurrentComplexBoundary
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPGlobalResidualConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι]
local instance : CompactSpace compactSubgroup :=
  isCompact_iff_compactSpace.mp compactSubgroup_isCompact

local instance : SecondCountableTopology compactSubgroup := by
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
    change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
    infer_instance
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  letI : SecondCountableTopology ComplexGL2 := Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology ComplexPGL2 :=
    inferInstanceAs (SecondCountableTopology (ComplexGL2 ⧸ Subgroup.center _))
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

def productBoundary (μ : Measure (ι → compactSubgroup)) (s : ι → ℝ)
    (f : ∀ i, PrincipalSeries (s i)) (g : ∀ i, PrincipalSeries (-s i)) : ℂ :=
  ∫ k, ∏ i, (KPCplxPrincipalSeriesCharts.pi (s i) (k i).val (f i)) 1 * star ((KPCplxPrincipalSeriesCharts.pi (-s i) (k i).val (g i)) 1) ∂μ

theorem productBoundary_factor
    (μ : Measure (ι → compactSubgroup)) [IsProbabilityMeasure μ] [μ.IsHaarMeasure]
    (ν : ι → Measure compactSubgroup) [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, (ν i).IsHaarMeasure] (s : ι → ℝ)
    (f : ∀ i, PrincipalSeries (s i)) (g : ∀ i, PrincipalSeries (-s i)) :
    productBoundary μ s f g = ∏ i, quotientBoundary (ν i) (s i) (f i) (g i) := by
  have hm : μ = Measure.pi ν := Measure.isHaarMeasure_eq_of_isProbabilityMeasure μ (Measure.pi ν)
  unfold productBoundary quotientBoundary
  rw [hm]
  exact integral_fintype_prod_eq_prod (μ := ν) (fun i (k : compactSubgroup) =>
    (KPCplxPrincipalSeriesCharts.pi (s i) k.val (f i)) 1 * star ((KPCplxPrincipalSeriesCharts.pi (-s i) k.val (g i)) 1))

theorem productBoundary_word_adjoint
    (ρ : Measure ComplexSU2) [IsProbabilityMeasure ρ] [ρ.IsHaarMeasure]
    (μ : Measure (ι → compactSubgroup)) [IsProbabilityMeasure μ] [μ.IsHaarMeasure]
    (ν : ι → Measure compactSubgroup) [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, (ν i).IsHaarMeasure] (s : ι → ℝ)
    (w : ι → List (Matrix (Fin 2) (Fin 2) ℂ))
    (f : ∀ i, PrincipalSeries (s i)) (g : ∀ i, PrincipalSeries (-s i)) :
    productBoundary μ s (fun i => matrixWord (s i) (w i) (f i)) g =
      (-1 : ℂ)^(∑ i, (w i).length) *
        productBoundary μ s f (fun i => matrixWord (-s i) (w i).reverse (g i)) := by
  rw [productBoundary_factor μ ν, productBoundary_factor μ ν]
  simp_rw [quotientBoundary_word_adjoint ρ]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
end DedekindZetaZeroFree.CurrentComplexBoundary

end
