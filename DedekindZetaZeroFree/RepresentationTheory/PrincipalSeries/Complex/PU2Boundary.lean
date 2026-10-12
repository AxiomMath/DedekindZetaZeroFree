module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.BoundaryOperatorWords

@[expose] public section

open _root_.DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts renaming evaluation_point_eval_continuous → evaluation_point_eval_continuous
noncomputable section
open MeasureTheory
open scoped Topology Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.CurrentComplexBoundary
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPGlobalResidualConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def compactQuotient : ComplexSU2 →* compactSubgroup :=
  (Matrix.ProjGenLinGroup.mk.comp complexSU2Embedding).rangeRestrict

theorem compactQuotient_surjective : Function.Surjective compactQuotient := by
  intro k
  obtain ⟨u,hu⟩ := k.property
  exact ⟨u,Subtype.ext hu⟩

theorem compactQuotient_continuous : Continuous compactQuotient := by
  apply Continuous.subtype_mk
  have he : Continuous complexSU2Embedding := by
    apply Units.continuous_iff.mpr
    constructor
    · exact continuous_subtype_val
    · have hi (k : ComplexSU2) :
          (↑(complexSU2Embedding k)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) =
            star (k : Matrix (Fin 2) (Fin 2) ℂ) := by
        rw [← map_inv]
        rfl
      simp_rw [hi]
      exact continuous_subtype_val.star
  exact (show Continuous (Matrix.ProjGenLinGroup.mk : ComplexGL2 → ComplexPGL2) from
    continuous_coinduced_rng).comp he

local instance : CompactSpace compactSubgroup :=
  isCompact_iff_compactSpace.mp compactSubgroup_isCompact

theorem compactQuotient_measurePreserving
    (ν : Measure ComplexSU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (μ : Measure compactSubgroup) [IsProbabilityMeasure μ] [μ.IsHaarMeasure] :
    MeasurePreserving compactQuotient ν μ :=
  MonoidHom.measurePreserving compactQuotient_continuous compactQuotient_surjective (by simp)

def quotientBoundary (μ : Measure compactSubgroup) (s : ℝ)
    (f : PrincipalSeries s) (g : PrincipalSeries (-s)) : ℂ :=
  ∫ k, (KPCplxPrincipalSeriesCharts.pi s k.val f) 1 * star ((KPCplxPrincipalSeriesCharts.pi (-s) k.val g) 1) ∂μ

theorem quotientBoundary_eq (ν : Measure ComplexSU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (μ : Measure compactSubgroup) [IsProbabilityMeasure μ] [μ.IsHaarMeasure]
    (s : ℝ) (f : PrincipalSeries s) (g : PrincipalSeries (-s)) :
    quotientBoundary μ s f g = compactBoundary ν s f g := by
  have hc : Continuous (fun k : compactSubgroup =>
      (KPCplxPrincipalSeriesCharts.pi s k.val f) 1 * star ((KPCplxPrincipalSeriesCharts.pi (-s) k.val g) 1)) := by
    exact ((evaluation_point_eval_continuous s 1).comp
      ((pi_continuous s).comp (continuous_subtype_val.prodMk continuous_const))).mul
      (((evaluation_point_eval_continuous (-s) 1).comp
        ((pi_continuous (-s)).comp (continuous_subtype_val.prodMk continuous_const))).star)
  have hh := integral_map (μ := ν) compactQuotient_continuous.measurable.aemeasurable hc.aestronglyMeasurable
  rw [(compactQuotient_measurePreserving ν μ).map_eq] at hh
  change quotientBoundary μ s f g = ∫ k : ComplexSU2,
    (KPCplxPrincipalSeriesCharts.pi s (Matrix.ProjGenLinGroup.mk (complexSU2Embedding k)) f) 1 *
      star ((KPCplxPrincipalSeriesCharts.pi (-s) (Matrix.ProjGenLinGroup.mk (complexSU2Embedding k)) g) 1) ∂ν at hh
  simpa only [compactBoundary,pi_mk,KPCplxPrincipalSeriesCharts.rightTranslate,one_mul] using hh

theorem quotientBoundary_word_adjoint
    (ν : Measure ComplexSU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]
    (μ : Measure compactSubgroup) [IsProbabilityMeasure μ] [μ.IsHaarMeasure]
    (s : ℝ) (w : List (Matrix (Fin 2) (Fin 2) ℂ))
    (f : PrincipalSeries s) (g : PrincipalSeries (-s)) :
    quotientBoundary μ s (matrixWord s w f) g = (-1 : ℂ)^w.length *
      quotientBoundary μ s f (matrixWord (-s) w.reverse g) := by
  simp only [quotientBoundary_eq ν μ]
  exact compactBoundary_word_adjoint ν s w f g
end DedekindZetaZeroFree.CurrentComplexBoundary

end
