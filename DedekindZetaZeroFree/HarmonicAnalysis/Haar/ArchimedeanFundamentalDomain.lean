module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AdelicComponents.ArchimedeanSelector

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPActualComponentHaarSources.ProductDisintegration
open KPMsFixedHaar

theorem primitive_arch_group_domain
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (i : Fin A.componentCount)
    (μ : Measure (KPSmoothActualFlowData.GInfinity F)) [μ.IsHaarMeasure] :
    ∃ D : Set (KPSmoothActualFlowData.GInfinity F),
      MeasurableSet D ∧ IsFundamentalDomain (Ga F ζ hζ hF U A i) D μ := by
  obtain ⟨-, -, D, hDm, huniq⟩ :=
    actual_component_arch_group_selector F ζ hζ hF U A i
  refine ⟨D, hDm, IsFundamentalDomain.mk' hDm.nullMeasurableSet fun x => ?_⟩
  obtain ⟨γ, hγ, hu⟩ := huniq x
  refine ⟨γ, ?_, ?_⟩
  · show γ • x ∈ D
    rw [Subgroup.smul_def]; exact hγ
  · intro a ha
    exact hu a (by rw [Subgroup.smul_def] at ha; exact ha)

end DedekindZetaZeroFree.KPActualComponentHaarSources.ProductDisintegration

end
