module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ComplexChartsAndSphericalSections

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.ThetaArchAngularChartSeminorms

open KPCplxPrincipalSeriesCharts Filter Topology

theorem tendsto_submodule_of_chartSeminorm
    {ι : Type*} (s : ℝ) (U : Submodule ℂ (PrincipalSeries s))
    (l : Filter ι) (f : ι → U) (e : U)
    (h : ∀ n : ℕ, Tendsto
      (fun a => chartSeminorm s n ((f a : PrincipalSeries s) - (e : PrincipalSeries s)))
      l (𝓝 (0 : ℝ))) :
    Tendsto f l (𝓝 e) := by
  have hp : WithSeminorms (chartSeminorm s) := ⟨rfl⟩
  rw [tendsto_subtype_rng]
  rw [hp.tendsto_nhds]
  intro n ε hε
  have := h n
  rw [tendsto_order] at this
  exact this.2 ε hε

end DedekindZetaZeroFree.ThetaArchAngularChartSeminorms

end
