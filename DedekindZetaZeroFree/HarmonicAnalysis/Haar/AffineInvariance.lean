module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalFields.ValuationShellMeasure

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair.CompactBorel
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalPrincipalSeries
variable (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))

theorem integral_affine (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (a : (LocalField F q)ˣ) (ha : localAbs (LocalField F q) a = 1)
    (t : LocalField F q) (f : LocalField F q → ℂ) :
    (∫ x, f ((a : LocalField F q) * x + t) ∂μ) = ∫ x, f x ∂μ := by
  have hm : Measure.map (fun x : LocalField F q => (a : LocalField F q) * x) μ = μ := by
    have HH := NonarchimedeanHaarScaling.map_mul (LocalField F q) μ (a : LocalField F q) a.ne_zero
    rw [← actualAbs_units F q a, ha] at HH
    simpa using HH
  have he : MeasurableEmbedding (fun x : LocalField F q => (a : LocalField F q) * x) :=
    (Homeomorph.mulLeft₀ (a : LocalField F q) a.ne_zero).isClosedEmbedding.measurableEmbedding
  have HH := he.integral_map (μ := μ) (fun x => f (x + t))
  rw [hm] at HH
  exact HH.symm.trans (integral_add_right_eq_self f t)

end DedekindZetaZeroFree.KPRankOneShellRepair.CompactBorel

end
