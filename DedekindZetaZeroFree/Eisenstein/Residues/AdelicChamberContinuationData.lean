module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.ScalarRealizationClosure

@[expose] public section

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Classical NumberField ENNReal NNReal Topology InnerProductSpace ComplexOrder
namespace DedekindZetaZeroFree.KPGlobalResidualKernel
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev RawAdeles := KPGlobalTorusFunctionData.Adeles F
abbrev RawAdditiveQuotient := RawAdeles F ⧸ NumberField.AdeleRing.principalSubgroup (𝓞 F) F

end DedekindZetaZeroFree.KPGlobalResidualKernel

end

section

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Classical NumberField ENNReal NNReal Topology InnerProductSpace ComplexOrder
namespace DedekindZetaZeroFree.KPGlobalResidualKernel
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rawRationalBorel : Subgroup (KPRationalAdelicSplitting.RationalPGL2 F) :=
  (KPGlobalTorusFunctionData.borel F ζ hζ).comap
    (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ)
abbrev RawRationalQuotient := Quotient (QuotientGroup.rightRel (rawRationalBorel F ζ hζ))

variable {F ζ hζ}
variable (T : KPMsRationalCompactCrossPairing.ModelData F ζ hζ)
variable (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ T D R P H)

structure RawResidueData (S : Submodule ℂ (KPMsFixedHaarDisintegration.X F ζ hζ → ℂ)) where
  additiveHaar : Measure (RawAdeles F)
  additive_isHaar : additiveHaar.IsAddHaarMeasure
  additiveQuotientHaar : Measure (RawAdditiveQuotient F)
  additive_probability : IsProbabilityMeasure additiveQuotientHaar
  additive_compatible : KPChamberAdditivePeriodization.CompatibleHaar F
    additiveHaar additiveQuotientHaar
  domain : Set ℂ
  domain_open : IsOpen domain
  domain_connected : IsConnected domain
  zero_mem : (0 : ℂ) ∈ domain
  chamber_subset : {s : ℂ | (1 : ℝ) / 3 < s.re} ⊆ domain
  E : ℂ → KPMsRationalCompactCrossPairing.Vplus F ζ hζ D →ₗ[ℂ]
    S
  M : ℂ → KPMsRationalCompactCrossPairing.Vplus F ζ hζ D →ₗ[ℂ] (KPMsRationalCompactCrossPairing.G F ζ hζ → ℂ)
  E_meromorphic : ∀ f x, MeromorphicOn (fun s => (E s f).val x) domain
  M_meromorphic : ∀ f g, MeromorphicOn (fun s => M s f g) domain
  E_summable : ∀ s, (1 : ℝ) / 3 < s.re → ∀ f g,
    KPGlobalEisensteinData.EisensteinSummable
      (fun q : RawRationalQuotient F ζ hζ =>
        KPRationalAdelicSplitting.rationalPGLHom F ζ hζ (Quotient.out q))
      (A.sourceFlat s f).val g
  E_chamber : ∀ s (hs : (1 : ℝ) / 3 < s.re) f g,
    (E s f).val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) =
      KPGlobalEisensteinData.eisenstein
        (fun q : RawRationalQuotient F ζ hζ =>
          KPRationalAdelicSplitting.rationalPGLHom F ζ hζ (Quotient.out q))
        (A.sourceFlat s f).val g (E_summable s hs f g)
  M_integrable : ∀ s, (1 : ℝ) / 3 < s.re → ∀ f g,
    KPGlobalEisensteinData.IntertwinerIntegrable additiveHaar
      (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPCubicCoverConstruction.adelicW F ζ hζ))
      (KPGlobalTorusFunctionData.N F ζ hζ) (A.sourceFlat s f).val g
  M_chamber : ∀ s (hs : (1 : ℝ) / 3 < s.re) f g,
    M s f g = KPGlobalEisensteinData.intertwiner additiveHaar
      (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPCubicCoverConstruction.adelicW F ζ hζ))
      (KPGlobalTorusFunctionData.N F ζ hζ) (A.sourceFlat s f).val g
      (M_integrable s hs f g)
  radius : ℝ
  radius_pos : 0 < radius
  ball_subset : Metric.ball (0 : ℂ) radius ⊆ domain
  clearedE : ℂ → KPMsRationalCompactCrossPairing.Vplus F ζ hζ D →ₗ[ℂ]
    S
  clearedM : ℂ → KPMsRationalCompactCrossPairing.Vplus F ζ hζ D →ₗ[ℂ]
    (KPMsRationalCompactCrossPairing.G F ζ hζ → ℂ)
  clears_E : ∀ s ∈ Metric.ball (0 : ℂ) radius, s ≠ 0 →
    clearedE s = s • E s
  clears_M : ∀ s ∈ Metric.ball (0 : ℂ) radius, s ≠ 0 →
    clearedM s = s • M s
  clearedE_holomorphic : ∀ f x,
    AnalyticOnNhd ℂ (fun s => (clearedE s f).val x) (Metric.ball 0 radius)
  clearedM_holomorphic : ∀ f g,
    AnalyticOnNhd ℂ (fun s => clearedM s f g) (Metric.ball 0 radius)

end DedekindZetaZeroFree.KPGlobalResidualKernel

end
end
