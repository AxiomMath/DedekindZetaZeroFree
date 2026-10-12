module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactWordNumerator

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator renaming finite_literal_compact_numerator → finite_literal_compact_numerator

theorem native_compact_numerator
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (D : Set (G F ζ hζ)) (hD : IsCompact D)
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
    ∃ (Q : ℂ → ℂ) (S T : ℂ → C(D, ℂ)) (r : ℝ),
      AnalyticOnNhd ℂ Q KPContinuation.spectralDomain ∧ Q 0 = 1 ∧
      MeromorphicOn S KPContinuation.spectralDomain ∧
      (∀ s, (1 : ℝ) / 3 < s.re → ∀ g, S s g = Q s * eisenstein F ζ hζ K f s g) ∧
      0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
      AnalyticOnNhd ℂ T (Metric.ball (0 : ℂ) r) ∧
      ∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → T s = s • S s := by
  exact finite_literal_compact_numerator F ζ hζ C R P H D hD K hK f

theorem native_compact_source_exists
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (D : Set (G F ζ hζ)) (hD : IsCompact D)
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
    ∃ (Q : ℂ → ℂ) (S : ℂ → C(D, ℂ)),
      AnalyticOnNhd ℂ Q KPContinuation.spectralDomain ∧ Q 0 = 1 ∧
      MeromorphicOn S KPContinuation.spectralDomain ∧
      (∀ s, (1 : ℝ) / 3 < s.re → ∀ g, S s g = Q s * eisenstein F ζ hζ K f s g) := by
  letI : T2Space (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  letI : LocallyCompactSpace (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.1
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨L⟩ := KPGlobalProductPolarizationCharacter.exists_compatible_local_data F ζ hζ
  obtain ⟨C, _⟩ := KPGlobalTorusFiniteStages.compatibleModelData_exists F ζ hζ L
  obtain ⟨R, _, _, P, ⟨H⟩⟩ :=
    kp_ms_fixed_haar_disintegration F ζ hζ (MeasureTheory.Measure.haar : MeasureTheory.Measure (G F ζ hζ)) inferInstance
  obtain ⟨Q, S, T, r, hQ, hQ0, hS, hch, _⟩ :=
    native_compact_numerator F ζ hζ C R P H D hD K hK f
  exact ⟨Q, S, hQ, hQ0, hS, hch⟩

end DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation

end
