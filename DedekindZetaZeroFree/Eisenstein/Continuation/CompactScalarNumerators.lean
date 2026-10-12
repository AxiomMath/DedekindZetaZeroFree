module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarRegularization
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactWordNumerator

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.SharedSource
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator renaming finite_literal_compact_numerator → finite_literal_compact_numerator
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem literal_compact_numerator_exists
    (D : Set (G F ζ hζ)) (hD : IsCompact D)
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
    ∃ (q : ℂ → ℂ) (A N : ℂ → C(D, ℂ)) (r : ℝ),
      AnalyticOnNhd ℂ q KPContinuation.spectralDomain ∧ q 0 = 1 ∧
      MeromorphicOn A KPContinuation.spectralDomain ∧
      (∀ s, (1 / 3 : ℝ) < s.re → ∀ g, A s g = q s * eisenstein F ζ hζ K f s g) ∧
      0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
      AnalyticOnNhd ℂ N (Metric.ball (0 : ℂ) r) ∧
      ∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → N s = s • A s := by
  letI : T2Space (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  letI : LocallyCompactSpace (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.1
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨L⟩ := KPGlobalProductPolarizationCharacter.exists_compatible_local_data F ζ hζ
  obtain ⟨M, _⟩ := KPGlobalTorusFiniteStages.compatibleModelData_exists F ζ hζ L
  obtain ⟨μ, _, _, P, ⟨J⟩⟩ :=
    kp_ms_fixed_haar_disintegration F ζ hζ
      (MeasureTheory.Measure.haar : MeasureTheory.Measure (G F ζ hζ)) inferInstance
  exact finite_literal_compact_numerator F ζ hζ M μ P J D hD K hK f

end DedekindZetaZeroFree.SharedSource

end
