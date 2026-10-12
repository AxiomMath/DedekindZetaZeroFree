module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.LaplacianSmoothnessAndSupport
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.HolomorphicL2SectorClasses

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree

open KPContSectorSmoothFramesSupport KPContSectorFixedPushforwardSupport
open KPContActualSectorSmoothTestModules KPContActualCompactSectionL2Jets

theorem kp_cont_actual_compact_section_l2_jets
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (_realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (O : Set ℂ) (hO : IsOpen O)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsCompact K)
    (w : ℂ → Sections F ζ hζ U R P H)
    (smooth : ∀ s ∈ O, IsSmoothSections F ζ hζ U R P H (w s))
    (support : ∀ s ∈ O, tsupport (sectionNorm F ζ hζ U R P H (w s)) ⊆ K)
    (m : ℕ) (charts : Fin m → ActualChart (U := U) (H := H))
    (cover : K ⊆ ⋃ i, (charts i).baseDomain)
    (holomorphic : ∀ i, ChartHolomorphicOn (charts i) w O) :
    Conclusions w O K ∧
      ∀ v : ℂ → Sections F ζ hζ U R P H,
        IsLocalLaplacianFamily w v O →
        (∀ i, ChartHolomorphicOn (charts i) v O) → Conclusions v O K := by
  obtain ⟨wk, hwk0, hsupp, hderiv, hframe⟩ :=
    parameter_jets_sections_source O hO K hK w smooth support m charts cover holomorphic
  obtain ⟨W, hrep, hdiff, hiter, hbound, hlift⟩ :=
    parameter_jets_sector_classes_source O hO K hK w wk hwk0 hsupp hderiv m charts cover holomorphic
  refine ⟨⟨wk, W, hwk0, hsupp, hderiv, ?_, hdiff, hiter, hbound, hframe, hlift⟩, ?_⟩
  · intro k s hs
    exact ⟨(hrep k s hs).1, fun V hV => (hrep k s hs).2 V hV⟩
  · intro v hv hhol
    have hvss := local_laplacian_smooth_support_source O K w v smooth support hv
    obtain ⟨wk', hwk0', hsupp', hderiv', hframe'⟩ :=
      parameter_jets_sections_source O hO K hK v (fun s hs => (hvss s hs).1)
        (fun s hs => (hvss s hs).2) m charts cover hhol
    obtain ⟨W', hrep', hdiff', hiter', hbound', hlift'⟩ :=
      parameter_jets_sector_classes_source O hO K hK v wk' hwk0' hsupp' hderiv' m charts cover hhol
    exact ⟨wk', W', hwk0', hsupp', hderiv',
      fun k s hs => ⟨(hrep' k s hs).1, fun V hV => (hrep' k s hs).2 V hV⟩,
      hdiff', hiter', hbound', hframe', hlift'⟩

end DedekindZetaZeroFree

end
