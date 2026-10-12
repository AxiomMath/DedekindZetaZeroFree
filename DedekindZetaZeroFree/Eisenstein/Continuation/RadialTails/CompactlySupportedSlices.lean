module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspForms.RadialComparison

@[expose] public section

noncomputable section
open scoped Classical NumberField
open Topology

namespace DedekindZetaZeroFree.KPRadialTail

open KPContActualCuspRadialFormComparison
open KPContActualSectorSmoothTestModules KPContSectorSmoothFramesSupport

theorem radial_tail_slice_regular
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (c : Cusp F ζ hζ U R P H) (f : S_U F ζ hζ U R P H)
    (p : KPCuspCharts.Cross F) (T : ℝ)
    (hT : ((H.atlas U).cuspAtlas c.1).threshold < T)
    (hEmb : Topology.IsEmbedding (endChart F ζ hζ U R P H c T))
    (hRange : Set.range (endChart F ζ hζ U R P H c T) = endSet F ζ hζ U R P H c T)
    (hsupp : scalarSupport f.val ⊆ endSet F ζ hζ U R P H c T) :
    ContDiff ℝ (⊤ : ℕ∞)
        (fun t : ℝ => if T < t then (coefficient F ζ hζ U R P H f c p t : ℂ) else 0) ∧
      HasCompactSupport
        (fun t : ℝ => if T < t then (coefficient F ζ hζ U R P H f c p t : ℂ) else 0) := by

  have tests := kp_cont_actual_sector_smooth_test_modules F ζ hζ
    R.adelicHaar R.adelic_isHaar U R rfl P H realization
  have hSupport : scalarSupport f.val =
      tsupport (sectionNorm F ζ hζ U R P H (scalarSections f)) :=
    tests.scalar_support f
  have hCompact : IsCompact
      (tsupport (sectionNorm F ζ hζ U R P H (scalarSections f))) := by
    rw [← hSupport]
    exact f.property.2.2
  have hContained :
      tsupport (sectionNorm F ζ hζ U R P H (scalarSections f)) ⊆
        Set.range (endChart F ζ hζ U R P H c T) := by
    rw [← hSupport, hRange]
    exact hsupp
  obtain ⟨a, b, ha, hab⟩ := compact_embedding_height_bounds T
    (endChart F ζ hζ U R P H c T) hEmb
    (tsupport (sectionNorm F ζ hζ U R P H (scalarSections f))) hCompact hContained

  have hpoint : ∀ (t : ℝ) (ht : T < t),
      endChart F ζ hζ U R P H c T (Quotient.mk _ p, (⟨t, ht⟩ : Set.Ioi T)) =
        (H.atlas U).components ⟨c.1,
          Quotient.mk _ (cuspPoint F ζ hζ U R P H c.1 c.2 (p, t))⟩ := by
    intro t ht
    unfold endChart
    rw [(((H.atlas U).cuspAtlas c.1).geometry c.2).highPresentation_formula]
    rw [(H.atlas U).components_formula]
    rfl

  have hbridge : ∀ (t : ℝ) (ht : T < t),
      (coefficient F ζ hζ U R P H f c p t : ℂ) ≠ 0 → a ≤ t ∧ t ≤ b := by
    intro t ht hne
    have hmem : endChart F ζ hζ U R P H c T (Quotient.mk _ p, (⟨t, ht⟩ : Set.Ioi T)) ∈
        tsupport (sectionNorm F ζ hζ U R P H (scalarSections f)) := by
      apply subset_tsupport
      change sectionNorm F ζ hζ U R P H (scalarSections f)
        (endChart F ζ hζ U R P H c T (Quotient.mk _ p, (⟨t, ht⟩ : Set.Ioi T))) ≠ 0
      rw [hpoint t ht, sectionNorm_component]
      exact norm_ne_zero_iff.mpr hne
    have hz := hab _ hmem
    simpa using hz

  have hraw : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => (coefficient F ζ hζ U R P H f c p t : ℂ)) := by
    have hsm := cuspCoefficient_smooth F ζ hζ U R P H (scalarSections f)
      (tests.scalar_smooth f) c.1 c.2
    have hcomp : ContDiff ℝ (⊤ : ℕ∞)
        (fun t : ℝ =>
          (cuspCoefficient F ζ hζ U R P H (scalarSections f) c.1 c.2 (p, t) : ℂ)) :=
      hsm.comp (contDiff_const.prodMk contDiff_id)
    exact hcomp

  have hzero : ∀ t : ℝ, t < a →
      (if T < t then (coefficient F ζ hζ U R P H f c p t : ℂ) else 0) = 0 := by
    intro t hta
    by_cases hTt : T < t
    · rw [if_pos hTt]
      by_contra hne
      exact absurd (hbridge t hTt hne).1 (not_le.mpr hta)
    · rw [if_neg hTt]
  refine ⟨?_, ?_⟩
  · rw [← contDiffOn_univ]
    refine contDiffOn_of_locally_contDiffOn (fun x _ => ?_)
    rcases lt_or_ge x a with hx | hx
    · refine ⟨Set.Iio a, isOpen_Iio, hx, ?_⟩
      have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun t : ℝ => if T < t then (coefficient F ζ hζ U R P H f c p t : ℂ) else 0)
          (Set.Iio a) :=
        (contDiffOn_const (c := (0 : ℂ)) (s := Set.Iio a)).congr
          (fun t ht => hzero t ht)
      simpa using h1
    · refine ⟨Set.Ioi T, isOpen_Ioi, lt_of_lt_of_le ha hx, ?_⟩
      have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun t : ℝ => if T < t then (coefficient F ζ hζ U R P H f c p t : ℂ) else 0)
          (Set.Ioi T) :=
        (hraw.contDiffOn (s := Set.Ioi T)).congr (fun t ht => by
          rw [if_pos (show T < t from ht)])
      simpa using h2
  · refine HasCompactSupport.intro' (K := Set.Icc a b) isCompact_Icc isClosed_Icc
      (fun t ht => ?_)
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · exact hzero t h
    · by_cases hTt : T < t
      · rw [if_pos hTt]
        by_contra hne
        exact absurd (hbridge t hTt hne).2 (not_le.mpr h)
      · rw [if_neg hTt]

end DedekindZetaZeroFree.KPRadialTail

end
