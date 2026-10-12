module

public import DedekindZetaZeroFree.Metaplectic.Torus.PolarizationSubgroupCharacters
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactConjugationInvariance
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactAverages.AveragedKernels
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactAverages.TaylorJets

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel

open MeasureTheory Filter Set Topology
open scoped NumberField Classical Topology Matrix.Norms.Elementwise

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open _root_.DedekindZetaZeroFree.RepresentationTheory.ArchFiniteSplitting renaming projective_t2 → projective_t2
local instance : T2Space (Matrix.ProjGenLinGroup (Fin 2) ℂ) := projective_t2

local instance : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) := by
  change LocallyCompactSpace (Fin 2 → Fin 2 → ℂ)
  infer_instance

local instance : LocallyCompactSpace (Matrix.ProjGenLinGroup (Fin 2) ℂ) := by
  change LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸ Subgroup.center _)
  infer_instance
local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
  change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
  infer_instance
local instance : SecondCountableTopology ((Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ) :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology
local instance : SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) ℂ) :=
  Units.isEmbedding_embedProduct.secondCountableTopology
local instance : SecondCountableTopology (Matrix.ProjGenLinGroup (Fin 2) ℂ) := by
  change SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸ Subgroup.center _)
  infer_instance
local instance : LocallyCompactSpace (L F) :=
  @Pi.locallyCompactSpace_of_finite (NumberField.InfinitePlace F)
    (fun _ => Matrix.ProjGenLinGroup (Fin 2) ℂ) (fun _ => inferInstance)
    (fun _ => inferInstance) inferInstance
local instance : T2Space (L F) :=
  @Pi.t2Space (NumberField.InfinitePlace F)
    (fun _ => Matrix.ProjGenLinGroup (Fin 2) ℂ) (fun _ => inferInstance)
    (fun _ => inferInstance)
local instance : SecondCountableTopology (L F) :=
  @TopologicalSpace.instSecondCountableTopologyForallOfCountable (NumberField.InfinitePlace F)
    (fun _ => Matrix.ProjGenLinGroup (Fin 2) ℂ) inferInstance
    (fun _ => inferInstance) (fun _ => inferInstance)

open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming averaged_kernel_smooth → averaged_kernel_smooth

open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming averaged_support_subset → averaged_support_subset
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming averaged_hasCompactSupport → averaged_hasCompactSupport
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming averaged_continuous → averaged_continuous
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming conjugation_saturation_shrinks → conjugation_saturation_shrinks
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming averaged_integrable_parameter → averaged_integrable_parameter
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming averaged_conjugation_invariant → averaged_conjugation_invariant
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming averaged_mass → averaged_mass

def kappa (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (μL : Measure (L F)) (μK : Measure D.K)
    (b : ContDiffBump (e0 F)) (a : L F) : ℝ :=
  ∫ k : D.K, eta F μL b
    ((PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k.val)⁻¹ * a *
      PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k.val) ∂μK

theorem actual_compact_averaged_kernels
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (μL : Measure (L F)) [μL.IsHaarMeasure]
    (μK : Measure D.K) [μK.IsHaarMeasure] [IsProbabilityMeasure μK]
    (b : ℕ → ContDiffBump (e0 F)) (hb : BumpSequence F μL b) :
  (∀ k : D.K, Measure.map
    (fun a : L F =>
      (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k.val)⁻¹ * a *
        PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k.val) μL = μL) ∧
  (∀ m a, Integrable (fun k : D.K => eta F μL (b m)
    ((PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k.val)⁻¹ * a *
      PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k.val)) μK) ∧
  (∀ m, Continuous (kappa F ζ hζ D μL μK (b m)) ∧
    KernelSmooth F (kappa F ζ hζ D μL μK (b m)) ∧
    HasCompactSupport (kappa F ζ hζ D μL μK (b m)) ∧
    (∀ a, 0 ≤ kappa F ζ hζ D μL μK (b m) a) ∧
    (∫ a, kappa F ζ hζ D μL μK (b m) a ∂μL) = 1 ∧
    (∀ (k : D.K) (a : L F), kappa F ζ hζ D μL μK (b m)
      ((PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k.val)⁻¹ * a *
        PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k.val) =
      kappa F ζ hζ D μL μK (b m) a)) ∧
  (∀ O ∈ 𝓝 (1 : L F), ∀ᶠ m in atTop,
    tsupport (kappa F ζ hζ D μL μK (b m)) ⊆ O) := by
  letI : CompactSpace D.K := isCompact_iff_compactSpace.mp D.compact
  letI : T2Space (G F ζ hζ) := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  let π : D.K →* L F :=
    (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ).comp D.K.subtype
  have hπ : Continuous π :=
    (RepresentationTheory.ArchFiniteSplitting.splitting_maps_continuous F ζ hζ).2.comp continuous_subtype_val
  have hmap : ∀ k : D.K, Measure.map (fun a : L F => (π k)⁻¹ * a * π k) μL = μL :=
    CompactHaar.map_conjugation_compact π hπ μL
  refine ⟨hmap, ?_, ?_, ?_⟩
  · intro m a
    exact averaged_integrable_parameter π hπ μK (hb.2.2.2.1 m).1 a
  · intro m
    obtain ⟨hc, hd, hs, hn, hi⟩ := hb.2.2.2.1 m
    refine ⟨averaged_continuous π hπ μK hc, ?_,
      averaged_hasCompactSupport π hπ μK hs, ?_, ?_, ?_⟩
    · exact averaged_kernel_smooth F μK π hπ (eta F μL (b m)) hd
    · intro a
      exact integral_nonneg (fun k => hn _)
    · change (∫ a, (∫ k, eta F μL (b m) ((π k)⁻¹ * a * π k) ∂μK) ∂μL) = 1
      rw [averaged_mass π hπ μL μK hmap hc hs, hi]
    · intro k a
      exact averaged_conjugation_invariant π μK (eta F μL (b m)) k a
  · intro O hO
    obtain ⟨U, hU, hsat⟩ := conjugation_saturation_shrinks π hπ hO
    filter_upwards [hb.2.2.2.2 U hU] with m hm
    intro a ha
    obtain ⟨⟨k, x⟩, hx, rfl⟩ :=
      averaged_support_subset π hπ μK (hb.2.2.2.1 m).2.2.1 ha
    exact hsat k x (hm hx.2)

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel

end
