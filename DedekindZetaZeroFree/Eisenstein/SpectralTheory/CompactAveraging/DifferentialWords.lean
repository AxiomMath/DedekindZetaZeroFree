module

public import DedekindZetaZeroFree.Eisenstein.Residues.CompactConvolution.ArchimedeanJets
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.SmoothAutomorphicAveraging
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.ChamberCasimir

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualAverageWord
open KPLiteralRaw KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation
open KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming native_word_chart_jets → native_word_chart_jets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local instance (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

theorem translated_word_continuous
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IsCompact (K : Set (KPLiteralRaw.G F ζ hζ)))
    (μ : Measure K) [IsFiniteMeasure μ] (u : KPLiteralRaw.G F ζ hζ → ℂ)
    (hu : Smooth F ζ hζ u) (w : List (Fin (groupDimension F))) (g : KPLiteralRaw.G F ζ hζ) :
    Continuous (fun k : K => actualRightWord F ζ hζ w (fun a => u (a*k.val)) g) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : IsFiniteMeasureOnCompacts μ := ⟨fun _ _ => measure_lt_top μ _⟩
  obtain ⟨m,c,j,hword⟩ := native_word_chart_jets F ζ hζ w
  let D := archDomain F
  have hD : IsOpen D := KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F
  have hb : archBase F ∈ D := by simp [D, archBase, archDomain]
  have hs (k : K) : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u ((a*archChart F ζ hζ x)*k.val)) D :=
    fun a => ArchRegularity.right_translate_arch_slice_smooth F ζ hζ u hu a k.val
  let J (i : Fin m) (k : K) := iteratedFDeriv ℝ (j i).1
    (fun x => u ((g*archChart F ζ hζ x)*k.val)) (archBase F) (j i).2
  have hc (i : Fin m) : Continuous (J i) := by
    have hj := ArchRegularity.continuous_parameter_arch_spatial_jets
      F ζ hζ u hu g (fun k : K => k.val) continuous_subtype_val (j i).1
    have hh : Continuous (fun k : K => iteratedFDeriv ℝ (j i).1
        (fun x => u ((g*archChart F ζ hζ x)*k.val)) (archBase F)) := by
      rw [← continuousOn_univ]
      exact hj.comp (continuous_const.prodMk continuous_id).continuousOn
        (by intro k hk; exact ⟨hb,hk⟩)
    have hv := hh.eval_const (j i).2
    simpa only [J,iteratedFDerivWithin_of_isOpen _ hD hb] using hv
  have hfun : (fun k : K => actualRightWord F ζ hζ w (fun a => u (a*k.val)) g) =
      fun k => ∑ i, c i * J i k := by
    funext k
    exact hword (fun a => u (a*k.val)) (hs k) g
  rw [hfun]
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hc i))

theorem word_average
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IsCompact (K : Set (KPLiteralRaw.G F ζ hζ)))
    (μ : Measure K) [IsFiniteMeasure μ] (u : KPLiteralRaw.G F ζ hζ → ℂ)
    (hu : Smooth F ζ hζ u) (w : List (Fin (groupDimension F))) (g : KPLiteralRaw.G F ζ hζ) :
    actualRightWord F ζ hζ w (ResidualRawAverage.average F ζ hζ K μ u) g =
      ∫ k : K, actualRightWord F ζ hζ w (fun a => u (a*k.val)) g ∂μ := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : IsFiniteMeasureOnCompacts μ := ⟨fun _ _ => measure_lt_top μ _⟩
  obtain ⟨m,c,j,hword⟩ := native_word_chart_jets F ζ hζ w
  let D := archDomain F
  have hD : IsOpen D := KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F
  have hb : archBase F ∈ D := by simp [D, archBase, archDomain]
  have hav := (ResidualRawAverage.average_smooth F ζ hζ K hK μ u hu).2.1
  rw [hword _ hav]
  have hs (k : K) : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u ((a*archChart F ζ hζ x)*k.val)) D :=
    fun a => ArchRegularity.right_translate_arch_slice_smooth F ζ hζ u hu a k.val
  let J (i : Fin m) (k : K) := iteratedFDeriv ℝ (j i).1
    (fun x => u ((g*archChart F ζ hζ x)*k.val)) (archBase F) (j i).2
  have hc (i : Fin m) : Continuous (J i) := by
    have hj := ArchRegularity.continuous_parameter_arch_spatial_jets
      F ζ hζ u hu g (fun k : K => k.val) continuous_subtype_val (j i).1
    have hh : Continuous (fun k : K => iteratedFDeriv ℝ (j i).1
        (fun x => u ((g*archChart F ζ hζ x)*k.val)) (archBase F)) := by
      rw [← continuousOn_univ]
      exact hj.comp (continuous_const.prodMk continuous_id).continuousOn
        (by intro k hk; exact ⟨hb,hk⟩)
    have hv := hh.eval_const (j i).2
    simpa only [J,iteratedFDerivWithin_of_isOpen _ hD hb] using hv
  have hi (i : Fin m) : Integrable (J i) μ :=
    (hc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (i : Fin m) : iteratedFDeriv ℝ (j i).1
      (fun x => ResidualRawAverage.average F ζ hζ K μ u (g*archChart F ζ hζ x))
      (archBase F) (j i).2 = ∫ k : K, J i k ∂μ := by
    have hh := ResidualConvolutionJets.compact_convolution_arch_jets F ζ hζ K hK μ (1 : C(K,ℂ)) u hu g (j i).1 (archBase F) hb
    simp only [compactConvolution,ContinuousMap.one_apply,one_mul] at hh
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := archDomain F) (j i).1 hD hb] at hh
    simp_rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := archDomain F) (j i).1 hD hb] at hh
    change iteratedFDeriv ℝ (j i).1 (fun x => ∫ k:K,u ((g*archChart F ζ hζ x)*k.val) ∂μ) (archBase F) (j i).2 = _
    rw [hh,ContinuousMultilinearMap.integral_apply]
    · have hj := ArchRegularity.continuous_parameter_arch_spatial_jets F ζ hζ u hu g (fun k:K => k.val) continuous_subtype_val (j i).1
      have ht : Continuous (fun k:K => iteratedFDeriv ℝ (j i).1 (fun x => u ((g*archChart F ζ hζ x)*k.val)) (archBase F)) := by
        rw [← continuousOn_univ]
        exact hj.comp (continuous_const.prodMk continuous_id).continuousOn (by intro k hk; exact ⟨hb,hk⟩)
      simpa only [iteratedFDerivWithin_of_isOpen _ hD hb] using ht.integrable_of_hasCompactSupport (μ:=μ) (HasCompactSupport.of_compactSpace _)
  simp_rw [he]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun i _ => (hi i).const_mul (c i))]
  apply integral_congr_ae
  filter_upwards with k
  exact (hword (fun a => u (a*k.val)) (hs k) g).symm

end DedekindZetaZeroFree.FourierContinuation.ResidualAverageWord

end
