module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Convolution.CompactAveragedKernels
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactAverages.ConjugationAndSupport
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ArchimedeanCompactAverageIntegrability

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel
open MeasureTheory Filter Set Topology
open scoped NumberField Classical Topology Matrix.Norms.Elementwise

open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming pgl_locallyCompact → pgl_locallyCompact
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming pgl_secondCountable → pgl_secondCountable

private theorem integrable_compact_weight
    {A : Type*} [TopologicalSpace A] [MeasurableSpace A] [OpensMeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasureOnCompacts μ]
    (k : A → ℝ) (f : A → ℂ) (hk : Continuous k)
    (hs : HasCompactSupport k) (hf : Continuous f) :
    Integrable (fun a => (k a : ℂ) * f a) μ := by
  have hc : Continuous (fun a => (k a : ℂ) * f a) :=
    (Complex.continuous_ofReal.comp hk).mul hf
  have hcs : HasCompactSupport (fun a => (k a : ℂ)) :=
    hs.comp_left Complex.ofReal_zero
  have hprod : HasCompactSupport (fun a => (k a : ℂ) * f a) :=
    HasCompactSupport.mul_right (f := fun a => (k a : ℂ)) (f' := f) hcs
  exact hc.integrable_of_hasCompactSupport hprod

private theorem compact_weight_error_le
    {A : Type*} [TopologicalSpace A] [MeasurableSpace A] [OpensMeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasureOnCompacts μ]
    (k : A → ℝ) (f : A → ℂ) (hk : Continuous k)
    (hs : HasCompactSupport k) (hf : Continuous f)
    (hn : ∀ a, 0 ≤ k a) (hm : (∫ a, k a ∂μ) = 1)
    (c : ℂ) (ε : ℝ) (_hε : 0 ≤ ε)
    (hbound : ∀ a ∈ tsupport k, ‖f a - c‖ ≤ ε) :
    ‖(∫ a, (k a : ℂ) * f a ∂μ) - c‖ ≤ ε := by
  have hki := hk.integrable_of_hasCompactSupport hs (μ := μ)
  have hfi := integrable_compact_weight μ k f hk hs hf
  have hci := integrable_compact_weight μ k (fun _ => c) hk hs continuous_const
  have hmass : (∫ a, (k a : ℂ) * c ∂μ) = c := by
    rw [integral_mul_const, integral_complex_ofReal, hm]
    simp
  rw [← hmass, ← integral_sub hfi hci]
  have hb : ∀ a, ‖(k a : ℂ) * f a - (k a : ℂ) * c‖ ≤ k a * ε := by
    intro a
    by_cases ha : a ∈ tsupport k
    · rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hn a)]
      exact mul_le_mul_of_nonneg_left (hbound a ha) (hn a)
    · rw [image_eq_zero_of_notMem_tsupport ha]
      simp
  apply (norm_integral_le_of_norm_le (hki.mul_const ε) (Eventually.of_forall hb)).trans_eq
  rw [integral_mul_const, hm, one_mul]

private theorem compact_weights_tendsto
    {A : Type*} [TopologicalSpace A] [MeasurableSpace A] [OpensMeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasureOnCompacts μ]
    (k : ℕ → A → ℝ) (f : A → ℂ) (x : A)
    (hk : ∀ m, Continuous (k m)) (hs : ∀ m, HasCompactSupport (k m))
    (hn : ∀ m a, 0 ≤ k m a) (hm : ∀ m, (∫ a, k m a ∂μ) = 1)
    (hshrink : ∀ O ∈ 𝓝 x, ∀ᶠ m in atTop, tsupport (k m) ⊆ O)
    (hf : Continuous f) :
    Tendsto (fun m => ∫ a, (k m a : ℂ) * f a ∂μ) atTop (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ho : {a | ‖f a - f x‖ < ε / 2} ∈ 𝓝 x := by
    have h := (hf.continuousAt.tendsto : Tendsto f (𝓝 x) (𝓝 (f x)))
    have hpre : f ⁻¹' Metric.ball (f x) (ε / 2) ∈ 𝓝 x :=
      h (Metric.ball_mem_nhds (f x) (half_pos hε))
    simpa only [Metric.ball, dist_eq_norm, Set.preimage_ofPred_eq] using hpre
  filter_upwards [hshrink _ ho] with m hsub
  rw [dist_eq_norm]
  exact lt_of_le_of_lt
    (compact_weight_error_le μ (k m) f (hk m) (hs m) hf (hn m) (hm m)
      (f x) (ε / 2) (half_pos hε).le (fun a ha => (hsub ha).le))
    (half_lt_self hε)

theorem actual_kernel_pointwise_approximation
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (μL : Measure (L F)) [μL.IsHaarMeasure]
    (μK : Measure D.K) [μK.IsHaarMeasure] [IsProbabilityMeasure μK]
    (b : ℕ → ContDiffBump (e0 F)) (hb : BumpSequence F μL b)
    (v : G F ζ hζ → ℂ) (hv : Continuous v) (g : G F ζ hζ) :
    Tendsto (fun m => ∫ a : L F, (kappa F ζ hζ D μL μK (b m) a : ℂ) *
      v (g * PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a) ∂μL)
      atTop (𝓝 (v g)) := by
  let : IsTopologicalGroup (G F ζ hζ) :=
    (KPCubicCoverConstruction.adelic_topological_covers F ζ hζ).2.2.2.1
  let : CompactSpace D.K := isCompact_iff_compactSpace.mp D.compact
  let : T2Space (G F ζ hζ) := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  let : LocallyCompactSpace (L F) :=
    @Pi.locallyCompactSpace_of_finite (NumberField.InfinitePlace F)
      (fun _ => PGLComplex.Group) (fun _ => PGLComplex.instTopologicalSpaceGroup)
      (fun _ => pgl_locallyCompact) inferInstance
  let : SecondCountableTopology (L F) :=
    @TopologicalSpace.instSecondCountableTopologyForallOfCountable
      (NumberField.InfinitePlace F) (fun _ => PGLComplex.Group) inferInstance
      (fun _ => PGLComplex.instTopologicalSpaceGroup) (fun _ => pgl_secondCountable)
  let π := (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ).comp D.K.subtype
  have hπ : Continuous π :=
    (RepresentationTheory.ArchFiniteSplitting.splitting_maps_continuous F ζ hζ).2.comp
      continuous_subtype_val
  have hc m : Continuous (kappa F ζ hζ D μL μK (b m)) :=
    AverageBasic.continuous_average π hπ μK _ (hb.2.2.2.1 m).1
  have hs m : HasCompactSupport (kappa F ζ hζ D μL μK (b m)) :=
    AverageBasic.compact_support_average π hπ μK _ (hb.2.2.2.1 m).2.2.1
  have hn m : ∀ a, 0 ≤ kappa F ζ hζ D μL μK (b m) a :=
    AverageBasic.average_nonneg π μK _ (hb.2.2.2.1 m).2.2.2.1
  have hm m : (∫ a, kappa F ζ hζ D μL μK (b m) a ∂μL) = 1 := by
    rw [show kappa F ζ hζ D μL μK (b m) =
      AverageBasic.average π μK (eta F μL (b m)) from rfl,
      AverageBasic.integral_average π hπ μL μK _ (hb.2.2.2.1 m).1
        (hb.2.2.2.1 m).2.2.1]
    exact (hb.2.2.2.1 m).2.2.2.2
  have hshrink : ∀ O ∈ 𝓝 (1 : L F), ∀ᶠ m in atTop,
      tsupport (kappa F ζ hζ D μL μK (b m)) ⊆ O :=
    AverageBasic.average_support_shrinks π hπ μK _
      (fun m => (hb.2.2.2.1 m).2.2.1) hb.2.2.2.2
  have hi : Continuous (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ) :=
    (RepresentationTheory.ArchFiniteSplitting.splitting_maps_continuous F ζ hζ).1
  have ho : PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (1 : L F) = 1 := by
    obtain ⟨s, hs⟩ := RepresentationTheory.ArchFiniteSplitting.insertion_hom F ζ hζ
    have he : s (1 : L F) = PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ 1 := hs 1
    rw [← he, map_one]
  simpa only [ho, mul_one] using compact_weights_tendsto μL
    (fun m => kappa F ζ hζ D μL μK (b m))
    (fun a => v (g * PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a))
    (1 : L F) hc hs hn hm hshrink (hv.comp (continuous_const.mul hi))

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel

end
