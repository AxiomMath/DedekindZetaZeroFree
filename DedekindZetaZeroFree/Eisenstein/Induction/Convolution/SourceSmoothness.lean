module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.SpatialSmoothingAndCovariantClosure
public import DedekindZetaZeroFree.Eisenstein.Induction.Convolution.NormalizedParameterSpan

@[expose] public section

noncomputable section
open MeasureTheory Filter Set Topology
open scoped NumberField Classical Topology Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.SourceSpatialRegularity
open KPSpatialSmoothing KPSpatialSmoothing.ArchKernel KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming arch_insertion_continuous → arch_insertion_continuous
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming rightConv_integrable → rightConv_integrable
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming rightConv_linear → rightConv_linear
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming rightConv_continuous → rightConv_continuous
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming globalLevel_le_finite → globalLevel_le_finite
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming arch_commutes_finite → arch_commutes_finite
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming actual_kernel_pointwise_approximation → actual_kernel_pointwise_approximation
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing renaming actual_cover_of_torus_cosets → actual_cover_of_torus_cosets
open _root_.DedekindZetaZeroFree.KPSpatialSamplingClosure renaming covariant_smooth_approximation_closed → covariant_smooth_approximation_closed
open _root_.DedekindZetaZeroFree.KPSpatialCovariantOrbit renaming orbit_finiteDimensional → orbit_finiteDimensional
open _root_.DedekindZetaZeroFree.KPSpatialCovariantOrbit renaming orbit_stable → orbit_stable
open _root_.DedekindZetaZeroFree.KPSpatialCovariantOrbit renaming orbit_continuous → orbit_continuous
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming pgl_t2 → pgl_t2
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming pgl_locallyCompact → pgl_locallyCompact
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
private theorem character_right_convolution_calculus
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (χ : actualC F ζ hζ →* ℂ)
    (J0 : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hnormalize : ∀ (k : D.K)
      (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J0),
      k.val⁻¹ * j.val * k.val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J0)
    (μL : Measure (L F)) [μL.IsHaarMeasure]
    (μK : Measure D.K) [μK.IsHaarMeasure] [IsProbabilityMeasure μK]
    (b : ℕ → ContDiffBump (e0 F)) (hb : BumpSequence F μL b) :
  (∀ m (u v : KPLiteralRaw.G F ζ hζ → ℂ) (c : ℂ), Continuous u → Continuous v →
    rightConv F ζ hζ D μL μK (b m) (u + v) =
      rightConv F ζ hζ D μL μK (b m) u + rightConv F ζ hζ D μL μK (b m) v ∧
    rightConv F ζ hζ D μL μK (b m) (c • v) =
      c • rightConv F ζ hζ D μL μK (b m) v) ∧
  (∀ (v : CovariantSampling.V_J (actualC F ζ hζ)
        (KPGlobalTorusFunctionData.globalLevel F ζ hζ J0) χ), Continuous v.val →
    (∀ m g, Integrable (fun a : L F =>
      (kappa F ζ hζ D μL μK (b m) a : ℂ) *
      v.val (g * PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a)) μL) ∧
    (∀ m, Continuous (rightConv F ζ hζ D μL μK (b m) v.val)) ∧
    (∀ m, rightConv F ζ hζ D μL μK (b m) v.val ∈ CovariantSampling.V_J (actualC F ζ hζ)
        (KPGlobalTorusFunctionData.globalLevel F ζ hζ J0) χ) ∧
    (∀ m (k : D.K),
      rightConv F ζ hζ D μL μK (b m)
        ((CovariantSampling.rho_J (actualC F ζ hζ) D.K
          (KPGlobalTorusFunctionData.globalLevel F ζ hζ J0)
          χ hnormalize k v).val) =
        fun g => rightConv F ζ hζ D μL μK (b m) v.val (g * k.val)) ∧
    (∀ m (g : KPLiteralRaw.G F ζ hζ), ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => rightConv F ζ hζ D μL μK (b m) v.val
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)) (D0 F)) ∧
    (∀ g, Tendsto (fun m => rightConv F ζ hζ D μL μK (b m) v.val g)
      atTop (𝓝 (v.val g)))) := by
  obtain ⟨hmap, _, hk, _⟩ :=
    actual_compact_averaged_kernels F ζ hζ D μL μK b hb
  refine ⟨?_, ?_⟩
  · intro m u v c hu hv
    exact rightConv_linear F ζ hζ D μL μK (b m)
      (hk m).1 (hk m).2.2.1 u v c hu hv
  · intro v hv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro m g
      exact rightConv_integrable F ζ hζ D μL μK (b m) v.val hv
        (hk m).1 (hk m).2.2.1 g
    · intro m
      exact rightConv_continuous F ζ hζ D μL μK (b m) v.val hv
        (hk m).1 (hk m).2.2.1
    · intro m
      constructor
      · intro c g
        simp only [rightConv, mul_assoc, v.property.1]
        simp_rw [mul_left_comm (kappa F ζ hζ D μL μK (b m) _ : ℂ) (χ c)]
        exact integral_const_mul _ _
      · intro j g
        unfold rightConv
        apply integral_congr_ae
        filter_upwards with a
        have hm := arch_commutes_finite F ζ hζ a
          ⟨j.val, globalLevel_le_finite F ζ hζ J0 j.property⟩
        rw [mul_assoc, ← hm, ← mul_assoc, v.property.2]
    · intro m k
      funext g
      simp only [rightConv, CovariantSampling.rho_J_apply]
      exact RightConvolution.conjugation_equivariance F ζ hζ μL
        (kappa F ζ hζ D μL μK (b m)) k.val (hmap k)
        (fun a => (hk m).2.2.2.2.2 k a) v.val g
    · intro m g
      let : IsTopologicalGroup (KPLiteralRaw.G F ζ hζ) :=
        (KPCubicCoverConstruction.adelic_topological_covers F ζ hζ).2.2.2.1
      obtain ⟨e, he, _⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
      let p := e.symm g
      have hg : g = PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ p.1 * p.2.val := by
        rw [← he]
        exact (e.apply_symm_apply g).symm
      have hf : Continuous (fun y : L F => v.val
          (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ y * p.2.val)) :=
        hv.comp ((arch_insertion_continuous F ζ hζ).mul continuous_const)
      have hd := RightConvolution.shifted_kernel_contDiffOn F μL
        (kappa F ζ hζ D μL μK (b m)) (hk m).1 (hk m).2.2.1 (hk m).2.1
        (fun y : L F => v.val
          (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ y * p.2.val)) hf p.1
      have hid : (fun z => rightConv F ζ hζ D μL μK (b m) v.val
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)) =
          (fun z => ∫ y : L F,
            (kappa F ζ hζ D μL μK (b m) (p.1⁻¹ * (ell F z)⁻¹ * y) : ℂ) *
            v.val (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ y * p.2.val) ∂μL) := by
        funext z
        rw [hg]
        exact RightConvolution.left_chart_substitution F ζ hζ μL
          (kappa F ζ hζ D μL μK (b m)) v.val p.1 p.2 z
      rw [hid]
      exact hd
    · intro g
      exact actual_kernel_pointwise_approximation F ζ hζ D μL μK b hb v.val hv g

private theorem kfinite_raw_orbit
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (v : KPLiteralRaw.Functions F ζ hζ)
    (hv : KFinite F ζ hζ K v) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range (fun k : K => fun g => v (g * k.val)))) := by
  obtain ⟨S, hS, hvS, hstable⟩ := hv
  have hs : Submodule.span ℂ
      (Set.range (fun k : K => fun g => v (g * k.val))) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact hstable k v hvS
  let : FiniteDimensional ℂ S := hS
  exact FiniteDimensional.of_injective (Submodule.inclusion hs)
    (Submodule.inclusion_injective hs)

private theorem covariant_source_left_smooth
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (χ : actualC F ζ hζ →* ℂ)
    (v : KPLiteralRaw.Functions F ζ hζ)
    (hv : Continuous v)
    (hc : ∀ c : actualC F ζ hζ, ∀ g, v (c.val * g) = χ c * v g)
    (hf : KFinite F ζ hζ D.K v)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hJ : ∀ g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
      v (g * j.val) = v g) :
    ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => v (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  let : IsTopologicalGroup (KPLiteralRaw.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  let : T2Space (KPLiteralRaw.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  let : CompactSpace D.K := isCompact_iff_compactSpace.mp D.compact
  let : LocallyCompactSpace D.K := inferInstance
  let : T2Space PGLComplex.Group := pgl_t2
  let : LocallyCompactSpace PGLComplex.Group := pgl_locallyCompact
  let : LocallyCompactSpace (L F) := by
    change LocallyCompactSpace (NumberField.InfinitePlace F → PGLComplex.Group)
    infer_instance
  let : T2Space (L F) := by
    change T2Space (NumberField.InfinitePlace F → PGLComplex.Group)
    infer_instance
  let μL : Measure (L F) := Measure.haar
  let μK : Measure D.K := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts D.K)
  let : μL.IsHaarMeasure := inferInstance
  let : μK.IsHaarMeasure := inferInstance
  let : IsProbabilityMeasure μK := ⟨Measure.haarMeasure_self⟩
  obtain ⟨J0, n, r, hle, hn, htorus⟩ :=
    actual_normalized_torus_finite_cover F ζ hζ D J
  have hcover := actual_cover_of_torus_cosets F ζ hζ D J0 n r hn htorus
  let C := actualC F ζ hζ
  let JG := KPGlobalTorusFunctionData.globalLevel F ζ hζ J0
  let ρ := CovariantSampling.rho_J C D.K JG χ hn
  let u : CovariantSampling.V_J C JG χ := ⟨v, hc,
    fun j g => hJ g ⟨j.val, hle j.property⟩⟩
  let W := Submodule.span ℂ (Set.range (fun k : D.K => ρ k u))
  let : FiniteDimensional ℂ W := orbit_finiteDimensional C D.K JG χ hn u
    (kfinite_raw_orbit F ζ hζ D.K v hf)
  let τ := ρ.subrepresentation W (orbit_stable C D.K JG χ hn u)
  let incl : τ.IntertwiningMap ρ :=
    W.subtype.intertwiningMap_of_isIntertwiningMap τ ρ (fun _ _ => rfl)
  have hwc (w : W) : Continuous w.val.val := orbit_continuous C D.K JG χ hn u hv w
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, b, hb⟩ :=
    actual_chart_bridge_and_normalized_bumps F ζ hζ μL
  obtain ⟨hlin, hcal⟩ :=
    character_right_convolution_calculus F ζ hζ D χ J0 hn μL μK b hb
  let Lm : ℕ → W →ₗ[ℂ] CovariantSampling.V_J C JG χ := fun m => {
    toFun := fun w => ⟨rightConv F ζ hζ D μL μK (b m) w.val.val,
      (hcal w.val (hwc w)).2.2.1 m⟩
    map_add' := by
      intro w y
      apply Subtype.ext
      exact (hlin m w.val.val y.val.val 1 (hwc w) (hwc y)).1
    map_smul' := by
      intro c w
      apply Subtype.ext
      exact (hlin m w.val.val w.val.val c (hwc w) (hwc w)).2 }
  let tm : ℕ → τ.IntertwiningMap ρ := fun m =>
    (Lm m).intertwiningMap_of_isIntertwiningMap τ ρ (by
      intro k w
      apply Subtype.ext
      exact (hcal w.val (hwc w)).2.2.2.1 m k)
  let w0 : W := ⟨u, by
    have he : ρ 1 u = u := by rw [map_one]; rfl
    rw [← he]
    exact Submodule.subset_span ⟨1, rfl⟩⟩
  have hcov : ∀ g : KPLiteralRaw.G F ζ hζ,
      ∃ (i : Fin n) (c : C) (k : D.K) (j : JG),
        g = c.val * (r i).val * k.val * j.val := by
    intro g
    obtain ⟨i, h, x, k, j, he⟩ := hcover g
    exact ⟨i, ⟨h.val.val * KPGlobalTorusFunctionData.N F ζ hζ x,
      (mem_actualC_iff F ζ hζ _).mpr ⟨h, x, rfl⟩⟩, k, j, he⟩
  exact covariant_smooth_approximation_closed C D.K JG χ n (fun i => (r i).val)
    hcov hn τ (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ)
    (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) incl tm
    (fun m w g => (hcal w.val (hwc w)).2.2.2.2.1 m g) w0
    (fun g => (hcal u hv).2.2.2.2.2 g)

 theorem covariant_source_smooth
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (χ : actualC F ζ hζ →* ℂ)
    (v : KPLiteralRaw.Functions F ζ hζ)
    (hv : Continuous v)
    (hc : ∀ c : actualC F ζ hζ, ∀ g, v (c.val * g) = χ c * v g)
    (hf : KFinite F ζ hζ D.K v)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hJ : ∀ g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
      v (g * j.val) = v g) : Smooth F ζ hζ v := by
  refine ⟨hv, ?_, ⟨J, fun g u hu => hJ g ⟨u, hu⟩⟩⟩
  intro g
  apply contDiffOn_of_locally_contDiffOn
  intro x₀ hx₀
  obtain ⟨O, q, hO, hxO, hq, hqO, heq⟩ :=
    KPLiteralChamber.literal_right_to_left_chart_local_transition
      F ζ hζ g x₀ hx₀
  refine ⟨O, hO, hxO, ?_⟩
  have hb := covariant_source_left_smooth F ζ hζ D χ v hv hc hf J hJ
    (g * KPGlobalResidualConstruction.archChart F ζ hζ x₀)
  have hcomp := hb.comp hq hqO
  apply (hcomp.congr (fun x hx => ?_)).mono Set.inter_subset_right
  rw [heq x hx]
  rfl

open KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ConvolutionSpan.ActualSourceStage
local instance (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : MeasurableSpace K := borel K
local instance (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : BorelSpace K := ⟨rfl⟩
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.NormalizedFiniteSource renaming sourceChi → sourceChi
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.NormalizedFiniteSource renaming source_covariant → source_covariant

end DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.SourceSpatialRegularity

end
