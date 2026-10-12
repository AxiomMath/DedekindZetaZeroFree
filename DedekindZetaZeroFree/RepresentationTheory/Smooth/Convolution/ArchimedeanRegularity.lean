module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.UpperAndLowerBigCellTransitions
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.ParameterizedArchimedeanJets
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.Convolution.UniformApproximation

@[expose] public section

section

noncomputable section
open scoped NumberField Classical Topology
open NumberField
namespace DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ArchRegularity
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem right_translate_arch_slice_smooth
    (u : Functions F ζ hζ) (hu : Smooth F ζ hζ u)
    (g a : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u ((g * KPGlobalResidualConstruction.archChart F ζ hζ x) * a))
      (KPGlobalResidualConstruction.archDomain F) := by
  have hleft (b : G F ζ hζ) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => u (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * b))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
    apply contDiffOn_of_locally_contDiffOn
    intro z₀ hz₀
    obtain ⟨O, q, hO, hzO, hq, hqO, heq⟩ :=
      KPLiteralChamber.literal_group_chart_local_transition F ζ hζ b z₀ hz₀
    refine ⟨O, hO, hzO, ?_⟩
    have hc := (hu.2.1
      (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z₀ * b)).comp hq hqO
    exact (hc.congr (fun z hz => congrArg u (heq z hz))).mono
      Set.inter_subset_right
  apply contDiffOn_of_locally_contDiffOn
  intro x₀ hx₀
  obtain ⟨O, q, hO, hxO, hq, hqO, heq⟩ :=
    KPLiteralChamber.literal_right_to_left_chart_local_transition F ζ hζ g x₀ hx₀
  refine ⟨O, hO, hxO, ?_⟩
  have hc := (hleft ((g * KPGlobalResidualConstruction.archChart F ζ hζ x₀) * a)).comp
    hq hqO
  apply (hc.congr (fun x hx => ?_)).mono Set.inter_subset_right
  rw [heq x hx, mul_assoc]
  rfl

end DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ArchRegularity

end

end

section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance convolutionArchBorelMeasurable (K : Subgroup (G F ζ hζ)) :
    MeasurableSpace K := borel K
local instance convolutionArchBorelSpace (K : Subgroup (G F ζ hζ)) :
    BorelSpace K := ⟨rfl⟩

theorem compact_convolution_arch_regular
    (K : Subgroup (G F ζ hζ)) (hK : IsCompact (K : Set (G F ζ hζ)))
    (μ : Measure K) [IsFiniteMeasure μ] (h : C(K, ℂ))
    (u : Functions F ζ hζ) (hu : Smooth F ζ hζ u) :
    ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => compactConvolution F ζ hζ K μ h u
        (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
      (KPGlobalResidualConstruction.archDomain F) := by
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  intro g
  let D := KPGlobalResidualConstruction.archDomain F
  have hD : IsOpen D := KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F
  let f : KPGlobalResidualConstruction.ArchCoordinates F → K → ℂ :=
    fun x k => h k * u ((g * KPGlobalResidualConstruction.archChart F ζ hζ x) * k.val)
  have hs (k : K) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u ((g * KPGlobalResidualConstruction.archChart F ζ hζ x) * k.val)) D :=
    ArchRegularity.right_translate_arch_slice_smooth F ζ hζ u hu g k.val
  have hf (k : K) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f x k) D :=
    contDiffOn_const.mul (hs k)
  change ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ∫ k, f x k ∂μ) D
  apply KPSpatialSmoothing.ArchKernel.CompactJets.contDiffOn_average_of_taylor μ D hD f
    (fun x k => ftaylorSeriesWithin ℝ (fun x => f x k) D x)
  · intro k
    exact (hf k).ftaylorSeriesWithin hD.uniqueDiffOn
  · intro n
    have hj := ArchRegularity.continuous_parameter_arch_spatial_jets
      F ζ hζ u hu g (fun k : K => k.val) continuous_subtype_val n
    have hw := (h.continuous.comp continuous_snd).continuousOn.smul hj
    apply hw.congr
    intro p hp
    change iteratedFDerivWithin ℝ n (fun x => f x p.2) D p.1 = _
    rw [iteratedFDerivWithin_of_isOpen n hD hp.1]
    change iteratedFDeriv ℝ n (fun x => f x p.2) p.1 = h p.2 •
      iteratedFDeriv ℝ n
        (fun x => u ((g * KPGlobalResidualConstruction.archChart F ζ hζ x) * p.2.val)) p.1
    simpa only [f, smul_eq_mul] using
      (iteratedFDeriv_const_smul_apply'
        (((hs p.2).contDiffAt (hD.mem_nhds hp.1)).of_le (by simp))
        (a := h p.2))

end DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation

end

end
