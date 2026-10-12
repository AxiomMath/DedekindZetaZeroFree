module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactAveraging.TaylorJets
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Convolution.ArchimedeanRegularity

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualConvolutionJets
open KPLiteralRaw KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local instance (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩
theorem compact_convolution_arch_jets
    (K : Subgroup (G F ζ hζ)) (hK : IsCompact (K : Set (G F ζ hζ)))
    (μ : Measure K) [IsFiniteMeasure μ] (h : C(K, ℂ))
    (u : Functions F ζ hζ) (hu : Smooth F ζ hζ u) :
    ∀ g n x, x ∈ KPGlobalResidualConstruction.archDomain F →
      iteratedFDerivWithin ℝ n
        (fun x => compactConvolution F ζ hζ K μ h u
          (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
        (KPGlobalResidualConstruction.archDomain F) x =
      ∫ k : K, iteratedFDerivWithin ℝ n
        (fun x => h k * u ((g * KPGlobalResidualConstruction.archChart F ζ hζ x) * k.val))
        (KPGlobalResidualConstruction.archDomain F) x ∂μ := by
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  intro g n x hx
  let D := KPGlobalResidualConstruction.archDomain F
  have hD : IsOpen D := KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F
  let f : KPGlobalResidualConstruction.ArchCoordinates F → K → ℂ :=
    fun x k => h k * u ((g * KPGlobalResidualConstruction.archChart F ζ hζ x) * k.val)
  have hs (k : K) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u ((g * KPGlobalResidualConstruction.archChart F ζ hζ x) * k.val)) D :=
    ArchRegularity.right_translate_arch_slice_smooth F ζ hζ u hu g k.val
  have hf (k : K) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f x k) D :=
    contDiffOn_const.mul (hs k)
  have ht : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) (fun x => ∫ k, f x k ∂μ)
      (fun x m => ∫ k, ftaylorSeriesWithin ℝ (fun x => f x k) D x m ∂μ) D := by
    apply ResidualAverageJets.hasTaylor_average μ D hD f
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
  exact (ht.eq_iteratedFDerivWithin_of_uniqueDiffOn (by simp) hD.uniqueDiffOn hx).symm

end DedekindZetaZeroFree.FourierContinuation.ResidualConvolutionJets

end
