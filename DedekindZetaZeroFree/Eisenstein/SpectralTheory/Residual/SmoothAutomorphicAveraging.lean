module

public import DedekindZetaZeroFree.Adeles.Approximation.UniformConjugatedFiniteLevel
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Convolution.ArchimedeanRegularity

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualRawAverage
open KPLiteralRaw KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local instance : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
local instance (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

def average (K : Subgroup (G F ζ hζ)) (μ : Measure K) (f : G F ζ hζ → ℂ) : G F ζ hζ → ℂ :=
  fun g => ∫ k : K, f (g*k.val) ∂μ

theorem average_continuous (K : Subgroup (G F ζ hζ))
    (hK : IsCompact (K : Set (G F ζ hζ))) (μ : Measure K) [IsFiniteMeasure μ]
    (f : G F ζ hζ → ℂ) (hf : Continuous f) : Continuous (average F ζ hζ K μ f) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun p : G F ζ hζ × K => f (p.1*p.2.val)) :=
    hf.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))
  rw [← continuousOn_univ]
  exact continuousOn_integral_of_compact_support (μ := μ) isCompact_univ
    hc.continuousOn (fun _ _ _ hk => (hk (Set.mem_univ _)).elim)

theorem average_smooth (K : Subgroup (G F ζ hζ))
    (hK : IsCompact (K : Set (G F ζ hζ))) (μ : Measure K) [IsFiniteMeasure μ]
    (f : G F ζ hζ → ℂ) (hf : Smooth F ζ hζ f) : Smooth F ζ hζ (average F ζ hζ K μ f) := by
  obtain ⟨U,hU⟩ := hf.2.2
  obtain ⟨V,hV⟩ := compact_uniform_conjugated_finite_level F ζ hζ (K : Set _) hK U
  refine ⟨average_continuous F ζ hζ K hK μ f hf.1, ?_, V, ?_⟩
  · have hs := compact_convolution_arch_regular F ζ hζ K hK μ (1 : C(K,ℂ)) f hf
    simpa only [compactConvolution, ContinuousMap.one_apply, one_mul, average] using hs
  · intro g u hu
    apply integral_congr_ae
    filter_upwards with k
    have he : (g*u)*k.val = (g*k.val)*(k.val⁻¹*u*k.val) := by group
    rw [he,hU _ _ (hV k.val k.property u hu)]

theorem average_automorphic (K : Subgroup (G F ζ hζ))
    (hK : IsCompact (K : Set (G F ζ hζ))) (μ : Measure K) [IsFiniteMeasure μ]
    (f : G F ζ hζ → ℂ) (hf : Automorphic F ζ hζ f) :
    Automorphic F ζ hζ (average F ζ hζ K μ f) := by
  refine ⟨average_smooth F ζ hζ K hK μ f hf.1, ?_, ?_⟩
  · intro γ g
    apply integral_congr_ae
    filter_upwards with k
    rw [mul_assoc,hf.2.1]
  · intro ε g
    unfold average
    simp_rw [mul_assoc,hf.2.2]
    exact integral_const_mul _ _

theorem average_fixed (K : Subgroup (G F ζ hζ)) (μ : Measure K)
    [μ.IsMulLeftInvariant] (f : G F ζ hζ → ℂ) (g : G F ζ hζ) (k : K) :
    average F ζ hζ K μ f (g*k.val) = average F ζ hζ K μ f g := by
  unfold average
  simp_rw [mul_assoc]
  exact integral_mul_left_eq_self (μ := μ) (fun a : K => f (g*a.val)) k
end DedekindZetaZeroFree.FourierContinuation.ResidualRawAverage

end
