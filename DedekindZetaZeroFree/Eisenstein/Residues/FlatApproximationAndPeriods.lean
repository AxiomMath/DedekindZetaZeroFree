module

public import DedekindZetaZeroFree.Eisenstein.Residues.CompactConvolution.Range
public import DedekindZetaZeroFree.Analysis.Integration.UniformIntegralDetection
public import DedekindZetaZeroFree.Adeles.Quotients.CompactRootRepresentatives
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Convolution.AutomorphicKFiniteVectors
public import DedekindZetaZeroFree.Theta.Whittaker.FourierVanishingAndRootInvariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualOwnedDensity
open KPLiteralRaw
open KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
local instance : IsTopologicalGroup (G F ζ hζ) :=
 (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
local instance (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

theorem right_automorphic (f : Functions F ζ hζ) (hf : Automorphic F ζ hζ f)
    (a : G F ζ hζ) : Automorphic F ζ hζ (fun g => f (g*a)) := by
  obtain ⟨U,hU⟩ := hf.1.2.2
  obtain ⟨V,hV⟩ := compact_uniform_conjugated_finite_level F ζ hζ {a} isCompact_singleton U
  refine ⟨⟨hf.1.1.comp (continuous_id.mul continuous_const), ?_, V, ?_⟩, ?_, ?_⟩
  · intro g
    exact ArchRegularity.right_translate_arch_slice_smooth F ζ hζ f hf.1 g a
  · intro g b hb
    have hc := hV a (Set.mem_singleton a) b hb
    change f ((g*b)*a) = f (g*a)
    rw [show (g*b)*a = (g*a)*(a⁻¹*b*a) by group, hU _ _ hc]
  · intro γ g
    simpa only [mul_assoc] using hf.2.1 γ (g*a)
  · intro ε g
    simpa only [mul_assoc] using hf.2.2 ε (g*a)

theorem flat_root_approximation
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (A : TensorActionSource.LiteralResidueFamily hK)
    (f : Flat F ζ hζ K) (hf : Automorphic F ζ hζ (A.cleared f 0))
    (a : G F ζ hζ) (ε : ℝ) (hε : 0 < ε) :
    ∃ b : Flat F ζ hζ K, Automorphic F ζ hζ (A.cleared b 0) ∧
      ∀ x : KPAdditiveQuotient F,
        ‖A.cleared b 0 (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out x)) -
          A.cleared f 0 (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out x)*a)‖ < ε := by
  let φ := fun g => A.cleared f 0 (g*a)
  have hφ := right_automorphic F ζ hζ _ hf a
  obtain ⟨D,hD,hrep⟩ := KPLiteralPeriod.HCCoreDensity.compact_root_evaluation_representatives F ζ hζ
  obtain ⟨μ,hHaar,hProb,h,hh,happrox⟩ := representative_convolution_uniform_approximation
    F ζ hζ K hK.1 φ hφ.1.1 D hD ε hε
  letI : μ.IsHaarMeasure := hHaar
  letI : IsProbabilityMeasure μ := hProb
  obtain ⟨v,hv⟩ := ResidualCompactConvolution.convolution_mem_owned_range
    F ζ hζ C R P H K hK A μ f a h hh
  let b : TensorActionSource.literalFlatModule K := (TensorActionSource.literalZeroProfileEquiv hK).symm v
  have hb : A.cleared (TensorActionSource.asLiteralFlat b) 0 = compactConvolution F ζ hζ K μ h φ := by
    rw [← A.residue_flat b]
    change A.residue ((TensorActionSource.literalZeroProfileEquiv hK)
      ((TensorActionSource.literalZeroProfileEquiv hK).symm v)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hv
  have hauto := (representative_convolution_automorphic_kfinite F ζ hζ K hK.1 μ h hh φ hφ).1
  refine ⟨b, hb ▸ hauto, ?_⟩
  intro x
  obtain ⟨y,hy,heval⟩ := hrep x
  have hbval := heval _ hauto.2.1
  have hφval := heval φ hφ.2.1
  rw [hb,hbval]
  change ‖compactConvolution F ζ hζ K μ h φ y - φ (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out x))‖ < ε
  rw [hφval]
  exact happrox y hy

theorem exists_flat_period_ne_zero
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (A : TensorActionSource.LiteralResidueFamily hK)
    (f : Flat F ζ hζ K) (hf : Automorphic F ζ hζ (A.cleared f 0))
    (ψ : ContinuousAddChar (KPAdditiveQuotient F))
    (hψ : KPReflectionSpec.NontrivialCharacter ψ)
    (μ : Measure (KPAdditiveQuotient F)) (hμ : μ.IsAddHaarMeasure)
    (a : G F ζ hζ) (ha : KPLiteralRaw.period F ζ hζ ψ μ
      (rightAction F ζ hζ a (A.cleared f 0)) ≠ 0) :
    ∃ b : Flat F ζ hζ K, Automorphic F ζ hζ (A.cleared b 0) ∧
      KPLiteralRaw.period F ζ hζ ψ μ (A.cleared b 0) ≠ 0 := by
  obtain ⟨hfinite,hmass,hint,_⟩ :=
    KPLiteralPeriod.haar_fourier_vanishing_forces_root_invariance F ζ hζ ψ hψ μ hμ
      (A.cleared f 0) hf
  let I := {b : Flat F ζ hζ K // Automorphic F ζ hζ (A.cleared b 0)}
  let v : I → KPAdditiveQuotient F → ℂ := fun b x =>
    A.cleared b.val 0 (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out x))
  have hv : ∀ b:I, Integrable (fun x => v b x * star (ψ.toAddChar x)) μ := by
    intro b
    have hb := (KPLiteralPeriod.haar_fourier_vanishing_forces_root_invariance
      F ζ hζ ψ hψ μ hμ (A.cleared b.val 0) b.property).2.2.1 (1:G F ζ hζ)
    simpa only [v,mul_one] using hb
  have happrox : ∀ ε:ℝ, 0 < ε → ∃ b:I, ∀ x,
      ‖v b x - A.cleared f 0 (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out x)*a)‖ < ε := by
    intro ε hε
    obtain ⟨b,hb,he⟩ := flat_root_approximation F ζ hζ C R P H K hK A f hf a ε hε
    exact ⟨⟨b,hb⟩,he⟩
  obtain ⟨b,hb⟩ := KPLiteralPeriod.nonzero_integral_detected_by_uniform_approximation
    μ hfinite hmass
    (fun x => A.cleared f 0 (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out x)*a))
    (fun x => star (ψ.toAddChar x))
    (fun x => by rw [norm_star]; exact ψ.unitary x) (hint a) ha v hv happrox
  exact ⟨b.val,b.property,hb⟩

end DedekindZetaZeroFree.FourierContinuation.ResidualOwnedDensity

end
