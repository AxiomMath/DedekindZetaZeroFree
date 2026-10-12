module

public import DedekindZetaZeroFree.Eisenstein.Residues.CompactCenterEquality
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactWordNumerator
public import DedekindZetaZeroFree.Eisenstein.Continuation.Convolution.ChamberExpansionAndSmoothness

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualCompactConvolution
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator renaming finite_literal_compact_numerator → finite_literal_compact_numerator
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
local instance : IsTopologicalGroup (G F ζ hζ) :=
 (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
local instance (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

def observation {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (q : C(Y,X)) (μ : Measure Y) [IsProbabilityMeasure μ] (h : C(Y,ℂ)) :
    C(X,ℂ) →L[ℂ] ℂ :=
  let l : C(X,ℂ) →ₗ[ℂ] ℂ := {
    toFun := fun f => ∫ k, h k * f (q k) ∂μ
    map_add' := by
      intro f g
      simp only [ContinuousMap.add_apply, mul_add]
      exact integral_add
        ((h.continuous.mul (f.continuous.comp q.continuous)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
        ((h.continuous.mul (g.continuous.comp q.continuous)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
    map_smul' := by
      intro c f
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      simp_rw [mul_left_comm (h _) c]
      exact integral_const_mul c _ }
  l.mkContinuous ‖h‖ (by
    intro f
    change ‖∫ k, h k * f (q k) ∂μ‖ ≤ ‖h‖ * ‖f‖
    simpa using norm_integral_le_of_norm_le_const (μ := μ) (f := fun k => h k * f (q k))
      (Filter.Eventually.of_forall (fun k => by
        rw [norm_mul]
        exact mul_le_mul (h.norm_coe_le_norm k) (f.norm_coe_le_norm (q k))
          (norm_nonneg _) (norm_nonneg _))))

theorem residue_expansion
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (A : TensorActionSource.LiteralResidueFamily hK)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (h : C(K,ℂ)) (hh : h ∈ TauCeti.representativeSubmodule ℂ K) :
    ∃ (n : ℕ) (b : Fin n → Flat F ζ hζ K) (c : Fin n → ℂ),
      ∀ g, (∫ k:K, h k * A.cleared f 0 (g*k.val*a) ∂μ) =
        ∑ i, c i * A.cleared (b i) 0 g := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK.1
  obtain ⟨n,b,c,hc,hch⟩ :=
    KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ConvolutionSpan.ChamberExchange.representative_raw_chamber_expansion
      F ζ hζ K hK μ f a h hh
  refine ⟨n,b,fun i => c i 0,?_⟩
  intro g
  let D : Set (G F ζ hζ) := (fun k:K => g*k.val*a) '' Set.univ
  have hD : IsCompact D := isCompact_univ.image
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let q : C(K,D) := ⟨fun k => ⟨g*k.val*a,⟨k,Set.mem_univ _,rfl⟩⟩,
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _⟩
  let L : C(D,ℂ) →L[ℂ] ℂ := observation q μ h
  obtain ⟨Q,S,T,r,hQ,hQ0,hS,hSc,hr,hball,hT,hclear⟩ :=
    finite_literal_compact_numerator F ζ hζ C R P H D hD K hK f
  have hpin := ResidualOwnedCompactPin.center_eq F ζ hζ K hK A f D hD
    Q S T hQ hQ0 hS hSc r hr hT hclear
  have he : (fun s => L (S s)) =ᶠ[𝓝[≠] (0:ℂ)]
      (fun s => Q s * ∑ i, c i s * A.E (b i) s g) := by
    apply CompactPeriodAnalyticity.UpperPeriodContinuation.chamber_identity_germ
      (CompactPeriodAnalyticity.UpperPeriodContinuation.meromorphicOn_observation L S _ hS)
      (hQ.meromorphicOn.mul (MeromorphicOn.fun_sum
        (fun i _ => (show MeromorphicOn (c i) KPContinuation.spectralDomain from fun s _ => ((hc i).analyticAt s).meromorphicAt).mul ((A.normal (b i) g).meromorphicOn))))
      KPContinuation.spectralDomain_isConnected.isPreconnected
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ?_ 0 ?_
    · intro s hs
      change (∫ k:K, h k * S s (q k) ∂μ) = _
      simp_rw [hSc s hs]
      simp_rw [mul_left_comm (h _) (Q s)]
      rw [integral_const_mul]
      change Q s * (∫ k:K, h k * eisenstein F ζ hζ K f s (g*k.val*a) ∂μ) = _
      rw [hch s hs]
      change Q s * (∑ i, c i s * eisenstein F ζ hζ K (b i) s g) =
        Q s * (∑ i, c i s * A.E (b i) s g)
      simp only [A.germ.1 _ s hs]
    · norm_num [KPContinuation.spectralDomain]
  have hall : ∀ᶠ s in 𝓝[≠] (0:ℂ),
      ∀ i, A.cleared (b i) s g = s * A.E (b i) s g := by
    apply Filter.eventually_all.mpr
    intro i
    obtain ⟨O,u,hO,hcon,hOc,hu,hub,hE,hAc,han⟩ := A.germ.2 (b i)
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℂ) hu),self_mem_nhdsWithin]
      with s hs hn
    exact congrFun (hAc s hs hn) g
  have hnum : (fun s => L (T s)) =ᶠ[𝓝[≠] (0:ℂ)]
      (fun s => Q s * ∑ i, c i s * A.cleared (b i) s g) := by
    filter_upwards [he,hall,nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℂ) hr),self_mem_nhdsWithin]
      with s hes hcs hs hn
    rw [hclear s hs hn, map_smul, smul_eq_mul, hes]
    simp_rw [hcs]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hcont : ContinuousAt (fun s => Q s * ∑ i, c i s * A.cleared (b i) s g) 0 := by
    apply (hQ 0 (by norm_num [KPContinuation.spectralDomain])).continuousAt.mul
    have hci (i : Fin n) : ContinuousAt (fun s => c i s * A.cleared (b i) s g) 0 := by
      obtain ⟨O,u,hO,hcon,hOc,hu,hub,hE,hAc,han⟩ := A.germ.2 (b i)
      exact (hc i 0).continuousAt.mul ((han g) 0 (Metric.mem_ball_self hu)).continuousAt
    fun_prop
  have he0 := (((L.analyticAt _).comp (hT 0 (Metric.mem_ball_self hr))).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hcont).mp hnum |>.eq_of_nhds
  simp only [hQ0,one_mul] at he0
  change (∫ k:K, h k * A.cleared f 0 (g*k.val*a) ∂μ) = _
  convert he0 using 1
  change _ = ∫ k:K, h k * T 0 (q k) ∂μ
  exact integral_congr_ae (Filter.Eventually.of_forall (fun k => by change h k * _ = h k * _; rw [hpin]; rfl))

theorem convolution_mem_owned_range
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (A : TensorActionSource.LiteralResidueFamily hK)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (h : C(K,ℂ)) (hh : h ∈ TauCeti.representativeSubmodule ℂ K) :
    (fun g => ∫ k:K, h k * A.cleared f 0 (g*k.val*a) ∂μ) ∈ A.residue.range := by
  obtain ⟨n,b,c,he⟩ := residue_expansion F ζ hζ C R P H K hK A μ f a h hh
  refine ⟨∑ i, c i • TensorActionSource.literalZeroProfileEquiv hK
    (b i : TensorActionSource.literalFlatModule K), ?_⟩
  funext g
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    TensorActionSource.LiteralResidueFamily.residue_flat]
  exact (he g).symm

end DedekindZetaZeroFree.FourierContinuation.ResidualCompactConvolution

end
