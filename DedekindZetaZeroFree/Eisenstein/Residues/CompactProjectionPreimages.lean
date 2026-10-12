module

public import DedekindZetaZeroFree.Eisenstein.Residues.IteratedLiePreimages
public import DedekindZetaZeroFree.Eisenstein.Continuation.Convolution.ProjectedNumerator
public import DedekindZetaZeroFree.Eisenstein.Continuation.Convolution.ProjectedChamberInterchange

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter MeasureTheory
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.ActualProjectedFlatExpansion renaming projected_family_finite_flat_expansion → projected_family_finite_flat_expansion
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.ProjectedChamberComparison renaming finite_flat_projected_chamber → finite_flat_projected_chamber
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.NativeProjectedNumerator renaming weightedOrbitFunctional → weightedOrbitFunctional
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.NativeProjectedNumerator renaming weightedOrbitFunctional_apply → weightedOrbitFunctional_apply
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.NativeProjectedNumerator renaming meromorphic_comp_functional → meromorphic_comp_functional
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator renaming finite_literal_compact_numerator → finite_literal_compact_numerator
open _root_.DedekindZetaZeroFree.RootDerivatives renaming chamber_germ_unique → chamber_germ_unique
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
local instance (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

 theorem projected_flat_residue {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (Cf : FlatScalarResidue F ζ hζ f) (a : G F ζ hζ)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (h : C(K, ℂ)) (hh : h ∈ TauCeti.representativeSubmodule ℂ K) :
    ∃ (v : Flat F ζ hζ K) (Cv : FlatScalarResidue F ζ hζ v),
      ∀ g, Cv.numerator 0 g = ∫ k : K, h k * Cf.numerator 0 (g * k.val * a) ∂μ := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK.1
  obtain ⟨n,b,c,hc,he⟩ := projected_family_finite_flat_expansion F ζ hζ K hK μ f a h hh
  let C := fun j => Classical.choice (flatScalarResidue_nonempty F ζ hζ K hK (b j))
  let v := FiniteWhittakerProjectors.FlatFiniteSum.sum F ζ hζ Finset.univ (fun j => c j 0) b
  let Cv := Classical.choice (flatScalarResidue_nonempty F ζ hζ K hK v)
  refine ⟨v,Cv,?_⟩
  intro g
  rw [flat_sum_residue hK Finset.univ (fun j => c j 0) b Cv C]
  let orbit : K → G F ζ hζ := fun k => g * k.val * a
  have ho : Continuous orbit := (continuous_const.mul continuous_subtype_val).mul continuous_const
  let D : Set (G F ζ hζ) := Set.range orbit
  have hD : IsCompact D := isCompact_range ho
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let q : C(K,D) := ⟨fun k => ⟨orbit k,⟨k,rfl⟩⟩,ho.subtype_mk _⟩
  letI : T2Space (G F ζ hζ) := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  letI : LocallyCompactSpace (G F ζ hζ) := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.1
  obtain ⟨L⟩ := KPGlobalProductPolarizationCharacter.exists_compatible_local_data F ζ hζ
  obtain ⟨M,_⟩ := KPGlobalTorusFiniteStages.compatibleModelData_exists F ζ hζ L
  obtain ⟨R,_,_,P,⟨H⟩⟩ := kp_ms_fixed_haar_disintegration F ζ hζ
    (Measure.haar : Measure (G F ζ hζ)) inferInstance
  obtain ⟨Q,A,B,r,hQ,hQ0,hAm,hAc,hr,hball,hBa,hclear⟩ :=
    finite_literal_compact_numerator F ζ hζ M R P H D hD K hK f
  have hz : (0 : ℂ) ∈ KPContinuation.spectralDomain := by norm_num [KPContinuation.spectralDomain]
  have hpin (x : D) : B 0 x = Cf.numerator 0 x.val := by
    have hg := chamber_germ_unique (fun s => A s x) (fun s => Q s * Cf.E s x.val)
      (meromorphic_comp_functional (ContinuousMap.evalCLM ℂ x) hAm)
      (hQ.meromorphicOn.mul (Cf.meromorphic x.val))
      (fun s hs => by rw [hAc s hs,Cf.chamber s hs])
    have hn : (fun s => B s x) =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => Q s * Cf.numerator s x.val) := by
      filter_upwards [hg,Cf.clears x.val,nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),self_mem_nhdsWithin]
        with s hg hc hs hn
      rw [hclear s hs hn]
      change s * A s x = _
      rw [hg,hc]; ring
    have hb := ((ContinuousMap.evalCLM ℂ x).analyticAt _).comp (hBa 0 (Metric.mem_ball_self hr))
    have hcf := (hQ 0 hz).continuousAt.mul ((Cf.analytic x.val 0 (Metric.mem_ball_self Cf.radius_pos)).continuousAt)
    simpa only [Function.comp_def, ContinuousMap.evalCLM_apply, Pi.mul_apply, hQ0,one_mul] using ((hb.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hcf).mp hn).eq_of_nhds
  let W := weightedOrbitFunctional q μ h
  have hWc (s : ℂ) (hs : (1/3 : ℝ) < s.re) : W (A s) =
      Q s * ∑ j, c j s * (C j).E s g := by
    rw [weightedOrbitFunctional_apply]
    have hp : (fun k : K => h k * A s (q k)) =
        fun k : K => Q s * (h k * eisenstein F ζ hζ K f s (g * k.val * a)) := by
      funext k; rw [hAc s hs]; change h k * (Q s * eisenstein F ζ hζ K f s (g * k.val * a)) = _; ring
    rw [hp,integral_const_mul,finite_flat_projected_chamber F ζ hζ K hK μ f a h n b c he s hs g]
    simp_rw [(C _).chamber s hs]
  have hg := chamber_germ_unique (fun s => W (A s))
    (fun s => Q s * ∑ j, c j s * (C j).E s g)
    (meromorphic_comp_functional W hAm)
    (hQ.meromorphicOn.mul (MeromorphicOn.fun_sum (fun j _ =>
      ((hc j).mono (Set.subset_univ _)).meromorphicOn.mul ((C j).meromorphic g)))) hWc
  have hn : (fun s => W (B s)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun s => Q s * ∑ j, c j s * (C j).numerator s g) := by
    have hall := Filter.eventually_all.mpr (fun j => (C j).clears g)
    filter_upwards [hg,hall,nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),self_mem_nhdsWithin]
      with s hg hcs hs hn
    rw [hclear s hs hn,map_smul]
    change s * W (A s) = _
    rw [hg]
    simp_rw [hcs]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hBc := (W.analyticAt _).comp (hBa 0 (Metric.mem_ball_self hr))
  have hCc : ContinuousAt (fun s => Q s * ∑ j, c j s * (C j).numerator s g) 0 := by
    apply (hQ 0 hz).continuousAt.mul
    apply tendsto_finsetSum
    intro j _
    exact (hc j 0 (Set.mem_univ _)).continuousAt.mul
      ((C j).analytic g 0 (Metric.mem_ball_self (C j).radius_pos)).continuousAt
  have hp := ((hBc.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hCc).mp hn).eq_of_nhds
  simp only [hQ0,one_mul] at hp
  rw [← hp]
  change weightedOrbitFunctional q μ h (B 0) = _
  rw [weightedOrbitFunctional_apply]
  apply integral_congr_ae
  filter_upwards [] with k
  rw [hpin]
  rfl

end DedekindZetaZeroFree.RootDerivatives

end
