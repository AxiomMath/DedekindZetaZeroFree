module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberAbsoluteConvergence
public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarFlatSections
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FlatFiniteSum

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open KPLiteralRaw
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

structure FlatScalarResidue {K : Subgroup (G F ζ hζ)} (f : Flat F ζ hζ K) where
  E : ℂ → Functions F ζ hζ
  meromorphic : ∀ g, MeromorphicOn (fun z => E z g) KPContinuation.spectralDomain
  chamber : ∀ z, (1 / 3 : ℝ) < z.re → ∀ g, E z g = eisenstein F ζ hζ K f z g
  radius : ℝ
  radius_pos : 0 < radius
  numerator : ℂ → Functions F ζ hζ
  analytic : ∀ g, AnalyticOnNhd ℂ (fun z => numerator z g) (Metric.ball 0 radius)
  clears : ∀ g, (fun z => numerator z g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => z * E z g)

variable {F ζ hζ}

theorem FlatScalarResidue.value_unique {K : Subgroup (G F ζ hζ)}
    {f : Flat F ζ hζ K} (A B : FlatScalarResidue F ζ hζ f) (g : G F ζ hζ) :
    A.numerator 0 g = B.numerator 0 g := by
  have he : (fun z => A.E z g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => B.E z g) := by
    apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
      (A.meromorphic g) (B.meromorphic g)
      KPContinuation.spectralDomain_isConnected.isPreconnected
      (isOpen_lt continuous_const Complex.continuous_re)
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ⟨1, by norm_num⟩ ?_
      (by norm_num [KPContinuation.spectralDomain])
    intro z hz
    change A.E z g = B.E z g
    rw [A.chamber z hz g, B.chamber z hz g]
  have hn : (fun z => A.numerator z g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => B.numerator z g) := by
    filter_upwards [A.clears g, B.clears g, he] with z ha hb he
    rw [ha, hb, he]
  have hAc := (A.analytic g 0 (Metric.mem_ball_self A.radius_pos)).continuousAt
  have hBc := (B.analytic g 0 (Metric.mem_ball_self B.radius_pos)).continuousAt
  exact ((hAc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hBc).mp hn).eq_of_nhds

variable (F ζ hζ)

variable {F ζ hζ}

theorem flat_finite_chamber {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    {I : Type*} (s : Finset I) (v : I → Flat F ζ hζ K) (b : I → ℂ → ℂ)
    (a : G F ζ hζ)
    (hexp : ∀ z g, f.val z (g * a) = ∑ i ∈ s, b i z * (v i).val z g)
    (z : ℂ) (hz : (1 / 3 : ℝ) < z.re) (g : G F ζ hζ) :
    eisenstein F ζ hζ K f z (g * a) = ∑ i ∈ s, b i z * eisenstein F ζ hζ K (v i) z g := by
  unfold eisenstein
  simp only [← mul_assoc, hexp]
  rw [Summable.tsum_finsetSum (fun i _ =>
    (KPLiteralExceptionalResidue.chamberConvergence F ζ hζ K hK (v i) z hz g).mul_left (b i z))]
  exact Finset.sum_congr rfl (fun i _ => tsum_mul_left)

theorem flat_finite_residue {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) {f : Flat F ζ hζ K}
    (A : FlatScalarResidue F ζ hζ f) {I : Type*} (s : Finset I)
    (v : I → Flat F ζ hζ K) (B : ∀ i, FlatScalarResidue F ζ hζ (v i))
    (b : I → ℂ → ℂ) (hb : ∀ i ∈ s, AnalyticOnNhd ℂ (b i) KPContinuation.spectralDomain)
    (a : G F ζ hζ)
    (hexp : ∀ z g, f.val z (g * a) = ∑ i ∈ s, b i z * (v i).val z g)
    (g : G F ζ hζ) :
    A.numerator 0 (g * a) = ∑ i ∈ s, b i 0 * (B i).numerator 0 g := by
  have hzero : (0 : ℂ) ∈ KPContinuation.spectralDomain := by norm_num [KPContinuation.spectralDomain]
  have he : (fun z => A.E z (g * a)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => ∑ i ∈ s, b i z * (B i).E z g) := by
    apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
      (A.meromorphic _) (MeromorphicOn.fun_sum (fun i hi =>
        (hb i hi).meromorphicOn.mul ((B i).meromorphic g)))
      KPContinuation.spectralDomain_isConnected.isPreconnected
      (isOpen_lt continuous_const Complex.continuous_re)
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ⟨1, by norm_num⟩ ?_ hzero
    intro z hz
    change A.E z (g * a) = _
    rw [A.chamber z hz, flat_finite_chamber hK f s v b a hexp z hz]
    exact Finset.sum_congr rfl (fun i _ => congrArg (b i z * ·) ((B i).chamber z hz g).symm)
  have hall : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ i ∈ s,
      (B i).numerator z g = z * (B i).E z g :=
    (Filter.eventually_all_finite s.finite_toSet).mpr (fun i hi => (B i).clears g)
  have hn : (fun z => A.numerator z (g * a)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => ∑ i ∈ s, b i z * (B i).numerator z g) := by
    filter_upwards [A.clears _, he, hall] with z ha he hz
    rw [ha, he, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => by rw [hz i hi]; ring)
  have hcont : ContinuousAt (fun z => ∑ i ∈ s, b i z * (B i).numerator z g) 0 := by
    apply tendsto_finsetSum
    intro i hi
    exact (hb i hi 0 hzero).continuousAt.mul
      ((B i).analytic g 0 (Metric.mem_ball_self (B i).radius_pos)).continuousAt
  have hAc := (A.analytic (g * a) 0 (Metric.mem_ball_self A.radius_pos)).continuousAt
  exact ((hAc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hcont).mp hn).eq_of_nhds

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end

section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

structure FlatScalarResidue {K : Subgroup (G F ζ hζ)} (f : Flat F ζ hζ K) where
  E : ℂ → Functions F ζ hζ
  meromorphic : ∀ g, MeromorphicOn (fun z => E z g) KPContinuation.spectralDomain
  chamber : ∀ z, (1 / 3 : ℝ) < z.re → ∀ g, E z g = eisenstein F ζ hζ K f z g
  radius : ℝ
  radius_pos : 0 < radius
  numerator : ℂ → Functions F ζ hζ
  analytic : ∀ g, AnalyticOnNhd ℂ (fun z => numerator z g) (Metric.ball 0 radius)
  clears : ∀ g, (fun z => numerator z g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => z * E z g)

variable {F ζ hζ}

variable (F ζ hζ)
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.FiniteWordNumerator renaming finite_word_numerator → finite_word_numerator

theorem flatScalarResidue_exists (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    Nonempty (FlatScalarResidue F ζ hζ f) := by
  obtain ⟨Q,S,T,r,hQ,hQ0,hS,hch,hr,hb,hne,hTa,hTe⟩ :=
    finite_word_numerator F ζ hζ C R P H K hK f
  obtain ⟨E,hE,hEc⟩ := EisensteinSmoothGerms.ScalarSource.literal_scalar_continuation F ζ hζ C R P H K hK f
  have he (g) : (fun z => S z g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => Q z * E z g) := by
    apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
      (hS g) (hQ.meromorphicOn.mul (hE g).meromorphicOn)
      KPContinuation.spectralDomain_isConnected.isPreconnected
      (isOpen_lt continuous_const Complex.continuous_re)
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ⟨1, by norm_num⟩ ?_
      (by norm_num [KPContinuation.spectralDomain])
    intro z hz
    change S z g = Q z * E z g
    rw [hch z hz g, hEc z hz g]
  refine ⟨{
    E := E
    meromorphic := fun g => (hE g).meromorphicOn
    chamber := hEc
    radius := r
    radius_pos := hr
    numerator := fun z g => T z g / Q z
    analytic := fun g => (hTa g).div (hQ.mono hb) hne
    clears := ?_ }⟩
  intro g
  filter_upwards [he g, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
    self_mem_nhdsWithin] with z hz hzr hzne
  rw [hTe z hzr hzne g, hz]
  calc
    z * (Q z * E z g) / Q z = (z * E z g) * Q z / Q z := by ring
    _ = _ := mul_div_cancel_right₀ _ (hne z hzr)

variable {F ζ hζ}

theorem flat_finite_chamber {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    {I : Type*} (s : Finset I) (v : I → Flat F ζ hζ K) (b : I → ℂ → ℂ)
    (a : G F ζ hζ)
    (hexp : ∀ z g, f.val z (g * a) = ∑ i ∈ s, b i z * (v i).val z g)
    (z : ℂ) (hz : (1 / 3 : ℝ) < z.re) (g : G F ζ hζ) :
    eisenstein F ζ hζ K f z (g * a) = ∑ i ∈ s, b i z * eisenstein F ζ hζ K (v i) z g := by
  unfold eisenstein
  simp only [← mul_assoc, hexp]
  rw [Summable.tsum_finsetSum (fun i _ =>
    (KPLiteralExceptionalResidue.chamberConvergence F ζ hζ K hK (v i) z hz g).mul_left (b i z))]
  exact Finset.sum_congr rfl (fun i _ => tsum_mul_left)

theorem flat_finite_residue {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) {f : Flat F ζ hζ K}
    (A : FlatScalarResidue F ζ hζ f) {I : Type*} (s : Finset I)
    (v : I → Flat F ζ hζ K) (B : ∀ i, FlatScalarResidue F ζ hζ (v i))
    (b : I → ℂ → ℂ) (hb : ∀ i ∈ s, AnalyticOnNhd ℂ (b i) KPContinuation.spectralDomain)
    (a : G F ζ hζ)
    (hexp : ∀ z g, f.val z (g * a) = ∑ i ∈ s, b i z * (v i).val z g)
    (g : G F ζ hζ) :
    A.numerator 0 (g * a) = ∑ i ∈ s, b i 0 * (B i).numerator 0 g := by
  have hzero : (0 : ℂ) ∈ KPContinuation.spectralDomain := by norm_num [KPContinuation.spectralDomain]
  have he : (fun z => A.E z (g * a)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => ∑ i ∈ s, b i z * (B i).E z g) := by
    apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
      (A.meromorphic _) (MeromorphicOn.fun_sum (fun i hi =>
        (hb i hi).meromorphicOn.mul ((B i).meromorphic g)))
      KPContinuation.spectralDomain_isConnected.isPreconnected
      (isOpen_lt continuous_const Complex.continuous_re)
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ⟨1, by norm_num⟩ ?_ hzero
    intro z hz
    change A.E z (g * a) = _
    rw [A.chamber z hz, flat_finite_chamber hK f s v b a hexp z hz]
    exact Finset.sum_congr rfl (fun i _ => congrArg (b i z * ·) ((B i).chamber z hz g).symm)
  have hall : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ i ∈ s,
      (B i).numerator z g = z * (B i).E z g :=
    (Filter.eventually_all_finite s.finite_toSet).mpr (fun i hi => (B i).clears g)
  have hn : (fun z => A.numerator z (g * a)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => ∑ i ∈ s, b i z * (B i).numerator z g) := by
    filter_upwards [A.clears _, he, hall] with z ha he hz
    rw [ha, he, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => by rw [hz i hi]; ring)
  have hcont : ContinuousAt (fun z => ∑ i ∈ s, b i z * (B i).numerator z g) 0 := by
    apply tendsto_finsetSum
    intro i hi
    exact (hb i hi 0 hzero).continuousAt.mul
      ((B i).analytic g 0 (Metric.mem_ball_self (B i).radius_pos)).continuousAt
  have hAc := (A.analytic (g * a) 0 (Metric.mem_ball_self A.radius_pos)).continuousAt
  exact ((hAc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hcont).mp hn).eq_of_nhds

theorem FlatScalarResidue.value_unique {K : Subgroup (G F ζ hζ)}
    {f : Flat F ζ hζ K} (A B : FlatScalarResidue F ζ hζ f) (g : G F ζ hζ) :
    A.numerator 0 g = B.numerator 0 g := by
  have he : (fun z => A.E z g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => B.E z g) := by
    apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
      (A.meromorphic g) (B.meromorphic g)
      KPContinuation.spectralDomain_isConnected.isPreconnected
      (isOpen_lt continuous_const Complex.continuous_re)
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ⟨1, by norm_num⟩ ?_
      (by norm_num [KPContinuation.spectralDomain])
    intro z hz
    change A.E z g = B.E z g
    rw [A.chamber z hz g, B.chamber z hz g]
  have hn : (fun z => A.numerator z g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => B.numerator z g) := by
    filter_upwards [A.clears g, B.clears g, he] with z ha hb he
    rw [ha, hb, he]
  have hAc := (A.analytic g 0 (Metric.mem_ball_self A.radius_pos)).continuousAt
  have hBc := (B.analytic g 0 (Metric.mem_ball_self B.radius_pos)).continuousAt
  exact ((hAc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hBc).mp hn).eq_of_nhds

end DedekindZetaZeroFree.RootDerivatives

end
end
