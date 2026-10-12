module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarBranchUniquenessAndSingularSets

@[expose] public section

noncomputable section
open Filter
open scoped Topology
namespace DedekindZetaZeroFree.ResidueContinuity.ScalarSourcePoleGeometry

theorem analytic_zeroSet_isolated {O : Set ℂ} (hO : IsOpen O)
    (hconn : IsPreconnected O) (q : ℂ → ℂ) (hq : AnalyticOnNhd ℂ q O)
    {a : ℂ} (ha : a ∈ O) (hqa : q a ≠ 0) :
    IsolatedPoles O {s | s ∈ O ∧ q s = 0} := by
  have hne : ∀ᶠ s in codiscreteWithin O, q s ≠ 0 := by
    rcases hq.eqOn_zero_or_eventually_ne_zero_of_preconnected hconn with hz | hn
    · exact (hqa (hz ha)).elim
    · exact hn
  intro z hz
  have hlocal := eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hne z hz
  have hall : ∀ᶠ s in 𝓝 z, s ≠ z → s ∈ O → q s ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      eventually_nhdsWithin_iff.mp hlocal
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hall
  obtain ⟨t, ht, htO⟩ := Metric.isOpen_iff.mp hO z hz
  refine ⟨min r t, lt_min hr ht,
    (Metric.ball_subset_ball (min_le_right _ _)).trans htO, ?_⟩
  intro s hs hp
  by_contra hsz
  exact hball ((Metric.mem_ball.mp hs).trans_le (min_le_left _ _)) hsz hp.1 hp.2

end DedekindZetaZeroFree.ResidueContinuity.ScalarSourcePoleGeometry

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms ResidueContinuity.ScalarSourcePoleGeometry
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
variable {B : JointRootAlignedSources R N} {v : R.A.UnitQuotient}

theorem SelectedScalarBranch.germ_eq_of_weighted_chamber
    (D : SelectedScalarBranch R B v) (q : ℂ → ℂ) (A : ℂ → Functions R)
    (hq : AnalyticOnNhd ℂ q KPContinuation.spectralDomain)
    (hq0 : q 0 ≠ 0)
    (hA : ∀ g, MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain)
    (hch : ∀ s, (1 / 3 : ℝ) < s.re → ∀ g,
      A s g = q s * KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
        B.sources.K (B.sources.flat v) s g)
    (g : Group R) {s : ℂ} (hs : s ∈ KPContinuation.spectralDomain) :
    (fun z => D.E z g) =ᶠ[𝓝[≠] s] (fun z => A z g / q z) := by
  have he : (fun z => q z * D.E z g) =ᶠ[𝓝[≠] s] (fun z => A z g) := by
    apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
      (hq.meromorphicOn.mul (D.normal g).meromorphicOn) (hA g)
      KPContinuation.spectralDomain_isConnected.isPreconnected
      (isOpen_lt continuous_const Complex.continuous_re)
      KPContinuation.convergenceHalfPlane_subset_spectralDomain
      ⟨1, by norm_num⟩ _ hs
    intro z hz
    change q z * D.E z g = A z g
    rw [D.chamber z hz g, hch z hz g]
  have hne : ∀ᶠ z in codiscreteWithin KPContinuation.spectralDomain, q z ≠ 0 := by
    rcases hq.eqOn_zero_or_eventually_ne_zero_of_preconnected
      KPContinuation.spectralDomain_isConnected.isPreconnected with hz | hn
    · exact (hq0 (hz (by norm_num [KPContinuation.spectralDomain]))).elim
    · exact hn
  have hlocal := eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hne s hs
  filter_upwards [he, hlocal,
    nhdsWithin_le_nhds (KPContinuation.spectralDomain_isOpen.mem_nhds hs)] with z he hn hz
  rw [← he, mul_div_cancel_left₀ _ (hn hz)]

theorem selectedPoleSet_of_weighted_comparison
    (D : SelectedScalarBranch R B v) (P : Set ℂ)
    (hP : P ⊆ KPContinuation.spectralDomain)
    (hi : IsolatedPoles KPContinuation.spectralDomain P)
    (q : ℂ → ℂ) (A : ℂ → Functions R)
    (hq : AnalyticOnNhd ℂ q KPContinuation.spectralDomain) (hq0 : q 0 ≠ 0)
    (hA : ∀ g, MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain)
    (hch : ∀ s, (1 / 3 : ℝ) < s.re → ∀ g,
      A s g = q s * KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
        B.sources.K (B.sources.flat v) s g)
    (hreg : ∀ s ∈ KPContinuation.spectralDomain, s ∉ P →
      ∀ g, AnalyticAt ℂ (fun z => A z g) s) :
    Nonempty (SelectedPoleSet D) := by
  let Z : Set ℂ := {s | s ∈ KPContinuation.spectralDomain ∧ q s = 0}
  have hZi : IsolatedPoles KPContinuation.spectralDomain Z :=
    analytic_zeroSet_isolated KPContinuation.spectralDomain_isOpen
      KPContinuation.spectralDomain_isConnected.isPreconnected q hq
      (by norm_num [KPContinuation.spectralDomain]) hq0
  apply selectedPoleSet_of_regular D (P ∪ Z)
    (fun _ hs => hs.elim (fun hp => hP hp) (fun hz => hz.1)) (hi.union hZi)
  intro s hs hn g
  have hnp : s ∉ P := fun hp => hn (Or.inl hp)
  have hqne : q s ≠ 0 := fun hz => hn (Or.inr ⟨hs, hz⟩)
  exact D.analyticAt_of_germ g hs ((hreg s hs hnp g).div (hq s hs) hqne)
    (D.germ_eq_of_weighted_chamber q A hq hq0 hA hch g hs)

end DedekindZetaZeroFree.ThetaExpansion

end
