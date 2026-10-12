module

public import DedekindZetaZeroFree.Eisenstein.Continuation.FiniteWordNumerator
public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberAnalyticity

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open Filter
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.FiniteWordNumerator renaming finite_word_numerator → finite_word_numerator
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

 theorem normalize_div_chamber {O V : Set ℂ} (hO : IsPreconnected O)
    (hVO : V ⊆ O) (hV : IsOpen V)
    (q S E : ℂ → ℂ) (hq : AnalyticOnNhd ℂ q O) (hq0 : q 0 = 1)
    (hz : (0 : ℂ) ∈ O) (hS : MeromorphicOn S O) (hE : AnalyticOnNhd ℂ E V)
    (hpin : ∀ z ∈ V, S z = q z * E z) :
    ∀ z ∈ V, toMeromorphicNFOn (fun s => S s / q s) O z = E z := by
  have hqne : ∀ᶠ z in codiscreteWithin O, q z ≠ 0 := by
    rcases hq.eqOn_zero_or_eventually_ne_zero_of_preconnected hO with he | hn
    · have hh := he hz
      simp only [hq0, Pi.zero_apply] at hh
      exact (one_ne_zero hh).elim
    · exact hn
  have hm : MeromorphicOn (fun s => S s / q s) O := hS.div hq.meromorphicOn
  intro z hzV
  have hg : (fun s => S s / q s) =ᶠ[𝓝[≠] z] E := by
    have hn := eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hqne z (hVO hzV)
    filter_upwards [hn, nhdsWithin_le_nhds (hV.mem_nhds hzV)] with s hs hv
    rw [hpin s hv, mul_div_cancel_left₀ _ (hs (hVO hv))]
  have hn := hm.toMeromorphicNFOn_eq_self_on_nhdsNE (hVO hzV)
  have hf := meromorphicNFOn_toMeromorphicNFOn (fun s => S s / q s) O (hVO hzV)
  exact ((hf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hE z hzV).meromorphicNFAt).mp
    (hn.trans hg)).eq_of_nhds

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

include C R P H in

theorem literal_scalar_continuation
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ E : ℂ → G F ζ hζ → ℂ,
      (∀ g, MeromorphicNFOn (fun s => E s g) KPContinuation.spectralDomain) ∧
      ∀ s, (1 / 3 : ℝ) < s.re → ∀ g, E s g = eisenstein F ζ hζ K f s g := by
  obtain ⟨Q, S, T, r, hQ, hQ0, hS, hSc, hr, hb, hne, hT, hclear⟩ :=
    finite_word_numerator F ζ hζ C R P H K hK f
  let E : ℂ → G F ζ hζ → ℂ := fun s g =>
    toMeromorphicNFOn (fun z => S z g / Q z) KPContinuation.spectralDomain s
  refine ⟨E, fun g => meromorphicNFOn_toMeromorphicNFOn _ _, ?_⟩
  intro s hs g
  apply normalize_div_chamber KPContinuation.spectralDomain_isConnected.isPreconnected
    KPContinuation.convergenceHalfPlane_subset_spectralDomain
    (isOpen_lt continuous_const Complex.continuous_re) Q (fun z => S z g)
    (fun z => eisenstein F ζ hζ K f z g) hQ hQ0
    (by norm_num [KPContinuation.spectralDomain]) (hS g)
    (fun z hz => KPLiteralExceptionalResidue.LiteralChamberAnalytic.raw_chamber_analytic F ζ hζ K hK f z hz g)
    (fun z hz => hSc z hz g) s hs

end DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource

end
