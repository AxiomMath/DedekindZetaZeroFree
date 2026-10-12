module

public import DedekindZetaZeroFree.Analysis.Complex.CompactMeromorphicFamilies
public import DedekindZetaZeroFree.Eisenstein.Residues.TensorProducts.ResidueFamiliesAndPeriods

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualOwnedCompactPin
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem center_eq
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (A : TensorActionSource.LiteralResidueFamily hK)
    (f : Flat F ζ hζ K) (D : Set (G F ζ hζ)) (hD : IsCompact D) :
    letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
    ∀ (Q : ℂ → ℂ) (S T : ℂ → C(D, ℂ))
      (hQ : AnalyticOnNhd ℂ Q KPContinuation.spectralDomain) (hQ0 : Q 0 = 1)
      (hS : MeromorphicOn S KPContinuation.spectralDomain)
      (hSc : ∀ s, (1 : ℝ) / 3 < s.re → ∀ g, S s g = Q s * eisenstein F ζ hζ K f s g)
      (r : ℝ) (hr : 0 < r)
      (hT : AnalyticOnNhd ℂ T (Metric.ball (0 : ℂ) r))
      (hclear : ∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → T s = s • S s),
      ∀ g : D, T 0 g = A.cleared f 0 g := by
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
  intro Q S T hQ hQ0 hS hSc r hr hT hclear g
  obtain ⟨O,u,hO,hc,hOc,hu,hub,hE,hAc,han⟩ := A.germ.2 f
  let ev : C(D, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ g
  have he : (fun s => S s g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => Q s * A.E f s g) := by
    apply CompactPeriodAnalyticity.UpperPeriodContinuation.chamber_identity_germ
      (CompactPeriodAnalyticity.UpperPeriodContinuation.meromorphicOn_observation ev S _ hS)
      (hQ.meromorphicOn.mul ((A.normal f g).meromorphicOn))
      KPContinuation.spectralDomain_isConnected.isPreconnected
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ?_ 0 ?_
    · intro s hs
      change S s g = Q s * A.E f s g
      rw [hSc s hs, A.germ.1 f s hs]
    · norm_num [KPContinuation.spectralDomain]
  have hnum : (fun s => T s g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => Q s * A.cleared f s g) := by
    filter_upwards [he, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hu), self_mem_nhdsWithin]
      with s hes hsr hsu hne
    rw [hclear s hsr hne]
    change s * S s g = Q s * A.cleared f s g
    rw [hes, congrFun (hAc s hsu hne) g]
    change s * (Q s * A.E f s g) = Q s * (s * A.E f s g)
    ring
  have hQc : ContinuousAt (fun s => Q s * A.cleared f s g) 0 :=
    (hQ 0 (by norm_num [KPContinuation.spectralDomain])).continuousAt.mul
      ((han g) 0 (Metric.mem_ball_self hu)).continuousAt
  have ht : ContinuousAt (fun s => T s g) 0 :=
    ((ev.analyticAt _).comp (hT 0 (Metric.mem_ball_self hr))).continuousAt
  have he0 := (ht.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hQc).mp hnum |>.eq_of_nhds
  simpa only [hQ0, one_mul] using he0

end DedekindZetaZeroFree.FourierContinuation.ResidualOwnedCompactPin

end
