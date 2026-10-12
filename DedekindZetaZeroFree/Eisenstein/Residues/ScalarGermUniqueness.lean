module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarAndSmoothGerms

@[expose] public section

noncomputable section
open scoped Topology
open Filter
namespace DedekindZetaZeroFree.KPScalarContinuation
open MomentSources EisensteinSmoothGerms

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}

theorem scalar_continuation_germ_unique (C D : ScalarContinuation R Q)
    (v : R.A.UnitQuotient) (g : Group R) (z : ℂ)
    (hz : z ∈ KPContinuation.spectralDomain) :
    (fun s => C.E v s g) =ᶠ[𝓝[≠] z] (fun s => D.E v s g) := by
  apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
    (C.meromorphic v g) (D.meromorphic v g)
    KPContinuation.spectralDomain_isConnected.isPreconnected
    (isOpen_lt continuous_const Complex.continuous_re)
    KPContinuation.convergenceHalfPlane_subset_spectralDomain ⟨1, by norm_num⟩ ?_ hz
  intro s hs
  change C.E v s g = D.E v s g
  rw [C.chamber v s hs g, D.chamber v s hs g]

theorem cleared_family_unique (C D : ScalarContinuation R Q)
    (v : R.A.UnitQuotient) (f h : ℂ → Functions R)
    (ρ τ : ℝ) (hρ : 0 < ρ) (hτ : 0 < τ)
    (hf : ∀ g, AnalyticOnNhd ℂ (fun s => f s g) (Metric.ball (0 : ℂ) ρ))
    (hh : ∀ g, AnalyticOnNhd ℂ (fun s => h s g) (Metric.ball (0 : ℂ) τ))
    (hfc : ∀ s ∈ Metric.ball (0 : ℂ) ρ, s ≠ 0 → f s = s • (C.E v s : Functions R))
    (hhc : ∀ s ∈ Metric.ball (0 : ℂ) τ, s ≠ 0 → h s = s • (D.E v s : Functions R))
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) (min ρ τ)) : f s = h s := by
  have hp : 0 < min ρ τ := lt_min hρ hτ
  have hsubρ : Metric.ball (0 : ℂ) (min ρ τ) ⊆ Metric.ball 0 ρ :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hsubτ : Metric.ball (0 : ℂ) (min ρ τ) ⊆ Metric.ball 0 τ :=
    Metric.ball_subset_ball (min_le_right _ _)
  funext g
  have he := scalar_continuation_germ_unique C D v g 0
    (by norm_num [KPContinuation.spectralDomain])
  have heN : (fun z => f z g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => h z g) := by
    filter_upwards [he, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hp),
      self_mem_nhdsWithin] with z he hz hn
    have hleft := congrFun (hfc z (hsubρ hz) hn) g
    have hright := congrFun (hhc z (hsubτ hz) hn) g
    change f z g = z * C.E v z g at hleft
    change h z g = z * D.E v z g at hright
    rw [hleft, hright, he]
  exact ((hf g).mono hsubρ).eqOn_of_preconnected_of_frequently_eq
    ((hh g).mono hsubτ) (convex_ball (0 : ℂ) (min ρ τ)).isPreconnected
    (Metric.mem_ball_self hp) heN.frequently hs

theorem scalar_smooth_cleared_unique {C D : ScalarContinuation R Q}
    {v : R.A.UnitQuotient} (H : ScalarGerm C v) (G : IndividualSmoothGerm D v)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) (min H.radius G.radius)) :
    (H.cleared s : Functions R) = G.cleared s :=
  cleared_family_unique C D v (fun z => H.cleared z) G.cleared
    H.radius G.radius H.radius_pos G.radius_pos H.analytic G.analytic H.clears G.clears s hs

end DedekindZetaZeroFree.KPScalarContinuation

end
