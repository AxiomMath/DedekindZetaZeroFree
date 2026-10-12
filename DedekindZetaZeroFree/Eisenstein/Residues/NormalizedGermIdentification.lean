module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarAndSmoothGerms
public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarRegularization

@[expose] public section

noncomputable section
open scoped Topology Classical
open Filter
namespace DedekindZetaZeroFree.SharedSource
open MomentSources EisensteinSmoothGerms
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}

theorem scalar_residue_eq_literal_ancestor
    (E N : KPLiteralRaw.Flat F R.A.zeta12 R.A.primitive_zeta12 Q.K → ℂ → Functions R)
    (hE : KPLiteralRaw.ExceptionalGerm F R.A.zeta12 R.A.primitive_zeta12 Q.K E N)
    (hNF : ∀ f g, MeromorphicNFOn (fun s => E f s g) KPContinuation.spectralDomain)
    {C : ScalarContinuation R Q} {v : R.A.UnitQuotient} (H : ScalarGerm C v) :
    (H.cleared 0 : Functions R) = N (Q.flat v) 0 := by
  obtain ⟨U, r, hUo, hUc, hUch, hr, hb, hm, hclear, ha⟩ := hE.2 (Q.flat v)
  have hC0 : (0 : ℂ) ∈ KPContinuation.spectralDomain := by
    norm_num [KPContinuation.spectralDomain]
  have he (g : Group R) : (fun s => C.E v s g) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun s => E (Q.flat v) s g) := by
    apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
      (C.meromorphic v g) ((hNF (Q.flat v) g).meromorphicOn)
      KPContinuation.spectralDomain_isConnected.isPreconnected
      (isOpen_lt continuous_const Complex.continuous_re)
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ⟨1, by norm_num⟩ ?_ hC0
    intro s hs
    change C.E v s g = E (Q.flat v) s g
    rw [C.chamber v s hs g, hE.1 (Q.flat v) s hs g]
  funext g
  have hnear : (fun s => H.cleared s g) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun s => N (Q.flat v) s g) := by
    filter_upwards [he g,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) H.radius_pos),
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
      self_mem_nhdsWithin] with s hs hsH hsr hs0
    rw [congrFun (H.clears s hsH hs0) g, congrFun (hclear s hsr hs0) g]
    change s * C.E v s g = s * E (Q.flat v) s g
    rw [hs]
  exact tendsto_nhds_unique
    (((H.analytic g 0 (Metric.mem_ball_self H.radius_pos)).continuousAt.tendsto
      |>.mono_left nhdsWithin_le_nhds).congr' hnear)
    ((ha g 0 (Metric.mem_ball_self hr)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

end DedekindZetaZeroFree.SharedSource

end
