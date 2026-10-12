module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarChamberSeries
public import DedekindZetaZeroFree.Analysis.Meromorphic.SimplePoleOrderAndPrincipalPart

@[expose] public section

noncomputable section
open Filter
open scoped Topology
namespace DedekindZetaZeroFree.ResidueContinuity
open MomentSources ThetaExpansion
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R} {B : JointRootAlignedSources R N}
variable {v : R.A.UnitQuotient}

theorem selected_order_of_reconstruction_numerator (D : SelectedScalarBranch R B v)
    (Q : ℂ → ℂ) (A : ℂ → Functions R)
    (hQ : AnalyticOnNhd ℂ Q KPContinuation.spectralDomain) (hQ0 : Q 0 = 1)
    (hA : ∀ g, MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain)
    (hch : ∀ s, (1 / 3 : ℝ) < s.re → ∀ g,
      A s g = Q s * KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
        B.sources.K (B.sources.flat v) s g)
    (hN : ∀ g, ∃ N : ℂ → ℂ, AnalyticAt ℂ N 0 ∧
      N =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => s * A s g)) :
    ∀ g, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun s => D.E s g) 0 := by
  have hc : (0 : ℂ) ∈ KPContinuation.spectralDomain := by
    norm_num [KPContinuation.spectralDomain]
  have hqne : Q 0 ≠ 0 := by rw [hQ0]; exact one_ne_zero
  intro g
  have he : (fun s => Q s * D.E s g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => A s g) := by
    apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
      (hQ.meromorphicOn.mul (D.normal g).meromorphicOn) (hA g)
      KPContinuation.spectralDomain_isConnected.isPreconnected
      (isOpen_lt continuous_const Complex.continuous_re)
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ⟨1, by norm_num⟩ _ hc
    intro s hs
    change Q s * D.E s g = A s g
    rw [D.chamber s hs g, hch s hs g]
  obtain ⟨N, hNa, hNe⟩ := hN g
  have hdiv : AnalyticAt ℂ (fun s => N s / Q s) 0 := hNa.div (hQ 0 hc) hqne
  apply order_ge_neg_one_of_clearing (D.normal g hc).meromorphicAt hdiv
  have hnear : ∀ᶠ s in 𝓝 (0 : ℂ), Q s ≠ 0 :=
    (hQ 0 hc).continuousAt.eventually (isOpen_ne.mem_nhds hqne)
  filter_upwards [he, hNe, hnear.filter_mono nhdsWithin_le_nhds] with s hs hns hqs
  simp only [sub_zero, smul_eq_mul]
  rw [hns, ← hs]
  field_simp

end DedekindZetaZeroFree.ResidueContinuity

end
