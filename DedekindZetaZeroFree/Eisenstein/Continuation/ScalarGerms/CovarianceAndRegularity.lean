module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberRationalInvariance
public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarAndSmoothGerms
public import DedekindZetaZeroFree.Eisenstein.Induction.Genuineness

@[expose] public section

noncomputable section
open scoped Topology
open Filter
namespace DedekindZetaZeroFree.EisensteinSmoothGerms
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}

theorem scalarGerm_covariance {C : ScalarContinuation R Q}
    {v : R.A.UnitQuotient} (H : ScalarGerm C v) (g h : Group R) (c : ℂ)
    (hc : ∀ z : ℂ, (1 / 3 : ℝ) < z.re →
      KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) z h =
        c * KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) z g)
    {s : ℂ} (hs : s ∈ Metric.ball 0 H.radius) :
    H.cleared s h = c * H.cleared s g := by
  have hz : (0 : ℂ) ∈ KPContinuation.spectralDomain := by
    norm_num [KPContinuation.spectralDomain]
  have he : (fun z => C.E v z h) =ᶠ[𝓝[≠] 0] (fun z => c * C.E v z g) := by
    apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
      (C.meromorphic v h) ((MeromorphicOn.const c).mul (C.meromorphic v g))
      KPContinuation.spectralDomain_isConnected.isPreconnected
      (isOpen_lt continuous_const Complex.continuous_re)
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ⟨1, by norm_num⟩ ?_ hz
    intro z hz
    change C.E v z h = c * C.E v z g
    rw [C.chamber v z hz h, C.chamber v z hz g]
    exact hc z hz
  have heN : (fun z => H.cleared z h) =ᶠ[𝓝[≠] 0]
      (fun z => c * H.cleared z g) := by
    filter_upwards [he, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) H.radius_pos),
      self_mem_nhdsWithin] with z he hz hn
    have hh := congrFun (H.clears z hz hn) h
    have hg := congrFun (H.clears z hz hn) g
    change H.cleared z h = z * C.E v z h at hh
    change H.cleared z g = z * C.E v z g at hg
    rw [hh, hg, he, mul_left_comm]
  exact (H.analytic h).eqOn_of_preconnected_of_frequently_eq
    ((analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => c) _).mul (H.analytic g))
    (convex_ball (0 : ℂ) H.radius).isPreconnected
    (Metric.mem_ball_self H.radius_pos) heN.frequently hs

theorem scalarGerm_level {C : ScalarContinuation R Q}
    {v : R.A.UnitQuotient} (H : ScalarGerm C v)
    {s : ℂ} (hs : s ∈ Metric.ball 0 H.radius) (g u : Group R)
    (hu : u ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 Q.level) :
    H.cleared s (g * u) = H.cleared s g := by
  simpa only [one_mul] using scalarGerm_covariance H g (g * u) 1 (by
    intro z _
    unfold KPLiteralRaw.eisenstein
    rw [one_mul]
    apply tsum_congr
    intro a
    rw [← mul_assoc]
    exact Q.common_level v z _ u hu) hs

end DedekindZetaZeroFree.EisensteinSmoothGerms

end
