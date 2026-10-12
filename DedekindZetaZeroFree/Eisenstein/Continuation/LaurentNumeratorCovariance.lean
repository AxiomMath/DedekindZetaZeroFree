module

public import DedekindZetaZeroFree.Eisenstein.Residues.ScalarGermUniqueness
public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberRationalInvariance
public import DedekindZetaZeroFree.Eisenstein.Induction.Genuineness

@[expose] public section

noncomputable section
open scoped Topology
open Filter
namespace DedekindZetaZeroFree.KPScalarContinuation
open MomentSources EisensteinSmoothGerms

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
variable {C : ScalarContinuation R Q} {v : R.A.UnitQuotient}

theorem scalar_cleared_covariance (H : ScalarGerm C v) (g h : Group R) (c : ℂ)
    (hch : ∀ z : ℂ, (1 / 3 : ℝ) < z.re →
      KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) z h =
        c * KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) z g)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) H.radius) :
    H.cleared s h = c * H.cleared s g := by
  have hz : (0 : ℂ) ∈ KPContinuation.spectralDomain := by
    norm_num [KPContinuation.spectralDomain]
  have he : (fun z => C.E v z h) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => c * C.E v z g) := by
    apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
      (C.meromorphic v h) ((MeromorphicOn.const c).mul (C.meromorphic v g))
      KPContinuation.spectralDomain_isConnected.isPreconnected
      (isOpen_lt continuous_const Complex.continuous_re)
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ⟨1, by norm_num⟩ ?_ hz
    intro z hz
    change C.E v z h = c * C.E v z g
    rw [C.chamber v z hz h, C.chamber v z hz g]
    exact hch z hz
  have heN : (fun z => H.cleared z h) =ᶠ[𝓝[≠] (0 : ℂ)]
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

theorem scalar_cleared_exterior_spherical (H : ScalarGerm C v)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) H.radius)
    (p : KPFinitePlace F) (hp : p ∉ R.A.Sf)
    (k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (hk : k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12
      R.A.primitive_zeta12 (Sum.inr p)) (g : Group R) :
    H.cleared s (g * KPAdelicCoverRestrictedProduct.scalarQuotient F
      R.A.zeta12 R.A.primitive_zeta12 (KPAdelicCoverRestrictedProduct.localInjection
        F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) k)) = H.cleared s g := by
  simpa only [one_mul] using scalar_cleared_covariance H g _ 1 (by
    intro z _
    unfold KPLiteralRaw.eisenstein
    rw [one_mul]
    apply tsum_congr
    intro a
    rw [← mul_assoc]
    exact Q.exterior_spherical v z p hp k hk _) s hs

end DedekindZetaZeroFree.KPScalarContinuation

end
