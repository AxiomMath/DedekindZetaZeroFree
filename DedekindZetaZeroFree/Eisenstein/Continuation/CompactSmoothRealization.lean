module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarAndSmoothGerms
public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberRationalInvariance
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

theorem cleared_covariance (C : ScalarContinuation R Q) (v : R.A.UnitQuotient)
    (G : IndividualSmoothGerm C v) (g h : Group R) (c : ℂ)
    (hc : ∀ z : ℂ, (1 / 3 : ℝ) < z.re →
      KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) z h =
        c * KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) z g)
    (s : ℂ) (hs : s ∈ Metric.ball 0 G.radius) :
    G.cleared s h = c * G.cleared s g := by
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
  have heN : (fun z => G.cleared z h) =ᶠ[𝓝[≠] 0]
      (fun z => c * G.cleared z g) := by
    filter_upwards [he, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) G.radius_pos),
      self_mem_nhdsWithin] with z he hz hn
    have hh := congrFun (G.clears z hz hn) h
    have hg := congrFun (G.clears z hz hn) g
    change G.cleared z h = z * C.E v z h at hh
    change G.cleared z g = z * C.E v z g at hg
    rw [hh, hg, he, mul_left_comm]
  exact (G.analytic h).eqOn_of_preconnected_of_frequently_eq
    ((analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => c) _).mul (G.analytic g))
    (convex_ball (0 : ℂ) G.radius).isPreconnected
    (Metric.mem_ball_self G.radius_pos) heN.frequently hs

theorem cleared_level (C : ScalarContinuation R Q) (v : R.A.UnitQuotient)
    (G : IndividualSmoothGerm C v) (s : ℂ) (hs : s ∈ Metric.ball 0 G.radius)
    (g u : Group R)
    (hu : u ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 Q.level) :
    G.cleared s (g * u) = G.cleared s g := by
  simpa only [one_mul] using cleared_covariance C v G g (g * u) 1 (by
    intro z _
    unfold KPLiteralRaw.eisenstein
    rw [one_mul]
    apply tsum_congr
    intro a
    rw [← mul_assoc]
    exact Q.common_level v z _ u hu) s hs

theorem cleared_rational (C : ScalarContinuation R Q) (v : R.A.UnitQuotient)
    (G : IndividualSmoothGerm C v) (s : ℂ) (hs : s ∈ Metric.ball 0 G.radius)
    (a : Matrix.ProjGenLinGroup (Fin 2) F) (g : Group R) :
    G.cleared s (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 a * g) =
      G.cleared s g := by
  simpa only [one_mul] using cleared_covariance C v G g _ 1 (by
    intro z _
    simpa only [one_mul] using literal_rational_invariant (Q.flat v) z a g) s hs

theorem cleared_genuine (C : ScalarContinuation R Q) (v : R.A.UnitQuotient)
    (G : IndividualSmoothGerm C v) (s : ℂ) (hs : s ∈ Metric.ball 0 G.radius)
    (ε : rootsOfUnity 3 F) (g : Group R) :
    G.cleared s (KPAdelicCoverRestrictedProduct.pglCentralInjection
      F R.A.zeta12 R.A.primitive_zeta12 ε * g) =
      (KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12 ε : ℂ) * G.cleared s g := by
  apply cleared_covariance C v G g _ _ ?_ s hs
  intro z hz
  exact KPLiteralExceptionalResidue.ResidueAutomorphy.eisenstein_genuine
    F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) z hz ε g

def assemble (C : ScalarContinuation R Q) (G : ∀ v, IndividualSmoothGerm C v) :
    Realization R Q := by
  let ρ := Classical.choose (common_radius G)
  have hρ := (Classical.choose_spec (common_radius G)).1
  have hdom := (Classical.choose_spec (common_radius G)).2.1
  have hb := (Classical.choose_spec (common_radius G)).2.2
  have hsub (v : R.A.UnitQuotient) : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball 0 (G v).radius :=
    Metric.ball_subset_ball (hb v)
  exact {
    E := C.E
    meromorphic := C.meromorphic
    chamber := C.chamber
    radius := ρ
    radius_pos := hρ
    disc_domain := hdom
    cleared := fun v => (G v).cleared
    clears := fun v s hs hn => (G v).clears s (hsub v hs) hn
    smooth := fun v s hs => (G v).smooth s (hsub v hs)
    common_cleared_level := fun v s hs g u hu => cleared_level C v (G v) s (hsub v hs) g u hu
    analytic := fun v g => ((G v).analytic g).mono (hsub v)
    coefficients := fun v => (G v).coefficients
    coefficients_smooth := fun v => (G v).coefficients_smooth
    compact_smooth_taylor := fun v g m K hK hKd r hr hrρ =>
      (G v).compact_smooth_taylor g m K hK hKd r hr (hrρ.trans_le (hb v))
    automorphic := fun v => ⟨(G v).smooth 0 (Metric.mem_ball_self (G v).radius_pos),
      cleared_rational C v (G v) 0 (Metric.mem_ball_self (G v).radius_pos),
      cleared_genuine C v (G v) 0 (Metric.mem_ball_self (G v).radius_pos)⟩ }
end DedekindZetaZeroFree.EisensteinSmoothGerms

end
