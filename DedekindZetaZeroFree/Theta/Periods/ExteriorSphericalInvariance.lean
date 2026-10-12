module

public import DedekindZetaZeroFree.Theta.Periods.CompactDigitContinuity

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.DigitMasks
open MomentSources NumberField MeasureTheory Filter
open scoped Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem cleared_right_fixed {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (k : Group R)
    (hk : ∀ s g, (Q.flat v).val s (g * k) = (Q.flat v).val s g)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) T.radius) (g : Group R) :
    T.cleared v s (g * k) = T.cleared v s g := by
  have hopen : IsOpen {z : ℂ | (1 : ℝ) / 3 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h1 : (1 : ℂ) ∈ {z : ℂ | (1 : ℝ) / 3 < z.re} := by norm_num
  have hnear : (fun z => T.E v z (g * k)) =ᶠ[𝓝[≠] (1 : ℂ)] (fun z => T.E v z g) := by
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds h1)] with z hz
    rw [T.chamber v z hz (g * k), T.chamber v z hz g]
    unfold KPLiteralRaw.eisenstein
    apply tsum_congr
    intro c
    rw [← mul_assoc, hk]
  have htop : meromorphicOrderAt (fun z => T.E v z (g * k) - T.E v z g) 1 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [hnear] with z hz
    exact sub_eq_zero.mpr hz
  have hz : (0 : ℂ) ∈ Metric.ball (0 : ℂ) T.radius := Metric.mem_ball_self T.radius_pos
  have htop0 := ((T.meromorphic v (g * k)).sub (T.meromorphic v g)).meromorphicOrderAt_eq_top_of_isPreconnected
    KPContinuation.spectralDomain_isConnected.isPreconnected
    (KPContinuation.convergenceHalfPlane_subset_spectralDomain h1) (T.disc_domain hz) htop
  have hcleared : (fun z => T.cleared v z (g * k)) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => T.cleared v z g) := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp htop0,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) T.radius_pos), self_mem_nhdsWithin]
      with z he hz hz0
    have ha := congrFun (T.clears v z hz hz0) (g * k)
    have hb := congrFun (T.clears v z hz hz0) g
    simp only [Pi.smul_apply, smul_eq_mul] at ha hb
    change T.E v z (g * k) - T.E v z g = 0 at he
    rw [ha, hb, sub_eq_zero.mp he]
  have ha := T.analytic v (g * k)
  have hb := T.analytic v g
  have he := ((ha 0 hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hb 0 hz).continuousAt).mp hcleared
  exact ha.eqOn_of_preconnected_of_eventuallyEq hb (convex_ball (0 : ℂ) T.radius).isPreconnected
    hz he hs

theorem theta_exterior_spherical {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (p : KPFinitePlace F) (hp : p ∉ R.A.Sf)
    (k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (hk : k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (g : Group R) :
    T.theta v (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) k)) =
      T.theta v g :=
  cleared_right_fixed R T v _ (fun s g => Q.exterior_spherical v s p hp k hk g)
    0 (Metric.mem_ball_self T.radius_pos) g

end DedekindZetaZeroFree.DigitMasks

end
