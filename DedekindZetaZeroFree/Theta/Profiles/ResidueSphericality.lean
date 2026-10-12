module

public import DedekindZetaZeroFree.Theta.Periods.IntegrabilityAndResidueLimits

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
variable {Q : AdmissibleFlatSources R}

theorem cleared_eq_of_chamber_eq (T : Realization R Q) (v : R.A.UnitQuotient)
    (a b : Group R)
    (hab : ∀ s : ℂ, (1 / 3 : ℝ) < s.re → T.E v s a = T.E v s b)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) T.radius) :
    T.cleared v s a = T.cleared v s b := by
  have hopen : IsOpen {z : ℂ | (1 : ℝ) / 3 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h1 : (1 : ℂ) ∈ {z : ℂ | (1 : ℝ) / 3 < z.re} := by norm_num
  have htop : meromorphicOrderAt (fun z => T.E v z a - T.E v z b) 1 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds h1)] with z hz
    exact sub_eq_zero.mpr (hab z hz)
  have hz : (0 : ℂ) ∈ Metric.ball (0 : ℂ) T.radius := Metric.mem_ball_self T.radius_pos
  have htop0 := ((T.meromorphic v a).sub (T.meromorphic v b)).meromorphicOrderAt_eq_top_of_isPreconnected
    KPContinuation.spectralDomain_isConnected.isPreconnected
    (KPContinuation.convergenceHalfPlane_subset_spectralDomain h1) (T.disc_domain hz) htop
  have hcleared : (fun z => T.cleared v z a) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => T.cleared v z b) := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp htop0,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) T.radius_pos), self_mem_nhdsWithin]
      with z he hz hz0
    have ha := congrFun (T.clears v z hz hz0) a
    have hb := congrFun (T.clears v z hz hz0) b
    simp only [Pi.smul_apply, smul_eq_mul] at ha hb
    change T.E v z a - T.E v z b = 0 at he
    rw [ha, hb, sub_eq_zero.mp he]
  have ha := T.analytic v a
  have hb := T.analytic v b
  have he := ((ha 0 hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hb 0 hz).continuousAt).mp hcleared
  exact ha.eqOn_of_preconnected_of_eventuallyEq hb (convex_ball (0 : ℂ) T.radius).isPreconnected
    hz he hs

theorem cleared_exterior_spherical (T : Realization R Q) (v : R.A.UnitQuotient)
    (p : KPFinitePlace F) (hp : p ∉ R.A.Sf)
    (k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (hk : k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) T.radius) (g : Group R) :
    T.cleared v s (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) k)) =
        T.cleared v s g := by
  apply cleared_eq_of_chamber_eq T v _ g _ s hs
  intro z hz
  rw [T.chamber v z hz, T.chamber v z hz]
  unfold KPLiteralRaw.eisenstein
  apply tsum_congr
  intro c
  rw [← mul_assoc]
  exact Q.exterior_spherical v z p hp k hk _

theorem theta_exterior_spherical (T : Realization R Q) (v : R.A.UnitQuotient)
    (p : KPFinitePlace F) (hp : p ∉ R.A.Sf)
    (k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (hk : k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (g : Group R) :
    T.theta v (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) k)) =
        T.theta v g :=
  cleared_exterior_spherical T v p hp k hk 0 (Metric.mem_ball_self T.radius_pos) g

end DedekindZetaZeroFree.FourierContinuation

end
