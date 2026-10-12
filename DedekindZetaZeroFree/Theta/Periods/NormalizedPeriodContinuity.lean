module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactWordNumerator

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NormalizedPeriodContinuity
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator renaming finite_literal_compact_numerator → finite_literal_compact_numerator
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.QuotientUpperOrbit renaming upper_fiber_eq → upper_fiber_eq
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.QuotientUpperOrbit renaming compact_additive_representatives → compact_additive_representatives
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.CompactPeriodDescent renaming extension_of_compact_period → extension_of_compact_period
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.FiniteCompactAssembly renaming extension_evaluates_native_pullback → extension_evaluates_native_pullback
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.GlobalScalarPin renaming germ_eq_of_open_agreement → germ_eq_of_open_agreement
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 120000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem clearing_disk_rational
    (K : Subgroup (G F ζ hζ))
    (E cleared : Flat F ζ hζ K → ℂ → Functions F ζ hζ)
    (hGerm : ExceptionalGerm F ζ hζ K E cleared) (f : Flat F ζ hζ K) :
    ∃ r : ℝ, 0 < r ∧ ∀ s ∈ Metric.ball (0 : ℂ) r,
      ∀ (γ : Matrix.ProjGenLinGroup (Fin 2) F) g,
        cleared f s (rationalLift F ζ hζ γ * g) = cleared f s g := by
  obtain ⟨U, r, ho, hc, hch, hr, hb, hm, he, ha⟩ := hGerm.2 f
  refine ⟨r, hr, ?_⟩
  intro s hs γ g
  have hE := germ_eq_of_open_agreement
    (fun z => E f z (rationalLift F ζ hζ γ * g)) (fun z => E f z g)
    U {z : ℂ | (1 : ℝ) / 3 < z.re} hc.isPreconnected
    (isOpen_lt continuous_const Complex.continuous_re) (by refine ⟨1, ?_⟩; norm_num)
    hch (hm _) (hm _) (fun z hz => by
      dsimp only
      rw [hGerm.1 f z hz _, hGerm.1 f z hz _]
      exact KPLiteralExceptionalResidue.ResidueAutomorphy.eisenstein_rational F ζ hζ K f z hz γ g)
    0 (hb (Metric.mem_ball_self hr))
  have hnear : (fun z => cleared f z (rationalLift F ζ hζ γ * g)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => cleared f z g) := by
    filter_upwards [hE, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
      self_mem_nhdsWithin] with z hz hzball hz0
    rw [he z hzball hz0]
    simp only [Pi.smul_apply, smul_eq_mul, hz]
  have hnear' := ((ha _ 0 (Metric.mem_ball_self hr)).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (ha _ 0 (Metric.mem_ball_self hr)).continuousAt).mp hnear
  exact (ha _).eqOn_of_preconnected_of_eventuallyEq (ha _)
    (convex_ball (0 : ℂ) r).isPreconnected (Metric.mem_ball_self hr) hnear' hs

end DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NormalizedPeriodContinuity

end
