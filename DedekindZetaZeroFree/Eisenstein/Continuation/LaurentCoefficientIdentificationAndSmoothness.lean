module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ArchimedeanSmoothGerm

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology ContDiff BigOperators
open Filter
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource
open MomentSources
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
variable {C : ScalarContinuation R Q} {v : R.A.UnitQuotient}

theorem native_coefficients_eq (H : ScalarGerm C v)
    (f : ℂ → ArchSeries.space F R.A.zeta12 R.A.primitive_zeta12)
    (a : ℕ → ArchSeries.space F R.A.zeta12 R.A.primitive_zeta12)
    (t r : ℝ) (ht : 0 < t) (hr : 0 < r)
    (ha : KPGlobalEisensteinData.SmoothPowerSeriesOn
      (ArchSeries.jets F R.A.zeta12 R.A.primitive_zeta12) 0 t a f)
    (he : ∀ s ∈ Metric.ball (0 : ℂ) r, (f s).val = (H.cleared s : Functions R)) :
    ∀ n, (a n).val = H.coefficients n := by
  intro n
  funext g
  have hp := (ArchSeries.powerSeries_eval F R.A.zeta12 R.A.primitive_zeta12 ht ha g).hasFPowerSeriesAt
  have hc := ((H.analytic g).differentiableOn.mono
    (Metric.closedBall_subset_ball (by linarith [H.radius_pos] : H.radius/2 < H.radius))).hasFPowerSeriesOnBall
      (R := ⟨H.radius/2, (half_pos H.radius_pos).le⟩) (half_pos H.radius_pos)
  have hg : (fun s => (f s).val g) =ᶠ[𝓝 (0 : ℂ)] (fun s => H.cleared s g) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with s hs
    exact congrFun (he s hs) g
  have hq := hp.eq_formalMultilinearSeries_of_eventually hc.hasFPowerSeriesAt hg
  have hn := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => 1)) hq
  simp only [ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const_one, one_smul] at hn
  change (a n).val g = (cauchyPowerSeries (fun z => H.cleared z g) 0 (H.radius/2) n) (fun _ => 1)
  convert hn using 1
  congr 2

theorem selected_smooth_upgrade (H : ScalarGerm C v) :
    ∃ G : IndividualSmoothGerm C v,
      G.radius ≤ H.radius ∧ ∀ s ∈ Metric.ball (0 : ℂ) G.radius,
        G.cleared s = (H.cleared s : Functions R) := by
  obtain ⟨f,r,hr,hrH,hf,he⟩ := constructed_arch_germ H
  obtain ⟨t,ht,htB,a,ha⟩ := hf 0 (Metric.mem_ball_self hr)
  have hcoeff := native_coefficients_eq H f a t r ht hr ha he
  let ρ := min r t
  have hρ : 0 < ρ := lt_min hr ht
  have hρr : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball 0 r := Metric.ball_subset_ball (min_le_left _ _)
  have hρH : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball 0 H.radius :=
    hρr.trans (Metric.ball_subset_ball hrH)
  let G : IndividualSmoothGerm C v := {
    radius := ρ
    radius_pos := hρ
    cleared := fun s => H.cleared s
    clears := fun s hs hn => H.clears s (hρH hs) hn
    smooth := by
      intro s hs
      refine ⟨(H.cleared s).continuous, ?_, Q.level, ?_⟩
      · rw [← he s (hρr hs)]
        exact (f s).property
      · exact fun g u hu => scalarGerm_level H (hρH hs) g u hu
    analytic := fun g => (H.analytic g).mono hρH
    coefficients := fun n => (a n).val
    coefficients_smooth := by
      intro n
      have hl : ∀ g u, u ∈ KPGlobalTorusFunctionData.globalLevel
          F R.A.zeta12 R.A.primitive_zeta12 Q.level → (a n).val (g*u) = (a n).val g := by
        rw [hcoeff n]
        exact fun g u hu => H.coefficients_level n g u hu
      exact ⟨finite_level_arch_continuous F R.A.zeta12 R.A.primitive_zeta12
        Q.level (a n).val (a n).property hl, (a n).property, Q.level, hl⟩
    compact_smooth_taylor := by
      intro g m K hK hKd b hb hbρ ε hε
      obtain ⟨N,hN⟩ := ArchSeries.powerSeries_compact_jets F R.A.zeta12
        R.A.primitive_zeta12 ha g m K hK hKd b hb.le
        (hbρ.trans_le (min_le_right _ _)) ε hε
      refine ⟨N, ?_⟩
      intro M hM s hs x hx
      have hsR : s ∈ Metric.ball (0 : ℂ) r := by
        apply Metric.mem_ball.mpr
        simpa only [dist_zero_right] using hs.trans_lt (hbρ.trans_le (min_le_left _ _))
      have hh := hN M hM s hs x hx
      rw [he s hsR] at hh
      exact hh }
  exact ⟨G, (min_le_left _ _).trans hrH, fun _ _ => rfl⟩

end DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource

end
