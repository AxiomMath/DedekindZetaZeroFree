module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarGerms.Coefficients
public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothTaylorRepresentation
public import DedekindZetaZeroFree.Analysis.Analytic.SmoothSeries.CoherentTaylorCalculus

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff BigOperators
namespace DedekindZetaZeroFree.SharedSource
open MomentSources EisensteinSmoothGerms KPGlobalResidualConstruction KPGlobalEisensteinData
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CoherentTaylorCalculus renaming series_onBall → series_onBall
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CoherentTaylorCalculus renaming compactSeries → compactSeries
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
variable {C : ScalarContinuation R Q} {v : R.A.UnitQuotient}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem moving_series_scalar
    (N : ℂ → nativeSmoothSpace F R.A.zeta12 R.A.primitive_zeta12)
    (b : ℕ → nativeSmoothSpace F R.A.zeta12 R.A.primitive_zeta12)
    (ρ : ℝ) (hρ : 0 < ρ)
    (ht : SmoothPowerSeriesOn (movingJetMap F R.A.zeta12 R.A.primitive_zeta12) 0 ρ b N)
    (g : Group R) :
    HasFPowerSeriesOnBall (fun s => (N s).val g)
      (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) ((b n).val g))
      0 (ENNReal.ofReal ρ) := by
  let x : archDomain F := ⟨archBase F, ActualDifferentialData.archBase_mem_domain F⟩
  let i : DifferentialCompact (archDomain F) (Group R × Jet F) :=
    ⟨{x}, isCompact_singleton, g, 0, Fin.elim0⟩
  letI : CompactSpace i.compact := isCompact_iff_compactSpace.mp i.isCompact
  let L : C(i.compact, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ ⟨x, rfl⟩
  have hp := L.comp_hasFPowerSeriesOnBall
    (series_onBall (movingJetMap F R.A.zeta12 R.A.primitive_zeta12) ht hρ i)
  have he (f : nativeSmoothSpace F R.A.zeta12 R.A.primitive_zeta12) :
      L (derivativeRestriction (movingJetMap F R.A.zeta12 R.A.primitive_zeta12) i f) = f.val g := by
    change iteratedFDeriv ℝ 0
      (fun y => f.val (g * archChart F R.A.zeta12 R.A.primitive_zeta12 y)) (archBase F) Fin.elim0 = f.val g
    simp only [iteratedFDeriv_zero_apply, KPInterface.ResidueConstruction.Raw.archChart_base, mul_one]
  convert hp using 1
  · funext s
    exact (he (N s)).symm
  · ext n z
    simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      compactSeries, ContinuousMultilinearMap.mkPiRing_apply, map_smul, he]

theorem moving_coefficients_eq_scalar (H : ScalarGerm C v)
    (N : ℂ → nativeSmoothSpace F R.A.zeta12 R.A.primitive_zeta12)
    (b : ℕ → nativeSmoothSpace F R.A.zeta12 R.A.primitive_zeta12)
    (ρ : ℝ) (hρ : 0 < ρ) (hρH : ρ ≤ H.radius)
    (he : ∀ s ∈ Metric.ball (0 : ℂ) ρ, (N s).val = (H.cleared s : Functions R))
    (ht : SmoothPowerSeriesOn (movingJetMap F R.A.zeta12 R.A.primitive_zeta12) 0 ρ b N)
    (n : ℕ) : (b n).val = H.coefficients n := by
  funext g
  have hp := moving_series_scalar N b ρ hρ ht g
  have hsmall : HasFPowerSeriesOnBall (fun s => H.cleared s g)
      (cauchyPowerSeries (fun s => H.cleared s g) 0 (ρ / 2)) 0
      (ENNReal.ofReal (ρ / 2)) := by
    have hh := ((H.analytic g).differentiableOn.mono
      (Metric.closedBall_subset_ball ((half_lt_self hρ).trans_le hρH))).hasFPowerSeriesOnBall
      (R := ⟨ρ / 2, (half_pos hρ).le⟩) (half_pos hρ)
    convert hh using 1
    · rfl
    · exact ENNReal.ofReal_coe_nnreal (p := (⟨ρ / 2, (half_pos hρ).le⟩ : NNReal))
  have hg : (fun s => (N s).val g) =ᶠ[𝓝 (0 : ℂ)] (fun s => H.cleared s g) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hρ] with s hs
    exact congrFun (he s hs) g
  have hsame := hp.hasFPowerSeriesAt.congr hg
  have heq := hsame.eq_formalMultilinearSeries hsmall.hasFPowerSeriesAt
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
  rw [H.coefficients_eq_circle (ρ/2) (half_pos hρ) ((half_lt_self hρ).trans_le hρH) n g]
  simpa only [FormalMultilinearSeries.coeff, ContinuousMultilinearMap.mkPiRing_apply,
    Pi.one_apply, Finset.prod_const_one, one_smul] using hc

theorem scalarGerm_coefficients_smooth_constructed (H : ScalarGerm C v) (n : ℕ) :
    KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 (H.coefficients n) := by
  obtain ⟨ρ, N, b, hρ, hρH, hb, he, ht⟩ := scalarGerm_coherent_moving_series H
  rw [← moving_coefficients_eq_scalar H N b ρ hρ hρH he ht n]
  exact (b n).property

theorem scalarGerm_upgrade_canonical (H : ScalarGerm C v) :
    ∃ G : IndividualSmoothGerm C v,
      G.radius ≤ H.radius ∧ G.cleared = (fun s => (H.cleared s : Functions R)) ∧
      G.coefficients = H.coefficients := by
  obtain ⟨ρ, N, b, hρ, hρH, hb, he, ht⟩ := scalarGerm_coherent_moving_series H
  have hc := moving_coefficients_eq_scalar H N b ρ hρ hρH he ht
  let G : IndividualSmoothGerm C v := {
    radius := ρ
    radius_pos := hρ
    cleared := fun s => H.cleared s
    clears := fun s hs hn => H.clears s (Metric.ball_subset_ball hρH hs) hn
    smooth := fun s hs => (he s hs) ▸ (N s).property
    analytic := fun g => (H.analytic g).mono (Metric.ball_subset_ball hρH)
    coefficients := H.coefficients
    coefficients_smooth := scalarGerm_coefficients_smooth_constructed H
    compact_smooth_taylor := by
      intro g m K hK hKd r hr hrρ ε hε
      obtain ⟨k, hk⟩ := compact_taylor_of_movingJet_powerSeries F R.A.zeta12 R.A.primitive_zeta12
        b N ρ ht g m K hK hKd r hr hrρ ε hε
      refine ⟨k, ?_⟩
      intro M hM s hs x hx
      have hsr : s ∈ Metric.ball (0 : ℂ) ρ := by
        simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hs.trans_lt hrρ
      have hh := hk M hM s hs x hx
      simpa only [he s hsr, hc] using hh }
  exact ⟨G, hρH, rfl, rfl⟩

end DedekindZetaZeroFree.SharedSource

end
