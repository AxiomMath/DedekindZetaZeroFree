module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarAndSmoothGerms
public import DedekindZetaZeroFree.Eisenstein.Continuation.FlatFamilyMovingJetSeries
public import DedekindZetaZeroFree.Eisenstein.Continuation.ClearedResidueReconstruction

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff BigOperators NNReal
open Filter MeasureTheory
namespace DedekindZetaZeroFree.SharedSource
open MomentSources EisensteinSmoothGerms KPGlobalResidualConstruction KPGlobalEisensteinData
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
variable {C : ScalarContinuation R Q} {v : R.A.UnitQuotient}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem literal_moving_series_exists
    (K : Subgroup (Group R))
    (hK : KPLiteralRaw.IwasawaCompact F R.A.zeta12 R.A.primitive_zeta12 K)
    (f : KPLiteralRaw.Flat F R.A.zeta12 R.A.primitive_zeta12 K) :
    ∃ (q : ℂ → ℂ) (A : ℂ → Functions R) (ρ : ℝ),
      AnalyticOnNhd ℂ q KPContinuation.spectralDomain ∧ q 0 = 1 ∧
      (∀ g, MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain) ∧
      (∀ s, (1 / 3 : ℝ) < s.re → ∀ g,
        A s g = q s * KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 K f s g) ∧
      0 < ρ ∧ Metric.ball (0 : ℂ) ρ ⊆ KPContinuation.spectralDomain ∧
      (∀ s ∈ Metric.ball (0 : ℂ) ρ, q s ≠ 0) ∧
      ∃ N : ℂ → nativeSmoothSpace F R.A.zeta12 R.A.primitive_zeta12,
        (∀ g, AnalyticOnNhd ℂ (fun s => (N s).val g) (Metric.ball (0 : ℂ) ρ)) ∧
        (∀ s ∈ Metric.ball (0 : ℂ) ρ, s ≠ 0 → (N s).val = s • A s) ∧
        ∃ b : ℕ → nativeSmoothSpace F R.A.zeta12 R.A.primitive_zeta12,
          SmoothPowerSeriesOn (movingJetMap F R.A.zeta12 R.A.primitive_zeta12) 0 ρ b N := by
  letI : T2Space (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).1
  letI : LocallyCompactSpace (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.1
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  obtain ⟨L⟩ := KPGlobalProductPolarizationCharacter.exists_compatible_local_data
    F R.A.zeta12 R.A.primitive_zeta12
  obtain ⟨M, _⟩ := KPGlobalTorusFiniteStages.compatibleModelData_exists
    F R.A.zeta12 R.A.primitive_zeta12 L
  obtain ⟨μ, _, _, P, ⟨J⟩⟩ := kp_ms_fixed_haar_disintegration
    F R.A.zeta12 R.A.primitive_zeta12 (Measure.haar : Measure (Group R)) inferInstance
  exact literal_moving_series F R.A.zeta12 R.A.primitive_zeta12 M μ P J K hK f

theorem regularized_moving_numerator_pin (H : ScalarGerm C v)
    (q : ℂ → ℂ) (A : ℂ → Functions R)
    (hq : AnalyticOnNhd ℂ q KPContinuation.spectralDomain)
    (hA : ∀ g, MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain)
    (hch : ∀ s, (1 / 3 : ℝ) < s.re → ∀ g,
      A s g = q s * KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) s g)
    (N : ℂ → nativeSmoothSpace F R.A.zeta12 R.A.primitive_zeta12)
    (t : ℝ) (hN : ∀ g, AnalyticOnNhd ℂ (fun s => (N s).val g) (Metric.ball (0 : ℂ) t))
    (hclear : ∀ s ∈ Metric.ball (0 : ℂ) t, s ≠ 0 → (N s).val = s • A s)
    (r : ℝ) (hrt : r ≤ t) (hrH : r ≤ H.radius)
    (hb : Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain) :
    ∀ s ∈ Metric.ball (0 : ℂ) r, (N s).val = q s • (H.cleared s : Functions R) := by
  intro s hs
  funext g
  apply KPMsClearedTruncationL2.ActualRaisingContinuationPin.cleared_identity_on_open
    (hA g) (hq.meromorphicOn.mul (C.meromorphic v g))
    KPContinuation.spectralDomain_isConnected.isPreconnected
    (isOpen_lt continuous_const Complex.continuous_re)
    KPContinuation.convergenceHalfPlane_subset_spectralDomain ⟨1, by norm_num⟩
    (fun z hz => by
      change A z g = q z * C.E v z g
      rw [hch z hz g, C.chamber v z hz g]) Metric.isOpen_ball hb
    ((hN g).continuousOn.mono (Metric.ball_subset_ball hrt))
    ((hq.continuousOn.mono hb).mul
      ((H.analytic g).continuousOn.mono (Metric.ball_subset_ball hrH))) _ _ hs
  · intro z hz hn
    exact congrFun (hclear z (Metric.ball_subset_ball hrt hz) hn) g
  · intro z hz hn
    change q z * H.cleared z g = z * (q z * C.E v z g)
    rw [congrFun (H.clears z (Metric.ball_subset_ball hrH hz) hn) g]
    change q z * (z * C.E v z g) = z * (q z * C.E v z g)
    ring

theorem scalarGerm_coherent_moving_series (H : ScalarGerm C v) :
    ∃ (r : ℝ) (N : ℂ → nativeSmoothSpace F R.A.zeta12 R.A.primitive_zeta12)
      (b : ℕ → nativeSmoothSpace F R.A.zeta12 R.A.primitive_zeta12),
      0 < r ∧ r ≤ H.radius ∧
      Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
      (∀ s ∈ Metric.ball (0 : ℂ) r, (N s).val = (H.cleared s : Functions R)) ∧
      SmoothPowerSeriesOn (movingJetMap F R.A.zeta12 R.A.primitive_zeta12) 0 r b N := by
  obtain ⟨q, A, t, hq, hq0, hA, hch, ht, hb, hne, NN, hNa, hclear, bb, hseries⟩ :=
    literal_moving_series_exists Q.K Q.iwasawa (Q.flat v)
  let r := min (t / 2) H.radius
  have hr : 0 < r := lt_min (half_pos ht) H.radius_pos
  have hrt : r < t := (min_le_left _ _).trans_lt (half_lt_self ht)
  have hrH : r ≤ H.radius := min_le_right _ _
  have hsub : Metric.ball (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) t := Metric.ball_subset_ball hrt.le
  have hclosed : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) t :=
    Metric.closedBall_subset_ball hrt
  have hi : AnalyticOnNhd ℂ (fun s => (q s)⁻¹) (Metric.ball (0 : ℂ) t) :=
    fun s hs => (hq s (hb hs)).inv (hne s hs)
  have hp : HasFPowerSeriesOnBall (fun s => (q s)⁻¹)
      (cauchyPowerSeries (fun s => (q s)⁻¹) 0 r) 0 (ENNReal.ofReal r) := by
    have hh := (hi.differentiableOn.mono hclosed).hasFPowerSeriesOnBall
      (R := ⟨r, hr.le⟩) hr
    convert hh using 1
    · rfl
    · exact ENNReal.ofReal_coe_nnreal (p := (⟨r, hr.le⟩ : NNReal))
  let N : ℂ → nativeSmoothSpace F R.A.zeta12 R.A.primitive_zeta12 :=
    fun s => (q s)⁻¹ • NN s
  let b := AnalyticScalarMultiplication.coefficientConvolution
    (cauchyPowerSeries (fun s => (q s)⁻¹) 0 r).coeff bb
  refine ⟨r, N, b, hr, hrH, hsub.trans hb, ?_, ?_⟩
  · intro s hs
    have he := regularized_moving_numerator_pin H q A hq hA hch NN t hNa hclear
      r hrt.le hrH (hsub.trans hb) s hs
    change (q s)⁻¹ • (NN s).val = (H.cleared s : Functions R)
    rw [he, smul_smul, inv_mul_cancel₀ (hne s (hsub hs)), one_smul]
  · exact AnalyticScalarMultiplication.powerSeries_smul _ hr hp
      (SmoothSeriesAlgebra.powerSeries_mono _ hseries hrt.le)

end DedekindZetaZeroFree.SharedSource

end
