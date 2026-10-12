module

public import DedekindZetaZeroFree.Eisenstein.Residues.Spherical.LaplacianEigenCenters
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.SphericalChamberCasimir
public import DedekindZetaZeroFree.Eisenstein.Continuation.ClearedResidueReconstruction

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
open Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualSphericalGeometry
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming native_second_word → native_second_word
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming nativeIndex → nativeIndex
open _root_.DedekindZetaZeroFree.KPContinuation.NativeWordCompactHolomorphy renaming actualRightWord_compact_holomorphy → actualRightWord_compact_holomorphy
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming scalar_analytic_of_right_holomorphic → scalar_analytic_of_right_holomorphic
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming word_smul → word_smul
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local notation "G" => KPGlobalTorusFunctionData.G F ζ hζ

theorem casimir_smul (c : ℂ) (f : G → ℂ) (g : G) :
    KPMsGreenFlux.casimir F ζ hζ (c • f) g =
      c * KPMsGreenFlux.casimir F ζ hζ f g := by
  unfold KPMsGreenFlux.casimir
  simp_rw [← native_second_word, word_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  ring

theorem casimir_analytic {O : Set ℂ} {A : ℂ → G → ℂ}
    (hA : ∀ w g, AnalyticOnNhd ℂ (fun s => actualRightWord F ζ hζ w (A s) g) O)
    (g : G) : AnalyticOnNhd ℂ (fun s => KPMsGreenFlux.casimir F ζ hζ (A s) g) O := by
  unfold KPMsGreenFlux.casimir
  simp_rw [← native_second_word]
  apply Finset.analyticOnNhd_fun_sum
  intro w hw
  exact analyticOnNhd_const.mul (((hA _ g).sub (hA _ g)).add
    (analyticOnNhd_const.mul ((((hA _ g).add (hA _ g)).sub (hA _ g)).sub (hA _ g))))

theorem casimir_meromorphic {O : Set ℂ} {A : ℂ → G → ℂ}
    (hA : ∀ w g, MeromorphicOn (fun s => actualRightWord F ζ hζ w (A s) g) O)
    (g : G) : MeromorphicOn (fun s => KPMsGreenFlux.casimir F ζ hζ (A s) g) O := by
  unfold KPMsGreenFlux.casimir
  simp_rw [← native_second_word]
  apply MeromorphicOn.fun_sum
  intro w hw
  exact analyticOnNhd_const.meromorphicOn.mul (((hA _ g).sub (hA _ g)).add
    (analyticOnNhd_const.meromorphicOn.mul ((((hA _ g).add (hA _ g)).sub (hA _ g)).sub (hA _ g))))

variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U

theorem actual_word_analytic {O : Set ℂ} (hO : IsOpen O) (A : ℂ → G → ℂ)
    (hA : ∀ D : GroupChart F ζ hζ level R P H,
      KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields
        (fun s x => A s (D.groupLift x)) O) (w) (g) :
    AnalyticOnNhd ℂ (fun s => actualRightWord F ζ hζ w (A s) g) O := by
  apply scalar_analytic_of_right_holomorphic F ζ hζ C R P H U _ O hO
  intro D
  exact actualRightWord_compact_holomorphy D _ _ (hA D) w

theorem actual_word_meromorphic (A : ℂ → G → ℂ)
    (hlocal : ∀ c ∈ KPContinuation.spectralDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
      ∃ N : ℂ → G → ℂ,
        (∀ D : GroupChart F ζ hζ level R P H,
          KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields
            (fun s x => N s (D.groupLift x)) (Metric.ball c r)) ∧
        (∀ s ∈ Metric.ball c r, s ≠ c → N s = (s-c) • A s))
    (w) (g) : MeromorphicOn (fun s => actualRightWord F ζ hζ w (A s) g)
      KPContinuation.spectralDomain := by
  intro c hc
  obtain ⟨r, hr, hb, N, hN, he⟩ := hlocal c hc
  have han := actual_word_analytic F ζ hζ C R P H U Metric.isOpen_ball N hN w g
  have hn := (han c (Metric.mem_ball_self hr)).meromorphicAt
  have hq : MeromorphicAt (fun s => actualRightWord F ζ hζ w (N s) g / (s-c)) c := hn.div ((analyticAt_id.sub analyticAt_const).meromorphicAt)
  apply hq.congr
  filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)),
    self_mem_nhdsWithin] with s hs hne
  have hsne : s ≠ c := by simpa using hne
  rw [he s hs hsne, word_smul]
  change (s-c) * actualRightWord F ζ hζ w (A s) g / (s-c) = _
  exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hsne)

theorem spherical_numerator_casimir
    (U₀ : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U₀)
    (A : ℂ → G → ℂ)
    (hA : ∀ w g, MeromorphicOn (fun s => actualRightWord F ζ hζ w (A s) g)
      KPContinuation.spectralDomain)
    (hch : ∀ s, (1/3 : ℝ) < s.re → A s = fun h =>
      ∑' q : KPChamberBruhatTwoCells.RationalQuotient F,
        (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
          (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out q) * h))
    (c : ℂ) (hc : c ∈ KPContinuation.spectralDomain)
    (r : ℝ) (hr : 0 < r)
    (N : ℂ → G → ℂ)
    (hN : ∀ w g, AnalyticOnNhd ℂ (fun s => actualRightWord F ζ hζ w (N s) g)
      (Metric.ball c r))
    (he : ∀ s ∈ Metric.ball c r, s ≠ c → N s = (s-c) • A s)
    (g : G) : KPMsGreenFlux.casimir F ζ hζ (N c) g =
      KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) c * N c g := by
  let lam := KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ)
  have hlam : AnalyticOnNhd ℂ lam Set.univ := by
    intro s hs
    change AnalyticAt ℂ (fun z : ℂ => (KPCuspLogShape.dimension F : ℂ) * (1 - (1/3 + 2*z)^2)) s
    fun_prop
  have hbase : MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain := hA [] g
  have heq := KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
    (casimir_meromorphic F ζ hζ hA g)
    ((hlam.mono (Set.subset_univ _)).meromorphicOn.mul hbase)
    KPContinuation.spectralDomain_isConnected.isPreconnected
    (isOpen_lt continuous_const Complex.continuous_re)
    KPContinuation.convergenceHalfPlane_subset_spectralDomain
    (show {s : ℂ | (1/3 : ℝ) < s.re}.Nonempty from ⟨1, by norm_num⟩)
    (show Set.EqOn (fun s => KPMsGreenFlux.casimir F ζ hζ (A s) g)
      (fun s => lam s * A s g) {s : ℂ | (1/3 : ℝ) < s.re} from by
        intro s hs
        change KPMsGreenFlux.casimir F ζ hζ (A s) g = lam s * A s g
        rw [hch s hs]
        exact actual_spherical_chamber_casimir F ζ hζ U₀ v s hs g) hc
  have hn : AnalyticOnNhd ℂ (fun s => N s g) (Metric.ball c r) := hN [] g
  have hl := ((casimir_analytic F ζ hζ hN g).continuousOn.continuousAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).tendsto
  have hrhs := (((hlam.mono (Set.subset_univ _)).mul hn).continuousOn.continuousAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).tendsto
  have hev : (fun s => KPMsGreenFlux.casimir F ζ hζ (N s) g)
      =ᶠ[𝓝[≠] c] (fun s => lam s * N s g) := by
    filter_upwards [heq, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))]
      with s hs hne hb
    have hsne : s ≠ c := by simpa using hne
    rw [he s hb hsne, casimir_smul F ζ hζ, hs]
    change (s-c) * (lam s * A s g) = lam s * ((s-c) * A s g)
    ring
  exact tendsto_nhds_unique ((hl.mono_left nhdsWithin_le_nhds).congr' hev)
    (hrhs.mono_left nhdsWithin_le_nhds)

end DedekindZetaZeroFree.FourierContinuation.ResidualSphericalGeometry

end
