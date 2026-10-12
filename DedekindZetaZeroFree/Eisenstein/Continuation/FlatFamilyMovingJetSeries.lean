module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SphericalWordMovingJetSeries
public import DedekindZetaZeroFree.Eisenstein.Continuation.FiniteSourceCircleBounds

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff BigOperators NNReal
open Filter
namespace DedekindZetaZeroFree.SharedSource
open KPGlobalResidualConstruction KPGlobalEisensteinData KPContActualSphericalRightFieldIdentification
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming literal_finite_word_chamber → literal_finite_word_chamber
open _root_.DedekindZetaZeroFree.KPActualReflectionData.CanonicalStageCircle renaming powerSeries_finset_sum → powerSeries_finset_sum
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

include C R P H in

theorem literal_moving_series
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : KPLiteralRaw.IwasawaCompact F ζ hζ K)
    (f : KPLiteralRaw.Flat F ζ hζ K) :
    ∃ (q : ℂ → ℂ) (A : ℂ → KPLiteralRaw.Functions F ζ hζ) (ρ : ℝ),
      AnalyticOnNhd ℂ q KPContinuation.spectralDomain ∧ q 0 = 1 ∧
      (∀ g, MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain) ∧
      (∀ s, (1 / 3 : ℝ) < s.re → ∀ g,
        A s g = q s * KPLiteralRaw.eisenstein F ζ hζ K f s g) ∧
      0 < ρ ∧ Metric.ball (0 : ℂ) ρ ⊆ KPContinuation.spectralDomain ∧
      (∀ s ∈ Metric.ball (0 : ℂ) ρ, q s ≠ 0) ∧
      ∃ N : ℂ → nativeSmoothSpace F ζ hζ,
        (∀ g, AnalyticOnNhd ℂ (fun s => (N s).val g) (Metric.ball (0 : ℂ) ρ)) ∧
        (∀ s ∈ Metric.ball (0 : ℂ) ρ, s ≠ 0 → (N s).val = s • A s) ∧
        ∃ b : ℕ → nativeSmoothSpace F ζ hζ,
          SmoothPowerSeriesOn (movingJetMap F ζ hζ) 0 ρ b N := by
  obtain ⟨n, U, m, v, w, q, B, hq, hq0, ⟨r₀, hr₀, hb₀, hne₀⟩, hB, hrec, hch⟩ :=
    literal_finite_word_chamber F ζ hζ K hK f
  choose A hAc hAm r hr hb N hclear hNa b ht using
    (fun (i : Fin n) (j : Fin (m i)) =>
      sphericalWord_moving_series F ζ hζ C R P H (U i) (v i j) (w i j))
  have hall : ∀ᶠ s in 𝓝 (0 : ℂ),
      s ∈ Metric.ball (0 : ℂ) r₀ ∧ ∀ i j, s ∈ Metric.ball (0 : ℂ) (r i j) := by
    apply Filter.Eventually.and (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₀))
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hr i j))
  obtain ⟨t, ht0, htsub⟩ := Metric.mem_nhds_iff.mp hall
  let ρ := t / 2
  have hρ : 0 < ρ := half_pos ht0
  have hclosed : Metric.closedBall (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) t :=
    Metric.closedBall_subset_ball (half_lt_self ht0)
  have hρr (i : Fin n) (j : Fin (m i)) : ρ ≤ r i j := by
    have hz : (ρ : ℂ) ∈ Metric.ball (0 : ℂ) t := by
      simpa only [Metric.mem_ball, dist_eq_norm, sub_zero, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hρ] using half_lt_self ht0
    have h := Metric.mem_ball.mp ((htsub hz).2 i j)
    have h' : ρ < r i j := by
      simpa only [dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] using h
    exact h'.le
  have hΩ : Metric.closedBall (0 : ℂ) ρ ⊆ KPContinuation.spectralDomain :=
    fun s hs => hb₀ (htsub (hclosed hs)).1
  have hscalar (i : Fin n) (j : Fin (m i)) :
      HasFPowerSeriesOnBall (B i j) (cauchyPowerSeries (B i j) 0 ρ) 0 (ENNReal.ofReal ρ) := by
    have hp := ((hB i j).differentiableOn.mono hΩ).hasFPowerSeriesOnBall
      (R := ⟨ρ, hρ.le⟩) hρ
    convert hp using 1
    · rfl
    · exact ENNReal.ofReal_coe_nnreal (p := (⟨ρ, hρ.le⟩ : NNReal))
  let bb := fun i j => AnalyticScalarMultiplication.coefficientConvolution
    (cauchyPowerSeries (B i j) 0 ρ).coeff (b i j)
  have hprod (i : Fin n) (j : Fin (m i)) :
      SmoothPowerSeriesOn (movingJetMap F ζ hζ) 0 ρ (bb i j)
        (fun s => B i j s • N i j s) :=
    AnalyticScalarMultiplication.powerSeries_smul _ hρ (hscalar i j)
      (SmoothSeriesAlgebra.powerSeries_mono _ (ht i j) (hρr i j))
  let a : ℂ → KPLiteralRaw.Functions F ζ hζ := fun s g => ∑ i, ∑ j, B i j s * A i j s g
  let NN : ℂ → nativeSmoothSpace F ζ hζ := fun s => ∑ i, ∑ j, B i j s • N i j s
  let bbb : ℕ → nativeSmoothSpace F ζ hζ := fun k => ∑ i, ∑ j, bb i j k
  refine ⟨q, a, ρ, hq, hq0, ?_, ?_, hρ, ?_, ?_, NN, ?_, ?_, bbb, ?_⟩
  · intro g s hs
    apply MeromorphicAt.fun_sum
    intro i _
    apply MeromorphicAt.fun_sum
    intro j _
    exact ((hB i j) s hs).meromorphicAt.mul (hAm i j g s hs)
  · intro s hs g
    dsimp [a]
    simp_rw [hAc _ _ s hs]
    exact (hch s hs g).symm
  · exact Metric.ball_subset_closedBall.trans hΩ
  · intro s hs
    exact hne₀ s (htsub (hclosed (Metric.ball_subset_closedBall hs))).1
  · intro g s hs
    dsimp [NN]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.univ.analyticAt_fun_sum
    intro i _
    apply Finset.univ.analyticAt_fun_sum
    intro j _
    exact ((hB i j) s (hΩ (Metric.ball_subset_closedBall hs))).mul
      ((hNa i j g) s ((htsub (hclosed (Metric.ball_subset_closedBall hs))).2 i j))
  · intro s hs hn
    funext g
    dsimp [NN, a]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have he (i : Fin n) (j : Fin (m i)) : (N i j s).val g = s * A i j s g :=
      congrFun (hclear i j s ((htsub (hclosed (Metric.ball_subset_closedBall hs))).2 i j) hn) g
    simp_rw [he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · have hj (i : Fin n) : SmoothPowerSeriesOn (movingJetMap F ζ hζ) 0 ρ
        (fun k => ∑ j, bb i j k) (fun s => ∑ j, B i j s • N i j s) := by
      simpa only [one_smul] using powerSeries_finset_sum (movingJetMap F ζ hζ)
        Finset.univ (fun _ => 1) (bb i) (fun j s => B i j s • N i j s) 0 ρ (fun j _ => hprod i j)
    simpa only [one_smul] using powerSeries_finset_sum (movingJetMap F ζ hζ)
      Finset.univ (fun _ => 1) (fun i k => ∑ j, bb i j k)
      (fun i s => ∑ j, B i j s • N i j s) 0 ρ (fun i _ => hj i)

end DedekindZetaZeroFree.SharedSource

end
