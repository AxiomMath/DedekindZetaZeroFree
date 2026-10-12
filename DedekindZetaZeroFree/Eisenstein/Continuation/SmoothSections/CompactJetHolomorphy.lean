module

public import DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData

@[expose] public section

noncomputable section
open scoped Topology NNReal
open Filter
set_option backward.isDefEq.respectTransparency false

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.FiniteStageAnalytic

variable {G₀ V J S : Type*} [TopologicalSpace G₀] [AddCommGroup V] [Module ℂ V]
  [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]

 def compactJet (D : J → V →ₗ[ℂ] C(G₀, ℂ))
    (ι : S →ₗ[ℂ] V) (i : KPGlobalEisensteinData.DifferentialCompact G₀ J) :
    S →ₗ[ℂ] C(i.compact, ℂ) where
  toFun v := (D i.operator (ι v)).restrict i.compact
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

private theorem compactJet_bound (D : J → V →ₗ[ℂ] C(G₀, ℂ))
    (ι : S →ₗ[ℂ] V) (i : KPGlobalEisensteinData.DifferentialCompact G₀ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, KPGlobalEisensteinData.smoothSeminorm D i (ι v) ≤ C * ‖v‖ := by
  letI : CompactSpace i.compact := isCompact_iff_compactSpace.mp i.isCompact
  let T := (compactJet D ι i).toContinuousLinearMap
  exact ⟨‖T‖, norm_nonneg _, T.le_opNorm⟩

theorem powerSeries_into_smooth (D : J → V →ₗ[ℂ] C(G₀, ℂ))
    (ι : S →ₗ[ℂ] V) {f : ℂ → S} {p : FormalMultilinearSeries ℂ ℂ S}
    {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : HasFPowerSeriesOnBall f p z₀ (ENNReal.ofReal ρ)) :
    KPGlobalEisensteinData.SmoothPowerSeriesOn D z₀ ρ
      (fun n => ι (p.coeff n)) (fun z => ι (f z)) := by
  intro i r hr hrρ ε hε
  obtain ⟨C, hC, hb⟩ := compactJet_bound D ι i
  let R : NNReal := ⟨(r + ρ) / 2, by positivity⟩
  have hR : (R : ENNReal) < ENNReal.ofReal ρ := by
    rw [ENNReal.coe_lt_ofReal]
    change (r + ρ) / 2 < ρ
    linarith
  have hu := hf.tendstoUniformlyOn' hR
  rw [Metric.tendstoUniformlyOn_iff] at hu
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hu (ε / (C + 1)) (by positivity))
  refine ⟨N, fun M hM z hz => ?_⟩
  have hzR : z ∈ Metric.ball z₀ (R : ℝ) := by
    apply Metric.mem_ball.mpr
    apply (Metric.mem_closedBall.mp hz).trans_lt
    change r < (r + ρ) / 2
    linarith
  have hn := hN M hM z hzR
  have heq : (∑ q ∈ Finset.range M, (z - z₀) ^ q • ι (p.coeff q)) - ι (f z) =
      ι (p.partialSum M (z - z₀) - f z) := by
    simp [FormalMultilinearSeries.partialSum, FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  rw [heq]
  apply lt_of_le_of_lt (hb _)
  have hsmall : (C + 1) * ‖p.partialSum M (z - z₀) - f z‖ < ε := by
    rw [dist_eq_norm] at hn
    simpa only [norm_sub_rev, mul_comm] using
      (lt_div_iff₀ (by positivity : 0 < C + 1)).mp hn
  nlinarith [norm_nonneg (p.partialSum M (z - z₀) - f z)]

theorem holomorphic_into_smooth (D : J → V →ₗ[ℂ] C(G₀, ℂ))
    (ι : S →ₗ[ℂ] V) {f : ℂ → S} {O : Set ℂ}
    (hO : IsOpen O) (hf : DifferentiableOn ℂ f O) :
    KPGlobalEisensteinData.SmoothHolomorphicOn D (fun z => ι (f z)) O := by
  letI : CompleteSpace S := FiniteDimensional.complete ℂ S
  intro z hz
  obtain ⟨t, ht, htb⟩ := Metric.isOpen_iff.mp hO z hz
  let ρ := t / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hc : Metric.closedBall z ρ ⊆ O := by
    intro w hw
    apply htb
    apply Metric.mem_ball.mpr
    apply (Metric.mem_closedBall.mp hw).trans_lt
    dsimp [ρ]
    linarith
  have hp := (hf.mono hc).hasFPowerSeriesOnBall (R := ⟨ρ, hρ.le⟩) hρ
  have hp' : HasFPowerSeriesOnBall f (cauchyPowerSeries f z ρ) z
      (ENNReal.ofReal ρ) := by
    convert hp using 1
    · rfl
    · exact ENNReal.ofReal_coe_nnreal (p := (⟨ρ, hρ.le⟩ : NNReal))
  exact ⟨ρ, hρ, Metric.ball_subset_closedBall.trans hc,
    (fun n => ι ((cauchyPowerSeries f z ρ).coeff n)),
    powerSeries_into_smooth D ι hρ hp'⟩

end DedekindZetaZeroFree.KPGlobalResidualConstruction.FiniteStageAnalytic

end
