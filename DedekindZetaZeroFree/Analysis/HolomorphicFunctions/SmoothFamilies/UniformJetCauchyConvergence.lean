module

public import DedekindZetaZeroFree.Analysis.HolomorphicFunctions.SmoothFamilies.ScalarMultiplication

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly.ContourLift

open KPContLocalNorm
open scoped NNReal

theorem scalar_jet_cauchy_uniform {n : ℕ} (B : LocalBall n)
    (O : Set ℂ) (f : ℂ → Space n → ℂ)
    (hf : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (f z) B.carrier)
    (hjets : Raw.JetContinuousOn B f O)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hclosed : Metric.closedBall c ρ ⊆ O)
    (hhol : ∀ (m : ℕ) (α : MultiIndex n m) (x : Space n), x ∈ B.carrier →
      DifferentiableOn ℂ (fun z => coordinateDerivative α (f z) x) (Metric.ball c ρ))
    (K : Set (Space n)) (hK : IsCompact K) (hKB : K ⊆ B.carrier)
    (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (hrρ : r < ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ M ≥ N, ∀ z ∈ Metric.closedBall c r,
      ∀ α : MultiIndex n m, ∀ x : K,
        ‖(∑ j ∈ Finset.range M, (z - c) ^ j *
          ((cauchyPowerSeries (fun w => coordinateDerivative α (f w) x) c ρ j)
            (fun _ => (1 : ℂ)))) - coordinateDerivative α (f z) x‖ < ε := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let J : ℂ → CompactJets K m := fun z =>
    if hz : z ∈ O then fun α =>
      ⟨fun x => coordinateDerivative α (f z) x,
        ((finite_coordinate_derivative_smooth B (hf z hz) α.directions).continuousOn.mono
          hKB).restrict⟩ else 0
  have hJ : ContinuousOn J O := by
    apply continuousOn_iff_continuous_restrict.mpr
    apply Metric.continuous_iff.mpr
    intro z₀ η hη
    obtain ⟨δ, hδ, hb⟩ := hjets z₀ z₀.property K hK hKB m η hη
    refine ⟨δ, hδ, ?_⟩
    intro z hz
    rw [dist_eq_norm]
    apply (pi_norm_lt_iff hη).mpr
    intro α
    apply (ContinuousMap.norm_lt_iff _ hη).mpr
    intro x
    change ‖J z α x - J z₀ α x‖ < η
    simp only [J, dif_pos z.property, dif_pos z₀.property]
    change ‖coordinateDerivative α (f z) x - coordinateDerivative α (f z₀) x‖ < η
    have he := finite_coordinate_derivative_sub B (hf z z.property) (hf z₀ z₀.property)
      α.directions (hKB x.property)
    change coordinateDerivative α (fun y => f z y - f z₀ y) x =
      coordinateDerivative α (f z) x - coordinateDerivative α (f z₀) x at he
    rw [← he]
    exact hb z z.property hz α x
  have hscalar (α : MultiIndex n m) (x : K) :
      ContinuousOn (fun z => coordinateDerivative α (f z) x) O := by
    let L : CompactJets K m →L[ℂ] ℂ :=
      (ContinuousMap.evalCLM ℂ x).comp (ContinuousLinearMap.proj α)
    exact (L.continuous.comp_continuousOn hJ).congr (by
      intro z hz
      change coordinateDerivative α (f z) x = J z α x
      simp only [J, dif_pos hz]
      rfl)
  have hcirc : Continuous (fun θ => J (circleMap c ρ θ)) :=
    hJ.comp_continuous (continuous_circleMap c ρ)
      (fun θ => hclosed (Metric.sphere_subset_closedBall (circleMap_mem_sphere c hρ.le θ)))
  let A : ℝ := (2 * Real.pi)⁻¹ * ∫ θ : ℝ in 0..2 * Real.pi, ‖J (circleMap c ρ θ)‖
  have hcoef (j : ℕ) (α : MultiIndex n m) (x : K) :
      ‖(cauchyPowerSeries (fun w => coordinateDerivative α (f w) x) c ρ j)
        (fun _ => (1 : ℂ))‖ ≤ A * ρ⁻¹ ^ j := by
    have hscirc : Continuous (fun θ => coordinateDerivative α (f (circleMap c ρ θ)) x) :=
      (hscalar α x).comp_continuous (continuous_circleMap c ρ)
        (fun θ => hclosed (Metric.sphere_subset_closedBall (circleMap_mem_sphere c hρ.le θ)))
    have hb : ∀ θ, ‖coordinateDerivative α (f (circleMap c ρ θ)) x‖ ≤
        ‖J (circleMap c ρ θ)‖ := by
      intro θ
      have hz := hclosed (Metric.sphere_subset_closedBall (circleMap_mem_sphere c hρ.le θ))
      calc
        _ = ‖J (circleMap c ρ θ) α x‖ := by simp only [J, dif_pos hz]; rfl
        _ ≤ ‖J (circleMap c ρ θ) α‖ := ContinuousMap.norm_coe_le_norm _ x
        _ ≤ _ := norm_le_pi_norm _ α
    calc
      _ ≤ ‖cauchyPowerSeries (fun w => coordinateDerivative α (f w) x) c ρ j‖ := by
        simpa using (cauchyPowerSeries (fun w => coordinateDerivative α (f w) x) c ρ j).le_opNorm
          (fun _ => (1 : ℂ))
      _ ≤ ((2 * Real.pi)⁻¹ * ∫ θ : ℝ in 0..2 * Real.pi,
          ‖coordinateDerivative α (f (circleMap c ρ θ)) x‖) * ρ⁻¹ ^ j := by
        simpa [abs_of_pos hρ] using norm_cauchyPowerSeries_le
          (fun w => coordinateDerivative α (f w) x) c ρ j
      _ ≤ A * ρ⁻¹ ^ j := by
        dsimp [A]
        gcongr
        exact intervalIntegral.integral_mono_on (by positivity) (hscirc.norm.intervalIntegrable _ _)
          (hcirc.norm.intervalIntegrable _ _) (fun θ _ => hb θ)
  let X := Metric.closedBall c r × MultiIndex n m × K
  let g : ℕ → X → ℂ := fun j p => (p.1.val - c) ^ j *
    (cauchyPowerSeries (fun w => coordinateDerivative p.2.1 (f w) p.2.2) c ρ j)
      (fun _ => (1 : ℂ))
  have hmajor : ∀ j p, ‖g j p‖ ≤ A * (r / ρ) ^ j := by
    intro j p
    have hz : ‖p.1.val - c‖ ≤ r := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.mp p.1.property
    dsimp [g]
    rw [norm_mul, norm_pow]
    calc
      _ ≤ r ^ j * ‖(cauchyPowerSeries
          (fun w => coordinateDerivative p.2.1 (f w) p.2.2) c ρ j) (fun _ => (1 : ℂ))‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz j) (norm_nonneg _)
      _ ≤ r ^ j * (A * ρ⁻¹ ^ j) :=
        mul_le_mul_of_nonneg_left (hcoef j p.2.1 p.2.2) (pow_nonneg hr j)
      _ = A * (r / ρ) ^ j := by rw [div_eq_mul_inv, mul_pow]; ring
  have hs : Summable (fun j => A * (r / ρ) ^ j) :=
    (summable_geometric_of_lt_one (div_nonneg hr hρ.le)
      ((div_lt_one hρ).mpr hrρ)).mul_left A
  have hsum (p : X) : (∑' j, g j p) = coordinateDerivative p.2.1 (f p.1.val) p.2.2 := by
    let R : ℝ≥0 := ⟨ρ, hρ.le⟩
    have hd : DiffContOnCl ℂ (fun z => coordinateDerivative p.2.1 (f z) p.2.2)
        (Metric.ball c (R : ℝ)) := by
      refine ⟨hhol m p.2.1 p.2.2 (hKB p.2.2.property), ?_⟩
      exact ((hscalar p.2.1 p.2.2).mono hclosed).mono
        (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
    have hp := hd.hasFPowerSeriesOnBall (show 0 < R from hρ)
    have hz : p.1.val ∈ Metric.eball c (R : ENNReal) := by
      rw [Metric.eball_coe]
      exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp p.1.property).trans_lt hrρ)
    have ht := hp.hasSum_sub hz
    convert ht.tsum_eq using 1
    congr 1
    funext j
    dsimp [g]
    simp [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, mul_comm, R]
    exact Or.inl rfl
  have hu := tendstoUniformly_tsum_nat hs hmajor
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((Metric.tendstoUniformly_iff.mp hu) ε hε)
  refine ⟨N, ?_⟩
  intro M hM z hz α x
  have hh := hN M hM (⟨z, hz⟩, α, x)
  rw [hsum] at hh
  simpa only [dist_eq_norm, norm_sub_rev, g] using hh

end DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly.ContourLift

end
