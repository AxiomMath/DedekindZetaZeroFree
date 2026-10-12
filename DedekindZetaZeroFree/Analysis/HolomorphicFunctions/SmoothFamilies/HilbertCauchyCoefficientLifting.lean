module

public import DedekindZetaZeroFree.Analysis.HolomorphicFunctions.SmoothFamilies.SpatialCauchyDifferentiation
public import DedekindZetaZeroFree.Analysis.HolomorphicFunctions.SmoothFamilies.UniformJetCauchyConvergence

@[expose] public section

section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly.ContourLift

open MeasureTheory KPContLocalNorm

private theorem cauchy_map {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) (g : ℂ → E) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (j : ℕ) (hg : CircleIntegrable g c r) :
    L ((cauchyPowerSeries g c r j) (fun _ => (1 : ℂ))) =
      (cauchyPowerSeries (fun z => L (g z)) c r j) (fun _ => (1 : ℂ)) := by
  have hne : c ∉ Metric.sphere c |r| := by
    simp [Metric.mem_sphere, abs_of_pos hr, (ne_of_gt hr).symm]
  have hi := hg.sub_zpow_smul (-(j : ℤ) - 1) hne
  have hi' : CircleIntegrable (fun z => (z - c)⁻¹ ^ j • (z - c)⁻¹ • g z) c r := by
    convert hi using 1
    funext z
    rw [show -(j : ℤ) - 1 = -((j + 1 : ℕ) : ℤ) by omega]
    rw [zpow_neg, zpow_natCast]
    simp [smul_smul, pow_succ, mul_inv_rev, mul_comm]
  rw [cauchyPowerSeries_apply, cauchyPowerSeries_apply, map_smul]
  simp only [one_div]
  have hm : L (∮ z in C(c, r), (z - c)⁻¹ ^ j • (z - c)⁻¹ • g z) =
      ∮ z in C(c, r), L ((z - c)⁻¹ ^ j • (z - c)⁻¹ • g z) := by
    rw [circleIntegral, circleIntegral, ← L.intervalIntegral_comp_comm hi'.out]
    simp only [map_smul]
  rw [hm]
  simp only [map_smul]

private theorem cauchy_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g h : ℂ → E) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (he : Set.EqOn g h (Metric.sphere c r)) (j : ℕ) :
    (cauchyPowerSeries g c r j) (fun _ => (1 : ℂ)) =
      (cauchyPowerSeries h c r j) (fun _ => (1 : ℂ)) := by
  rw [cauchyPowerSeries_apply, cauchyPowerSeries_apply]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  dsimp only
  rw [he hz]

private theorem zero_derivative {n : ℕ} (u : Space n → ℂ) :
    coordinateDerivative (⟨fun _ => 0, by simp⟩ : MultiIndex n 0) u = u := by
  have hn : ∀ l : List (Fin n), l.flatMap (fun _ => ([] : List (Fin n))) = [] := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih => simpa using ih
  simp [coordinateDerivative, MultiIndex.directions, coordinateDerivativeList, hn]

 def compactFamily {n : ℕ} (B : LocalBall n) (K : Set (Space n))
    (hK : K ⊆ B.carrier) (O : Set ℂ) (f : ℂ → Space n → ℂ)
    (hf : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (f z) B.carrier) : ℂ → C(K, ℂ) := by
  classical
  exact fun z => if hz : z ∈ O then ⟨fun x => f z x,
    ((hf z hz).continuousOn.mono hK).restrict⟩ else 0

private theorem compactFamily_continuous {n : ℕ} (B : LocalBall n)
    (K : Set (Space n)) (hc : IsCompact K) (hK : K ⊆ B.carrier)
    (O : Set ℂ) (f : ℂ → Space n → ℂ)
    (hf : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (f z) B.carrier)
    (hj : Raw.JetContinuousOn B f O) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hc
    ContinuousOn (compactFamily B K hK O f hf) O := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hc
  apply continuousOn_iff_continuous_restrict.mpr
  apply Metric.continuous_iff.mpr
  intro z₀ ε hε
  obtain ⟨δ, hδ, hb⟩ := hj z₀ z₀.property K hc hK 0 ε hε
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_lt_iff _ hε).mpr
  intro x
  change ‖compactFamily B K hK O f hf z x - compactFamily B K hK O f hf z₀ x‖ < ε
  simp only [compactFamily, dif_pos z.property, dif_pos z₀.property]
  change ‖f z x - f z₀ x‖ < ε
  simpa only [zero_derivative] using
    hb z z.property hz (⟨fun _ => 0, by simp⟩ : MultiIndex n 0) x

set_option maxHeartbeats 800000 in
private theorem coefficient_on_compact {n : ℕ} (B : LocalBall n)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (R : H →L[ℂ] BallL2 B) (O : Set ℂ) (v : ℂ → H)
    (hv : ContinuousOn v O) (f : ℂ → Space n → ℂ)
    (hf : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (f z) B.carrier ∧
      (f z =ᵐ[volume.restrict B.carrier] (fun x => R (v z) x)))
    (hj : Raw.JetContinuousOn B f O)
    (c : ℂ) (r : ℝ) (hr : 0 < r) (hs : Metric.closedBall c r ⊆ O)
    (j : ℕ) (K : Set (Space n)) (hc : IsCompact K) (hK : K ⊆ B.carrier) :
    (fun x => (cauchyPowerSeries (fun z => f z x) c r j) (fun _ => (1 : ℂ)))
      =ᵐ[(volume.restrict B.carrier).restrict K]
        (fun x => R ((cauchyPowerSeries v c r j) (fun _ => (1 : ℂ))) x) := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hc
  let μK : Measure K := (volume.restrict B.carrier).comap Subtype.val
  haveI : IsFiniteMeasure μK := by
    apply (isFiniteMeasure_iff μK).mpr
    dsimp [μK]
    rw [comap_subtype_coe_apply hc.measurableSet, Set.image_univ, Subtype.range_coe]
    exact lt_of_le_of_lt (Measure.restrict_le_self K) hc.measure_lt_top
  let F := compactFamily B K hK O f (fun z hz => (hf z hz).1)
  have hF : CircleIntegrable F c r :=
    ((compactFamily_continuous B K hc hK O f (fun z hz => (hf z hz).1) hj).mono
      (Metric.sphere_subset_closedBall.trans hs)).circleIntegrable hr.le
  have hv' : CircleIntegrable v c r :=
    (hv.mono (Metric.sphere_subset_closedBall.trans hs)).circleIntegrable hr.le
  let S := LpToLpRestrictCLM (Space n) ℂ ℂ (volume.restrict B.carrier) 2 K
  have hS (u : BallL2 B) : S u =ᵐ[(volume.restrict B.carrier).restrict K] u :=
    LpToLpRestrictCLM_coeFn ℂ K u
  let mp : MeasurePreserving (Subtype.val : K → Space n) μK
      ((volume.restrict B.carrier).restrict K) :=
    measurePreserving_subtype_coe hc.measurableSet
  let T : BallL2 B →L[ℂ] Lp ℂ 2 μK :=
    (Lp.compMeasurePreservingₗᵢ ℂ Subtype.val mp).toContinuousLinearMap.comp S
  have hT (u : BallL2 B) : T u =ᵐ[μK] (fun x : K => u x) :=
    (Lp.coeFn_compMeasurePreserving (S u) mp).trans
      (mp.quasiMeasurePreserving.ae_eq (hS u))
  let A : C(K, ℂ) →L[ℂ] Lp ℂ 2 μK := ContinuousMap.toLp 2 μK ℂ
  have he : Set.EqOn (fun z => A (F z)) (fun z => T (R (v z))) (Metric.sphere c r) := by
    intro z hz
    have hzO := hs (Metric.sphere_subset_closedBall hz)
    apply Lp.ext
    have hfe : (f z) =ᵐ[(volume.restrict B.carrier).restrict K] (fun x => R (v z) x) := by
      exact ae_restrict_of_ae (s := K) (hf z hzO).2
    refine (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) (μ := μK) (F z)).trans ?_
    refine Filter.EventuallyEq.trans ?_ (hT (R (v z))).symm
    have hh := mp.quasiMeasurePreserving.ae_eq hfe
    simp only [F, compactFamily, dif_pos hzO]
    exact hh
  have hcoeff : A ((cauchyPowerSeries F c r j) (fun _ => (1 : ℂ))) =
      T (R ((cauchyPowerSeries v c r j) (fun _ => (1 : ℂ)))) := by
    rw [cauchy_map A F c r hr j hF, cauchy_congr _ _ c r hr.le he j]
    exact (cauchy_map (T.comp R) v c r hr j hv').symm
  apply (ae_restrict_iff_subtype hc.measurableSet).mpr
  have hrep := ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) (μ := μK)
    ((cauchyPowerSeries F c r j) (fun _ => (1 : ℂ)))
  rw [hcoeff] at hrep
  have hrep' := hrep.symm.trans (hT (R ((cauchyPowerSeries v c r j) (fun _ => (1 : ℂ)))))
  filter_upwards [hrep'] with x hx
  have hxcoeff : ((cauchyPowerSeries F c r j) (fun _ => (1 : ℂ))) x =
      (cauchyPowerSeries (fun z => f z x) c r j) (fun _ => (1 : ℂ)) := by
    rw [show ((cauchyPowerSeries F c r j) (fun _ => (1 : ℂ))) x =
      (ContinuousMap.evalCLM ℂ x) ((cauchyPowerSeries F c r j) (fun _ => (1 : ℂ))) by rfl,
      cauchy_map (ContinuousMap.evalCLM ℂ x) F c r hr j hF]
    apply cauchy_congr _ _ c r hr.le _ j
    intro z hz
    have hzO := hs (Metric.sphere_subset_closedBall hz)
    simp only [F, compactFamily, dif_pos hzO, ContinuousMap.evalCLM_apply]
    rfl
  exact hxcoeff.symm.trans hx

theorem coefficient_ae_eq {n : ℕ} (B : LocalBall n)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (R : H →L[ℂ] BallL2 B) (O : Set ℂ) (v : ℂ → H)
    (hv : ContinuousOn v O) (f : ℂ → Space n → ℂ)
    (hf : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (f z) B.carrier ∧
      (f z =ᵐ[volume.restrict B.carrier] (fun x => R (v z) x)))
    (hjets : Raw.JetContinuousOn B f O)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hclosed : Metric.closedBall c ρ ⊆ O)
    (j : ℕ) :
    (fun x => (cauchyPowerSeries (fun z => f z x) c ρ j) (fun _ => (1 : ℂ)))
      =ᵐ[volume.restrict B.carrier]
        (fun x => R ((cauchyPowerSeries v c ρ j) (fun _ => (1 : ℂ))) x) := by
  letI : LocallyCompactSpace B.carrier :=
    (Metric.isOpen_ball : IsOpen B.carrier).locallyCompactSpace
  have hσ : IsSigmaCompact B.carrier :=
    isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨K, hKc, hKu⟩ := hσ
  have hKB : ∀ i, K i ⊆ B.carrier := by
    intro i
    rw [← hKu]
    exact Set.subset_iUnion K i
  let g : Space n → ℂ := fun x =>
    (cauchyPowerSeries (fun z => f z x) c ρ j) (fun _ => (1 : ℂ))
  let h : Space n → ℂ := fun x =>
    R ((cauchyPowerSeries v c ρ j) (fun _ => (1 : ℂ))) x
  change g =ᵐ[volume.restrict B.carrier] h
  rw [← hKu]
  apply (ae_eq_restrict_iUnion_iff K g h).mpr
  intro i
  have hh := coefficient_on_compact B R O v hv f hf hjets c ρ hρ hclosed j
    (K i) (hKc i) (hKB i)
  rw [Measure.restrict_restrict_of_subset (hKB i)] at hh
  exact hh

end DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly.ContourLift

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly.ContourLift

open MeasureTheory KPContLocalNorm Filter Topology
open scoped NNReal

private theorem jets_continuous {n m : ℕ} (B : LocalBall n)
    (K : Set (Space n)) (hcompact : IsCompact K) (hK : K ⊆ B.carrier)
    (O : Set ℂ) (f : ℂ → Space n → ℂ)
    (hf : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (f z) B.carrier)
    (hjets : Raw.JetContinuousOn B f O) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
    Continuous (fun z : O => compactJet (m := m) B K hK (f z) (hf z z.property)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  apply Metric.continuous_iff.mpr
  intro z₀ ε hε
  obtain ⟨δ, hδ, hbound⟩ := hjets z₀ z₀.property K hcompact hK m ε hε
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  rw [dist_eq_norm]
  apply (pi_norm_lt_iff hε).mpr
  intro α
  apply (ContinuousMap.norm_lt_iff _ hε).mpr
  intro x
  change ‖coordinateDerivative α (f z) x - coordinateDerivative α (f z₀) x‖ < ε
  have he := finite_coordinate_derivative_sub B (hf z z.property)
    (hf z₀ z₀.property) α.directions (hK x.property)
  change coordinateDerivative α (fun y => f z y - f z₀ y) x =
    coordinateDerivative α (f z) x - coordinateDerivative α (f z₀) x at he
  rw [← he]
  exact hbound z z.property hz α x

theorem spatial_jet_continuousOn {n : ℕ} (B : LocalBall n)
    (O : Set ℂ) (f : ℂ → Space n → ℂ)
    (hf : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (f z) B.carrier)
    (hjets : Raw.JetContinuousOn B f O)
    (m : ℕ) (α : MultiIndex n m) (x : Space n) (hx : x ∈ B.carrier) :
    ContinuousOn (fun z => coordinateDerivative α (f z) x) O := by
  apply Metric.continuousOn_iff.mpr
  intro z₀ hz₀ ε hε
  obtain ⟨δ, hδ, hb⟩ := hjets z₀ hz₀ {x} (isCompact_singleton)
    (Set.singleton_subset_iff.mpr hx) m ε hε
  refine ⟨δ, hδ, ?_⟩
  intro z hz hdist
  rw [dist_eq_norm]
  have he := finite_coordinate_derivative_sub B (hf z hz) (hf z₀ hz₀)
    α.directions hx
  change coordinateDerivative α (fun y => f z y - f z₀ y) x =
    coordinateDerivative α (f z) x - coordinateDerivative α (f z₀) x at he
  rw [← he]
  exact hb z hz hdist α ⟨x, Set.mem_singleton x⟩

theorem jetContinuousOn_continuous_mul {n : ℕ} (B : LocalBall n)
    (O : Set ℂ) (f : ℂ → Space n → ℂ)
    (hf : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (f z) B.carrier)
    (hjets : Raw.JetContinuousOn B f O)
    (q : ℂ → ℂ) (hq : ContinuousOn q O) :
    Raw.JetContinuousOn B (fun z y => q z * f z y) O := by
  intro z₀ hz₀ K hcompact hK m ε hε
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  have hcont := (continuousOn_iff_continuous_restrict.mp hq).smul
    (jets_continuous (m := m) B K hcompact hK O f hf hjets)
  obtain ⟨δ, hδ, hb⟩ := Metric.continuous_iff.mp hcont (⟨z₀, hz₀⟩ : O) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro z hz hdist α x
  have hb' := hb (⟨z, hz⟩ : O) hdist
  rw [dist_eq_norm] at hb'
  have hpi := (pi_norm_lt_iff hε).mp hb' α
  have hpt : ‖q z * coordinateDerivative α (f z) x -
      q z₀ * coordinateDerivative α (f z₀) x‖ < ε :=
    (ContinuousMap.norm_lt_iff _ hε).mp hpi x
  have hfs : ∀ t ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => q t * f t y) B.carrier := by
    intro t ht
    simpa only [smul_eq_mul] using (hf t ht).const_smul (q t)
  change ‖coordinateDerivativeList α.directions (fun y => q z * f z y - q z₀ * f z₀ y) x‖ < ε
  rw [finite_coordinate_derivative_sub B (hfs z hz) (hfs z₀ hz₀) α.directions (hK x.property)]
  simpa only [coordinateDerivative, finite_coordinate_derivative_const_mul] using hpt

theorem spatial_jets_differentiableOn {n : ℕ} (B : LocalBall n)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (R : H →L[ℂ] BallL2 B)
    (O : Set ℂ) (v : ℂ → H) (hv : DifferentiableOn ℂ v O)
    (f : ℂ → Space n → ℂ)
    (hf : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (f z) B.carrier ∧
      (f z =ᵐ[volume.restrict B.carrier] (fun x => R (v z) x)))
    (hjets : Raw.JetContinuousOn B f O)
    (m : ℕ) (α : MultiIndex n m) (x : Space n) (hx : x ∈ B.carrier) :
    DifferentiableOn ℂ (fun z => coordinateDerivative α (f z) x) (interior O) := by
  intro c hc
  obtain ⟨s, hs, hsO⟩ := Metric.isOpen_iff.mp isOpen_interior c hc
  let ρ := s / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hclosed : Metric.closedBall c ρ ⊆ O := fun z hz =>
    interior_subset (hsO (Metric.closedBall_subset_ball (by dsimp [ρ]; linarith) hz))
  have hball : Metric.ball c ρ ⊆ interior O := fun z hz =>
    hsO (Metric.ball_subset_ball (by dsimp [ρ]; linarith) hz)
  let g : ℂ → ℂ := fun z => coordinateDerivative α (f z) x
  let G : ℂ → ℂ := fun w => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ∮ z in C(c, ρ), (z - w)⁻¹ • g z
  have hG : DifferentiableOn ℂ G (Metric.ball c ρ) := by
    have hi : CircleIntegrable g c ρ :=
      ((spatial_jet_continuousOn B O f (fun z hz => (hf z hz).1) hjets m α x hx).mono
        (fun z hz => hclosed (Metric.sphere_subset_closedBall hz))).circleIntegrable hρ.le
    let r : ℝ≥0 := ⟨ρ, hρ.le⟩
    have hh := (hasFPowerSeriesOn_cauchy_integral (R := r) hi hρ).analyticOnNhd
    change AnalyticOnNhd ℂ G (Metric.eball c (r : ENNReal)) at hh
    rw [Metric.eball_coe] at hh
    exact hh.differentiableOn
  have heq : Set.EqOn g G (Metric.ball c ρ) := by
    intro w hw
    let d := ρ - ‖w - c‖
    have hd : 0 < d := by dsimp [d]; exact sub_pos.mpr (mem_ball_iff_norm.mp hw)
    let a : ℂ → ℂ := fun z => (z - c) * star (z - w) *
      ((max (Complex.normSq (z - w)) (d ^ 2))⁻¹ : ℝ)
    have ha : Continuous a := by
      have hm : Continuous (fun z : ℂ => max (Complex.normSq (z - w)) (d ^ 2)) := by fun_prop
      have hn : ∀ z : ℂ, max (Complex.normSq (z - w)) (d ^ 2) ≠ 0 := by
        intro z
        exact ne_of_gt (lt_of_lt_of_le (sq_pos_of_pos hd) (le_max_right _ _))
      dsimp [a]
      exact ((continuous_id.sub continuous_const).mul
        (continuous_star.comp (continuous_id.sub continuous_const))).mul
        (Complex.continuous_ofReal.comp (hm.inv₀ hn))
    have haeq : ∀ z ∈ Metric.sphere c ρ, a z = (z - c) * (z - w)⁻¹ := by
      intro z hz
      have hzρ : ‖z - c‖ = ρ := mem_sphere_iff_norm.mp hz
      have ht : d ≤ ‖z - w‖ := by
        have ht := norm_add_le (z - w) (w - c)
        rw [sub_add_sub_cancel] at ht
        dsimp [d]
        linarith
      have ht' : d ^ 2 ≤ Complex.normSq (z - w) := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg (z - w)]
      dsimp [a]
      rw [max_eq_left ht', Complex.inv_def]
      simp only [Complex.star_def, Complex.ofReal_inv]
      ring
    have hkernel : ∀ z ∈ Metric.sphere c ρ, (z - c)⁻¹ * a z = (z - w)⁻¹ := by
      intro z hz
      have hzc : z - c ≠ 0 := by
        intro he
        have hzρ := mem_sphere_iff_norm.mp hz
        rw [he, norm_zero] at hzρ
        linarith
      rw [haeq z hz, ← mul_assoc, inv_mul_cancel₀ hzc, one_mul]
    let F : ℂ → Space n → ℂ := fun z y => a z * f z y
    let V : ℂ → H := fun z => a z • v z
    have hF : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (F z) B.carrier :=
      fun z hz => contDiffOn_const.mul (hf z hz).1
    have hFj : Raw.JetContinuousOn B F O :=
      jetContinuousOn_continuous_mul B O f (fun z hz => (hf z hz).1) hjets a ha.continuousOn
    have hFa : ∀ z ∈ O, F z =ᵐ[volume.restrict B.carrier] (fun y => R (V z) y) := by
      intro z hz
      dsimp [V]
      rw [map_smul]
      filter_upwards [(hf z hz).2, Lp.coeFn_smul (a z) (R (v z))] with y hy hy'
      dsimp [F]
      rw [hy]
      exact hy'.symm
    have hcoeff : (cauchyPowerSeries V c ρ 0) (fun _ => (1 : ℂ)) = v w := by
      rw [cauchyPowerSeries_apply]
      simp only [pow_zero, one_smul]
      have hci : (∮ z in C(c, ρ), (z - c)⁻¹ • V z) =
          ∮ z in C(c, ρ), (z - w)⁻¹ • v z := by
        apply circleIntegral.integral_congr hρ.le
        intro z hz
        dsimp [V]
        rw [smul_smul, hkernel z hz]
      rw [hci]
      exact Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        Set.countable_empty hw (hv.continuousOn.mono hclosed)
        (fun z hz => (hv z (hclosed (Metric.ball_subset_closedBall hz.1))).differentiableAt
          (Filter.mem_of_superset (isOpen_interior.mem_nhds (hball hz.1)) interior_subset))
    let A : Space n → ℂ := fun y => (cauchyPowerSeries (fun z => F z y) c ρ 0)
      (fun _ => (1 : ℂ))
    have hAs := coefficient_smooth_and_derivatives B O F hF hFj c ρ hρ hclosed 0
    have hAe : A =ᵐ[volume.restrict B.carrier] f w := by
      have h := coefficient_ae_eq B R O V (ha.continuousOn.smul hv.continuousOn) F
        (fun z hz => ⟨hF z hz, hFa z hz⟩) hFj c ρ hρ hclosed 0
      rw [hcoeff] at h
      exact h.trans ((hf w (hclosed (Metric.ball_subset_closedBall hw))).2.symm)
    have hAf : Set.EqOn A (f w) B.carrier := Measure.eqOn_open_of_ae_eq hAe
      Metric.isOpen_ball hAs.1.continuousOn (hf w (hclosed (Metric.ball_subset_closedBall hw))).1.continuousOn
    have hder : coordinateDerivative α A x = coordinateDerivative α (f w) x := by
      exact (KPLocalCubeSobolevJets.coordinateDerivativeList_eventuallyEq α.directions
        (Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx) hAf)).eq_of_nhds
    change coordinateDerivative α (f w) x = G w
    rw [← hder, hAs.2 m α hx]
    dsimp [G, g]
    rw [cauchyPowerSeries_apply]
    simp only [pow_zero, one_smul]
    congr 1
    apply circleIntegral.integral_congr hρ.le
    intro z hz
    change (z - c)⁻¹ • coordinateDerivativeList α.directions (fun y => a z * f z y) x = _
    rw [finite_coordinate_derivative_const_mul]
    simp only [smul_eq_mul, ← mul_assoc, hkernel z hz, coordinateDerivative]
  have hnear : g =ᶠ[nhds c] G := Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds c hρ) heq
  exact (hG c (Metric.mem_ball_self hρ)).differentiableAt (Metric.ball_mem_nhds c hρ)
    |>.congr_of_eventuallyEq hnear |>.differentiableWithinAt

end DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly.ContourLift

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly

open MeasureTheory KPContLocalNorm

def spatialCauchyCoefficient {n : ℕ} (f : ℂ → Space n → ℂ)
    (c : ℂ) (r : ℝ) (j : ℕ) (x : Space n) : ℂ :=
  (cauchyPowerSeries (fun z => f z x) c r j) (fun _ => (1 : ℂ))

theorem eqOn_of_ae_eq_of_contDiffOn {n : ℕ} {B : LocalBall n} {g h : Space n → ℂ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g B.carrier) (hh : ContDiffOn ℝ (⊤ : ℕ∞) h B.carrier)
    (hgh : g =ᵐ[volume.restrict B.carrier] h) : Set.EqOn g h B.carrier :=
  MeasureTheory.Measure.eqOn_of_ae_eq hgh hg.continuousOn hh.continuousOn (by
    rw [LocalBall.carrier, Metric.isOpen_ball.interior_eq]
    exact subset_closure)

theorem smooth_cauchy_coefficient_unique {n : ℕ} (B : LocalBall n)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (R : H →L[ℂ] BallL2 B) (v : ℂ → H) (z₀ : ℂ) (ρ : ℝ) (j : ℕ)
    (c : Space n → ℂ) (hc : ContDiffOn ℝ (⊤ : ℕ∞) c B.carrier)
    (hcae : c =ᵐ[volume.restrict B.carrier]
      (fun x => R ((cauchyPowerSeries v z₀ ρ j) (fun _ => (1 : ℂ))) x))
    (g : Space n → ℂ) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g B.carrier)
    (hgae : g =ᵐ[volume.restrict B.carrier]
      (fun x => R ((cauchyPowerSeries v z₀ ρ j) (fun _ => (1 : ℂ))) x)) :
    Set.EqOn g c B.carrier :=
  eqOn_of_ae_eq_of_contDiffOn hg hc (hgae.trans hcae.symm)

theorem cauchy_coefficients_of_jet_continuity {n : ℕ} (B : LocalBall n)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (R : H →L[ℂ] BallL2 B)
    (O : Set ℂ) (v : ℂ → H) (hv : DifferentiableOn ℂ v O)
    (f : ℂ → Space n → ℂ)
    (hf : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (f z) B.carrier ∧
      (f z =ᵐ[volume.restrict B.carrier] (fun x => R (v z) x)))
    (hjets : Raw.JetContinuousOn B f O)
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hclosed : Metric.closedBall z₀ ρ ⊆ O) :
    ∃ coeff : ℕ → Space n → ℂ,
      (∀ j : ℕ,
        (coeff j =ᵐ[volume.restrict B.carrier]
          (fun x => R ((cauchyPowerSeries v z₀ ρ j) (fun _ => (1 : ℂ))) x)) ∧
        (∀ g : Space n → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) g B.carrier →
          (g =ᵐ[volume.restrict B.carrier]
            (fun x => R ((cauchyPowerSeries v z₀ ρ j) (fun _ => (1 : ℂ))) x)) →
          Set.EqOn g (coeff j) B.carrier)) ∧
      Raw.SmoothPowerSeriesOn B z₀ ρ coeff f := by
  let coeff : ℕ → Space n → ℂ := spatialCauchyCoefficient f z₀ ρ
  have hsmooth : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (coeff j) B.carrier := by
    intro j
    exact (ContourLift.coefficient_smooth_and_derivatives B O f
      (fun z hz => (hf z hz).1) hjets z₀ ρ hρ hclosed j).1
  have hae : ∀ j, coeff j =ᵐ[volume.restrict B.carrier]
      (fun x => R ((cauchyPowerSeries v z₀ ρ j) (fun _ => (1 : ℂ))) x) := by
    intro j
    exact ContourLift.coefficient_ae_eq B R O v hv.continuousOn f hf hjets
      z₀ ρ hρ hclosed j
  refine ⟨coeff, ?_, ?_⟩
  · intro j
    refine ⟨hae j, ?_⟩
    intro g hg hgae
    exact smooth_cauchy_coefficient_unique B R v z₀ ρ j (coeff j)
      (hsmooth j) (hae j) g hg hgae
  · refine ⟨hsmooth, fun z hz => (hf z (hclosed
      (Metric.ball_subset_closedBall hz))).1, ?_⟩
    intro K hK hKB m r hr hrρ ε hε
    have hhol : ∀ (m : ℕ) (α : MultiIndex n m) (x : Space n), x ∈ B.carrier →
        DifferentiableOn ℂ (fun z => coordinateDerivative α (f z) x)
          (Metric.ball z₀ ρ) := by
      intro m α x hx
      exact (ContourLift.spatial_jets_differentiableOn B R O v hv f hf hjets
        m α x hx).mono (interior_maximal
          (Metric.ball_subset_closedBall.trans hclosed) Metric.isOpen_ball)
    obtain ⟨N, hN⟩ := ContourLift.scalar_jet_cauchy_uniform B O f
      (fun z hz => (hf z hz).1) hjets z₀ ρ hρ hclosed hhol
      K hK hKB m r hr hrρ ε hε
    refine ⟨N, ?_⟩
    intro M hM z hz α x
    have hzO : z ∈ O := hclosed ((Metric.closedBall_subset_closedBall hrρ.le) hz)
    rw [coordinate_derivative_taylor_remainder B coeff hsmooth (f z)
      (hf z hzO).1 (z - z₀) M α (hKB x.property)]
    have hderiv : ∀ j, coordinateDerivative α (coeff j) x =
        (cauchyPowerSeries (fun w => coordinateDerivative α (f w) x) z₀ ρ j)
          (fun _ => (1 : ℂ)) := by
      intro j
      exact (ContourLift.coefficient_smooth_and_derivatives B O f
        (fun w hw => (hf w hw).1) hjets z₀ ρ hρ hclosed j).2 m α (hKB x.property)
    simp only [hderiv]
    exact hN M hM z hz α x

end DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly

end

end
