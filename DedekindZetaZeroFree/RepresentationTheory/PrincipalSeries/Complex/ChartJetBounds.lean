module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ComplexChartsAndSphericalSections

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts

noncomputable section

open Filter Topology
open scoped ContDiff

private def compactifiedChart (f : PrincipalSeries positiveParameter) (p : ℝ × ℂ) : ℂ :=
  ((‖p.2‖ ^ (-(8 / 3 : ℝ)) : ℝ) : ℂ) * infinityCoordinate f ((p.1 : ℂ) / p.2)

private lemma compactifiedChart_smooth (f : PrincipalSeries positiveParameter) :
    ContDiffOn ℝ (⊤ : ℕ∞) (compactifiedChart f) {p | p.2 ≠ 0} := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  unfold compactifiedChart
  apply ContDiffAt.mul
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp p
      ((contDiff_snd.contDiffAt.norm ℝ hp).rpow_const_of_ne (norm_ne_zero_iff.mpr hp))
  · apply f.property.2.2.contDiffAt.comp p
    apply ContDiffAt.mul
    · exact Complex.ofRealCLM.contDiff.contDiffAt.comp p contDiff_fst.contDiffAt
    · exact (contDiffAt_inv (𝕜 := ℝ) hp).comp p contDiff_snd.contDiffAt

private lemma openChart_rescaling (f : PrincipalSeries positiveParameter)
    (R : ℝ) (hR : 0 < R) (z : ℂ) (hz : z ≠ 0) :
    openCoordinate f ((R : ℂ) * z) =
      ((R ^ (-(8 / 3 : ℝ)) : ℝ) : ℂ) * compactifiedChart f (R⁻¹, z) := by
  have hx : (R : ℂ) * z ≠ 0 := mul_ne_zero (by exact_mod_cast hR.ne') hz
  have ht := coordinate_transition positiveParameter f (((R : ℂ) * z)⁻¹) (inv_ne_zero hx)
  rw [inv_inv] at ht
  have hw : transitionWeight positiveParameter (((R : ℂ) * z)⁻¹) =
      ‖(R : ℂ) * z‖ ^ (8 / 3 : ℝ) := by
    unfold transitionWeight
    rw [norm_inv]
    change (‖(R : ℂ) * z‖⁻¹) ^ (-2 * (1 + 2 * positiveParameter)) = _
    rw [Real.inv_rpow (norm_nonneg _),
      show -2 * (1 + 2 * positiveParameter) = -(8 / 3 : ℝ) by norm_num [positiveParameter],
      Real.rpow_neg (norm_nonneg _), inv_inv]
  rw [hw] at ht
  have hp : ((‖(R : ℂ) * z‖ ^ (8 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) (8 / 3 : ℝ)).ne'
  apply (mul_left_cancel₀ hp)
  rw [← ht]
  unfold compactifiedChart
  have hn : ‖(R : ℂ) * z‖ = R * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  rw [hn, Real.mul_rpow hR.le (norm_nonneg z)]
  have he : R ^ (8 / 3 : ℝ) * R ^ (-(8 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hR, add_neg_cancel, Real.rpow_zero]
  have hzpow : ‖z‖ ^ (8 / 3 : ℝ) * ‖z‖ ^ (-(8 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add (norm_pos_iff.mpr hz), add_neg_cancel, Real.rpow_zero]
  push_cast
  have hi : ((R : ℂ) * z)⁻¹ = (R⁻¹ : ℝ) / z := by
    simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
  rw [hi]
  have he' := congrArg (fun r : ℝ => (r : ℂ)) he
  have hz' := congrArg (fun r : ℝ => (r : ℂ)) hzpow
  push_cast at he' hz'
  symm
  calc
    _ = ((R ^ (8 / 3 : ℝ) : ℝ) : ℂ) * ((R ^ (-(8 / 3 : ℝ)) : ℝ) : ℂ) *
      (((‖z‖ ^ (8 / 3 : ℝ) : ℝ) : ℂ) * ((‖z‖ ^ (-(8 / 3 : ℝ)) : ℝ) : ℂ)) *
        infinityCoordinate f ((R⁻¹ : ℝ) / z) := by
          simp only [Complex.ofReal_inv]
          ring
    _ = _ := by
      rw [he', hz']
      simp

private lemma compactifiedChart_uniform_jets (f : PrincipalSeries positiveParameter) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (z : ℂ), t ∈ Set.Icc 0 1 → ‖z‖ = 1 →
      ‖iteratedFDeriv ℝ n (compactifiedChart f) (t, z)‖ ≤ C := by
  let s : Set (ℝ × ℂ) := Set.Icc 0 1 ×ˢ Metric.sphere (0 : ℂ) 1
  have hs : IsCompact s := isCompact_Icc.prod (isCompact_sphere _ _)
  have ho : IsOpen {p : ℝ × ℂ | p.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
  have hsub : s ⊆ {p : ℝ × ℂ | p.2 ≠ 0} := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hn : ‖z‖ = 1 := by simpa using hz
    exact norm_ne_zero_iff.mp (by rw [hn]; norm_num)
  have hc := ContinuousOn.continuousOn_iteratedFDeriv (compactifiedChart_smooth f) ho
    (show (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)
  obtain ⟨C, hC⟩ := (hs.bddAbove_image (hc.norm.mono hsub))
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro t z ht hz
  have hm : (t, z) ∈ s := ⟨ht, by simpa using hz⟩
  exact (hC ⟨(t, z), hm, rfl⟩).trans (by linarith [le_max_left C 0])

private lemma compactifiedChart_slice_jet_le (f : PrincipalSeries positiveParameter)
    (n : ℕ) (t : ℝ) (z : ℂ) (hz : z ≠ 0) :
    ‖iteratedFDeriv ℝ n (fun w : ℂ => compactifiedChart f (t, w)) z‖ ≤
      ‖iteratedFDeriv ℝ n (compactifiedChart f) (t, z)‖ := by
  let L : ℂ →L[ℝ] ℝ × ℂ := ContinuousLinearMap.inr ℝ ℝ ℂ
  let H := fun p : ℝ × ℂ => compactifiedChart f ((t, 0) + p)
  let S : Set (ℝ × ℂ) := {p | p.2 ≠ 0}
  have hS : IsOpen S := isOpen_ne_fun continuous_snd continuous_const
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H S := by
    apply (compactifiedChart_smooth f).comp (contDiff_const.add contDiff_id).contDiffOn
    intro p hp
    simpa [S] using hp
  have hp : L z ∈ S := hz
  have he := L.iteratedFDerivWithin_comp_right hH hS.uniqueDiffOn
    (hS.preimage L.continuous).uniqueDiffOn hp (show (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)
  rw [iteratedFDerivWithin_of_isOpen n (hS.preimage L.continuous) (show z ∈ L ⁻¹' S from hz),
    iteratedFDerivWithin_of_isOpen n hS hp] at he
  have hn : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    simp [L]
  have hb := (iteratedFDeriv ℝ n H (L z)).norm_compContinuousLinearMap_le (fun _ => L)
  have hprod : (∏ _ : Fin n, ‖L‖) ≤ 1 := by
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hn)
  have heH : iteratedFDeriv ℝ n H (L z) = iteratedFDeriv ℝ n (compactifiedChart f) (t, z) := by
    convert iteratedFDeriv_comp_add_left n (t, 0) (L z) using 1
    simp [L]
  have hfun : (fun w : ℂ => compactifiedChart f (t, w)) = H ∘ L := by
    funext w
    simp [H, L]
  rw [hfun, he, ← heH]
  exact hb.trans (by nlinarith [norm_nonneg (iteratedFDeriv ℝ n H (L z))])

private lemma openChart_scaled_jet_norm (f : PrincipalSeries positiveParameter)
    (n : ℕ) (R : ℝ) (hR : 0 < R) (z : ℂ) (hz : z ≠ 0) :
    R ^ n * ‖iteratedFDeriv ℝ n (openCoordinate f) ((R : ℂ) * z)‖ =
      R ^ (-(8 / 3 : ℝ)) *
        ‖iteratedFDeriv ℝ n (fun w : ℂ => compactifiedChart f (R⁻¹, w)) z‖ := by
  have hG : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => compactifiedChart f (R⁻¹, w)) z := by
    apply ((compactifiedChart_smooth f).contDiffAt ?_).comp z
      (contDiff_const.prodMk contDiff_id).contDiffAt
    exact (isOpen_ne_fun continuous_snd continuous_const).mem_nhds hz
  have hEq : (fun w : ℂ => openCoordinate f (R • w)) =ᶠ[nhds z]
      (fun w : ℂ => R ^ (-(8 / 3 : ℝ)) • compactifiedChart f (R⁻¹, w)) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    simpa only [Complex.real_smul] using openChart_rescaling f R hR w hw
  have hj := (hEq.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
  rw [iteratedFDeriv_comp_const_smul R (f.property.2.1.of_le (by simp)),
    iteratedFDeriv_const_smul_apply' (hG.of_le (by simp))] at hj
  have hnorm := congrArg norm hj
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hR n),
    abs_of_pos (Real.rpow_pos_of_pos hR _), Complex.real_smul] using hnorm

lemma norm_iteratedFDeriv_openCoordinate_le_of_one_le
    (f : PrincipalSeries positiveParameter) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℂ, 1 ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ n (openCoordinate f) x‖ ≤
        C * ‖x‖ ^ (-(8 / 3 : ℝ) - (n : ℝ)) := by
  obtain ⟨C, hC, hjets⟩ := compactifiedChart_uniform_jets f n
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hR : 0 < ‖x‖ := by linarith
  let z : ℂ := (‖x‖ : ℂ)⁻¹ * x
  have hz : ‖z‖ = 1 := by
    dsimp [z]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
      inv_mul_cancel₀ hR.ne']
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have hmul : (‖x‖ : ℂ) * z = x := by
    dsimp [z]
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hR.ne'), one_mul]
  have hb := hjets ‖x‖⁻¹ z ⟨inv_nonneg.mpr hR.le, inv_le_one_of_one_le₀ hx⟩ hz
  have hb' := (compactifiedChart_slice_jet_le f n ‖x‖⁻¹ z hz0).trans hb
  have he := openChart_scaled_jet_norm f n ‖x‖ hR z hz0
  rw [hmul] at he
  have hbound : ‖x‖ ^ n * ‖iteratedFDeriv ℝ n (openCoordinate f) x‖ ≤
      ‖x‖ ^ (-(8 / 3 : ℝ)) * C := by
    rw [he]
    exact mul_le_mul_of_nonneg_left hb' (Real.rpow_nonneg hR.le _)
  apply (le_of_mul_le_mul_left ?_ (pow_pos hR n))
  calc
    ‖x‖ ^ n * ‖iteratedFDeriv ℝ n (openCoordinate f) x‖ ≤
        ‖x‖ ^ (-(8 / 3 : ℝ)) * C := hbound
    _ = ‖x‖ ^ n * (C * ‖x‖ ^ (-(8 / 3 : ℝ) - (n : ℝ))) := by
      rw [← Real.rpow_natCast ‖x‖ n]
      rw [mul_left_comm, ← Real.rpow_add hR,
        show (n : ℝ) + (-(8 / 3 : ℝ) - (n : ℝ)) = -(8 / 3 : ℝ) by ring]
      exact mul_comm _ _

lemma norm_iteratedFDeriv_openCoordinate_le (f : PrincipalSeries positiveParameter) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℂ,
      ‖iteratedFDeriv ℝ n (openCoordinate f) x‖ ≤
        C * (1 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ) - (n : ℝ) / 2) := by
  obtain ⟨C, hC, hlarge⟩ := norm_iteratedFDeriv_openCoordinate_le_of_one_le f n
  let a : ℝ := (4 / 3 : ℝ) + (n : ℝ) / 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hs := (isCompact_closedBall (0 : ℂ) 1).bddAbove_image
    ((f.property.2.1.continuous_iteratedFDeriv (m := n) (by simp)).norm.continuousOn)
  obtain ⟨M, hM⟩ := hs
  let D : ℝ := max (max M 0) C
  have hD : 0 < D := lt_of_lt_of_le hC (le_max_right _ _)
  refine ⟨D * (2 : ℝ) ^ a, mul_pos hD (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro x
  have hb : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have he : -(4 / 3 : ℝ) - (n : ℝ) / 2 = -a := by dsimp [a]; ring
  rw [he]
  by_cases hx : ‖x‖ ≤ 1
  · have hm : x ∈ Metric.closedBall (0 : ℂ) 1 := by simpa using hx
    have hv : ‖iteratedFDeriv ℝ n (openCoordinate f) x‖ ≤ D :=
      (hM ⟨x, hm, rfl⟩).trans ((le_max_left M 0).trans (le_max_left _ _))
    have hbase : 1 + ‖x‖ ^ 2 ≤ 2 := by nlinarith [norm_nonneg x]
    have hp : 1 ≤ (2 : ℝ) ^ a * (1 + ‖x‖ ^ 2) ^ (-a) := by
      rw [Real.rpow_neg hb.le]
      apply (le_mul_inv_iff₀ (Real.rpow_pos_of_pos hb a)).mpr
      simpa using Real.rpow_le_rpow hb.le hbase ha
    calc
      _ ≤ D := hv
      _ ≤ D * ((2 : ℝ) ^ a * (1 + ‖x‖ ^ 2) ^ (-a)) := by nlinarith
      _ = _ := by ring
  · have hx1 : 1 ≤ ‖x‖ := le_of_lt (lt_of_not_ge hx)
    have hxpos : 0 < ‖x‖ := by linarith
    have hv := hlarge x hx1
    have hp : ‖x‖ ^ (-(8 / 3 : ℝ) - (n : ℝ)) ≤
        (2 : ℝ) ^ a * (1 + ‖x‖ ^ 2) ^ (-a) := by
      have hbase : 1 + ‖x‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 := by nlinarith
      have hp := Real.rpow_le_rpow hb.le hbase ha
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg _),
        ← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul hxpos.le] at hp
      have hexp : -(8 / 3 : ℝ) - (n : ℝ) = -(2 * a) := by dsimp [a]; ring
      rw [hexp, Real.rpow_neg hxpos.le, Real.rpow_neg hb.le]
      apply (le_mul_inv_iff₀ (Real.rpow_pos_of_pos hb a)).mpr
      apply (inv_mul_le_iff₀ (Real.rpow_pos_of_pos hxpos (2 * a))).mpr
      simpa [mul_comm] using hp
    calc
      _ ≤ C * ‖x‖ ^ (-(8 / 3 : ℝ) - (n : ℝ)) := hv
      _ ≤ D * ‖x‖ ^ (-(8 / 3 : ℝ) - (n : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hxpos.le _)
      _ ≤ D * ((2 : ℝ) ^ a * (1 + ‖x‖ ^ 2) ^ (-a)) :=
        mul_le_mul_of_nonneg_left hp hD.le
      _ = _ := by ring

end

end DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts
