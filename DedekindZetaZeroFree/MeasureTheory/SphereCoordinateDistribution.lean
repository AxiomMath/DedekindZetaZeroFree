module

public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.FractionalIntegrals.NormalizedKernel

@[expose] public section

section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.SphereProjection

open MeasureTheory Set
open scoped ENNReal

private lemma coordinate_bounds (y : Sphere) :
    -1 ≤ (y : Ambient) 0 ∧ (y : Ambient) 0 ≤ 1 := by
  have h : ‖(y : Ambient) 0‖ ≤ 1 := by
    calc
      _ ≤ ‖(y : Ambient)‖ := PiLp.norm_apply_le _ _
      _ = 1 := mem_sphere_zero_iff_norm.mp y.property
  simpa [Real.norm_eq_abs, abs_le] using h

theorem projection_of_raw_caps
    (hmass : (volume : Measure Ambient).toSphere univ = ENNReal.ofReal (4 * Real.pi))
    (hcap : ∀ t : ℝ, -1 ≤ t → t ≤ 1 →
      (volume : Measure Ambient).toSphere {y : Sphere | (y : Ambient) 0 ≤ t} =
        ENNReal.ofReal (2 * Real.pi * (t + 1))) :
    Measure.map (fun y : Sphere => (1 - (y : Ambient) 0) / 2) sphereArea =
      (volume : Measure ℝ).restrict (Icc (0 : ℝ) 1) := by
  letI := sphereArea_isProbabilityMeasure
  have hp : Measurable (fun y : Sphere => (1 - (y : Ambient) 0) / 2) := by fun_prop
  apply Measure.ext_of_Ici
  intro a
  rw [Measure.map_apply hp measurableSet_Ici,
    Measure.restrict_apply measurableSet_Ici]
  by_cases ha : a ≤ 0
  · have hpre : (fun y : Sphere => (1 - (y : Ambient) 0) / 2) ⁻¹' Ici a = univ := by
      ext y
      simp only [mem_preimage, mem_Ici, mem_univ, iff_true]
      have := (coordinate_bounds y).2
      linarith
    have hinter : Ici a ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
      ext z
      simp only [mem_inter_iff, mem_Ici, mem_Icc]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨ha.trans h.1, h⟩
    rw [hpre, hinter]
    simp
  · by_cases ha1 : 1 < a
    · have hpre : (fun y : Sphere => (1 - (y : Ambient) 0) / 2) ⁻¹' Ici a = ∅ := by
        ext y
        simp only [mem_preimage, mem_Ici, mem_empty_iff_false, iff_false]
        have := (coordinate_bounds y).1
        linarith
      have hinter : Ici a ∩ Icc (0 : ℝ) 1 = ∅ := by
        ext z
        simp only [mem_inter_iff, mem_Ici, mem_Icc, mem_empty_iff_false, iff_false]
        rintro ⟨hz, -, hz1⟩
        linarith
      simp [hpre, hinter]
    · have ha0 : 0 ≤ a := le_of_lt (lt_of_not_ge ha)
      have ha1' : a ≤ 1 := le_of_not_gt ha1
      have hpre : (fun y : Sphere => (1 - (y : Ambient) 0) / 2) ⁻¹' Ici a =
          {y : Sphere | (y : Ambient) 0 ≤ 1 - 2 * a} := by
        ext y
        simp only [mem_preimage, mem_Ici, mem_setOf_eq]
        constructor <;> intro h <;> linarith
      have hinter : Ici a ∩ Icc (0 : ℝ) 1 = Icc a 1 := by
        ext z
        simp only [mem_inter_iff, mem_Ici, mem_Icc]
        constructor
        · exact fun h => ⟨h.1, h.2.2⟩
        · exact fun h => ⟨h.1, ha0.trans h.1, h.2⟩
      rw [hpre, hinter, sphereArea, Measure.smul_apply, smul_eq_mul, hmass,
        hcap (1 - 2 * a) (by linarith) (by linarith), Real.volume_Icc]
      rw [show 2 * Real.pi * (1 - 2 * a + 1) = (4 * Real.pi) * (1 - a) by ring]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.pi)]
      rw [← mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_mul]

end DedekindZetaZeroFree.ComplexFractionalInverse.SphereProjection

end

section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.SphereProjection
open MeasureTheory Set Filter
open scoped ENNReal Topology

theorem open_north_cap_of_closed
    (μ : Measure Sphere)
    (hcap : ∀ t : ℝ, 0 < t → t ≤ 1 →
      μ {y : Sphere | t ≤ (y : Ambient) 0} = ENNReal.ofReal (2 * Real.pi * (1 - t)))
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) :
    μ {y : Sphere | t < (y : Ambient) 0} = ENNReal.ofReal (2 * Real.pi * (1 - t)) := by
  let r : ℕ → ℝ := fun n => t + (1 - t) / ((n : ℝ) + 1)
  have hrpos (n : ℕ) : 0 < r n := by
    have : 0 < (1 - t) / ((n : ℝ) + 1) := div_pos (by linarith) (by positivity)
    dsimp [r]
    linarith
  have hrle (n : ℕ) : r n ≤ 1 := by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg n)
    have : (1 - t) / ((n : ℝ) + 1) ≤ 1 - t := by
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
      nlinarith
    dsimp [r]
    linarith
  have hrmono : Antitone r := by
    intro n m hnm
    dsimp [r]
    apply add_le_add_right
    apply div_le_div_of_nonneg_left (by linarith) (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hrt : Tendsto r atTop (𝓝 t) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 - t)
    simpa [r, div_eq_mul_inv] using tendsto_const_nhds.add h
  have hsets : (⋃ n, {y : Sphere | r n ≤ (y : Ambient) 0}) =
      {y : Sphere | t < (y : Ambient) 0} := by
    ext y
    simp only [mem_iUnion, mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩
      have hrt' : t < r n := by
        dsimp [r]
        exact lt_add_of_pos_right _ (div_pos (by linarith) (by positivity))
      exact hrt'.trans_le hn
    · intro hy
      have he := hrt.eventually (gt_mem_nhds hy)
      obtain ⟨n, hn⟩ := he.exists
      exact ⟨n, hn.le⟩
  have hmono : Monotone (fun n => {y : Sphere | r n ≤ (y : Ambient) 0}) := by
    intro n m hnm y hy
    exact (hrmono hnm).trans hy
  have hmeasure := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hsets] at hmeasure
  have hvalue : Tendsto (fun n => μ {y : Sphere | r n ≤ (y : Ambient) 0}) atTop
      (𝓝 (ENNReal.ofReal (2 * Real.pi * (1 - t)))) := by
    simp_rw [hcap _ (hrpos _) (hrle _)]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub hrt))
  exact tendsto_nhds_unique hmeasure hvalue

theorem raw_lower_caps_of_positive_north
    (μ : Measure Sphere) [IsFiniteMeasure μ]
    (hmass : μ univ = ENNReal.ofReal (4 * Real.pi))
    (hsym : ∀ t : ℝ, μ {y : Sphere | (y : Ambient) 0 ≤ t} =
      μ {y : Sphere | -t ≤ (y : Ambient) 0})
    (hcap : ∀ t : ℝ, 0 < t → t ≤ 1 →
      μ {y : Sphere | t ≤ (y : Ambient) 0} = ENNReal.ofReal (2 * Real.pi * (1 - t))) :
    ∀ t : ℝ, -1 ≤ t → t ≤ 1 →
      μ {y : Sphere | (y : Ambient) 0 ≤ t} = ENNReal.ofReal (2 * Real.pi * (t + 1)) := by
  intro t ht ht1
  by_cases ht0 : t < 0
  · rw [hsym t, hcap (-t) (by linarith) (by linarith)]
    congr 1
    ring
  · have ht0' : 0 ≤ t := le_of_not_gt ht0
    by_cases htend : t = 1
    · subst t
      have hset : {y : Sphere | (y : Ambient) 0 ≤ (1 : ℝ)} = univ := by
        ext y
        simp only [mem_setOf_eq, mem_univ, iff_true]
        have h : ‖(y : Ambient) 0‖ ≤ 1 := by
          calc
            _ ≤ ‖(y : Ambient)‖ := PiLp.norm_apply_le _ _
            _ = 1 := mem_sphere_zero_iff_norm.mp y.property
        exact (abs_le.mp (by simpa [Real.norm_eq_abs] using h)).2
      rw [hset, hmass]
      congr 1
      ring
    · have htlt : t < 1 := lt_of_le_of_ne ht1 htend
      have hc : {y : Sphere | (y : Ambient) 0 ≤ t} =
          {y : Sphere | t < (y : Ambient) 0}ᶜ := by
        ext y
        simp only [mem_setOf_eq, mem_compl_iff, not_lt]
      rw [hc, measure_compl (by measurability) (measure_ne_top _ _), hmass,
        open_north_cap_of_closed μ hcap t ht0' htlt,
        ← ENNReal.ofReal_sub (4 * Real.pi) (by positivity : 0 ≤ 2 * Real.pi * (1 - t))]
      congr 1
      ring

end DedekindZetaZeroFree.ComplexFractionalInverse.SphereProjection

end
