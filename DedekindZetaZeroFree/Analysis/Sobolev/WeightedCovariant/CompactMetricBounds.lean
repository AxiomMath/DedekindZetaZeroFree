module

public import DedekindZetaZeroFree.Analysis.Sobolev.WeightedCovariant.CoordinateData

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

namespace KPCompactInteriorH1

open MeasureTheory TopologicalSpace
open scoped ContDiff InnerProductSpace

private lemma inner_re_eq {r : ℕ} (v w : V r) :
    Complex.re ⟪v, w⟫_ℂ = ∑ a, ((v a).re * (w a).re + (v a).im * (w a).im) := by
  rw [PiLp.inner_apply]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [RCLike.inner_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private lemma quadratic_eq {n r : ℕ} {Ω : Opens (E n)} (Q : InverseMetric Ω)
    (x : E n) (v : Fin n → V r) :
    Q.quadratic x v =
      ∑ a : Fin r,
        ((∑ j, (v j a).re * (∑ k, Q.Q x j k * (v k a).re)) +
         (∑ j, (v j a).im * (∑ k, Q.Q x j k * (v k a).im))) := by
  unfold InverseMetric.quadratic
  simp_rw [inner_re_eq]
  simp_rw [Finset.mul_sum]
  have hcomm : (∑ j : Fin n, ∑ k : Fin n, ∑ a : Fin r,
      Q.Q x j k * ((v j a).re * (v k a).re + (v j a).im * (v k a).im))
      = ∑ a : Fin r, ∑ j : Fin n, ∑ k : Fin n,
      Q.Q x j k * ((v j a).re * (v k a).re + (v j a).im * (v k a).im) := by
    calc (∑ j : Fin n, ∑ k : Fin n, ∑ a : Fin r,
          Q.Q x j k * ((v j a).re * (v k a).re + (v j a).im * (v k a).im))
        = ∑ j : Fin n, ∑ a : Fin r, ∑ k : Fin n,
          Q.Q x j k * ((v j a).re * (v k a).re + (v j a).im * (v k a).im) := by
          apply Finset.sum_congr rfl; intro j _
          exact Finset.sum_comm
      _ = ∑ a : Fin r, ∑ j : Fin n, ∑ k : Fin n,
          Q.Q x j k * ((v j a).re * (v k a).re + (v j a).im * (v k a).im) :=
          Finset.sum_comm
  rw [hcomm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _; ring
  · apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _; ring

private lemma quadratic_smul {n r : ℕ} {Ω : Opens (E n)} (Q : InverseMetric Ω)
    (x : E n) (c : ℝ) (v : Fin n → V r) :
    Q.quadratic x (c • v) = c ^ 2 * Q.quadratic x v := by
  rw [quadratic_eq, quadratic_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hre : ∀ j, ((c • v) j a).re = c * (v j a).re := fun j => by
    simp only [Pi.smul_apply, WithLp.ofLp_smul, Pi.smul_apply, Complex.real_smul,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
  have him : ∀ j, ((c • v) j a).im = c * (v j a).im := fun j => by
    simp only [Pi.smul_apply, WithLp.ofLp_smul, Pi.smul_apply, Complex.real_smul,
      Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, mul_zero, zero_mul, add_zero]
  simp only [hre, him, Finset.mul_sum]
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _; ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _; ring

private lemma quadratic_pos {n r : ℕ} {Ω : Opens (E n)} (Q : InverseMetric Ω)
    (x : E n) (hx : x ∈ (Ω : Set (E n))) {v : Fin n → V r} (hv : v ≠ 0) :
    0 < Q.quadratic x v := by
  rw [quadratic_eq]
  have hpd : (Q.Q x).PosDef := Q.positive_definite x hx
  have hpsd : (Q.Q x).PosSemidef := hpd.posSemidef
  have hnonneg : ∀ (u : Fin n → ℝ), 0 ≤ ∑ j, u j * (∑ k, Q.Q x j k * u k) := by
    intro u
    have := Matrix.PosSemidef.dotProduct_mulVec_nonneg hpsd u
    simpa [dotProduct, Matrix.mulVec] using this
  have hpos : ∀ (u : Fin n → ℝ), u ≠ 0 → 0 < ∑ j, u j * (∑ k, Q.Q x j k * u k) := by
    intro u hu
    have := Matrix.PosDef.dotProduct_mulVec_pos hpd hu
    simpa [dotProduct, Matrix.mulVec] using this
  have hex : ∃ a : Fin r, ∃ j : Fin n, v j a ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext fun j => by ext a; exact h a j)
  obtain ⟨a0, j0, ha0⟩ := hex
  have hnn : ∀ a : Fin r,
      0 ≤ ∑ j, (v j a).re * (∑ k, Q.Q x j k * (v k a).re) +
          ∑ j, (v j a).im * (∑ k, Q.Q x j k * (v k a).im) := by
    intro a
    have h1 := hnonneg (fun j => (v j a).re)
    have h2 := hnonneg (fun j => (v j a).im)
    linarith
  refine Finset.sum_pos' (fun a _ => hnn a) ⟨a0, Finset.mem_univ _, ?_⟩
  have hcase : (v j0 a0).re ≠ 0 ∨ (v j0 a0).im ≠ 0 := by
    by_cases hre : (v j0 a0).re = 0
    · right
      intro him
      exact ha0 (Complex.ext (by simpa using hre) (by simpa using him))
    · left; exact hre
  rcases hcase with hre | him
  · have hA : 0 < ∑ j, (v j a0).re * (∑ k, Q.Q x j k * (v k a0).re) :=
      hpos _ (by intro hh; exact hre (by simpa using congrFun hh j0))
    have h2 := hnonneg (fun j => (v j a0).im)
    linarith
  · have hA : 0 < ∑ j, (v j a0).im * (∑ k, Q.Q x j k * (v k a0).im) :=
      hpos _ (by intro hh; exact him (by simpa using congrFun hh j0))
    have h1 := hnonneg (fun j => (v j a0).re)
    linarith

private lemma exists_ellipticity {n r : ℕ} (Ω : Opens (E n))
    (C : Set (E n)) (hC : IsCompact C) (hCΩ : C ⊆ (Ω : Set (E n)))
    (Q : InverseMetric Ω) :
    ∃ κ Λ : ℝ, 0 < κ ∧ 0 < Λ ∧
      ∀ x ∈ C, ∀ v : Fin n → V r,
        κ * (∑ j, ‖v j‖ ^ (2:ℕ)) ≤ Q.quadratic x v ∧
        Q.quadratic x v ≤ Λ * (∑ j, ‖v j‖ ^ (2:ℕ)) := by
  set S : Set (Fin n → V r) := {v | ∑ j, ‖v j‖ ^ (2:ℕ) = 1} with hSdef
  have hSclosed : IsClosed S := by
    rw [hSdef]
    have hcont : Continuous (fun v : Fin n → V r => ∑ j, ‖v j‖ ^ (2:ℕ)) :=
      continuous_finsetSum Finset.univ
        (fun j _ => ((continuous_apply j).norm).pow 2)
    exact isClosed_eq hcont continuous_const
  have hScomp : IsCompact S := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [hSdef]
      convert isCompact_empty using 1
      ext v
      simp [Finset.univ_eq_empty]
    · have hSsub : S ⊆ Metric.closedBall 0 1 := by
        intro v hv
        rw [Metric.mem_closedBall, dist_zero_right,
          pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
        intro j
        have h1 : ‖v j‖ ^ (2:ℕ) ≤ ∑ k, ‖v k‖ ^ (2:ℕ) :=
          Finset.single_le_sum (f := fun k => ‖v k‖ ^ (2:ℕ))
            (fun k _ => by positivity) (Finset.mem_univ j)
        rw [hv] at h1
        nlinarith [norm_nonneg (v j)]
      exact IsCompact.of_isClosed_subset (isCompact_closedBall 0 1) hSclosed hSsub
  have hφcont : ContinuousOn (fun p : E n × (Fin n → V r) => Q.quadratic p.1 p.2)
      (C ×ˢ S) := by
    unfold InverseMetric.quadratic
    apply continuousOn_finsetSum Finset.univ
    intro j _
    apply continuousOn_finsetSum Finset.univ
    intro k _
    apply ContinuousOn.mul
    · exact (Q.smooth j k).continuousOn.comp continuous_fst.continuousOn
        (fun p hp => hCΩ hp.1)
    · have h1 : Continuous (fun p : E n × (Fin n → V r) => p.2 j) :=
        (continuous_apply j).comp continuous_snd
      have h2 : Continuous (fun p : E n × (Fin n → V r) => p.2 k) :=
        (continuous_apply k).comp continuous_snd
      exact ((Complex.continuous_re.comp continuous_inner).comp
        (h1.prodMk h2)).continuousOn
  have hKS : IsCompact (C ×ˢ S) := hC.prod hScomp
  have hpos : ∀ p ∈ C ×ˢ S, 0 < Q.quadratic p.1 p.2 := by
    rintro ⟨x, u⟩ ⟨hx, hu⟩
    have hu1 : ∑ j, ‖u j‖ ^ (2:ℕ) = 1 := hu
    have hu0 : u ≠ 0 := by
      intro h
      rw [h] at hu1
      simp at hu1
    exact quadratic_pos Q x (hCΩ hx) hu0
  obtain ⟨κ, hκ, hκle⟩ := hKS.exists_forall_le' hφcont hpos
  set T : Set ℝ := (fun p : E n × (Fin n → V r) => Q.quadratic p.1 p.2) '' (C ×ˢ S) with hT
  have hbdd : BddAbove T := by
    rw [hT]; exact hKS.bddAbove_image hφcont
  refine ⟨κ, max 1 (sSup T), hκ, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx v
  have hκu : ∀ u ∈ S, κ ≤ Q.quadratic x u := fun u hu => hκle (x, u) ⟨hx, hu⟩
  have hΛu : ∀ u ∈ S, Q.quadratic x u ≤ max 1 (sSup T) := by
    intro u hu
    have hmem : Q.quadratic x u ∈ T := by
      rw [hT]
      exact Set.mem_image_of_mem (fun p : E n × (Fin n → V r) => Q.quadratic p.1 p.2)
        (show (x, u) ∈ C ×ˢ S from ⟨hx, hu⟩)
    exact le_trans (le_csSup hbdd hmem) (le_max_right _ _)
  by_cases hv : v = 0
  · subst hv
    constructor <;> simp [InverseMetric.quadratic]
  · set s := Real.sqrt (∑ j, ‖v j‖ ^ (2:ℕ)) with hs
    have hsum_pos : 0 < ∑ j, ‖v j‖ ^ (2:ℕ) := by
      obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
        by_contra h; push Not at h; exact hv (funext h)
      have hle : ‖v j‖ ^ (2:ℕ) ≤ ∑ k, ‖v k‖ ^ (2:ℕ) :=
        Finset.single_le_sum (f := fun k => ‖v k‖ ^ (2:ℕ))
          (fun k _ => by positivity) (Finset.mem_univ j)
      exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hj) 2) hle
    have hspos : 0 < s := Real.sqrt_pos.mpr hsum_pos
    have hs2 : s ^ 2 = ∑ j, ‖v j‖ ^ (2:ℕ) := Real.sq_sqrt hsum_pos.le
    set u : Fin n → V r := fun j => (s⁻¹ : ℝ) • v j with hu
    have hu_smul : u = (s⁻¹ : ℝ) • v := by funext j; rfl
    have husum : ∑ j, ‖u j‖ ^ (2:ℕ) = 1 := by
      have hterm : ∀ j, ‖u j‖ ^ (2:ℕ) = (s⁻¹) ^ 2 * ‖v j‖ ^ (2:ℕ) := by
        intro j
        simp only [hu, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hspos), mul_pow]
      simp only [hterm, ← Finset.mul_sum]
      rw [← hs2, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hspos), one_pow]
    have huS : u ∈ S := husum
    have hq : Q.quadratic x v = s ^ 2 * Q.quadratic x u := by
      have h1 : Q.quadratic x u = (s⁻¹) ^ 2 * Q.quadratic x v := by
        rw [hu_smul, quadratic_smul]
      rw [h1, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hspos), one_pow, one_mul]
    constructor
    · rw [hq, ← hs2]
      calc κ * s ^ 2 ≤ Q.quadratic x u * s ^ 2 :=
            mul_le_mul_of_nonneg_right (hκu u huS) (sq_nonneg s)
        _ = s ^ 2 * Q.quadratic x u := by ring
    · rw [hq, ← hs2]
      calc s ^ 2 * Q.quadratic x u ≤ s ^ 2 * max 1 (sSup T) :=
            mul_le_mul_of_nonneg_left (hΛu u huS) (sq_nonneg s)
        _ = max 1 (sSup T) * s ^ 2 := by ring

theorem exists_compact_metric_bounds {n r : ℕ} (Ω : Opens (E n))
    (C : Set (E n)) (hC : IsCompact C) (hCΩ : C ⊆ (Ω : Set (E n)))
    (w : E n → ℝ) (hw : ContDiffOn ℝ ∞ w (Ω : Set (E n)))
    (hwpos : ∀ x ∈ (Ω : Set (E n)), 0 < w x)
    (Q : InverseMetric Ω) (A : Connection (r := r) Ω) :
    ∃ c_w C_w κ Λ M : ℝ,
      0 < c_w ∧ 0 < C_w ∧ 0 < κ ∧ 0 < Λ ∧ 0 ≤ M ∧
      ∀ x ∈ C,
        (c_w ≤ w x ∧ w x ≤ C_w) ∧
        (∀ v : Fin n → V r,
          κ * (∑ j, ‖v j‖ ^ (2 : ℕ)) ≤ Q.quadratic x v ∧
          Q.quadratic x v ≤ Λ * (∑ j, ‖v j‖ ^ (2 : ℕ))) ∧
        (∀ j : Fin n, ‖A.A j x‖ ≤ M) := by
  have hwC : ContinuousOn w C := hw.continuousOn.mono hCΩ
  obtain ⟨c_w, hc_w, hc_wle⟩ := hC.exists_forall_le' hwC (fun b hb => hwpos b (hCΩ hb))
  have hbddw : BddAbove (w '' C) := hC.bddAbove_image hwC
  obtain ⟨κ, Λ, hκ, hΛ, hell⟩ := exists_ellipticity Ω C hC hCΩ Q
  have hAcont : ∀ j : Fin n, ContinuousOn (fun x => ‖A.A j x‖) C :=
    fun j => ((A.smooth j).continuousOn.norm).mono hCΩ
  have hbddA : ∀ j : Fin n, BddAbove ((fun x => ‖A.A j x‖) '' C) :=
    fun j => hC.bddAbove_image (hAcont j)
  set M : ℝ := max 0 (sSup (Set.range fun j : Fin n => sSup ((fun x => ‖A.A j x‖) '' C)))
    with hM
  refine ⟨c_w, max 1 (sSup (w '' C)), κ, Λ, M, hc_w,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), hκ, hΛ, le_max_left _ _, ?_⟩
  intro x hx
  refine ⟨⟨hc_wle x hx, ?_⟩, hell x hx, ?_⟩
  · exact le_trans (le_csSup hbddw (Set.mem_image_of_mem w hx)) (le_max_right _ _)
  · intro j
    have h1 : ‖A.A j x‖ ≤ sSup ((fun x => ‖A.A j x‖) '' C) :=
      le_csSup (hbddA j) (Set.mem_image_of_mem _ hx)
    have h2 : sSup ((fun x => ‖A.A j x‖) '' C) ≤
        sSup (Set.range fun j : Fin n => sSup ((fun x => ‖A.A j x‖) '' C)) := by
      apply le_csSup
      · exact (Set.finite_range _).bddAbove
      · exact Set.mem_range_self j
    exact le_trans h1 (le_trans h2 (le_max_right _ _))

theorem weightedMeasure_mutually_absolutelyContinuous {n : ℕ}
    (Ω : Opens (E n)) (w : E n → ℝ)
    (hw : ContDiffOn ℝ ∞ w (Ω : Set (E n)))
    (hwpos : ∀ x ∈ (Ω : Set (E n)), 0 < w x) :
    KPChartL2.weightedMeasure n (Ω : Set (E n)) w ≪
        volume.restrict (Ω : Set (E n)) ∧
      volume.restrict (Ω : Set (E n)) ≪
        KPChartL2.weightedMeasure n (Ω : Set (E n)) w := by
  have hΩ : MeasurableSet (Ω : Set (E n)) := Ω.isOpen.measurableSet
  have hcont : ContinuousOn w (Ω : Set (E n)) := hw.continuousOn
  have hwae : AEMeasurable w (volume.restrict (Ω : Set (E n))) := hcont.aemeasurable hΩ
  refine ⟨?_, ?_⟩
  · rw [KPChartL2.weightedMeasure]
    exact withDensity_absolutelyContinuous _ _
  · rw [KPChartL2.weightedMeasure]
    refine withDensity_absolutelyContinuous' ?_ ?_
    · exact ENNReal.measurable_ofReal.comp_aemeasurable hwae
    · filter_upwards [self_mem_ae_restrict hΩ] with x hx
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (hwpos x hx))

private theorem weight_bounds {n : ℕ} (Ω : Opens (E n))
    (C : Set (E n)) (hC : IsCompact C) (hCΩ : C ⊆ (Ω : Set (E n)))
    (w : E n → ℝ) (hw : ContDiffOn ℝ ∞ w (Ω : Set (E n)))
    (hwpos : ∀ x ∈ (Ω : Set (E n)), 0 < w x) :
    ∃ c b : ℝ, 0 < c ∧ 0 < b ∧ ∀ x ∈ C, c ≤ w x ∧ w x ≤ b := by
  by_cases hne : C.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hC.exists_isMinOn hne (hw.continuousOn.mono hCΩ)
    obtain ⟨b, hb⟩ := hC.bddAbove_image (hw.continuousOn.mono hCΩ)
    refine ⟨w x, max b 1, hwpos x (hCΩ hx), lt_max_of_lt_right zero_lt_one, ?_⟩
    intro y hy
    exact ⟨hmin hy, (hb (Set.mem_image_of_mem w hy)).trans (le_max_left _ _)⟩
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

private theorem weight_measure_bounds {n : ℕ} (Ω : Opens (E n))
    (C : Set (E n)) (hC : IsCompact C) (hCΩ : C ⊆ (Ω : Set (E n)))
    (w : E n → ℝ) (hw : ContDiffOn ℝ ∞ w (Ω : Set (E n)))
    (hwpos : ∀ x ∈ (Ω : Set (E n)), 0 < w x) :
    ∃ c b : ENNReal, c ≠ ⊤ ∧ b ≠ ⊤ ∧
      volume.restrict C ≤ c • (KPChartL2.weightedMeasure n (Ω : Set (E n)) w).restrict C ∧
      (KPChartL2.weightedMeasure n (Ω : Set (E n)) w).restrict C ≤ b • volume.restrict C := by
  obtain ⟨a, b, ha, hb, hab⟩ := weight_bounds Ω C hC hCΩ w hw hwpos
  have heq : (KPChartL2.weightedMeasure n (Ω : Set (E n)) w).restrict C =
      (volume.restrict C).withDensity (fun x => ENNReal.ofReal (w x)) := by
    rw [KPChartL2.weightedMeasure, restrict_withDensity hC.measurableSet,
      Measure.restrict_restrict_of_subset hCΩ]
  have hd : AEMeasurable (fun x => ENNReal.ofReal (w x)) (volume.restrict C) :=
    ((hw.continuousOn.mono hCΩ).aemeasurable hC.measurableSet).ennreal_ofReal
  have hn : ∀ᵐ x ∂volume.restrict C, ENNReal.ofReal (w x) ≠ 0 := by
    filter_upwards [ae_restrict_mem hC.measurableSet] with x hx
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (hwpos x (hCΩ hx)))
  have hi : ((volume.restrict C).withDensity (fun x => ENNReal.ofReal (w x))).withDensity
      (fun x => (ENNReal.ofReal (w x))⁻¹) = volume.restrict C :=
    withDensity_inv_same₀ hd hn (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)
  refine ⟨(ENNReal.ofReal a)⁻¹, ENNReal.ofReal b,
    ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr ha)), ENNReal.ofReal_ne_top, ?_, ?_⟩
  · rw [heq]
    calc
      volume.restrict C = ((volume.restrict C).withDensity (fun x => ENNReal.ofReal (w x))).withDensity
          (fun x => (ENNReal.ofReal (w x))⁻¹) := hi.symm
      _ ≤ ((volume.restrict C).withDensity (fun x => ENNReal.ofReal (w x))).withDensity
          (fun _ => (ENNReal.ofReal a)⁻¹) := by
        apply withDensity_mono
        apply (withDensity_absolutelyContinuous _ _).ae_le
        filter_upwards [ae_restrict_mem hC.measurableSet] with x hx
        exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (hab x hx).1)
      _ = _ := withDensity_const _
  · rw [heq, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hC.measurableSet] with x hx
    exact ENNReal.ofReal_le_ofReal (hab x hx).2

private theorem supported_restrict_iff {n r : ℕ} (C : Set (E n))
    (hC : MeasurableSet C) (μ : Measure (E n)) (f : E n → V r)
    (hfsupp : ∀ᵐ x ∂μ, x ∉ C → f x = 0) :
    MemLp f 2 μ ↔ MemLp f 2 (μ.restrict C) := by
  refine ⟨fun hf => hf.restrict C, fun hf => ?_⟩
  have heq : C.indicator f =ᵐ[μ] f := by
    filter_upwards [hfsupp] with x hx
    by_cases h : x ∈ C
    · simp [h]
    · simp [h, hx h]
  exact ((memLp_indicator_iff_restrict hC.nullMeasurableSet).mpr hf).ae_eq heq

private theorem connection_term_memLp {n r : ℕ} (Ω : Opens (E n))
    (C : Set (E n)) (hC : IsCompact C) (hCΩ : C ⊆ (Ω : Set (E n)))
    (A : Connection (r := r) Ω) (f : E n → V r)
    (hf : MemLp f 2 (volume.restrict (Ω : Set (E n))))
    (hfsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), x ∉ C → f x = 0)
    (j : Fin n) : MemLp (fun x => A.A j x (f x)) 2
      (volume.restrict (Ω : Set (E n))) := by
  obtain ⟨b, hb⟩ := hC.bddAbove_image ((A.smooth j).continuousOn.norm.mono hCΩ)
  have hmeas : AEStronglyMeasurable (fun x => A.A j x (f x))
      (volume.restrict (Ω : Set (E n))) :=
    (ContinuousLinearMap.apply ℂ (V r)).aestronglyMeasurable_comp₂
      hf.aestronglyMeasurable
      ((A.smooth j).continuousOn.aestronglyMeasurable Ω.isOpen.measurableSet)
  apply (hf.norm.const_smul (max b 0)).mono hmeas
  filter_upwards [hfsupp] with x hx
  by_cases hxC : x ∈ C
  · calc
      ‖A.A j x (f x)‖ ≤ ‖A.A j x‖ * ‖f x‖ := (A.A j x).le_opNorm _
      _ ≤ max b 0 * ‖f x‖ := mul_le_mul_of_nonneg_right
        ((hb (Set.mem_image_of_mem _ hxC)).trans (le_max_left _ _)) (norm_nonneg _)
      _ = ‖((max b 0) • (fun x => ‖f x‖)) x‖ := by simp [abs_of_nonneg (le_max_right b 0)]
  · simp [hx hxC]
private theorem compact_section_memLp_iff {n r : ℕ} (Ω : Opens (E n))
    (C : Set (E n)) (hC : IsCompact C) (hCΩ : C ⊆ (Ω : Set (E n)))
    (w : E n → ℝ) (hw : ContDiffOn ℝ ∞ w (Ω : Set (E n)))
    (hwpos : ∀ x ∈ (Ω : Set (E n)), 0 < w x)
    (f : E n → V r)
    (hfsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), x ∉ C → f x = 0) :
    MemLp f 2 (volume.restrict (Ω : Set (E n))) ↔
      MemLp f 2 (KPChartL2.weightedMeasure n (Ω : Set (E n)) w) := by
  obtain ⟨c, b, hc, hb, hlo, hhi⟩ := weight_measure_bounds Ω C hC hCΩ w hw hwpos
  have hwfsupp : ∀ᵐ x ∂KPChartL2.weightedMeasure n (Ω : Set (E n)) w,
      x ∉ C → f x = 0 := (withDensity_absolutelyContinuous
    (volume.restrict (Ω : Set (E n))) (fun x => ENNReal.ofReal (w x))).ae_le hfsupp
  rw [supported_restrict_iff C hC.measurableSet _ f hfsupp,
    supported_restrict_iff C hC.measurableSet _ f hwfsupp,
    Measure.restrict_restrict_of_subset hCΩ]
  exact ⟨fun hf => hf.of_measure_le_smul hb hhi, fun hf => hf.of_measure_le_smul hc hlo⟩

private theorem energy_meas {n r : ℕ} (Ω : Opens (E n))
    (w : E n → ℝ) (hw : ContDiffOn ℝ ∞ w (Ω : Set (E n)))
    (Q : InverseMetric Ω) (d : Fin n → E n → V r)
    (hd : ∀ j, AEStronglyMeasurable (d j) (volume.restrict (Ω : Set (E n)))) :
    AEStronglyMeasurable (fun x => w x * Q.quadratic x (fun j => d j x))
      (volume.restrict (Ω : Set (E n))) := by
  apply (hw.continuousOn.aestronglyMeasurable Ω.isOpen.measurableSet).mul
  unfold InverseMetric.quadratic
  have hh : ∀ j k, AEStronglyMeasurable (fun x => Q.Q x j k * Complex.re ⟪d j x, d k x⟫_ℂ)
      (volume.restrict (Ω : Set (E n))) := fun j k =>
    ((Q.smooth j k).continuousOn.aestronglyMeasurable Ω.isOpen.measurableSet).mul
      (Complex.continuous_re.comp_aestronglyMeasurable ((hd j).inner (hd k)))
  convert Finset.aestronglyMeasurable_sum Finset.univ (fun j _ =>
      Finset.aestronglyMeasurable_sum Finset.univ (fun k _ => hh j k)) using 1
  funext x
  simp
private theorem compact_energy_iff {n r : ℕ} (Ω : Opens (E n))
    (C : Set (E n)) (hC : IsCompact C) (hCΩ : C ⊆ (Ω : Set (E n)))
    (w : E n → ℝ) (hw : ContDiffOn ℝ ∞ w (Ω : Set (E n)))
    (hwpos : ∀ x ∈ (Ω : Set (E n)), 0 < w x)
    (Q : InverseMetric Ω) (A : Connection (r := r) Ω)
    (d : Fin n → E n → V r)
    (hd : ∀ j, AEStronglyMeasurable (d j) (volume.restrict (Ω : Set (E n))))
    (hsupp : ∀ j, ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), x ∉ C → d j x = 0) :
    (∀ j, MemLp (d j) 2 (volume.restrict (Ω : Set (E n)))) ↔
      Integrable (fun x => w x * Q.quadratic x (fun j => d j x))
        (volume.restrict (Ω : Set (E n))) := by
  obtain ⟨a, b, κ, Λ, M, ha, hb, hk, hl, hM, hbound⟩ :=
    exists_compact_metric_bounds Ω C hC hCΩ w hw hwpos Q A
  have hzero : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), x ∉ C → ∀ j, d j x = 0 := by
    have hall : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), ∀ j, x ∉ C → d j x = 0 :=
      (Filter.eventually_all.mpr hsupp)
    exact hall.mono fun x hx hxC j => hx j hxC
  have hpoint : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      a * κ * (∑ j, ‖d j x‖ ^ 2) ≤ w x * Q.quadratic x (fun j => d j x) ∧
      w x * Q.quadratic x (fun j => d j x) ≤ b * Λ * (∑ j, ‖d j x‖ ^ 2) := by
    filter_upwards [hzero] with x hx
    by_cases hxC : x ∈ C
    · obtain ⟨hwx, hqx, hax⟩ := hbound x hxC
      have hs : 0 ≤ ∑ j, ‖d j x‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hqn : 0 ≤ Q.quadratic x (fun j => d j x) :=
        (mul_nonneg hk.le hs).trans (hqx _).1
      constructor
      · calc
          a * κ * (∑ j, ‖d j x‖ ^ 2) = a * (κ * (∑ j, ‖d j x‖ ^ 2)) := by ring
          _ ≤ a * Q.quadratic x (fun j => d j x) := mul_le_mul_of_nonneg_left (hqx _).1 ha.le
          _ ≤ w x * Q.quadratic x (fun j => d j x) := mul_le_mul_of_nonneg_right hwx.1 hqn
      · calc
          w x * Q.quadratic x (fun j => d j x) ≤ b * Q.quadratic x (fun j => d j x) :=
            mul_le_mul_of_nonneg_right hwx.2 hqn
          _ ≤ b * (Λ * (∑ j, ‖d j x‖ ^ 2)) := mul_le_mul_of_nonneg_left (hqx _).2 hb.le
          _ = b * Λ * (∑ j, ‖d j x‖ ^ 2) := by ring
    · simp [hx hxC, InverseMetric.quadratic]
  have hnonneg : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      0 ≤ w x * Q.quadratic x (fun j => d j x) := hpoint.mono fun x hx =>
    (mul_nonneg (mul_nonneg ha.le hk.le) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans hx.1
  constructor
  · intro hdLp
    have hi : Integrable (fun x => ∑ j, ‖d j x‖ ^ 2)
        (volume.restrict (Ω : Set (E n))) :=
      integrable_finset_sum _ (fun j _ => (hdLp j).integrable_norm_pow (by norm_num))
    apply (hi.const_mul (b * Λ)).mono' (energy_meas Ω w hw Q d hd)
    filter_upwards [hpoint, hnonneg] with x hx hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hx.2
  · intro hi j
    apply (memLp_two_iff_integrable_sq_norm (hd j)).mpr
    apply (hi.const_mul ((a * κ)⁻¹)).mono' ((hd j).norm.pow 2)
    filter_upwards [hpoint] with x hx
    have hsum : ‖d j x‖ ^ 2 ≤ ∑ k, ‖d k x‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖d k x‖ ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have hp : 0 < a * κ := mul_pos ha hk
    have hh : a * κ * ‖d j x‖ ^ 2 ≤ w x * Q.quadratic x (fun j => d j x) :=
      (mul_le_mul_of_nonneg_left hsum hp.le).trans hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (le_inv_mul_iff₀ hp).mpr hh

theorem compact_finiteH0_iff_finiteHw {n r : ℕ} (Ω : Opens (E n))
    (C : Set (E n)) (hC : IsCompact C) (hCΩ : C ⊆ (Ω : Set (E n)))
    (w : E n → ℝ) (hw : ContDiffOn ℝ ∞ w (Ω : Set (E n)))
    (hwpos : ∀ x ∈ (Ω : Set (E n)), 0 < w x)
    (Q : InverseMetric Ω) (A : Connection (r := r) Ω)
    (f : E n → V r) (g : Fin n → E n → V r)
    (hfmeas : AEStronglyMeasurable f (volume.restrict (Ω : Set (E n))))
    (hgmeas : ∀ j, AEStronglyMeasurable (g j) (volume.restrict (Ω : Set (E n))))
    (hfsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), x ∉ C → f x = 0)
    (hgsupp : ∀ j, ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), x ∉ C → g j x = 0) :
    FiniteH0 (Ω : Set (E n)) f g ↔
      FiniteHw (Ω : Set (E n)) w Q A f g := by
  have hdf : ∀ j, ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∉ C → covariantFirst A f g j x = 0 := by
    intro j
    filter_upwards [hfsupp, hgsupp j] with x hx hy
    intro hxC
    simp [covariantFirst, hx hxC, hy hxC]
  have hdmeas : ∀ j, AEStronglyMeasurable (covariantFirst A f g j)
      (volume.restrict (Ω : Set (E n))) := by
    intro j
    exact (hgmeas j).add ((ContinuousLinearMap.apply ℂ (V r)).aestronglyMeasurable_comp₂
      hfmeas ((A.smooth j).continuousOn.aestronglyMeasurable Ω.isOpen.measurableSet))
  have he := compact_energy_iff Ω C hC hCΩ w hw hwpos Q A
    (fun j => covariantFirst A f g j) hdmeas hdf
  have hfe := compact_section_memLp_iff Ω C hC hCΩ w hw hwpos f hfsupp
  constructor
  · rintro ⟨hf, hg⟩
    refine ⟨hfe.mp hf, he.mp (fun j => ?_)⟩
    exact (hg j).add (connection_term_memLp Ω C hC hCΩ A f hf hfsupp j)
  · rintro ⟨hf, hi⟩
    have hf0 := hfe.mpr hf
    have hd := he.mpr hi
    refine ⟨hf0, fun j => ?_⟩
    have hg := (hd j).sub (connection_term_memLp Ω C hC hCΩ A f hf0 hfsupp j)
    convert hg using 1
    funext x
    simp [covariantFirst]

theorem compact_finiteH0_iff_weighted_covariant_memLp {n r : ℕ}
    (Ω : Opens (E n)) (C : Set (E n)) (hC : IsCompact C)
    (hCΩ : C ⊆ (Ω : Set (E n))) (w : E n → ℝ)
    (hw : ContDiffOn ℝ ∞ w (Ω : Set (E n)))
    (hwpos : ∀ x ∈ (Ω : Set (E n)), 0 < w x)
    (A : Connection (r := r) Ω)
    (f : E n → V r) (g : Fin n → E n → V r)
    (hfmeas : AEStronglyMeasurable f (volume.restrict (Ω : Set (E n))))
    (hgmeas : ∀ j, AEStronglyMeasurable (g j) (volume.restrict (Ω : Set (E n))))
    (hfsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), x ∉ C → f x = 0)
    (hgsupp : ∀ j, ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), x ∉ C → g j x = 0) :
    FiniteH0 (Ω : Set (E n)) f g ↔
      (MemLp f 2 (KPChartL2.weightedMeasure n (Ω : Set (E n)) w) ∧
        ∀ j, MemLp (covariantFirst A f g j) 2
          (KPChartL2.weightedMeasure n (Ω : Set (E n)) w)) := by
  have hdf : ∀ j, ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∉ C → covariantFirst A f g j x = 0 := by
    intro j
    filter_upwards [hfsupp, hgsupp j] with x hx hy
    intro hxC
    simp [covariantFirst, hx hxC, hy hxC]
  have hfe := compact_section_memLp_iff Ω C hC hCΩ w hw hwpos f hfsupp
  have hde := fun j => compact_section_memLp_iff Ω C hC hCΩ w hw hwpos
    (covariantFirst A f g j) (hdf j)
  constructor
  · rintro ⟨hf, hg⟩
    refine ⟨hfe.mp hf, fun j => (hde j).mp ?_⟩
    exact (hg j).add (connection_term_memLp Ω C hC hCΩ A f hf hfsupp j)
  · rintro ⟨hf, hd⟩
    have hf0 := hfe.mpr hf
    refine ⟨hf0, fun j => ?_⟩
    have hg := ((hde j).mpr (hd j)).sub
      (connection_term_memLp Ω C hC hCΩ A f hf0 hfsupp j)
    convert hg using 1
    funext x
    simp [covariantFirst]

private theorem weighted_sq_integral {n r : ℕ} (Ω : Opens (E n)) (w : E n → ℝ)
    (hw : ContDiffOn ℝ ∞ w (Ω : Set (E n)))
    (hwpos : ∀ x ∈ (Ω : Set (E n)), 0 < w x) (f : E n → V r) :
    (∫ x, ‖f x‖ ^ 2 ∂KPChartL2.weightedMeasure n (Ω : Set (E n)) w) =
      ∫ x in (Ω : Set (E n)), w x * ‖f x‖ ^ 2 := by
  rw [KPChartL2.weightedMeasure, integral_withDensity_eq_integral_toReal_smul₀
    (hw.continuousOn.aemeasurable Ω.isOpen.measurableSet).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  simp [ENNReal.toReal_ofReal (hwpos x hx).le]

private theorem density_bounds {n r : ℕ} (Ω : Opens (E n))
    (C : Set (E n)) (w : E n → ℝ) (Q : InverseMetric Ω)
    (A : Connection (r := r) Ω) (a b κ Λ M : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < κ) (hl : 0 < Λ) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ C,
      (a ≤ w x ∧ w x ≤ b) ∧
      (∀ v : Fin n → V r, κ * (∑ j, ‖v j‖ ^ 2) ≤ Q.quadratic x v ∧
        Q.quadratic x v ≤ Λ * (∑ j, ‖v j‖ ^ 2)) ∧
      (∀ j, ‖A.A j x‖ ≤ M))
    (f : E n → V r) (g : Fin n → E n → V r)
    (hfsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), x ∉ C → f x = 0)
    (hgsupp : ∀ j, ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), x ∉ C → g j x = 0) :
    let B := b + 2 * b * Λ + 2 * b * Λ * n * M ^ 2
    let D := a⁻¹ + 2 * (a * κ)⁻¹ + 2 * n * M ^ 2 * a⁻¹
    ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      0 ≤ w x * Q.quadratic x (fun j => covariantFirst A f g j x) ∧
      w x * ‖f x‖ ^ 2 + w x * Q.quadratic x (fun j => covariantFirst A f g j x) ≤
        B * (‖f x‖ ^ 2 + ∑ j, ‖g j x‖ ^ 2) ∧
      ‖f x‖ ^ 2 + ∑ j, ‖g j x‖ ^ 2 ≤
        D * (w x * ‖f x‖ ^ 2 + w x * Q.quadratic x (fun j => covariantFirst A f g j x)) := by
  dsimp only
  have hall : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), ∀ j, x ∉ C → g j x = 0 :=
    Filter.eventually_all.mpr hgsupp
  filter_upwards [hfsupp, hall] with x hfx hgx
  by_cases hxC : x ∈ C
  · obtain ⟨hwx, hqx, hax⟩ := hbound x hxC
    let F := ‖f x‖ ^ 2
    let G := ∑ j, ‖g j x‖ ^ 2
    let d := fun j => covariantFirst A f g j x
    let J := ∑ j, ‖d j‖ ^ 2
    have hF : 0 ≤ F := sq_nonneg _
    have hG : 0 ≤ G := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hJ : 0 ≤ J := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hconn : ∀ j, ‖A.A j x (f x)‖ ≤ M * ‖f x‖ := fun j =>
      ((A.A j x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hax j) (norm_nonneg _))
    have hdg : ∀ j, ‖d j‖ ^ 2 ≤ 2 * ‖g j x‖ ^ 2 + 2 * M ^ 2 * F := by
      intro j
      have hh : ‖d j‖ ≤ ‖g j x‖ + M * ‖f x‖ := (norm_add_le _ _).trans
        (add_le_add_right (hconn j) _)
      dsimp [F]
      nlinarith [norm_nonneg (d j), norm_nonneg (g j x), norm_nonneg (f x),
        mul_nonneg hM (norm_nonneg (f x)), sq_nonneg (‖g j x‖ - M * ‖f x‖)]
    have hgd : ∀ j, ‖g j x‖ ^ 2 ≤ 2 * ‖d j‖ ^ 2 + 2 * M ^ 2 * F := by
      intro j
      have hh : ‖g j x‖ ≤ ‖d j‖ + M * ‖f x‖ := by
        have heq : g j x = d j - A.A j x (f x) := by simp [d, covariantFirst]
        rw [heq]
        exact (norm_sub_le _ _).trans (add_le_add_right (hconn j) _)
      dsimp [F]
      nlinarith [norm_nonneg (d j), norm_nonneg (g j x), norm_nonneg (f x),
        mul_nonneg hM (norm_nonneg (f x)), sq_nonneg (‖d j‖ - M * ‖f x‖)]
    have hJG : J ≤ 2 * G + 2 * n * M ^ 2 * F := by
      have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hdg j)
      simpa [J, G, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hh
    have hGJ : G ≤ 2 * J + 2 * n * M ^ 2 * F := by
      have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hgd j)
      simpa [J, G, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hh
    have hqlo : κ * J ≤ Q.quadratic x d := (hqx d).1
    have hqhi : Q.quadratic x d ≤ Λ * J := (hqx d).2
    have hqn : 0 ≤ Q.quadratic x d := (mul_nonneg hk.le hJ).trans hqlo
    have hwqn : 0 ≤ w x * Q.quadratic x d := mul_nonneg (ha.le.trans hwx.1) hqn
    have hWF : w x * F ≤ b * F := mul_le_mul_of_nonneg_right hwx.2 hF
    have hWJ : w x * Q.quadratic x d ≤ b * Λ * J := by
      calc w x * Q.quadratic x d ≤ b * Q.quadratic x d := mul_le_mul_of_nonneg_right hwx.2 hqn
           _ ≤ b * (Λ * J) := mul_le_mul_of_nonneg_left hqhi hb.le
           _ = b * Λ * J := by ring
    have hFrev : F ≤ a⁻¹ * (w x * F) := (le_inv_mul_iff₀ ha).mpr
      (mul_le_mul_of_nonneg_right hwx.1 hF)
    have hJrev : J ≤ (a * κ)⁻¹ * (w x * Q.quadratic x d) := by
      apply (le_inv_mul_iff₀ (mul_pos ha hk)).mpr
      calc a * κ * J = a * (κ * J) := by ring
           _ ≤ a * Q.quadratic x d := mul_le_mul_of_nonneg_left hqlo ha.le
           _ ≤ w x * Q.quadratic x d := mul_le_mul_of_nonneg_right hwx.1 hqn
    have hJG' := mul_le_mul_of_nonneg_left hJG (mul_pos hb hl).le
    have hFrev' := mul_le_mul_of_nonneg_left hFrev
      (by positivity : 0 ≤ 2 * (n : ℝ) * M ^ 2)
    have hJrev' := mul_le_mul_of_nonneg_left hJrev (by norm_num : (0 : ℝ) ≤ 2)
    change 0 ≤ w x * Q.quadratic x d ∧
      w x * F + w x * Q.quadratic x d ≤
        (b + 2*b*Λ + 2*b*Λ*n*M^2) * (F+G) ∧
      F+G ≤ (a⁻¹ + 2*(a*κ)⁻¹ + 2*n*M^2*a⁻¹) * (w x*F + w x*Q.quadratic x d)
    refine ⟨hwqn, ?_, ?_⟩
    · have ht : 0 ≤ b * G + 2*b*Λ*F + 2*b*Λ*n*M^2*G :=
        add_nonneg (add_nonneg (mul_nonneg hb.le hG)
          (mul_nonneg (by positivity) hF)) (mul_nonneg (by positivity) hG)
      nlinarith only [hWF, hWJ, hJG', ht]
    · have hWFpos : 0 ≤ w x * F := mul_nonneg (ha.le.trans hwx.1) hF
      have ht : 0 ≤ a⁻¹*(w x*Q.quadratic x d) + 2*(a*κ)⁻¹*(w x*F) +
          2*n*M^2*a⁻¹*(w x*Q.quadratic x d) :=
        add_nonneg (add_nonneg (mul_nonneg (inv_nonneg.mpr ha.le) hwqn)
          (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr (mul_pos ha hk).le)) hWFpos))
          (mul_nonneg (mul_nonneg (by positivity) (inv_nonneg.mpr ha.le)) hwqn)
      nlinarith
  · simp [hfx hxC, hgx, hxC, covariantFirst, InverseMetric.quadratic]

private theorem sqrt_sum_bounds (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a+b) ≤ Real.sqrt a + Real.sqrt b ∧
    Real.sqrt a + Real.sqrt b ≤ 2 * Real.sqrt (a+b) := by
  have hA := Real.sq_sqrt ha
  have hB := Real.sq_sqrt hb
  have hC := Real.sq_sqrt (add_nonneg ha hb)
  have hnA := Real.sqrt_nonneg a
  have hnB := Real.sqrt_nonneg b
  have hnC := Real.sqrt_nonneg (a+b)
  constructor <;> nlinarith [mul_nonneg hnA hnB, sq_nonneg (Real.sqrt a - Real.sqrt b)]

private theorem weighted_sq_integrable {n r : ℕ} (Ω : Opens (E n))
    (w : E n → ℝ) (hw : ContDiffOn ℝ ∞ w (Ω : Set (E n)))
    (hwpos : ∀ x ∈ (Ω : Set (E n)), 0 < w x) (f : E n → V r)
    (hf : MemLp f 2 (KPChartL2.weightedMeasure n (Ω : Set (E n)) w)) :
    Integrable (fun x => w x * ‖f x‖ ^ 2) (volume.restrict (Ω : Set (E n))) := by
  have hd : AEMeasurable (fun x => ENNReal.ofReal (w x)) (volume.restrict (Ω : Set (E n))) :=
    (hw.continuousOn.aemeasurable Ω.isOpen.measurableSet).ennreal_ofReal
  have hh := (integrable_withDensity_iff_integrable_smul₀' hd
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp
    (hf.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))
  convert hh.congr (show (fun x => (ENNReal.ofReal (w x)).toReal • ‖f x‖ ^ 2) =ᵐ[
      volume.restrict (Ω : Set (E n))] (fun x => w x * ‖f x‖ ^ 2) from ?_)
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  simp [ENNReal.toReal_ofReal (hwpos x hx).le]

end KPCompactInteriorH1

open KPCompactInteriorH1 MeasureTheory TopologicalSpace
open scoped ContDiff

theorem kp_cont_compact_h1_metric_bounds {n r : ℕ} (Ω : Opens (E n))
    (C : Set (E n)) (hC : IsCompact C) (hCΩ : C ⊆ (Ω : Set (E n)))
    (w : E n → ℝ) (hw : ContDiffOn ℝ ∞ w (Ω : Set (E n)))
    (hwpos : ∀ x ∈ (Ω : Set (E n)), 0 < w x)
    (Q : InverseMetric Ω) (A : Connection (r := r) Ω) :
    ∃ c C' : ℝ, 0 < c ∧ 0 < C' ∧
      ∀ (f : E n → V r) (g : Fin n → E n → V r)
        (hfsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), x ∉ C → f x = 0)
        (hgsupp : ∀ j, ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), x ∉ C → g j x = 0)
        (h0 : FiniteH0 (Ω : Set (E n)) f g),
        let hW := (compact_finiteH0_iff_finiteHw Ω C hC hCΩ w hw hwpos Q A f g
          h0.1.aestronglyMeasurable (fun j => (h0.2 j).aestronglyMeasurable)
          hfsupp hgsupp).mp h0
        c * H0 (Ω : Set (E n)) f g h0 ≤ Hw (Ω : Set (E n)) w Q A f g hW ∧
          Hw (Ω : Set (E n)) w Q A f g hW ≤ C' * H0 (Ω : Set (E n)) f g h0 := by
  obtain ⟨a, b, κ, Λ, M, ha, hb, hk, hl, hM, hbound⟩ :=
    exists_compact_metric_bounds Ω C hC hCΩ w hw hwpos Q A
  let B := b + 2 * b * Λ + 2 * b * Λ * n * M ^ 2
  let D := a⁻¹ + 2 * (a * κ)⁻¹ + 2 * n * M ^ 2 * a⁻¹
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨(2 * Real.sqrt D)⁻¹, 2 * Real.sqrt B,
    inv_pos.mpr (mul_pos (by norm_num) (Real.sqrt_pos.mpr hD)),
    mul_pos (by norm_num) (Real.sqrt_pos.mpr hB), ?_⟩
  intro f g hfsupp hgsupp h0
  dsimp only
  let hW := (compact_finiteH0_iff_finiteHw Ω C hC hCΩ w hw hwpos Q A f g
    h0.1.aestronglyMeasurable (fun j => (h0.2 j).aestronglyMeasurable)
    hfsupp hgsupp).mp h0
  let μ := volume.restrict (Ω : Set (E n))
  let F := ∫ x, ‖f x‖ ^ 2 ∂μ
  let G := ∫ x, (∑ j, ‖g j x‖ ^ 2) ∂μ
  let U := ∫ x, w x * ‖f x‖ ^ 2 ∂μ
  let T := ∫ x, w x * Q.quadratic x (fun j => covariantFirst A f g j x) ∂μ
  have hfI : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    h0.1.integrable_norm_pow (by norm_num)
  have hgI : ∀ j, Integrable (fun x => ‖g j x‖ ^ 2) μ := fun j =>
    (h0.2 j).integrable_norm_pow (by norm_num)
  have hGI : Integrable (fun x => ∑ j, ‖g j x‖ ^ 2) μ :=
    integrable_finset_sum _ (fun j _ => hgI j)
  have hUI : Integrable (fun x => w x * ‖f x‖ ^ 2) μ :=
    weighted_sq_integrable Ω w hw hwpos f hW.1
  have hTI : Integrable (fun x => w x * Q.quadratic x (fun j => covariantFirst A f g j x)) μ := hW.2
  have hpoint := density_bounds Ω C w Q A a b κ Λ M ha hb hk hl hM hbound f g hfsupp hgsupp
  have hF : 0 ≤ F := integral_nonneg fun _ => sq_nonneg _
  have hG : 0 ≤ G := integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hU : 0 ≤ U := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
    exact mul_nonneg (hwpos x hx).le (sq_nonneg _)
  have hT : 0 ≤ T := integral_nonneg_of_ae (hpoint.mono fun x hx => hx.1)
  have hupper : U + T ≤ B * (F + G) := by
    have hh := integral_mono_ae (hUI.add hTI) ((hfI.add hGI).const_mul B)
      (hpoint.mono fun x hx => hx.2.1)
    simpa only [Pi.add_apply, integral_add hUI hTI, integral_const_mul, integral_add hfI hGI] using hh
  have hlower : F + G ≤ D * (U + T) := by
    have hh := integral_mono_ae (hfI.add hGI) ((hUI.add hTI).const_mul D)
      (hpoint.mono fun x hx => hx.2.2)
    simpa only [Pi.add_apply, integral_add hUI hTI, integral_const_mul, integral_add hfI hGI] using hh
  have h0eq : H0 (Ω : Set (E n)) f g h0 = Real.sqrt F + Real.sqrt G := by
    unfold H0 l2Norm
    congr 1
    rw [show G = ∑ j, ∫ x, ‖g j x‖ ^ 2 ∂μ from integral_finset_sum _ (fun j _ => hgI j)]
    apply congrArg Real.sqrt
    apply Finset.sum_congr rfl
    intro j hj
    exact Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  have hWeq : Hw (Ω : Set (E n)) w Q A f g hW = Real.sqrt U + Real.sqrt T := by
    unfold Hw l2Norm
    rw [weighted_sq_integral Ω w hw hwpos f]
  have h0bounds := sqrt_sum_bounds F G hF hG
  have hWbounds := sqrt_sum_bounds U T hU hT
  have hupper_sqrt : Real.sqrt (U+T) ≤ Real.sqrt B * Real.sqrt (F+G) := by
    simpa only [Real.sqrt_mul hB.le] using Real.sqrt_le_sqrt hupper
  have hlower_sqrt : Real.sqrt (F+G) ≤ Real.sqrt D * Real.sqrt (U+T) := by
    simpa only [Real.sqrt_mul hD.le] using Real.sqrt_le_sqrt hlower
  rw [h0eq, hWeq]
  constructor
  · apply (inv_mul_le_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.mpr hD))).mpr
    have hh := mul_le_mul_of_nonneg_left hWbounds.1 (Real.sqrt_nonneg D)
    nlinarith only [h0bounds.2, hlower_sqrt, hh]
  · have hh := mul_le_mul_of_nonneg_left h0bounds.1 (Real.sqrt_nonneg B)
    nlinarith only [hWbounds.2, hupper_sqrt, hh]

end DedekindZetaZeroFree

end
