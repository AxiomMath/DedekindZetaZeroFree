module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.SourceJetVerticalBounds
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.RegularizedCompactRegionBounds
public import DedekindZetaZeroFree.Analysis.Gamma.QuotientBounds

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve

def B (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  (D : ℂ) ^ (s - 1 / 2) * Complex.Gammaℂ s ^ r *
    ((Complex.Gammaℂ (1 - s))⁻¹) ^ (r - 1) * Vendor.originMellinQ h (1 - s)

private lemma kernelFactor_diff (D : ℝ) (r : ℕ) (hD : 0 < D)
    (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => (D : ℂ) ^ (z - 1 / 2) *
      Complex.Gammaℂ z ^ r * (Complex.Gammaℂ (1 - z))⁻¹ ^ (r - 1)) s := by
  have hGam : DifferentiableAt ℂ Complex.Gamma s := by
    refine Complex.differentiableAt_Gamma s fun m h => ?_
    have h2 : s.re = -(m : ℝ) := by rw [h]; simp
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [h2] at hs
    linarith
  have hnum : DifferentiableAt ℂ (fun z : ℂ => Complex.Gammaℂ z) s := by
    have heq : (fun z : ℂ => Complex.Gammaℂ z) =
        fun z : ℂ => (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-z) * Complex.Gamma z := by
      funext z; rw [Complex.Gammaℂ_def]
    rw [heq]
    exact ((differentiableAt_const (2 : ℂ)).mul (differentiableAt_id.neg.const_cpow
      (Or.inl (by norm_num : (2 * (Real.pi : ℂ)) ≠ 0)))).mul hGam
  have hden : DifferentiableAt ℂ (fun z : ℂ => (Complex.Gammaℂ (1 - z))⁻¹) s :=
    Complex.differentiable_Gammaℂ_inv.differentiableAt.comp s
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (D : ℂ) ^ (z - 1 / 2)) s :=
    (differentiableAt_id.sub (differentiableAt_const _)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
  exact (hpow.mul (hnum.pow r)).mul (hden.pow (r - 1))

theorem B_differentiableOn (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) :
    DifferentiableOn ℂ (B D r h) {s : ℂ | 0 < s.re} := by
  intro s hs
  exact ((kernelFactor_diff D r hD s hs).mul
    ((Vendor.originMellinQ_differentiable h hh hhc).differentiableAt.comp s
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id))).differentiableWithinAt

private lemma kernel_S_mono (b : ℝ) (m n : ℕ) (h : ℝ → ℂ)
    (hmn : m ≤ n) : Vendor.S b m h ≤ Vendor.S b n h := by
  unfold Vendor.S
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hmn 1))
    (fun i _ _ => Real.sSup_nonneg fun y ⟨x, _, hy⟩ => hy ▸ norm_nonneg _)

private lemma kernel_power_bound (D a v : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Set.Icc a v →
      ‖(D : ℂ) ^ (s - 1 / 2)‖ ≤ C := by
  refine ⟨max (D ^ (a - 1 / 2)) (D ^ (v - 1 / 2)),
    lt_of_lt_of_le (Real.rpow_pos_of_pos hD _) (le_max_left _ _), ?_⟩
  intro s hs
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]
  have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
  rw [hre]
  rcases le_total 1 D with h1 | h1
  · exact (Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hs.2])).trans
      (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_exponent_ge hD h1 (by linarith [hs.1])).trans
      (le_max_left _ _)

private lemma kernel_small_factor_bound (D : ℝ) (r : ℕ) (a v : ℝ)
    (hD : 0 < D) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc a v, ∀ t : ℝ, |t| ≤ 1 →
      ‖(D : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1 / 2) *
        Complex.Gammaℂ ((σ : ℂ) + (t : ℂ) * Complex.I) ^ r *
        (Complex.Gammaℂ (1 - ((σ : ℂ) + (t : ℂ) * Complex.I)))⁻¹ ^ (r - 1)‖ ≤ C := by
  let f : ℂ → ℂ := fun z : ℂ => (D : ℂ) ^ (z - 1 / 2) * Complex.Gammaℂ z ^ r *
    (Complex.Gammaℂ (1 - z))⁻¹ ^ (r - 1)
  have hc : ContinuousOn (fun p : ℝ × ℝ => f ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))
      (Set.Icc a v ×ˢ Set.Icc (-1 : ℝ) 1) := by
    intro p hp
    have hs : 0 < ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).re := by
      simp only [Set.mem_prod, Set.mem_Icc] at hp
      simpa using lt_of_lt_of_le ha hp.1.1
    have hf : ContinuousAt f ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) :=
      (kernelFactor_diff D r hD _ hs).continuousAt
    have hg : ContinuousAt (fun q : ℝ × ℝ =>
        (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) p := by fun_prop
    exact (ContinuousAt.comp (f := fun q : ℝ × ℝ =>
      (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) (x := p) hf hg).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨max C 0 + 1, by positivity, fun σ hσ t ht => ?_⟩
  exact (hC (σ, t) ⟨hσ, by simpa [Set.mem_Icc, abs_le] using ht⟩).trans
    (by linarith [le_max_left C 0])

private lemma kernel_large_identity (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hr : 1 ≤ r) (s : ℂ) (hs : s.im ≠ 0) :
    B D r h s = (D : ℂ) ^ (s - 1 / 2) *
      (Complex.Gammaℂ s / Complex.Gammaℂ (1 - s)) ^ r *
      (Complex.Gammaℂ (1 - s) * Vendor.originMellinQ h (1 - s)) := by
  have hne : Complex.Gammaℂ (1 - s) ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_
    · exact Complex.cpow_ne_zero_iff.mpr
        (Or.inl (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    · intro h0
      rw [Complex.Gamma_eq_zero_iff] at h0
      obtain ⟨m, hm⟩ := h0
      apply hs
      have him := congrArg Complex.im hm
      simpa using him
  have hp : (Complex.Gammaℂ (1 - s))⁻¹ ^ r * Complex.Gammaℂ (1 - s) =
      (Complex.Gammaℂ (1 - s))⁻¹ ^ (r - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hr, pow_succ]
    simp [mul_assoc, hne]
  simp only [B, div_eq_mul_inv, mul_pow]
  calc _ = (D : ℂ) ^ (s - 1 * 2⁻¹) * Complex.Gammaℂ s ^ r *
      ((Complex.Gammaℂ (1 - s))⁻¹ ^ r * Complex.Gammaℂ (1 - s)) *
        Vendor.originMellinQ h (1 - s) := by rw [hp]
    _ = _ := by ring

theorem B_uniform_rapid_bound (D : ℝ) (r : ℕ) (b a v : ℝ) (k : ℕ)
    (hD : 0 < D) (hr : 1 ≤ r) (hb : 0 < b) (ha : 0 < a) (hav : a ≤ v) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
        (∀ x : ℝ, b < x → h x = 0) →
        ∀ (σ : ℝ), σ ∈ Set.Icc a v → ∀ t : ℝ,
          (1 + |t|) ^ k * ‖B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * Vendor.S b N h := by
  obtain ⟨CD, hCD, hpower⟩ := kernel_power_bound D a v hD
  obtain ⟨CG, l, hCG, hgamma⟩ := Vendor.gammaQuotient_polynomial_bound ha hav r
  obtain ⟨NH, CH, hCH, hlarge⟩ := Vendor.originMellin_source_vertical_bound b hb
    (1 - v) (1 - a) (by linarith) (k + l)
  obtain ⟨NQ, CQ, hCQ, hsmall⟩ := Vendor.originMellinQ_rectangle_source_bound b hb
    (1 - v) (1 - a)
  obtain ⟨CF, hCF, hfactor⟩ := kernel_small_factor_bound D r a v hD ha
  let Cbig := CD * CG * CH
  let Csmall := (2 : ℝ) ^ k * CF * CQ
  have hbig : 0 < Cbig := by dsimp [Cbig]; positivity
  have hsm : 0 < Csmall := by dsimp [Csmall]; positivity
  refine ⟨max NH NQ, Cbig + Csmall, by positivity, ?_⟩
  intro h hh hhc hpos σ hσ t
  have hSH : Vendor.S b NH h ≤ Vendor.S b (max NH NQ) h :=
    kernel_S_mono b NH _ h (le_max_left _ _)
  have hSQ : Vendor.S b NQ h ≤ Vendor.S b (max NH NQ) h :=
    kernel_S_mono b NQ _ h (le_max_right _ _)
  have hS : 0 ≤ Vendor.S b (max NH NQ) h := Vendor.S_nonneg b hb _ h hh
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hreflect : 1 - s = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    dsimp [s]; push_cast; ring
  have hσ' : 1 - σ ∈ Set.Icc (1 - v) (1 - a) := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  by_cases ht : 1 ≤ |t|
  · have hi : s.im ≠ 0 := by rw [hsim]; exact abs_pos.mp (lt_of_lt_of_le zero_lt_one ht)
    have hp := hpower s (by rwa [hsre])
    have hg := hgamma s (by rw [hsre]; exact hσ.1) (by rw [hsre]; exact hσ.2)
    rw [hsim] at hg
    have hH := hlarge h hh hhc hpos (1 - σ) (-t) hσ' (by simpa using ht)
    rw [abs_neg, ← hreflect] at hH
    change (1 + |t|) ^ k * ‖B D r h s‖ ≤ _
    rw [kernel_large_identity D r h hr s hi, norm_mul, norm_mul]
    calc
      (1 + |t|) ^ k *
          (‖(D : ℂ) ^ (s - 1 / 2)‖ *
            ‖(Complex.Gammaℂ s / Complex.Gammaℂ (1 - s)) ^ r‖ *
            ‖Complex.Gammaℂ (1 - s) * Vendor.originMellinQ h (1 - s)‖)
        ≤ (1 + |t|) ^ k * (CD * (CG * (1 + |t|) ^ l) *
            ‖Complex.Gammaℂ (1 - s) * Vendor.originMellinQ h (1 - s)‖) := by
              gcongr
      _ = CD * CG * ((1 + |t|) ^ (k + l) *
            ‖Complex.Gammaℂ (1 - s) * Vendor.originMellinQ h (1 - s)‖) := by
              rw [pow_add]; ring
      _ ≤ CD * CG * (CH * Vendor.S b NH h) :=
        mul_le_mul_of_nonneg_left hH (by positivity)
      _ = Cbig * Vendor.S b NH h := by dsimp [Cbig]; ring
      _ ≤ Cbig * Vendor.S b (max NH NQ) h :=
        mul_le_mul_of_nonneg_left hSH hbig.le
      _ ≤ (Cbig + Csmall) * Vendor.S b (max NH NQ) h := by
        gcongr; linarith
  · have ht1 : |t| ≤ 1 := le_of_lt (lt_of_not_ge ht)
    have hF := hfactor σ hσ t ht1
    have hQ := hsmall h hh hhc hpos (1 - s)
      (by simp [hsre]; linarith [hσ.2]) (by simp [hsre]; linarith [hσ.1])
      (by simp [hsim]; exact ht1)
    have hk : (1 + |t|) ^ k ≤ (2 : ℝ) ^ k := by gcongr; linarith
    change (1 + |t|) ^ k * ‖B D r h s‖ ≤ _
    unfold B
    rw [norm_mul]
    calc
      (1 + |t|) ^ k *
          (‖(D : ℂ) ^ (s - 1 / 2) * Complex.Gammaℂ s ^ r *
            (Complex.Gammaℂ (1 - s))⁻¹ ^ (r - 1)‖ *
            ‖Vendor.originMellinQ h (1 - s)‖)
        ≤ (2 : ℝ) ^ k * (CF * (CQ * Vendor.S b NQ h)) := by
          gcongr
      _ = Csmall * Vendor.S b NQ h := by dsimp [Csmall]; ring
      _ ≤ Csmall * Vendor.S b (max NH NQ) h :=
        mul_le_mul_of_nonneg_left hSQ hsm.le
      _ ≤ (Cbig + Csmall) * Vendor.S b (max NH NQ) h := by
        gcongr; linarith

theorem B_rapid_bound (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (a v : ℝ) (k : ℕ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (ha : 0 < a) (hav : a ≤ v) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ), σ ∈ Set.Icc a v → ∀ t : ℝ,
      (1 + |t|) ^ k * ‖B D r h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_iff_hasCompactSupport.mpr hhc
  obtain ⟨b, hb⟩ := hK.bddAbove
  have hb0 : 0 < max b 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hpos : ∀ x : ℝ, max b 1 < x → h x = 0 := by
    intro x hx
    apply hK0 x
    intro hxK
    exact absurd (hb hxK) (not_le.mpr (lt_of_le_of_lt (le_max_left _ _) hx))
  obtain ⟨N, C, hC, hbound⟩ := B_uniform_rapid_bound D r (max b 1) a v k hD hr hb0 ha hav
  have hS : 0 ≤ Vendor.S (max b 1) N h := Vendor.S_nonneg _ hb0 N h hh
  refine ⟨C * Vendor.S (max b 1) N h + 1, by positivity, ?_⟩
  intro σ hσ t
  exact (hbound h hh hhc hpos σ hσ t).trans (by linarith)

end DedekindZetaZeroFree.LargeSieve

end
