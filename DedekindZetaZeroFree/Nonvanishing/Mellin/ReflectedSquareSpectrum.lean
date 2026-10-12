module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.SpectralMultiplier
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.CompactSupportAndUniformFourierDecay
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.ReflectedSquareGammaDuplication

@[expose] public section

noncomputable section

open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve

def squareMellinSpectrum (D : ℝ) (r : ℕ) (W : ℝ → ℂ) (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * B D r W (s / 2)

def squareReflectionFactor (D : ℝ) (r : ℕ) (s : ℂ) : ℂ :=
  (D : ℂ) ^ (s - 1 / 2) *
    (Complex.Gammaℂ s * (Complex.Gammaℂ (1 - s))⁻¹) ^ r

def reflectedSquareSpectrum (D : ℝ) (r : ℕ) (W : ℝ → ℂ) (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (D : ℂ) ^ ((s - 1) / 2) *
    ((2 : ℂ) ^ (2 * s - 1) * Complex.Gammaℂ (s / 2) *
      (Complex.Gammaℂ (1 - s / 2))⁻¹) ^ r *
    mellin W ((1 + s) / 2)

theorem reflectedSquareSpectrum_differentiableOn
    (D : ℝ) (r : ℕ) (W : ℝ → ℂ) (a b : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hW : ContDiff ℝ ∞ W)
    (hsupp : Function.support W ⊆ Set.Icc a b)
    (ha : 0 < a) (hab : a < b) :
    DifferentiableOn ℂ (reflectedSquareSpectrum D r W) {s : ℂ | 0 < s.re} := by
  have hpow : Differentiable ℂ (fun s : ℂ => (D : ℂ) ^ ((s - 1) / 2)) :=
    ((differentiable_id.sub_const 1).div_const (2 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hD)))
  have hmel : Differentiable ℂ (fun s : ℂ => mellin W ((1 + s) / 2)) :=
    (Vendor.compact_mellin_differentiable W a b hW hsupp ha hab).comp
      (((differentiable_const (1 : ℂ)).add differentiable_id).div_const (2 : ℂ))
  exact (((differentiable_const (c := (1 / 2 : ℂ))).differentiableOn.mul
    hpow.differentiableOn).mul
    (Vendor.reflectedSquareGammaContinuation_differentiableOn.pow r)).mul hmel.differentiableOn

theorem reflectedSquareSpectrum_eq_of_im_ne_zero
    (D : ℝ) (r : ℕ) (W : ℝ → ℂ) (a b : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hW : ContDiff ℝ ∞ W)
    (hsupp : Function.support W ⊆ Set.Icc a b)
    (ha : 0 < a) (hab : a < b) (s : ℂ)
    (hs : 0 < s.re) (hsi : s.im ≠ 0) :
    reflectedSquareSpectrum D r W s =
      squareReflectionFactor D r s * squareMellinSpectrum D r W (1 - s) := by
  have hc : HasCompactSupport W :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have harg : 1 - (1 - s) / 2 = (1 + s) / 2 := by ring
  have hq := Vendor.originMellinQ_eq_mellin_div_Gammaℂ W hW hc ((1 + s) / 2)
    (by simp [Complex.div_re, Complex.add_re]; linarith)
  have hdup := Vendor.reflected_square_gamma_duplication s hsi
  have hDne : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hD)
  have hcp : (D : ℂ) ^ (s - 1 / 2) * (D : ℂ) ^ ((1 - s) / 2 - 1 / 2) =
      (D : ℂ) ^ ((s - 1) / 2) := by
    rw [← Complex.cpow_add _ _ hDne]
    congr 1
    ring
  unfold reflectedSquareSpectrum squareReflectionFactor squareMellinSpectrum B
  rw [harg, hq]
  have hpow : (Complex.Gammaℂ ((1 + s) / 2))⁻¹ ^ (r - 1) *
      (Complex.Gammaℂ ((1 + s) / 2))⁻¹ = (Complex.Gammaℂ ((1 + s) / 2))⁻¹ ^ r := by
    rw [← pow_succ, Nat.sub_add_cancel hr]

  have hgam : (Complex.Gammaℂ s * (Complex.Gammaℂ (1 - s))⁻¹) ^ r *
      Complex.Gammaℂ ((1 - s) / 2) ^ r *
      ((Complex.Gammaℂ ((1 + s) / 2))⁻¹ ^ (r - 1) *
        (Complex.Gammaℂ ((1 + s) / 2))⁻¹) =
      ((2 : ℂ) ^ (2 * s - 1) * Complex.Gammaℂ (s / 2) *
        (Complex.Gammaℂ (1 - s / 2))⁻¹) ^ r := by
    rw [hpow, ← mul_pow, ← mul_pow]
    apply congrArg (fun z : ℂ => z ^ r)
    calc
      _ = Complex.Gammaℂ s * Complex.Gammaℂ ((1 - s) / 2) /
          (Complex.Gammaℂ (1 - s) * Complex.Gammaℂ ((1 + s) / 2)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by rw [hdup, div_eq_mul_inv]
  rw [div_eq_mul_inv]
  calc
    _ = (1 / 2 : ℂ) * ((D : ℂ) ^ (s - 1 / 2) *
        (D : ℂ) ^ ((1 - s) / 2 - 1 / 2)) *
        ((Complex.Gammaℂ s * (Complex.Gammaℂ (1 - s))⁻¹) ^ r *
        Complex.Gammaℂ ((1 - s) / 2) ^ r *
        ((Complex.Gammaℂ ((1 + s) / 2))⁻¹ ^ (r - 1) *
        (Complex.Gammaℂ ((1 + s) / 2))⁻¹)) * mellin W ((1 + s) / 2) := by
      rw [hcp, hgam]
      simp only [div_eq_mul_inv]
    _ = _ := by simp only [div_eq_mul_inv]; ring

private lemma square_S_mono (b : ℝ) (m n : ℕ) (W : ℝ → ℂ)
    (hmn : m ≤ n) : Vendor.S b m W ≤ Vendor.S b n W := by
  unfold Vendor.S
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hmn 1))
    (fun i _ _ => Real.sSup_nonneg fun y ⟨x, _, hy⟩ => hy ▸ norm_nonneg _)

private lemma square_cpow_strip_bound (D u v : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Set.Icc u v → ‖(D : ℂ) ^ s‖ ≤ C := by
  refine ⟨max (D ^ u) (D ^ v),
    lt_of_lt_of_le (Real.rpow_pos_of_pos hD _) (le_max_left _ _), ?_⟩
  intro s hs
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]
  rcases le_total 1 D with h1 | h1
  · exact (Real.rpow_le_rpow_of_exponent_le h1 hs.2).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_exponent_ge hD h1 hs.1).trans (le_max_left _ _)

private lemma square_gamma_diff_pos (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℂ s := by
  have hGam : DifferentiableAt ℂ Complex.Gamma s := by
    refine Complex.differentiableAt_Gamma s fun m h => ?_
    have h2 : s.re = -(m : ℝ) := by rw [h]; simp
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  unfold Complex.Gammaℂ
  exact ((differentiableAt_const (2 : ℂ)).mul (differentiableAt_id.neg.const_cpow
    (Or.inl (by norm_num : (2 * (Real.pi : ℂ)) ≠ 0)))).mul hGam

private lemma square_small_factor_bound (D : ℝ) (r : ℕ) (u v : ℝ)
    (hD : 0 < D) (hu : 0 < u) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc u v, ∀ t : ℝ, |t| ≤ 2 →
      ‖(1 / 2 : ℂ) * (D : ℂ) ^ ((((σ : ℂ) + (t : ℂ) * Complex.I) - 1) / 2) *
        Vendor.reflectedSquareGammaContinuation ((σ : ℂ) + (t : ℂ) * Complex.I) ^ r *
        Complex.Gammaℂ ((1 + ((σ : ℂ) + (t : ℂ) * Complex.I)) / 2)‖ ≤ C := by
  let f : ℂ → ℂ := fun s => (1 / 2 : ℂ) * (D : ℂ) ^ ((s - 1) / 2) *
    Vendor.reflectedSquareGammaContinuation s ^ r * Complex.Gammaℂ ((1 + s) / 2)
  have hp : Differentiable ℂ (fun s : ℂ => (D : ℂ) ^ ((s - 1) / 2)) :=
    ((differentiable_id.sub_const 1).div_const (2 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hD)))
  have hc : ContinuousOn (fun p : ℝ × ℝ => f ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))
      (Set.Icc u v ×ˢ Set.Icc (-2 : ℝ) 2) := by
    intro p hp'
    let s : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
    have hs : 0 < s.re := by
      simpa [s] using lt_of_lt_of_le hu hp'.1.1
    have hg : DifferentiableAt ℂ Vendor.reflectedSquareGammaContinuation s :=
      Vendor.reflectedSquareGammaContinuation_differentiableOn.differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
    have hG : DifferentiableAt ℂ (fun s : ℂ => Complex.Gammaℂ ((1 + s) / 2)) s :=
      (square_gamma_diff_pos _ (by simp; linarith)).comp s
        (((differentiableAt_const (1 : ℂ)).add differentiableAt_id).div_const (2 : ℂ))
    have hf : ContinuousAt f s :=
      ((((differentiableAt_const (1 / 2 : ℂ)).mul (hp s)).mul (hg.pow r)).mul hG).continuousAt
    have hz : ContinuousAt (fun q : ℝ × ℝ =>
        (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) p := by fun_prop
    exact (ContinuousAt.comp (f := fun q : ℝ × ℝ =>
      (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) (x := p) hf hz).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨max C 0 + 1, by positivity, fun σ hσ t ht => ?_⟩
  exact (hC (σ, t) ⟨hσ, by simpa [Set.mem_Icc, abs_le] using ht⟩).trans
    (by linarith [le_max_left C 0])

theorem reflectedSquareSpectrum_uniform_rapid_bound
    (D : ℝ) (r : ℕ) (a b u v : ℝ) (n : ℕ)
    (hD : 0 < D) (hr : 1 ≤ r) (ha : 0 < a) (hab : a < b)
    (hu : 0 < u) (huv : u ≤ v) :
    ∃ (N : ℕ) (C₀ : ℝ), 0 < C₀ ∧
      ∀ (W : ℝ → ℂ), ContDiff ℝ ∞ W →
        Function.support W ⊆ Set.Icc a b →
        ∀ (σ : ℝ), σ ∈ Set.Icc u v → ∀ (t : ℝ),
          (1 + |t|) ^ n *
            ‖reflectedSquareSpectrum D r W ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
              C₀ * Vendor.S b N W := by
  have hb : 0 < b := lt_trans ha hab
  obtain ⟨CD, hCD, hpower⟩ := square_cpow_strip_bound D ((u - 1) / 2) ((v - 1) / 2) hD
  obtain ⟨C2, hC2, htwo⟩ := square_cpow_strip_bound 2 (2 * u - 1) (2 * v - 1) (by norm_num)
  obtain ⟨CG, l, hCG, hgamma⟩ := Vendor.gammaQuotient_polynomial_bound
    (a := u / 2) (b := v / 2) (by positivity) (by linarith) r
  obtain ⟨NH, CH, hCH, hlarge⟩ := Vendor.originMellin_source_vertical_bound b hb
    ((1 + u) / 2) ((1 + v) / 2) (by linarith) (n + l)
  obtain ⟨NQ, CQ, hCQ, hsmall⟩ := Vendor.originMellinQ_rectangle_source_bound b hb
    ((1 + u) / 2) ((1 + v) / 2)
  obtain ⟨CF, hCF, hfactor⟩ := square_small_factor_bound D r u v hD hu
  let Cbig := (2 : ℝ) ^ n * (1 / 2 : ℝ) * CD * C2 ^ r * CG * CH
  let Csmall := (3 : ℝ) ^ n * CF * CQ
  have hbig : 0 < Cbig := by dsimp [Cbig]; positivity
  have hsm : 0 < Csmall := by dsimp [Csmall]; positivity
  refine ⟨max NH NQ, Cbig + Csmall, by positivity, ?_⟩
  intro W hW hsupp σ hσ t
  have hc : HasCompactSupport W :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hpos : Vendor.PositiveSideSupport b W := by
    intro x hx
    by_contra h
    exact (not_le.mpr hx) (hsupp h).2
  have hSH := square_S_mono b NH (max NH NQ) W (le_max_left _ _)
  have hSQ := square_S_mono b NQ (max NH NQ) W (le_max_right _ _)
  have hS := Vendor.S_nonneg b hb (max NH NQ) W hW
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hzre : ((1 + s) / 2).re = (1 + σ) / 2 := by simp [hsre]
  have hzim : ((1 + s) / 2).im = t / 2 := by simp [hsim]
  have hz : (1 + s) / 2 = (((1 + σ) / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
    dsimp [s]; push_cast; ring
  have hzpos : 0 < ((1 + s) / 2).re := by rw [hzre]; linarith [hσ.1]
  have hσ' : (1 + σ) / 2 ∈ Set.Icc ((1 + u) / 2) ((1 + v) / 2) :=
    ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hmell := Vendor.Gammaℂ_mul_originMellinQ_eq_mellin W hW hc ((1 + s) / 2) hzpos
  by_cases ht : 2 ≤ |t|
  · have ht' : 1 ≤ |t / 2| := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
    have hp := hpower ((s - 1) / 2) (by simp [hsre]; constructor <;> linarith [hσ.1, hσ.2])
    have h2 := htwo (2 * s - 1) (by simp [hsre]; constructor <;> linarith [hσ.1, hσ.2])
    have hg := hgamma (s / 2) (by simp [hsre]; linarith [hσ.1])
      (by simp [hsre]; linarith [hσ.2])
    have hH := hlarge W hW hc hpos ((1 + σ) / 2) (t / 2) hσ' ht'
    rw [← hz, hmell] at hH
    have hk : (1 + |t|) ^ n ≤ (2 : ℝ) ^ n * (1 + |t / 2|) ^ n := by
      rw [← mul_pow]
      gcongr
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hg' : ‖((2 : ℂ) ^ (2 * s - 1) * Complex.Gammaℂ (s / 2) *
        (Complex.Gammaℂ (1 - s / 2))⁻¹) ^ r‖ ≤
          C2 ^ r * (CG * (1 + |t / 2|) ^ l) := by
      have heq : (2 : ℂ) ^ (2 * s - 1) * Complex.Gammaℂ (s / 2) *
          (Complex.Gammaℂ (1 - s / 2))⁻¹ =
            (2 : ℂ) ^ (2 * s - 1) * (Complex.Gammaℂ (s / 2) / Complex.Gammaℂ (1 - s / 2)) := by
        simp only [div_eq_mul_inv, mul_assoc]
      rw [heq, mul_pow, norm_mul, norm_pow]
      have hi : (s / 2).im = t / 2 := by simp [hsim]
      rw [hi] at hg
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h2 r) hg
        (norm_nonneg _) (by positivity)
    change (1 + |t|) ^ n * ‖reflectedSquareSpectrum D r W s‖ ≤ _
    unfold reflectedSquareSpectrum
    rw [norm_mul, norm_mul, norm_mul]
    have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hhalf]
    calc
      (1 + |t|) ^ n * ((1 / 2 : ℝ) * ‖(D : ℂ) ^ ((s - 1) / 2)‖ *
          ‖((2 : ℂ) ^ (2 * s - 1) * Complex.Gammaℂ (s / 2) *
            (Complex.Gammaℂ (1 - s / 2))⁻¹) ^ r‖ * ‖mellin W ((1 + s) / 2)‖)
        ≤ ((2 : ℝ) ^ n * (1 + |t / 2|) ^ n) *
          ((1 / 2 : ℝ) * CD * (C2 ^ r * (CG * (1 + |t / 2|) ^ l)) *
            ‖mellin W ((1 + s) / 2)‖) := by gcongr
      _ = (2 : ℝ) ^ n * (1 / 2 : ℝ) * CD * C2 ^ r * CG *
          ((1 + |t / 2|) ^ (n + l) * ‖mellin W ((1 + s) / 2)‖) := by
        rw [pow_add]; ring
      _ ≤ (2 : ℝ) ^ n * (1 / 2 : ℝ) * CD * C2 ^ r * CG * (CH * Vendor.S b NH W) :=
        mul_le_mul_of_nonneg_left hH (by positivity)
      _ = Cbig * Vendor.S b NH W := by dsimp [Cbig]; ring
      _ ≤ Cbig * Vendor.S b (max NH NQ) W := mul_le_mul_of_nonneg_left hSH hbig.le
      _ ≤ (Cbig + Csmall) * Vendor.S b (max NH NQ) W := by gcongr; linarith
  · have ht1 : |t| ≤ 2 := le_of_lt (lt_of_not_ge ht)
    have hF := hfactor σ hσ t ht1
    have hQ := hsmall W hW hc hpos ((1 + s) / 2)
      (by rw [hzre]; exact hσ'.1) (by rw [hzre]; exact hσ'.2)
      (by rw [hzim, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith)
    have hk : (1 + |t|) ^ n ≤ (3 : ℝ) ^ n := by gcongr; linarith
    have hid : reflectedSquareSpectrum D r W s =
        ((1 / 2 : ℂ) * (D : ℂ) ^ ((s - 1) / 2) *
          Vendor.reflectedSquareGammaContinuation s ^ r * Complex.Gammaℂ ((1 + s) / 2)) *
            Vendor.originMellinQ W ((1 + s) / 2) := by
      unfold reflectedSquareSpectrum Vendor.reflectedSquareGammaContinuation
      rw [← hmell]; ring
    change (1 + |t|) ^ n * ‖reflectedSquareSpectrum D r W s‖ ≤ _
    rw [hid, norm_mul]
    calc
      _ ≤ (3 : ℝ) ^ n * (CF * (CQ * Vendor.S b NQ W)) := by gcongr
      _ = Csmall * Vendor.S b NQ W := by dsimp [Csmall]; ring
      _ ≤ Csmall * Vendor.S b (max NH NQ) W := mul_le_mul_of_nonneg_left hSQ hsm.le
      _ ≤ (Cbig + Csmall) * Vendor.S b (max NH NQ) W := by gcongr; linarith

theorem reflectedSquareSpectrum_rapid_bound
    (D : ℝ) (r : ℕ) (W : ℝ → ℂ) (a b u v : ℝ) (n : ℕ)
    (hD : 0 < D) (hr : 1 ≤ r) (hW : ContDiff ℝ ∞ W)
    (hsupp : Function.support W ⊆ Set.Icc a b)
    (ha : 0 < a) (hab : a < b) (hu : 0 < u) (huv : u ≤ v) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ), σ ∈ Set.Icc u v → ∀ (t : ℝ),
      (1 + |t|) ^ n *
        ‖reflectedSquareSpectrum D r W ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨N, C₀, hC₀, hbound⟩ :=
    reflectedSquareSpectrum_uniform_rapid_bound D r a b u v n hD hr ha hab hu huv
  have hS := Vendor.S_nonneg b (by linarith) N W hW
  refine ⟨C₀ * Vendor.S b N W + 1, by positivity, ?_⟩
  intro σ hσ t
  exact (hbound W hW hsupp σ hσ t).trans (by linarith)

end DedekindZetaZeroFree.LargeSieve

end
