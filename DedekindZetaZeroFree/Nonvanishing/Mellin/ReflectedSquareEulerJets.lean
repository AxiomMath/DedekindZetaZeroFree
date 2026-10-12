module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SquareTransformCoprimeSummationAndResidues
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.InverseSpectrumEulerDerivatives

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.LargeSieve.ReflectedSquareDerivatives

def inverseWeight (D : ℝ) (r : ℕ) (W : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then mellinInv 2 (reflectedSquareSpectrum D r W) x else 0

end DedekindZetaZeroFree.LargeSieve.ReflectedSquareDerivatives

end

end

section

noncomputable section
open scoped Classical ContDiff
namespace DedekindZetaZeroFree.LargeSieve.ReflectedSquareDerivatives

theorem identify_inverseWeight
    (D : ℝ) (r : ℕ) (W : ℝ → ℂ) (a b : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hW : ContDiff ℝ ∞ W)
    (hsupp : Function.support W ⊆ Set.Icc a b) (ha : 0 < a) (hab : a < b) :
    SquareSecondPass.reflectedTransform D r W = inverseWeight D r W := by
  have hc : HasCompactSupport W :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hlines : ∀ (c d x : ℝ), 0 < c → c < 3 → 0 < d → d < 3 → 0 < x →
      mellinInv c (reflectedSquareSpectrum D r W) x =
        mellinInv d (reflectedSquareSpectrum D r W) x := by
    apply (Vendor.LogReflection.strip_inverse_api
      (reflectedSquareSpectrum D r W) 0 3 ?_ ?_).1
    · intro s hs _
      exact (reflectedSquareSpectrum_differentiableOn D r W a b hD hr hW hsupp ha hab).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
    · intro u v hu huv _ n
      obtain ⟨C, hC, hbound⟩ :=
        reflectedSquareSpectrum_rapid_bound D r W a b u v n hD hr hW hsupp ha hab hu huv
      exact ⟨C, hC.le, fun σ t hσ hσ' _ => hbound σ ⟨hσ, hσ'⟩ t⟩
  have hline (x : ℝ) (hx : 0 < x) :
      mellinInv (3 / 2) (SquareSecondPass.reflectedSpectrum D r W) x =
        mellinInv (3 / 2) (reflectedSquareSpectrum D r W) x := by
    unfold mellinInv
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume : MeasureTheory.Measure ℝ) 0]
      with t ht
    have hsi : (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).im ≠ 0 := by
      simpa using ht
    have hreg := reflectedSquareSpectrum_eq_of_im_ne_zero D r W a b hD hr hW hsupp ha hab
      (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) (by norm_num [Complex.add_re, Complex.mul_re]) hsi
    have hid : SquareSecondPass.reflectedSpectrum D r W
        (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      squareReflectionFactor D r (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
        squareMellinSpectrum D r W (1 - (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
      simp only [SquareSecondPass.reflectedSpectrum, SquareSecondPass.spectrum,
        squareReflectionFactor, squareMellinSpectrum]
      ring
    rw [hreg, hid]
  funext x
  by_cases hx : 0 < x
  · simp only [SquareSecondPass.reflectedTransform, inverseWeight, if_pos hx]
    exact (hline x hx).trans (hlines (3 / 2) 2 x (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hx)
  · simp [SquareSecondPass.reflectedTransform, inverseWeight, hx]

end DedekindZetaZeroFree.LargeSieve.ReflectedSquareDerivatives

end

end

section

noncomputable section
open scoped Classical ContDiff
namespace DedekindZetaZeroFree.LargeSieve.ReflectedSquareDerivatives

private lemma rapid (D : ℝ) (r : ℕ) (W : ℝ → ℂ) (a b : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hW : ContDiff ℝ ∞ W)
    (hsupp : Function.support W ⊆ Set.Icc a b) (ha : 0 < a) (hab : a < b)
    (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, u ≤ σ → σ ≤ v → 1 ≤ |t| →
      (1 + |t|) ^ n * ‖reflectedSquareSpectrum D r W ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    reflectedSquareSpectrum_rapid_bound D r W a b u v n hD hr hW hsupp ha hab hu huv
  exact ⟨C, hC.le, fun σ t hσ hσv _ => hbound σ ⟨hσ, hσv⟩ t⟩

private lemma weighted_integrable (D : ℝ) (r : ℕ) (W : ℝ → ℂ) (a b : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hW : ContDiff ℝ ∞ W)
    (hsupp : Function.support W ⊆ Set.Icc a b) (ha : 0 < a) (hab : a < b)
    (c : ℝ) (hc : 0 < c) (j : ℕ) :
    MeasureTheory.Integrable (fun t : ℝ =>
      (-((c : ℂ) + (t : ℂ) * Complex.I)) ^ j *
        reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  let K : ℂ → ℂ := fun s => (-s) ^ j * reflectedSquareSpectrum D r W s
  have hhol : ∀ s : ℂ, (0 : ℝ) < s.re → s.re < c + 1 →
      DifferentiableAt ℂ K s := by
    intro s hs _
    exact (differentiableAt_id.neg.pow j).mul
      ((reflectedSquareSpectrum_differentiableOn D r W a b hD hr hW hsupp ha hab s hs).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs))
  have hrapid : ∀ u v : ℝ, (0 : ℝ) < u → u ≤ v → v < c + 1 → ∀ N : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, u ≤ σ → σ ≤ v → 1 ≤ |t| →
        (1 + |t|) ^ N * ‖K ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
    intro u v hu huv _ N
    obtain ⟨C, hC, hbound⟩ := rapid D r W a b hD hr hW hsupp ha hab u v hu huv (N + j)
    refine ⟨(1 + |v|) ^ j * C, mul_nonneg (by positivity) hC, ?_⟩
    intro σ t hσ hσv ht
    have hσpos : 0 ≤ σ := (hu.trans_le hσ).le
    have hs : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ (1 + |v|) * (1 + |t|) := by
      calc
        _ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |σ| + |t| := by simp
        _ ≤ (1 + |v|) * (1 + |t|) := by
          rw [abs_of_nonneg hσpos]
          have hvpos : 0 ≤ v := (hσpos.trans hσv)
          rw [abs_of_nonneg hvpos]
          nlinarith [abs_nonneg t, mul_nonneg hvpos (abs_nonneg t)]
    have hpow : (1 + |t|) ^ (N + j) = (1 + |t|) ^ N * (1 + |t|) ^ j := pow_add _ _ _
    have hB := hbound σ t hσ hσv ht
    simp only [K, norm_mul, norm_pow, norm_neg] at *
    calc
      (1 + |t|) ^ N * (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ j *
          ‖reflectedSquareSpectrum D r W ((σ : ℂ) + (t : ℂ) * Complex.I)‖)
        ≤ (1 + |v|) ^ j * ((1 + |t|) ^ (N + j) *
            ‖reflectedSquareSpectrum D r W ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
          rw [hpow]
          have hh := pow_le_pow_left₀ (norm_nonneg _) hs j
          rw [mul_pow] at hh
          have hh' := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hh
              (norm_nonneg (reflectedSquareSpectrum D r W ((σ : ℂ) + (t : ℂ) * Complex.I))))
            (pow_nonneg (show (0 : ℝ) ≤ 1 + |t| by positivity) N)
          convert hh' using 1 <;> ring
      _ ≤ (1 + |v|) ^ j * C := mul_le_mul_of_nonneg_left hB (by positivity)
  exact (DedekindZetaZeroFree.LargeSieve.Vendor.LogReflection.strip_integrability K 0 (c + 1)
    hhol hrapid c hc (by linarith)).1

theorem inverseWeight_regularity
    (D : ℝ) (r : ℕ) (W : ℝ → ℂ) (a b : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hW : ContDiff ℝ ∞ W)
    (hsupp : Function.support W ⊆ Set.Icc a b) (ha : 0 < a) (hab : a < b) :
    ContDiffOn ℝ ∞ (inverseWeight D r W) (Set.Ioi 0) ∧
      ∀ (j : ℕ) (c x : ℝ), 0 < c → 0 < x →
        Vendor.EulerIter j (inverseWeight D r W) x =
          mellinInv c (fun s : ℂ => (-s) ^ j * reflectedSquareSpectrum D r W s) x := by
  let K := reflectedSquareSpectrum D r W
  have hint : ∀ c : ℝ, 0 < c → ∀ j : ℕ, MeasureTheory.Integrable
      (fun t : ℝ => (-((c : ℂ) + (t : ℂ) * Complex.I)) ^ j *
        K ((c : ℂ) + (t : ℂ) * Complex.I)) :=
    fun c hc j => weighted_integrable D r W a b hD hr hW hsupp ha hab c hc j
  have hshift : ∀ c d x : ℝ, 0 < c → 0 < d → 0 < x → mellinInv c K x = mellinInv d K x := by
    intro c d x hc hd hx
    let B := max c d + 1
    have hB : c < B ∧ d < B := by dsimp [B]; constructor <;> linarith [le_max_left c d, le_max_right c d]
    exact (DedekindZetaZeroFree.LargeSieve.Vendor.LogReflection.strip_inverse_api K 0 B
      (fun s hs _ => (reflectedSquareSpectrum_differentiableOn D r W a b hD hr hW hsupp ha hab s hs).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs))
      (fun u v hu huv _ N => rapid D r W a b hD hr hW hsupp ha hab u v hu huv N)).1
      c d x hc hB.1 hd hB.2 hx
  constructor
  · have h := Vendor.InverseSpectrumEuler.contDiffOn_weighted 2 K (hint 2 (by norm_num)) 0
    exact h.congr fun x hx => by simp [inverseWeight, K, Set.mem_Ioi.mp hx]
  · intro j c x hc hx
    have hjet : ∀ j : ℕ, ∀ y : ℝ, 0 < y →
        Vendor.EulerIter j (inverseWeight D r W) y = Vendor.EulerIter j (mellinInv c K) y := by
      intro k
      induction k with
      | zero =>
        intro y hy
        simpa [Vendor.EulerIter, inverseWeight, hy, K] using hshift 2 c y (by norm_num) hc hy
      | succ k ih =>
        intro y hy
        rw [Vendor.EulerIter_succ_of_pos k _ y hy, Vendor.EulerIter_succ_of_pos k _ y hy]
        have he : Vendor.EulerIter k (inverseWeight D r W) =ᶠ[nhds y]
            Vendor.EulerIter k (mellinInv c K) :=
          Filter.eventually_of_mem (Ioi_mem_nhds hy) (fun z hz => ih z hz)
        rw [he.deriv_eq]
    exact (hjet j x hx).trans
      (Vendor.InverseSpectrumEuler.EulerIter_eq_mellinInv c K (hint c hc) j x hx)

end DedekindZetaZeroFree.LargeSieve.ReflectedSquareDerivatives

end

end

section

noncomputable section
open scoped Classical ContDiff
open MeasureTheory
namespace DedekindZetaZeroFree.LargeSieve.ReflectedSquareDerivatives

private lemma uniform_complex_norm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

private lemma uniform_norm_add_mul_I_le (c t v : ℝ) (hc0 : 0 ≤ c) (hcv : c ≤ v) (hv0 : 0 ≤ v) :
    ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ≤ (v + 1) * (1 + |t|) := by
  calc ‖(c : ℂ) + (t : ℂ) * Complex.I‖
      ≤ ‖(c : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |c| + |t| := by
        rw [uniform_complex_norm_ofReal, norm_mul, uniform_complex_norm_ofReal,
          Complex.norm_I, mul_one]
    _ = c + |t| := by rw [abs_of_nonneg hc0]
    _ ≤ v + |t| := by linarith
    _ ≤ (v + 1) * (1 + |t|) := by nlinarith [abs_nonneg t, hv0]

private lemma uniform_abs_rpow_neg_two_le (t : ℝ) :
    (1 + |t|) ^ (-2 : ℝ) ≤ 2 * (1 + t ^ 2)⁻¹ := by
  rw [Real.rpow_neg (by positivity), Real.rpow_two, ← one_div, ← div_eq_mul_inv]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [abs_nonneg t, sq_abs t, sq_nonneg t]

private lemma uniform_integrable_one_add_abs_rpow_neg_two :
    Integrable (fun t : ℝ => (1 + |t|) ^ (-2 : ℝ)) := by
  simpa using (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp))

private lemma uniform_integral_one_add_abs_rpow_neg_two_le :
    ∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ) ≤ 2 * Real.pi := by
  have h := integral_mono_of_nonneg (μ := volume)
    (Filter.Eventually.of_forall (fun t => Real.rpow_nonneg (by positivity) _))
    (integrable_inv_one_add_sq.const_mul 2)
    (Filter.Eventually.of_forall (fun t => uniform_abs_rpow_neg_two_le t))
  rwa [integral_const_mul, integral_univ_inv_one_add_sq] at h

private lemma uniform_rpow_pow_mul_inv (u : ℝ) (hu : 0 < u) (j : ℕ) :
    u ^ j * (u ^ (j + 2))⁻¹ = u ^ (-2 : ℝ) := by
  rw [← Real.rpow_natCast u j, ← Real.rpow_natCast u (j + 2), ← Real.rpow_neg hu.le,
    ← Real.rpow_add hu]
  push_cast
  ring_nf

private lemma uniform_jet_mul_bound (u : ℝ) (hu : 0 < u) (j : ℕ) (X Y : ℝ)
    (hXY : u ^ (j + 2) * Y ≤ X) :
    u ^ j * Y ≤ X * u ^ (-2 : ℝ) := by
  have hu2 : (0 : ℝ) < u ^ (j + 2) := by positivity
  have hY : Y ≤ X * (u ^ (j + 2))⁻¹ := by
    rw [le_mul_inv_iff₀ hu2, mul_comm]; exact hXY
  calc u ^ j * Y ≤ u ^ j * (X * (u ^ (j + 2))⁻¹) :=
        mul_le_mul_of_nonneg_left hY (by positivity)
    _ = X * (u ^ j * (u ^ (j + 2))⁻¹) := by ring
    _ = X * u ^ (-2 : ℝ) := by rw [uniform_rpow_pow_mul_inv u hu j]

private lemma uniform_norm_mellinInv_le (c x A : ℝ) (g : ℂ → ℂ) (hx : 0 < x) (hA : 0 ≤ A)
    (hbound : ∀ t : ℝ, ‖g (c + (t : ℂ) * Complex.I)‖ ≤ A * (1 + |t|) ^ (-2 : ℝ)) :
    ‖mellinInv c g x‖ ≤ A * x ^ (-c) := by
  set F : ℝ → ℂ := fun t => (x : ℂ) ^ (-(c + (t : ℂ) * Complex.I)) * g (c + (t : ℂ) * Complex.I)
    with hF
  have hFn : ∀ t, ‖F t‖ = x ^ (-c) * ‖g (c + (t : ℂ) * Complex.I)‖ := by
    intro t
    rw [hF, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    congr 1
    simp [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re]
  have hmaj_int : Integrable (fun t : ℝ => x ^ (-c) * A * (1 + |t|) ^ (-2 : ℝ)) := by
    have h := (uniform_integrable_one_add_abs_rpow_neg_two.const_mul (x ^ (-c) * A))
    simpa [mul_assoc] using h
  have hle : ∫ t, ‖F t‖ ≤ ∫ t, x ^ (-c) * A * (1 + |t|) ^ (-2 : ℝ) := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg (F t))) hmaj_int
    apply Filter.Eventually.of_forall
    intro t
    change ‖F t‖ ≤ x ^ (-c) * A * (1 + |t|) ^ (-2 : ℝ)
    rw [hFn t]
    have hxc : 0 ≤ x ^ (-c) := Real.rpow_nonneg hx.le _
    calc x ^ (-c) * ‖g (c + (t : ℂ) * Complex.I)‖
        ≤ x ^ (-c) * (A * (1 + |t|) ^ (-2 : ℝ)) := mul_le_mul_of_nonneg_left (hbound t) hxc
      _ = x ^ (-c) * A * (1 + |t|) ^ (-2 : ℝ) := by ring
  have hIeq : ∫ t, x ^ (-c) * A * (1 + |t|) ^ (-2 : ℝ)
      = x ^ (-c) * A * ∫ t, (1 + |t|) ^ (-2 : ℝ) := by
    rw [← integral_const_mul]
  have hscal : ‖(1 / (2 * Real.pi) : ℝ)‖ = 1 / (2 * Real.pi) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hInv : mellinInv c g x = (1 / (2 * Real.pi)) • ∫ t, F t := by
    rw [mellinInv]
    congr 1
  rw [hInv, norm_smul, hscal]
  calc (1 / (2 * Real.pi)) * ‖∫ t, F t‖
      ≤ (1 / (2 * Real.pi)) * ∫ t, ‖F t‖ := by
        exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm F) (by positivity)
    _ ≤ (1 / (2 * Real.pi)) * (x ^ (-c) * A * ∫ t, (1 + |t|) ^ (-2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← hIeq]; exact hle
    _ ≤ (1 / (2 * Real.pi)) * (x ^ (-c) * A * (2 * Real.pi)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left uniform_integral_one_add_abs_rpow_neg_two_le
            (mul_nonneg (Real.rpow_nonneg hx.le _) hA)
        · positivity
    _ = A * x ^ (-c) := by field_simp

theorem inverseWeight_uniform_euler_jet
    (D : ℝ) (r : ℕ) (a b : ℝ) (j n : ℕ) (δ : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc a b →
        ∀ q ≤ j,
          (∀ x : ℝ, 0 < x → x ≤ 1 →
            ‖Vendor.EulerIter q (inverseWeight D r W) x‖ ≤
              C * Vendor.S b N W * Real.rpow x (-δ)) ∧
          (∀ x : ℝ, 1 ≤ x →
            ‖Vendor.EulerIter q (inverseWeight D r W) x‖ ≤
              C * Vendor.S b N W * Real.rpow x (-(n : ℝ))) := by
  set u : ℝ := min δ ((n : ℝ) + 1) with hu_def
  set v : ℝ := max δ ((n : ℝ) + 1) with hv_def
  have hu : 0 < u := by rw [hu_def]; exact lt_min hδ (by positivity)
  have huv : u ≤ v := by rw [hu_def, hv_def]; exact min_le_max
  have hv0 : 0 ≤ v := le_of_lt (lt_of_lt_of_le hu huv)
  obtain ⟨N, C0, hC0, hrap⟩ :=
    reflectedSquareSpectrum_uniform_rapid_bound D r a b u v (j + 2) hD hr ha hab hu huv
  refine ⟨N, C0 * (v + 1) ^ j, by positivity, ?_⟩
  intro W hW hsupp q hq
  have hS : 0 ≤ Vendor.S b N W := Vendor.S_nonneg b (by linarith) N W hW
  have hδmem : δ ∈ Set.Icc u v :=
    ⟨by rw [hu_def]; exact min_le_left _ _, by rw [hv_def]; exact le_max_left _ _⟩
  have hmem : ((n : ℝ) + 1) ∈ Set.Icc u v :=
    ⟨by rw [hu_def]; exact min_le_right _ _, by rw [hv_def]; exact le_max_right _ _⟩
  have hA : 0 ≤ C0 * Vendor.S b N W * (v + 1) ^ j :=
    mul_nonneg (mul_nonneg (le_of_lt hC0) hS) (by positivity)
  have step : ∀ c ∈ Set.Icc u v, ∀ x : ℝ, 0 < x →
      ‖Vendor.EulerIter q (inverseWeight D r W) x‖
        ≤ C0 * (v + 1) ^ j * Vendor.S b N W * x ^ (-c) := by
    intro c hc x hx
    have hcpos : 0 < c := lt_of_lt_of_le hu hc.1
    have hcv : c ≤ v := hc.2
    rw [(inverseWeight_regularity D r W a b hD hr hW hsupp ha hab).2 q c x hcpos hx]
    have hbnd : ∀ t : ℝ,
        ‖(-(((c : ℂ) + (t : ℂ) * Complex.I))) ^ q
            * reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (C0 * Vendor.S b N W * (v + 1) ^ j) * (1 + |t|) ^ (-2 : ℝ) := by
      intro t
      have hrp := hrap W hW hsupp c hc t
      have hs : ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ≤ (v + 1) * (1 + |t|) :=
        uniform_norm_add_mul_I_le c t v (le_of_lt hcpos) hcv hv0
      have hu : 0 < 1 + |t| := by positivity
      have hnorm :
          ‖(-(((c : ℂ) + (t : ℂ) * Complex.I))) ^ q
              * reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I)‖
            = ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ^ q
              * ‖reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [norm_mul, norm_pow, norm_neg]
      rw [hnorm]
      have h1 : ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ^ q
              * ‖reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (v + 1) ^ j
              * ((1 + |t|) ^ j * ‖reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I)‖) := by
        have hsp : ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ^ q ≤ (v + 1) ^ j * (1 + |t|) ^ j := by
          rw [← mul_pow]
          exact (pow_le_pow_left₀ (norm_nonneg _) hs q).trans
              (pow_le_pow_right₀ (by nlinarith [abs_nonneg t]) hq)
        calc ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ^ q
              * ‖reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I)‖
            ≤ ((v + 1) ^ j * (1 + |t|) ^ j)
                * ‖reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I)‖ :=
              mul_le_mul_of_nonneg_right hsp (norm_nonneg _)
          _ = (v + 1) ^ j
                * ((1 + |t|) ^ j * ‖reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I)‖) := by ring
      have h2 : (1 + |t|) ^ j * ‖reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (C0 * Vendor.S b N W) * (1 + |t|) ^ (-2 : ℝ) :=
        uniform_jet_mul_bound (1 + |t|) hu j (C0 * Vendor.S b N W)
          ‖reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I)‖ hrp
      calc ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ^ q
              * ‖reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (v + 1) ^ j
              * ((1 + |t|) ^ j * ‖reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I)‖) := h1
        _ ≤ (v + 1) ^ j * ((C0 * Vendor.S b N W) * (1 + |t|) ^ (-2 : ℝ)) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (C0 * Vendor.S b N W * (v + 1) ^ j) * (1 + |t|) ^ (-2 : ℝ) := by ring
    have hmain := uniform_norm_mellinInv_le c x (C0 * Vendor.S b N W * (v + 1) ^ j)
      (fun s => (-s) ^ q * reflectedSquareSpectrum D r W s) hx hA hbnd
    calc ‖mellinInv c (fun s => (-s) ^ q * reflectedSquareSpectrum D r W s) x‖
        ≤ (C0 * Vendor.S b N W * (v + 1) ^ j) * x ^ (-c) := hmain
      _ = C0 * (v + 1) ^ j * Vendor.S b N W * x ^ (-c) := by ring
  refine ⟨?_, ?_⟩
  · intro x hx0 hx1
    simpa using step δ hδmem x hx0
  · intro x hx1
    have hlt : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
    calc ‖Vendor.EulerIter q (inverseWeight D r W) x‖
        ≤ C0 * (v + 1) ^ j * Vendor.S b N W * x ^ (-(((n : ℝ) + 1))) :=
          step ((n : ℝ) + 1) hmem x hlt
      _ ≤ C0 * (v + 1) ^ j * Vendor.S b N W * x ^ (-(n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)

end DedekindZetaZeroFree.LargeSieve.ReflectedSquareDerivatives

end

end

section

noncomputable section

open scoped Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve

theorem EulerIter_reflectedSquareTransform_eq_mellinInv
    (D : ℝ) (r : ℕ) (W : ℝ → ℂ) (a b : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hW : ContDiff ℝ ∞ W)
    (hsupp : Function.support W ⊆ Set.Icc a b) (ha : 0 < a) (hab : a < b)
    (j : ℕ) (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    Vendor.EulerIter j (SquareSecondPass.reflectedTransform D r W) x =
      mellinInv c (fun s : ℂ => (-s) ^ j * reflectedSquareSpectrum D r W s) x := by
  rw [ReflectedSquareDerivatives.identify_inverseWeight D r W a b hD hr hW hsupp ha hab]
  exact (ReflectedSquareDerivatives.inverseWeight_regularity D r W a b
    hD hr hW hsupp ha hab).2 j c x hc hx

theorem reflectedSquareTransform_contDiffOn
    (D : ℝ) (r : ℕ) (W : ℝ → ℂ) (a b : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hW : ContDiff ℝ ∞ W)
    (hsupp : Function.support W ⊆ Set.Icc a b) (ha : 0 < a) (hab : a < b) :
    ContDiffOn ℝ ∞ (SquareSecondPass.reflectedTransform D r W) (Set.Ioi 0) := by
  rw [ReflectedSquareDerivatives.identify_inverseWeight D r W a b hD hr hW hsupp ha hab]
  exact (ReflectedSquareDerivatives.inverseWeight_regularity D r W a b
    hD hr hW hsupp ha hab).1

theorem reflectedSquareTransform_euler_two_ended_bound
    (D : ℝ) (r : ℕ) (W : ℝ → ℂ) (a b : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hW : ContDiff ℝ ∞ W)
    (hsupp : Function.support W ⊆ Set.Icc a b) (ha : 0 < a) (hab : a < b)
    (j n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ x : ℝ, 0 < x → x ≤ 1 →
        ‖Vendor.EulerIter j (SquareSecondPass.reflectedTransform D r W) x‖ ≤
          C * Real.rpow x (-δ)) ∧
      (∀ x : ℝ, 1 ≤ x →
        ‖Vendor.EulerIter j (SquareSecondPass.reflectedTransform D r W) x‖ ≤
          C * Real.rpow x (-(n : ℝ))) := by
  obtain ⟨N, C, hC, hjet⟩ :=
    ReflectedSquareDerivatives.inverseWeight_uniform_euler_jet D r a b j n δ
      hD hr ha hab hδ
  rw [ReflectedSquareDerivatives.identify_inverseWeight D r W a b hD hr hW hsupp ha hab]
  refine ⟨max (C * Vendor.S b N W) 0 + 1, by positivity, ?_, ?_⟩
  · intro x hx hx1
    calc ‖Vendor.EulerIter j (ReflectedSquareDerivatives.inverseWeight D r W) x‖
        ≤ C * Vendor.S b N W * Real.rpow x (-δ) := (hjet W hW hsupp j le_rfl).1 x hx hx1
      _ ≤ (max (C * Vendor.S b N W) 0 + 1) * Real.rpow x (-δ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
        have := le_max_left (C * Vendor.S b N W) 0
        linarith
  · intro x hx1
    calc ‖Vendor.EulerIter j (ReflectedSquareDerivatives.inverseWeight D r W) x‖
        ≤ C * Vendor.S b N W * Real.rpow x (-(n : ℝ)) := (hjet W hW hsupp j le_rfl).2 x hx1
      _ ≤ (max (C * Vendor.S b N W) 0 + 1) * Real.rpow x (-(n : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
        have := le_max_left (C * Vendor.S b N W) 0
        linarith

end DedekindZetaZeroFree.LargeSieve

end

end
