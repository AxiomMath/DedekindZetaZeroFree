module

public import DedekindZetaZeroFree.LFunctions.Hecke.IdealCoefficientMellinSummation
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.TruncatedLogarithmicPolynomials

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section
open MeasureTheory
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve

variable {F : Type*} [Field F] [NumberField F]

private lemma absNorm_cast_pos {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    (0 : ℝ) < (Ideal.absNorm I : ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))

private lemma summable_ideal_scaled_inverse_power (p Y : ℝ) (hp : 1 < p) (hY : 0 < Y) :
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      (Y * (Ideal.absNorm I.val : ℝ)) ^ (-p)) := by
  have hbase : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      (Ideal.absNorm I.val : ℝ) ^ (-p)) := by
    have h := (summable_ideal_inverse_power F p hp).subtype ({I : Ideal (𝓞 F) | I ≠ ⊥})
    exact h.congr fun I => by
      rw [Function.comp_apply, if_neg I.2]
  have hmul : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      Y ^ (-p) * (Ideal.absNorm I.val : ℝ) ^ (-p)) :=
    Summable.mul_left _ hbase
  have hfun : (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      (Y * (Ideal.absNorm I.val : ℝ)) ^ (-p)) =
      fun I => Y ^ (-p) * (Ideal.absNorm I.val : ℝ) ^ (-p) := by
    funext I
    rw [Real.mul_rpow (le_of_lt hY) (le_of_lt (absNorm_cast_pos I.2))]
  rw [hfun]
  exact hmul

private lemma norm_cpow_vertical {z c t : ℝ} (hz : 0 < z) :
    ‖((z : ℝ) : ℂ) ^ (-((c : ℂ) + t * Complex.I))‖ = z ^ (-c) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hz]
  congr 1
  simp [Complex.neg_re, Complex.add_re, Complex.mul_re]

private lemma norm_vertical_summand_le {K : ℂ → ℂ} {c : ℝ} {a : ℂ} {z : ℝ} (hz : 0 < z)
    (ha : ‖a‖ ≤ 1) (t : ℝ) :
    ‖K ((c : ℂ) + t * Complex.I) * ((z : ℝ) : ℂ) ^ (-((c : ℂ) + t * Complex.I)) * a‖ ≤
      z ^ (-c) * ‖K ((c : ℂ) + t * Complex.I)‖ := by
  rw [norm_mul, norm_mul, norm_cpow_vertical hz]
  calc ‖K ((c : ℂ) + t * Complex.I)‖ * z ^ (-c) * ‖a‖
      ≤ ‖K ((c : ℂ) + t * Complex.I)‖ * z ^ (-c) * 1 :=
        mul_le_mul_of_nonneg_left ha
          (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hz.le _))
    _ = z ^ (-c) * ‖K ((c : ℂ) + t * Complex.I)‖ := by ring

private lemma integrable_vertical_summand {K : ℂ → ℂ} {c : ℝ}
    (hK : Integrable (fun t : ℝ => K ((c : ℂ) + t * Complex.I)))
    (hKcont : Continuous fun t : ℝ => K ((c : ℂ) + t * Complex.I))
    {a : ℂ} {z : ℝ} (hz : 0 < z) (ha : ‖a‖ ≤ 1) :
    Integrable (fun t : ℝ => K ((c : ℂ) + t * Complex.I) *
      ((z : ℝ) : ℂ) ^ (-((c : ℂ) + t * Complex.I)) * a) := by
  refine Integrable.mono' (hK.norm.const_mul (z ^ (-c))) ?_ ?_
  · have hcp : Continuous fun t : ℝ =>
        ((z : ℝ) : ℂ) ^ (-((c : ℂ) + t * Complex.I)) :=
      Continuous.const_cpow (f := fun t : ℝ => -((c : ℂ) + t * Complex.I))
        (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hz.ne'))
    exact ((hKcont.mul hcp).mul continuous_const).aestronglyMeasurable
  · filter_upwards with t
    exact norm_vertical_summand_le hz ha t

private lemma norm_integral_vertical_summand_le {K : ℂ → ℂ} {c : ℝ}
    (hK : Integrable (fun t : ℝ => K ((c : ℂ) + t * Complex.I)))
    {a : ℂ} {z : ℝ} (hz : 0 < z) (ha : ‖a‖ ≤ 1) :
    (∫ t : ℝ, ‖K ((c : ℂ) + t * Complex.I) *
        ((z : ℝ) : ℂ) ^ (-((c : ℂ) + t * Complex.I)) * a‖) ≤
      z ^ (-c) * ∫ t : ℝ, ‖K ((c : ℂ) + t * Complex.I)‖ := by
  calc (∫ t : ℝ, ‖K ((c : ℂ) + t * Complex.I) *
        ((z : ℝ) : ℂ) ^ (-((c : ℂ) + t * Complex.I)) * a‖)
      ≤ ∫ t : ℝ, z ^ (-c) * ‖K ((c : ℂ) + t * Complex.I)‖ :=
        integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _)
          (hK.norm.const_mul _) (ae_of_all _ fun t => norm_vertical_summand_le hz ha t)
    _ = z ^ (-c) * ∫ t : ℝ, ‖K ((c : ℂ) + t * Complex.I)‖ := integral_const_mul _ _

private lemma norm_mellinInv_le {K : ℂ → ℂ} {c : ℝ}
    (hK : Integrable (fun t : ℝ => K ((c : ℂ) + t * Complex.I))) {z : ℝ} (hz : 0 < z) :
    ‖mellinInv c K z‖ ≤
      (1 / (2 * Real.pi)) * (z ^ (-c) * ∫ t : ℝ, ‖K ((c : ℂ) + t * Complex.I)‖) := by
  have hpi : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by
      push_cast; ring]
    rw [show ‖(((1 / (2 * Real.pi) : ℝ)) : ℂ)‖ = |(1 / (2 * Real.pi) : ℝ)| from
      by simpa using @RCLike.norm_ofReal ℂ _ (1 / (2 * Real.pi) : ℝ)]
    rw [abs_of_pos (by positivity)]
  have hXint : (∫ y : ℝ, ‖((z : ℝ) : ℂ) ^ (-((c : ℂ) + y * Complex.I)) *
        K ((c : ℂ) + y * Complex.I)‖) =
      z ^ (-c) * ∫ t : ℝ, ‖K ((c : ℂ) + t * Complex.I)‖ := by
    have hfun : (fun y : ℝ => ‖((z : ℝ) : ℂ) ^ (-((c : ℂ) + y * Complex.I)) *
          K ((c : ℂ) + y * Complex.I)‖) =
        fun y : ℝ => z ^ (-c) * ‖K ((c : ℂ) + y * Complex.I)‖ := by
      funext y
      rw [norm_mul, norm_cpow_vertical hz]
    rw [hfun, integral_const_mul]
  rw [Vendor.mellinInv_eq_verticalIntegral c K hz, Vendor.verticalIntegral, norm_mul, hpi]
  calc (1 / (2 * Real.pi)) * ‖∫ y : ℝ,
        ((z : ℝ) : ℂ) ^ (-((c : ℂ) + y * Complex.I)) * K ((c : ℂ) + y * Complex.I)‖
      ≤ (1 / (2 * Real.pi)) * ∫ y : ℝ,
          ‖((z : ℝ) : ℂ) ^ (-((c : ℂ) + y * Complex.I)) * K ((c : ℂ) + y * Complex.I)‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = (1 / (2 * Real.pi)) *
          (z ^ (-c) * ∫ t : ℝ, ‖K ((c : ℂ) + t * Complex.I)‖) := by rw [hXint]

private lemma continuous_idealCoefficientLSeries_line (a : Ideal (𝓞 F) → ℂ)
    (ha : ∀ I, I ≠ ⊥ → ‖a I‖ ≤ 1) {c : ℝ} (hc : 1 < c) :
    Continuous fun t : ℝ => idealCoefficientLSeries a ((c : ℂ) + t * Complex.I) := by
  have hS : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      (Ideal.absNorm I.val : ℝ) ^ (-c)) := by
    simpa using summable_ideal_scaled_inverse_power (F := F) c 1 hc one_pos
  have h := continuous_tsum
    (u := fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => (Ideal.absNorm I.val : ℝ) ^ (-c))
    (f := fun I (t : ℝ) => a I.val * (Ideal.absNorm I.val : ℂ) ^ (-((c : ℂ) + t * Complex.I)))
    (fun I => by
      refine Continuous.mul continuous_const ?_
      refine Continuous.const_cpow (f := fun t : ℝ => -((c : ℂ) + t * Complex.I))
        (by fun_prop) (Or.inl ?_)
      exact Complex.ofReal_ne_zero.mpr
        (absNorm_cast_pos I.2).ne')
    hS
    (fun I (t : ℝ) => by
      rw [norm_mul, ← Complex.ofReal_natCast, norm_cpow_vertical (absNorm_cast_pos I.2)]
      calc ‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-c)
          ≤ 1 * (Ideal.absNorm I.val : ℝ) ^ (-c) :=
            mul_le_mul_of_nonneg_right (ha I.val I.2)
              (Real.rpow_nonneg (absNorm_cast_pos I.2).le _)
        _ = (Ideal.absNorm I.val : ℝ) ^ (-c) := one_mul _)
  simpa only [idealCoefficientLSeries] using h

private lemma norm_lseries_le (a : Ideal (𝓞 F) → ℂ) (ha : ∀ I, I ≠ ⊥ → ‖a I‖ ≤ 1)
    {c : ℝ} (hc : 1 < c) (t : ℝ) :
    ‖idealCoefficientLSeries a ((c : ℂ) + t * Complex.I)‖ ≤
      ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, (Ideal.absNorm I.val : ℝ) ^ (-c) := by
  have hS : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      (Ideal.absNorm I.val : ℝ) ^ (-c)) := by
    simpa using summable_ideal_scaled_inverse_power (F := F) c 1 hc one_pos
  have hterm : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      ‖a I.val * (Ideal.absNorm I.val : ℂ) ^ (-((c : ℂ) + t * Complex.I))‖ ≤
        (Ideal.absNorm I.val : ℝ) ^ (-c) := by
    intro I
    rw [norm_mul, ← Complex.ofReal_natCast, norm_cpow_vertical (absNorm_cast_pos I.2)]
    calc ‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-c)
        ≤ 1 * (Ideal.absNorm I.val : ℝ) ^ (-c) :=
          mul_le_mul_of_nonneg_right (ha I.val I.2)
            (Real.rpow_nonneg (absNorm_cast_pos I.2).le _)
      _ = (Ideal.absNorm I.val : ℝ) ^ (-c) := one_mul _
  have hsum : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      a I.val * (Ideal.absNorm I.val : ℂ) ^ (-((c : ℂ) + t * Complex.I))) :=
    Summable.of_norm_bounded hS hterm
  calc ‖idealCoefficientLSeries a ((c : ℂ) + t * Complex.I)‖
      = ‖∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
          a I.val * (Ideal.absNorm I.val : ℂ) ^ (-((c : ℂ) + t * Complex.I))‖ := rfl
    _ ≤ ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
          ‖a I.val * (Ideal.absNorm I.val : ℂ) ^ (-((c : ℂ) + t * Complex.I))‖ :=
        norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, (Ideal.absNorm I.val : ℝ) ^ (-c) :=
        Summable.tsum_le_tsum hterm hsum.norm hS

private lemma integrable_lseries_line (a : Ideal (𝓞 F) → ℂ)
    (ha : ∀ I, I ≠ ⊥ → ‖a I‖ ≤ 1) {K : ℂ → ℂ} {c Y : ℝ} (hc : 1 < c) (hY : 0 < Y)
    (hK : Integrable (fun t : ℝ => K ((c : ℂ) + t * Complex.I)))
    (hKcont : Continuous fun t : ℝ => K ((c : ℂ) + t * Complex.I)) :
    Integrable (fun t : ℝ => K ((c : ℂ) + t * Complex.I) * (Y : ℂ) ^ (-((c : ℂ) + t * Complex.I)) *
      idealCoefficientLSeries a ((c : ℂ) + t * Complex.I)) := by
  have hLcont := continuous_idealCoefficientLSeries_line a ha hc
  have hS : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      (Ideal.absNorm I.val : ℝ) ^ (-c)) := by
    simpa using summable_ideal_scaled_inverse_power (F := F) c 1 hc one_pos
  have hSnn : 0 ≤ ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, (Ideal.absNorm I.val : ℝ) ^ (-c) :=
    tsum_nonneg fun I => Real.rpow_nonneg (absNorm_cast_pos I.2).le _
  refine Integrable.mono' (hK.norm.const_mul (Y ^ (-c) *
      ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, (Ideal.absNorm I.val : ℝ) ^ (-c))) ?_ ?_
  · have hcp : Continuous fun t : ℝ => (Y : ℂ) ^ (-((c : ℂ) + t * Complex.I)) :=
      Continuous.const_cpow (f := fun t : ℝ => -((c : ℂ) + t * Complex.I))
        (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))
    exact ((hKcont.mul hcp).mul hLcont).aestronglyMeasurable
  · filter_upwards with t
    rw [norm_mul, norm_mul, norm_cpow_vertical hY]
    calc ‖K ((c : ℂ) + t * Complex.I)‖ * Y ^ (-c) *
          ‖idealCoefficientLSeries a ((c : ℂ) + t * Complex.I)‖
        ≤ ‖K ((c : ℂ) + t * Complex.I)‖ * Y ^ (-c) *
            (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, (Ideal.absNorm I.val : ℝ) ^ (-c)) :=
          mul_le_mul_of_nonneg_left (norm_lseries_le a ha hc t)
            (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hY.le _))
      _ = (Y ^ (-c) * (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
            (Ideal.absNorm I.val : ℝ) ^ (-c))) * ‖K ((c : ℂ) + t * Complex.I)‖ := by ring

private theorem countable_ideal_fubini (F : Type*) [Field F] [NumberField F] :
    Countable (Ideal (𝓞 F)) := by
  have h : (Set.univ : Set (Ideal (𝓞 F))) =
      ⋃ n : ℕ, {I | (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} := by
    ext I
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact ⟨Ideal.absNorm I, by push_cast; exact le_refl _⟩
  rw [← Set.countable_univ_iff, h]
  exact Set.countable_iUnion fun n => (finite_ideals_absNorm_le F (n : ℝ)).countable

theorem idealCoefficientLSeries_eq_tsum_zeroBranch
    (a : Ideal (𝓞 F) → ℂ) (s : ℂ) :
    idealCoefficientLSeries a s =
      ∑' I : Ideal (𝓞 F),
        if I = ⊥ then 0 else a I * (Ideal.absNorm I : ℂ) ^ (-s) := by
  calc idealCoefficientLSeries a s
      = ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, a I.val * (Ideal.absNorm I.val : ℂ) ^ (-s) := rfl
    _ = ∑' I : Ideal (𝓞 F), ({I : Ideal (𝓞 F) | I ≠ ⊥}.indicator
          (fun I => a I * (Ideal.absNorm I : ℂ) ^ (-s))) I :=
        tsum_subtype {I : Ideal (𝓞 F) | I ≠ ⊥}
          (fun I => a I * (Ideal.absNorm I : ℂ) ^ (-s))
    _ = ∑' I : Ideal (𝓞 F),
          if I = ⊥ then 0 else a I * (Ideal.absNorm I : ℂ) ^ (-s) :=
        tsum_congr fun I => by
          by_cases h : I = ⊥ <;> simp [Set.indicator_apply, h]

theorem idealLogMellin_inverseSpectrum_interchange
    (a : Ideal (𝓞 F) → ℂ) (ha : ∀ I, I ≠ ⊥ → ‖a I‖ ≤ 1)
    (K : ℂ → ℂ) (k : ℝ → ℂ) {c Y : ℝ}
    (hc : 1 < c) (hY : 0 < Y)
    (hKcont : Continuous (fun t : ℝ => K ((c : ℂ) + t * Complex.I)))
    (hK : Complex.VerticalIntegrable K c)
    (hk : ∀ x : ℝ, 0 < x → k x = mellinInv c K x) :
    (∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      Complex.VerticalIntegrable
        (fun s => K s * (Y * (Ideal.absNorm I.val : ℝ) : ℂ) ^ (-s) * a I.val) c) ∧
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ∫ t : ℝ,
        ‖K ((c : ℂ) + t * Complex.I) *
          (Y * (Ideal.absNorm I.val : ℝ) : ℂ) ^
            (-((c : ℂ) + t * Complex.I)) * a I.val‖) ∧
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖k (Y * (Ideal.absNorm I.val : ℝ))‖) ∧
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖a I.val * k (Y * (Ideal.absNorm I.val : ℝ))‖) ∧
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      a I.val * k (Y * (Ideal.absNorm I.val : ℝ))) ∧
    Complex.VerticalIntegrable
      (fun s => K s * (Y : ℂ) ^ (-s) * idealCoefficientLSeries a s) c ∧
    Vendor.verticalIntegral c
      (fun s => K s * (Y : ℂ) ^ (-s) * idealCoefficientLSeries a s) =
      ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
        a I.val * k (Y * (Ideal.absNorm I.val : ℝ)) := by
  have hKnorm : Integrable (fun t : ℝ => ‖K ((c : ℂ) + t * Complex.I)‖) := hK.norm
  have hzpos : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      0 < Y * (Ideal.absNorm I.val : ℝ) :=
    fun I => mul_pos hY (absNorm_cast_pos I.2)
  have hsingle : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      Integrable (fun t : ℝ => K ((c : ℂ) + t * Complex.I) *
        ((Y : ℂ) * ((Ideal.absNorm I.val : ℝ) : ℂ)) ^ (-((c : ℂ) + t * Complex.I)) *
          a I.val) :=
    fun I => (integrable_vertical_summand hK hKcont (hzpos I) (ha I.val I.2)).congr
      (ae_of_all _ fun t => by simp only [Complex.ofReal_mul])
  have hint_le : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      (∫ t : ℝ, ‖K ((c : ℂ) + t * Complex.I) *
          ((Y : ℂ) * ((Ideal.absNorm I.val : ℝ) : ℂ)) ^ (-((c : ℂ) + t * Complex.I)) *
            a I.val‖) ≤
        (Y * (Ideal.absNorm I.val : ℝ)) ^ (-c) *
          ∫ t : ℝ, ‖K ((c : ℂ) + t * Complex.I)‖ := by
    intro I
    have h := norm_integral_vertical_summand_le hK (hzpos I) (ha I.val I.2)
    rw [show (∫ t : ℝ, ‖K ((c : ℂ) + t * Complex.I) *
          ((Y : ℂ) * ((Ideal.absNorm I.val : ℝ) : ℂ)) ^ (-((c : ℂ) + t * Complex.I)) *
            a I.val‖) = (∫ t : ℝ, ‖K ((c : ℂ) + t * Complex.I) *
          (((Y * (Ideal.absNorm I.val : ℝ) : ℝ)) : ℂ) ^ (-((c : ℂ) + t * Complex.I)) *
            a I.val‖) from by
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only [Complex.ofReal_mul]]
    exact h
  have hsum_int : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ∫ t : ℝ, ‖K ((c : ℂ) + t * Complex.I) *
        ((Y : ℂ) * ((Ideal.absNorm I.val : ℝ) : ℂ)) ^ (-((c : ℂ) + t * Complex.I)) *
          a I.val‖) :=
    Summable.of_nonneg_of_le (fun I => integral_nonneg fun t => norm_nonneg _) hint_le
      (Summable.mul_right _ (summable_ideal_scaled_inverse_power (F := F) c Y hc hY))
  have hk_bound : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      ‖k (Y * (Ideal.absNorm I.val : ℝ))‖ ≤
        (1 / (2 * Real.pi)) * ((Y * (Ideal.absNorm I.val : ℝ)) ^ (-c) *
          ∫ t : ℝ, ‖K ((c : ℂ) + t * Complex.I)‖) := by
    intro I
    rw [hk _ (hzpos I)]
    exact norm_mellinInv_le hK (hzpos I)
  have hsum_k : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖k (Y * (Ideal.absNorm I.val : ℝ))‖) :=
    Summable.of_nonneg_of_le (fun I => norm_nonneg _) hk_bound
      (Summable.mul_left _ (Summable.mul_right _
        (summable_ideal_scaled_inverse_power (F := F) c Y hc hY)))
  have hsum_ak : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖a I.val * k (Y * (Ideal.absNorm I.val : ℝ))‖) :=
    Summable.of_nonneg_of_le (fun I => norm_nonneg _)
      (fun I => by
        rw [norm_mul]
        have h1 : ‖a I.val‖ ≤ 1 := ha I.val I.2
        have h2 : 0 ≤ ‖k (Y * (Ideal.absNorm I.val : ℝ))‖ := norm_nonneg _
        nlinarith [h1, h2])
      hsum_k
  have hsum_a : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      a I.val * k (Y * (Ideal.absNorm I.val : ℝ))) := Summable.of_norm hsum_ak
  have hvert : Complex.VerticalIntegrable
      (fun s => K s * (Y : ℂ) ^ (-s) * idealCoefficientLSeries a s) c := by
    rw [Complex.VerticalIntegrable]
    exact integrable_lseries_line a ha hc hY hK hKcont

  have hpoint : ∀ t : ℝ,
      K ((c : ℂ) + t * Complex.I) * (Y : ℂ) ^ (-((c : ℂ) + t * Complex.I)) *
        idealCoefficientLSeries a ((c : ℂ) + t * Complex.I)
      = ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
          K ((c : ℂ) + t * Complex.I) *
            ((Y : ℂ) * ((Ideal.absNorm I.val : ℝ) : ℂ)) ^ (-((c : ℂ) + t * Complex.I)) *
              a I.val := by
    intro t
    set s : ℂ := (c : ℂ) + t * Complex.I with hs
    have hcp : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
        (Y : ℂ) ^ (-s) * ((Ideal.absNorm I.val : ℝ) : ℂ) ^ (-s) =
          ((Y : ℂ) * ((Ideal.absNorm I.val : ℝ) : ℂ)) ^ (-s) := by
      intro I
      exact (Complex.mul_cpow_ofReal_nonneg (le_of_lt hY) (Nat.cast_nonneg _) (-s)).symm
    simp only [idealCoefficientLSeries, ← Complex.ofReal_natCast]
    rw [← tsum_mul_left (a := K s * (Y : ℂ) ^ (-s))]
    refine tsum_congr fun I => ?_
    rw [← hcp I]
    ring
  have hFubini : (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
        ∫ t : ℝ, K ((c : ℂ) + t * Complex.I) *
          ((Y : ℂ) * ((Ideal.absNorm I.val : ℝ) : ℂ)) ^ (-((c : ℂ) + t * Complex.I)) *
            a I.val) =
      ∫ t : ℝ, ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
          K ((c : ℂ) + t * Complex.I) *
            ((Y : ℂ) * ((Ideal.absNorm I.val : ℝ) : ℂ)) ^ (-((c : ℂ) + t * Complex.I)) *
              a I.val := by
    haveI : Countable (Ideal (𝓞 F)) := countable_ideal_fubini F
    haveI : Countable {I : Ideal (𝓞 F) // I ≠ ⊥} := inferInstance
    exact integral_tsum_of_summable_integral_norm hsingle hsum_int

  have hterm : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, K ((c : ℂ) + t * Complex.I) *
          ((Y : ℂ) * ((Ideal.absNorm I.val : ℝ) : ℂ)) ^ (-((c : ℂ) + t * Complex.I)) *
            a I.val) =
      a I.val * k (Y * (Ideal.absNorm I.val : ℝ)) := by
    intro I
    have hInt : (∫ t : ℝ, K ((c : ℂ) + t * Complex.I) *
          ((Y : ℂ) * ((Ideal.absNorm I.val : ℝ) : ℂ)) ^ (-((c : ℂ) + t * Complex.I)) *
            a I.val) =
        (∫ t : ℝ, ((Y : ℂ) * ((Ideal.absNorm I.val : ℝ) : ℂ)) ^
            (-((c : ℂ) + t * Complex.I)) *
          K ((c : ℂ) + t * Complex.I)) * a I.val := by
      rw [← integral_mul_const (a I.val)]
      exact integral_congr_ae (ae_of_all _ fun t => by ring)
    rw [hInt, hk _ (hzpos I), Vendor.mellinInv_eq_verticalIntegral c K (hzpos I),
      Vendor.verticalIntegral]
    have : ((Y * (Ideal.absNorm I.val : ℝ) : ℝ) : ℂ) =
        (Y : ℂ) * ((Ideal.absNorm I.val : ℝ) : ℂ) := Complex.ofReal_mul _ _
    rw [this]
    ring
  refine ⟨?_, hsum_int, hsum_k, hsum_ak, hsum_a, hvert, ?_⟩
  · intro I
    rw [Complex.VerticalIntegrable]
    exact hsingle I
  · rw [Vendor.verticalIntegral]
    have hcongr : (∫ t : ℝ, K ((c : ℂ) + t * Complex.I) * (Y : ℂ) ^ (-((c : ℂ) + t * Complex.I)) *
          idealCoefficientLSeries a ((c : ℂ) + t * Complex.I)) =
        ∫ t : ℝ, ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
          K ((c : ℂ) + t * Complex.I) *
            ((Y : ℂ) * ((Ideal.absNorm I.val : ℝ) : ℂ)) ^ (-((c : ℂ) + t * Complex.I)) *
              a I.val :=
      integral_congr_ae (ae_of_all _ hpoint)
    rw [hcongr, ← hFubini, ← tsum_mul_left]
    exact tsum_congr fun I => hterm I

theorem logSpectrum_continuousOn_line {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}
    {H : ℂ → ℂ} (hf : Vendor.LogMellinAdmissible f δ P H) {c : ℝ} (hc : 1 < c) :
    Continuous fun t : ℝ => H ((c : ℂ) + (t : ℂ) * Complex.I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hre : -δ < ((c : ℂ) + (t : ℂ) * Complex.I).re := by
    have : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by simp
    rw [this]; linarith [hf.delta_pos, hc]
  have hne : ((c : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by simp
    rw [h] at this
    simp at this
    linarith
  have hg : ContinuousAt (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) t := by fun_prop
  exact (hf.differentiableAt _ hre hne).continuousAt.comp'
    (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) hg

theorem logSpectrum_verticalIntegrable {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}
    {H : ℂ → ℂ} (hf : Vendor.LogMellinAdmissible f δ P H) {c : ℝ} (hc : 1 < c) :
    Complex.VerticalIntegrable H c := by
  obtain ⟨C, hC0, hCbound⟩ := hf.rapid_vertical_decay c c (by linarith [hf.delta_pos]) le_rfl 2
  have hline := logSpectrum_continuousOn_line hf hc
  have hcontψ : ContinuousOn (fun y : ℝ => (1 + |y|)^2 * ‖H ((c : ℂ) + (y : ℂ) * Complex.I)‖)
      (Set.Icc (-1) 1) :=
    (((continuous_const.add continuous_abs).pow 2).mul hline.norm).continuousOn
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 1)).exists_bound_of_continuousOn hcontψ
  have hboundD : ∀ y : ℝ, ‖H ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      max C M * (1 + |y|) ^ (-(2:ℝ)) := by
    intro y
    have hpos : (0:ℝ) ≤ (1 + |y|) ^ (-(2:ℝ)) := by positivity
    rcases le_total 1 |y| with hle | hle
    · have hy := hCbound c y le_rfl le_rfl hle
      have hBpos : 0 < (1 + |y|)^2 := by positivity
      have h1 : ‖H ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C / (1 + |y|)^2 :=
        (le_div_iff₀ hBpos).mpr (by rw [mul_comm]; exact hy)
      have h2 : C / (1 + |y|)^2 = C * (1 + |y|) ^ (-(2:ℝ)) := by
        rw [div_eq_mul_inv, Real.rpow_neg (by positivity)]
        norm_num
      rw [h2] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left C M) hpos)
    · have hmem : y ∈ Set.Icc (-1) 1 := by
        rw [Set.mem_Icc]
        have := abs_le.mp hle
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
      have hy := hM y hmem
      have hy' : (1 + |y|)^2 * ‖H ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤ M := by
        have hnn : 0 ≤ (1 + |y|)^2 * ‖H ((c : ℂ) + (y : ℂ) * Complex.I)‖ := by positivity
        simpa only [Real.norm_eq_abs, abs_of_nonneg hnn] using hy
      have hBpos : 0 < (1 + |y|)^2 := by positivity
      have h1 : ‖H ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤ M / (1 + |y|)^2 :=
        (le_div_iff₀ hBpos).mpr (by rw [mul_comm]; exact hy')
      have h2 : M / (1 + |y|)^2 = M * (1 + |y|) ^ (-(2:ℝ)) := by
        rw [div_eq_mul_inv, Real.rpow_neg (by positivity)]
        norm_num
      rw [h2] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right C M) hpos)
  refine Integrable.mono'
    ((integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)).const_mul (max C M))
    hline.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  simpa only [Real.norm_eq_abs] using hboundD y

theorem logSource_mellinConvergent {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}
    {H : ℂ → ℂ} (hf : Vendor.LogMellinAdmissible f δ P H) {c : ℝ} (hc : 1 < c) :
    MellinConvergent f (c : ℂ) := by
  have hpow : ContinuousOn (fun t : ℝ => (t:ℂ)^((c:ℂ)-1)) (Set.Ioi 0) :=
    fun t ht => (Complex.continuousAt_ofReal_cpow_const t ((c:ℂ)-1) (Or.inr (ne_of_gt ht))).continuousWithinAt
  have hPint : IntegrableOn (fun t : ℝ => (t:ℂ)^((c:ℂ)-1) * P.eval (Real.log t : ℂ)) (Set.Ioo 0 1) := by
    have hTP := (Vendor.truncatedLogPolynomial_mellinConvergent P (c:ℂ)
      (by simp only [Complex.ofReal_re]; linarith)).mono_set (Set.Ioo_subset_Ioi_self (b := (0:ℝ)) (a := 1))
    refine hTP.congr_fun ?_ measurableSet_Ioo
    intro t ht
    simp [Vendor.truncatedLogPolynomial, ht.1, ht.2, smul_eq_mul]
  have hGint : IntegrableOn (fun t : ℝ => (t:ℂ)^((c:ℂ)-1) * (f t - P.eval (Real.log t : ℂ)))
      (Set.Ioo 0 1) := by
    obtain ⟨C, hC0, hCbound⟩ := hf.origin_remainder 0
    have hdom : IntegrableOn (fun t : ℝ => C * t^(c-1+δ)) (Set.Ioo 0 1) := by
      have hbase : IntegrableOn (fun t : ℝ => t^(c-1+δ)) (Set.Ioo 0 1) :=
        (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mpr (by linarith [hf.delta_pos])
      exact hbase.integrable.const_mul C
    refine Integrable.mono' hdom ?_ ?_
    · have hlog : ContinuousOn (fun t : ℝ => (Real.log t : ℂ)) (Set.Ioi 0) :=
        Complex.continuous_ofReal.comp_continuousOn
          (Real.continuousOn_log.mono (by intro x hx; simpa using ne_of_gt hx))
      have hPlog : ContinuousOn (fun t : ℝ => P.eval (Real.log t : ℂ)) (Set.Ioi 0) :=
        (Polynomial.continuous P).comp_continuousOn hlog
      have hgc : ContinuousOn (fun t : ℝ => f t - P.eval (Real.log t : ℂ)) (Set.Ioi 0) :=
        hf.contDiffOn.continuousOn.sub hPlog
      exact ((hpow.mul hgc).mono (Set.Ioo_subset_Ioi_self (b := (0:ℝ)) (a := 1))).aestronglyMeasurable
        measurableSet_Ioo
    · rw [ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have ht1 : 0 < t := ht.1
      have htle : t ≤ 1 := ht.2.le
      have hnorm : ‖(t:ℂ)^((c:ℂ)-1)‖ = t^(c-1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ht1]; simp
      have hb := hCbound t ht1 htle
      simp only [Vendor.EulerIter_zero] at hb
      calc ‖(t:ℂ)^((c:ℂ)-1) * (f t - P.eval (Real.log t : ℂ))‖
          = ‖(t:ℂ)^((c:ℂ)-1)‖ * ‖f t - P.eval (Real.log t : ℂ)‖ := norm_mul _ _
        _ ≤ t^(c-1) * (C * t^δ) := by
            rw [hnorm]
            exact mul_le_mul_of_nonneg_left hb (by positivity)
        _ = C * t^(c-1+δ) := by
            rw [Real.rpow_add ht1]; ring
  have hFint : IntegrableOn (fun t : ℝ => (t:ℂ)^((c:ℂ)-1) * f t) (Set.Ici 1) := by
    obtain ⟨n, hn⟩ := exists_nat_ge (c + 1)
    have hnc : c < (n:ℝ) := by linarith
    obtain ⟨C, hC0, hCbound⟩ := hf.rapid_decay 0 n
    have hdom : IntegrableOn (fun t : ℝ => C * t^(c-1-(n:ℝ))) (Set.Ici 1) := by
      have hbase : IntegrableOn (fun t : ℝ => t^(c-1-(n:ℝ))) (Set.Ici 1) :=
        (integrableOn_Ici_iff_integrableOn_Ioi (f := fun t : ℝ => t^(c-1-(n:ℝ))) (b := 1)).mpr
          (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one)
      exact hbase.integrable.const_mul C
    refine Integrable.mono' hdom ?_ ?_
    · have hfc : ContinuousOn (fun t : ℝ => f t) (Set.Ioi 0) := hf.contDiffOn.continuousOn
      exact ((hpow.mul hfc).mono (by intro x hx; exact lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp hx))).aestronglyMeasurable
        measurableSet_Ici
    · rw [ae_restrict_iff' measurableSet_Ici]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have ht1 : 1 ≤ t := ht
      have hpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
      have hnorm : ‖(t:ℂ)^((c:ℂ)-1)‖ = t^(c-1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]; simp
      have hb := hCbound t ht1
      simp only [Vendor.EulerIter_zero] at hb
      calc ‖(t:ℂ)^((c:ℂ)-1) * f t‖
          = ‖(t:ℂ)^((c:ℂ)-1)‖ * ‖f t‖ := norm_mul _ _
        _ ≤ t^(c-1) * (C * t^(-(n:ℝ))) := by
            rw [hnorm]
            exact mul_le_mul_of_nonneg_left hb (by positivity)
        _ = C * t^(c-1-(n:ℝ)) := by
            rw [show c - 1 - (n:ℝ) = (c-1) + (-(n:ℝ)) by ring, Real.rpow_add hpos]; ring
  have hnear : IntegrableOn (fun t : ℝ => (t:ℂ)^((c:ℂ)-1) * f t) (Set.Ioo 0 1) := by
    refine (hPint.add hGint).congr_fun ?_ measurableSet_Ioo
    intro t ht
    simp only [Pi.add_apply]
    ring
  have hsub : Set.Ioi (0:ℝ) ⊆ Set.Ioo 0 1 ∪ Set.Ici 1 := by
    intro t ht
    rcases lt_or_ge t 1 with h | h
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr h
  exact (hnear.union hFint).mono_set hsub

theorem idealLogMellin_source_interchange
    (a : Ideal (𝓞 F) → ℂ) (ha : ∀ I, I ≠ ⊥ → ‖a I‖ ≤ 1)
    {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}
    (hf : Vendor.LogMellinAdmissible f δ P H)
    {X c : ℝ} (hX : 0 < X) (hc : 1 < c) :
    Complex.VerticalIntegrable
      (fun s => H s * (X : ℂ) ^ s * idealCoefficientLSeries a s) c ∧
    Vendor.verticalIntegral c
      (fun s => H s * (X : ℂ) ^ s * idealCoefficientLSeries a s) =
      ∑' I : Ideal (𝓞 F), idealMellinWeight a f X I := by
  have hline := logSpectrum_continuousOn_line hf hc
  have hVIH := logSpectrum_verticalIntegrable hf hc
  have hMC := logSource_mellinConvergent hf hc

  have hVI_mellin : Complex.VerticalIntegrable (mellin f) c := by
    refine hVIH.congr (Filter.Eventually.of_forall fun y => ?_)
    exact hf.eq_mellin _ (by simp; linarith)

  have hk : ∀ x : ℝ, 0 < x → f x = mellinInv c H x := by
    intro x hx
    have hfx : mellinInv c (mellin f) x = f x :=
      mellinInv_mellin_eq c f hx hMC hVI_mellin
        ((hf.contDiffOn.contDiffAt (Ioi_mem_nhds hx)).continuousAt)
    have hsame : mellinInv c H x = mellinInv c (mellin f) x := by
      simp only [mellinInv]
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      rw [hf.eq_mellin _ (by simp; linarith)]
    rw [hsame, hfx]

  have hcpow : ∀ s : ℂ, (((X⁻¹ : ℝ) : ℂ)) ^ (-s) = (X : ℂ) ^ s := by
    intro s
    have harg : (X : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hX.le]; exact Real.pi_ne_zero.symm
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]
  obtain ⟨-, -, -, -, -, hVI, hVeq⟩ :=
    idealLogMellin_inverseSpectrum_interchange a ha H f (Y := X⁻¹) hc (by positivity) hline hVIH hk
  refine ⟨?_, ?_⟩
  · refine hVI.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hcpow]
  · have hfun : (fun s => H s * (X : ℂ) ^ s * idealCoefficientLSeries a s)
        = (fun s => H s * (((X⁻¹ : ℝ) : ℂ)) ^ (-s) * idealCoefficientLSeries a s) := by
      funext s
      rw [hcpow s]
    rw [hfun, hVeq]
    change ∑' (I : ↑({I : Ideal (𝓞 F) | I ≠ ⊥})),
        (fun J : Ideal (𝓞 F) => a J * f (X⁻¹ * ↑(Ideal.absNorm J))) ↑I =
      ∑' I : Ideal (𝓞 F), idealMellinWeight a f X I
    rw [tsum_subtype ({I : Ideal (𝓞 F) | I ≠ ⊥})
      (fun J : Ideal (𝓞 F) => a J * f (X⁻¹ * ↑(Ideal.absNorm J)))]
    apply tsum_congr
    intro I
    rw [idealMellinWeight, Set.indicator_apply]
    by_cases hI : I = ⊥
    · simp [hI]
    · simp [hI, inv_mul_eq_div]

end DedekindZetaZeroFree.LargeSieve

end
