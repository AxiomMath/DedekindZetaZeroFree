module

public import DedekindZetaZeroFree.Moments.Probes.AnnularWeightsAndCancellingProfiles

@[expose] public section

namespace DedekindZetaZeroFree.ProbeSheetGlobalIntegrability
noncomputable section
open scoped Classical NumberField WithZero
open NumberField IsDedekindDomain MeasureTheory Set

variable {K : Type*} [NontriviallyNormedField K] [ProperSpace K]
private theorem compact_annulus (a R : ℝ) (ha : 0 < a) :
    IsCompact {x : Kˣ | a ≤ ‖x.val‖ ∧ ‖x.val‖ ≤ R} := by
  apply Units.isOpenEmbedding_val.isEmbedding.isCompact_iff.mpr
  have he : Units.val '' {x : Kˣ | a ≤ ‖x.val‖ ∧ ‖x.val‖ ≤ R} =
      Metric.closedBall (0 : K) R ∩ {x | a ≤ ‖x‖} := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [Metric.mem_closedBall, dist_zero_right] using And.intro hu.2 hu.1
    · rintro ⟨hx, ha'⟩
      have hn : x ≠ 0 := by intro h; simp [h] at ha'; linarith
      exact ⟨Units.mk0 x hn, ⟨ha', by simpa [Metric.mem_closedBall, dist_zero_right] using hx⟩, rfl⟩
  rw [he]
  exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)

private theorem finite_generic [MeasurableSpace K] [BorelSpace K]
    (g : K → ℂ) (hg : Continuous g) (hc : HasCompactSupport g)
    (ν : Measure Kˣ) [ν.IsHaarMeasure] (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : Kˣ => g x.val * (‖x.val‖ : ℂ) ^ z) ν := by
  letI : BorelSpace Kˣ := ⟨by
    change (‹MeasurableSpace K›).comap Units.val = borel _
    rw [BorelSpace.measurable_eq (α := K)]
    rw [← borel_comap, ← Units.isOpenEmbedding_val.isEmbedding.isInducing.eq_induced]⟩
  obtain ⟨p, hp, hp1⟩ := NormedField.exists_norm_lt_one K
  let u : Kˣ := Units.mk0 p (norm_pos_iff.mp hp)
  let r : ℝ := ‖p‖
  have hr : 0 < r := hp
  have hr1 : r < 1 := hp1
  obtain ⟨R, hR, hRg⟩ := hc.exists_pos_le_norm
  obtain ⟨C, hC⟩ := hg.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hC' : ∀ x, ‖g x‖ ≤ C := fun x => hC (mem_range_self x)
  have hC0 : 0 ≤ C := (norm_nonneg (g 0)).trans (hC' 0)
  let s : ℕ → Set Kˣ := fun n => {x | r ^ (n+1) * R ≤ ‖x.val‖ ∧ ‖x.val‖ ≤ r^n * R}
  have hs (n : ℕ) : IsCompact (s n) := compact_annulus _ _ (mul_pos (pow_pos hr _) hR)
  have hmeasure (n : ℕ) : ν (s n) = ν (s 0) := by
    have he : (fun x : Kˣ => u ^ n * x) ⁻¹' s n = s 0 := by
      ext x
      simp only [s, mem_preimage, mem_setOf_eq, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow]
      change (r^(n+1)*R ≤ r^n*‖x.val‖ ∧ r^n*‖x.val‖ ≤ r^n*R) ↔ _
      rw [pow_succ]
      simp only [pow_zero, pow_one, one_mul]
      rw [mul_assoc, mul_le_mul_iff_right₀ (pow_pos hr n), mul_le_mul_iff_right₀ (pow_pos hr n)]
      simp
    rw [← measure_preimage_mul ν (u ^ n) (s n), he]
  let f : Kˣ → ℂ := fun x => g x.val * (‖x.val‖ : ℂ) ^ z
  have hfc : Continuous f := by
    apply (hg.comp Units.continuous_val).mul
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (Complex.continuousAt_ofReal_cpow ‖x.val‖ z (Or.inl hz)).comp
      (x := x) ((continuous_norm.comp Units.continuous_val).continuousAt.prodMk continuousAt_const)
  have hbound (n : ℕ) (x : Kˣ) (hx : x ∈ s n) :
      ‖f x‖ ≤ C * R ^ z.re * (r ^ z.re) ^ n := by
    dsimp [f]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr x.ne_zero)]
    calc
      ‖g x.val‖ * ‖x.val‖ ^ z.re ≤ C * (r^n * R) ^ z.re :=
        mul_le_mul (hC' _) (Real.rpow_le_rpow (norm_nonneg _) hx.2 hz.le)
          (Real.rpow_nonneg (norm_nonneg _) _) hC0
      _ = _ := by
        rw [Real.mul_rpow (pow_nonneg hr.le _) hR.le,
          ← Real.rpow_natCast_mul hr.le, mul_comm (n : ℝ) z.re,
          Real.rpow_mul_natCast hr.le]
        ring
  have hi (n : ℕ) : IntegrableOn f (s n) ν := hfc.continuousOn.integrableOn_compact (hs n)
  have hsum : Summable (fun n : ℕ => ∫ x in s n, ‖f x‖ ∂ν) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _))
      (fun n => ?_)
      ((summable_geometric_of_norm_lt_one (x := r ^ z.re)
        (by rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hr.le _)]; exact Real.rpow_lt_one hr.le hr1 hz)).mul_left
        (C * R ^ z.re * ν.real (s 0)))
    have hb := norm_setIntegral_le_of_norm_le_const (μ := ν) (f := fun x => ‖f x‖) (hs n).measure_lt_top
      (fun x hx => by simpa only [norm_norm] using hbound n x hx)
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))] at hb
    simpa [Measure.real, hmeasure n, mul_assoc, mul_comm, mul_left_comm] using hb
  have hu : IntegrableOn f (⋃ n, s n) ν := integrableOn_iUnion_of_summable_integral_norm hi hsum
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hu
  intro x hx
  have hsmall : ‖x.val‖ < R := by
    by_contra h
    have hg0 := hRg x.val (le_of_not_gt h)
    exact hx (by simp [f, hg0])
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one
    (div_pos (norm_pos_iff.mpr x.ne_zero) hR) (by rw [div_le_one₀ hR]; exact hsmall.le) hr hr1
  apply mem_iUnion.mpr
  refine ⟨n, ?_, ?_⟩
  · exact (le_div_iff₀ hR).mp hn.le
  · exact (div_le_iff₀ hR).mp hn'

variable (F : Type) [Field F] [NumberField F]
 local instance adicCompletionMeasurableSpaceFiniteLocalUnitsIntegrability (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _
 local instance adicCompletionBorelSpaceFiniteLocalUnitsIntegrability (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem finiteUnitsMellin_integrable
    (v : HeightOneSpectrum (𝓞 F))
    (g : v.adicCompletion F → ℂ)
    (hlc : IsLocallyConstant g) (hc : HasCompactSupport g)
    (ν : Measure (v.adicCompletion F)ˣ) [ν.IsHaarMeasure]
    (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : (v.adicCompletion F)ˣ =>
      g x.val * (‖x.val‖ : ℂ) ^ z) ν := by
  letI : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) ℤᵐ⁰
  exact finite_generic g hlc.continuous hc ν z hz

end
end DedekindZetaZeroFree.ProbeSheetGlobalIntegrability
