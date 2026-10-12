module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompletionBallMass

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneMellin.AdditiveMellinIntegrability
open IsDedekindDomain NumberField

theorem mellin_unit_shells_cover
    (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    (⋃ n : ℕ, {x : v.adicCompletion F |
      ‖x‖ = ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n}) =
      {x : v.adicCompletion F | 0 < ‖x‖ ∧ ‖x‖ ≤ 1} := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < Ideal.absNorm v.asIdeal := zero_lt_one.trans hq
  have hqi0 : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ := inv_pos.mpr hq0
  have hqi1 : ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hq0]
    exact hq.le
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨?_, ?_⟩
    · rw [hn]; exact pow_pos hqi0 n
    · rw [hn]; exact pow_le_one₀ hqi0.le hqi1
  · rintro ⟨hpos, hle⟩
    have hx : x ≠ 0 := by rintro rfl; simp at hpos
    obtain ⟨k, hk⟩ : ∃ k : ℤ, ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
      refine ⟨WithZero.log (Valued.v x), ?_⟩
      rw [FinitePlace.norm_def]
      rw [WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v)
        (by simpa [Valued.v] using hx)]
      rw [NNReal.coe_zpow]
      rfl
    have hk0 : k ≤ 0 := by
      rw [← zpow_le_one_iff_right₀ hq]
      rw [← hk]; exact hle
    refine ⟨(-k).toNat, ?_⟩
    have key : ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ (-k).toNat
        = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
      rw [show ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ (-k).toNat
          = (Ideal.absNorm v.asIdeal : ℝ) ^ (-((-k).toNat : ℤ)) by
        rw [zpow_neg, zpow_natCast, ← inv_pow]]
      rw [Int.toNat_of_nonneg (by omega), neg_neg]
    rw [hk, key]

end DedekindZetaZeroFree.KPRankOneMellin.AdditiveMellinIntegrability

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneMellin.AdditiveMellinIntegrability
open MeasureTheory IsDedekindDomain NumberField

theorem mellin_unit_shell_mass_bound
    (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      MeasurableSet {x : v.adicCompletion F |
        ‖x‖ = ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n} ∧
      μ {x : v.adicCompletion F |
        ‖x‖ = ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n} ≠ ⊤ ∧
      μ.real {x : v.adicCompletion F |
        ‖x‖ = ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n} ≤
          C * ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n := by
  have hm := (BorelSpace.measurable_eq (α := v.adicCompletion F))
  cases hm
  refine ⟨μ.real {x : v.adicCompletion F | ‖x‖ ≤ 1}, ENNReal.toReal_nonneg, ?_⟩
  intro n
  have hcompact : IsCompact {x : v.adicCompletion F |
      ‖x‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      isCompact_closedBall (0 : v.adicCompletion F)
        (((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n)
  have hfinite := hcompact.measure_lt_top (μ := μ)
  have hsub : {x : v.adicCompletion F |
      ‖x‖ = ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n} ⊆
      {x : v.adicCompletion F | ‖x‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n} :=
    fun x hx => le_of_eq hx
  refine ⟨measurableSet_eq_fun (by fun_prop) measurable_const,
    (lt_of_le_of_lt (measure_mono hsub) hfinite).ne, ?_⟩
  have hmass := CompletionHaarModule.closedBall_measure F v μ (-(n : ℤ))
  have hpow : (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n : ℤ)) =
      ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hpow] at hmass
  calc
    _ ≤ μ.real {x : v.adicCompletion F |
        ‖x‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n} :=
      measureReal_mono hsub hfinite.ne
    _ = _ := by rw [hmass, mul_comm]

end DedekindZetaZeroFree.KPRankOneMellin.AdditiveMellinIntegrability

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneMellin.AdditiveMellinIntegrability
open MeasureTheory Function

theorem mellin_integrableOn_compl_punctured_unit_ball
    {K : Type*} [NormedField K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure]
    (φ : K → ℂ) (hφ : Continuous φ) (hφcs : HasCompactSupport φ)
    (s : ℂ) :
    IntegrableOn (fun x : K => φ x * (‖x‖ : ℂ) ^ (s - 1))
      {x : K | 0 < ‖x‖ ∧ ‖x‖ ≤ 1}ᶜ μ := by
  let f : K → ℂ := fun x => φ x * (‖x‖ : ℂ) ^ (s - 1)

  have hset : {x : K | 0 < ‖x‖ ∧ ‖x‖ ≤ 1}ᶜ = {0} ∪ {x : K | 1 < ‖x‖} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h
      by_cases hx : x = 0
      · exact Or.inl hx
      · refine Or.inr ?_
        rw [not_and_or] at h
        rcases h with h | h
        · exact absurd (norm_pos_iff.mpr hx) h
        · exact lt_of_not_ge h
    · rintro (rfl | h)
      · simp
      · intro hc
        exact absurd hc.2 (not_le.mpr h)
  rw [hset]
  refine IntegrableOn.union ?_ ?_
  ·
    refine integrableOn_singleton ?_ ?_
    · exact enorm_ne_top
    · exact isCompact_singleton.measure_lt_top
  ·

    set B : Set K := {x : K | 1 < ‖x‖} with hBdef
    have hBmeas : MeasurableSet B := (isOpen_lt continuous_const continuous_norm).measurableSet
    have hK' : IsCompact (tsupport φ ∩ {x : K | (1:ℝ) ≤ ‖x‖}) :=
      hφcs.isCompact.inter_right (isClosed_le continuous_const continuous_norm)
    have hcont : ContinuousOn f (tsupport φ ∩ {x : K | (1:ℝ) ≤ ‖x‖}) := by
      intro x hx
      apply ContinuousAt.continuousWithinAt
      have hx1 : (1:ℝ) ≤ ‖x‖ := hx.2
      have hne : ‖x‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hx1)
      refine hφ.continuousAt.mul ?_
      exact (Complex.continuousAt_ofReal_cpow_const (‖x‖) (s - 1) (Or.inr hne)).comp
        (f := fun y : K => ‖y‖) continuous_norm.continuousAt
    have hint : IntegrableOn f (tsupport φ ∩ {x : K | (1:ℝ) ≤ ‖x‖}) μ :=
      hcont.integrableOn_compact hK'
    have hsupp : support f ⊆ tsupport φ := by
      intro x hx
      rw [mem_support] at hx
      apply subset_tsupport
      intro hφ0
      exact hx (by simp [f, hφ0])
    have hsub : B ∩ support f ⊆ tsupport φ ∩ {x : K | (1:ℝ) ≤ ‖x‖} := by
      intro x hx
      have hx1 : (1:ℝ) < ‖x‖ := hx.1
      exact ⟨hsupp hx.2, hx1.le⟩
    exact IntegrableOn.of_inter_support hBmeas (hint.mono_set hsub)

end DedekindZetaZeroFree.KPRankOneMellin.AdditiveMellinIntegrability

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPRankOneMellin.AdditiveMellinIntegrability

open MeasureTheory IsDedekindDomain NumberField

theorem additive_mellin_integrableOn_of_geometric_shells {K : Type*} [NormedField K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    (φ : K → ℂ) (hφ : Continuous φ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖φ x‖ ≤ B)
    (shell : ℕ → Set K) (hm : ∀ n, MeasurableSet (shell n))
    (hfinite : ∀ n, μ (shell n) ≠ ⊤)
    (R r C : ℝ) (hR : 0 < R) (hr : 0 < r) (hr1 : r < 1) (hC : 0 ≤ C)
    (hnorm : ∀ n x, x ∈ shell n → ‖x‖ = R * r ^ n)
    (hmass : ∀ n, μ.real (shell n) ≤ C * r ^ n)
    (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : K => φ x * (‖x‖ : ℂ) ^ (s - 1)) (⋃ n, shell n) μ := by
  let f : K → ℂ := fun x => φ x * (‖x‖ : ℂ) ^ (s - 1)
  have hi (n : ℕ) : IntegrableOn f (shell n) μ := by
    have hc : IntegrableOn (fun _ : K => ((R * r ^ n : ℝ) : ℂ) ^ (s - 1))
        (shell n) μ := integrableOn_const (hfinite n)
    have hd : IntegrableOn (fun x : K => φ x * ((R * r ^ n : ℝ) : ℂ) ^ (s - 1))
        (shell n) μ := hc.bdd_mul hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
    exact hd.congr_fun (fun x hx => by simp [f, hnorm n x hx]) (hm n)
  have hweight (n : ℕ) :
      (R * r ^ n) ^ (s.re - 1) * (C * r ^ n) =
        (R ^ (s.re - 1) * C) * (r ^ s.re) ^ n := by
    rw [Real.mul_rpow hR.le (pow_nonneg hr.le _), ← Real.rpow_pow_comm hr.le]
    have he : (r ^ (s.re - 1)) ^ n * r ^ n = (r ^ s.re) ^ n := by
      rw [← mul_pow]
      congr 1
      calc
        r ^ (s.re - 1) * r = r ^ (s.re - 1) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = r ^ (s.re - 1 + 1) := (Real.rpow_add hr _ _).symm
        _ = r ^ s.re := by congr 1; ring
    calc
      R ^ (s.re - 1) * (r ^ (s.re - 1)) ^ n * (C * r ^ n) =
          (R ^ (s.re - 1) * C) * ((r ^ (s.re - 1)) ^ n * r ^ n) := by ring
      _ = _ := by rw [he]
  have hb (n : ℕ) : (∫ x in shell n, ‖f x‖ ∂μ) ≤
      (B * R ^ (s.re - 1) * C) * (r ^ s.re) ^ n := by
    have hk : ∀ x ∈ shell n, ‖f x‖ ≤ B * (R * r ^ n) ^ (s.re - 1) := by
      intro x hx
      change ‖φ x * (‖x‖ : ℂ) ^ (s - 1)‖ ≤ _
      rw [norm_mul, hnorm n x hx,
        Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hR (pow_pos hr _))]
      simp only [Complex.sub_re, Complex.one_re]
      exact mul_le_mul_of_nonneg_right (hbound x) (Real.rpow_nonneg (by positivity) _)
    calc
      (∫ x in shell n, ‖f x‖ ∂μ) ≤
          ∫ _ in shell n, B * (R * r ^ n) ^ (s.re - 1) ∂μ :=
        setIntegral_mono_on (hi n).norm (integrableOn_const (hfinite n)) (hm n) hk
      _ = (B * (R * r ^ n) ^ (s.re - 1)) * μ.real (shell n) := by
        simp [mul_comm]
      _ ≤ (B * (R * r ^ n) ^ (s.re - 1)) * (C * r ^ n) :=
        mul_le_mul_of_nonneg_left (hmass n) (by positivity)
      _ = (B * R ^ (s.re - 1) * C) * (r ^ s.re) ^ n := by
        rw [mul_assoc B, hweight]
        ring
  apply integrableOn_iUnion_of_summable_integral_norm hi
  exact Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _)) hb
    ((summable_geometric_of_lt_one (Real.rpow_nonneg hr.le _)
      (Real.rpow_lt_one hr.le hr1 hs)).mul_left _)

theorem additive_mellin_integrable
    (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (φ : v.adicCompletion F → ℂ)
    (hφlc : IsLocallyConstant φ) (hφcs : HasCompactSupport φ)
    (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun x : v.adicCompletion F => φ x * (‖x‖ : ℂ) ^ (s - 1)) μ := by
  let r : ℝ := (Ideal.absNorm v.asIdeal : ℝ)⁻¹
  let shell : ℕ → Set (v.adicCompletion F) := fun n => {x | ‖x‖ = r ^ n}
  have hq : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hr : 0 < r := inv_pos.mpr (lt_trans zero_lt_one hq)
  have hr1 : r < 1 := by
    dsimp [r]
    exact (inv_lt_one₀ (lt_trans zero_lt_one hq)).mpr hq
  obtain ⟨C, hC, hmass⟩ := mellin_unit_shell_mass_bound F v μ
  obtain ⟨B, hB⟩ := hφlc.continuous.bounded_above_of_compact_support hφcs
  have hBnonneg : 0 ≤ B := (norm_nonneg (φ 0)).trans (hB 0)
  have htail : IntegrableOn
      (fun x : v.adicCompletion F => φ x * (‖x‖ : ℂ) ^ (s - 1))
      (⋃ n, shell n) μ :=
    additive_mellin_integrableOn_of_geometric_shells μ φ hφlc.continuous B hBnonneg hB
      shell (fun n => (hmass n).1) (fun n => (hmass n).2.1)
      1 r C zero_lt_one hr hr1 hC
      (fun n x hx => by simpa only [one_mul] using (show ‖x‖ = r ^ n from hx))
      (fun n => (hmass n).2.2) s hs
  have hcover : (⋃ n, shell n) =
      {x : v.adicCompletion F | 0 < ‖x‖ ∧ ‖x‖ ≤ 1} :=
    mellin_unit_shells_cover F v
  rw [hcover] at htail
  have hout := mellin_integrableOn_compl_punctured_unit_ball μ φ hφlc.continuous hφcs s
  have hall := htail.union hout
  simpa only [Set.union_compl_self, integrableOn_univ] using hall

end DedekindZetaZeroFree.KPRankOneMellin.AdditiveMellinIntegrability

end

end
