module

public import DedekindZetaZeroFree.Arithmetic.Ideals.InverseNormPowerSums
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.PositiveLineInversion
public import DedekindZetaZeroFree.Analysis.MellinVerticalIntegral

@[expose] public section

noncomputable section
open MeasureTheory
open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve

variable {F : Type*} [Field F] [NumberField F]

def idealCoefficientLSeries (a : Ideal (𝓞 F) → ℂ) (s : ℂ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
    a I.val * (Ideal.absNorm I.val : ℂ) ^ (-s)

def idealMellinWeight (a : Ideal (𝓞 F) → ℂ) (h : ℝ → ℂ) (X : ℝ)
    (I : Ideal (𝓞 F)) : ℂ :=
  if I = ⊥ then 0 else a I * h ((Ideal.absNorm I : ℝ) / X)

theorem idealMellinWeight_hasFiniteSupport (a : Ideal (𝓞 F) → ℂ)
    {h : ℝ → ℂ} (hcompact : HasCompactSupport h) {X : ℝ} (hX : 0 < X) :
    Function.HasFiniteSupport (idealMellinWeight a h X) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, Function.support h ⊆ Set.Icc (-R) R := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1
      (hcompact.isBounded.subset (subset_tsupport h))
    refine ⟨R, fun x hx => ?_⟩
    have hx' : |x| ≤ R := by
      simpa [Real.dist_eq] using hR hx
    exact ⟨neg_le_of_abs_le hx', le_of_abs_le hx'⟩
  refine Set.Finite.subset (finite_ideals_absNorm_le F (R * X)) fun I hI => ?_
  simp only [Function.mem_support, Set.mem_setOf_eq] at hI ⊢
  rw [idealMellinWeight] at hI
  split_ifs at hI with hbot
  · exact absurd rfl hI
  have hne : h ((Ideal.absNorm I : ℝ) / X) ≠ 0 := fun hc => hI (by rw [hc, mul_zero])
  have hmem := hR (by simpa [Function.mem_support] using hne)
  have hle : (Ideal.absNorm I : ℝ) / X ≤ R := hmem.2
  rw [div_le_iff₀ hX] at hle
  exact hle

theorem idealCoefficientLSeries_summable (a : Ideal (𝓞 F) → ℂ)
    (ha0 : a ⊥ = 0) (ha : ∀ I, ‖a I‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖a I.val * (Ideal.absNorm I.val : ℂ) ^ (-s)‖) ∧
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      a I.val * (Ideal.absNorm I.val : ℂ) ^ (-s)) := by
  have hbase : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      (Ideal.absNorm I.val : ℝ) ^ (-s.re)) :=
    ((summable_ideal_inverse_power F s.re hs).subtype (fun I : Ideal (𝓞 F) => I ≠ ⊥)).congr
      fun I => by simp [I.property]
  have hbound : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      ‖a I.val * (Ideal.absNorm I.val : ℂ) ^ (-s)‖ ≤
        (Ideal.absNorm I.val : ℝ) ^ (-s.re) := by
    intro I
    have hpos : 0 < (Ideal.absNorm I.val : ℝ) := by
      have hne : Ideal.absNorm I.val ≠ 0 := by
        simpa [Ideal.absNorm_eq_zero_iff] using I.property
      exact_mod_cast Nat.pos_of_ne_zero hne
    have hnorm : ‖(Ideal.absNorm I.val : ℂ) ^ (-s)‖ =
        (Ideal.absNorm I.val : ℝ) ^ (-s.re) := by
      rw [← Complex.ofReal_natCast]
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos hpos (-s)
    rw [norm_mul, hnorm]
    calc ‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-s.re)
        ≤ 1 * (Ideal.absNorm I.val : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (ha I.val) (Real.rpow_nonneg hpos.le _)
      _ = (Ideal.absNorm I.val : ℝ) ^ (-s.re) := one_mul _
  have hnorm : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖a I.val * (Ideal.absNorm I.val : ℂ) ^ (-s)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hbase
  exact ⟨hnorm, hnorm.of_norm⟩

private theorem countable_ideal (F : Type*) [Field F] [NumberField F] :
    Countable (Ideal (𝓞 F)) := by
  have h : (Set.univ : Set (Ideal (𝓞 F))) =
      ⋃ n : ℕ, {I | (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} := by
    ext I
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact ⟨Ideal.absNorm I, by push_cast; exact le_refl _⟩
  rw [← Set.countable_univ_iff, h]
  exact Set.countable_iUnion fun n => (finite_ideals_absNorm_le F (n : ℝ)).countable

private theorem norm_absNorm_cpow {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (w : ℂ) :
    ‖(Ideal.absNorm I : ℂ) ^ w‖ = (Ideal.absNorm I : ℝ) ^ w.re := by
  have hpos : 0 < (Ideal.absNorm I : ℝ) := by
    have hne : Ideal.absNorm I ≠ 0 := by
      simpa [Ideal.absNorm_eq_zero_iff] using hI
    exact_mod_cast Nat.pos_of_ne_zero hne
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hpos]

theorem idealMellin_verticalIntegrable (a : Ideal (𝓞 F) → ℂ)
    (ha0 : a ⊥ = 0) (ha : ∀ I, ‖a I‖ ≤ 1)
    {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    {X σ : ℝ} (hX : 0 < X) (hσ : 1 < σ) :
    Complex.VerticalIntegrable
      (fun s => mellin h s * (X : ℂ) ^ s * idealCoefficientLSeries a s) σ := by
  haveI : Countable (Ideal (𝓞 F)) := countable_ideal F
  set CL : ℝ := (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
    ‖a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(σ : ℂ))‖) with hCL
  have hCLsum : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(σ : ℂ))‖) :=
    (idealCoefficientLSeries_summable a ha0 ha hσ).1
  have hCLnn : 0 ≤ CL := by
    rw [hCL]; exact tsum_nonneg fun _ => norm_nonneg _

  have hLcont : Continuous (fun t : ℝ => idealCoefficientLSeries a (σ + t * Complex.I)) := by
    refine continuous_tsum (f := fun (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) (t : ℝ) =>
        a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(σ + t * Complex.I))) ?_ hCLsum ?_
    · intro I
      have hne : (Ideal.absNorm I.val : ℂ) ≠ 0 := by
        have : Ideal.absNorm I.val ≠ 0 := by
          simpa [Ideal.absNorm_eq_zero_iff] using I.property
        exact_mod_cast this
      have harg : Continuous fun t : ℝ => -(σ + t * Complex.I) := by fun_prop
      exact (harg.const_cpow (Or.inl hne)).const_mul (a I.val)
    · intro I t
      have h1 : ‖(Ideal.absNorm I.val : ℂ) ^ (-(σ + t * Complex.I))‖ =
          (Ideal.absNorm I.val : ℝ) ^ (-σ) := by
        rw [norm_absNorm_cpow I.property]
        simp
      have h2 : ‖(Ideal.absNorm I.val : ℂ) ^ (-(σ : ℂ))‖ =
          (Ideal.absNorm I.val : ℝ) ^ (-σ) := by
        rw [norm_absNorm_cpow I.property]
        simp
      rw [norm_mul, h1]
      rw [norm_mul, h2]
  have hint : Integrable (fun t : ℝ => mellin h (σ + t * Complex.I)) :=
    (Vendor.mellin_inversion_positive_line h hh hcompact σ (lt_trans zero_lt_one hσ)).1
  have hcontX : Continuous (fun t : ℝ => (X : ℂ) ^ (σ + t * Complex.I)) := by
    have hne : (X : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hX
    have harg : Continuous fun t : ℝ => σ + t * Complex.I := by fun_prop
    exact harg.const_cpow (Or.inl hne)
  refine Integrable.mono'
    (g := fun t : ℝ => CL * X ^ σ * ‖mellin h (σ + t * Complex.I)‖)
    ((hint.norm).const_mul (CL * X ^ σ)) ?_ (ae_of_all _ fun t => ?_)
  · exact ((hint.aestronglyMeasurable.mul hcontX.aestronglyMeasurable).mul
      hLcont.aestronglyMeasurable)
  · have hnormX : ‖(X : ℂ) ^ (σ + t * Complex.I)‖ = X ^ σ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
      norm_num
    have hsum_t : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
        a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(σ + t * Complex.I))) :=
      (idealCoefficientLSeries_summable a ha0 ha (s := (σ : ℂ) + t * Complex.I) (by
        simpa using hσ)).2
    have hle : ‖idealCoefficientLSeries a (σ + t * Complex.I)‖ ≤ CL := by
      rw [hCL, idealCoefficientLSeries]
      refine (norm_tsum_le_tsum_norm hsum_t.norm).trans (le_of_eq (tsum_congr fun I => ?_))
      have h2 : ‖(Ideal.absNorm I.val : ℂ) ^ (-(σ : ℂ))‖ =
          (Ideal.absNorm I.val : ℝ) ^ (-σ) := by
        rw [norm_absNorm_cpow I.property]
        simp
      have h1 : ‖(Ideal.absNorm I.val : ℂ) ^ (-(σ + t * Complex.I))‖ =
          (Ideal.absNorm I.val : ℝ) ^ (-σ) := by
        rw [norm_absNorm_cpow I.property]
        simp
      rw [norm_mul, norm_mul, h1, h2]
    rw [norm_mul, norm_mul, hnormX]
    have hnonneg : 0 ≤ ‖mellin h (σ + t * Complex.I)‖ * X ^ σ :=
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hX.le _)
    calc ‖mellin h (σ + t * Complex.I)‖ * X ^ σ * ‖idealCoefficientLSeries a (σ + t * Complex.I)‖
        ≤ ‖mellin h (σ + t * Complex.I)‖ * X ^ σ * CL :=
          mul_le_mul_of_nonneg_left hle hnonneg
      _ = CL * X ^ σ * ‖mellin h (σ + t * Complex.I)‖ := by ring

private theorem cpow_absNorm_div {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) {X : ℝ} (hX : 0 < X)
    (s : ℂ) :
    (Ideal.absNorm I : ℂ) ^ (-s) * (X : ℂ) ^ s =
      (((Ideal.absNorm I : ℝ) / X : ℝ) : ℂ) ^ (-s) := by
  have hpos : 0 < (Ideal.absNorm I : ℝ) := by
    have hne : Ideal.absNorm I ≠ 0 := by
      simpa [Ideal.absNorm_eq_zero_iff] using hI
    exact_mod_cast Nat.pos_of_ne_zero hne
  have harg : (X : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hX.le]
    exact Real.pi_ne_zero.symm
  rw [show (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) from
    (Complex.ofReal_natCast (Ideal.absNorm I)).symm]
  have h1 : (((Ideal.absNorm I : ℝ) / X : ℝ) : ℂ) =
      ((Ideal.absNorm I : ℝ) : ℂ) * ((X : ℝ) : ℂ)⁻¹ := by
    rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
  rw [h1, ← Complex.ofReal_inv (X : ℝ),
    Complex.mul_cpow_ofReal_nonneg hpos.le (inv_nonneg.mpr hX.le) (-s),
    Complex.ofReal_inv (X : ℝ), Complex.inv_cpow ((X : ℝ) : ℂ) (-s) harg,
    ← Complex.cpow_neg ((X : ℝ) : ℂ) (-s), neg_neg]

theorem idealMellin_finsum_eq_verticalIntegral (a : Ideal (𝓞 F) → ℂ)
    (ha0 : a ⊥ = 0) (ha : ∀ I, ‖a I‖ ≤ 1)
    {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    {X σ : ℝ} (hX : 0 < X) (hσ : 1 < σ) :
    (∑ᶠ I : Ideal (𝓞 F), idealMellinWeight a h X I) =
      Vendor.verticalIntegral σ
        (fun s => mellin h s * (X : ℂ) ^ s * idealCoefficientLSeries a s) := by
  haveI : Countable (Ideal (𝓞 F)) := countable_ideal F
  have hσ0 : 0 < σ := lt_trans zero_lt_one hσ
  have hLsum : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(σ : ℂ))‖) :=
    (idealCoefficientLSeries_summable a ha0 ha hσ).1
  have hLsum' : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-σ)) :=
    hLsum.congr fun I => by rw [norm_mul, norm_absNorm_cpow I.property]; simp
  have hint : Integrable (fun t : ℝ => mellin h (σ + t * Complex.I)) :=
    (Vendor.mellin_inversion_positive_line h hh hcompact σ hσ0).1
  have hcontX : Continuous (fun t : ℝ => (X : ℂ) ^ (σ + t * Complex.I)) := by
    have hne : (X : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hX
    have harg : Continuous fun t : ℝ => σ + t * Complex.I := by fun_prop
    exact harg.const_cpow (Or.inl hne)
  have hcoef_cont : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      Continuous (fun t : ℝ =>
        a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(σ + t * Complex.I))) := by
    intro I
    have hne : (Ideal.absNorm I.val : ℂ) ≠ 0 := by
      have : Ideal.absNorm I.val ≠ 0 := by
        simpa [Ideal.absNorm_eq_zero_iff] using I.property
      exact_mod_cast this
    have harg : Continuous fun t : ℝ => -(σ + t * Complex.I) := by fun_prop
    exact (harg.const_cpow (Or.inl hne)).const_mul (a I.val)
  set G : {I : Ideal (𝓞 F) // I ≠ ⊥} → ℝ → ℂ := fun I t =>
    mellin h (σ + t * Complex.I) * (X : ℂ) ^ (σ + t * Complex.I) *
      (a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(σ + t * Complex.I))) with hG
  have hnormX : ∀ t : ℝ, ‖(X : ℂ) ^ (σ + t * Complex.I)‖ = X ^ σ := by
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp
  have hG_le : ∀ (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) (t : ℝ),
      ‖G I t‖ ≤ (X ^ σ * (‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-σ))) *
        ‖mellin h (σ + t * Complex.I)‖ := by
    intro I t
    have hnormN : ‖(Ideal.absNorm I.val : ℂ) ^ (-(σ + t * Complex.I))‖ =
        (Ideal.absNorm I.val : ℝ) ^ (-σ) := by
      rw [norm_absNorm_cpow I.property]; simp
    change ‖mellin h (σ + t * Complex.I) * (X : ℂ) ^ (σ + t * Complex.I) *
      (a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(σ + t * Complex.I)))‖ ≤ _
    rw [norm_mul, norm_mul, norm_mul, hnormX t, hnormN]
    exact le_of_eq (by ring)
  have hG_int : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥}, Integrable (G I) := by
    intro I
    have hmeas : AEStronglyMeasurable (G I) := by
      change AEStronglyMeasurable (fun t : ℝ =>
        mellin h (σ + t * Complex.I) * (X : ℂ) ^ (σ + t * Complex.I) *
          (a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(σ + t * Complex.I))))
      exact (hint.aestronglyMeasurable.mul hcontX.aestronglyMeasurable).mul
        (hcoef_cont I).aestronglyMeasurable
    refine Integrable.mono' (g := fun t : ℝ =>
      (X ^ σ * (‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-σ))) *
        ‖mellin h (σ + t * Complex.I)‖)
      ((hint.norm).const_mul _) hmeas (ae_of_all _ fun t => hG_le I t)
  set A : ℝ := ∫ t : ℝ, ‖mellin h (σ + t * Complex.I)‖ with hA
  have hG_sum : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => ∫ t : ℝ, ‖G I t‖) := by
    refine Summable.of_nonneg_of_le (fun I => integral_nonneg fun t => norm_nonneg _) ?_
      (hLsum'.mul_left (X ^ σ * A))
    intro I
    have hmaj : Integrable (fun t : ℝ =>
        (X ^ σ * (‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-σ))) *
          ‖mellin h (σ + t * Complex.I)‖) := (hint.norm).const_mul _
    calc ∫ t : ℝ, ‖G I t‖
        ≤ ∫ t : ℝ, (X ^ σ * (‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-σ))) *
            ‖mellin h (σ + t * Complex.I)‖ :=
          integral_mono (hG_int I).norm hmaj (fun t => hG_le I t)
      _ = (X ^ σ * (‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-σ))) * A := by
          rw [integral_const_mul, hA]
      _ = (X ^ σ * A) * (‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-σ)) := by ring
  have hswap : (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, ∫ t : ℝ, G I t) =
      ∫ t : ℝ, ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, G I t :=
    integral_tsum_of_summable_integral_norm hG_int hG_sum
  have hpoint : ∀ t : ℝ, (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, G I t) =
      mellin h (σ + t * Complex.I) * (X : ℂ) ^ (σ + t * Complex.I) *
        idealCoefficientLSeries a (σ + t * Complex.I) := by
    intro t
    have hs : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
        a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(σ + t * Complex.I))) :=
      (idealCoefficientLSeries_summable a ha0 ha (s := (σ : ℂ) + t * Complex.I)
        (by simpa using hσ)).2
    rw [idealCoefficientLSeries, ← tsum_mul_left]
  have hper : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, G I t =
        a I.val * h ((Ideal.absNorm I.val : ℝ) / X) := by
    intro I
    have hpos : 0 < (Ideal.absNorm I.val : ℝ) := by
      have hne : Ideal.absNorm I.val ≠ 0 := by
        simpa [Ideal.absNorm_eq_zero_iff] using I.property
      exact_mod_cast Nat.pos_of_ne_zero hne
    have hxpos : 0 < (Ideal.absNorm I.val : ℝ) / X := div_pos hpos hX
    have hcongr : (∫ t : ℝ, G I t) = a I.val * ∫ t : ℝ,
        (((Ideal.absNorm I.val : ℝ) / X : ℝ) : ℂ) ^ (-(σ + t * Complex.I)) *
          mellin h (σ + t * Complex.I) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      change mellin h (σ + t * Complex.I) * (X : ℂ) ^ (σ + t * Complex.I) *
        (a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(σ + t * Complex.I))) =
        a I.val * ((((Ideal.absNorm I.val : ℝ) / X : ℝ) : ℂ) ^ (-(σ + t * Complex.I)) *
          mellin h (σ + t * Complex.I))
      rw [← cpow_absNorm_div I.property hX (σ + t * Complex.I)]
      ring
    rw [← (Vendor.mellin_inversion_positive_line h hh hcompact σ hσ0).2
        ((Ideal.absNorm I.val : ℝ) / X) hxpos,
      Vendor.mellinInv_eq_verticalIntegral σ (mellin h) hxpos, Vendor.verticalIntegral,
      hcongr]
    ring
  have hRHS : Vendor.verticalIntegral σ
      (fun s => mellin h s * (X : ℂ) ^ s * idealCoefficientLSeries a s) =
      ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
        a I.val * h ((Ideal.absNorm I.val : ℝ) / X) := by
    rw [Vendor.verticalIntegral]
    have h1 : (∫ t : ℝ, (fun s => mellin h s * (X : ℂ) ^ s * idealCoefficientLSeries a s)
          (σ + t * Complex.I)) =
        ∫ t : ℝ, ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, G I t :=
      integral_congr_ae (ae_of_all _ fun t => (hpoint t).symm)
    rw [h1, ← hswap, ← tsum_mul_left]
    exact tsum_congr fun I => hper I
  have hLHS : (∑ᶠ I : Ideal (𝓞 F), idealMellinWeight a h X I) =
      ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
        a I.val * h ((Ideal.absNorm I.val : ℝ) / X) := by
    have hfs := idealMellinWeight_hasFiniteSupport a hcompact hX
    have htsum : (∑' I : Ideal (𝓞 F), idealMellinWeight a h X I) =
        ∑ I ∈ hfs.toFinset, idealMellinWeight a h X I :=
      tsum_eq_sum fun b hb => by
        by_contra hne
        exact hb ((hfs.mem_toFinset).2 (by simpa [Function.mem_support] using hne))
    have hsub : (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
          a I.val * h ((Ideal.absNorm I.val : ℝ) / X)) =
        ∑' I : Ideal (𝓞 F), idealMellinWeight a h X I := by
      refine (tsum_subtype {I : Ideal (𝓞 F) | I ≠ ⊥}
        (fun I => a I * h ((Ideal.absNorm I : ℝ) / X))).trans ?_
      refine tsum_congr fun I => ?_
      by_cases hI : I = ⊥
      · simp [Set.indicator_of_notMem, hI, idealMellinWeight]
      · rw [Set.indicator_of_mem (by simpa using hI), idealMellinWeight]
        simp [hI]
    rw [finsum_eq_finsetSum_of_support_subset _
      (by rw [hfs.coe_toFinset]), hsub, htsum]
  exact hLHS.trans hRHS.symm

theorem idealMellin_dual_interchange (a : Ideal (𝓞 F) → ℂ)
    (ha0 : a ⊥ = 0) (ha : ∀ I, ‖a I‖ ≤ 1)
    (B : ℂ → ℂ) (T : ℝ → ℂ) {c X q : ℝ}
    (hc : 1 < c) (hX : 0 < X) (hq : 0 < q)
    (hB : Complex.VerticalIntegrable B c)
    (hT : ∀ x : ℝ, 0 < x → T x = mellinInv c B x) :
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖a I.val * T (X * (Ideal.absNorm I.val : ℝ) / q)‖) ∧
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      a I.val * T (X * (Ideal.absNorm I.val : ℝ) / q)) ∧
    Complex.VerticalIntegrable
      (fun s => B s * ((X / q : ℝ) : ℂ) ^ (-s) * idealCoefficientLSeries a s) c ∧
    Vendor.verticalIntegral c
      (fun s => B s * ((X / q : ℝ) : ℂ) ^ (-s) * idealCoefficientLSeries a s) =
      ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
        a I.val * T (X * (Ideal.absNorm I.val : ℝ) / q) := by
  haveI : Countable (Ideal (𝓞 F)) := countable_ideal F
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hq0 : 0 < X / q := div_pos hX hq
  have hposI : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥}, 0 < (Ideal.absNorm I.val : ℝ) := by
    intro I
    have hne : Ideal.absNorm I.val ≠ 0 := by
      simpa [Ideal.absNorm_eq_zero_iff] using I.property
    exact_mod_cast Nat.pos_of_ne_zero hne
  have hxI : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥}, 0 < X * (Ideal.absNorm I.val : ℝ) / q :=
    fun I => div_pos (mul_pos hX (hposI I)) hq
  have hrpow : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      (X * (Ideal.absNorm I.val : ℝ) / q) ^ (-c) =
        (X / q) ^ (-c) * (Ideal.absNorm I.val : ℝ) ^ (-c) := by
    intro I
    rw [show X * (Ideal.absNorm I.val : ℝ) / q =
        (X / q) * (Ideal.absNorm I.val : ℝ) by ring]
    rw [Real.mul_rpow (div_nonneg hX.le hq.le) (hposI I).le]

  have hLsum : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(c : ℂ))‖) :=
    (idealCoefficientLSeries_summable a ha0 ha hc).1
  have hLsumN : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      (Ideal.absNorm I.val : ℝ) ^ (-c)) :=
    ((summable_ideal_inverse_power F c hc).subtype (fun I : Ideal (𝓞 F) => I ≠ ⊥)).congr
      fun I => by simp [I.property]
  have hLsumA : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-c)) :=
    hLsum.congr fun I => by rw [norm_mul, norm_absNorm_cpow I.property]; simp
  set CL : ℝ := (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
    ‖a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(c : ℂ))‖) with hCL
  have hBint : Integrable (fun t : ℝ => B (c + t * Complex.I)) := hB
  set K : ℝ := ‖(1 / (2 * Real.pi) : ℂ)‖ * ∫ t : ℝ, ‖B (c + t * Complex.I)‖ with hK

  have hTbound : ∀ x : ℝ, 0 < x → ‖T x‖ ≤ K * x ^ (-c) := by
    intro x hx
    have hxpow : ∀ t : ℝ, ‖(x : ℂ) ^ (-(c + t * Complex.I))‖ = x ^ (-c) := by
      intro t
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp
    calc ‖T x‖ = ‖(1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
          (x : ℂ) ^ (-(c + t * Complex.I)) * B (c + t * Complex.I)‖ := by
          rw [hT x hx, Vendor.mellinInv_eq_verticalIntegral c B hx, Vendor.verticalIntegral]
      _ = ‖(1 / (2 * Real.pi) : ℂ)‖ * ‖∫ t : ℝ,
          (x : ℂ) ^ (-(c + t * Complex.I)) * B (c + t * Complex.I)‖ := by rw [norm_mul]
      _ ≤ ‖(1 / (2 * Real.pi) : ℂ)‖ * ∫ t : ℝ,
          ‖(x : ℂ) ^ (-(c + t * Complex.I)) * B (c + t * Complex.I)‖ :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
      _ = ‖(1 / (2 * Real.pi) : ℂ)‖ * (x ^ (-c) * ∫ t : ℝ, ‖B (c + t * Complex.I)‖) := by
          congr 1
          rw [← integral_const_mul]
          exact integral_congr_ae (ae_of_all _ fun t => by
            dsimp only
            rw [norm_mul, hxpow t])
      _ = K * x ^ (-c) := by rw [hK]; ring
  have hsumTnorm : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖a I.val * T (X * (Ideal.absNorm I.val : ℝ) / q)‖) := by
    refine Summable.of_nonneg_of_le (fun I => norm_nonneg _) ?_
      (hLsumN.mul_left (K * (X / q) ^ (-c)))
    intro I
    rw [norm_mul]
    calc ‖a I.val‖ * ‖T (X * (Ideal.absNorm I.val : ℝ) / q)‖
        ≤ 1 * (K * (X * (Ideal.absNorm I.val : ℝ) / q) ^ (-c)) :=
          mul_le_mul (ha I.val) (hTbound _ (hxI I)) (norm_nonneg _) zero_le_one
      _ = (K * (X / q) ^ (-c)) * (Ideal.absNorm I.val : ℝ) ^ (-c) := by
          rw [hrpow I]; ring

  have hcoef_cont : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      Continuous (fun t : ℝ =>
        a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(c + t * Complex.I))) := by
    intro I
    have hne : (Ideal.absNorm I.val : ℂ) ≠ 0 := by
      have : Ideal.absNorm I.val ≠ 0 := by
        simpa [Ideal.absNorm_eq_zero_iff] using I.property
      exact_mod_cast this
    have harg : Continuous fun t : ℝ => -(c + t * Complex.I) := by fun_prop
    exact (harg.const_cpow (Or.inl hne)).const_mul (a I.val)
  have hLcont : Continuous (fun t : ℝ => idealCoefficientLSeries a (c + t * Complex.I)) := by
    refine continuous_tsum (f := fun (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) (t : ℝ) =>
        a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(c + t * Complex.I))) ?_ hLsum ?_
    · exact hcoef_cont
    · intro I t
      have h1 : ‖(Ideal.absNorm I.val : ℂ) ^ (-(c + t * Complex.I))‖ =
          (Ideal.absNorm I.val : ℝ) ^ (-c) := by
        rw [norm_absNorm_cpow I.property]; simp
      have h2 : ‖(Ideal.absNorm I.val : ℂ) ^ (-(c : ℂ))‖ =
          (Ideal.absNorm I.val : ℝ) ^ (-c) := by
        rw [norm_absNorm_cpow I.property]; simp
      rw [norm_mul, h1]
      rw [norm_mul, h2]
  have hLbound : ∀ t : ℝ, ‖idealCoefficientLSeries a (c + t * Complex.I)‖ ≤ CL := by
    intro t
    have hsum_t : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
        a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(c + t * Complex.I))) :=
      (idealCoefficientLSeries_summable a ha0 ha (s := (c : ℂ) + t * Complex.I)
        (by simpa using hc)).2
    rw [hCL, idealCoefficientLSeries]
    refine (norm_tsum_le_tsum_norm hsum_t.norm).trans (le_of_eq (tsum_congr fun I => ?_))
    have h1 : ‖(Ideal.absNorm I.val : ℂ) ^ (-(c + t * Complex.I))‖ =
        (Ideal.absNorm I.val : ℝ) ^ (-c) := by
      rw [norm_absNorm_cpow I.property]; simp
    have h2 : ‖(Ideal.absNorm I.val : ℂ) ^ (-(c : ℂ))‖ =
        (Ideal.absNorm I.val : ℝ) ^ (-c) := by
      rw [norm_absNorm_cpow I.property]; simp
    rw [norm_mul, norm_mul, h1, h2]
  have hcontY : Continuous (fun t : ℝ => ((X / q : ℝ) : ℂ) ^ (-(c + t * Complex.I))) := by
    have hne : ((X / q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq0
    have harg : Continuous fun t : ℝ => -(c + t * Complex.I) := by fun_prop
    exact harg.const_cpow (Or.inl hne)
  have hYnorm : ∀ t : ℝ, ‖((X / q : ℝ) : ℂ) ^ (-(c + t * Complex.I))‖ = (X / q) ^ (-c) := by
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq0]; simp

  have hVert : Complex.VerticalIntegrable
      (fun s => B s * ((X / q : ℝ) : ℂ) ^ (-s) * idealCoefficientLSeries a s) c := by
    refine Integrable.mono'
      (g := fun t : ℝ => CL * (X / q) ^ (-c) * ‖B (c + t * Complex.I)‖)
      ((hBint.norm).const_mul (CL * (X / q) ^ (-c))) ?_ (ae_of_all _ fun t => ?_)
    · change AEStronglyMeasurable (fun t : ℝ => B (c + t * Complex.I) *
        ((X / q : ℝ) : ℂ) ^ (-(c + t * Complex.I)) *
          idealCoefficientLSeries a (c + t * Complex.I))
      exact (hB.aestronglyMeasurable.mul hcontY.aestronglyMeasurable).mul
        hLcont.aestronglyMeasurable
    · change ‖B (c + t * Complex.I) * ((X / q : ℝ) : ℂ) ^ (-(c + t * Complex.I)) *
        idealCoefficientLSeries a (c + t * Complex.I)‖ ≤ _
      rw [norm_mul, norm_mul, hYnorm t]
      have hnn : 0 ≤ ‖B (c + t * Complex.I)‖ * (X / q) ^ (-c) :=
        mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hq0.le _)
      calc ‖B (c + t * Complex.I)‖ * (X / q) ^ (-c) *
            ‖idealCoefficientLSeries a (c + t * Complex.I)‖
          ≤ ‖B (c + t * Complex.I)‖ * (X / q) ^ (-c) * CL :=
            mul_le_mul_of_nonneg_left (hLbound t) hnn
        _ = CL * (X / q) ^ (-c) * ‖B (c + t * Complex.I)‖ := by ring

  set H : {I : Ideal (𝓞 F) // I ≠ ⊥} → ℝ → ℂ := fun I t =>
    B (c + t * Complex.I) * ((X / q : ℝ) : ℂ) ^ (-(c + t * Complex.I)) *
      (a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(c + t * Complex.I))) with hHdef
  have hH_le : ∀ (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) (t : ℝ),
      ‖H I t‖ ≤ ((X / q) ^ (-c) * (‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-c))) *
        ‖B (c + t * Complex.I)‖ := by
    intro I t
    have hnormN : ‖(Ideal.absNorm I.val : ℂ) ^ (-(c + t * Complex.I))‖ =
        (Ideal.absNorm I.val : ℝ) ^ (-c) := by
      rw [norm_absNorm_cpow I.property]; simp
    change ‖B (c + t * Complex.I) * ((X / q : ℝ) : ℂ) ^ (-(c + t * Complex.I)) *
      (a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(c + t * Complex.I)))‖ ≤ _
    rw [norm_mul, norm_mul, norm_mul, hYnorm t, hnormN]
    exact le_of_eq (by ring)
  have hH_int : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥}, Integrable (H I) := by
    intro I
    have hmeas : AEStronglyMeasurable (H I) := by
      change AEStronglyMeasurable (fun t : ℝ =>
        B (c + t * Complex.I) * ((X / q : ℝ) : ℂ) ^ (-(c + t * Complex.I)) *
          (a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(c + t * Complex.I))))
      exact (hB.aestronglyMeasurable.mul hcontY.aestronglyMeasurable).mul
        (hcoef_cont I).aestronglyMeasurable
    refine Integrable.mono' (g := fun t : ℝ =>
      ((X / q) ^ (-c) * (‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-c))) *
        ‖B (c + t * Complex.I)‖) ((hBint.norm).const_mul _) hmeas
      (ae_of_all _ fun t => hH_le I t)
  set A : ℝ := ∫ t : ℝ, ‖B (c + t * Complex.I)‖ with hA
  have hH_sum : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => ∫ t : ℝ, ‖H I t‖) := by
    refine Summable.of_nonneg_of_le (fun I => integral_nonneg fun t => norm_nonneg _) ?_
      (hLsumA.mul_left ((X / q) ^ (-c) * A))
    intro I
    have hmaj : Integrable (fun t : ℝ =>
        ((X / q) ^ (-c) * (‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-c))) *
          ‖B (c + t * Complex.I)‖) := (hBint.norm).const_mul _
    calc ∫ t : ℝ, ‖H I t‖
        ≤ ∫ t : ℝ, ((X / q) ^ (-c) *
            (‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-c))) *
              ‖B (c + t * Complex.I)‖ :=
          integral_mono (hH_int I).norm hmaj (fun t => hH_le I t)
      _ = ((X / q) ^ (-c) * (‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-c))) * A := by
          rw [integral_const_mul, hA]
      _ = ((X / q) ^ (-c) * A) * (‖a I.val‖ * (Ideal.absNorm I.val : ℝ) ^ (-c)) := by ring
  have hswap : (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, ∫ t : ℝ, H I t) =
      ∫ t : ℝ, ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, H I t :=
    integral_tsum_of_summable_integral_norm hH_int hH_sum
  have hpoint : ∀ t : ℝ, (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, H I t) =
      B (c + t * Complex.I) * ((X / q : ℝ) : ℂ) ^ (-(c + t * Complex.I)) *
        idealCoefficientLSeries a (c + t * Complex.I) := by
    intro t
    rw [idealCoefficientLSeries, ← tsum_mul_left]
  have hper : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, H I t =
        a I.val * T (X * (Ideal.absNorm I.val : ℝ) / q) := by
    intro I
    have hxq : 0 < X * (Ideal.absNorm I.val : ℝ) / q := hxI I
    have hcongr : (∫ t : ℝ, H I t) = a I.val * ∫ t : ℝ,
        (((X * (Ideal.absNorm I.val : ℝ) / q : ℝ)) : ℂ) ^ (-(c + t * Complex.I)) *
          B (c + t * Complex.I) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      change B (c + t * Complex.I) * ((X / q : ℝ) : ℂ) ^ (-(c + t * Complex.I)) *
        (a I.val * (Ideal.absNorm I.val : ℂ) ^ (-(c + t * Complex.I))) =
        a I.val * ((((X * (Ideal.absNorm I.val : ℝ) / q : ℝ)) : ℂ) ^
          (-(c + t * Complex.I)) * B (c + t * Complex.I))
      rw [show (((X * (Ideal.absNorm I.val : ℝ) / q : ℝ)) : ℂ) ^ (-(c + t * Complex.I)) =
          ((X / q : ℝ) : ℂ) ^ (-(c + t * Complex.I)) *
            ((Ideal.absNorm I.val : ℝ) : ℂ) ^ (-(c + t * Complex.I)) from by
        rw [← Complex.mul_cpow_ofReal_nonneg (div_nonneg hX.le hq.le) (hposI I).le
          (-(c + t * Complex.I))]
        congr 1
        push_cast
        ring]
      rw [show (Ideal.absNorm I.val : ℂ) = ((Ideal.absNorm I.val : ℝ) : ℂ) from
        (Complex.ofReal_natCast (Ideal.absNorm I.val)).symm]
      ring
    rw [hcongr]
    have hstep : (1 / (2 * Real.pi) : ℂ) * (a I.val * ∫ t : ℝ,
        (((X * (Ideal.absNorm I.val : ℝ) / q : ℝ)) : ℂ) ^ (-(c + t * Complex.I)) *
          B (c + t * Complex.I)) = a I.val * ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        (((X * (Ideal.absNorm I.val : ℝ) / q : ℝ)) : ℂ) ^ (-(c + t * Complex.I)) *
          B (c + t * Complex.I)) := by ring
    have hfold : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        (((X * (Ideal.absNorm I.val : ℝ) / q : ℝ)) : ℂ) ^ (-(c + t * Complex.I)) *
          B (c + t * Complex.I) =
        Vendor.verticalIntegral c (fun s =>
          (((X * (Ideal.absNorm I.val : ℝ) / q : ℝ)) : ℂ) ^ (-s) * B s) := by
      rw [Vendor.verticalIntegral]
    rw [hstep, hfold, ← Vendor.mellinInv_eq_verticalIntegral c B hxq, ← hT _ hxq]
  have hEq : Vendor.verticalIntegral c
      (fun s => B s * ((X / q : ℝ) : ℂ) ^ (-s) * idealCoefficientLSeries a s) =
      ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
        a I.val * T (X * (Ideal.absNorm I.val : ℝ) / q) := by
    rw [Vendor.verticalIntegral]
    have h1 : (∫ t : ℝ,
          (fun s => B s * ((X / q : ℝ) : ℂ) ^ (-s) * idealCoefficientLSeries a s)
            (c + t * Complex.I)) =
        ∫ t : ℝ, ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, H I t :=
      integral_congr_ae (ae_of_all _ fun t => (hpoint t).symm)
    rw [h1, ← hswap, ← tsum_mul_left]
    exact tsum_congr fun I => hper I
  exact ⟨hsumTnorm, hsumTnorm.of_norm, hVert, hEq⟩

end DedekindZetaZeroFree.LargeSieve

end
