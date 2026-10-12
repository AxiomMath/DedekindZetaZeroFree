module

public import DedekindZetaZeroFree.Theta.Unfolding.MixedRadialJacobian
public import DedekindZetaZeroFree.Nonvanishing.Mellin.ArchimedeanGaussianFactors

@[expose] public section

noncomputable section

open Classical NumberField NumberField.InfinitePlace MeasureTheory

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

private theorem positive_prod_cpow {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ t, 0 ≤ a i) (s : ℂ) :
    (∏ i ∈ t, (a i : ℂ) ^ s) = ((∏ i ∈ t, a i : ℝ) : ℂ) ^ s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (ha i (Finset.mem_insert_self _ _))
        (Finset.prod_nonneg (fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))]

private theorem place_integral (x : K) (hx : x ≠ 0) (s : ℂ) (hs : 0 < s.re)
    (v : InfinitePlace K) :
    (∫ q : ℝ in Set.Ioi 0,
      (q : ℂ) ^ ((v.mult : ℂ) * s - 1) *
        Complex.exp (-(Real.pi : ℂ) * (v.mult : ℂ) * (q : ℂ) ^ 2 * (v x : ℂ) ^ 2)) =
      (if IsReal v then (1 / 2 : ℂ) * Complex.Gammaℝ s
        else (1 / 4 : ℂ) * Complex.Gammaℂ s) *
      ((v x ^ v.mult : ℝ) : ℂ) ^ (-s) := by
  classical
  have ha : 0 < v x := pos_iff.mpr hx
  have hp : ((v x ^ v.mult : ℝ) : ℂ) ^ (-s) =
      (v x : ℂ) ^ ((v.mult : ℂ) * (-s)) := by
    rw [← Real.rpow_natCast, ← Complex.cpow_mul_ofReal_nonneg ha.le]
    simp
  rw [hp]
  rcases isReal_or_isComplex v with hv | hv
  · rw [if_pos hv, hv.mult_eq_one]
    simp only [Nat.cast_one, one_mul]
    convert gaussian_real_place_mellin s (v x) hs ha using 1
    · push_cast
      congr! 2
      ring_nf
    · ring
  · rw [if_neg (not_isReal_iff_isComplex.mpr hv), hv.mult_eq_two]
    simp only [Nat.cast_ofNat]
    convert gaussian_complex_place_mellin s (v x) hs ha using 1
    · push_cast
      congr! 2
      ring_nf
    · ring

theorem integrable_mixedMellinGaussian (x : K) (hx : x ≠ 0)
    (s : ℂ) (hs : 0 < s.re) :
    Integrable (mixedMellinGaussian K x s)
      (Measure.pi (fun _v : InfinitePlace K ↦
        (volume : Measure ℝ).restrict (Set.Ioi 0))) := by
  classical
  unfold mixedMellinGaussian
  apply Integrable.fintype_prod (f := fun (v : InfinitePlace K) (q : ℝ) ↦
    (q : ℂ) ^ ((v.mult : ℂ) * s - 1) *
      Complex.exp (-(Real.pi : ℂ) * (v.mult : ℂ) * (q : ℂ) ^ 2 * (v x : ℂ) ^ 2))
  intro v
  have ha : 0 < v x := pos_iff.mpr hx
  rcases isReal_or_isComplex v with hv | hv
  · convert integrableOn_gaussian_real_place_mellin s (v x) hs ha using 1
    simp only [hv.mult_eq_one, Nat.cast_one, one_mul, Complex.ofReal_mul,
      Complex.ofReal_pow, IntegrableOn]
    congr! 2
    push_cast
    ring_nf
  · convert integrableOn_gaussian_complex_place_mellin s (v x) hs ha using 1
    simp only [hv.mult_eq_two, Nat.cast_ofNat, Complex.ofReal_mul,
      Complex.ofReal_pow, IntegrableOn]
    congr! 2
    push_cast
    ring_nf

theorem integral_mixedMellinGaussian (x : K) (hx : x ≠ 0)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ q : InfinitePlace K → ℝ, mixedMellinGaussian K x s q
      ∂Measure.pi (fun _v : InfinitePlace K ↦
        (volume : Measure ℝ).restrict (Set.Ioi 0))) =
      (1 / 2 : ℂ) ^ nrRealPlaces K *
        (1 / 4 : ℂ) ^ nrComplexPlaces K *
        Complex.Gammaℝ s ^ nrRealPlaces K *
        Complex.Gammaℂ s ^ nrComplexPlaces K *
        ((|Algebra.norm ℚ x| : ℚ) : ℂ) ^ (-s) := by
  classical
  unfold mixedMellinGaussian
  rw [integral_fintype_prod_eq_prod (fun (v : InfinitePlace K) (q : ℝ) ↦
    (q : ℂ) ^ ((v.mult : ℂ) * s - 1) *
      Complex.exp (-(Real.pi : ℂ) * (v.mult : ℂ) * (q : ℂ) ^ 2 * (v x : ℂ) ^ 2))]
  simp_rw [place_integral K x hx s hs]
  rw [Finset.prod_mul_distrib, positive_prod_cpow]
  · rw [prod_eq_abs_norm]
    have hc : (∏ v : InfinitePlace K,
        if IsReal v then (1 / 2 : ℂ) * Complex.Gammaℝ s
          else (1 / 4 : ℂ) * Complex.Gammaℂ s) =
        ((1 / 2 : ℂ) * Complex.Gammaℝ s) ^ nrRealPlaces K *
          ((1 / 4 : ℂ) * Complex.Gammaℂ s) ^ nrComplexPlaces K := by
      rw [prod_eq_prod_mul_prod]
      have hr (v : {v : InfinitePlace K // IsReal v}) : IsReal v.val := v.property
      have hi (v : {v : InfinitePlace K // IsComplex v}) : ¬IsReal v.val :=
        not_isReal_iff_isComplex.mpr v.property
      simp only [hr, hi, if_true, if_false, Finset.prod_const, Finset.card_univ,
        nrRealPlaces, nrComplexPlaces]
    rw [hc, Rat.cast_abs]
    norm_cast
    ring
  · intro v hv
    exact pow_nonneg (AbsoluteValue.nonneg _ _) _

theorem norm_mixedMellinGaussian_eq_realPart (x : K) (s : ℂ)
    (q : InfinitePlace K → ℝ) (hq : ∀ v, 0 < q v) :
    ‖mixedMellinGaussian K x s q‖ =
      ‖mixedMellinGaussian K x (s.re : ℂ) q‖ := by
  rw [norm_mixedMellinGaussian K x s q hq,
    norm_mixedMellinGaussian K x (s.re : ℂ) q hq]
  simp

private theorem kernel_real_norm (x : K) (σ : ℝ) (q : InfinitePlace K → ℝ)
    (hq : ∀ v, 0 < q v) :
    mixedMellinGaussian K x (σ : ℂ) q =
      (‖mixedMellinGaussian K x (σ : ℂ) q‖ : ℂ) := by
  rw [norm_mixedMellinGaussian K x (σ : ℂ) q hq]
  unfold mixedMellinGaussian
  simp only [Complex.ofReal_re, Complex.ofReal_prod, Complex.ofReal_mul,
    Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow,
    Complex.ofReal_natCast, Complex.ofReal_sub, Complex.ofReal_one]
  apply Finset.prod_congr rfl
  intro v hv
  rw [Complex.ofReal_cpow (hq v).le]
  push_cast
  ring_nf

private theorem positive_coordinates_ae :
    ∀ᵐ q : InfinitePlace K → ℝ ∂Measure.pi (fun _v : InfinitePlace K ↦
      (volume : Measure ℝ).restrict (Set.Ioi 0)), ∀ v, 0 < q v := by
  apply Filter.eventually_all.mpr
  intro v
  exact (MeasureTheory.Measure.tendsto_eval_ae_ae (i := v)).eventually
    (ae_restrict_mem measurableSet_Ioi)

theorem integral_norm_mixedMellinGaussian (x : K) (hx : x ≠ 0)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ q : InfinitePlace K → ℝ, ‖mixedMellinGaussian K x s q‖
      ∂Measure.pi (fun _v : InfinitePlace K ↦
        (volume : Measure ℝ).restrict (Set.Ioi 0))) =
      (1 / 2 : ℝ) ^ nrRealPlaces K *
        (1 / 4 : ℝ) ^ nrComplexPlaces K *
        ‖Complex.Gammaℝ (s.re : ℂ)‖ ^ nrRealPlaces K *
        ‖Complex.Gammaℂ (s.re : ℂ)‖ ^ nrComplexPlaces K *
        ((|Algebra.norm ℚ x| : ℚ) : ℝ) ^ (-s.re) := by
  let μ := Measure.pi (fun _v : InfinitePlace K ↦
    (volume : Measure ℝ).restrict (Set.Ioi 0))
  have heq : (∫ q, ‖mixedMellinGaussian K x s q‖ ∂μ) =
      ∫ q, ‖mixedMellinGaussian K x (s.re : ℂ) q‖ ∂μ := by
    apply integral_congr_ae
    exact (positive_coordinates_ae K).mono fun q hq ↦
      norm_mixedMellinGaussian_eq_realPart K x s q hq
  have hi : (∫ q, mixedMellinGaussian K x (s.re : ℂ) q ∂μ) =
      (((∫ q, ‖mixedMellinGaussian K x (s.re : ℂ) q‖ ∂μ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact (positive_coordinates_ae K).mono fun q hq ↦ kernel_real_norm K x s.re q hq
  have hn : ‖∫ q, mixedMellinGaussian K x (s.re : ℂ) q ∂μ‖ =
      ∫ q, ‖mixedMellinGaussian K x (s.re : ℂ) q‖ ∂μ := by
    rw [hi, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun q ↦ norm_nonneg _)]
  change (∫ q, ‖mixedMellinGaussian K x s q‖ ∂μ) = _
  rw [heq, ← hn]
  change ‖∫ q, mixedMellinGaussian K x (s.re : ℂ) q
    ∂Measure.pi (fun _v : InfinitePlace K ↦
      (volume : Measure ℝ).restrict (Set.Ioi 0))‖ = _
  rw [integral_mixedMellinGaussian K x hx (s.re : ℂ) (by simpa using hs)]
  simp only [norm_mul, norm_pow]
  have hnorm : 0 < ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
    have hprod : 0 < ∏ v : InfinitePlace K, v x ^ v.mult :=
      Finset.prod_pos fun v hv ↦ pow_pos (pos_iff.mpr hx) _
    rwa [prod_eq_abs_norm] at hprod
  rw [show (-(s.re : ℂ)) = ((-s.re : ℝ) : ℂ) by simp,
    ← Complex.ofReal_ratCast, Complex.norm_cpow_eq_rpow_re_of_pos hnorm]
  norm_num

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
