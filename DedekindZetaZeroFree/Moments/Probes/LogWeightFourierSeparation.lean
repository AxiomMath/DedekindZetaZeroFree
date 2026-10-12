module

public import DedekindZetaZeroFree.Moments.Probes.UniformLogarithmicDerivatives

@[expose] public section

section

namespace DedekindZetaZeroFree.ProbeLogarithmicRowCoefficients
noncomputable section
open MeasureTheory

def normalizedCoefficient (f : ℝ → ℂ) (a L : ℝ) (j : ℤ) : ℂ :=
  (L : ℂ)⁻¹ * ∫ u in Set.Icc a (a + L),
    f u * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
      (u : ℂ) / (L : ℂ))

private theorem local_norm_fourierCoeffOn_le {a b M : ℝ} (hab : a < b) (f : ℝ → ℂ)
    (hbound : ∀ u ∈ Set.Icc a b, ‖f u‖ ≤ M) :
    ∀ j : ℤ, ‖fourierCoeffOn hab f j‖ ≤ M := by
  intro j
  letI : Fact (0 < b - a) := ⟨sub_pos.mpr hab⟩
  rw [fourierCoeffOn_eq_integral, norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr (sub_pos.mpr hab))]
  have hh : ‖∫ u in a..b, fourier (-j) (u : AddCircle (b - a)) • f u‖ ≤ M * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    exact hbound u (Set.Ioc_subset_Icc_self (by simpa only [Set.uIoc_of_le hab.le] using hu))
  calc
    (1 / (b - a)) * ‖∫ u in a..b, fourier (-j) (u : AddCircle (b - a)) • f u‖
      ≤ (1 / (b - a)) * (M * |b - a|) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = M := by rw [abs_of_pos (sub_pos.mpr hab)]; field_simp [sub_pos.mpr hab |>.ne']

private theorem local_twice_integration_by_parts {a b : ℝ} (hab : a < b)
    (f f₁ f₂ : ℝ → ℂ)
    (h₁ : ∀ u ∈ Set.Icc a b, HasDerivAt f (f₁ u) u)
    (h₂ : ∀ u ∈ Set.Icc a b, HasDerivAt f₁ (f₂ u) u)
    (hi₁ : IntervalIntegrable f₁ volume a b)
    (hi₂ : IntervalIntegrable f₂ volume a b)
    (hz : f a = f b) (hz₁ : f₁ a = f₁ b)
    (j : ℤ) (hj : j ≠ 0) :
    fourierCoeffOn hab f j =
      (((b - a : ℝ) : ℂ) / (2 * Real.pi * Complex.I * (j : ℂ))) ^ 2 *
        fourierCoeffOn hab f₂ j := by
  have he := fourierCoeffOn_of_hasDerivAt hab hj (by simpa only [Set.uIcc_of_le hab.le] using h₁) hi₁
  have he₁ := fourierCoeffOn_of_hasDerivAt hab hj (by simpa only [Set.uIcc_of_le hab.le] using h₂) hi₂
  rw [← hz, sub_self, mul_zero, zero_sub] at he
  rw [← hz₁, sub_self, mul_zero, zero_sub] at he₁
  rw [he, he₁, Complex.ofReal_sub]
  ring

theorem quadratic_coefficient_bound {Y : Type*} (f : Y → ℝ → ℂ)
    (a L b0 b1 : ℝ) (hL : 0 < L) (ha : a < b0) (hb : b1 < a + L)
    (hsupport : ∀ y, tsupport (f y) ⊆ Set.Icc b0 b1)
    (hsmooth : ∀ y, ContDiff ℝ (2 : ℕ∞) (f y))
    (hbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ u y,
      ‖f y u‖ + ‖iteratedDeriv 2 (f y) u‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℤ) (y : Y),
      ‖normalizedCoefficient (f y) a L j‖ ≤ C / (1 + (j : ℝ) ^ 2) := by
  obtain ⟨B, hB, hbound⟩ := hbound
  have hab : a < a + L := lt_add_of_pos_right a hL
  have heq (g : ℝ → ℂ) (j : ℤ) :
      normalizedCoefficient g a L j = fourierCoeffOn hab g j := by
    letI : Fact (0 < L) := ⟨hL⟩
    rw [fourierCoeffOn_eq_integral]
    simp only [add_sub_cancel_left]
    rw [intervalIntegral.integral_of_le hab.le]
    rw [normalizedCoefficient, ← integral_Icc_eq_integral_Ioc]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, one_div,
      Complex.ofReal_inv]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp only
    rw [fourier_coe_apply, smul_eq_mul]
    simp only [Int.cast_neg, mul_neg, neg_mul, mul_comm, add_sub_cancel_left]
  let D : ℝ := ‖(L : ℂ) / (2 * Real.pi * Complex.I)‖ ^ 2 * B
  refine ⟨B + 2 * D, by dsimp [D]; positivity, ?_⟩
  intro j y
  rw [heq]
  have hf₀ (u : ℝ) : ‖f y u‖ ≤ B := (le_add_of_nonneg_right (norm_nonneg _)).trans (hbound u y)
  have hf₂ (u : ℝ) : ‖iteratedDeriv 2 (f y) u‖ ≤ B :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans (hbound u y)
  by_cases hj : j = 0
  · subst j
    simpa using (local_norm_fourierCoeffOn_le hab (f y) (fun u _ => hf₀ u) 0).trans
      (show B ≤ B + 2 * D from le_add_of_nonneg_right (by dsimp [D]; positivity))
  · have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj
    have hs : 1 ≤ (j : ℝ)^2 := by
      have h : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast (Int.one_le_abs hj)
      nlinarith [sq_nonneg (|(j : ℝ)| - 1), sq_abs (j : ℝ)]
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hd : Differentiable ℝ (f y) := (hsmooth y).differentiable (by norm_num)
    have hd₁ : Differentiable ℝ (deriv (f y)) := by
      simpa using (contDiff_nat_iff_iteratedDeriv.mp (show ContDiff ℝ (2 : ℕ) (f y) from hsmooth y)).2 1 (by norm_num)
    have h₁ (u : ℝ) (_ : u ∈ Set.Icc a (a + L)) :
        HasDerivAt (f y) (deriv (f y) u) u := (hd u).hasDerivAt
    have h₂ (u : ℝ) (_ : u ∈ Set.Icc a (a + L)) :
        HasDerivAt (deriv (f y)) (iteratedDeriv 2 (f y) u) u := by
      simpa [iteratedDeriv_succ] using (hd₁ u).hasDerivAt
    have hc₁ : Continuous (deriv (f y)) := by
      simpa using (hsmooth y).continuous_iteratedDeriv 1 (by norm_num)
    have hi₁ : IntervalIntegrable (deriv (f y)) volume a (a + L) :=
      hc₁.intervalIntegrable _ _
    have hi₂ : IntervalIntegrable (iteratedDeriv 2 (f y)) volume a (a + L) :=
      ((hsmooth y).continuous_iteratedDeriv 2 (by norm_num)).intervalIntegrable _ _
    have hza : a ∉ tsupport (f y) := fun h => (not_le.mpr ha) ((hsupport y h).1)
    have hzb : a + L ∉ tsupport (f y) := fun h => (not_le.mpr hb) ((hsupport y h).2)
    have hz : f y a = f y (a + L) := by
      rw [image_eq_zero_of_notMem_tsupport hza, image_eq_zero_of_notMem_tsupport hzb]
    have hz₁ : deriv (f y) a = deriv (f y) (a + L) := by
      rw [deriv_of_notMem_tsupport hza, deriv_of_notMem_tsupport hzb]
    have hcoef : ‖fourierCoeffOn hab (f y) j‖ ≤ D / (j : ℝ)^2 := by
      rw [local_twice_integration_by_parts hab (f y) (deriv (f y))
        (iteratedDeriv 2 (f y)) h₁ h₂ hi₁ hi₂ hz hz₁ j hj]
      simp only [add_sub_cancel_left]
      rw [show ((L : ℂ) / (2 * Real.pi * Complex.I * (j : ℂ))) =
        ((L : ℂ) / (2 * Real.pi * Complex.I)) / (j : ℂ) by ring]
      rw [norm_mul, norm_pow, norm_div, Complex.norm_intCast, div_pow, sq_abs]
      exact mul_le_mul_of_nonneg_left
        (local_norm_fourierCoeffOn_le hab (iteratedDeriv 2 (f y)) (fun u _ => hf₂ u) j)
        (by positivity) |>.trans_eq (by dsimp [D]; ring)
    apply hcoef.trans
    apply (div_le_div_iff₀ (sq_pos_of_ne_zero hjR) (by positivity : 0 < 1 + (j : ℝ)^2)).mpr
    nlinarith [mul_nonneg hB (sq_nonneg (j : ℝ)), mul_nonneg hD (sub_nonneg.mpr hs)]

end
end DedekindZetaZeroFree.ProbeLogarithmicRowCoefficients

end

section

namespace DedekindZetaZeroFree.ProbeLogarithmicRowCoefficients
noncomputable section
open MeasureTheory

theorem hasSum_normalized_coefficients (f : ℝ → ℂ) (a L b0 b1 : ℝ)
    (hL : 0 < L) (ha : a < b0) (hb : b1 < a + L)
    (hf : Continuous f) (hsupport : tsupport f ⊆ Set.Icc b0 b1)
    (hsummable : Summable (fun j : ℤ => normalizedCoefficient f a L j)) :
    ∀ u ∈ Set.Icc a (a + L),
      HasSum (fun j : ℤ => normalizedCoefficient f a L j *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (u : ℂ) / (L : ℂ)))
        (f u) := by

  have hfzero : ∀ x, x < b0 ∨ b1 < x → f x = 0 := by
    intro x hx
    by_contra h
    have hxs : x ∈ Function.support f := by simpa [Function.mem_support] using h
    exact absurd (hsupport (subset_tsupport f hxs)) (by
      rintro ⟨h1, h2⟩; rcases hx with h | h <;> linarith)
  have hfa : f a = 0 := hfzero a (Or.inl ha)
  have hfb : f (a + L) = 0 := hfzero (a + L) (Or.inr (by linarith))
  haveI : Fact (0 < L) := ⟨hL⟩

  let g : C(AddCircle L, ℂ) :=
    ⟨AddCircle.liftIoc L a f,
      AddCircle.liftIoc_continuous (p := L) (a := a) (f := f)
        (by rw [hfa, hfb]) hf.continuousOn⟩

  have hcoeff : ∀ j : ℤ, fourierCoeff g j = normalizedCoefficient f a L j := by
    intro j
    have h1 : fourierCoeff g j =
        (L : ℂ)⁻¹ * ∫ x in Set.Ioc a (a + L),
          f x * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (x : ℂ) / (L : ℂ)) := by
      rw [fourierCoeff_eq_intervalIntegral g j a, Complex.real_smul, one_div]
      congr 1
      · exact Complex.ofReal_inv L
      · rw [intervalIntegral.integral_of_le (le_of_lt (lt_add_of_pos_right a hL))]
        refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
        rw [smul_eq_mul]
        change fourier (-j) (x : AddCircle L) * AddCircle.liftIoc L a f (x : AddCircle L)
          = f x * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (x : ℂ) / (L : ℂ))
        rw [AddCircle.liftIoc_coe_apply hx, fourier_coe_apply, mul_comm]
        congr 1
        push_cast
        ring_nf
    have h2 : normalizedCoefficient f a L j =
        (L : ℂ)⁻¹ * ∫ x in Set.Ioc a (a + L),
          f x * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (x : ℂ) / (L : ℂ)) := by
      rw [normalizedCoefficient, integral_Icc_eq_integral_Ioc]
    rw [h1, h2]
  have hsumg : Summable (fourierCoeff g) := hsummable.congr fun j => (hcoeff j).symm
  intro u hu
  have hpt := has_pointwise_sum_fourier_series_of_summable hsumg (u : AddCircle L)
  have hgu : g (u : AddCircle L) = f u := by
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h]
      have hper : (a : AddCircle L) = ((a + L : ℝ) : AddCircle L) :=
        (AddCircle.coe_add_period L a).symm
      rw [hper]
      change AddCircle.liftIoc L a f ((a + L : ℝ) : AddCircle L) = f a
      rw [AddCircle.liftIoc_coe_apply
        (show (a + L) ∈ Set.Ioc a (a + L) from ⟨lt_add_of_pos_right a hL, le_rfl⟩), hfb, hfa]
    · change AddCircle.liftIoc L a f (u : AddCircle L) = f u
      rw [AddCircle.liftIoc_coe_apply (show u ∈ Set.Ioc a (a + L) from ⟨h, hu.2⟩)]
  rw [hgu] at hpt
  simpa only [hcoeff, smul_eq_mul, fourier_coe_apply] using hpt

end
end DedekindZetaZeroFree.ProbeLogarithmicRowCoefficients

end

section

namespace DedekindZetaZeroFree
noncomputable section
open scoped Classical NumberField BoundedContinuousFunction
open NumberField IsDedekindDomain MeasureTheory

namespace ProbeLogWeight
variable {F : Type} [Field F] [NumberField F]

def row (A : SArithmeticData F) (W0 : SLocalProduct F A.Sf → ℂ)
    (W1 : ProbeRealAnnularWeight) (v : ℝ) (y : SLocalProduct F A.Sf) : ℂ :=
  (v ^ (-(1 / 2 : ℝ)) : ℝ) * (W1 v : ℂ) *
    W0 (y * (ProbeSheet.ell A v)⁻¹.val)

def mode (L : ℝ) (j : ℤ) (v : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (Real.log v : ℂ) / (L : ℂ))

def truncatedSeries (A : SArithmeticData F) (v0 v1 L : ℝ)
    (c : ℤ → SLocalProduct F A.Sf →ᵇ ℂ) (v : ℝ) (y : SLocalProduct F A.Sf) : ℂ :=
  if v ∈ Set.Icc v0 v1 then ∑' j : ℤ, c j y * mode L j v else 0

def coefficient (A : SArithmeticData F) (W0 : SLocalProduct F A.Sf → ℂ)
    (W1 : ProbeRealAnnularWeight) (a L : ℝ) (j : ℤ)
    (y : SLocalProduct F A.Sf) : ℂ :=
  (L : ℂ)⁻¹ * ∫ u in Set.Icc a (a + L),
    row A W0 W1 (Real.exp u) y *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (u : ℂ) / (L : ℂ))

def Separation (A : SArithmeticData F) (W0 : SLocalProduct F A.Sf → ℂ)
    (W1 : ProbeRealAnnularWeight) (v0 v1 a L : ℝ)
    (K : Set (SLocalProduct F A.Sf))
    (c : ℤ → SLocalProduct F A.Sf →ᵇ ℂ) : Prop :=
  0 < v0 ∧ v0 < v1 ∧ 0 < L ∧
  a < Real.log v0 ∧ Real.log v1 < a + L ∧
  tsupport W1 ⊆ Set.Ioo v0 v1 ∧
  IsCompact K ∧ K ⊆ {x | IsUnit x} ∧
  (∀ v ∈ Set.Icc v0 v1, ∀ x ∈ tsupport W0,
    (ProbeSheet.ell A v).val * x ∈ K) ∧
  (∀ j : ℤ, tsupport (c j) ⊆ K) ∧
  (∀ (j : ℤ) (y : SLocalProduct F A.Sf), c j y = coefficient A W0 W1 a L j y) ∧
  Summable (fun j : ℤ => ‖c j‖) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℤ, ‖c j‖ ≤ C / (1 + (j : ℝ) ^ 2)) ∧
  (∀ (v : ℝ), 0 < v → Real.log v ∈ Set.Icc a (a + L) →
    ∀ y : SLocalProduct F A.Sf,
      Summable (fun j : ℤ => ‖c j y * mode L j v‖) ∧
      HasSum (fun j : ℤ => c j y * mode L j v) (row A W0 W1 v y)) ∧
  TendstoUniformlyOn
    (fun s : Finset ℤ => fun p : ℝ × SLocalProduct F A.Sf =>
      ∑ j ∈ s, c j p.2 * mode L j (Real.exp p.1))
    (fun p : ℝ × SLocalProduct F A.Sf => row A W0 W1 (Real.exp p.1) p.2)
    Filter.atTop (Set.Icc a (a + L) ×ˢ Set.univ) ∧
  (∀ (v : ℝ), 0 < v → ∀ y : SLocalProduct F A.Sf,
    row A W0 W1 v y = truncatedSeries A v0 v1 L c v y) ∧
  (∀ (I : A.Exterior) (y : SLocalProduct F A.Sf),
    row A W0 W1 (A.exteriorNorm I) y =
      truncatedSeries A v0 v1 L c (A.exteriorNorm I) y)

theorem norm_mode (L : ℝ) (j : ℤ) (v : ℝ) : ‖mode L j v‖ = 1 := by
  simp [mode, Complex.norm_exp, Complex.div_re, Complex.mul_re, Complex.mul_im]

theorem row_eq_zero_outside_range (A : SArithmeticData F) (W0 : SLocalProduct F A.Sf → ℂ)
    (W1 : ProbeRealAnnularWeight) {v0 v1 v : ℝ}
    (hsupport : tsupport W1 ⊆ Set.Ioo v0 v1) (hv : v ∉ Set.Icc v0 v1)
    (y : SLocalProduct F A.Sf) : row A W0 W1 v y = 0 := by
  have hz : W1 v = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hv (Set.Ioo_subset_Icc_self (hsupport h))
  simp [row, hz]

theorem summable_norm_modes (A : SArithmeticData F) (c : ℤ → SLocalProduct F A.Sf →ᵇ ℂ)
    (hc : Summable (fun j => ‖c j‖)) (L v : ℝ) (y : SLocalProduct F A.Sf) :
    Summable (fun j => ‖c j y * mode L j v‖) := by
  apply hc.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
  rw [norm_mul, norm_mode, mul_one]
  exact BoundedContinuousFunction.norm_coe_le_norm _ _

 theorem tendstoUniformlyOn_modes (A : SArithmeticData F) (c : ℤ → SLocalProduct F A.Sf →ᵇ ℂ)
    (hc : Summable (fun j => ‖c j‖)) (L : ℝ) (s : Set (ℝ × SLocalProduct F A.Sf)) :
    TendstoUniformlyOn
      (fun t : Finset ℤ => fun p : ℝ × SLocalProduct F A.Sf =>
        ∑ j ∈ t, c j p.2 * mode L j (Real.exp p.1))
      (fun p : ℝ × SLocalProduct F A.Sf => ∑' j, c j p.2 * mode L j (Real.exp p.1))
      Filter.atTop s := by
  apply tendstoUniformlyOn_tsum hc
  intro j p hp
  rw [norm_mul, norm_mode, mul_one]
  exact BoundedContinuousFunction.norm_coe_le_norm _ _

theorem row_eq_truncatedSeries_of_hasSum (A : SArithmeticData F) (W0 : SLocalProduct F A.Sf → ℂ)
    (W1 : ProbeRealAnnularWeight) (v0 v1 a L : ℝ)
    (c : ℤ → SLocalProduct F A.Sf →ᵇ ℂ)
    (hsupport : tsupport W1 ⊆ Set.Ioo v0 v1)
    (hlog : ∀ v ∈ Set.Icc v0 v1, 0 < v → Real.log v ∈ Set.Icc a (a + L))
    (hsum : ∀ v, 0 < v → Real.log v ∈ Set.Icc a (a + L) → ∀ y,
      HasSum (fun j : ℤ => c j y * mode L j v) (row A W0 W1 v y)) :
    ∀ v, 0 < v → ∀ y, row A W0 W1 v y = truncatedSeries A v0 v1 L c v y := by
  intro v hv y
  by_cases hmem : v ∈ Set.Icc v0 v1
  · simpa [truncatedSeries, hmem] using (hsum v hv (hlog v hmem hv) y).tsum_eq.symm
  · simp [truncatedSeries, hmem, row_eq_zero_outside_range A W0 W1 hsupport hmem y]

theorem tendstoUniformlyOn_row_of_hasSum (A : SArithmeticData F) (W0 : SLocalProduct F A.Sf → ℂ)
    (W1 : ProbeRealAnnularWeight) (a L : ℝ)
    (c : ℤ → SLocalProduct F A.Sf →ᵇ ℂ)
    (hc : Summable (fun j => ‖c j‖))
    (hsum : ∀ v, 0 < v → Real.log v ∈ Set.Icc a (a + L) → ∀ y,
      HasSum (fun j : ℤ => c j y * mode L j v) (row A W0 W1 v y)) :
    TendstoUniformlyOn
      (fun t : Finset ℤ => fun p : ℝ × SLocalProduct F A.Sf =>
        ∑ j ∈ t, c j p.2 * mode L j (Real.exp p.1))
      (fun p : ℝ × SLocalProduct F A.Sf => row A W0 W1 (Real.exp p.1) p.2)
      Filter.atTop (Set.Icc a (a + L) ×ˢ Set.univ) := by
  apply (tendstoUniformlyOn_modes A c hc L _).congr_right
  intro p hp
  exact (hsum _ (Real.exp_pos _) (by simpa only [Real.log_exp] using hp.1) _).tsum_eq

theorem continuous_ell_val_exp (A : SArithmeticData F) :
    Continuous (fun u : ℝ => (ProbeSheet.ell A (Real.exp u)).val) := by
  have hc := A.continuous_radialSection.comp
    (show Continuous (fun u : ℝ => (⟨Real.exp u, Real.exp_pos u⟩ : {T : ℝ // 0 < T})) from
      Real.continuous_exp.subtype_mk _)
  have hh : (fun u : ℝ => (ProbeSheet.ell A (Real.exp u)).val) =
    fun u => ((fun w => ((A.radialSection (Real.exp u) (Real.exp_pos u)).1 w).val),
      fun v => ((A.radialSection (Real.exp u) (Real.exp_pos u)).2 v).val) := by
    funext u
    simp only [ProbeSheet.ell, dif_pos (Real.exp_pos u)]
    rfl
  rw [hh]
  apply Continuous.prodMk
  · exact continuous_pi (fun w => Units.continuous_val.comp ((continuous_apply w).comp (continuous_fst.comp hc)))
  · exact continuous_pi (fun v => Units.continuous_val.comp ((continuous_apply v).comp (continuous_snd.comp hc)))

theorem exists_positive_support_range (W1 : ProbeRealAnnularWeight) :
    ∃ v0 v1 : ℝ, 0 < v0 ∧ v0 < v1 ∧ tsupport W1 ⊆ Set.Ioo v0 v1 := by
  obtain ⟨m, hm, hmin⟩ := W1.compactSupport.exists_forall_le' continuous_id.continuousOn
    (fun v hv => W1.support_positive hv)
  obtain ⟨M, hM⟩ := W1.compactSupport.bddAbove
  refine ⟨m / 2, max M m + 1, by linarith, ?_, ?_⟩
  · have := le_max_right M m
    linarith
  · intro v hv
    constructor
    · have h : m ≤ v := hmin v hv
      linarith
    · have h := hM hv
      have := le_max_left M m
      linarith

theorem exists_log_period {v0 v1 : ℝ} (hv0 : 0 < v0) (hv1 : v0 < v1) :
    ∃ a L : ℝ, 0 < L ∧ a < Real.log v0 ∧ Real.log v1 < a + L ∧
      ∀ v ∈ Set.Icc v0 v1, Real.log v ∈ Set.Icc a (a + L) := by
  have hlog : Real.log v0 < Real.log v1 := Real.log_lt_log hv0 hv1
  refine ⟨Real.log v0 - 1, Real.log v1 - Real.log v0 + 2, by linarith,
    by linarith, by linarith, ?_⟩
  intro v hv
  have hvpos : 0 < v := hv0.trans_le hv.1
  have hleft := Real.log_le_log hv0 hv.1
  have hright := Real.log_le_log hvpos hv.2
  constructor <;> linarith

theorem exists_compact_annulus (A : SArithmeticData F) (W0 : SLocalProduct F A.Sf → ℂ)
    (hcompact : HasCompactSupport W0) (hannular : tsupport W0 ⊆ {x | IsUnit x})
    {v0 v1 : ℝ} (hv0 : 0 < v0) (hv1 : v0 < v1) :
    ∃ K : Set (SLocalProduct F A.Sf), IsCompact K ∧ K ⊆ {x | IsUnit x} ∧
      ∀ v ∈ Set.Icc v0 v1, ∀ x ∈ tsupport W0, (ProbeSheet.ell A v).val * x ∈ K := by
  let f : ℝ × SLocalProduct F A.Sf → SLocalProduct F A.Sf :=
    fun p => (ProbeSheet.ell A (Real.exp p.1)).val * p.2
  have hf : Continuous f := ((continuous_ell_val_exp A).comp continuous_fst).mul continuous_snd
  let T := Set.Icc (Real.log v0) (Real.log v1) ×ˢ tsupport W0
  refine ⟨f '' T, (isCompact_Icc.prod hcompact).image hf, ?_, ?_⟩
  · rintro y ⟨⟨u, x⟩, hx, rfl⟩
    exact (ProbeSheet.ell A (Real.exp u)).isUnit.mul (hannular hx.2)
  · intro v hv x hx
    have hvpos := hv0.trans_le hv.1
    refine ⟨(Real.log v, x), ⟨?_, hx⟩, ?_⟩
    · exact ⟨Real.log_le_log hv0 hv.1, Real.log_le_log hvpos hv.2⟩
    · simp [f, Real.exp_log hvpos]

theorem row_eq_zero_outside_annulus (A : SArithmeticData F) (W0 : SLocalProduct F A.Sf → ℂ)
    (W1 : ProbeRealAnnularWeight) {v0 v1 : ℝ} (K : Set (SLocalProduct F A.Sf))
    (hsupport : tsupport W1 ⊆ Set.Ioo v0 v1)
    (hK : ∀ v ∈ Set.Icc v0 v1, ∀ x ∈ tsupport W0, (ProbeSheet.ell A v).val * x ∈ K)
    {v : ℝ} {y : SLocalProduct F A.Sf} (hy : y ∉ K) : row A W0 W1 v y = 0 := by
  by_cases hv : W1 v = 0
  · simp [row, hv]
  have hvinterval : v ∈ Set.Icc v0 v1 :=
    Set.Ioo_subset_Icc_self (hsupport (subset_tsupport W1 hv))
  have hw : W0 (y * (ProbeSheet.ell A v)⁻¹.val) = 0 := by
    by_contra hw
    have hx := hK v hvinterval _ (subset_tsupport W0 hw)
    apply hy
    convert hx using 1
    simp [mul_left_comm, mul_assoc]
  simp [row, hw]

theorem coefficient_tsupport_subset (A : SArithmeticData F) (W0 : SLocalProduct F A.Sf → ℂ)
    (W1 : ProbeRealAnnularWeight) {v0 v1 : ℝ} (K : Set (SLocalProduct F A.Sf))
    (hsupport : tsupport W1 ⊆ Set.Ioo v0 v1) (hclosed : IsClosed K)
    (hK : ∀ v ∈ Set.Icc v0 v1, ∀ x ∈ tsupport W0, (ProbeSheet.ell A v).val * x ∈ K)
    (a L : ℝ) (j : ℤ) : tsupport (coefficient A W0 W1 a L j) ⊆ K := by
  apply closure_minimal _ hclosed
  intro y hy
  by_contra hyK
  have hz : coefficient A W0 W1 a L j y = 0 := by
    simp only [coefficient, row_eq_zero_outside_annulus A W0 W1 K hsupport hK hyK, zero_mul,
      integral_zero, mul_zero]
  exact hy hz

theorem separation_of_coefficients (A : SArithmeticData F)
    (W0 : SLocalProduct F A.Sf → ℂ) (W1 : ProbeRealAnnularWeight)
    (v0 v1 a L : ℝ) (K : Set (SLocalProduct F A.Sf))
    (c : ℤ → SLocalProduct F A.Sf →ᵇ ℂ)
    (hv0 : 0 < v0) (hv1 : v0 < v1) (hL : 0 < L)
    (ha : a < Real.log v0) (hb : Real.log v1 < a + L)
    (hsupport : tsupport W1 ⊆ Set.Ioo v0 v1)
    (hcompact : IsCompact K) (hannular : K ⊆ {x | IsUnit x})
    (hK : ∀ v ∈ Set.Icc v0 v1, ∀ x ∈ tsupport W0, (ProbeSheet.ell A v).val * x ∈ K)
    (hcoeff : ∀ j y, c j y = coefficient A W0 W1 a L j y)
    (hc : Summable (fun j => ‖c j‖))
    (hdecay : ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℤ, ‖c j‖ ≤ C / (1 + (j : ℝ) ^ 2))
    (hsum : ∀ v, 0 < v → Real.log v ∈ Set.Icc a (a + L) → ∀ y,
      HasSum (fun j : ℤ => c j y * mode L j v) (row A W0 W1 v y)) :
    Separation A W0 W1 v0 v1 a L K c := by
  have hlog : ∀ v ∈ Set.Icc v0 v1, 0 < v → Real.log v ∈ Set.Icc a (a + L) := by
    intro v hv hvpos
    exact ⟨ha.le.trans (Real.log_le_log hv0 hv.1),
      (Real.log_le_log hvpos hv.2).trans hb.le⟩
  have hcut := row_eq_truncatedSeries_of_hasSum A W0 W1 v0 v1 a L c hsupport hlog hsum
  refine ⟨hv0, hv1, hL, ha, hb, hsupport, hcompact, hannular, hK, ?_, hcoeff,
    hc, hdecay, ?_, tendstoUniformlyOn_row_of_hasSum A W0 W1 a L c hc hsum, hcut, ?_⟩
  · intro j
    have heq : ⇑(c j) = coefficient A W0 W1 a L j := funext (hcoeff j)
    rw [heq]
    exact coefficient_tsupport_subset A W0 W1 K hsupport hcompact.isClosed hK a L j
  · intro v hv hvl y
    exact ⟨summable_norm_modes A c hc L v y, hsum v hv hvl y⟩
  · intro I y
    exact hcut _ (A.exteriorNorm_pos I) y

theorem summable_quadratic_majorant : Summable (fun j : ℤ => 1 / (1 + (j : ℝ) ^ 2)) := by
  have hs : Summable (fun j : ℤ => 1 / (j : ℝ) ^ 2) := Real.summable_one_div_int_pow.mpr (by norm_num)
  apply Summable.of_norm_bounded_eventually hs
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply one_div_le_one_div_of_le
  · positivity
  · linarith

theorem summable_norm_coefficients_of_quadratic_bound (A : SArithmeticData F)
    (c : ℤ → SLocalProduct F A.Sf →ᵇ ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ j : ℤ, ‖c j‖ ≤ C / (1 + (j : ℝ) ^ 2)) :
    Summable (fun j => ‖c j‖) := by
  apply (summable_quadratic_majorant.mul_left C).of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
  simpa only [mul_one_div] using hbound j

theorem continuous_weight (A : SArithmeticData F) (W0 : SLocalProduct F A.Sf → ℂ)
    (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0) : Continuous W0 := by
  obtain ⟨fr, fc, ff, hr, hc, hf, heq⟩ := hW0
  have hm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply v.1)
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply v.1)
  have he : W0 = (fun x =>
      (∏ v, fr v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 v)) *
      (∏ v, fc v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v)) *
      ∏ v : ↥A.Sf, ff v (x.2 v)) := funext heq
  rw [he]
  apply Continuous.mul
  · apply Continuous.mul
    · apply continuous_finset_prod
      intro v hv
      exact (hr v).1.continuous.comp ((continuous_apply v).comp (continuous_fst.comp (hm.comp continuous_fst)))
    · apply continuous_finset_prod
      intro v hv
      exact (hc v).1.continuous.comp ((continuous_apply v).comp (continuous_snd.comp (hm.comp continuous_fst)))
  · apply continuous_finset_prod
    intro v hv
    exact (hf v).1.continuous.comp ((continuous_apply v).comp continuous_snd)

theorem continuous_ell_inv_exp (A : SArithmeticData F) :
    Continuous (fun u : ℝ => ((ProbeSheet.ell A (Real.exp u))⁻¹).val) := by
  have hc := A.continuous_radialSection.comp
    (show Continuous (fun u : ℝ => (⟨Real.exp u, Real.exp_pos u⟩ : {T : ℝ // 0 < T})) from
      Real.continuous_exp.subtype_mk _)
  have hh : (fun u : ℝ => ((ProbeSheet.ell A (Real.exp u))⁻¹).val) =
    fun u => ((fun w => (((A.radialSection (Real.exp u) (Real.exp_pos u)).1 w)⁻¹).val),
      fun v => (((A.radialSection (Real.exp u) (Real.exp_pos u)).2 v)⁻¹).val) := by
    funext u
    simp only [ProbeSheet.ell, dif_pos (Real.exp_pos u)]
    rfl
  rw [hh]
  apply Continuous.prodMk
  · exact continuous_pi (fun w => Units.continuous_coe_inv.comp ((continuous_apply w).comp (continuous_fst.comp hc)))
  · exact continuous_pi (fun v => Units.continuous_coe_inv.comp ((continuous_apply v).comp (continuous_snd.comp hc)))

local instance instMeasurableSpaceLogWeightSLocalProduct (A : SArithmeticData F) : MeasurableSpace (SLocalProduct F A.Sf) := borel _

local instance instBorelSpaceLogWeightSLocalProduct (A : SArithmeticData F) : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩

theorem continuous_row_exp (A : SArithmeticData F) (W0 : SLocalProduct F A.Sf → ℂ)
    (W1 : ProbeRealAnnularWeight) (hW0 : Continuous W0) :
    Continuous (fun p : ℝ × SLocalProduct F A.Sf => row A W0 W1 (Real.exp p.1) p.2) := by
  have hexp : Continuous (fun p : ℝ × SLocalProduct F A.Sf => Real.exp p.1) :=
    Real.continuous_exp.comp continuous_fst
  exact ((Complex.continuous_ofReal.comp
    (hexp.rpow_const (p := -(1 / 2 : ℝ)) (fun p => Or.inl (Real.exp_ne_zero _)))).mul
    (Complex.continuous_ofReal.comp (W1.smooth.continuous.comp hexp))).mul
    (hW0.comp (continuous_snd.mul ((continuous_ell_inv_exp A).comp continuous_fst)))

theorem continuous_coefficient_of_continuous (A : SArithmeticData F) (W0 : SLocalProduct F A.Sf → ℂ)
    (W1 : ProbeRealAnnularWeight) (hW0 : Continuous W0) (a L : ℝ) (j : ℤ) :
    Continuous (coefficient A W0 W1 a L j) := by
  change Continuous (fun y => (L : ℂ)⁻¹ * ∫ u in Set.Icc a (a + L),
    row A W0 W1 (Real.exp u) y *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (u : ℂ) / (L : ℂ)))
  have hr : Continuous (fun p : SLocalProduct F A.Sf × ℝ =>
      row A W0 W1 (Real.exp p.2) p.1) :=
    (continuous_row_exp A W0 W1 hW0).comp (continuous_snd.prodMk continuous_fst)
  have hf : Continuous (Function.uncurry (fun y u => row A W0 W1 (Real.exp u) y *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (u : ℂ) / (L : ℂ)))) :=
    hr.mul (Complex.continuous_exp.comp
      ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)).div_const _))
  by_cases hL : 0 ≤ L
  · have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := a) hf (continuous_const : Continuous (fun _ : SLocalProduct F A.Sf => a + L))
    have hab : a ≤ a + L := le_add_of_nonneg_right hL
    have hi' : Continuous (fun y => (L : ℂ)⁻¹ *
        ∫ u in a..(a + L), row A W0 W1 (Real.exp u) y *
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (u : ℂ) / (L : ℂ)) ∂volume) :=
      continuous_const.mul hi
    simp only [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at hi'
    exact hi'
  · have hempty : Set.Icc a (a + L) = ∅ := Set.Icc_eq_empty_of_lt (by linarith)
    simpa only [coefficient, hempty, Measure.restrict_empty, integral_zero_measure, mul_zero]
      using (continuous_const : Continuous (fun _ : SLocalProduct F A.Sf => (0 : ℂ)))

theorem exists_bounded_coefficients_on_annulus (A : SArithmeticData F)
    (W0 : SLocalProduct F A.Sf → ℂ) (W1 : ProbeRealAnnularWeight)
    (hW0 : Continuous W0) {v0 v1 : ℝ} (K : Set (SLocalProduct F A.Sf))
    (hsupport : tsupport W1 ⊆ Set.Ioo v0 v1) (hcompact : IsCompact K)
    (hK : ∀ v ∈ Set.Icc v0 v1, ∀ x ∈ tsupport W0, (ProbeSheet.ell A v).val * x ∈ K)
    (a L : ℝ) :
    ∃ c : ℤ → SLocalProduct F A.Sf →ᵇ ℂ,
      (∀ j y, c j y = coefficient A W0 W1 a L j y) ∧
      (∀ j, tsupport (c j) ⊆ K) := by
  have hs (j : ℤ) := coefficient_tsupport_subset A W0 W1 K hsupport hcompact.isClosed hK a L j
  have hc (j : ℤ) := continuous_coefficient_of_continuous A W0 W1 hW0 a L j
  have hb (j : ℤ) : ∃ C, ∀ y, ‖coefficient A W0 W1 a L j y‖ ≤ C := by
    have hcs : HasCompactSupport (coefficient A W0 W1 a L j) :=
      hcompact.of_isClosed_subset (isClosed_tsupport _) (hs j)
    exact hcs.exists_bound_of_continuous (hc j)
  choose C hC using hb
  let c : ℤ → SLocalProduct F A.Sf →ᵇ ℂ := fun j =>
    BoundedContinuousFunction.ofNormedAddCommGroup _ (hc j) (C j) (hC j)
  exact ⟨c, fun j y => rfl, hs⟩

end ProbeLogWeight

theorem probe_logweight_separation (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (W0 : SLocalProduct F A.Sf → ℂ)
    (W1 : ProbeRealAnnularWeight) (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0)
    (hcompact : HasCompactSupport W0) (hannular : tsupport W0 ⊆ {x | IsUnit x}) :
    ∃ (v0 v1 a L : ℝ) (K : Set (SLocalProduct F A.Sf))
      (c : ℤ → SLocalProduct F A.Sf →ᵇ ℂ),
      ProbeLogWeight.Separation A W0 W1 v0 v1 a L K c := by
  obtain ⟨v0, v1, hv0, hv1, hs⟩ := ProbeLogWeight.exists_positive_support_range W1
  obtain ⟨a, L, hL, ha, hb, hlog⟩ := ProbeLogWeight.exists_log_period hv0 hv1
  obtain ⟨K, hKcompact, hKannular, hK⟩ :=
    ProbeLogWeight.exists_compact_annulus A W0 hcompact hannular hv0 hv1
  obtain ⟨c, hcoeff, _⟩ := ProbeLogWeight.exists_bounded_coefficients_on_annulus
    A W0 W1 (ProbeLogWeight.continuous_weight A W0 hW0) K hs hKcompact hK a L
  let f : SLocalProduct F A.Sf → ℝ → ℂ :=
    fun y u => ProbeLogarithmicRowCoefficients.logRow A W0 W1 u y
  have hfrow (y : SLocalProduct F A.Sf) (u : ℝ) :
      f y u = ProbeLogWeight.row A W0 W1 (Real.exp u) y := rfl
  have hfsupport : ∀ y, tsupport (f y) ⊆ Set.Icc (Real.log v0) (Real.log v1) := by
    intro y
    apply closure_minimal _ isClosed_Icc
    intro u hu
    have hv : Real.exp u ∈ Set.Icc v0 v1 := by
      by_contra hv
      exact hu (ProbeLogWeight.row_eq_zero_outside_range A W0 W1 hs hv y)
    simpa only [Real.log_exp] using
      (show Real.log (Real.exp u) ∈ Set.Icc (Real.log v0) (Real.log v1) from
        ⟨Real.log_le_log hv0 hv.1, Real.log_le_log (Real.exp_pos _) hv.2⟩)
  obtain ⟨hfsmooth, hfbound⟩ :=
    ProbeLogarithmicRowCoefficients.uniform_log_derivatives A W0 W1 hW0 hcompact hannular
  have hcf (j : ℤ) (y : SLocalProduct F A.Sf) :
      c j y = ProbeLogarithmicRowCoefficients.normalizedCoefficient (f y) a L j := hcoeff j y
  obtain ⟨C, hC, hCb⟩ := ProbeLogarithmicRowCoefficients.quadratic_coefficient_bound f a L
    (Real.log v0) (Real.log v1) hL ha hb hfsupport hfsmooth hfbound
  have hdecay (j : ℤ) : ‖c j‖ ≤ C / (1 + (j : ℝ) ^ 2) := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro y
    rw [hcf]
    exact hCb j y
  have hc : Summable (fun j : ℤ => ‖c j‖) :=
    ProbeLogWeight.summable_norm_coefficients_of_quadratic_bound A c hC hdecay
  have hsum : ∀ v, 0 < v → Real.log v ∈ Set.Icc a (a + L) → ∀ y,
      HasSum (fun j : ℤ => c j y * ProbeLogWeight.mode L j v)
        (ProbeLogWeight.row A W0 W1 v y) := by
    intro v hv hvl y
    have hsc : Summable (fun j : ℤ => ProbeLogarithmicRowCoefficients.normalizedCoefficient (f y) a L j) := by
      apply hc.of_norm_bounded
      intro j
      rw [← hcf]
      exact BoundedContinuousFunction.norm_coe_le_norm _ _
    have hh := ProbeLogarithmicRowCoefficients.hasSum_normalized_coefficients (f y) a L
      (Real.log v0) (Real.log v1) hL ha hb (hfsmooth y).continuous
      (hfsupport y) hsc (Real.log v) hvl
    simpa only [← hcf, ProbeLogWeight.mode, hfrow, Real.exp_log hv] using hh
  exact ⟨v0, v1, a, L, K, c, ProbeLogWeight.separation_of_coefficients A W0 W1
    v0 v1 a L K c hv0 hv1 hL ha hb hs hKcompact hKannular hK hcoeff hc
    ⟨C, hC, hdecay⟩ hsum⟩

end
end DedekindZetaZeroFree

end
