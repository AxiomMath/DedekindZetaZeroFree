module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Convolution

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectorMellin

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory
open scoped Classical

variable (F : Type) [Field F] [NumberField F]

def smoothedSummand (U : ℝ) {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m) (β γ : ℝ)
    (n : Ideal (𝓞 F)) : ℂ :=
  if n ≠ ⊥ then
    (DetectorDef.a F U n : ℂ) * ω n *
      (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I)) *
      (Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) : ℂ)
  else 0

def mellinIntegrand (U : ℝ) (ω : Detector.PrimitiveFrequencyCharacter F) (β γ : ℝ)
    (v : ℂ) : ℂ :=
  Detector.idealLSeries F ω.character ((β : ℂ) + (γ : ℂ) * Complex.I + v) *
    DetectorDef.D F U ω.character ((β : ℂ) + (γ : ℂ) * Complex.I + v) *
    Complex.Gamma v * ((U : ℂ) ^ ((DetectorDef.r : ℂ) * v))

namespace Aux

lemma gamma_vertical_continuous (a : ℝ) (ha : 0 < a) :
    Continuous (fun t : ℝ => Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (Complex.continuousAt_Gamma _ ?_).comp
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt)
  intro n hn
  have hr := congrArg Complex.re hn
  simp at hr
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

lemma gamma_vertical_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (fun t : ℝ => Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨C, hC, h⟩ := detector_sz_gamma_decay a a le_rfl 2
  refine ComparisonShiftProof.integrable_tail _ (4 * C) (gamma_vertical_continuous a ha) ?_
  intro t ht
  have hb := h a ⟨le_rfl, le_rfl⟩ t ht
  have hp : 0 < |t| := by linarith
  have hp' : (0 : ℝ) < 1 + |t| := by linarith
  have key : Real.rpow |t| (-((2 : ℕ) : ℝ)) ≤ 4 * (1 + |t|) ^ (-2 : ℝ) := by
    have h1 : Real.rpow |t| (-((2 : ℕ) : ℝ)) = (|t| ^ 2)⁻¹ := by
      show |t| ^ (-((2 : ℕ) : ℝ)) = _
      rw [Real.rpow_neg (abs_nonneg t), Real.rpow_natCast]
    have h2 : (1 + |t|) ^ (-2 : ℝ) = ((1 + |t|) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hp'.le, Real.rpow_two]
    have e3 : (|t| ^ 2)⁻¹ = 1 / |t| ^ 2 := (one_div _).symm
    have e4 : ((1 + |t|) ^ 2)⁻¹ = 1 / (1 + |t|) ^ 2 := (one_div _).symm
    rw [h1, h2, e3, e4, mul_one_div, div_le_div_iff₀ (pow_pos hp 2) (pow_pos hp' 2)]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (by linarith : (0 : ℝ) ≤ 3 * |t| + 1)]
  calc ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ C * Real.rpow |t| (-((2 : ℕ) : ℝ)) := hb
    _ ≤ C * (4 * (1 + |t|) ^ (-2 : ℝ)) := mul_le_mul_of_nonneg_left key hC.le
    _ = 4 * C * (1 + |t|) ^ (-2 : ℝ) := by ring

lemma gamma_power_integrable (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : 0 < x) :
    Integrable (fun t : ℝ => Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
      (x : ℂ) ^ (-((a : ℂ) + (t : ℂ) * Complex.I))) := by
  have hp : Continuous (fun t : ℝ => (x : ℂ) ^ (-((a : ℂ) + (t : ℂ) * Complex.I))) :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).neg.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hi := (gamma_vertical_integrable a ha).norm.mul_const (x ^ (-a))
  have hbound : ∀ t : ℝ, ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
      (x : ℂ) ^ (-((a : ℂ) + (t : ℂ) * Complex.I))‖ ≤
      ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * x ^ (-a) := by
    intro t
    have hre : (-((a : ℂ) + (t : ℂ) * Complex.I)).re = -a := by simp
    refine le_of_eq ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
  refine hi.mono' ((gamma_vertical_continuous a ha).mul hp).aestronglyMeasurable ?_
  filter_upwards [] with t
  exact hbound t

lemma exp_inversion (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : 0 < x) :
    (Real.exp (-x) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
        (x : ℂ) ^ (-((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hline (t : ℝ) :
      mellin (fun y : ℝ => (Real.exp (-y) : ℂ)) ((a : ℂ) + (t : ℂ) * Complex.I) =
        Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) := by
    have hre : 0 < ((a : ℂ) + (t : ℂ) * Complex.I).re := by simpa using ha
    rw [← Complex.GammaIntegral_eq_mellin, Complex.Gamma_eq_integral hre]
  have hf : MellinConvergent (fun y : ℝ => (Real.exp (-y) : ℂ)) (a : ℂ) := by
    have hre : 0 < (a : ℂ).re := by simpa using ha
    simpa [MellinConvergent, smul_eq_mul, mul_comm] using
      (Complex.GammaIntegral_convergent hre)
  have hF : Complex.VerticalIntegrable
      (mellin (fun y : ℝ => (Real.exp (-y) : ℂ))) a := by
    simpa only [Complex.VerticalIntegrable, hline] using gamma_vertical_integrable a ha
  have hfx : ContinuousAt (fun y : ℝ => (Real.exp (-y) : ℂ)) x := by
    fun_prop
  have hi := (mellinInv_mellin_eq a (fun y : ℝ => (Real.exp (-y) : ℂ)) hx hf hF hfx).symm
  simp only [mellinInv, smul_eq_mul, Complex.real_smul] at hi
  simp_rw [hline] at hi
  simpa only [mul_comm] using hi

lemma power_id (q : ℕ) (X : ℝ) (hq : 0 < q) (hX : 0 < X) (s z : ℂ) :
    (q : ℂ) ^ (-s) * ((((q : ℝ) / X : ℝ)) : ℂ) ^ (-z) =
      (X : ℂ) ^ z * (q : ℂ) ^ (-(s + z)) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hq0 hX.le, Complex.ofReal_natCast,
    Complex.cpow_neg (X : ℂ), div_inv_eq_mul, neg_add, Complex.cpow_add _ _ hqc]
  ring

lemma ideals_countable : Countable (Ideal (𝓞 F)) := by
  apply Set.countable_univ_iff.mp
  have h : (⋃ N : ℕ, {n : Ideal (𝓞 F) | Ideal.absNorm n ≤ N}).Countable :=
    Set.countable_iUnion fun N => (Ideal.finite_setOfPred_absNorm_le N).countable
  have he : (⋃ N : ℕ, {n : Ideal (𝓞 F) | Ideal.absNorm n ≤ N}) = Set.univ := by
    ext n
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨Ideal.absNorm n, le_rfl⟩
  rwa [he] at h

def coef (U : ℝ) {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m) (w : ℂ)
    (n : Ideal (𝓞 F)) : ℂ :=
  if n ≠ ⊥ then (DetectorDef.a F U n : ℂ) * ω n * (Ideal.absNorm n : ℂ) ^ (-w) else 0

def profile (U : ℝ) {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m) (β γ v₀ : ℝ)
    (n : Ideal (𝓞 F)) (t : ℝ) : ℂ :=
  Complex.Gamma ((v₀ : ℂ) + (t : ℂ) * Complex.I) *
    ((((U ^ DetectorDef.r : ℝ)) : ℂ)) ^ ((v₀ : ℂ) + (t : ℂ) * Complex.I) *
    coef F U ω ((β : ℂ) + (γ : ℂ) * Complex.I + ((v₀ : ℂ) + (t : ℂ) * Complex.I)) n

lemma coef_norm_eq (U : ℝ) {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m) (z w : ℂ)
    (h : z.re = w.re) (n : Ideal (𝓞 F)) :
    ‖coef F U ω z n‖ = ‖coef F U ω w n‖ := by
  by_cases hn : n = ⊥
  · simp [coef, hn]
  · have hn' : n ≠ ⊥ := hn
    have hN : 0 < Ideal.absNorm n :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn')
    simp only [coef, if_pos hn', norm_mul, Complex.norm_natCast_cpow_of_pos hN, Complex.neg_re, h]

lemma profile_norm (U : ℝ) (hU : 0 < U) {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m)
    (β γ v₀ : ℝ) (n : Ideal (𝓞 F)) (t : ℝ) :
    ‖profile F U ω β γ v₀ n t‖ =
      ‖Complex.Gamma ((v₀ : ℂ) + (t : ℂ) * Complex.I)‖ * (U ^ DetectorDef.r) ^ v₀ *
        ‖coef F U ω ((β : ℂ) + (γ : ℂ) * Complex.I + (v₀ : ℂ)) n‖ := by
  have hX : 0 < U ^ DetectorDef.r := Real.rpow_pos_of_pos hU _
  have hre : ((β : ℂ) + (γ : ℂ) * Complex.I + ((v₀ : ℂ) + (t : ℂ) * Complex.I)).re =
      ((β : ℂ) + (γ : ℂ) * Complex.I + (v₀ : ℂ)).re := by simp
  have hz : ((v₀ : ℂ) + (t : ℂ) * Complex.I).re = v₀ := by simp
  unfold profile
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX,
    coef_norm_eq F U ω _ _ hre, hz]

lemma profile_eq (U : ℝ) (hU : 0 < U) {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m)
    (β γ v₀ : ℝ) (n : Ideal (𝓞 F)) (hn : n ≠ ⊥) (t : ℝ) :
    profile F U ω β γ v₀ n t =
      ((DetectorDef.a F U n : ℂ) * ω n *
        (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I))) *
      (Complex.Gamma ((v₀ : ℂ) + (t : ℂ) * Complex.I) *
        ((((Ideal.absNorm n : ℝ) / U ^ DetectorDef.r : ℝ)) : ℂ) ^
          (-((v₀ : ℂ) + (t : ℂ) * Complex.I))) := by
  have hN : 0 < Ideal.absNorm n :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)
  have hX : 0 < U ^ DetectorDef.r := Real.rpow_pos_of_pos hU _
  have he := power_id (Ideal.absNorm n) (U ^ DetectorDef.r) hN hX
    ((β : ℂ) + (γ : ℂ) * Complex.I) ((v₀ : ℂ) + (t : ℂ) * Complex.I)
  unfold profile coef
  rw [if_pos hn]
  linear_combination (-((DetectorDef.a F U n : ℂ) * ω n *
    Complex.Gamma ((v₀ : ℂ) + (t : ℂ) * Complex.I))) * he

lemma profile_integrable (U : ℝ) (hU : 0 < U) {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m)
    (β γ v₀ : ℝ) (hv : 0 < v₀) (n : Ideal (𝓞 F)) :
    Integrable (profile F U ω β γ v₀ n) := by
  by_cases hn : n = ⊥
  · have h0 : profile F U ω β γ v₀ n = fun _ => 0 := by
      funext t
      simp [profile, coef, hn]
    rw [h0]
    exact integrable_zero _ _ _
  · have hn' : n ≠ ⊥ := hn
    have hN : 0 < Ideal.absNorm n :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn')
    have hX : 0 < U ^ DetectorDef.r := Real.rpow_pos_of_pos hU _
    have hx : (0 : ℝ) < (Ideal.absNorm n : ℝ) / U ^ DetectorDef.r :=
      div_pos (by exact_mod_cast hN) hX
    have hi := (gamma_power_integrable v₀ hv _ hx).const_mul
      ((DetectorDef.a F U n : ℂ) * ω n *
        (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I)))
    refine hi.congr ?_
    filter_upwards [] with t
    exact (profile_eq F U hU ω β γ v₀ n hn' t).symm

lemma summand_eq (U : ℝ) (hU : 0 < U) {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m)
    (β γ v₀ : ℝ) (hv : 0 < v₀) (n : Ideal (𝓞 F)) :
    smoothedSummand F U ω β γ n =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, profile F U ω β γ v₀ n t := by
  by_cases hn : n = ⊥
  · simp [smoothedSummand, profile, coef, hn]
  · have hn' : n ≠ ⊥ := hn
    have hN : 0 < Ideal.absNorm n :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn')
    have hX : 0 < U ^ DetectorDef.r := Real.rpow_pos_of_pos hU _
    have hx : (0 : ℝ) < (Ideal.absNorm n : ℝ) / U ^ DetectorDef.r :=
      div_pos (by exact_mod_cast hN) hX
    have hi := exp_inversion v₀ hv _ hx
    rw [← neg_div] at hi
    have hI : ∫ t : ℝ, profile F U ω β γ v₀ n t =
        ((DetectorDef.a F U n : ℂ) * ω n *
          (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I))) *
        ∫ t : ℝ, Complex.Gamma ((v₀ : ℂ) + (t : ℂ) * Complex.I) *
          ((((Ideal.absNorm n : ℝ) / U ^ DetectorDef.r : ℝ)) : ℂ) ^
            (-((v₀ : ℂ) + (t : ℂ) * Complex.I)) := by
      calc ∫ t : ℝ, profile F U ω β γ v₀ n t
          = ∫ t : ℝ, ((DetectorDef.a F U n : ℂ) * ω n *
              (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I))) *
            (Complex.Gamma ((v₀ : ℂ) + (t : ℂ) * Complex.I) *
              ((((Ideal.absNorm n : ℝ) / U ^ DetectorDef.r : ℝ)) : ℂ) ^
                (-((v₀ : ℂ) + (t : ℂ) * Complex.I))) := by
            refine integral_congr_ae ?_
            filter_upwards [] with t
            exact profile_eq F U hU ω β γ v₀ n hn' t
        _ = _ := integral_const_mul _ _
    unfold smoothedSummand
    rw [if_pos hn', hI]
    linear_combination ((DetectorDef.a F U n : ℂ) * ω n *
      (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I))) * hi

end Aux

theorem detector_mellin_identity (U : ℝ) (hU : 2 ≤ U)
    (ω : Detector.PrimitiveFrequencyCharacter F) (hω : ¬ ω.character.IsPrincipal)
    (β : ℝ) (hβ : DetectorDef.σ₀ ≤ β ∧ β ≤ 1) (γ : ℝ) (v₀ : ℝ) (hv₀ : 1 < v₀) :
    Summable (fun n : Ideal (𝓞 F) => ‖smoothedSummand F U ω.character β γ n‖) ∧
    Integrable (fun t : ℝ => mellinIntegrand F U ω β γ ((v₀ : ℂ) + (t : ℂ) * Complex.I)) ∧
    ∑' n : Ideal (𝓞 F), smoothedSummand F U ω.character β γ n =
      comparisonVerticalIntegral v₀ (mellinIntegrand F U ω β γ) := by
  classical
  letI := Aux.ideals_countable F
  have hU0 : 0 < U := by linarith
  have hv0 : 0 < v₀ := by linarith
  have hβpos : 0 < β := lt_of_lt_of_le (by unfold DetectorDef.σ₀; norm_num) hβ.1
  have hre0 : ((β : ℂ) + (γ : ℂ) * Complex.I + (v₀ : ℂ)).re = β + v₀ := by simp
  have hsumv : Summable (Aux.coef F U ω.character
      ((β : ℂ) + (γ : ℂ) * Complex.I + (v₀ : ℂ))) :=
    (DetectorConvolution.idealLSeries_mul_D F ω.conductor ω.conductor_ne_zero ω.character
      ω.primitive U _ (by rw [hre0]; linarith)).1
  have hcn := hsumv.norm
  have hg : Integrable (fun t : ℝ =>
      ‖Complex.Gamma ((v₀ : ℂ) + (t : ℂ) * Complex.I)‖) :=
    (Aux.gamma_vertical_integrable v₀ hv0).norm
  have hp := Aux.profile_integrable F U hU0 ω.character β γ v₀ hv0
  have hn : Summable (fun n : Ideal (𝓞 F) =>
      ∫ t : ℝ, ‖Aux.profile F U ω.character β γ v₀ n t‖) := by
    have he (n : Ideal (𝓞 F)) :
        (∫ t : ℝ, ‖Aux.profile F U ω.character β γ v₀ n t‖) =
        ((∫ t : ℝ, ‖Complex.Gamma ((v₀ : ℂ) + (t : ℂ) * Complex.I)‖) *
          (U ^ DetectorDef.r) ^ v₀) *
          ‖Aux.coef F U ω.character ((β : ℂ) + (γ : ℂ) * Complex.I + (v₀ : ℂ)) n‖ := by
      simp_rw [Aux.profile_norm F U hU0 ω.character β γ v₀ n]
      rw [integral_mul_const, integral_mul_const]
    simp_rw [he]
    exact hcn.mul_left _
  have ha : Summable (fun n : Ideal (𝓞 F) =>
      ‖smoothedSummand F U ω.character β γ n‖) := by
    apply (hn.mul_left ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖).of_nonneg_of_le
      (fun n => norm_nonneg _)
    intro n
    rw [Aux.summand_eq F U hU0 ω.character β γ v₀ hv0 n, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
  have hpoint (t : ℝ) : (∑' n : Ideal (𝓞 F), Aux.profile F U ω.character β γ v₀ n t) =
      mellinIntegrand F U ω β γ ((v₀ : ℂ) + (t : ℂ) * Complex.I) := by
    have hre1 : ((β : ℂ) + (γ : ℂ) * Complex.I + ((v₀ : ℂ) + (t : ℂ) * Complex.I)).re =
        β + v₀ := by simp
    have hsum := (DetectorConvolution.idealLSeries_mul_D F ω.conductor ω.conductor_ne_zero
      ω.character ω.primitive U
      ((β : ℂ) + (γ : ℂ) * Complex.I + ((v₀ : ℂ) + (t : ℂ) * Complex.I))
      (by rw [hre1]; linarith)).2
    have hsum' : HasSum (Aux.coef F U ω.character
        ((β : ℂ) + (γ : ℂ) * Complex.I + ((v₀ : ℂ) + (t : ℂ) * Complex.I)))
        (Detector.idealLSeries F ω.character
          ((β : ℂ) + (γ : ℂ) * Complex.I + ((v₀ : ℂ) + (t : ℂ) * Complex.I)) *
         DetectorDef.D F U ω.character
          ((β : ℂ) + (γ : ℂ) * Complex.I + ((v₀ : ℂ) + (t : ℂ) * Complex.I))) := hsum
    have he := (hsum'.mul_left (Complex.Gamma ((v₀ : ℂ) + (t : ℂ) * Complex.I) *
      (((U ^ DetectorDef.r : ℝ)) : ℂ) ^ ((v₀ : ℂ) + (t : ℂ) * Complex.I))).tsum_eq
    calc (∑' n : Ideal (𝓞 F), Aux.profile F U ω.character β γ v₀ n t)
        = ∑' n : Ideal (𝓞 F), (Complex.Gamma ((v₀ : ℂ) + (t : ℂ) * Complex.I) *
          (((U ^ DetectorDef.r : ℝ)) : ℂ) ^ ((v₀ : ℂ) + (t : ℂ) * Complex.I)) *
          Aux.coef F U ω.character
            ((β : ℂ) + (γ : ℂ) * Complex.I + ((v₀ : ℂ) + (t : ℂ) * Complex.I)) n := rfl
      _ = _ := he
      _ = mellinIntegrand F U ω β γ ((v₀ : ℂ) + (t : ℂ) * Complex.I) := by
        unfold mellinIntegrand
        rw [Complex.cpow_mul_ofReal_nonneg hU0.le]
        ring
  have hint : Integrable (fun t : ℝ =>
      ∑' n : Ideal (𝓞 F), Aux.profile F U ω.character β γ v₀ n t) := by
    apply (hg.mul_const ((U ^ DetectorDef.r) ^ v₀ * ∑' n : Ideal (𝓞 F),
      ‖Aux.coef F U ω.character ((β : ℂ) + (γ : ℂ) * Complex.I + (v₀ : ℂ)) n‖)).mono'
      (AEStronglyMeasurable.tsum fun n => (hp n).aestronglyMeasurable)
    filter_upwards [] with t
    have hnorm : Summable (fun n : Ideal (𝓞 F) =>
        ‖Aux.profile F U ω.character β γ v₀ n t‖) := by
      simp_rw [Aux.profile_norm F U hU0 ω.character β γ v₀]
      exact hcn.mul_left _
    calc _ ≤ ∑' n : Ideal (𝓞 F), ‖Aux.profile F U ω.character β γ v₀ n t‖ :=
          norm_tsum_le_tsum_norm hnorm
      _ = _ := by
        simp_rw [Aux.profile_norm F U hU0 ω.character β γ v₀]
        rw [tsum_mul_left]
        ring
  have hk : (((1 / (2 * Real.pi) : ℝ)) : ℂ) = (2 * (Real.pi : ℂ))⁻¹ := by
    first | (push_cast; ring) | (push_cast) | simp
  refine ⟨ha, ?_, ?_⟩
  · refine hint.congr ?_
    filter_upwards [] with t
    exact hpoint t
  · calc ∑' n : Ideal (𝓞 F), smoothedSummand F U ω.character β γ n
        = ∑' n : Ideal (𝓞 F), ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t : ℝ, Aux.profile F U ω.character β γ v₀ n t :=
          tsum_congr (fun n => Aux.summand_eq F U hU0 ω.character β γ v₀ hv0 n)
      _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∑' n : Ideal (𝓞 F), ∫ t : ℝ, Aux.profile F U ω.character β γ v₀ n t :=
          tsum_mul_left
      _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t : ℝ, ∑' n : Ideal (𝓞 F), Aux.profile F U ω.character β γ v₀ n t := by
          rw [integral_tsum_of_summable_integral_norm hp hn]
      _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t : ℝ, mellinIntegrand F U ω β γ ((v₀ : ℂ) + (t : ℂ) * Complex.I) := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [] with t
          exact hpoint t
      _ = comparisonVerticalIntegral v₀ (mellinIntegrand F U ω β γ) := by
          unfold comparisonVerticalIntegral
          rw [hk]

end

end DedekindZetaZeroFree.Quantitative.DetectorMellin
