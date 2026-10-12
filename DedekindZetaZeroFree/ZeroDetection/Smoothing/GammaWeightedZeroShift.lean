module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.GammaVerticalMoments
public import Mathlib.Analysis.Complex.RemovableSingularity

@[expose] public section

namespace DedekindZetaZeroFree

section Helpers
open Set Filter MeasureTheory Complex
open scoped Topology

private lemma gammaZeroShift_regularized_holomorphic (X : ℝ) (f : ℂ → ℂ) (hX : 0 < X)
 (hf : DifferentiableOn ℂ f {v : ℂ | (-3 / 4 : ℝ) < v.re}) :
 DifferentiableOn ℂ (fun z => Gamma (z+1) * dslope f 0 z * (X : ℂ)^z)
 {v : ℂ | (-3 / 4 : ℝ) < v.re} := by
 have ho : IsOpen {v : ℂ | (-3 / 4 : ℝ) < v.re} := isOpen_lt continuous_const Complex.continuous_re
 have hd := (Complex.differentiableOn_dslope (c := (0 : ℂ)) (ho.mem_nhds (by norm_num))).mpr hf
 apply DifferentiableOn.mul (DifferentiableOn.mul ?_ hd)
   (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).differentiableOn
 intro z hz
 apply DifferentiableAt.differentiableWithinAt
 apply DifferentiableAt.comp z (Complex.differentiableAt_Gamma (z+1) ?_) (differentiableAt_id.add_const 1)
 intro m he
 have hh := congrArg Complex.re he
 simp only [add_re, one_re, neg_re, natCast_re] at hh
 have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
 dsimp at hz
 linarith
private lemma gammaZeroShift_regularized_eq (X : ℝ) (f : ℂ → ℂ) (hf0 : f 0 = 0) (z : ℂ) (hz : z ≠ 0) :
 Gamma (z+1) * dslope f 0 z * (X : ℂ)^z = Gamma z * f z * (X : ℂ)^z := by
 rw [Gamma_add_one z hz, dslope_of_ne f hz, slope]
 simp only [sub_zero, hf0, smul_eq_mul, vsub_eq_sub]
 field_simp
private lemma gammaZeroShift_polynomial_tail (B : ℝ) (hB : 0 ≤ B) (m : ℕ) (hm : B + 2 ≤ m)
 (t : ℝ) (ht : 1 ≤ |t|) :
 |t| ^ (-(m : ℝ)) * (2 + |t|) ^ B ≤
 (3 ^ B * 4) * (1 + |t|) ^ (-2 : ℝ) := by
 have hp : 0 < |t| := by linarith
 have h1 : (2 + |t|) ^ B ≤ 3 ^ B * |t| ^ B := by
  rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (abs_nonneg t)]
  apply Real.rpow_le_rpow (by positivity) (by linarith) hB
 have h2 : |t| ^ (-(m : ℝ)) * |t| ^ B ≤ |t| ^ (-2 : ℝ) := by
  rw [← Real.rpow_add hp]
  exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)
 have h3 : |t| ^ (-2 : ℝ) ≤ 4 * (1 + |t|) ^ (-2 : ℝ) := by
  rw [Real.rpow_neg (abs_nonneg t), Real.rpow_two,
   Real.rpow_neg (by positivity : 0 ≤ 1 + |t|), Real.rpow_two]
  have hden : 0 < (1 + |t|)^2 := by positivity
  rw [← one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity : 0 < |t|^2) hden).2
  nlinarith [sq_nonneg (|t| - 1)]
 calc
  _ ≤ |t| ^ (-(m : ℝ)) * (3 ^ B * |t| ^ B) :=
   mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (abs_nonneg t) _)
  _ = 3 ^ B * (|t| ^ (-(m : ℝ)) * |t| ^ B) := by ring
  _ ≤ 3 ^ B * |t| ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left h2 (by positivity)
  _ ≤ 3 ^ B * (4 * (1 + |t|) ^ (-2 : ℝ)) := mul_le_mul_of_nonneg_left h3 (by positivity)
  _ = _ := by ring

private lemma gammaZeroShift_rectangle_limits (G : ℂ → ℂ) {a b : ℝ} (hab : a≤b)
    (hG : DifferentiableOn ℂ G {z : ℂ | a≤z.re ∧ z.re≤b})
    {Va Vb : ℂ}
    (ha : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, G ((a:ℂ)+t*I)) atTop (𝓝 Va))
    (hb : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, G ((b:ℂ)+t*I)) atTop (𝓝 Vb))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, G ((x:ℂ)+(-T)*I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, G ((x:ℂ)+T*I)) atTop (𝓝 0)) :
    Va = Vb := by
  have hrect (T : ℝ) :
      (∫ x : ℝ in a..b, G ((x:ℂ)+(-T)*I)) -
      (∫ x : ℝ in a..b, G ((x:ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, G ((b:ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, G ((a:ℂ)+t*I)) = 0 := by
    have h := integral_boundary_rect_eq_zero_of_differentiableOn G
      ((a:ℂ)+(-T)*I) ((b:ℂ)+T*I) (hG.mono ?_)
    · simpa [smul_eq_mul] using h
    · intro z hz
      simpa [uIcc_of_le hab] using hz.1
  have hlim := ((hbot.sub htop).add (hb.const_mul I)).sub (ha.const_mul I)
  have hz : (0:ℂ)-0+I*Vb-I*Va=0 := tendsto_nhds_unique hlim
    (by simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) atTop (𝓝 0)))
  exact (mul_left_cancel₀ I_ne_zero (show I*Vb=I*Va by simpa using sub_eq_zero.mp hz)).symm

private lemma gammaZeroShift_integrable_tail (g : ℝ → ℂ) (C : ℝ) (hg : Continuous g)
    (hbound : ∀ t : ℝ, 1 ≤ |t| → ‖g t‖ ≤ C * (1 + |t|) ^ (-2 : ℝ)) :
    Integrable g := by
  have hi : Integrable (fun t : ℝ => C * (1 + |t|) ^ (-2 : ℝ)) := by
    simpa [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (r := 2) (μ := volume) (by simp)).const_mul C
  have hc : IntegrableOn g (Icc (-1) 1) := hg.integrableOn_Icc
  have ht : IntegrableOn g (Icc (-1) 1)ᶜ := by
    apply hi.integrableOn.mono' hg.aestronglyMeasurable.restrict
    apply ae_restrict_of_forall_mem measurableSet_Icc.compl
    intro t ht
    apply hbound t
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · rw [abs_of_neg (by linarith)]
      linarith
    · exact (le_abs_self t).trans' ht.le
  simpa only [union_compl_self, integrableOn_univ] using hc.union ht

private lemma gammaZeroShift_horizontal_decay_limit (F : ℂ → ℂ) (a b C ε : ℝ) (hab : a ≤ b)
    (hε : |ε| = 1)
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ, 1 ≤ |y| →
      ‖F ((x : ℂ) + y * I)‖ ≤ C * (1 + |y|) ^ (-2 : ℝ)) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + (ε*T) * I)) atTop (𝓝 0) := by
  have hr : Tendsto (fun T : ℝ => (1 + T) ^ (-2 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (by simpa using (hr.const_mul C).mul_const |b-a|)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have he : |ε*T| = T := by rw [abs_mul, hε, one_mul, abs_of_nonneg (by linarith)]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hh := hbound x (by simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx)
    (ε*T) (by simpa [he] using hT)
  rw [he, ofReal_mul, Real.rpow_neg (by linarith : 0 ≤ 1 + T), Real.rpow_two] at hh
  exact hh

end Helpers

theorem gamma_zero_shift (a X : ℝ) (f : ℂ → ℂ)
    (ha : a ∈ Set.Icc (-1 / 2 : ℝ) (-124 / 250 : ℝ))
    (hX : 0 < X)
    (hf : DifferentiableOn ℂ f {v : ℂ | (-3 / 4 : ℝ) < v.re})
    (hf0 : f 0 = 0)
    (hGrowth : ∃ M B : ℝ, 0 < M ∧ 0 ≤ B ∧
      ∀ (σ : ℝ), σ ∈ Set.Icc a 2 → ∀ (t : ℝ),
        ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * (2 + |t|) ^ B) :
    MeasureTheory.Integrable (fun t : ℝ =>
      Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
        f ((a : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)) ∧
    MeasureTheory.Integrable (fun t : ℝ =>
      Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) *
        f ((2 : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ ((2 : ℂ) + (t : ℂ) * Complex.I)) ∧
    (∫ t : ℝ, Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) *
        f ((2 : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ ((2 : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ, Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
        f ((a : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)) := open Set Filter MeasureTheory Complex in by
  obtain ⟨M, B, hM, hB, hg⟩ := hGrowth
  have hab : a ≤ 2 := by linarith [ha.2]
  have ho : IsOpen {v : ℂ | (-3 / 4 : ℝ) < v.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  let H : ℂ → ℂ := fun z => Gamma (z + 1) * dslope f 0 z * (X : ℂ)^z
  have hH : DifferentiableOn ℂ H {v : ℂ | (-3 / 4 : ℝ) < v.re} := gammaZeroShift_regularized_holomorphic X f hX hf
  have hstrip : {z : ℂ | a ≤ z.re ∧ z.re ≤ 2} ⊆ {v : ℂ | (-3 / 4 : ℝ) < v.re} := by
    intro z hz
    dsimp at hz ⊢
    linarith [ha.1]
  have hHs := hH.mono hstrip
  have hHeq (z : ℂ) (hz : z ≠ 0) :
      H z = Gamma z * f z * (X : ℂ)^z := gammaZeroShift_regularized_eq X f hf0 z hz
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image
    (Real.continuous_const_rpow hX.ne').continuousOn
  have hKbound (σ : ℝ) (hσ : σ ∈ Icc a 2) : X ^ σ ≤ K := hK ⟨σ, hσ, rfl⟩
  have hKpos : 0 < K := lt_of_lt_of_le (Real.rpow_pos_of_pos hX a) (hKbound a ⟨le_rfl, hab⟩)
  obtain ⟨m, hm⟩ := exists_nat_gt (B + 2)
  obtain ⟨C, hC, hd⟩ := detector_sz_gamma_decay a 2 hab m
  let D : ℝ := C * M * K * (3 ^ B * 4)
  have hbound : ∀ σ ∈ Icc a 2, ∀ t : ℝ, 1 ≤ |t| →
      ‖H ((σ : ℂ) + (t : ℂ)*I)‖ ≤ D * (1 + |t|) ^ (-2 : ℝ) := by
    intro σ hσ t ht
    have hz : (σ : ℂ) + (t : ℂ)*I ≠ 0 := by
      intro he
      have he' : t = 0 := by simpa using congrArg Complex.im he
      norm_num [he'] at ht
    rw [hHeq _ hz, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      zero_mul, sub_self, add_zero]
    calc
      ‖Gamma ((σ : ℂ) + (t : ℂ)*I)‖ * ‖f ((σ : ℂ) + (t : ℂ)*I)‖ * X ^ σ
          ≤ (C * |t| ^ (-(m : ℝ))) * (M * (2 + |t|)^B) * K := by
            apply mul_le_mul (mul_le_mul (hd σ hσ t ht) (hg σ hσ t) (norm_nonneg _)
              (mul_nonneg hC.le (Real.rpow_nonneg (abs_nonneg t) _)))
              (hKbound σ hσ) (Real.rpow_nonneg hX.le σ)
              (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (abs_nonneg t) _))
                (mul_nonneg hM.le (Real.rpow_nonneg (by positivity) _)))
      _ = C * M * K * (|t| ^ (-(m : ℝ)) * (2 + |t|)^B) := by ring
      _ ≤ C * M * K * ((3 ^ B * 4) * (1 + |t|)^(-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (gammaZeroShift_polynomial_tail B hB m hm.le t ht) (by positivity)
      _ = D * (1 + |t|)^(-2 : ℝ) := by dsimp [D]; ring
  have hi : ∀ σ ∈ Icc a 2, Integrable (fun t : ℝ => H ((σ : ℂ) + (t : ℂ)*I)) := by
    intro σ hσ
    apply gammaZeroShift_integrable_tail _ D
    · apply hH.continuousOn.comp_continuous (by fun_prop)
      intro t
      apply hstrip
      simpa using hσ
    · exact hbound σ hσ
  have hia := hi a ⟨le_rfl, hab⟩
  have hi2 := hi 2 ⟨hab, le_rfl⟩
  have heqa (t : ℝ) : H ((a : ℂ) + (t : ℂ)*I) =
      Gamma ((a : ℂ) + (t : ℂ)*I) * f ((a : ℂ) + (t : ℂ)*I) * (X : ℂ)^((a : ℂ) + (t : ℂ)*I) := by
    apply hHeq
    intro he
    have he' : a = 0 := by simpa using congrArg Complex.re he
    linarith [ha.2]
  have heq2 (t : ℝ) : H ((2 : ℂ) + (t : ℂ)*I) =
      Gamma ((2 : ℂ) + (t : ℂ)*I) * f ((2 : ℂ) + (t : ℂ)*I) * (X : ℂ)^((2 : ℂ) + (t : ℂ)*I) := by
    apply hHeq
    intro he
    have he' := congrArg Complex.re he
    norm_num at he'
  simp only [Complex.ofReal_ofNat] at hi2 heq2
  refine ⟨by simpa only [heqa] using hia, by simpa only [heq2] using hi2, ?_⟩
  have he := gammaZeroShift_rectangle_limits H hab hHs
    (intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id)
    (intervalIntegral_tendsto_integral hi2 tendsto_neg_atTop_atBot tendsto_id)
    (by simpa using gammaZeroShift_horizontal_decay_limit H a 2 D (-1) hab (by norm_num) hbound)
    (by simpa using gammaZeroShift_horizontal_decay_limit H a 2 D 1 hab (by norm_num) hbound)
  simpa only [Complex.ofReal_ofNat, heqa, heq2] using he.symm

end DedekindZetaZeroFree
