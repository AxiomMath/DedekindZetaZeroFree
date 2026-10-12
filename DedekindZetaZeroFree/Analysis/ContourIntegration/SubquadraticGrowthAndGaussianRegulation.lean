module

public import DedekindZetaZeroFree.Analysis.ContourIntegration.SimplePoleResidueSums

@[expose] public section

section

open Filter
open scoped Topology
open MeasureTheory

namespace DedekindZetaZeroFree.LargeSieve.Vendor.Subquadratic

private lemma norm_exp_ofReal_mul_sq_le (ε : ℝ) (hε : 0 ≤ ε) (c t : ℝ) :
    ‖Complex.exp ((ε : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)‖ ≤
      Real.exp (ε * c ^ 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (((c : ℂ) + (t : ℂ) * Complex.I) ^ 2).re = c ^ 2 - t ^ 2 := by
    rw [pow_two, Complex.mul_re]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_I_re, Complex.mul_I_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      zero_add, zero_sub, neg_zero]
    ring
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hre]
  nlinarith [sq_nonneg t]

theorem gaussianRegulator_boundary (f : ℂ → ℂ) (c : ℝ)
    (hc : Complex.VerticalIntegrable f c) :
    (∀ ε : ℝ, 0 ≤ ε → Complex.VerticalIntegrable (gaussianRegulator f ε) c) ∧
    Tendsto (fun ε : ℝ => verticalIntegral c (gaussianRegulator f ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (verticalIntegral c f)) := by
  have hc' : Integrable (fun t : ℝ => f ((c : ℂ) + (t : ℂ) * Complex.I)) := hc
  have hbase : Integrable
      (fun t : ℝ => Real.exp (c ^ 2) * ‖f ((c : ℂ) + (t : ℂ) * Complex.I)‖) :=
    hc'.norm.const_mul _
  refine ⟨?_, ?_⟩
  · intro ε hε
    show Integrable (fun t : ℝ => gaussianRegulator f ε ((c : ℂ) + (t : ℂ) * Complex.I))
    have hfun : (fun t : ℝ => gaussianRegulator f ε ((c : ℂ) + (t : ℂ) * Complex.I)) =
        fun t : ℝ => f ((c : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((ε : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2) := by
      ext t; simp only [gaussianRegulator]
    rw [hfun]
    exact hc'.mul_bdd (c := Real.exp (ε * c ^ 2))
      ((Complex.continuous_exp.comp
        (by fun_prop : Continuous fun t : ℝ =>
          (ε : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)).aestronglyMeasurable)
      (Eventually.of_forall (fun t => norm_exp_ofReal_mul_sq_le ε hε c t))
  · have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (0 : ℝ) < ε := self_mem_nhdsWithin
    have hle1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 :=
      nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
    have hconv : Tendsto
        (fun ε : ℝ => ∫ t : ℝ, gaussianRegulator f ε ((c : ℂ) + (t : ℂ) * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 (∫ t : ℝ, f ((c : ℂ) + (t : ℂ) * Complex.I))) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (fun t : ℝ => Real.exp (c ^ 2) * ‖f ((c : ℂ) + (t : ℂ) * Complex.I)‖) ?_ ?_ hbase ?_
      · filter_upwards with ε
        have hfun : (fun t : ℝ => gaussianRegulator f ε ((c : ℂ) + (t : ℂ) * Complex.I)) =
            fun t : ℝ => f ((c : ℂ) + (t : ℂ) * Complex.I) *
              Complex.exp ((ε : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2) := by
          ext t; simp only [gaussianRegulator]
        rw [hfun]
        exact hc'.aestronglyMeasurable.mul (Complex.continuous_exp.comp
          (by fun_prop : Continuous fun t : ℝ =>
            (ε : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)).aestronglyMeasurable
      · filter_upwards [hpos, hle1] with ε hε hε1
        filter_upwards with t
        simp only [gaussianRegulator, norm_mul]
        calc ‖f ((c : ℂ) + (t : ℂ) * Complex.I)‖ *
              ‖Complex.exp ((ε : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)‖
            ≤ ‖f ((c : ℂ) + (t : ℂ) * Complex.I)‖ * Real.exp (ε * c ^ 2) :=
              mul_le_mul_of_nonneg_left (norm_exp_ofReal_mul_sq_le ε (le_of_lt hε) c t)
                (norm_nonneg _)
          _ ≤ Real.exp (c ^ 2) * ‖f ((c : ℂ) + (t : ℂ) * Complex.I)‖ := by
              have h1 : Real.exp (ε * c ^ 2) ≤ Real.exp (c ^ 2) :=
                Real.exp_le_exp.mpr (by nlinarith [sq_nonneg c])
              calc ‖f ((c : ℂ) + (t : ℂ) * Complex.I)‖ * Real.exp (ε * c ^ 2)
                  ≤ ‖f ((c : ℂ) + (t : ℂ) * Complex.I)‖ * Real.exp (c ^ 2) :=
                    mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
                _ = Real.exp (c ^ 2) * ‖f ((c : ℂ) + (t : ℂ) * Complex.I)‖ := by ring
      · refine Eventually.of_forall (fun t => ?_)
        have hz : Tendsto (fun ε : ℝ => (ε : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have hε0 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
            (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
          simpa using hε0.mul_const (((c : ℂ) + (t : ℂ) * Complex.I) ^ 2)
        have hexp : Tendsto
            (fun ε : ℝ => Complex.exp ((ε : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2))
            (𝓝[>] (0 : ℝ)) (𝓝 1) := by
          have h := (Complex.continuous_exp.tendsto (0 : ℂ)).comp hz
          simpa [Function.comp_def, Complex.exp_zero] using h
        have hfun : (fun ε : ℝ => gaussianRegulator f ε ((c : ℂ) + (t : ℂ) * Complex.I)) =
            fun ε : ℝ => f ((c : ℂ) + (t : ℂ) * Complex.I) *
              Complex.exp ((ε : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I) ^ 2) := by
          ext ε; simp only [gaussianRegulator]
        rw [hfun]
        simpa using tendsto_const_nhds.mul hexp
    exact hconv.const_mul (1 / (2 * Real.pi) : ℂ)

end DedekindZetaZeroFree.LargeSieve.Vendor.Subquadratic

end

section

namespace DedekindZetaZeroFree.LargeSieve.Vendor.Subquadratic

private theorem rpow_three_quarters_le (a : ℝ) (ha : 0 ≤ a) :
    a ^ (3 / 4 : ℝ) ≤ 3 / 4 * a + 1 / 4 := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := (3 / 4 : ℝ)) (w₂ := (1 / 4 : ℝ))
    (p₁ := a) (p₂ := 1) (by norm_num) (by norm_num) ha (by norm_num) (by norm_num)
  simpa using h

private theorem rpow_three_halves_le_weighted (d u : ℝ) (hd : 0 < d) (hu : 0 ≤ u) :
    u ^ (3 / 2 : ℝ) ≤ 3 / 4 * d * u ^ 2 + 1 / (4 * d ^ 3) := by
  have hd4 : 0 ≤ d ^ 4 := by positivity
  have hu2 : 0 ≤ u ^ 2 := by positivity
  have hgm : (d ^ 4 * u ^ 2) ^ (3 / 4 : ℝ) ≤ 3 / 4 * (d ^ 4 * u ^ 2) + 1 / 4 :=
    rpow_three_quarters_le _ (by positivity)
  have hd3 : 0 < d ^ 3 := pow_pos hd 3
  have hval : (d ^ 4 * u ^ 2) ^ (3 / 4 : ℝ) = d ^ 3 * u ^ (3 / 2 : ℝ) := by
    rw [Real.mul_rpow hd4 hu2]
    have h1 : (d ^ 4) ^ (3 / 4 : ℝ) = d ^ 3 := by
      rw [← Real.rpow_natCast_mul (le_of_lt hd) 4 (3 / 4 : ℝ),
        show ((4 : ℕ) : ℝ) * (3 / 4 : ℝ) = 3 by norm_num]
      exact Real.rpow_natCast d 3
    have h2 : (u ^ 2) ^ (3 / 4 : ℝ) = u ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast_mul hu 2 (3 / 4 : ℝ),
        show ((2 : ℕ) : ℝ) * (3 / 4 : ℝ) = 3 / 2 by norm_num]
    rw [h1, h2]
  rw [hval] at hgm
  have h1 : u ^ (3 / 2 : ℝ) ≤ (3 / 4 * (d ^ 4 * u ^ 2) + 1 / 4) / d ^ 3 := by
    rw [le_div_iff₀ hd3]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hgm
  refine h1.trans (le_of_eq ?_)
  field_simp

private theorem one_add_rpow_le_quadratic (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u → (1 + u) ^ (3 / 2 : ℝ) ≤ c * u ^ 2 + K := by
  have h2pos : (0 : ℝ) < 2 ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  set d : ℝ := 4 / 3 * (c / 2 ^ (3 / 2 : ℝ)) with hddef
  have hdpos : 0 < d := by
    rw [hddef]; positivity
  have hcd : 2 ^ (3 / 2 : ℝ) * (3 / 4) * d = c := by
    rw [hddef]
    field_simp
  refine ⟨2 ^ (3 / 2 : ℝ) + 2 ^ (3 / 2 : ℝ) / (4 * d ^ 3), by positivity, ?_⟩
  intro u hu
  rcases le_or_gt u 1 with h | h
  · have h1u : (1 + u) ^ (3 / 2 : ℝ) ≤ 2 ^ (3 / 2 : ℝ) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      linarith
    have hcu : (0 : ℝ) ≤ c * u ^ 2 := by positivity
    have hk : (0 : ℝ) ≤ 2 ^ (3 / 2 : ℝ) / (4 * d ^ 3) := by positivity
    linarith
  · have h1u : (1 + u) ^ (3 / 2 : ℝ) ≤ (2 * u) ^ (3 / 2 : ℝ) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      linarith
    have hmul : (2 * u) ^ (3 / 2 : ℝ) = 2 ^ (3 / 2 : ℝ) * u ^ (3 / 2 : ℝ) :=
      Real.mul_rpow (by norm_num) hu
    rw [hmul] at h1u
    have hkey := rpow_three_halves_le_weighted d u hdpos hu
    have hmul2 := mul_le_mul_of_nonneg_left hkey (le_of_lt h2pos)
    have hexp : 2 ^ (3 / 2 : ℝ) * (3 / 4 * d * u ^ 2 + 1 / (4 * d ^ 3))
        = c * u ^ 2 + 2 ^ (3 / 2 : ℝ) / (4 * d ^ 3) := by
      rw [← hcd]
      ring
    rw [hexp] at hmul2
    have hk : 2 ^ (3 / 2 : ℝ) / (4 * d ^ 3)
        ≤ 2 ^ (3 / 2 : ℝ) + 2 ^ (3 / 2 : ℝ) / (4 * d ^ 3) := by
      have : (0 : ℝ) ≤ 2 ^ (3 / 2 : ℝ) := le_of_lt h2pos
      linarith
    linarith

theorem subquadratic_quadratic_absorption (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u →
      A * (1 + u) ^ (3 / 2 : ℝ) ≤ ε / 2 * u ^ 2 + K := by
  rcases hA.eq_or_lt with h0 | hpos
  · refine ⟨0, le_refl 0, ?_⟩
    intro u _
    rw [← h0, zero_mul, add_zero]
    positivity
  · obtain ⟨K, hK0, hK⟩ := one_add_rpow_le_quadratic (ε / (2 * A)) (by positivity)
    refine ⟨A * K, by positivity, ?_⟩
    intro u hu
    have h := mul_le_mul_of_nonneg_left (hK u hu) hA
    have heq : A * (ε / (2 * A) * u ^ 2 + K) = ε / 2 * u ^ 2 + A * K := by
      field_simp
    rw [heq] at h
    exact h

end DedekindZetaZeroFree.LargeSieve.Vendor.Subquadratic

end

section

open scoped Classical

namespace DedekindZetaZeroFree.LargeSieve.Vendor.Subquadratic

theorem gaussianRegulator_regular_part (n : ℕ) (p : Fin n → ℝ) (R : Fin n → ℂ)
    (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hregular : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      ∀ s ∈ U, (∀ j, s ≠ (p j : ℂ)) →
        g s = f s - ∑ j : Fin n, R j / (s - (p j : ℂ)))
    (ε : ℝ) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      ∀ s ∈ U, (∀ j, s ≠ (p j : ℂ)) →
        g s = gaussianRegulator f ε s -
          ∑ j : Fin n, (R j * Complex.exp ((ε : ℂ) * (p j : ℂ) ^ 2)) /
            (s - (p j : ℂ)) := by
  obtain ⟨g₀, hg₀_diff, hg₀_eq⟩ := hregular
  set Fz : ℂ → ℂ := fun z => Complex.exp ((ε : ℂ) * z ^ 2) with hFz
  have hF : Differentiable ℂ Fz := by
    rw [hFz]
    exact Complex.differentiable_exp.comp ((differentiable_id.pow 2).const_mul (ε : ℂ))
  refine ⟨fun s => Complex.exp ((ε : ℂ) * s ^ 2) * g₀ s +
      ∑ j : Fin n, R j * dslope Fz (p j : ℂ) s, ?_, ?_⟩
  · apply DifferentiableOn.add
    · exact (hF.differentiableOn).mul hg₀_diff
    · have h := DifferentiableOn.sum (u := Finset.univ)
        (A := fun j : Fin n => fun s : ℂ => R j * dslope Fz (p j : ℂ) s)
        (fun j _ => by
          have hd : DifferentiableOn ℂ (dslope Fz (p j : ℂ)) U :=
            ((Complex.differentiableOn_dslope (s := Set.univ) (c := (p j : ℂ))
              (by simp)).mpr hF.differentiableOn).mono (Set.subset_univ _)
          exact hd.const_mul (R j))
      simpa only [Finset.sum_fn] using h
  · intro s hs hne
    have hφ : ∀ j : Fin n, dslope Fz (p j : ℂ) s =
        (Complex.exp ((ε : ℂ) * s ^ 2) - Complex.exp ((ε : ℂ) * (p j : ℂ) ^ 2)) /
          (s - (p j : ℂ)) := by
      intro j
      rw [dslope_of_ne Fz (hne j), slope_def_field]
    have hterm : ∀ j : Fin n,
        Complex.exp ((ε : ℂ) * s ^ 2) * (R j / (s - (p j : ℂ))) -
            R j * dslope Fz (p j : ℂ) s =
          R j * Complex.exp ((ε : ℂ) * (p j : ℂ) ^ 2) / (s - (p j : ℂ)) := by
      intro j
      rw [hφ j]
      field_simp
      ring
    have hsum2 : -(∑ j : Fin n, Complex.exp ((ε : ℂ) * s ^ 2) * (R j / (s - (p j : ℂ)))) +
          (∑ j : Fin n, R j * dslope Fz (p j : ℂ) s) =
        -(∑ j : Fin n, R j * Complex.exp ((ε : ℂ) * (p j : ℂ) ^ 2) / (s - (p j : ℂ))) := by
      have e1 : -(∑ j : Fin n, Complex.exp ((ε : ℂ) * s ^ 2) * (R j / (s - (p j : ℂ)))) +
            (∑ j : Fin n, R j * dslope Fz (p j : ℂ) s) =
          ∑ j : Fin n, (-(Complex.exp ((ε : ℂ) * s ^ 2) * (R j / (s - (p j : ℂ)))) +
            R j * dslope Fz (p j : ℂ) s) := by
        rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      have e2 : (∑ j : Fin n, (-(Complex.exp ((ε : ℂ) * s ^ 2) * (R j / (s - (p j : ℂ)))) +
            R j * dslope Fz (p j : ℂ) s)) =
          ∑ j : Fin n, -(R j * Complex.exp ((ε : ℂ) * (p j : ℂ) ^ 2) / (s - (p j : ℂ))) :=
        Finset.sum_congr rfl (fun j _ => by rw [← hterm j]; ring)
      rw [e1, e2, Finset.sum_neg_distrib]
    have h1 : Complex.exp ((ε : ℂ) * s ^ 2) * g₀ s =
        f s * Complex.exp ((ε : ℂ) * s ^ 2) -
          ∑ j : Fin n, Complex.exp ((ε : ℂ) * s ^ 2) * (R j / (s - (p j : ℂ))) := by
      rw [hg₀_eq s hs hne, mul_sub, Finset.mul_sum]
      ring
    calc Complex.exp ((ε : ℂ) * s ^ 2) * g₀ s +
            ∑ j : Fin n, R j * dslope Fz (p j : ℂ) s
        = (f s * Complex.exp ((ε : ℂ) * s ^ 2) -
              ∑ j : Fin n, Complex.exp ((ε : ℂ) * s ^ 2) * (R j / (s - (p j : ℂ)))) +
            ∑ j : Fin n, R j * dslope Fz (p j : ℂ) s := by rw [h1]
      _ = f s * Complex.exp ((ε : ℂ) * s ^ 2) +
            (-(∑ j : Fin n, Complex.exp ((ε : ℂ) * s ^ 2) * (R j / (s - (p j : ℂ)))) +
              ∑ j : Fin n, R j * dslope Fz (p j : ℂ) s) := by ring
      _ = f s * Complex.exp ((ε : ℂ) * s ^ 2) +
            -(∑ j : Fin n, R j * Complex.exp ((ε : ℂ) * (p j : ℂ) ^ 2) /
              (s - (p j : ℂ))) := by rw [hsum2]
      _ = gaussianRegulator f ε s -
            ∑ j : Fin n, R j * Complex.exp ((ε : ℂ) * (p j : ℂ) ^ 2) /
              (s - (p j : ℂ)) := by
          rw [gaussianRegulator]; ring

end DedekindZetaZeroFree.LargeSieve.Vendor.Subquadratic

end

section

namespace DedekindZetaZeroFree.LargeSieve.Vendor.Subquadratic

theorem gaussianRegulator_bounded_tails {a b : ℝ} (f : ℂ → ℂ)
    (hgrowth : ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ (σ t : ℝ), σ ∈ Set.Icc a b → 1 ≤ |t| →
        ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * Real.exp (A * (1 + |t|) ^ (3 / 2 : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (σ t : ℝ), σ ∈ Set.Icc a b → 1 ≤ |t| →
      ‖gaussianRegulator f ε ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B := by
  obtain ⟨C, A, hC, hA, hf⟩ := hgrowth
  obtain ⟨K, hK, hAbs⟩ := subquadratic_quadratic_absorption A ε hA hε
  set M := max (a ^ 2) (b ^ 2) with hM
  have hre : ∀ σ t : ℝ,
      (((ε : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ 2)).re = ε * (σ ^ 2 - t ^ 2) := by
    intro σ t
    simp [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, sq]
  have hσM : ∀ σ : ℝ, σ ∈ Set.Icc a b → σ ^ 2 ≤ M := by
    intro σ hσ
    rw [hM]
    have h1 := hσ.1
    have h2 := hσ.2
    rcases le_total 0 σ with h | h
    · have hb : 0 ≤ b := le_trans h h2
      nlinarith [sq_nonneg a, sq_nonneg b, le_max_right (a ^ 2) (b ^ 2), hb, h, h2]
    · have ha : a ≤ 0 := le_trans h1 h
      nlinarith [sq_nonneg a, sq_nonneg b, le_max_left (a ^ 2) (b ^ 2), ha, h1, h]
  refine ⟨C * Real.exp (ε * M + K), by positivity, ?_⟩
  intro σ t hσ ht
  have hfbound := hf σ t hσ ht
  have habs := hAbs |t| (abs_nonneg t)
  have ht2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have hσ2 := hσM σ hσ
  have hexpσ : Real.exp (ε * (σ ^ 2 - t ^ 2)) ≤ Real.exp (ε * M - ε * t ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hε, hσ2]
  calc ‖gaussianRegulator f ε ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
          ‖Complex.exp ((ε : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ 2)‖ := by
        rw [gaussianRegulator, norm_mul]
    _ = ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * Real.exp (ε * (σ ^ 2 - t ^ 2)) := by
        rw [Complex.norm_exp, hre]
    _ ≤ (C * Real.exp (A * (1 + |t|) ^ (3 / 2 : ℝ))) * Real.exp (ε * M - ε * t ^ 2) :=
        mul_le_mul hfbound hexpσ (Real.exp_nonneg _) (by positivity)
    _ = C * Real.exp (ε * M + (A * (1 + |t|) ^ (3 / 2 : ℝ) - ε * t ^ 2)) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ C * Real.exp (ε * M + K) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Real.exp_le_exp.mpr
        have h := habs
        rw [sq_abs t] at h
        have hpos : 0 ≤ ε / 2 * t ^ 2 := by positivity
        nlinarith [h, hpos]

end DedekindZetaZeroFree.LargeSieve.Vendor.Subquadratic

end

section

open scoped NumberField Classical Topology
open Filter

namespace DedekindZetaZeroFree.LargeSieve.Vendor

open Subquadratic

private lemma gaussianRegulator_differentiableAt (f : ℂ → ℂ) (ε : ℝ) (s : ℂ)
    (hf : DifferentiableAt ℂ f s) : DifferentiableAt ℂ (gaussianRegulator f ε) s := by
  unfold gaussianRegulator
  exact hf.mul (by fun_prop)

theorem integral_eq_of_subquadratic_strip_growth {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ)
    (hf : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ f s)
    (ha : Complex.VerticalIntegrable f a)
    (hb : Complex.VerticalIntegrable f b)
    (hgrowth : ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ (σ t : ℝ), σ ∈ Set.Icc a b → 1 ≤ |t| →
        ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * Real.exp (A * (1 + |t|) ^ (3 / 2 : ℝ))) :
    verticalIntegral a f = verticalIntegral b f := by
  obtain ⟨hIntA, hlimA⟩ := gaussianRegulator_boundary f a ha
  obtain ⟨hIntB, hlimB⟩ := gaussianRegulator_boundary f b hb
  have hshift : ∀ ε : ℝ, 0 < ε →
      verticalIntegral a (gaussianRegulator f ε) =
        verticalIntegral b (gaussianRegulator f ε) := by
    intro ε hε
    have hdiff : ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        DifferentiableAt ℂ (gaussianRegulator f ε) s := by
      intro s hsa hsb
      exact gaussianRegulator_differentiableAt f ε s (hf s hsa hsb)
    have hcont : ContinuousOn (gaussianRegulator f ε)
        {s : ℂ | s.re ∈ Set.Icc a b} := by
      intro s hs
      exact (hdiff s hs.1 hs.2).continuousAt.continuousWithinAt
    obtain ⟨B, hB, hbound⟩ := strip_bound_of_tail_bound (gaussianRegulator f ε) hcont
      (gaussianRegulator_bounded_tails f hgrowth ε hε)
    apply integral_eq_of_exponential_strip_growth hab (gaussianRegulator f ε)
      hdiff (hIntA ε hε.le) (hIntB ε hε.le)
    refine ⟨0, B, le_rfl, hB, ?_⟩
    intro σ hσ t
    simpa using hbound σ t hσ
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      verticalIntegral a (gaussianRegulator f ε) =
        verticalIntegral b (gaussianRegulator f ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hshift ε hε
  exact tendsto_nhds_unique hlimA (hlimB.congr' (hev.mono fun ε h => h.symm))

theorem verticalIntegral_sub_eq_sum_residues_of_subquadratic_strip_growth
    {a b : ℝ} (hab : a < b) (n : ℕ) (p : Fin n → ℝ) (R : Fin n → ℂ)
    (hp_distinct : Function.Injective p) (hp_strip : ∀ j, p j ∈ Set.Ioo a b)
    (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hstrip : {s : ℂ | s.re ∈ Set.Icc a b} ⊆ U)
    (hf_holo : DifferentiableOn ℂ f (U \ Set.range (fun j => (p j : ℂ))))
    (hregular : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      ∀ s ∈ U, (∀ j, s ≠ (p j : ℂ)) →
        g s = f s - ∑ j : Fin n, R j / (s - (p j : ℂ)))
    (ha : Complex.VerticalIntegrable f a) (hb : Complex.VerticalIntegrable f b)
    (hgrowth : ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ (σ t : ℝ), σ ∈ Set.Icc a b → 1 ≤ |t| →
        ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * Real.exp (A * (1 + |t|) ^ (3 / 2 : ℝ))) :
    verticalIntegral b f - verticalIntegral a f = ∑ j : Fin n, R j := by
  obtain ⟨hIntA, hlimA⟩ := gaussianRegulator_boundary f a ha
  obtain ⟨hIntB, hlimB⟩ := gaussianRegulator_boundary f b hb
  have hshift : ∀ ε : ℝ, 0 < ε →
      verticalIntegral b (gaussianRegulator f ε) -
        verticalIntegral a (gaussianRegulator f ε) =
          ∑ j : Fin n, R j * Complex.exp ((ε : ℂ) * (p j : ℂ) ^ 2) := by
    intro ε hε
    have hdiff : DifferentiableOn ℂ (gaussianRegulator f ε)
        (U \ Set.range (fun j => (p j : ℂ))) := by
      unfold gaussianRegulator
      exact hf_holo.mul (by fun_prop)
    obtain ⟨B, hB, hbound⟩ := gaussianRegulator_bounded_tails f hgrowth ε hε
    apply verticalIntegral_sub_eq_sum_residues hab n p
      (fun j => R j * Complex.exp ((ε : ℂ) * (p j : ℂ) ^ 2))
      hp_distinct hp_strip (gaussianRegulator f ε) U hU hstrip hdiff
      (gaussianRegulator_regular_part n p R f U hU hregular ε)
      (hIntA ε hε.le) (hIntB ε hε.le)
    refine ⟨B, 0, hB, ?_⟩
    intro σ t hσ ht
    simpa using hbound σ t hσ ht
  have hres : Tendsto
      (fun ε : ℝ => ∑ j : Fin n, R j * Complex.exp ((ε : ℂ) * (p j : ℂ) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (∑ j : Fin n, R j)) := by
    have hc : ContinuousAt
        (fun ε : ℝ => ∑ j : Fin n, R j * Complex.exp ((ε : ℂ) * (p j : ℂ) ^ 2)) 0 := by
      fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      verticalIntegral b (gaussianRegulator f ε) -
        verticalIntegral a (gaussianRegulator f ε) =
          ∑ j : Fin n, R j * Complex.exp ((ε : ℂ) * (p j : ℂ) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hshift ε hε
  exact tendsto_nhds_unique (hlimB.sub hlimA)
    (hres.congr' (hev.mono fun ε h => h.symm))

end DedekindZetaZeroFree.LargeSieve.Vendor

end
