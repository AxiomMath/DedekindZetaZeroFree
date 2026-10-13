module

public import DedekindZetaZeroFree.Analysis.VerticalContourShift

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.SimplePoleVerticalShift

noncomputable section

open DedekindZetaZeroFree MeasureTheory Set Filter Complex
open scoped Topology

theorem verticalIntegral_sub_eq_residue
    {a b : ℝ} {p : ℂ} {f : ℂ → ℂ} {res : ℂ}
    (hap : a < p.re) (hpb : p.re < b)
    (hf : DifferentiableOn ℂ f (comparisonClosedStrip a b \ {p}))
    (hres : Tendsto (fun z : ℂ => (z - p) * f z) (𝓝[≠] p) (𝓝 res))
    (ha : Integrable (fun t : ℝ => f ((a : ℂ) + (t : ℂ) * I)))
    (hb : Integrable (fun t : ℝ => f ((b : ℂ) + (t : ℂ) * I)))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
      atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, f ((x : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0)) :
    comparisonVerticalIntegral b f - comparisonVerticalIntegral a f = res := by
  set c : ℝ := p.im with hc
  set q : ℝ := p.re with hq
  set g : ℂ → ℂ := fun z => f (z + (c : ℂ) * I) with hg
  have hpq : p = (q : ℂ) + (c : ℂ) * I := by
    apply Complex.ext <;> simp [hq, hc]
  have hcomp : ∀ σ : ℝ, (fun t : ℝ => g ((σ : ℂ) + (t : ℂ) * I)) =
      fun t : ℝ => f ((σ : ℂ) + ((t + c : ℝ) : ℂ) * I) := by
    intro σ; funext t; simp only [hg]; congr 1; push_cast; ring
  have hV : ∀ σ : ℝ, comparisonVerticalIntegral σ g = comparisonVerticalIntegral σ f := by
    intro σ
    unfold comparisonVerticalIntegral
    rw [hcomp σ]
    congr 1
    exact integral_add_right_eq_self (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * I)) c
  have hgint : ∀ σ : ℝ, Integrable (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * I)) →
      Integrable (fun t : ℝ => g ((σ : ℂ) + (t : ℂ) * I)) := by
    intro σ h
    rw [hcomp σ]
    exact h.comp_add_right c

  have hstrip : ∀ z : ℂ, z ∈ comparisonClosedStrip a b ↔ z + (c : ℂ) * I ∈ comparisonClosedStrip a b := by
    intro z; simp [comparisonClosedStrip]
  have hgd : DifferentiableOn ℂ g (comparisonClosedStrip a b \ {(q : ℂ)}) := by
    have hd : DifferentiableOn ℂ (fun z : ℂ => z + (c : ℂ) * I) (comparisonClosedStrip a b \ {(q : ℂ)}) :=
      (differentiable_id.add_const _).differentiableOn
    refine hf.comp hd ?_
    intro z hz
    refine ⟨(hstrip z).1 hz.1, ?_⟩
    intro h
    apply hz.2
    have : z + (c : ℂ) * I = p := h
    rw [hpq] at this
    have := add_right_cancel this
    simpa using this
  have hgres : Tendsto (fun z : ℂ => (z - (q : ℂ)) * g z) (𝓝[≠] (q : ℂ)) (𝓝 res) := by
    have ht : Tendsto (fun z : ℂ => z + (c : ℂ) * I) (𝓝[≠] (q : ℂ)) (𝓝[≠] p) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have : Tendsto (fun z : ℂ => z + (c : ℂ) * I) (𝓝 (q : ℂ)) (𝓝 p) := by
          rw [hpq]
          exact Continuous.tendsto (f := fun z : ℂ => z + (c : ℂ) * I) (by fun_prop) (q : ℂ)
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz h
        apply hz
        rw [hpq] at h
        simpa using add_right_cancel h
    refine (hres.comp ht).congr' ?_
    filter_upwards with z
    simp only [Function.comp, hg]
    congr 1
    rw [hpq]; ring

  set A : ℂ → ℂ := Function.update (fun z => (z - (q : ℂ)) * g z) (q : ℂ) res with hA
  have hnb : comparisonClosedStrip a b ∈ 𝓝 (q : ℂ) := by
    apply Filter.mem_of_superset
      (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
        (show a < (q : ℂ).re ∧ (q : ℂ).re < b from ⟨hap, hpb⟩))
    intro z hz
    exact ⟨hz.1.le, hz.2.le⟩
  have hAd : DifferentiableOn ℂ A (comparisonClosedStrip a b) := by
    rw [← differentiableOn_compl_singleton_and_continuousAt_iff hnb]
    constructor
    · have : DifferentiableOn ℂ (fun z => (z - (q : ℂ)) * g z) (comparisonClosedStrip a b \ {(q : ℂ)}) :=
        (differentiableOn_id.sub_const _).mul hgd
      refine this.congr ?_
      intro z hz
      simp only [hA]
      rw [Function.update_of_ne (by simpa using hz.2)]
    · exact continuousAt_update_same.mpr hgres
  have hF : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ (q : ℂ) → g z = A z / (z - (q : ℂ)) := by
    intro z _ _ hz
    simp only [hA]
    rw [Function.update_of_ne hz]
    have : z - (q : ℂ) ≠ 0 := sub_ne_zero.mpr hz
    field_simp
  have hbot' : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, g ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
    have h := hbot.comp (tendsto_atTop_add_const_right atTop (-c) tendsto_id)
    refine h.congr ?_
    intro T
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hg, Function.comp_apply, id]
    apply congrArg f
    push_cast
    ring
  have htop' : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, g ((x : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
    have h := htop.comp (tendsto_atTop_add_const_right atTop c tendsto_id)
    refine h.congr ?_
    intro T
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hg, Function.comp_apply, id]
    apply congrArg f
    push_cast
    ring
  have key := ComparisonShiftProof.simple_pole_of_boundary_control A g hap hpb hAd hF
    (hgint a ha) (hgint b hb) (by simpa using hbot') htop'
  have hAp : A (q : ℂ) = res := by simp [hA]
  rw [hAp, hV, hV] at key
  rw [key]; ring

theorem integrable_of_decay (g : ℝ → ℂ) (C T : ℝ) (hT : 1 ≤ T) (hg : Continuous g)
    (hbound : ∀ t : ℝ, T ≤ |t| → ‖g t‖ ≤ C * (1 + |t|) ^ (-2 : ℝ)) :
    Integrable g := by
  have hi : Integrable (fun t : ℝ => C * (1 + |t|) ^ (-2 : ℝ)) := by
    simpa [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (r := 2) (μ := volume) (by simp)).const_mul C
  have hc : IntegrableOn g (Icc (-T) T) := hg.integrableOn_Icc
  have ht : IntegrableOn g (Icc (-T) T)ᶜ := by
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

theorem horizontal_tendsto_zero_of_decay (f : ℂ → ℂ) (a b C T0 ε : ℝ) (hab : a ≤ b)
    (hε : |ε| = 1)
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ, T0 ≤ |y| →
      ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ C * (1 + |y|) ^ (-2 : ℝ)) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, f ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
  have hr : Tendsto (fun T : ℝ => (1 + T) ^ (-2 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  have hlim : Tendsto (fun T : ℝ => C * (1 + T) ^ (-2 : ℝ) * |b - a|) atTop (𝓝 0) := by
    simpa using (hr.const_mul C).mul_const |b - a|
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (max T0 1)] with T hT
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : T0 ≤ T := le_trans (le_max_left _ _) hT
  have he : |ε * T| = T := by rw [abs_mul, hε, one_mul, abs_of_nonneg (by linarith)]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hx' : x ∈ Icc a b := by
    rw [← uIcc_of_le hab]; exact uIoc_subset_uIcc hx
  have hh := hbound x hx' (ε * T) (by rw [he]; exact hT0)
  rw [he] at hh
  exact hh

theorem integrable_vertical_of_decay (f : ℂ → ℂ) (σ C T0 : ℝ)
    (hcont : Continuous fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * I))
    (hbound : ∀ y : ℝ, T0 ≤ |y| →
      ‖f ((σ : ℂ) + (y : ℂ) * I)‖ ≤ C * (1 + |y| : ℝ) ^ (-2 : ℝ)) :
    Integrable (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * I)) :=
  integrable_of_decay _ C (max T0 1) (le_max_right _ _) hcont
    (fun t ht => hbound t (le_trans (le_max_left _ _) ht))

theorem verticalIntegral_sub_eq_residue_of_decay
    {a b : ℝ} {p : ℂ} {f : ℂ → ℂ} {res : ℂ}
    (hap : a < p.re) (hpb : p.re < b)
    (hf : DifferentiableOn ℂ f (comparisonClosedStrip a b \ {p}))
    (hres : Tendsto (fun z : ℂ => (z - p) * f z) (𝓝[≠] p) (𝓝 res))
    (C T0 : ℝ)
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ, T0 ≤ |y| →
      ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ C * (1 + |y|) ^ (-2 : ℝ)) :
    comparisonVerticalIntegral b f - comparisonVerticalIntegral a f = res := by
  have hab : a ≤ b := (hap.trans hpb).le
  have hline : ∀ σ : ℝ, σ ∈ Icc a b → σ ≠ p.re →
      Integrable (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * I)) := by
    intro σ hσ hne
    apply integrable_vertical_of_decay f σ C T0
    · refine hf.continuousOn.comp_continuous (by fun_prop) ?_
      intro t
      refine ⟨by simpa [comparisonClosedStrip] using hσ, ?_⟩
      intro h
      have := congrArg Complex.re h
      simp at this
      exact hne this
    · intro y hy
      exact hbound σ hσ y hy
  refine verticalIntegral_sub_eq_residue hap hpb hf hres
    (hline a ⟨le_rfl, hab⟩ hap.ne) (hline b ⟨hab, le_rfl⟩ hpb.ne') ?_ ?_
  · simpa using horizontal_tendsto_zero_of_decay f a b C T0 (-1) hab (by norm_num) hbound
  · simpa using horizontal_tendsto_zero_of_decay f a b C T0 1 hab (by norm_num) hbound

end

end DedekindZetaZeroFree.Quantitative.SimplePoleVerticalShift
