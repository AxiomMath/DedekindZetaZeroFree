module

public import DedekindZetaZeroFree.Moments.Comparison.FiniteRowContourDecay

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section

def comparisonFrequencyKernel {ι : Type*}
    (q : ι → ℝ) (M W : ℂ → ℂ) (E : ι → ℂ → ℂ → ℂ → ℂ)
    (Z : ℝ) (u : ι) (ξ w z : ℂ) : ℂ :=
  comparisonRealPower Z
      ((comparisonA : ℂ) / 2 + ξ - 1 + (comparisonH₀ : ℂ) * z +
        (comparisonB : ℂ) * (w - 1)) *
    Complex.exp ((ξ + z - 1) ^ 2) * M z * W w *
    comparisonRealPower (q u) (-z) * E u ξ w z

def comparisonFrequencyIntegral {ι : Type*}
    (q : ι → ℝ) (M W : ℂ → ℂ) (E : ι → ℂ → ℂ → ℂ → ℂ)
    (C : Finset ι) (Z σξ σw σz : ℝ) : ℂ :=
  comparisonTripleVerticalIntegral σξ σw σz
    (fun ξ w z => ∑ u ∈ C, comparisonFrequencyKernel q M W E Z u ξ w z)

def comparisonFrequencyDyad {ι : Type*} (q : ι → ℝ) (principal : ι)
    (K U : ℝ) (C : Finset ι) : Prop :=
  (∀ u ∈ C, u ≠ principal ∧ U ≤ q u ∧ q u < 2 * U) ∧ (C.card : ℝ) ≤ K * U

def comparisonFarContourInput {ι : Type*}
    (q : ι → ℝ) (principal : ι) (M W : ℂ → ℂ)
    (E : ι → ℂ → ℂ → ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ M {z : ℂ | 0 < z.re} ∧
  Continuous (fun t : ℝ => W ((4 : ℂ) + (t : ℂ) * Complex.I)) ∧
  (∀ N : ℕ, ∃ A : ℝ, 0 < A ∧
    (∀ z : ℂ, z.re ∈ Set.Icc 2 comparisonR₀ →
      ‖M z‖ ≤ A * (1 + |z.im|) ^ (-(N : ℝ))) ∧
    (∀ t : ℝ, ‖W ((4 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      A * (1 + |t|) ^ (-(N : ℝ)))) ∧
  (∀ u : ι, u ≠ principal →
    ContinuousOn
      (fun p : ℝ × ℝ × ℂ => E u
        ((4 : ℂ) + (p.1 : ℂ) * Complex.I)
        ((4 : ℂ) + (p.2.1 : ℂ) * Complex.I) p.2.2)
      {p : ℝ × ℝ × ℂ | 2 / 5 < p.2.2.re}) ∧
  (∀ (u : ι) (tξ tw : ℝ), u ≠ principal →
    DifferentiableOn ℂ
      (fun z : ℂ => E u ((4 : ℂ) + (tξ : ℂ) * Complex.I)
        ((4 : ℂ) + (tw : ℂ) * Complex.I) z)
      {z : ℂ | 2 / 5 < z.re}) ∧
  (∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
    ∀ (u : ι) (tξ tw : ℝ) (z : ℂ), u ≠ principal → 1 ≤ q u →
      z.re ∈ Set.Icc 2 comparisonR₀ →
      ‖E u ((4 : ℂ) + (tξ : ℂ) * Complex.I)
        ((4 : ℂ) + (tw : ℂ) * Complex.I) z‖ ≤ A * (q u) ^ ε)

private lemma comparisonRealPower_norm (Z : ℝ) (hZ : 0 < Z) (s : ℂ) :
    ‖comparisonRealPower Z s‖ = Z ^ s.re := by
  rw [comparisonRealPower, Complex.norm_exp]
  have : (s * (Real.log Z : ℂ)).re = s.re * Real.log Z := by simp [Complex.mul_re]
  rw [this, Real.rpow_def_of_pos hZ, mul_comm]

private lemma kernel_norm_line_le
    {ι : Type*} (q : ι → ℝ) (M W : ℂ → ℂ) (E : ι → ℂ → ℂ → ℂ → ℂ)
    (Z σ : ℝ) (hZ : 1 ≤ Z) (u : ι) (hq : 1 ≤ q u)
    (p : ℝ × ℝ × ℝ)
    (A₂ : ℝ) (hA₂ : 0 ≤ A₂)
    (hM₂ : ‖M ((σ:ℂ)+(p.2.2:ℂ)*Complex.I)‖ ≤ A₂ * (1 + |p.2.2|) ^ (-2:ℝ))
    (hW₂ : ‖W ((4:ℂ) + (p.2.1:ℂ)*Complex.I)‖ ≤ A₂ * (1 + |p.2.1|) ^ (-2:ℝ))
    (Aε : ℝ) (hAε : 0 ≤ Aε) (ε : ℝ)
    (hEε : ‖E u ((4:ℂ) + (p.1:ℂ)*Complex.I) ((4:ℂ)+(p.2.1:ℂ)*Complex.I) ((σ:ℂ)+(p.2.2:ℂ)*Complex.I)‖ ≤ Aε * (q u)^ε) :
    ‖comparisonFrequencyKernel q M W E Z u ((4:ℂ) + (p.1:ℂ)*Complex.I) ((4:ℂ)+(p.2.1:ℂ)*Complex.I) ((σ:ℂ)+(p.2.2:ℂ)*Complex.I)‖ ≤
      Z ^ comparisonE 4 4 σ * Real.exp ((3+σ)^2) * A₂ * A₂ * Aε *
        (q u) ^ (-σ) * (q u)^ε *
        (Real.exp (-(p.1 + p.2.2)^2) * (1 + |p.2.2|)^(-2:ℝ) * (1 + |p.2.1|)^(-2:ℝ)) := by
  have hZpos : 0 < Z := by linarith
  have hqpos : 0 < q u := by linarith
  set ξ : ℂ := (4:ℂ) + (p.1:ℂ)*Complex.I with hξ
  set w : ℂ := (4:ℂ) + (p.2.1:ℂ)*Complex.I with hw
  set z : ℂ := (σ:ℂ) + (p.2.2:ℂ)*Complex.I with hz
  have h1 : ‖comparisonRealPower Z (comparisonA/2 + ξ - 1 + comparisonH₀*z + comparisonB*(w-1))‖
      ≤ Z ^ comparisonE 4 4 σ := by
    rw [comparisonRealPower_norm Z hZpos]
    have hre : (comparisonA/2 + ξ - 1 + comparisonH₀*z + comparisonB*(w-1)).re
        = comparisonE 4 4 σ := by
      simp only [hξ, hw, hz]
      simp [comparisonE, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im, Complex.I_re, Complex.I_im]
    rw [hre]
  have h2 : ‖Complex.exp ((ξ + z - 1)^2)‖
      ≤ Real.exp ((3+σ)^2) * Real.exp (-(p.1 + p.2.2)^2) := by
    rw [Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp]
    have hre : ((ξ + z - 1)^2).re = (3+σ)^2 - (p.1 + p.2.2)^2 := by
      have hξz : ξ + z - 1 = ((3+σ : ℝ) : ℂ) + ((p.1+p.2.2 : ℝ):ℂ)*Complex.I := by
        simp only [hξ, hw, hz]; push_cast; ring
      rw [hξz]
      simp [pow_two, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im]
    rw [hre]; linarith
  have h3 : ‖M z‖ ≤ A₂ * (1 + |p.2.2|) ^ (-2:ℝ) := by
    simpa only [← hz] using hM₂
  have h4 : ‖W w‖ ≤ A₂ * (1 + |p.2.1|) ^ (-2:ℝ) := by
    simpa only [← hw] using hW₂
  have h5 : ‖comparisonRealPower (q u) (-z)‖ ≤ (q u) ^ (-σ) := by
    rw [comparisonRealPower_norm (q u) hqpos]
    have : (-z).re = -σ := by simp [hz]
    rw [this]
  have h6 : ‖E u ξ w z‖ ≤ Aε * (q u)^ε := by
    simpa only [← hξ, ← hw, ← hz] using hEε
  rw [comparisonFrequencyKernel]
  simp only [norm_mul]
  refine (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _)
    (by positivity)) h3 (norm_nonneg _) (by positivity)) h4 (norm_nonneg _) (by positivity)) h5
    (norm_nonneg _) (by positivity)) h6 (norm_nonneg _) (by positivity)).trans (le_of_eq ?_)
  ring

open MeasureTheory

private lemma kernel_line_continuous {ι : Type*}
    (q : ι → ℝ) (principal : ι) (M W : ℂ → ℂ)
    (E : ι → ℂ → ℂ → ℂ → ℂ)
    (ha : comparisonFarContourInput q principal M W E)
    (Z : ℝ) (u : ι) (hu : u ≠ principal) (σ : ℝ) (hσ : 2 ≤ σ) :
    Continuous (fun p : ℝ × ℝ × ℝ => comparisonFrequencyKernel q M W E Z u
      ((4:ℂ)+p.1*Complex.I) ((4:ℂ)+p.2.1*Complex.I) ((σ:ℂ)+p.2.2*Complex.I)) := by
  have hM : Continuous (fun p : ℝ × ℝ × ℝ => M ((σ:ℂ)+p.2.2*Complex.I)) :=
    ha.1.continuousOn.comp_continuous (by fun_prop) (by intro p; simp; linarith)
  have hW : Continuous (fun p : ℝ × ℝ × ℝ => W ((4:ℂ)+p.2.1*Complex.I)) :=
    ha.2.1.comp (by fun_prop)
  have hE : Continuous (fun p : ℝ × ℝ × ℝ => E u
      ((4:ℂ)+p.1*Complex.I) ((4:ℂ)+p.2.1*Complex.I) ((σ:ℂ)+p.2.2*Complex.I)) :=
    (ha.2.2.2.1 u hu).comp_continuous
      (f := fun p : ℝ × ℝ × ℝ => (p.1, p.2.1, (σ:ℂ)+p.2.2*Complex.I))
      (by fun_prop) (by intro p; simp; linarith)
  unfold comparisonFrequencyKernel comparisonRealPower
  apply Continuous.mul _ hE
  apply Continuous.mul _ (by fun_prop)
  apply Continuous.mul _ hW
  apply Continuous.mul _ hM
  fun_prop

private lemma kernel_holomorphic {ι : Type*}
    (q : ι → ℝ) (principal : ι) (M W : ℂ → ℂ)
    (E : ι → ℂ → ℂ → ℂ → ℂ)
    (ha : comparisonFarContourInput q principal M W E)
    (Z : ℝ) (u : ι) (hu : u ≠ principal) (tξ tw : ℝ) :
    DifferentiableOn ℂ (fun z => comparisonFrequencyKernel q M W E Z u
      ((4:ℂ)+tξ*Complex.I) ((4:ℂ)+tw*Complex.I) z) {z : ℂ | 2/5 < z.re} := by
  have hM := ha.1.mono (show {z : ℂ | 2/5 < z.re} ⊆ {z : ℂ | 0 < z.re} by
    intro z hz; dsimp at *; linarith)
  have hE := ha.2.2.2.2.1 u tξ tw hu
  unfold comparisonFrequencyKernel comparisonRealPower
  fun_prop

private lemma strip_amplitude_le (Z Q σ ε : ℝ) (hZ : 1 ≤ Z) (hQ : 1 ≤ Q)
    (hσ : σ ∈ Set.Icc 2 comparisonR₀) :
    Z ^ comparisonE 4 4 σ * Real.exp ((3+σ)^2) * Q^(-σ) * Q^ε ≤
      Z ^ comparisonE 4 4 comparisonR₀ * Real.exp ((3+comparisonR₀)^2) * Q^ε := by
  have h1 : Z ^ comparisonE 4 4 σ ≤ Z ^ comparisonE 4 4 comparisonR₀ :=
    Real.rpow_le_rpow_of_exponent_le hZ (by dsimp [comparisonE, comparisonH₀]; linarith [hσ.2])
  have h2 : Real.exp ((3+σ)^2) ≤ Real.exp ((3+comparisonR₀)^2) :=
    Real.exp_le_exp.mpr (by dsimp [comparisonR₀] at *; nlinarith [hσ.1,hσ.2])
  have h3 : Q^(-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hQ (by linarith [hσ.1])
  calc
    _ ≤ (Z ^ comparisonE 4 4 comparisonR₀ * Real.exp ((3+comparisonR₀)^2)) * 1 * Q^ε :=
      mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity))
        h3 (by positivity) (by positivity)) (by positivity)
    _ = _ := by ring

private lemma kernel_uniform_line_bound {ι : Type*}
    (q : ι → ℝ) (principal : ι) (M W : ℂ → ℂ)
    (E : ι → ℂ → ℂ → ℂ → ℂ)
    (ha : comparisonFarContourInput q principal M W E)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Z : ℝ) (u : ι) (σ : ℝ) (p : ℝ × ℝ × ℝ),
      1 ≤ Z → u ≠ principal → 1 ≤ q u → σ ∈ Set.Icc 2 comparisonR₀ →
      ‖comparisonFrequencyKernel q M W E Z u
        ((4:ℂ)+p.1*Complex.I) ((4:ℂ)+p.2.1*Complex.I) ((σ:ℂ)+p.2.2*Complex.I)‖ ≤
      B * Z ^ comparisonE 4 4 comparisonR₀ * (q u)^ε *
        comparisonHeightEnvelope 2 p.1 p.2.1 p.2.2 := by
  obtain ⟨A₂, hA₂, hM, hW⟩ := ha.2.2.1 2
  obtain ⟨Aε, hAε, hE⟩ := ha.2.2.2.2.2 ε hε
  refine ⟨Real.exp ((3+comparisonR₀)^2)*A₂*A₂*Aε, by positivity, ?_⟩
  intro Z u σ p hZ hu hq hσ
  have hk := kernel_norm_line_le q M W E Z σ hZ u hq p A₂ hA₂.le
    (by simpa using hM ((σ:ℂ)+p.2.2*Complex.I) (by simpa using hσ))
    (by simpa using hW p.2.1) Aε hAε.le ε
    (hE u p.1 p.2.1 ((σ:ℂ)+p.2.2*Complex.I) hu hq (by simpa using hσ))
  have hamp := strip_amplitude_le Z (q u) σ ε hZ hq hσ
  have hm := mul_le_mul_of_nonneg_right hamp
    (show 0 ≤ A₂*A₂*Aε*comparisonHeightEnvelope 2 p.1 p.2.1 p.2.2 by
      unfold comparisonHeightEnvelope; positivity)
  exact hk.trans (by unfold comparisonHeightEnvelope at hm ⊢; nlinarith [hm])

private lemma kernel_line_integrable {ι : Type*}
    (q : ι → ℝ) (principal : ι) (M W : ℂ → ℂ)
    (E : ι → ℂ → ℂ → ℂ → ℂ)
    (ha : comparisonFarContourInput q principal M W E)
    (Z : ℝ) (hZ : 1 ≤ Z) (u : ι) (hu : u ≠ principal) (hq : 1 ≤ q u)
    (σ : ℝ) (hσ : σ ∈ Set.Icc 2 comparisonR₀) :
    Integrable (fun p : ℝ × ℝ × ℝ => comparisonFrequencyKernel q M W E Z u
      ((4:ℂ)+p.1*Complex.I) ((4:ℂ)+p.2.1*Complex.I) ((σ:ℂ)+p.2.2*Complex.I)) := by
  obtain ⟨B, hB, hb⟩ := kernel_uniform_line_bound q principal M W E ha 1 (by norm_num)
  have he : Integrable (fun p : ℝ × ℝ × ℝ => comparisonHeightEnvelope 2 p.1 p.2.1 p.2.2) := by
    simpa using comparisonHeightEnvelope_integrable 0 (by norm_num)
  exact (he.const_mul (B * Z ^ comparisonE 4 4 comparisonR₀ * (q u)^ (1:ℝ))).mono'
    (kernel_line_continuous q principal M W E ha Z u hu σ hσ.1).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => hb Z u σ p hZ hu hq hσ))

private lemma kernel_vertical_eq {ι : Type*}
    (q : ι → ℝ) (principal : ι) (M W : ℂ → ℂ)
    (E : ι → ℂ → ℂ → ℂ → ℂ)
    (ha : comparisonFarContourInput q principal M W E)
    (Z : ℝ) (hZ : 1 ≤ Z) (u : ι) (hu : u ≠ principal) (hq : 1 ≤ q u)
    (tξ tw : ℝ) :
    (∫ t : ℝ, comparisonFrequencyKernel q M W E Z u
      ((4:ℂ)+tξ*Complex.I) ((4:ℂ)+tw*Complex.I) ((2:ℂ)+t*Complex.I)) =
    ∫ t : ℝ, comparisonFrequencyKernel q M W E Z u
      ((4:ℂ)+tξ*Complex.I) ((4:ℂ)+tw*Complex.I) ((comparisonR₀:ℂ)+t*Complex.I) := by
  obtain ⟨B, hB, hb⟩ := kernel_uniform_line_bound q principal M W E ha 1 (by norm_num)
  apply verticalIntegral_eq_of_strip_decay 2 comparisonR₀
    (B * Z ^ comparisonE 4 4 comparisonR₀ * (q u)^(1:ℝ) * (1+|tw|)^(-2:ℝ))
    _ {z : ℂ | 2/5 < z.re} (by norm_num [comparisonR₀]) (by positivity)
    (isOpen_lt continuous_const Complex.continuous_re)
    (by intro z hz; dsimp [comparisonClosedStrip] at hz ⊢; linarith [hz.1])
    (kernel_holomorphic q principal M W E ha Z u hu tξ tw)
  intro z hz
  have hσ : z.re ∈ Set.Icc 2 comparisonR₀ := hz
  have hh := hb Z u z.re (tξ,tw,z.im) hZ hu hq hσ
  have hz' : (z.re:ℂ)+z.im*Complex.I = z := Complex.re_add_im z
  simp only [hz'] at hh
  have hg : Real.exp (-(tξ+z.im)^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (tξ+z.im)])
  unfold comparisonHeightEnvelope at hh
  calc
    _ ≤ _ := hh
    _ ≤ B * Z ^ comparisonE 4 4 comparisonR₀ * (q u)^(1:ℝ) *
        ((1+|z.im|)^(-2:ℝ) * (1+|tw|)^(-2:ℝ)) := by
      gcongr
      exact mul_le_of_le_one_left (by positivity) hg
    _ = _ := by ring

private lemma kernel_triple_eq {ι : Type*}
    (q : ι → ℝ) (principal : ι) (M W : ℂ → ℂ)
    (E : ι → ℂ → ℂ → ℂ → ℂ)
    (ha : comparisonFarContourInput q principal M W E)
    (Z : ℝ) (hZ : 1 ≤ Z) (u : ι) (hu : u ≠ principal) (hq : 1 ≤ q u) :
    comparisonTripleVerticalIntegral 4 4 2 (comparisonFrequencyKernel q M W E Z u) =
    comparisonTripleVerticalIntegral 4 4 comparisonR₀ (comparisonFrequencyKernel q M W E Z u) := by
  let f := fun (σ : ℝ) (p : ℝ × ℝ × ℝ) => comparisonFrequencyKernel q M W E Z u
    ((4:ℂ)+p.1*Complex.I) ((4:ℂ)+p.2.1*Complex.I) ((σ:ℂ)+p.2.2*Complex.I)
  have h2 : Integrable (f 2) := kernel_line_integrable q principal M W E ha Z hZ u hu hq 2
    (by norm_num [comparisonR₀])
  have hr : Integrable (f comparisonR₀) := kernel_line_integrable q principal M W E ha Z hZ u hu hq comparisonR₀
    (by norm_num [comparisonR₀])
  unfold comparisonTripleVerticalIntegral
  congr 1
  change (∫ p, f 2 p) = ∫ p, f comparisonR₀ p
  rw [Measure.volume_eq_prod] at h2 hr ⊢
  rw [integral_prod _ h2, integral_prod _ hr]
  apply integral_congr_ae
  filter_upwards [h2.prod_right_ae, hr.prod_right_ae] with t h2t hrt
  rw [Measure.volume_eq_prod] at h2t hrt ⊢
  rw [integral_prod _ h2t, integral_prod _ hrt]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun tw => kernel_vertical_eq q principal M W E ha Z hZ u hu hq t tw)

private lemma finite_triple_eq {ι : Type*}
    (q : ι → ℝ) (principal : ι) (M W : ℂ → ℂ)
    (E : ι → ℂ → ℂ → ℂ → ℂ)
    (ha : comparisonFarContourInput q principal M W E)
    (Z : ℝ) (hZ : 1 ≤ Z) (C : Finset ι)
    (hC : ∀ u ∈ C, u ≠ principal ∧ 1 ≤ q u) :
    comparisonFrequencyIntegral q M W E C Z 4 4 2 =
    comparisonFrequencyIntegral q M W E C Z 4 4 comparisonR₀ := by
  classical
  unfold comparisonFrequencyIntegral comparisonTripleVerticalIntegral
  rw [integral_finset_sum, integral_finset_sum]
  · congr 1
    apply Finset.sum_congr rfl
    intro u hu
    have hh := kernel_triple_eq q principal M W E ha Z hZ u (hC u hu).1 (hC u hu).2
    unfold comparisonTripleVerticalIntegral at hh
    exact mul_left_cancel₀ (by simp [Real.pi_ne_zero]) hh
  · intro u hu
    exact kernel_line_integrable q principal M W E ha Z hZ u (hC u hu).1 (hC u hu).2 comparisonR₀
      (by norm_num [comparisonR₀])
  · intro u hu
    exact kernel_line_integrable q principal M W E ha Z hZ u (hC u hu).1 (hC u hu).2 2
      (by norm_num [comparisonR₀])

private lemma kernel_far_bound {ι : Type*}
    (q : ι → ℝ) (principal : ι) (M W : ℂ → ℂ)
    (E : ι → ℂ → ℂ → ℂ → ℂ)
    (ha : comparisonFarContourInput q principal M W E)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Z U : ℝ) (u : ι) (p : ℝ × ℝ × ℝ),
      1 ≤ Z → 1 ≤ U → u ≠ principal → U ≤ q u → q u < 2*U →
      ‖comparisonFrequencyKernel q M W E Z u
        ((4:ℂ)+p.1*Complex.I) ((4:ℂ)+p.2.1*Complex.I) ((comparisonR₀:ℂ)+p.2.2*Complex.I)‖ ≤
      B * Z ^ comparisonE 4 4 comparisonR₀ * U^(-comparisonR₀+ε) *
        comparisonHeightEnvelope 2 p.1 p.2.1 p.2.2 := by
  obtain ⟨A₂, hA₂, hM, hW⟩ := ha.2.2.1 2
  obtain ⟨Aε, hAε, hE⟩ := ha.2.2.2.2.2 ε hε
  refine ⟨Real.exp ((3+comparisonR₀)^2)*A₂*A₂*Aε*2^ε, by positivity, ?_⟩
  intro Z U u p hZ hU hu hqu hqu2
  have hq : 1 ≤ q u := hU.trans hqu
  have hUp : 0 < U := by linarith
  have hk := kernel_norm_line_le q M W E Z comparisonR₀ hZ u hq p A₂ hA₂.le
    (by simpa using hM ((comparisonR₀:ℂ)+p.2.2*Complex.I) (by norm_num [comparisonR₀]))
    (by simpa using hW p.2.1) Aε hAε.le ε
    (hE u p.1 p.2.1 ((comparisonR₀:ℂ)+p.2.2*Complex.I) hu hq (by norm_num [comparisonR₀]))
  have h1 : (q u)^(-comparisonR₀) ≤ U^(-comparisonR₀) :=
    Real.rpow_le_rpow_of_nonpos hUp hqu (by norm_num [comparisonR₀])
  have h2 : (q u)^ε ≤ 2^ε * U^ε := by
    rw [← Real.mul_rpow (by norm_num) hUp.le]
    exact Real.rpow_le_rpow (by linarith) hqu2.le hε.le
  have h3 : (q u)^(-comparisonR₀) * (q u)^ε ≤ 2^ε * U^(-comparisonR₀+ε) := by
    calc
      _ ≤ U^(-comparisonR₀) * (2^ε*U^ε) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by rw [Real.rpow_add hUp]; ring
  have hm := mul_le_mul_of_nonneg_left h3
    (show 0 ≤ Z ^ comparisonE 4 4 comparisonR₀ * Real.exp ((3+comparisonR₀)^2)*A₂*A₂*Aε *
      comparisonHeightEnvelope 2 p.1 p.2.1 p.2.2 by unfold comparisonHeightEnvelope; positivity)
  exact hk.trans (by unfold comparisonHeightEnvelope at hm ⊢; nlinarith [hm])

theorem comparison_far_dyad {ι : Type*}
    (q : ι → ℝ) (principal : ι) (M W : ℂ → ℂ)
    (E : ι → ℂ → ℂ → ℂ → ℂ)
    (hAnalytic : comparisonFarContourInput q principal M W E)
    (K : ℝ) (hK : 0 < K) :
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
      ∀ (Z U : ℝ) (C : Finset ι), 1 ≤ Z → 1 ≤ U →
        comparisonFrequencyDyad q principal K U C →
        comparisonFrequencyIntegral q M W E C Z 4 4 2 =
          comparisonFrequencyIntegral q M W E C Z 4 4 comparisonR₀ ∧
        ‖comparisonFrequencyIntegral q M W E C Z 4 4 2‖ ≤
          A * Z ^ (3849 / 1000 + comparisonR₀ / 10) *
            U ^ (1 - comparisonR₀ + ε) := by
  intro ε hε
  obtain ⟨B, hB, hb⟩ := kernel_far_bound q principal M W E hAnalytic ε hε
  let H := fun p : ℝ × ℝ × ℝ => comparisonHeightEnvelope 2 p.1 p.2.1 p.2.2
  have hH : Integrable H := by simpa [H] using comparisonHeightEnvelope_integrable 0 (by norm_num)
  let L : ℝ := ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖
  let T : ℝ := 1 + |∫ p : ℝ × ℝ × ℝ, H p|
  have hL : 0 < L := by
    dsimp [L]
    apply norm_pos_iff.mpr
    exact pow_ne_zero _ (inv_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨L * B * K * T, by positivity, ?_⟩
  intro Z U C hZ hU hC
  have hqu : ∀ u ∈ C, u ≠ principal ∧ 1 ≤ q u := by
    intro u hu
    exact ⟨(hC.1 u hu).1, hU.trans (hC.1 u hu).2.1⟩
  have heq := finite_triple_eq q principal M W E hAnalytic Z hZ C hqu
  refine ⟨heq, ?_⟩
  rw [heq]
  classical
  have hsum (p : ℝ × ℝ × ℝ) :
      ‖∑ u ∈ C, comparisonFrequencyKernel q M W E Z u
        ((4:ℂ)+p.1*Complex.I) ((4:ℂ)+p.2.1*Complex.I) ((comparisonR₀:ℂ)+p.2.2*Complex.I)‖ ≤
      (C.card:ℝ) * (B * Z ^ comparisonE 4 4 comparisonR₀ * U^(-comparisonR₀+ε) * H p) := by
    calc
      _ ≤ ∑ u ∈ C, ‖comparisonFrequencyKernel q M W E Z u
        ((4:ℂ)+p.1*Complex.I) ((4:ℂ)+p.2.1*Complex.I) ((comparisonR₀:ℂ)+p.2.2*Complex.I)‖ := norm_sum_le _ _
      _ ≤ ∑ u ∈ C, B * Z ^ comparisonE 4 4 comparisonR₀ * U^(-comparisonR₀+ε) * H p :=
        Finset.sum_le_sum (fun u hu => hb Z U u p hZ hU (hC.1 u hu).1 (hC.1 u hu).2.1 (hC.1 u hu).2.2)
      _ = _ := by simp
  have hmaj := norm_integral_le_of_norm_le
    (hH.const_mul ((C.card:ℝ) * (B * Z ^ comparisonE 4 4 comparisonR₀ * U^(-comparisonR₀+ε))))
    (Filter.Eventually.of_forall (fun p => by simpa only [mul_assoc] using hsum p))
  rw [integral_const_mul] at hmaj
  have hi : (∫ p, H p) ≤ T := by dsimp [T]; linarith [le_abs_self (∫ p, H p)]
  have hexp : comparisonE 4 4 comparisonR₀ = 3849/1000+comparisonR₀/10 := by
    norm_num [comparisonE,comparisonA,comparisonB,comparisonH₀]; ring
  unfold comparisonFrequencyIntegral comparisonTripleVerticalIntegral
  rw [norm_mul]
  change L * ‖∫ p : ℝ × ℝ × ℝ, _‖ ≤ _
  calc
    _ ≤ L * ((C.card:ℝ) * (B * Z ^ comparisonE 4 4 comparisonR₀ * U^(-comparisonR₀+ε)) * ∫ p, H p) :=
      mul_le_mul_of_nonneg_left hmaj hL.le
    _ ≤ L * ((C.card:ℝ) * (B * Z ^ comparisonE 4 4 comparisonR₀ * U^(-comparisonR₀+ε)) * T) := by
      gcongr
    _ ≤ L * ((K*U) * (B * Z ^ comparisonE 4 4 comparisonR₀ * U^(-comparisonR₀+ε)) * T) := by
      gcongr
      exact hC.2
    _ = (L * B * K * T) * Z ^ (3849/1000+comparisonR₀/10) * U^(1-comparisonR₀+ε) := by
      rw [hexp]
      have hUp : 0 < U := by linarith
      have hp : U^(1-comparisonR₀+ε) = U * U^(-comparisonR₀+ε) := by
        rw [show (1-comparisonR₀+ε) = 1+(-comparisonR₀+ε) by ring, Real.rpow_add hUp, Real.rpow_one]
      rw [hp]
      ring

private lemma geometric_cutoff_bound (T b D : ℝ) (hT : 0 < T) (hb : b < 0)
    (hD : 0 ≤ D) (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j)
    (hle : ∀ j, f j ≤ if T < (2 : ℝ)^j then D * ((2 : ℝ)^j)^b else 0) :
    Summable f ∧ (∑' j, f j) ≤ D * T^b * (1 - (2 : ℝ)^b)⁻¹ := by
  have hr0 : 0 ≤ (2 : ℝ)^b := by positivity
  have hr1 : (2 : ℝ)^b < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hb
  have hex : ∃ n : ℕ, T < (2 : ℝ)^n :=
    ((tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).eventually
      (Filter.eventually_gt_atTop T)).exists
  let N := Nat.find hex
  have hN : T < (2 : ℝ)^N := Nat.find_spec hex
  have hprefix : ∀ j < N, f j = 0 := by
    intro j hj
    have hnot : ¬ T < (2 : ℝ)^j := Nat.find_min hex hj
    exact le_antisymm (by simpa [hnot] using hle j) (hf j)
  have htail : ∀ j, f (j + N) ≤ (D * T^b) * ((2 : ℝ)^b)^j := by
    intro j
    have heq : ((2 : ℝ)^(j + N))^b = ((2 : ℝ)^N)^b * ((2 : ℝ)^b)^j := by
      rw [pow_add, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast_mul (by norm_num) j b, mul_comm (j : ℝ) b,
        Real.rpow_mul_natCast (by norm_num)]
      ring
    calc
      f (j + N) ≤ D * ((2 : ℝ)^(j + N))^b := by
        by_cases h : T < (2 : ℝ)^(j+N)
        · simpa [h] using hle (j+N)
        · exact (show f (j+N) ≤ 0 by simpa [h] using hle (j+N)).trans (by positivity)
      _ = D * (((2 : ℝ)^N)^b * ((2 : ℝ)^b)^j) := by rw [heq]
      _ ≤ D * (T^b * ((2 : ℝ)^b)^j) := by
        apply mul_le_mul_of_nonneg_left _ hD
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hT hN.le hb.le) (by positivity)
      _ = (D * T^b) * ((2 : ℝ)^b)^j := by ring
  have hg := (summable_geometric_of_lt_one hr0 hr1).mul_left (D * T^b)
  have hs : Summable (fun j => f (j+N)) := Summable.of_nonneg_of_le (fun j => hf _) htail hg
  have hsall : Summable f := (summable_nat_add_iff N).mp hs
  refine ⟨hsall, ?_⟩
  have heq : (∑' j, f j) = ∑' j, f (j+N) := by
    have h := hsall.sum_add_tsum_nat_add N
    have hz : ∑ j ∈ Finset.range N, f j = 0 := Finset.sum_eq_zero (fun j hj => hprefix j (Finset.mem_range.mp hj))
    simpa [hz] using h.symm
  rw [heq]
  calc
    (∑' j, f (j+N)) ≤ ∑' j, (D*T^b) * ((2 : ℝ)^b)^j := hs.tsum_le_tsum htail hg
    _ = D*T^b*(1-(2 : ℝ)^b)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]

theorem comparison_far_dyad_sum {ι : Type*}
    (q : ι → ℝ) (principal : ι) (M W : ℂ → ℂ)
    (E : ι → ℂ → ℂ → ℂ → ℂ)
    (hAnalytic : comparisonFarContourInput q principal M W E)
    (K : ℝ) (hK : 0 < K) :
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
      ∀ (Z : ℝ) (C : ℕ → Finset ι), 1 ≤ Z →
        (∀ j : ℕ, comparisonFrequencyDyad q principal K ((2 : ℝ) ^ j) (C j)) →
        let terms := fun j : ℕ =>
          if Z ^ (10001 / 100000 : ℝ) < (2 : ℝ) ^ j then
            ‖comparisonFrequencyIntegral q M W E (C j) Z 4 4 2‖ else 0
        Summable terms ∧
          (∑' j : ℕ, terms j) ≤
            A * Z ^ (44901 / 100000 + (10001 / 100000) * ε) := by
  intro ε hε
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  let b := 1 - comparisonR₀ + δ
  have hb : b < 0 := by dsimp [b, comparisonR₀]; linarith
  have hr : (2 : ℝ)^b < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hb
  obtain ⟨B, hB, hbound⟩ := comparison_far_dyad q principal M W E hAnalytic K hK δ hδ
  refine ⟨B * (1 - (2 : ℝ)^b)⁻¹, by positivity, ?_⟩
  intro Z C hZ hC
  dsimp only
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have ht := geometric_cutoff_bound (Z ^ (10001 / 100000 : ℝ)) b
    (B * Z ^ (3849 / 1000 + comparisonR₀ / 10)) (by positivity) hb (by positivity)
    (fun j => if Z ^ (10001 / 100000 : ℝ) < (2 : ℝ)^j then
      ‖comparisonFrequencyIntegral q M W E (C j) Z 4 4 2‖ else 0)
    (fun j => by split_ifs <;> positivity) ?_
  · refine ⟨ht.1, ht.2.trans ?_⟩
    have hexp : (3849 / 1000 + comparisonR₀ / 10) +
        (10001 / 100000) * b = 44901 / 100000 + (10001 / 100000) * δ := by
      dsimp [b, comparisonR₀]; ring
    calc
      B * Z ^ (3849 / 1000 + comparisonR₀ / 10) *
          (Z ^ (10001 / 100000 : ℝ)) ^ b * (1 - (2 : ℝ)^b)⁻¹ =
          (B * (1 - (2 : ℝ)^b)⁻¹) * Z ^ (44901 / 100000 + (10001 / 100000) * δ) := by
        rw [← Real.rpow_mul hZpos.le, ← hexp,
          Real.rpow_add hZpos (3849 / 1000 + comparisonR₀ / 10)
            ((10001 / 100000) * b)]
        ring
      _ ≤ (B * (1 - (2 : ℝ)^b)⁻¹) * Z ^ (44901 / 100000 + (10001 / 100000) * ε) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)
  · intro j
    split_ifs with hj
    · exact (hbound Z ((2 : ℝ)^j) (C j) hZ
        (one_le_pow₀ (by norm_num)) (hC j)).2
    · rfl

end
end DedekindZetaZeroFree
