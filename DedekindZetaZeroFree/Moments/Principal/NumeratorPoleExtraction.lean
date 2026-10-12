module

public import DedekindZetaZeroFree.Moments.Comparison.TripleMellinKernel

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open MeasureTheory Complex

namespace PrincipalWShift

def kernel (Z : ℝ) (M W ζ L : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ)
    (ξ w z : ℂ) : ℂ :=
  comparisonRealPower (comparisonX Z) (1 / 2 - z) *
    comparisonRealPower Z (ξ + z - 1) *
    comparisonRealPower (comparisonY Z) (w - 1) *
    Complex.exp ((ξ + z - 1) ^ 2) * M z * W w *
    (ζ (6 * z) * ζ w / L ξ) * H ξ w z

def J (Z : ℝ) (M W ζ L : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ)
    (σξ σw σz : ℝ) : ℂ :=
  comparisonTripleVerticalIntegral σξ σw σz (kernel Z M W ζ L H)

def clearedKernel (Z : ℝ) (M W ζ L R : ℂ → ℂ)
    (H : ℂ → ℂ → ℂ → ℂ) (ξ w z : ℂ) : ℂ :=
  comparisonRealPower (comparisonX Z) (1 / 2 - z) *
    comparisonRealPower Z (ξ + z - 1) *
    comparisonRealPower (comparisonY Z) (w - 1) *
    Complex.exp ((ξ + z - 1) ^ 2) * M z * W w *
    (ζ (6 * z) * R w / L ξ) * H ξ w z

def residueKernel (Z : ℝ) (M W ζ L : ℂ → ℂ)
    (H : ℂ → ℂ → ℂ → ℂ) (ξ z : ℂ) : ℂ :=
  comparisonRealPower (comparisonX Z) (1 / 2 - z) *
    comparisonRealPower Z (ξ + z - 1) *
    Complex.exp ((ξ + z - 1) ^ 2) * M z * W 1 *
    (ζ (6 * z) / L ξ) * H ξ 1 z

def doubleVerticalIntegral (σξ σz : ℝ) (f : ℂ → ℂ → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ ^ 2 *
    ∫ t : ℝ × ℝ,
      f ((σξ : ℂ) + (t.1 : ℂ) * I)
        ((σz : ℂ) + (t.2 : ℂ) * I)

theorem clearedKernel_one (Z : ℝ) (M W ζ L R : ℂ → ℂ)
    (H : ℂ → ℂ → ℂ → ℂ) (ξ z : ℂ) :
    clearedKernel Z M W ζ L R H ξ 1 z =
      R 1 * residueKernel Z M W ζ L H ξ z := by
  simp only [clearedKernel, residueKernel, sub_self, comparisonRealPower,
    zero_mul, Complex.exp_zero, mul_one]
  ring

def reorder : ((ℝ × ℝ) × ℝ) ≃ᵐ ℝ × (ℝ × ℝ) :=
  MeasurableEquiv.prodAssoc.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.prodComm)

private lemma reorder_preserving : MeasurePreserving reorder volume volume := by
  have hi : MeasurePreserving (id : ℝ → ℝ) volume volume := MeasurePreserving.id volume
  have hs : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_swap
  exact (hi.prod hs).comp volume_preserving_prodAssoc

private lemma reorder_integrable (f : ℝ × (ℝ × ℝ) → ℂ) (hf : Integrable f) :
    Integrable (fun p : (ℝ × ℝ) × ℝ => f (p.1.1, p.2, p.1.2)) := by
  exact (reorder_preserving.integrable_comp_emb reorder.measurableEmbedding).mpr hf

private lemma reorder_integral (f : ℝ × (ℝ × ℝ) → ℂ) (hf : Integrable f) :
    (∫ p, f p) = ∫ p : ℝ × ℝ, ∫ t : ℝ, f (p.1, t, p.2) := by
  rw [← reorder_preserving.integral_comp reorder.measurableEmbedding f]
  exact integral_prod _ (reorder_integrable f hf)

private lemma last_integral (f : ℝ × (ℝ × ℝ) → ℂ) (hf : Integrable f) :
    (∫ p, f p) = ∫ p : ℝ × ℝ, ∫ t : ℝ, f (p.1, p.2, t) := by
  rw [← volume_preserving_prodAssoc.integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding f]
  exact integral_prod _
    ((volume_preserving_prodAssoc.integrable_comp_emb
      MeasurableEquiv.prodAssoc.measurableEmbedding).mpr hf)

private lemma separate_height_measurable (f : ℝ → ℝ → ℝ → ℂ)
    (hx : ∀ y z, Continuous (fun x => f x y z))
    (hy : ∀ x z, Continuous (fun y => f x y z))
    (hz : ∀ x y, Continuous (fun z => f x y z)) :
    Measurable (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) := by
  exact measurable_uncurry_of_continuous_of_measurable
    (u := fun x (p : ℝ × ℝ) => f x p.1 p.2)
    (fun p => hx p.1 p.2)
    (fun x => measurable_uncurry_of_continuous_of_measurable
      (u := fun y z => f x y z) (hy x) (fun y => (hz x y).measurable))

theorem initial_corridor
    (Z : ℝ) (hZ : 1 ≤ Z) (M W ζ L : ℂ → ℂ)
    (H : ℂ → ℂ → ℂ → ℂ) (U : Set (ℂ × ℂ × ℂ))
    (C : ℝ) (hC : 0 ≤ C) (hU : IsOpen U)
    (hcorridor : ∀ ξ w z : ℂ,
      ξ.re ∈ Set.Icc comparisonSigma₁ 4 →
      w.re ∈ Set.Icc comparisonSigma₁ 4 →
      z.re ∈ Set.Icc comparisonZeta₁ 2 → (ξ, w, z) ∈ U)
    (hξ : ∀ w z : ℂ, DifferentiableOn ℂ (fun ξ => kernel Z M W ζ L H ξ w z)
      {ξ | (ξ, w, z) ∈ U})
    (hw : ∀ ξ z : ℂ, DifferentiableOn ℂ (fun w => kernel Z M W ζ L H ξ w z)
      {w | (ξ, w, z) ∈ U})
    (hz : ∀ ξ w : ℂ, DifferentiableOn ℂ (fun z => kernel Z M W ζ L H ξ w z)
      {z | (ξ, w, z) ∈ U})
    (hdecay : ∀ ξ w z : ℂ, (ξ, w, z) ∈ U →
      ‖kernel Z M W ζ L H ξ w z‖ ≤
        C * (1 + |ξ.im|) ^ (-2 : ℝ) *
          (1 + |w.im|) ^ (-2 : ℝ) * (1 + |z.im|) ^ (-2 : ℝ)) :
    J Z M W ζ L H 4 4 2 =
      J Z M W ζ L H comparisonSigma₁ comparisonSigma₁ comparisonZeta₁ := by
  let g : ℝ → ℝ := fun t => (1 + |t|) ^ (-2 : ℝ)
  let F (a b c : ℝ) (x y z : ℝ) : ℂ :=
    kernel Z M W ζ L H ((a : ℂ) + (x : ℂ) * I)
      ((b : ℂ) + (y : ℂ) * I) ((c : ℂ) + (z : ℂ) * I)
  have hg : Integrable g := by
    simpa only [g, Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (r := 2) (μ := volume) (by simp))
  have hg3 : Integrable (fun t : ℝ × ℝ × ℝ =>
      (C * g t.1) * (g t.2.1 * g t.2.2)) :=
    (hg.const_mul C).mul_prod (hg.mul_prod hg)
  have hi (a b c : ℝ)
      (ha : a ∈ Set.Icc comparisonSigma₁ 4)
      (hb : b ∈ Set.Icc comparisonSigma₁ 4)
      (hc : c ∈ Set.Icc comparisonZeta₁ 2) :
      Integrable (fun t : ℝ × ℝ × ℝ => F a b c t.1 t.2.1 t.2.2) := by
    have hx (y z : ℝ) : Continuous (fun x => F a b c x y z) := by
      apply (hξ _ _).continuousOn.comp_continuous (by fun_prop)
      intro x
      exact hcorridor _ _ _ (by simpa using ha) (by simpa using hb)
        (by simpa using hc)
    have hy (x z : ℝ) : Continuous (fun y => F a b c x y z) := by
      apply (hw _ _).continuousOn.comp_continuous (by fun_prop)
      intro y
      exact hcorridor _ _ _ (by simpa using ha) (by simpa using hb)
        (by simpa using hc)
    have hz' (x y : ℝ) : Continuous (fun z => F a b c x y z) := by
      apply (hz _ _).continuousOn.comp_continuous (by fun_prop)
      intro z
      exact hcorridor _ _ _ (by simpa using ha) (by simpa using hb)
        (by simpa using hc)
    apply hg3.mono' (separate_height_measurable (F a b c) hx hy hz').aestronglyMeasurable
    filter_upwards [] with t
    have hd := hdecay ((a : ℂ) + (t.1 : ℂ) * I)
      ((b : ℂ) + (t.2.1 : ℂ) * I) ((c : ℂ) + (t.2.2 : ℂ) * I)
      (hcorridor _ _ _ (by simpa using ha) (by simpa using hb)
        (by simpa using hc))
    simpa only [F, g, mul_assoc, add_im, ofReal_im, mul_im, I_re, I_im,
      zero_mul, mul_zero, zero_add, mul_one, add_zero, ofReal_re] using hd
  have hσ : comparisonSigma₁ < 4 := by norm_num [comparisonSigma₁, comparisonDelta]
  have hζ : comparisonZeta₁ < 2 := by norm_num [comparisonZeta₁, comparisonDelta]
  have hσ₀ : comparisonSigma₁ ∈ Set.Icc comparisonSigma₁ 4 := ⟨le_rfl, hσ.le⟩
  have hσ₄ : (4 : ℝ) ∈ Set.Icc comparisonSigma₁ 4 := ⟨hσ.le, le_rfl⟩
  have hζ₀ : comparisonZeta₁ ∈ Set.Icc comparisonZeta₁ 2 := ⟨le_rfl, hζ.le⟩
  have hζ₂ : (2 : ℝ) ∈ Set.Icc comparisonZeta₁ 2 := ⟨hζ.le, le_rfl⟩
  have shiftξ (b c : ℝ) (hb : b ∈ Set.Icc comparisonSigma₁ 4)
      (hc : c ∈ Set.Icc comparisonZeta₁ 2) (y z : ℝ) :
      (∫ x : ℝ, F comparisonSigma₁ b c x y z) = ∫ x : ℝ, F 4 b c x y z := by
    let w' : ℂ := (b : ℂ) + (y : ℂ) * I
    let z' : ℂ := (c : ℂ) + (z : ℂ) * I
    apply verticalIntegral_eq_of_strip_decay comparisonSigma₁ 4
      (C * g y * g z) (fun ξ => kernel Z M W ζ L H ξ w' z')
      {ξ | (ξ, w', z') ∈ U} hσ
    · exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg (by positivity) _)
    · exact hU.preimage (by fun_prop)
    · intro ξ hξ'
      exact hcorridor _ _ _ hξ' (by simpa [w'] using hb) (by simpa [z'] using hc)
    · exact hξ w' z'
    · intro ξ hξ'
      have hd := hdecay ξ w' z'
        (hcorridor _ _ _ hξ' (by simpa [w'] using hb) (by simpa [z'] using hc))
      convert hd using 1 <;> simp only [w', z', g, add_im, ofReal_im, mul_im,
        I_re, I_im, zero_mul, mul_zero, zero_add, mul_one, add_zero, ofReal_re]
      ring
  have shiftw (a c : ℝ) (ha : a ∈ Set.Icc comparisonSigma₁ 4)
      (hc : c ∈ Set.Icc comparisonZeta₁ 2) (x z : ℝ) :
      (∫ y : ℝ, F a comparisonSigma₁ c x y z) = ∫ y : ℝ, F a 4 c x y z := by
    let ξ' : ℂ := (a : ℂ) + (x : ℂ) * I
    let z' : ℂ := (c : ℂ) + (z : ℂ) * I
    apply verticalIntegral_eq_of_strip_decay comparisonSigma₁ 4
      (C * g x * g z) (fun w => kernel Z M W ζ L H ξ' w z')
      {w | (ξ', w, z') ∈ U} hσ
    · exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg (by positivity) _)
    · exact hU.preimage (by fun_prop)
    · intro w hw'
      exact hcorridor _ _ _ (by simpa [ξ'] using ha) hw' (by simpa [z'] using hc)
    · exact hw ξ' z'
    · intro w hw'
      have hd := hdecay ξ' w z'
        (hcorridor _ _ _ (by simpa [ξ'] using ha) hw' (by simpa [z'] using hc))
      convert hd using 1 <;> simp only [ξ', z', g, add_im, ofReal_im, mul_im,
        I_re, I_im, zero_mul, mul_zero, zero_add, mul_one, add_zero, ofReal_re]
      ring
  have shiftz (a b : ℝ) (ha : a ∈ Set.Icc comparisonSigma₁ 4)
      (hb : b ∈ Set.Icc comparisonSigma₁ 4) (x y : ℝ) :
      (∫ z : ℝ, F a b comparisonZeta₁ x y z) = ∫ z : ℝ, F a b 2 x y z := by
    let ξ' : ℂ := (a : ℂ) + (x : ℂ) * I
    let w' : ℂ := (b : ℂ) + (y : ℂ) * I
    apply verticalIntegral_eq_of_strip_decay comparisonZeta₁ 2
      (C * g x * g y) (fun z => kernel Z M W ζ L H ξ' w' z)
      {z | (ξ', w', z) ∈ U} hζ
    · exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg (by positivity) _)
    · exact hU.preimage (by fun_prop)
    · intro z hz'
      exact hcorridor _ _ _ (by simpa [ξ'] using ha) (by simpa [w'] using hb) hz'
    · exact hz ξ' w'
    · intro z hz'
      have hd := hdecay ξ' w' z
        (hcorridor _ _ _ (by simpa [ξ'] using ha) (by simpa [w'] using hb) hz')
      simpa [ξ', w', g] using hd
  unfold J comparisonTripleVerticalIntegral
  congr 1
  change (∫ t : ℝ × ℝ × ℝ, F 4 4 2 t.1 t.2.1 t.2.2) =
    ∫ t : ℝ × ℝ × ℝ, F comparisonSigma₁ comparisonSigma₁ comparisonZeta₁
      t.1 t.2.1 t.2.2
  calc
    _ = ∫ p : ℝ × ℝ, ∫ x : ℝ, F 4 4 2 x p.1 p.2 :=
      integral_prod_symm _ (hi 4 4 2 hσ₄ hσ₄ hζ₂)
    _ = ∫ p : ℝ × ℝ, ∫ x : ℝ, F comparisonSigma₁ 4 2 x p.1 p.2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => (shiftξ 4 2 hσ₄ hζ₂ p.1 p.2).symm)
    _ = ∫ t : ℝ × ℝ × ℝ, F comparisonSigma₁ 4 2 t.1 t.2.1 t.2.2 :=
      (integral_prod_symm _ (hi comparisonSigma₁ 4 2 hσ₀ hσ₄ hζ₂)).symm
    _ = ∫ p : ℝ × ℝ, ∫ y : ℝ, F comparisonSigma₁ 4 2 p.1 y p.2 :=
      reorder_integral _ (hi comparisonSigma₁ 4 2 hσ₀ hσ₄ hζ₂)
    _ = ∫ p : ℝ × ℝ, ∫ y : ℝ, F comparisonSigma₁ comparisonSigma₁ 2 p.1 y p.2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun p => (shiftw comparisonSigma₁ 2 hσ₀ hζ₂ p.1 p.2).symm)
    _ = ∫ t : ℝ × ℝ × ℝ, F comparisonSigma₁ comparisonSigma₁ 2 t.1 t.2.1 t.2.2 :=
      (reorder_integral _ (hi comparisonSigma₁ comparisonSigma₁ 2 hσ₀ hσ₀ hζ₂)).symm
    _ = ∫ p : ℝ × ℝ, ∫ z : ℝ, F comparisonSigma₁ comparisonSigma₁ 2 p.1 p.2 z :=
      last_integral _ (hi comparisonSigma₁ comparisonSigma₁ 2 hσ₀ hσ₀ hζ₂)
    _ = ∫ p : ℝ × ℝ, ∫ z : ℝ,
        F comparisonSigma₁ comparisonSigma₁ comparisonZeta₁ p.1 p.2 z := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun p => (shiftz comparisonSigma₁ comparisonSigma₁ hσ₀ hσ₀ p.1 p.2).symm)
    _ = _ := (last_integral _
      (hi comparisonSigma₁ comparisonSigma₁ comparisonZeta₁ hσ₀ hσ₀ hζ₀)).symm

private lemma pole_slice (Z : ℝ) (M W ζ L R : ℂ → ℂ)
    (H : ℂ → ℂ → ℂ → ℂ) (U : Set ℂ) (C : ℝ)
    (hU : IsOpen U)
    (hstrip : comparisonClosedStrip (19 / 20) comparisonSigma₁ ⊆ U)
    (hR : ∀ w ∈ U, w ≠ 1 → R w = (w - 1) * ζ w)
    (hhol : ∀ ξ z : ℂ, ξ.re = comparisonSigma₁ → z.re = comparisonZeta₁ →
      DifferentiableOn ℂ (fun w => clearedKernel Z M W ζ L R H ξ w z) U)
    (hdecay : ∀ ξ w z : ℂ,
      ξ.re = comparisonSigma₁ → z.re = comparisonZeta₁ →
      w ∈ comparisonClosedStrip (19 / 20) comparisonSigma₁ → 1 ≤ |w.im| →
      ‖kernel Z M W ζ L H ξ w z‖ ≤
        C * (1 + |ξ.im|) ^ (-2 : ℝ) *
          (1 + |z.im|) ^ (-2 : ℝ) * (1 + |w.im|) ^ (-2 : ℝ))
    (p : ℝ × ℝ)
    (hleft : Integrable (fun t : ℝ => kernel Z M W ζ L H
      ((comparisonSigma₁ : ℂ) + (p.1 : ℂ) * I) ((19 / 20 : ℂ) + (t : ℂ) * I)
      ((comparisonZeta₁ : ℂ) + (p.2 : ℂ) * I)))
    (hright : Integrable (fun t : ℝ => kernel Z M W ζ L H
      ((comparisonSigma₁ : ℂ) + (p.1 : ℂ) * I)
      ((comparisonSigma₁ : ℂ) + (t : ℂ) * I)
      ((comparisonZeta₁ : ℂ) + (p.2 : ℂ) * I))) :
    comparisonVerticalIntegral comparisonSigma₁
      (kernel Z M W ζ L H ((comparisonSigma₁ : ℂ) + (p.1 : ℂ) * I) ·
        ((comparisonZeta₁ : ℂ) + (p.2 : ℂ) * I)) =
      comparisonVerticalIntegral (19 / 20)
        (kernel Z M W ζ L H ((comparisonSigma₁ : ℂ) + (p.1 : ℂ) * I) ·
          ((comparisonZeta₁ : ℂ) + (p.2 : ℂ) * I)) +
      R 1 * residueKernel Z M W ζ L H
        ((comparisonSigma₁ : ℂ) + (p.1 : ℂ) * I)
        ((comparisonZeta₁ : ℂ) + (p.2 : ℂ) * I) := by
  let ξ : ℂ := (comparisonSigma₁ : ℂ) + (p.1 : ℂ) * I
  let z : ℂ := (comparisonZeta₁ : ℂ) + (p.2 : ℂ) * I
  let f := fun w => kernel Z M W ζ L H ξ w z
  let A := fun w => clearedKernel Z M W ζ L R H ξ w z
  have hξ : ξ.re = comparisonSigma₁ := by simp [ξ]
  have hz : z.re = comparisonZeta₁ := by simp [z]
  have hab : (19 / 20 : ℝ) ≤ comparisonSigma₁ := by
    norm_num [comparisonSigma₁, comparisonDelta]
  have hap : (19 / 20 : ℝ) < 1 := by norm_num
  have hpb : (1 : ℝ) < comparisonSigma₁ := by
    norm_num [comparisonSigma₁, comparisonDelta]
  have hAs : DifferentiableOn ℂ A
      {w : ℂ | (19 / 20 : ℝ) ≤ w.re ∧ w.re ≤ comparisonSigma₁} :=
    (hhol ξ z hξ hz).mono hstrip
  have hF : ∀ w : ℂ, (19 / 20 : ℝ) ≤ w.re → w.re ≤ comparisonSigma₁ →
      w ≠ 1 → f w = A w / (w - 1) := by
    intro w hw₁ hw₂ hw
    have hr := hR w (hstrip ⟨hw₁, hw₂⟩) hw
    dsimp [f, A, kernel, clearedKernel]
    rw [hr]
    field_simp
  have hb : ∀ x ∈ Set.Icc (19 / 20 : ℝ) comparisonSigma₁,
      ∀ y : ℝ, 1 ≤ |y| →
      ‖f ((x : ℂ) + y * I)‖ ≤
        (C * (1 + |ξ.im|) ^ (-2 : ℝ) * (1 + |z.im|) ^ (-2 : ℝ)) *
          (1 + |y|) ^ (-2 : ℝ) := by
    intro x hx y hy
    simpa [f] using hdecay ξ ((x : ℂ) + y * I) z hξ hz
      (by simpa [comparisonClosedStrip] using hx) (by simpa using hy)
  have hlo := ComparisonShiftProof.horizontal_decay_limit f (19 / 20)
    comparisonSigma₁ (C * (1 + |ξ.im|) ^ (-2 : ℝ) *
      (1 + |z.im|) ^ (-2 : ℝ)) (-1) hab (by norm_num) hb
  have hhi := ComparisonShiftProof.horizontal_decay_limit f (19 / 20)
    comparisonSigma₁ (C * (1 + |ξ.im|) ^ (-2 : ℝ) *
      (1 + |z.im|) ^ (-2 : ℝ)) 1 hab (by norm_num) hb
  have h := ComparisonShiftProof.simple_pole_of_boundary_control A f hap hpb
    hAs hF (by simpa [f, ξ, z] using hleft)
    (by simpa [f, ξ, z] using hright) (by simpa using hlo) (by simpa using hhi)
  simpa [f, A, ξ, z, clearedKernel_one] using h

theorem numerator_pole
    (Z : ℝ) (hZ : 1 ≤ Z) (M W ζ L R : ℂ → ℂ)
    (H : ℂ → ℂ → ℂ → ℂ) (U : Set ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hU : IsOpen U)
    (hstrip : comparisonClosedStrip (19 / 20) comparisonSigma₁ ⊆ U)
    (hR : ∀ w ∈ U, w ≠ 1 → R w = (w - 1) * ζ w)
    (hhol : ∀ ξ z : ℂ, ξ.re = comparisonSigma₁ → z.re = comparisonZeta₁ →
      DifferentiableOn ℂ (fun w => clearedKernel Z M W ζ L R H ξ w z) U)
    (hdecay : ∀ ξ w z : ℂ,
      ξ.re = comparisonSigma₁ → z.re = comparisonZeta₁ →
      w ∈ comparisonClosedStrip (19 / 20) comparisonSigma₁ → 1 ≤ |w.im| →
      ‖kernel Z M W ζ L H ξ w z‖ ≤
        C * (1 + |ξ.im|) ^ (-2 : ℝ) *
          (1 + |z.im|) ^ (-2 : ℝ) * (1 + |w.im|) ^ (-2 : ℝ))
    (hendpoints : ∀ σw ∈ ({(19 / 20 : ℝ), comparisonSigma₁} : Set ℝ),
      Integrable (fun t : ℝ × ℝ × ℝ =>
        kernel Z M W ζ L H
          ((comparisonSigma₁ : ℂ) + (t.1 : ℂ) * I)
          ((σw : ℂ) + (t.2.1 : ℂ) * I)
          ((comparisonZeta₁ : ℂ) + (t.2.2 : ℂ) * I)))
    (hresidue : Integrable (fun t : ℝ × ℝ =>
      residueKernel Z M W ζ L H
        ((comparisonSigma₁ : ℂ) + (t.1 : ℂ) * I)
        ((comparisonZeta₁ : ℂ) + (t.2 : ℂ) * I))) :
    J Z M W ζ L H comparisonSigma₁ comparisonSigma₁ comparisonZeta₁ =
      J Z M W ζ L H comparisonSigma₁ (19 / 20) comparisonZeta₁ +
        R 1 * doubleVerticalIntegral comparisonSigma₁ comparisonZeta₁
          (residueKernel Z M W ζ L H) := by
  let F (σ : ℝ) (p : ℝ × ℝ) (t : ℝ) : ℂ :=
    kernel Z M W ζ L H
      ((comparisonSigma₁ : ℂ) + (p.1 : ℂ) * I)
      ((σ : ℂ) + (t : ℂ) * I)
      ((comparisonZeta₁ : ℂ) + (p.2 : ℂ) * I)
  let V (σ : ℝ) (p : ℝ × ℝ) : ℂ :=
    comparisonVerticalIntegral σ
      (fun w => kernel Z M W ζ L H
        ((comparisonSigma₁ : ℂ) + (p.1 : ℂ) * I) w
        ((comparisonZeta₁ : ℂ) + (p.2 : ℂ) * I))
  have hi (σ : ℝ) (hσ : σ ∈ ({(19 / 20 : ℝ), comparisonSigma₁} : Set ℝ)) :
      Integrable (fun p : (ℝ × ℝ) × ℝ => F σ p.1 p.2) := by
    exact reorder_integrable _ (hendpoints σ hσ)
  have hVI (σ : ℝ) (hσ : σ ∈ ({(19 / 20 : ℝ), comparisonSigma₁} : Set ℝ)) :
      Integrable (V σ) := by
    have hh := (hi σ hσ).integral_prod_left
    exact (by simpa [V, F, comparisonVerticalIntegral] using
      hh.const_mul ((2 * (Real.pi : ℂ))⁻¹))
  have hJ (σ : ℝ) (hσ : σ ∈ ({(19 / 20 : ℝ), comparisonSigma₁} : Set ℝ)) :
      J Z M W ζ L H comparisonSigma₁ σ comparisonZeta₁ =
        (2 * (Real.pi : ℂ))⁻¹ ^ 2 * ∫ p : ℝ × ℝ, V σ p := by
    unfold J comparisonTripleVerticalIntegral
    rw [reorder_integral _ (hendpoints σ hσ)]
    simp only [V, comparisonVerticalIntegral, integral_const_mul]
    ring
  have hl := (hi (19 / 20) (by simp)).prod_right_ae
  have hr := (hi comparisonSigma₁ (by simp)).prod_right_ae
  have hp : ∀ᵐ p : ℝ × ℝ, V comparisonSigma₁ p =
      V (19 / 20) p + R 1 * residueKernel Z M W ζ L H
        ((comparisonSigma₁ : ℂ) + (p.1 : ℂ) * I)
        ((comparisonZeta₁ : ℂ) + (p.2 : ℂ) * I) := by
    filter_upwards [hl, hr] with p hl hr
    apply pole_slice Z M W ζ L R H U C hU hstrip hR hhol hdecay p
    · simpa only [F, ofReal_div, ofReal_ofNat, ofReal_one] using hl
    · simpa only [F] using hr
  rw [hJ comparisonSigma₁ (by simp), hJ (19 / 20) (by simp)]
  rw [integral_congr_ae hp,
    integral_add (hVI (19 / 20) (by simp)) (hresidue.const_mul (R 1)),
    integral_const_mul]
  unfold doubleVerticalIntegral
  ring

end PrincipalWShift
end
end DedekindZetaZeroFree
