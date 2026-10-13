module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.Kernel

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.WeightConvolution

noncomputable section

open DedekindZetaZeroFree MeasureTheory

def modelIntegrand (A k T : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-(T + p.1) ^ 2) * (1 + |p.1|) ^ (-A) * (1 + |p.2|) ^ (-A) *
    (2 + |p.1| + |p.2| + |T|) ^ k

private def gaussPoly (M : ℕ) (u : ℝ) : ℝ := Real.exp (-u ^ 2) * (1 + |u|) ^ M

private lemma gaussPoly_integrable (M : ℕ) : Integrable (gaussPoly M) := by
  refine Integrable.mono'
    ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).const_mul
      (Real.exp ((M:ℝ) ^ 2 / 2))) ?_ ?_
  · unfold gaussPoly; fun_prop
  · refine Filter.Eventually.of_forall (fun u => ?_)
    have hnn : 0 ≤ gaussPoly M u := by unfold gaussPoly; positivity
    rw [Real.norm_of_nonneg hnn]
    unfold gaussPoly
    have hpow : (1 + |u|) ^ M ≤ Real.exp (M * |u|) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp |u|]) M
    have hexp : Real.exp (-u ^ 2) * Real.exp (M * |u|) ≤
        Real.exp ((M:ℝ) ^ 2 / 2) * Real.exp (-(1/2) * u ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_abs u, sq_nonneg (|u| - M)]
    calc Real.exp (-u ^ 2) * (1 + |u|) ^ M
        ≤ Real.exp (-u ^ 2) * Real.exp (M * |u|) :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ ≤ _ := hexp

private lemma pt_bound (A k B M a b c d S : ℝ) (hk : 0 ≤ k) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hd : 1 ≤ d) (hcda : c ≤ d * a) (hA : k + M + 2 ≤ A) (hM : k + B ≤ M)
    (hB0 : 0 ≤ B)
    (hS0 : 0 ≤ S) (hS : S ≤ 2 * a * b * c) :
    S ^ k * a ^ (-A) * b ^ (-A) ≤ 2 ^ k * d ^ M * c ^ (-B) * b ^ (-(A - k)) := by
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  have hcpos : 0 < c := by linarith
  have hdpos : 0 < d := by linarith
  have h1 : S ^ k ≤ 2 ^ k * a ^ k * b ^ k * c ^ k := by
    calc S ^ k ≤ (2 * a * b * c) ^ k := Real.rpow_le_rpow hS0 hS hk
      _ = 2 ^ k * a ^ k * b ^ k * c ^ k := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity)]
  have h2 : a ^ (k - A) ≤ a ^ (-M) := Real.rpow_le_rpow_of_exponent_le ha (by linarith)
  have h3 : a ^ (-M) ≤ d ^ M * c ^ (-M) := by
    have hX : 0 < c ^ M := Real.rpow_pos_of_pos hcpos M
    have hY : 0 < a ^ M := Real.rpow_pos_of_pos hapos M
    have hcM : c ^ M ≤ d ^ M * a ^ M := by
      calc c ^ M ≤ (d * a) ^ M := Real.rpow_le_rpow hcpos.le hcda (by linarith)
        _ = d ^ M * a ^ M := Real.mul_rpow hdpos.le hapos.le
    rw [Real.rpow_neg hapos.le, Real.rpow_neg hcpos.le, le_mul_inv_iff₀ hX,
      inv_mul_le_iff₀ hY]
    linarith [mul_comm (d ^ M) (a ^ M)]
  have h4 : c ^ k * c ^ (-M) = c ^ (-B) * c ^ (k - M + B) := by
    rw [← Real.rpow_add hcpos, ← Real.rpow_add hcpos]
    congr 1; ring
  have h5 : c ^ (k - M + B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc (by linarith)
  have hcpow : 0 < c ^ (-B) := Real.rpow_pos_of_pos hcpos _
  have hA' : 0 ≤ S ^ k := Real.rpow_nonneg hS0 k
  have hEa : a ^ (k - A) = a ^ k * a ^ (-A) := by
    rw [sub_eq_add_neg, Real.rpow_add hapos]
  have hEb : b ^ (k - A) = b ^ k * b ^ (-A) := by
    rw [sub_eq_add_neg, Real.rpow_add hbpos]
  have hEb' : b ^ (-(A - k)) = b ^ (k - A) := by congr 1; ring
  have hcpos' : 0 ≤ c ^ k := Real.rpow_nonneg hcpos.le k
  have hbA : 0 ≤ b ^ (-A) := Real.rpow_nonneg hbpos.le _
  have haA : 0 ≤ a ^ (-A) := Real.rpow_nonneg hapos.le _
  have hbk : 0 ≤ b ^ k := Real.rpow_nonneg hbpos.le _
  have hak : 0 ≤ a ^ k := Real.rpow_nonneg hapos.le _
  calc S ^ k * a ^ (-A) * b ^ (-A)
      ≤ (2 ^ k * a ^ k * b ^ k * c ^ k) * a ^ (-A) * b ^ (-A) := by
        apply mul_le_mul_of_nonneg_right _ hbA
        apply mul_le_mul_of_nonneg_right h1 haA
    _ = 2 ^ k * c ^ k * (a ^ k * a ^ (-A)) * (b ^ k * b ^ (-A)) := by ring
    _ = 2 ^ k * c ^ k * a ^ (k - A) * b ^ (k - A) := by rw [hEa, hEb]
    _ ≤ 2 ^ k * c ^ k * (d ^ M * c ^ (-M)) * b ^ (k - A) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hbpos.le _)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact h2.trans h3
    _ = 2 ^ k * d ^ M * (c ^ k * c ^ (-M)) * b ^ (k - A) := by ring
    _ = 2 ^ k * d ^ M * (c ^ (-B) * c ^ (k - M + B)) * b ^ (k - A) := by rw [h4]
    _ ≤ 2 ^ k * d ^ M * c ^ (-B) * b ^ (k - A) := by
        have : c ^ (-B) * c ^ (k - M + B) ≤ c ^ (-B) := by nlinarith
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hbpos.le _)
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 ^ k * d ^ M * c ^ (-B) * b ^ (-(A - k)) := by rw [hEb']

theorem model_decay (B k : ℝ) (hB : 0 < B) (hk : 0 ≤ k) :
    ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → ∃ C : ℝ, 0 ≤ C ∧
      (∀ T : ℝ, Integrable (modelIntegrand A k T)) ∧
      ∀ T : ℝ, ∫ p : ℝ × ℝ, modelIntegrand A k T p ≤ C * (1 + |T|) ^ (-B) := by
  obtain ⟨M, hM⟩ := exists_nat_ge (k + B)
  refine ⟨k + M + 2, fun A hA => ?_⟩
  have hgint : Integrable (fun t : ℝ => (1 + |t|) ^ (-(A - k))) := by
    have := integrable_one_add_norm (μ := volume) (E := ℝ) (r := A - k)
      (by norm_num; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)])
    simpa [Real.norm_eq_abs] using this
  have hfint := gaussPoly_integrable M
  have hfnn : ∀ u, 0 ≤ gaussPoly M u := fun u => by unfold gaussPoly; positivity
  have hgnn : ∀ t : ℝ, 0 ≤ (1 + |t|) ^ (-(A - k)) := fun t => by positivity
  have hmeas : ∀ T : ℝ, Measurable (modelIntegrand A k T) := fun T => by
    unfold modelIntegrand; fun_prop
  have hnn : ∀ T p, 0 ≤ modelIntegrand A k T p := fun T p => by
    unfold modelIntegrand; positivity
  have hprod : ∀ T : ℝ, Integrable (fun z : ℝ × ℝ =>
      (2 ^ k * (1 + |T|) ^ (-B)) * (gaussPoly M (T + z.1) * (1 + |z.2|) ^ (-(A - k)))) := by
    intro T
    apply Integrable.const_mul
    exact (hfint.comp_add_left T).mul_prod hgint
  have hpt : ∀ T : ℝ, ∀ p : ℝ × ℝ, modelIntegrand A k T p ≤
      (2 ^ k * (1 + |T|) ^ (-B)) * (gaussPoly M (T + p.1) * (1 + |p.2|) ^ (-(A - k))) := by
    intro T p
    have hcda : 1 + |T| ≤ (1 + |T + p.1|) * (1 + |p.1|) := by
      have h := abs_add_le (T + p.1) (-p.1)
      rw [abs_neg, show T + p.1 + -p.1 = T by ring] at h
      nlinarith [mul_nonneg (abs_nonneg (T + p.1)) (abs_nonneg p.1)]
    have hS : 2 + |p.1| + |p.2| + |T| ≤ 2 * (1 + |p.1|) * (1 + |p.2|) * (1 + |T|) := by
      nlinarith [abs_nonneg p.1, abs_nonneg p.2, abs_nonneg T, mul_nonneg (abs_nonneg p.1) (abs_nonneg p.2),
        mul_nonneg (abs_nonneg p.2) (abs_nonneg T), mul_nonneg (abs_nonneg p.1) (abs_nonneg T),
        mul_nonneg (mul_nonneg (abs_nonneg p.1) (abs_nonneg p.2)) (abs_nonneg T)]
    have key := pt_bound A k B M (1 + |p.1|) (1 + |p.2|) (1 + |T|) (1 + |T + p.1|)
      (2 + |p.1| + |p.2| + |T|) hk (by linarith [abs_nonneg p.1]) (by linarith [abs_nonneg p.2])
      (by linarith [abs_nonneg T]) (by linarith [abs_nonneg (T + p.1)]) hcda hA hM hB.le
      (by positivity) hS
    simp only [Real.rpow_natCast] at key
    have he := Real.exp_pos (-(T + p.1) ^ 2)
    unfold modelIntegrand gaussPoly
    calc Real.exp (-(T + p.1) ^ 2) * (1 + |p.1|) ^ (-A) * (1 + |p.2|) ^ (-A) *
          (2 + |p.1| + |p.2| + |T|) ^ k
        = Real.exp (-(T + p.1) ^ 2) * ((2 + |p.1| + |p.2| + |T|) ^ k * (1 + |p.1|) ^ (-A) *
          (1 + |p.2|) ^ (-A)) := by ring
      _ ≤ Real.exp (-(T + p.1) ^ 2) * (2 ^ k * (1 + |T + p.1|) ^ M * (1 + |T|) ^ (-B) *
          (1 + |p.2|) ^ (-(A - k))) := mul_le_mul_of_nonneg_left key he.le
      _ = (2 ^ k * (1 + |T|) ^ (-B)) * (Real.exp (-(T + p.1) ^ 2) * (1 + |T + p.1|) ^ M *
          (1 + |p.2|) ^ (-(A - k))) := by ring
  have hint : ∀ T : ℝ, Integrable (modelIntegrand A k T) := by
    intro T
    refine Integrable.mono' (hprod T) (hmeas T).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    rw [Real.norm_of_nonneg (hnn T p)]
    exact hpt T p
  refine ⟨2 ^ k * (∫ u, gaussPoly M u) * (∫ t : ℝ, (1 + |t|) ^ (-(A - k))), ?_, hint, ?_⟩
  · exact mul_nonneg (mul_nonneg (by positivity)
      (integral_nonneg hfnn)) (integral_nonneg hgnn)
  · intro T
    have hI := integral_mono (hint T) (hprod T) (by intro p; exact hpt T p)
    have h2 : ∫ z : ℝ × ℝ, gaussPoly M (T + z.1) * (1 + |z.2|) ^ (-(A - k)) =
        (∫ v, gaussPoly M (T + v)) * ∫ t : ℝ, (1 + |t|) ^ (-(A - k)) :=
      integral_prod_mul (fun v => gaussPoly M (T + v)) (fun t : ℝ => (1 + |t|) ^ (-(A - k)))
    have h3 : ∫ v, gaussPoly M (T + v) = ∫ u, gaussPoly M u :=
      integral_add_left_eq_self (gaussPoly M) T
    rw [integral_const_mul (2 ^ k * (1 + |T|) ^ (-B)), h2, h3] at hI
    refine le_trans hI (le_of_eq ?_)
    ring

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private lemma rpow_form (n : ℕ) (r C x : ℝ) (h : (1 + |r|) ^ n * x ≤ C) :
    x ≤ C * (1 + |r|) ^ (-(n : ℝ)) := by
  have hpos : (0 : ℝ) < 1 + |r| := by positivity
  rw [Real.rpow_neg hpos.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hpos n),
    mul_comm]
  exact h

def weightModulus (ξ : ℂ) (v y : ℝ) (p : ℝ × ℝ) : ℝ :=
  ‖Complex.exp ((ξ + ((v : ℂ) + (p.1 : ℂ) * Complex.I) - 1) ^ 2) *
    D.M ((v : ℂ) + (p.1 : ℂ) * Complex.I) * D.W1Hat ((y : ℂ) + (p.2 : ℂ) * Complex.I)‖

theorem weight_kernel_decay (a₁ b₁ a₂ b₂ x₀ x₁ : ℝ) (ha₁ : 0 < a₁) (hab₁ : a₁ ≤ b₁)
    (hab₂ : a₂ ≤ b₂) (hx : x₀ ≤ x₁) (B k : ℝ) (hB : 0 < B) (hk : 0 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℂ, x₀ ≤ ξ.re → ξ.re ≤ x₁ →
      ∀ v y : ℝ, a₁ ≤ v → v ≤ b₁ → a₂ ≤ y → y ≤ b₂ →
        Integrable (fun p : ℝ × ℝ =>
          weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k) ∧
        ∫ p : ℝ × ℝ, weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k
          ≤ C * (1 + |ξ.im|) ^ (-B) := by
  obtain ⟨A₀, hA₀⟩ := model_decay B k hB hk
  have hn : A₀ ≤ ((⌈A₀⌉₊ : ℕ) : ℝ) := Nat.le_ceil A₀
  obtain ⟨Cm, hCm0, hint, hbound⟩ := hA₀ ((⌈A₀⌉₊ : ℕ) : ℝ) hn
  obtain ⟨C₁, hC₁⟩ := D.M_vertical_decay a₁ b₁ ha₁ hab₁ ⌈A₀⌉₊
  obtain ⟨C₂, hC₂⟩ := D.W1Hat_vertical_decay a₂ b₂ hab₂ ⌈A₀⌉₊
  refine ⟨Real.exp ((|x₀ + a₁ - 1| + |x₁ + b₁ - 1|) ^ 2) * |C₁| * |C₂| * Cm, by positivity, ?_⟩
  intro ξ hx0 hx1 v y hv1 hv2 hy1 hy2
  have hexpb : ∀ s : ℝ, ‖Complex.exp ((ξ + ((v : ℂ) + (s : ℂ) * Complex.I) - 1) ^ 2)‖ ≤
      Real.exp ((|x₀ + a₁ - 1| + |x₁ + b₁ - 1|) ^ 2) * Real.exp (-(ξ.im + s) ^ 2) := by
    intro s
    rw [Complex.norm_exp]
    have hre : ((ξ + ((v : ℂ) + (s : ℂ) * Complex.I) - 1) ^ 2).re =
        (ξ.re + v - 1) ^ 2 - (ξ.im + s) ^ 2 := by
      simp [pow_two] <;> ring
    rw [hre, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq : (ξ.re + v - 1) ^ 2 ≤ (|x₀ + a₁ - 1| + |x₁ + b₁ - 1|) ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le (x₀ + a₁ - 1), abs_nonneg (x₁ + b₁ - 1)])
        (by linarith [le_abs_self (x₁ + b₁ - 1), abs_nonneg (x₀ + a₁ - 1)])
    linarith
  have hMn : ∀ s : ℝ, ‖D.M ((v : ℂ) + (s : ℂ) * Complex.I)‖ ≤
      |C₁| * (1 + |s|) ^ (-((⌈A₀⌉₊ : ℕ) : ℝ)) := by
    intro s
    have h := hC₁ ((v : ℂ) + (s : ℂ) * Complex.I) (by simpa using hv1) (by simpa using hv2)
    have h' : (1 + |s|) ^ ⌈A₀⌉₊ * ‖D.M ((v : ℂ) + (s : ℂ) * Complex.I)‖ ≤ |C₁| := by
      simpa using h.trans (le_abs_self _)
    exact rpow_form _ _ _ _ h'
  have hWn : ∀ t : ℝ, ‖D.W1Hat ((y : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      |C₂| * (1 + |t|) ^ (-((⌈A₀⌉₊ : ℕ) : ℝ)) := by
    intro t
    have h := hC₂ ((y : ℂ) + (t : ℂ) * Complex.I) (by simpa using hy1) (by simpa using hy2)
    have h' : (1 + |t|) ^ ⌈A₀⌉₊ * ‖D.W1Hat ((y : ℂ) + (t : ℂ) * Complex.I)‖ ≤ |C₂| := by
      simpa using h.trans (le_abs_self _)
    exact rpow_form _ _ _ _ h'
  have hpt : ∀ p : ℝ × ℝ,
      weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k ≤
        (Real.exp ((|x₀ + a₁ - 1| + |x₁ + b₁ - 1|) ^ 2) * |C₁| * |C₂|) *
          modelIntegrand ((⌈A₀⌉₊ : ℕ) : ℝ) k ξ.im p := by
    intro p
    unfold weightModulus modelIntegrand
    rw [norm_mul, norm_mul]
    have h1 := hexpb p.1
    have h2 := hMn p.1
    have h3 := hWn p.2
    have hS : 0 ≤ (2 + |p.1| + |p.2| + |ξ.im|) ^ k := by positivity
    calc ‖Complex.exp ((ξ + ((v : ℂ) + (p.1 : ℂ) * Complex.I) - 1) ^ 2)‖ *
          ‖D.M ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ *
          ‖D.W1Hat ((y : ℂ) + (p.2 : ℂ) * Complex.I)‖ * (2 + |p.1| + |p.2| + |ξ.im|) ^ k
        ≤ (Real.exp ((|x₀ + a₁ - 1| + |x₁ + b₁ - 1|) ^ 2) * Real.exp (-(ξ.im + p.1) ^ 2)) *
          (|C₁| * (1 + |p.1|) ^ (-((⌈A₀⌉₊ : ℕ) : ℝ))) *
          (|C₂| * (1 + |p.2|) ^ (-((⌈A₀⌉₊ : ℕ) : ℝ))) * (2 + |p.1| + |p.2| + |ξ.im|) ^ k := by
          gcongr
      _ = _ := by
          ring
  have hexp0 : Measurable fun p : ℝ × ℝ =>
      Complex.exp ((ξ + ((v : ℂ) + (p.1 : ℂ) * Complex.I) - 1) ^ 2) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Complex.exp ((ξ + ((v : ℂ) + (p.1 : ℂ) * Complex.I) - 1) ^ 2)).measurable
  have hMc : Continuous fun p : ℝ × ℝ => D.M ((v : ℂ) + (p.1 : ℂ) * Complex.I) :=
    D.M_differentiableOn.continuousOn.comp_continuous (by fun_prop)
      (fun p => by
        show 0 < ((v : ℂ) + (p.1 : ℂ) * Complex.I).re
        simp
        linarith)
  have hf1 : Measurable fun p : ℝ × ℝ => (y : ℂ) + (p.2 : ℂ) * Complex.I :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => (y : ℂ) + (p.2 : ℂ) * Complex.I).measurable
  have hWm := (PrincipalMellinComparison.principal_real_weight_measurable D.recipe).comp hf1
  have hwm : Measurable (weightModulus D ξ v y) := by
    unfold weightModulus
    exact Measurable.norm ((hexp0.mul hMc.measurable).mul hWm)
  have hmeas : Measurable fun p : ℝ × ℝ =>
      weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k :=
    hwm.mul ((by fun_prop : Continuous fun p : ℝ × ℝ => 2 + |p.1| + |p.2| + |ξ.im|).measurable.pow_const k)
  have hnn : ∀ p : ℝ × ℝ, 0 ≤ weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k := by
    intro p
    unfold weightModulus
    positivity
  have hKint := (hint ξ.im).const_mul
    (Real.exp ((|x₀ + a₁ - 1| + |x₁ + b₁ - 1|) ^ 2) * |C₁| * |C₂|)
  have hI : Integrable (fun p : ℝ × ℝ =>
      weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k) := by
    refine Integrable.mono' hKint hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    rw [Real.norm_of_nonneg (hnn p)]
    exact hpt p
  refine ⟨hI, ?_⟩
  calc ∫ p : ℝ × ℝ, weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k
      ≤ ∫ p : ℝ × ℝ, (Real.exp ((|x₀ + a₁ - 1| + |x₁ + b₁ - 1|) ^ 2) * |C₁| * |C₂|) *
          modelIntegrand ((⌈A₀⌉₊ : ℕ) : ℝ) k ξ.im p := integral_mono hI hKint hpt
    _ = (Real.exp ((|x₀ + a₁ - 1| + |x₁ + b₁ - 1|) ^ 2) * |C₁| * |C₂|) *
          ∫ p : ℝ × ℝ, modelIntegrand ((⌈A₀⌉₊ : ℕ) : ℝ) k ξ.im p := integral_const_mul _ _
    _ ≤ (Real.exp ((|x₀ + a₁ - 1| + |x₁ + b₁ - 1|) ^ 2) * |C₁| * |C₂|) *
          (Cm * (1 + |ξ.im|) ^ (-B)) :=
        mul_le_mul_of_nonneg_left (hbound _) (by positivity)
    _ = _ := by ring

theorem kernelWith_weight_eq (Fu : D.Row → ℂ → ℂ → ℂ → ℂ) (u : D.Row) (ξ w z : ℂ) (Z : ℝ) :
    PoissonKernel.kernelWith D Fu u ξ w z Z =
      (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z + (Scales.yExponent : ℂ) * (w - 1)) *
        (Complex.exp ((ξ + z - 1) ^ 2) * D.M z * D.W1Hat w) * (D.q u : ℂ) ^ (-z) *
          Fu u ξ w z := by
  unfold PoissonKernel.kernelWith; ring

end

end DedekindZetaZeroFree.Quantitative.WeightConvolution
