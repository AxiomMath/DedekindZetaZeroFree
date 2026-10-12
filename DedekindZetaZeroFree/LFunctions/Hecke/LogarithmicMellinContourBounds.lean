module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LogarithmicProductPrincipalParts
public import DedekindZetaZeroFree.Analysis.Gamma.ReciprocalStripGrowth
public import DedekindZetaZeroFree.Arithmetic.Ideals.InverseNormPowerSums
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LogarithmicStripDecayAndInversion
public import DedekindZetaZeroFree.LFunctions.Hecke.LocalContinuationAndFunctionalEquations

@[expose] public section

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.WeightedSeries.PoissonLogHeckeStrip

theorem completedGrowth
    (D : ℝ) (hD : 0 < D) (r n : ℕ) (U L : ℂ → ℂ)
    (hformula : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      L s = U s * (D : ℂ) ^ (-(s / 2)) *
        (Complex.Gammaℂ s)⁻¹ ^ r / (s * (s - 1)) ^ n)
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ,
      ‖U s‖ ≤ C * Real.exp (‖s‖ ^ (1 + ε)))
    {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}
    (hf : Vendor.LogMellinAdmissible f δ P H)
    (X : ℝ) (hX : 0 < X) (a b : ℝ) (haδ : -δ < a) (hab : a ≤ b) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc a b → 1 ≤ |t| →
        ‖Vendor.logMellinProduct H L X ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * Real.exp (A * Real.rpow (1 + |t|) (3 / 2 : ℝ)) := by
  obtain ⟨CU, hU⟩ := hgrowth (1 / 2) (by norm_num)
  obtain ⟨CG, AG, hCG, hAG, hG⟩ := Vendor.inverse_Gammaℂ_strip_exp_bound a b r
  obtain ⟨CH, hCH, hH⟩ := hf.rapid_vertical_decay a b haδ hab 0
  let B : ℝ := 1 + |a| + |b|
  let E : ℝ := Real.exp ((|Real.log X| + |Real.log D|) * B)
  have hB : 1 ≤ B := by dsimp [B]; linarith [abs_nonneg a, abs_nonneg b]
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hE : 0 ≤ E := Real.exp_nonneg _
  refine ⟨CH * E * (max CU 0 * CG), B ^ (3 / 2 : ℝ) + AG,
    by positivity, by positivity, ?_⟩
  intro σ t hσ ht
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hre : s.re = σ := by simp [s]
  have him : s.im = t := by simp [s]
  have hs0 : s ≠ 0 := by
    intro h
    have : t = 0 := by simpa [him] using congrArg Complex.im h
    norm_num [this] at ht
  have hs1 : s ≠ 1 := by
    intro h
    have : t = 0 := by simpa [him] using congrArg Complex.im h
    norm_num [this] at ht
  have hσabs : |σ| ≤ B := by
    apply abs_le.mpr
    have ha := neg_abs_le a
    have hb := le_abs_self b
    dsimp [B]
    constructor <;> linarith [hσ.1, hσ.2, abs_nonneg a, abs_nonneg b]
  have hH' : ‖H s‖ ≤ CH := by
    simpa [s] using hH σ t hσ.1 hσ.2 ht
  have hG' : ‖(Complex.Gammaℂ s)⁻¹‖ ^ r ≤ CG * Real.exp (AG * |t|) := by
    simpa [him] using hG s (by simpa [hre] using hσ)
  have hden : 1 ≤ ‖(s * (s - 1)) ^ n‖ := by
    rw [norm_pow, norm_mul]
    apply one_le_pow₀
    apply one_le_mul_of_one_le_of_one_le
    · exact ht.trans (by simpa [him] using Complex.abs_im_le_norm s)
    · exact ht.trans (by simpa [him] using Complex.abs_im_le_norm (s - 1))
  have hpowX : ‖(X : ℂ) ^ s‖ ≤ Real.exp (|Real.log X| * B) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, hre, Real.rpow_def_of_pos hX]
    apply Real.exp_le_exp.mpr
    calc Real.log X * σ ≤ |Real.log X * σ| := le_abs_self _
      _ = |Real.log X| * |σ| := abs_mul _ _
      _ ≤ |Real.log X| * B := mul_le_mul_of_nonneg_left hσabs (abs_nonneg _)
  have hpowD : ‖(D : ℂ) ^ (-(s / 2))‖ ≤ Real.exp (|Real.log D| * B) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hD, Real.rpow_def_of_pos hD]
    apply Real.exp_le_exp.mpr
    have he : (-(s / 2)).re = -(σ / 2) := by simp [div_eq_mul_inv, hre]
    have heabs : |(-(s / 2)).re| ≤ B := by
      rw [he, abs_neg, abs_div, show |(2 : ℝ)| = 2 by norm_num]
      linarith [abs_nonneg σ]
    calc Real.log D * (-(s / 2)).re ≤ |Real.log D * (-(s / 2)).re| := le_abs_self _
      _ = |Real.log D| * |(-(s / 2)).re| := abs_mul _ _
      _ ≤ |Real.log D| * B := mul_le_mul_of_nonneg_left heabs (abs_nonneg _)
  have hpow : ‖(X : ℂ) ^ s‖ * ‖(D : ℂ) ^ (-(s / 2))‖ ≤ E := by
    calc _ ≤ Real.exp (|Real.log X| * B) * Real.exp (|Real.log D| * B) :=
          mul_le_mul hpowX hpowD (norm_nonneg _) (Real.exp_nonneg _)
      _ = E := by dsimp [E]; rw [← Real.exp_add]; congr 1; ring
  have hnorm : ‖s‖ ≤ B * (1 + |t|) := by
    have hn := Complex.norm_le_abs_re_add_abs_im s
    rw [hre, him] at hn
    nlinarith [abs_nonneg t]
  have hS : 0 ≤ (1 + |t|) ^ (3 / 2 : ℝ) := by positivity
  have htS : |t| ≤ (1 + |t|) ^ (3 / 2 : ℝ) := by
    calc |t| ≤ 1 + |t| := by linarith
      _ ≤ (1 + |t|) ^ (3 / 2 : ℝ) := by
        simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 1 + |t| by linarith [abs_nonneg t])
          (show (1 : ℝ) ≤ 3 / 2 by norm_num)
  have hnormpow : ‖s‖ ^ (1 + (1 / 2 : ℝ)) ≤
      B ^ (3 / 2 : ℝ) * (1 + |t|) ^ (3 / 2 : ℝ) := by
    rw [show (1 + (1 / 2 : ℝ)) = 3 / 2 by norm_num]
    calc _ ≤ (B * (1 + |t|)) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) hnorm (by norm_num)
      _ = _ := Real.mul_rpow hB0 (by positivity)
  have hU' : ‖U s‖ ≤ max CU 0 *
      Real.exp (B ^ (3 / 2 : ℝ) * (1 + |t|) ^ (3 / 2 : ℝ)) := by
    calc _ ≤ CU * Real.exp (‖s‖ ^ (1 + (1 / 2 : ℝ))) := hU s
      _ ≤ max CU 0 * Real.exp (‖s‖ ^ (1 + (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hnormpow) (le_max_right _ _)
  have hUG : ‖U s‖ * ‖(Complex.Gammaℂ s)⁻¹‖ ^ r ≤
      (max CU 0 * CG) * Real.exp ((B ^ (3 / 2 : ℝ) + AG) *
        (1 + |t|) ^ (3 / 2 : ℝ)) := by
    calc _ ≤ (max CU 0 * Real.exp (B ^ (3 / 2 : ℝ) * (1 + |t|) ^ (3 / 2 : ℝ))) *
        (CG * Real.exp (AG * |t|)) :=
          mul_le_mul hU' hG' (by positivity) (by positivity)
      _ = (max CU 0 * CG) * Real.exp
          (B ^ (3 / 2 : ℝ) * (1 + |t|) ^ (3 / 2 : ℝ) + AG * |t|) := by
        rw [Real.exp_add]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left htS hAG]
  change ‖Vendor.logMellinProduct H L X s‖ ≤ _
  rw [Vendor.logMellinProduct, hformula s hs0 hs1, norm_mul, norm_mul,
    norm_div, norm_mul, norm_mul, norm_pow]
  calc _ ≤ ‖H s‖ * ‖(X : ℂ) ^ s‖ *
      (‖U s‖ * ‖(D : ℂ) ^ (-(s / 2))‖ * ‖(Complex.Gammaℂ s)⁻¹‖ ^ r) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_le_self (by positivity) hden
    _ = ‖H s‖ * (‖(X : ℂ) ^ s‖ * ‖(D : ℂ) ^ (-(s / 2))‖) *
        (‖U s‖ * ‖(Complex.Gammaℂ s)⁻¹‖ ^ r) := by ring
    _ ≤ CH * E * ((max CU 0 * CG) * Real.exp ((B ^ (3 / 2 : ℝ) + AG) *
        (1 + |t|) ^ (3 / 2 : ℝ))) := by
      apply mul_le_mul
      · exact mul_le_mul hH' hpow (by positivity) hCH
      · exact hUG
      · positivity
      · positivity
    _ = _ := by simp only [Real.rpow_eq_pow]; ring

end DedekindZetaZeroFree.LargeSieve.WeightedSeries.PoissonLogHeckeStrip

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped NumberField Classical Topology

namespace DedekindZetaZeroFree.LargeSieve.WeightedSeries.PoissonLogHeckeStrip

open Filter

private lemma patchPoint (R B : ℂ → ℂ) (p : ℂ) (S : Set ℂ)
    (hB : Vendor.HolomorphicNear B p) (heq : R =ᶠ[𝓝[≠] p] B)
    (hR : ∀ s ∈ S, s ≠ p → DifferentiableAt ℂ R s) :
    ∃ G : ℂ → ℂ, (∀ s ∈ S, DifferentiableAt ℂ G s) ∧ ∀ s, s ≠ p → G s = R s := by
  let G := Function.update R p (B p)
  have hGp : G =ᶠ[𝓝 p] B := by
    filter_upwards [eventually_nhdsWithin_iff.mp heq] with s hs
    by_cases hsp : s = p
    · subst s
      simp [G]
    · simpa [G, Function.update_of_ne hsp] using hs hsp
  have hGs : ∀ s, s ≠ p → G =ᶠ[𝓝 s] R := by
    intro s hs
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact Function.update_of_ne hz _ _
  refine ⟨G, ?_, fun s hs => Function.update_of_ne hs _ _⟩
  intro s hs
  by_cases hsp : s = p
  · subst s
    exact ((hB.self_of_nhds).congr_of_eventuallyEq hGp)
  · exact ((hR s hs hsp).congr_of_eventuallyEq (hGs s hsp))

private lemma powerDiff (X : ℝ) (hX : 0 < X) (s : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => (X : ℂ) ^ z) s :=
  (AnalyticAt.cpow analyticAt_const analyticAt_id
    (Complex.ofReal_mem_slitPlane.mpr hX)).differentiableAt

private lemma productDiff {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}
    (hf : Vendor.LogMellinAdmissible f δ P H) (L : ℂ → ℂ) (X : ℝ) (hX : 0 < X)
    (s : ℂ) (hs : -δ < s.re) (hs0 : s ≠ 0) (hL : DifferentiableAt ℂ L s) :
    DifferentiableAt ℂ (Vendor.logMellinProduct H L X) s := by
  exact ((hf.differentiableAt s hs hs0).mul (powerDiff X hX s)).mul hL

private lemma partDiff (c : ℕ → ℂ) (N : ℕ) (p s : ℂ) (hs : s ≠ p) :
    DifferentiableAt ℂ (fun z : ℂ => ∑ j ∈ Finset.Icc 1 N, c j / (z - p) ^ j) s := by
  refine DifferentiableAt.fun_sum fun j _ => ?_
  exact (differentiableAt_const _).div (by fun_prop) (pow_ne_zero _ (sub_ne_zero.mpr hs))

theorem principalContour
    (L : ℂ → ℂ) (hL : AnalyticOnNhd ℂ L ({1}ᶜ : Set ℂ)) (κ : ℂ)
    (hLp : Vendor.HasFinitePrincipalPart L 1 (fun _ => κ) 1)
    {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}
    (hf : Vendor.LogMellinAdmissible f δ P H) (X : ℝ) (hX : 0 < X) :
    DifferentiableOn ℂ (Vendor.logMellinProduct H L X)
        {s : ℂ | -δ < s.re ∧ s ≠ 0 ∧ s ≠ 1} ∧
      Vendor.HasFinitePrincipalPart (Vendor.logMellinProduct H L X) 0
        (Vendor.logProductPrincipalCoeff P X L) (P.natDegree + 1) ∧
      Vendor.HasFinitePrincipalPart (Vendor.logMellinProduct H L X) 1
        (fun _ => κ * (X : ℂ) * H 1) 1 ∧
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | -δ < s.re} ∧
        ∀ s : ℂ, -δ < s.re → s ≠ 0 → s ≠ 1 →
          G s = Vendor.logMellinProduct H L X s -
            (∑ j ∈ Finset.Icc 1 (P.natDegree + 1),
              Vendor.logProductPrincipalCoeff P X L j / s ^ j) -
            κ * (X : ℂ) * H 1 / (s - 1) := by
  have hL0 : Vendor.HolomorphicNear L 0 := by
    filter_upwards [isOpen_ne.mem_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with s hs
    exact (hL s hs).differentiableAt
  have hp0 := Vendor.logMellinProduct_principalPart_zero hf X hX L hL0
  have hp1 := Vendor.logMellinProduct_principalPart_one hf X hX L κ hLp
  have hdiff : ∀ s : ℂ, -δ < s.re → s ≠ 0 → s ≠ 1 →
      DifferentiableAt ℂ (Vendor.logMellinProduct H L X) s := by
    intro s hs hs0 hs1
    exact productDiff hf L X hX s hs hs0 (hL s hs1).differentiableAt
  refine ⟨fun s hs => (hdiff s hs.1 hs.2.1 hs.2.2).differentiableWithinAt, hp0, hp1, ?_⟩
  let C := κ * (X : ℂ) * H 1
  let Q0 := fun s : ℂ => ∑ j ∈ Finset.Icc 1 (P.natDegree + 1),
    Vendor.logProductPrincipalCoeff P X L j / s ^ j
  let Q1 := fun s : ℂ => C / (s - 1)
  let R := fun s : ℂ => Vendor.logMellinProduct H L X s - Q0 s - Q1 s
  have hQ0 : ∀ s : ℂ, s ≠ 0 → DifferentiableAt ℂ Q0 s := by
    intro s hs
    simpa [Q0] using partDiff (Vendor.logProductPrincipalCoeff P X L) (P.natDegree + 1) 0 s hs
  have hQ1 : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ Q1 s := by
    intro s hs
    exact (differentiableAt_const C).div (by fun_prop) (sub_ne_zero.mpr hs)
  obtain ⟨B0, hB0, heq0⟩ := hp0
  obtain ⟨B1, hB1, heq1⟩ := hp1
  have hnear0 : Vendor.HolomorphicNear (fun s => B0 s - Q1 s) 0 := by
    filter_upwards [hB0, isOpen_ne.mem_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with s hb hs
    exact hb.sub (hQ1 s hs)
  have heqR0 : R =ᶠ[𝓝[≠] 0] (fun s => B0 s - Q1 s) := by
    filter_upwards [heq0] with s hs
    simp only [sub_zero] at hs
    dsimp [R, Q0]
    rw [hs]
    ring
  obtain ⟨G0, hG0, heqG0⟩ := patchPoint R (fun s => B0 s - Q1 s) 0
    {s : ℂ | -δ < s.re ∧ s ≠ 1} hnear0 heqR0 (by
      intro s hs hs0
      exact ((hdiff s hs.1 hs0 hs.2).sub (hQ0 s hs0)).sub (hQ1 s hs.2))
  have hnear1 : Vendor.HolomorphicNear (fun s => B1 s - Q0 s) 1 := by
    filter_upwards [hB1, isOpen_ne.mem_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with s hb hs
    exact hb.sub (hQ0 s hs)
  have havoid0 : ∀ᶠ s : ℂ in 𝓝 (1 : ℂ), s ≠ 0 :=
    isOpen_ne.mem_nhds (show (1 : ℂ) ≠ 0 by norm_num)
  have heqR1 : G0 =ᶠ[𝓝[≠] 1] (fun s => B1 s - Q0 s) := by
    filter_upwards [heq1, havoid0.filter_mono nhdsWithin_le_nhds]
      with s hs hs0
    rw [heqG0 s hs0]
    simp only [Finset.Icc_self, Finset.sum_singleton, pow_one] at hs
    dsimp [R, Q1, C]
    rw [hs]
    ring
  obtain ⟨G, hG, heqG⟩ := patchPoint G0 (fun s => B1 s - Q0 s) 1
    {s : ℂ | -δ < s.re} hnear1 heqR1 (by
      intro s hs hs1
      exact hG0 s ⟨hs, hs1⟩)
  refine ⟨G, fun s hs => (hG s hs).differentiableWithinAt, ?_⟩
  intro s hs hs0 hs1
  rw [heqG s hs1, heqG0 s hs0]

end DedekindZetaZeroFree.LargeSieve.WeightedSeries.PoissonLogHeckeStrip

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.WeightedSeries.PoissonLogHeckeStrip

theorem positiveLine
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F) → ℂ) (hc : ∀ I, ‖c I‖ ≤ 1) (L : ℂ → ℂ)
    (hseries : ∀ s : ℂ, 1 < s.re →
      L s = ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
        c I * (Ideal.absNorm I : ℂ) ^ (-s))
    (hhol : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ L s)
    {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}
    (hf : Vendor.LogMellinAdmissible f δ P H)
    (X : ℝ) (hX : 0 < X) (b : ℝ) (hb : 1 < b) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ t : ℝ, ‖L ((b : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B) ∧
      Complex.VerticalIntegrable (Vendor.logMellinProduct H L X) b MeasureTheory.volume := by
  let a : Ideal (𝓞 F) → ℝ := fun I =>
    if I = ⊥ then 0 else (Ideal.absNorm I : ℝ) ^ (-b)
  have ha : Summable a := DedekindZetaZeroFree.LargeSieve.summable_ideal_inverse_power F b hb
  have ha0 : ∀ I, 0 ≤ a I := by
    intro I
    dsimp [a]
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hterm : ∀ (t : ℝ) (I : Ideal (𝓞 F)),
      ‖(if I = ⊥ then 0 else
        c I * (Ideal.absNorm I : ℂ) ^ (-((b : ℂ) + (t : ℂ) * Complex.I)))‖ ≤ a I := by
    intro t I
    by_cases hI : I = ⊥
    · simp [hI, a]
    · have hn : 0 < (Ideal.absNorm I : ℝ) := by
        have hn0 : Ideal.absNorm I ≠ 0 := fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz)
        exact_mod_cast Nat.pos_of_ne_zero hn0
      simp only [if_neg hI, a, norm_mul]
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn]
      simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hc I) (Real.rpow_nonneg hn.le (-b))
  let B : ℝ := ∑' I, a I
  have hB : 0 ≤ B := tsum_nonneg ha0
  have hbound : ∀ t : ℝ, ‖L ((b : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B := by
    intro t
    have hs : 1 < ((b : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hb
    rw [hseries _ hs]
    have hnorm : Summable (fun I : Ideal (𝓞 F) =>
        ‖(if I = ⊥ then 0 else
          c I * (Ideal.absNorm I : ℂ) ^ (-((b : ℂ) + (t : ℂ) * Complex.I)))‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm t) ha
    exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum (hterm t) ha)
  refine ⟨B, hB, hbound, ?_⟩
  have hLc : Continuous (fun t : ℝ => L ((b : ℂ) + (t : ℂ) * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact (hhol _ (by simpa using hb)).continuousAt.comp
      (continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const))
  haveI : NeZero (X : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hX.ne'⟩
  have hXc : Continuous (fun t : ℝ => (X : ℂ) ^ ((b : ℂ) + (t : ℂ) * Complex.I)) :=
    (continuous_const_cpow (X : ℂ)).comp (by fun_prop)
  have hXbound : ∀ t : ℝ,
      ‖(X : ℂ) ^ ((b : ℂ) + (t : ℂ) * Complex.I)‖ ≤ X ^ b := by
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp
  have hH : MeasureTheory.Integrable
      (fun t : ℝ => H ((b : ℂ) + (t : ℂ) * Complex.I)) MeasureTheory.volume :=
    hf.verticalIntegrable b (by linarith)
  have hHX := hH.mul_bdd hXc.aestronglyMeasurable (Filter.Eventually.of_forall hXbound)
  exact hHX.mul_bdd hLc.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

end DedekindZetaZeroFree.LargeSieve.WeightedSeries.PoissonLogHeckeStrip

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.WeightedSeries.PoissonLogHeckeStrip

theorem negativeLine
    (D : ℝ) (hD : 0 < D) (r : ℕ) (W : ℂ) (hW : ‖W‖ ≤ 1)
    (L Lbar : ℂ → ℂ)
    (hFE : ∀ s : ℂ, s.re < 0 →
      L s = W * (D : ℂ) ^ ((1 / 2 : ℂ) - s) *
        Complex.Gammaℂ (1 - s) ^ r * (Complex.Gammaℂ s)⁻¹ ^ r * Lbar (1 - s))
    (hhol : ∀ s : ℂ, s.re < 0 → DifferentiableAt ℂ L s)
    {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}
    (hf : Vendor.LogMellinAdmissible f δ P H)
    (X : ℝ) (hX : 0 < X) (a : ℝ) (haδ : -δ < a) (ha : a < 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hbar : ∀ t : ℝ,
      ‖Lbar (1 - ((a : ℂ) + (t : ℂ) * Complex.I))‖ ≤ B) :
    Complex.VerticalIntegrable (Vendor.logMellinProduct H L X) a MeasureTheory.volume := by
  let z : ℝ → ℂ := fun t => (a : ℂ) + (t : ℂ) * Complex.I
  have hzre (t : ℝ) : (z t).re = a := by simp [z]
  have hz0 (t : ℝ) : z t ≠ 0 := by
    intro h
    have : a = 0 := by simpa [hzre] using congrArg Complex.re h
    linarith
  have hzcont : Continuous z := by unfold z; fun_prop
  have hcont : Continuous (fun t : ℝ => Vendor.logMellinProduct H L X (z t)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hH := hf.differentiableAt (z t) (by rw [hzre]; exact haδ) (hz0 t)
    have hL := hhol (z t) (by rw [hzre]; exact ha)
    have hpow : DifferentiableAt ℂ (fun s : ℂ => (X : ℂ) ^ s) (z t) :=
      differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
    exact ((hH.mul hpow).mul hL).continuousAt.comp hzcont.continuousAt
  obtain ⟨C, k, hC, hgamma⟩ :=
    Vendor.gammaQuotient_polynomial_bound (by linarith : 0 < 1 - a) le_rfl r
  have hgamma' (t : ℝ) :
      ‖Complex.Gammaℂ (1 - z t) ^ r * (Complex.Gammaℂ (z t))⁻¹ ^ r‖ ≤
        C * (1 + |t|) ^ k := by
    have hg := hgamma (1 - z t) (by simp [hzre]) (by simp [hzre])
    simpa [div_eq_mul_inv, mul_pow, z] using hg
  have hDpow (t : ℝ) : ‖(D : ℂ) ^ ((1 / 2 : ℂ) - z t)‖ = D ^ (1 / 2 - a) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]
    congr 1
    simp [hzre]
  have hXpow (t : ℝ) : ‖(X : ℂ) ^ z t‖ = X ^ a := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, hzre]
  have hLbound (t : ℝ) : ‖L (z t)‖ ≤
      (D ^ (1 / 2 - a) * C * B) * (1 + |t|) ^ k := by
    rw [hFE (z t) (by rw [hzre]; exact ha)]
    rw [show W * (D : ℂ) ^ ((1 / 2 : ℂ) - z t) *
        Complex.Gammaℂ (1 - z t) ^ r * (Complex.Gammaℂ (z t))⁻¹ ^ r * Lbar (1 - z t) =
        (W * (D : ℂ) ^ ((1 / 2 : ℂ) - z t)) *
          (Complex.Gammaℂ (1 - z t) ^ r * (Complex.Gammaℂ (z t))⁻¹ ^ r) * Lbar (1 - z t) by ring]
    simp only [norm_mul, hDpow]
    rw [← norm_mul (Complex.Gammaℂ (1 - z t) ^ r) ((Complex.Gammaℂ (z t))⁻¹ ^ r)]
    calc ‖W‖ * D ^ (1 / 2 - a) *
          ‖Complex.Gammaℂ (1 - z t) ^ r * (Complex.Gammaℂ (z t))⁻¹ ^ r‖ * ‖Lbar (1 - z t)‖
        ≤ (1 * D ^ (1 / 2 - a)) * (C * (1 + |t|) ^ k) * B :=
          mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hW (by positivity))
            (hgamma' t) (norm_nonneg _) (by positivity))
            (hbar t) (norm_nonneg _) (by positivity)
      _ = (D ^ (1 / 2 - a) * C * B) * (1 + |t|) ^ k := by ring
  let A : ℝ := X ^ a * (D ^ (1 / 2 - a) * C * B)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hprod (t : ℝ) : ‖Vendor.logMellinProduct H L X (z t)‖ ≤
      A * ((1 + |t|) ^ k * ‖H (z t)‖) := by
    simp only [Vendor.logMellinProduct, norm_mul, hXpow]
    calc ‖H (z t)‖ * X ^ a * ‖L (z t)‖
        ≤ (‖H (z t)‖ * X ^ a) * ((D ^ (1 / 2 - a) * C * B) * (1 + |t|) ^ k) :=
          mul_le_mul_of_nonneg_left (hLbound t) (by positivity)
      _ = A * ((1 + |t|) ^ k * ‖H (z t)‖) := by dsimp [A]; ring
  obtain ⟨CH, hCH, hdec⟩ := hf.rapid_vertical_decay a a haδ le_rfl (k + 2)
  have htail (t : ℝ) (ht : 1 ≤ |t|) :
      ‖Vendor.logMellinProduct H L X (z t)‖ ≤ (A * CH) * ((1 + |t|) ^ 2)⁻¹ := by
    have hb := hdec a t le_rfl le_rfl ht
    change (1 + |t|) ^ (k + 2) * ‖H (z t)‖ ≤ CH at hb
    have hm := mul_le_mul_of_nonneg_left (hprod t) (show 0 ≤ (1 + |t|) ^ 2 by positivity)
    have hb' : (1 + |t|) ^ 2 * ‖Vendor.logMellinProduct H L X (z t)‖ ≤ A * CH := by
      calc (1 + |t|) ^ 2 * ‖Vendor.logMellinProduct H L X (z t)‖
          ≤ (1 + |t|) ^ 2 * (A * ((1 + |t|) ^ k * ‖H (z t)‖)) := hm
        _ = A * ((1 + |t|) ^ (k + 2) * ‖H (z t)‖) := by rw [pow_add]; ring
        _ ≤ A * CH := mul_le_mul_of_nonneg_left hb hA
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < (1 + |t|) ^ 2)]
    nlinarith [hb']
  obtain ⟨C1, hC1⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hcont.continuousOn (s := Set.Icc (-1) 1))
  let K : ℝ := 4 * (A * CH + max C1 0)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbound (t : ℝ) : ‖Vendor.logMellinProduct H L X (z t)‖ ≤ K * (1 + t ^ 2)⁻¹ := by
    have hstep : ((1 + |t|) ^ 2)⁻¹ ≤ (1 + t ^ 2)⁻¹ := by
      have hle : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
      simpa only [one_div] using one_div_le_one_div_of_le (show 0 < 1 + t ^ 2 by positivity) hle
    by_cases ht : 1 ≤ |t|
    · have hCK : A * CH ≤ K := by dsimp [K]; nlinarith [mul_nonneg hA hCH, le_max_right C1 0]
      exact (htail t ht).trans ((mul_le_mul_of_nonneg_right hCK (by positivity)).trans
        (mul_le_mul_of_nonneg_left hstep hK))
    · have ht' : |t| < 1 := not_le.mp ht
      have hb := hC1 t (show t ∈ Set.Icc (-1) 1 from
        ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩)
      have h4 : (1 + |t|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg t, sq_abs t, sq_nonneg t]
      have hinv : (4 : ℝ)⁻¹ ≤ ((1 + |t|) ^ 2)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le
          (show 0 < (1 + |t|) ^ 2 by positivity) h4
      have hCK : C1 ≤ K * (4 : ℝ)⁻¹ := by
        dsimp [K]
        have := le_max_left C1 0
        nlinarith [mul_nonneg hA hCH]
      exact hb.trans (hCK.trans ((mul_le_mul_of_nonneg_left hinv hK).trans
        (mul_le_mul_of_nonneg_left hstep hK)))
  show MeasureTheory.Integrable (fun t : ℝ => Vendor.logMellinProduct H L X (z t)) MeasureTheory.volume
  exact MeasureTheory.Integrable.mono' (integrable_inv_one_add_sq.const_mul K)
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

end DedekindZetaZeroFree.LargeSieve.WeightedSeries.PoissonLogHeckeStrip

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped NumberField Classical Topology

namespace DedekindZetaZeroFree.LargeSieve

theorem principalLogMellinProduct_boundary_integrable
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}
    (hf : Vendor.LogMellinAdmissible f δ P H)
    (X : ℝ) (hX : 0 < X) (a b : ℝ)
    (haδ : -δ < a) (ha : a < 0) (hb : 1 < b) :
    Complex.VerticalIntegrable
        (Vendor.logMellinProduct H (principalZetaContinuation F hF) X)
        a MeasureTheory.volume ∧
      Complex.VerticalIntegrable
        (Vendor.logMellinProduct H (principalZetaContinuation F hF) X)
        b MeasureTheory.volume := by
  have hhol : ∀ s : ℂ, s ≠ 1 →
      DifferentiableAt ℂ (principalZetaContinuation F hF) s := by
    intro s hs
    exact (principalZetaContinuation_analyticOnNhd F hF s (by simpa using hs)).differentiableAt
  have hseries : ∀ s : ℂ, 1 < s.re →
      principalZetaContinuation F hF s =
        ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
          (1 : ℂ) * (Ideal.absNorm I : ℂ) ^ (-s) := by
    intro s hs
    simpa using principalZetaContinuation_eq_dirichlet F hF s hs
  have hright : ∀ s : ℂ, 1 < s.re →
      DifferentiableAt ℂ (principalZetaContinuation F hF) s := by
    intro s hs
    apply hhol s
    intro h
    simpa [h] using hs
  obtain ⟨_, _, _, hbint⟩ := WeightedSeries.PoissonLogHeckeStrip.positiveLine F
    (fun _ => 1) (by intro I; simp) _ hseries hright hf X hX b hb
  obtain ⟨B, hB, hbound, _⟩ := WeightedSeries.PoissonLogHeckeStrip.positiveLine F
    (fun _ => 1) (by intro I; simp) _ hseries hright hf X hX (1 - a) (by linarith)
  refine ⟨?_, hbint⟩
  apply WeightedSeries.PoissonLogHeckeStrip.negativeLine
    (principalDiscriminant F) (principalDiscriminant_pos F)
    (principalComplexPlaces F) 1 (by simp)
    (principalZetaContinuation F hF) (principalZetaContinuation F hF)
    (by intro s hs; simpa using principalZetaContinuation_functional_equation F hF s hs)
    (by
      intro s hs
      apply hhol s
      intro h
      have hs' : (1 : ℝ) < 0 := by simpa [h] using hs
      linarith)
    hf X hX a haδ ha B hB
  intro t
  convert hbound (-t) using 1 <;> congr 1 <;> push_cast <;> ring

theorem principalLogMellinProduct_subquadratic_growth
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}
    (hf : Vendor.LogMellinAdmissible f δ P H)
    (X : ℝ) (hX : 0 < X) (a b : ℝ)
    (haδ : -δ < a) (ha : a < 0) (hb : 1 < b) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc a b → 1 ≤ |t| →
        ‖Vendor.logMellinProduct H (principalZetaContinuation F hF) X
            ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * Real.exp (A * Real.rpow (1 + |t|) (3 / 2 : ℝ)) := by
  apply WeightedSeries.PoissonLogHeckeStrip.completedGrowth
    (principalDiscriminant F) (principalDiscriminant_pos F) (principalComplexPlaces F) 1
    (principalHeckeData F hF).E (principalZetaContinuation F hF)
    (by
      intro s hs0 hs1
      simpa using principalZetaContinuation_eq F hF s hs0 hs1)
    (principalHeckeData F hF).E_growth hf X hX a b haδ
  linarith

theorem principalLogMellinProduct_contour_data
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}
    (hf : Vendor.LogMellinAdmissible f δ P H) (X : ℝ) (hX : 0 < X) :
    DifferentiableOn ℂ
        (Vendor.logMellinProduct H (principalZetaContinuation F hF) X)
        {s : ℂ | -δ < s.re ∧ s ≠ 0 ∧ s ≠ 1} ∧
      Vendor.HasFinitePrincipalPart
        (Vendor.logMellinProduct H (principalZetaContinuation F hF) X) 0
        (Vendor.logProductPrincipalCoeff P X (principalZetaContinuation F hF))
        (P.natDegree + 1) ∧
      Vendor.HasFinitePrincipalPart
        (Vendor.logMellinProduct H (principalZetaContinuation F hF) X) 1
        (fun _ => principalZetaResidueCoefficient F hF * (X : ℂ) * H 1) 1 ∧
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | -δ < s.re} ∧
        ∀ s : ℂ, -δ < s.re → s ≠ 0 → s ≠ 1 →
          G s = Vendor.logMellinProduct H (principalZetaContinuation F hF) X s -
            (∑ j ∈ Finset.Icc 1 (P.natDegree + 1),
              Vendor.logProductPrincipalCoeff P X
                (principalZetaContinuation F hF) j / s ^ j) -
            principalZetaResidueCoefficient F hF * (X : ℂ) * H 1 / (s - 1) := by
  have hp : Vendor.HasFinitePrincipalPart (principalZetaContinuation F hF) 1
      (fun _ => principalZetaResidueCoefficient F hF) 1 := by
    obtain ⟨R, hR, hEq⟩ := principalZetaContinuation_local_pole F hF
    refine ⟨R, Complex.analyticAt_iff_eventually_differentiableAt.mp hR, ?_⟩
    filter_upwards [hEq] with s hs
    simpa using (sub_eq_iff_eq_add.mp hs)
  exact WeightedSeries.PoissonLogHeckeStrip.principalContour
    (principalZetaContinuation F hF)
    (principalZetaContinuation_analyticOnNhd F hF)
    (principalZetaResidueCoefficient F hF) hp hf X hX

end DedekindZetaZeroFree.LargeSieve

end

end
