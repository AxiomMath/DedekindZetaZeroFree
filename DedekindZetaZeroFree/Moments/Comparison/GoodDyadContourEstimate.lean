module

public import DedekindZetaZeroFree.Moments.Comparison.OrdinaryDyadContourEstimate

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open MeasureTheory Complex

def comparisonTruncatedFrequencyIntegral {ι : Type*}
    (q : ι → ℝ) (M W : ℂ → ℂ) (E : ι → ℂ → ℂ → ℂ → ℂ)
    (C : Finset ι) (Z σξ σw σz T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ ^ 3 *
    ∫ t : ℝ × ℝ × ℝ in {t : ℝ × ℝ × ℝ | |t.1| ≤ T},
      ∑ u ∈ C, comparisonFrequencyKernel q M W E Z u
        ((σξ : ℂ) + (t.1 : ℂ) * Complex.I)
        ((σw : ℂ) + (t.2.1 : ℂ) * Complex.I)
        ((σz : ℂ) + (t.2.2 : ℂ) * Complex.I)

private lemma goodDyad_weighted_convolution (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      Integrable (fun p : ℝ × ℝ =>
        comparisonHeightEnvelope (A + D + 2) t p.1 p.2 * (2 + |t|)^D) ∧
      (∫ p : ℝ × ℝ, comparisonHeightEnvelope (A + D + 2) t p.1 p.2 *
        (2 + |t|)^D) ≤ C * (1 + |t|)^(-(A+2)) := by
  obtain ⟨C, hC, hb⟩ := comparisonHeightEnvelope_convolution (A+D) (by linarith)
  refine ⟨C * 2^D, by positivity, ?_⟩
  intro t
  have hp : (2+|t|)^D ≤ 2^D*(1+|t|)^D := by
    calc
      _ ≤ (2*(1+|t|))^D := Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg t]) hD
      _ = _ := Real.mul_rpow (by positivity) (by positivity)
  refine ⟨(hb t).1.mul_const _, ?_⟩
  rw [integral_mul_const]
  calc
    _ ≤ (C*(1+|t|)^(-(A+D+2))) * (2^D*(1+|t|)^D) :=
      mul_le_mul (hb t).2 hp (by positivity) (by positivity)
    _ = (C*2^D) * (1+|t|)^(-(A+2)) := by
      rw [show -(A+2) = -(A+D+2)+D by ring, Real.rpow_add (by positivity)]
      ring

private lemma goodDyad_weighted_integrable (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    Integrable (fun p : ℝ × ℝ × ℝ =>
      comparisonHeightEnvelope (A + D + 2) p.1 p.2.1 p.2.2 * (2 + |p.1|)^D) := by
  obtain ⟨C, hC, hb⟩ := goodDyad_weighted_convolution A D hA hD
  have hi : Integrable (fun t : ℝ => (1+|t|)^(-(A+2))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := A+2) (by simp; linarith))
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ =>
      comparisonHeightEnvelope (A + D + 2) p.1 p.2.1 p.2.2 * (2 + |p.1|)^D) volume := by
    unfold comparisonHeightEnvelope
    apply Measurable.aestronglyMeasurable
    fun_prop
  apply (integrable_prod_iff hm).mpr
  refine ⟨Filter.Eventually.of_forall (fun t => (hb t).1), ?_⟩
  apply (hi.const_mul C).mono' hm.norm.integral_prod_right'
  filter_upwards [] with t
  have heq : (fun p : ℝ × ℝ => ‖comparisonHeightEnvelope (A+D+2) t p.1 p.2 * (2+|t|)^D‖) =
      (fun p : ℝ × ℝ => comparisonHeightEnvelope (A+D+2) t p.1 p.2 * (2+|t|)^D) := by
    funext p
    exact Real.norm_of_nonneg (by unfold comparisonHeightEnvelope; positivity)
  rw [heq]
  rw [Real.norm_of_nonneg (integral_nonneg (fun p => by unfold comparisonHeightEnvelope; positivity))]
  exact (hb t).2

private lemma goodDyad_kernel_norm {ι : Type*} (q : ι → ℝ) (M W : ℂ → ℂ)
    (E : ι → ℂ → ℂ → ℂ → ℂ) (Z : ℝ) (u : ι) (ξ w z : ℂ)
    (hZ : 0 < Z) (hq : 0 < q u) :
    ‖comparisonFrequencyKernel q M W E Z u ξ w z‖ =
      Z ^ comparisonE ξ.re w.re z.re * ‖comparisonGaussianMellinWeight M W ξ w z‖ *
        (q u)^(-z.re) * ‖E u ξ w z‖ := by
  unfold comparisonFrequencyKernel comparisonGaussianMellinWeight
  simp only [norm_mul, comparisonRealPower_norm Z hZ, comparisonRealPower_norm (q u) hq,
    Complex.neg_re]
  have he : ((comparisonA : ℂ)/2 + ξ - 1 + (comparisonH₀ : ℂ)*z +
      (comparisonB : ℂ)*(w-1)).re = comparisonE ξ.re w.re z.re := by
    simp [comparisonE, Complex.mul_re, Complex.div_re]
  rw [he]
  ring

private lemma goodDyad_left_kernel_bound {ι : Type*} (principal : ι) (q : ι → ℝ)
    (M W : ℂ → ℂ) (E P : ι → ℂ → ℂ → ℂ → ℂ) (L : ι → ℂ → ℂ)
    (good : ℝ → ι → Prop) (D : ℝ) (hD : 0 ≤ D)
    (hM : comparisonRapidStripDecay M (2/5) 2)
    (hW : comparisonRapidStripDecay W (3/1000) 4)
    (hfactor : ∀ u ξ w z, u ≠ principal →
      ξ ∈ comparisonClosedStrip (499/500) comparisonSigma₁ →
      w.re = 3/1000 → z.re = 2/5 → L u ξ ≠ 0 → E u ξ w z = P u ξ w z / L u ξ)
    (hP : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 0 < B ∧
      ∀ u ξ w z, u ≠ principal → 1 ≤ q u →
      ξ ∈ comparisonClosedStrip (499/500) comparisonSigma₁ →
      w.re = 3/1000 → z.re = 2/5 →
      ‖P u ξ w z‖ ≤ B*(q u)^(1/2+δ)*(2+|ξ.im|)^D*(2+|w.im|)^D*(2+|z.im|)^D)
    (ρ : ℝ)
    (hdet : ∀ δ : ℝ, 0 < δ → ∃ B Udet : ℝ, 0 < B ∧ 1 ≤ Udet ∧
      ∀ U u, Udet ≤ U → good U u → U ≤ q u → q u < 2*U →
      ∀ ξ : ℂ, 499/500 ≤ ξ.re → |ξ.im| ≤ 2*U^ρ →
      L u ξ ≠ 0 ∧ ‖(L u ξ)⁻¹‖ ≤ B*U^δ)
    (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ B Udet : ℝ, 0 < B ∧ 1 ≤ Udet ∧ ∀ U Z u ξ w z,
      Udet ≤ U → 1 ≤ Z → u ≠ principal → good U u → U ≤ q u → q u < 2*U →
      ξ ∈ comparisonClosedStrip (499/500) comparisonSigma₁ →
      |ξ.im| ≤ 2*U^ρ → w.re = 3/1000 → z.re = 2/5 →
      ‖comparisonFrequencyKernel q M W E Z u ξ w z‖ ≤
        B * Z^(comparisonE ξ.re (3/1000) (2/5)) * (q u)^(1/10+δ) * U^δ *
          (comparisonHeightEnvelope (A+D+2) ξ.im w.im z.im * (2+|ξ.im|)^D) := by
  obtain ⟨BP, hBP, hPb⟩ := hP δ hδ
  obtain ⟨BL, Udet, hBL, hUdet, hLb⟩ := hdet δ hδ
  obtain ⟨BW, hBW, hWb⟩ := comparisonGaussianMellinWeight_polynomial_bound
    M W (499/500) comparisonSigma₁ (3/1000) 4 (2/5) 2 (A+D+2) D D
    (by norm_num [comparisonSigma₁, comparisonDelta]) (by norm_num) (by norm_num)
    (by norm_num) (by linarith) hD hD hM hW
  refine ⟨BP*BL*BW, Udet, by positivity, hUdet, ?_⟩
  intro U Z u ξ w z hU hZ hu hg hqu hqu' hξ ht hw hz
  have hUpos : 0 < U := by linarith
  have hqpos : 0 < q u := by linarith
  have hZpos : 0 < Z := by linarith
  have hξlo : 499/500 ≤ ξ.re := hξ.1
  obtain ⟨hLnz, hLnorm⟩ := hLb U u hU hg hqu hqu' ξ hξlo ht
  have hwmem : w ∈ comparisonClosedStrip (3/1000) 4 := by
    rw [comparisonClosedStrip]; constructor <;> rw [hw] <;> norm_num
  have hzmem : z ∈ comparisonClosedStrip (2/5) 2 := by
    rw [comparisonClosedStrip]; constructor <;> rw [hz] <;> norm_num
  have hPnorm := hPb u ξ w z hu (by linarith : 1 ≤ q u) hξ hw hz
  have hWnorm := hWb ξ w z hξ hwmem hzmem
  have hEnorm : ‖E u ξ w z‖ ≤ BP * (q u)^(1/2+δ) *
      (2+|ξ.im|)^D*(2+|w.im|)^D*(2+|z.im|)^D * (BL*U^δ) := by
    rw [hfactor u ξ w z hu hξ hw hz hLnz, div_eq_mul_inv, norm_mul]
    exact mul_le_mul hPnorm hLnorm (norm_nonneg _) (by positivity)
  rw [goodDyad_kernel_norm q M W E Z u ξ w z hZpos hqpos, hw, hz]
  have hQ : (q u)^(-(2/5:ℝ)) * (q u)^(1/2+δ) = (q u)^(1/10+δ) := by
    rw [← Real.rpow_add hqpos]; congr 1; ring
  have hnonneg : 0 ≤ comparisonHeightEnvelope (A+D+2) ξ.im w.im z.im := by
    unfold comparisonHeightEnvelope; positivity
  calc
    _ ≤ Z^(comparisonE ξ.re (3/1000) (2/5)) *
      ‖comparisonGaussianMellinWeight M W ξ w z‖ * (q u)^(-(2/5:ℝ)) *
      (BP*(q u)^(1/2+δ)*(2+|ξ.im|)^D*(2+|w.im|)^D*(2+|z.im|)^D*(BL*U^δ)) :=
        mul_le_mul_of_nonneg_left hEnorm (by positivity)
    _ = (BP*BL) * Z^(comparisonE ξ.re (3/1000) (2/5)) *
        (q u)^(1/10+δ)*U^δ * (2+|ξ.im|)^D *
        (‖comparisonGaussianMellinWeight M W ξ w z‖*(2+|w.im|)^D*(2+|z.im|)^D) := by
      rw [← hQ]; ring
    _ ≤ (BP*BL) * Z^(comparisonE ξ.re (3/1000) (2/5)) *
        (q u)^(1/10+δ)*U^δ * (2+|ξ.im|)^D *
        (BW*comparisonHeightEnvelope (A+D+2) ξ.im w.im z.im) :=
      mul_le_mul_of_nonneg_left hWnorm (by positivity)
    _ = _ := by ring

private lemma goodDyad_truncated_bound {ι : Type*} (q : ι → ℝ) (principal : ι)
    (M W : ℂ → ℂ) (E : ι → ℂ → ℂ → ℂ → ℂ)
    (D : ℝ) (hD : 0 ≤ D) (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) :
    ∃ H : ℝ, 0 < H ∧ ∀ Z U T B : ℝ, ∀ C : Finset ι,
      1 ≤ Z → 1 ≤ U → 0 ≤ B → comparisonFrequencyDyad q principal K U C →
      (∀ u ∈ C, ∀ t τ ν : ℝ, |t| ≤ T →
        ‖comparisonFrequencyKernel q M W E Z u
          (((499/500:ℝ):ℂ) + (t:ℂ)*Complex.I)
          (((3/1000:ℝ):ℂ) + (τ:ℂ)*Complex.I)
          (((2/5:ℝ):ℂ) + (ν:ℂ)*Complex.I)‖ ≤
          B * Z^(comparisonE (499/500) (3/1000) (2/5)) * (q u)^(1/10+δ)*U^δ *
            (comparisonHeightEnvelope (D+2) t τ ν * (2+|t|)^D)) →
      ‖comparisonTruncatedFrequencyIntegral q M W E C Z
        (499/500) (3/1000) (2/5) T‖ ≤
          H*B*Z^(comparisonE (499/500) (3/1000) (2/5))*U^(11/10+2*δ) := by
  let F : ℝ × ℝ × ℝ → ℝ := fun p =>
    comparisonHeightEnvelope (D+2) p.1 p.2.1 p.2.2 * (2+|p.1|)^D
  have hi : Integrable F := by
    simpa [F] using goodDyad_weighted_integrable 0 D (by norm_num) hD
  have hF : ∀ p, 0 ≤ F p := by intro p; dsimp [F, comparisonHeightEnvelope]; positivity
  let c : ℝ := ‖(2*(Real.pi:ℂ))⁻¹^3‖
  let J : ℝ := ∫ p, F p
  have hc : 0 ≤ c := norm_nonneg _
  have hJ : 0 ≤ J := integral_nonneg hF
  refine ⟨c*K*2^(1/10+δ)*J + 1, by positivity, ?_⟩
  intro Z U T B C hZ hU hB hdy hb
  have hUpos : 0 < U := by linarith
  have hZpos : 0 < Z := by linarith
  let a := comparisonE (499/500) (3/1000) (2/5)
  let V := B*Z^a*K*2^(1/10+δ)*U^(11/10+2*δ)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hsum : ∀ p : ℝ × ℝ × ℝ, |p.1| ≤ T →
      ‖∑ u ∈ C, comparisonFrequencyKernel q M W E Z u
        (((499/500:ℝ):ℂ) + (p.1:ℂ)*Complex.I)
        (((3/1000:ℝ):ℂ) + (p.2.1:ℂ)*Complex.I)
        (((2/5:ℝ):ℂ) + (p.2.2:ℂ)*Complex.I)‖ ≤ V*F p := by
    intro p hp
    have hq : ∀ u ∈ C, (q u)^(1/10+δ) ≤ (2*U)^(1/10+δ) := by
      intro u hu
      exact Real.rpow_le_rpow (by linarith [(hdy.1 u hu).2.1])
        (hdy.1 u hu).2.2.le (by linarith)
    calc
      _ ≤ ∑ u ∈ C, ‖comparisonFrequencyKernel q M W E Z u
        (((499/500:ℝ):ℂ) + (p.1:ℂ)*Complex.I)
        (((3/1000:ℝ):ℂ) + (p.2.1:ℂ)*Complex.I)
        (((2/5:ℝ):ℂ) + (p.2.2:ℂ)*Complex.I)‖ := norm_sum_le _ _
      _ ≤ ∑ u ∈ C, B*Z^a*(2*U)^(1/10+δ)*U^δ*F p := by
        apply Finset.sum_le_sum
        intro u hu
        exact (hb u hu p.1 p.2.1 p.2.2 hp).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hq u hu) (by positivity))
              (by positivity)) (hF p))
      _ = (C.card:ℝ) * (B*Z^a*(2*U)^(1/10+δ)*U^δ*F p) := by simp
      _ ≤ (K*U) * (B*Z^a*(2*U)^(1/10+δ)*U^δ*F p) :=
        mul_le_mul_of_nonneg_right hdy.2 (mul_nonneg (by positivity) (hF p))
      _ = V*F p := by
        dsimp [V]
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        have he : U*U^(1/10+δ)*U^δ = U^(11/10+2*δ) := by
          conv_lhs => lhs; lhs; rw [← Real.rpow_one U]
          rw [← Real.rpow_add hUpos, ← Real.rpow_add hUpos]
          congr 1; ring
        rw [← he]; ring
  have hnorm : ‖∫ p : ℝ × ℝ × ℝ in {p | |p.1| ≤ T},
      ∑ u ∈ C, comparisonFrequencyKernel q M W E Z u
        (((499/500:ℝ):ℂ) + (p.1:ℂ)*Complex.I)
        (((3/1000:ℝ):ℂ) + (p.2.1:ℂ)*Complex.I)
        (((2/5:ℝ):ℂ) + (p.2.2:ℂ)*Complex.I)‖ ≤ V*J := by
    calc
      _ ≤ ∫ p in {p : ℝ × ℝ × ℝ | |p.1| ≤ T}, V*F p :=
        norm_integral_le_of_norm_le (hi.const_mul V).integrableOn
          ((ae_restrict_mem (by measurability)).mono (fun p hp => hsum p hp))
      _ ≤ ∫ p, V*F p := setIntegral_le_integral (hi.const_mul V)
        (Filter.Eventually.of_forall (fun p => mul_nonneg hV (hF p)))
      _ = V*J := integral_const_mul _ _
  unfold comparisonTruncatedFrequencyIntegral
  rw [norm_mul]
  have hh := mul_le_mul_of_nonneg_left hnorm hc
  dsimp [V, a, c] at hh ⊢
  calc
    _ ≤ c*(V*J) := hh
    _ ≤ _ := by
      dsimp [V, a, c, J]
      nlinarith [mul_nonneg hB (mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Z) a)
        (Real.rpow_nonneg (by linarith : 0 ≤ U) (11/10+2*δ)))]

private lemma goodDyad_central_estimate {ι : Type*} (principal : ι) (q : ι → ℝ)
    (M W : ℂ → ℂ) (E P : ι → ℂ → ℂ → ℂ → ℂ) (L : ι → ℂ → ℂ)
    (good : ℝ → ι → Prop) (D : ℝ) (hD : 0 ≤ D)
    (hM : comparisonRapidStripDecay M (2/5) 2)
    (hW : comparisonRapidStripDecay W (3/1000) 4)
    (hfactor : ∀ u ξ w z, u ≠ principal →
      ξ ∈ comparisonClosedStrip (499/500) comparisonSigma₁ →
      w.re = 3/1000 → z.re = 2/5 → L u ξ ≠ 0 → E u ξ w z = P u ξ w z / L u ξ)
    (hP : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 0 < B ∧
      ∀ u ξ w z, u ≠ principal → 1 ≤ q u →
      ξ ∈ comparisonClosedStrip (499/500) comparisonSigma₁ →
      w.re = 3/1000 → z.re = 2/5 →
      ‖P u ξ w z‖ ≤ B*(q u)^(1/2+δ)*(2+|ξ.im|)^D*(2+|w.im|)^D*(2+|z.im|)^D)
    (ρ : ℝ)
    (hdet : ∀ δ : ℝ, 0 < δ → ∃ B Udet : ℝ, 0 < B ∧ 1 ≤ Udet ∧
      ∀ U u, Udet ≤ U → good U u → U ≤ q u → q u < 2*U →
      ∀ ξ : ℂ, 499/500 ≤ ξ.re → |ξ.im| ≤ 2*U^ρ →
      L u ξ ≠ 0 ∧ ‖(L u ξ)⁻¹‖ ≤ B*U^δ)
    (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε) :
    ∃ Bcentral Udet : ℝ, 0 < Bcentral ∧ 1 ≤ Udet ∧
      ∀ Z U C, 1 ≤ Z → Udet ≤ U → comparisonFrequencyDyad q principal K U C →
      (∀ u ∈ C, good U u) →
      ‖comparisonTruncatedFrequencyIntegral q M W E C Z
        (499/500) (3/1000) (2/5) (U^ρ)‖ ≤
        Bcentral * Z^(comparisonE (499/500) (3/1000) (2/5)) * U^(11/10+ε) := by
  obtain ⟨B, Udet, hB, hUdet, hb⟩ := goodDyad_left_kernel_bound
    principal q M W E P L good D hD hM hW hfactor hP ρ hdet 0 (ε/2)
    (by norm_num) (by linarith)
  obtain ⟨H, hH, hHb⟩ := goodDyad_truncated_bound q principal M W E D hD K (ε/2) hK (by linarith)
  refine ⟨H*B, Udet, by positivity, hUdet, ?_⟩
  intro Z U C hZ hU hdy hg
  have hh := hHb Z U (U^ρ) B C hZ (hUdet.trans hU) hB.le hdy ?_
  · simpa only [show 2 * (ε / 2) = ε by ring] using hh
  intro u hu t τ ν ht
  have hmem : (((499/500:ℝ):ℂ)+(t:ℂ)*Complex.I) ∈
      comparisonClosedStrip (499/500) comparisonSigma₁ := by
    norm_num [comparisonClosedStrip, comparisonSigma₁, comparisonDelta]
  have hh := hb U Z u
    (((499/500:ℝ):ℂ)+(t:ℂ)*Complex.I)
    (((3/1000:ℝ):ℂ)+(τ:ℂ)*Complex.I)
    (((2/5:ℝ):ℂ)+(ν:ℂ)*Complex.I)
    hU hZ (hdy.1 u hu).1 (hg u hu) (hdy.1 u hu).2.1 (hdy.1 u hu).2.2
    hmem (by simpa using ht.trans (by have : 0 ≤ U^ρ := Real.rpow_nonneg (by linarith) _; linarith))
    (by simp) (by simp)
  simpa using hh

private lemma goodDyad_rectangle_norm (a b T : ℝ) (f : ℂ → (ℝ × ℝ) → ℂ)
    (hab : a < b) (hT : 0 < T)
    (hhol : ∀ p, DifferentiableOn ℂ (fun s => f s p)
      {s : ℂ | a ≤ s.re ∧ s.re ≤ b ∧ -T ≤ s.im ∧ s.im ≤ T})
    (ha : Integrable (fun p : ℝ × ℝ => ∫ t : ℝ in -T..T, f ((a:ℂ)+(t:ℂ)*I) p))
    (hb : Integrable (fun p : ℝ × ℝ => ∫ t : ℝ in -T..T, f ((b:ℂ)+(t:ℂ)*I) p))
    (hedge : Integrable (fun p : ℝ × ℝ => ∫ x : ℝ in a..b,
      ‖f ((x:ℂ)+(-T:ℝ)*I) p‖ + ‖f ((x:ℂ)+(T:ℂ)*I) p‖))
    (hbottom : ∀ p, IntervalIntegrable (fun x : ℝ => f ((x:ℂ)+(-T:ℝ)*I) p) volume a b)
    (htop : ∀ p, IntervalIntegrable (fun x : ℝ => f ((x:ℂ)+(T:ℂ)*I) p) volume a b) :
    ‖(∫ p : ℝ × ℝ, ∫ t : ℝ in -T..T, f ((b:ℂ)+(t:ℂ)*I) p) -
      (∫ p : ℝ × ℝ, ∫ t : ℝ in -T..T, f ((a:ℂ)+(t:ℂ)*I) p)‖ ≤
      ∫ p : ℝ × ℝ, ∫ x : ℝ in a..b,
        ‖f ((x:ℂ)+(-T:ℝ)*I) p‖ + ‖f ((x:ℂ)+(T:ℂ)*I) p‖ := by
  rw [← integral_sub hb ha]
  apply norm_integral_le_of_norm_le hedge
  filter_upwards [] with p
  have hrect := verticalIntegral_rectangle_difference a b T (fun s => f s p) hab hT (hhol p)
  rw [norm_sub_rev]
  rw [hrect, norm_mul, norm_neg, norm_I, one_mul]
  calc
    _ ≤ ‖∫ x : ℝ in a..b, f ((x:ℂ)+(-T:ℝ)*I) p‖ +
      ‖∫ x : ℝ in a..b, f ((x:ℂ)+(T:ℂ)*I) p‖ := norm_sub_le _ _
    _ ≤ (∫ x : ℝ in a..b, ‖f ((x:ℂ)+(-T:ℝ)*I) p‖) +
      (∫ x : ℝ in a..b, ‖f ((x:ℂ)+(T:ℂ)*I) p‖) :=
        add_le_add (intervalIntegral.norm_integral_le_integral_norm hab.le)
          (intervalIntegral.norm_integral_le_integral_norm hab.le)
    _ = _ := (intervalIntegral.integral_add (hbottom p).norm (htop p).norm).symm

private lemma goodDyad_product_rectangle_norm (a b T : ℝ) (f : ℂ → (ℝ × ℝ) → ℂ)
    (hab : a < b) (hT : 0 < T)
    (hhol : ∀ p, DifferentiableOn ℂ (fun s => f s p)
      {s : ℂ | a ≤ s.re ∧ s.re ≤ b ∧ -T ≤ s.im ∧ s.im ≤ T})
    (ha : Integrable (fun p : ℝ × ℝ × ℝ => f ((a:ℂ)+(p.1:ℂ)*I) p.2)
      ((volume.restrict (Set.Ioc (-T) T)).prod volume))
    (hb : Integrable (fun p : ℝ × ℝ × ℝ => f ((b:ℂ)+(p.1:ℂ)*I) p.2)
      ((volume.restrict (Set.Ioc (-T) T)).prod volume))
    (hbottom : Integrable (fun p : ℝ × ℝ × ℝ => f ((p.1:ℂ)+(-T:ℝ)*I) p.2)
      ((volume.restrict (Set.Ioc a b)).prod volume))
    (htop : Integrable (fun p : ℝ × ℝ × ℝ => f ((p.1:ℂ)+(T:ℂ)*I) p.2)
      ((volume.restrict (Set.Ioc a b)).prod volume)) :
    ‖(∫ p : ℝ × ℝ × ℝ in Set.Ioc (-T) T ×ˢ Set.univ, f ((b:ℂ)+(p.1:ℂ)*I) p.2) -
      (∫ p : ℝ × ℝ × ℝ in Set.Ioc (-T) T ×ˢ Set.univ, f ((a:ℂ)+(p.1:ℂ)*I) p.2)‖ ≤
      ∫ p : ℝ × ℝ × ℝ in Set.Ioc a b ×ˢ Set.univ,
        ‖f ((p.1:ℂ)+(-T:ℝ)*I) p.2‖ + ‖f ((p.1:ℂ)+(T:ℂ)*I) p.2‖ := by
  rw [Measure.volume_eq_prod, ← Measure.restrict_prod_eq_prod_univ,
    ← Measure.restrict_prod_eq_prod_univ]
  rw [integral_prod_symm _ hb, integral_prod_symm _ ha]
  have hn : Integrable (fun p : ℝ × ℝ × ℝ =>
      ‖f ((p.1:ℂ)+(-T:ℝ)*I) p.2‖ + ‖f ((p.1:ℂ)+(T:ℂ)*I) p.2‖)
      ((volume.restrict (Set.Ioc a b)).prod volume) := hbottom.norm.add htop.norm
  rw [integral_prod_symm _ hn]
  simp_rw [← intervalIntegral.integral_of_le (by linarith : -T ≤ T),
    ← intervalIntegral.integral_of_le hab.le]
  apply goodDyad_rectangle_norm a b T f hab hT hhol
  · simpa only [intervalIntegral.integral_of_le (by linarith : -T ≤ T)] using ha.integral_prod_right
  · simpa only [intervalIntegral.integral_of_le (by linarith : -T ≤ T)] using hb.integral_prod_right
  · simpa only [intervalIntegral.integral_of_le hab.le] using hn.integral_prod_right
  · intro p
    apply ContinuousOn.intervalIntegrable
    apply (hhol p).continuousOn.comp (by fun_prop : ContinuousOn (fun x : ℝ => (x:ℂ)+(-T:ℝ)*I) (Set.uIcc a b))
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    simpa using And.intro hx.1 (And.intro hx.2 (And.intro (le_refl (-T)) (by linarith : -T ≤ T)))
  · intro p
    apply ContinuousOn.intervalIntegrable
    apply (hhol p).continuousOn.comp (by fun_prop : ContinuousOn (fun x : ℝ => (x:ℂ)+(T:ℂ)*I) (Set.uIcc a b))
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    simpa using And.intro hx.1 (And.intro hx.2 (And.intro (by linarith : -T ≤ T) (le_refl T)))

private lemma goodDyad_truncate_fubini (f : ℝ → (ℝ × ℝ) → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hi : Integrable (fun p : ℝ × ℝ × ℝ => f p.1 p.2)
      (volume.restrict {p : ℝ × ℝ × ℝ | |p.1| ≤ T})) :
    (∫ p : ℝ × ℝ × ℝ in {p | |p.1| ≤ T}, f p.1 p.2) =
      ∫ p : ℝ × ℝ, ∫ t : ℝ in -T..T, f t p := by
  have hs : {p : ℝ × ℝ × ℝ | |p.1| ≤ T} = Set.Icc (-T) T ×ˢ Set.univ := by
    ext p; simp [abs_le]
  rw [hs, Measure.volume_eq_prod, ← Measure.restrict_prod_eq_prod_univ] at hi ⊢
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  exact integral_Icc_eq_integral_Ioc

private lemma goodDyad_envelope_tail (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t : ℝ in {t | T < |t|},
        (∫ p : ℝ × ℝ, comparisonHeightEnvelope (A+D+4) t p.1 p.2) * (2+|t|)^D) ≤
      C*T^(-A) := by
  obtain ⟨C, hC, hb⟩ := comparisonHeightEnvelope_convolution_xiHeight (A+2) D (by linarith) hD
  let w₀ : ℝ → ℝ := fun t => (1+|t|)^(-(2:ℝ))
  have hw : Integrable w₀ := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp))
  have hJ : 0 ≤ ∫ t, w₀ t := integral_nonneg (fun t => by dsimp [w₀]; positivity)
  refine ⟨C*(∫ t, w₀ t)+1, by positivity, ?_⟩
  intro T hT
  have hTp : 0 < T := by linarith

  have hm : ∀ t : ℝ, T < |t| →
      (1+|t|)^(-(A+2)) ≤ T^(-A)*w₀ t := by
    intro t ht
    have hh := Real.rpow_le_rpow_of_nonpos hTp
      (by linarith : T ≤ 1+|t|) (by linarith : -A ≤ 0)
    rw [show -(A+2) = -A + -(2:ℝ) by ring, Real.rpow_add (by positivity)]
    exact mul_le_mul_of_nonneg_right hh (by positivity)
  have henv : ∀ t : ℝ, (∫ p : ℝ × ℝ,
      comparisonHeightEnvelope (A+D+4) t p.1 p.2)*(2+|t|)^D ≤ C*(1+|t|)^(-(A+2)) := by
    intro t
    simpa only [show A+2+D+2 = A+D+4 by ring] using (hb t).2
  calc
    _ ≤ ∫ t : ℝ in {t | T < |t|}, (C*T^(-A))*w₀ t :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => by
        apply mul_nonneg
        · apply integral_nonneg; intro p; unfold comparisonHeightEnvelope; positivity
        · positivity)) ((hw.const_mul _).integrableOn)
        ((ae_restrict_mem (by measurability)).mono (fun t ht => by
          exact (henv t).trans (by
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hm t ht) hC.le)))
    _ ≤ ∫ t : ℝ, (C*T^(-A))*w₀ t := setIntegral_le_integral (hw.const_mul _)
      (Filter.Eventually.of_forall (fun t => by dsimp [w₀]; positivity))
    _ = C*(∫ t, w₀ t)*T^(-A) := by rw [integral_const_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

private lemma goodDyad_exterior_tail_norm (f : ℝ → (ℝ × ℝ) → ℂ) (T : ℝ)
    (hi : Integrable (fun p : ℝ × ℝ × ℝ => f p.1 p.2)) :
    ‖(∫ p : ℝ × ℝ × ℝ, f p.1 p.2) -
      (∫ p : ℝ × ℝ × ℝ in {p | |p.1| ≤ T}, f p.1 p.2)‖ ≤
      ∫ t : ℝ in {t | T < |t|}, ∫ p : ℝ × ℝ, ‖f t p‖ := by
  rw [← setIntegral_compl (by measurability) hi]
  have hs : {p : ℝ × ℝ × ℝ | |p.1| ≤ T}ᶜ = {t : ℝ | T < |t|} ×ˢ Set.univ := by
    ext p; simp
  rw [hs]
  calc
    _ ≤ ∫ p : ℝ × ℝ × ℝ in {t : ℝ | T < |t|} ×ˢ Set.univ, ‖f p.1 p.2‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      rw [Measure.volume_eq_prod, ← Measure.restrict_prod_eq_prod_univ]
      have hn : Integrable (fun p : ℝ × ℝ × ℝ => ‖f p.1 p.2‖)
          ((volume.restrict {t : ℝ | T < |t|}).prod volume) := by
        rw [Measure.restrict_prod_eq_prod_univ, ← Measure.volume_eq_prod]
        exact hi.norm.integrableOn
      exact integral_prod _ hn

private lemma goodDyad_rectangle_with_exterior (a b T : ℝ) (f : ℂ → (ℝ × ℝ) → ℂ)
    (hab : a < b) (hT : 0 < T)
    (hhol : ∀ p, DifferentiableOn ℂ (fun s => f s p)
      {s : ℂ | a ≤ s.re ∧ s.re ≤ b ∧ -T ≤ s.im ∧ s.im ≤ T})
    (ha : Integrable (fun p : ℝ × ℝ × ℝ => f ((a:ℂ)+(p.1:ℂ)*I) p.2)
      (volume.restrict {p : ℝ × ℝ × ℝ | |p.1| ≤ T}))
    (hb : Integrable (fun p : ℝ × ℝ × ℝ => f ((b:ℂ)+(p.1:ℂ)*I) p.2))
    (hbottom : Integrable (fun p : ℝ × ℝ × ℝ => f ((p.1:ℂ)+(-T:ℝ)*I) p.2)
      ((volume.restrict (Set.Ioc a b)).prod volume))
    (htop : Integrable (fun p : ℝ × ℝ × ℝ => f ((p.1:ℂ)+(T:ℂ)*I) p.2)
      ((volume.restrict (Set.Ioc a b)).prod volume)) :
    ‖(∫ p : ℝ × ℝ × ℝ, f ((b:ℂ)+(p.1:ℂ)*I) p.2) -
      (∫ p : ℝ × ℝ × ℝ in {p | |p.1| ≤ T}, f ((a:ℂ)+(p.1:ℂ)*I) p.2)‖ ≤
      (∫ p : ℝ × ℝ × ℝ in Set.Ioc a b ×ˢ Set.univ,
        ‖f ((p.1:ℂ)+(-T:ℝ)*I) p.2‖ + ‖f ((p.1:ℂ)+(T:ℂ)*I) p.2‖) +
      (∫ t : ℝ in {t | T < |t|}, ∫ p : ℝ × ℝ, ‖f ((b:ℂ)+(t:ℂ)*I) p‖) := by
  have ha' : Integrable (fun p : ℝ × ℝ × ℝ => f ((a:ℂ)+(p.1:ℂ)*I) p.2)
      ((volume.restrict (Set.Ioc (-T) T)).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ, ← Measure.volume_eq_prod]
    apply IntegrableOn.mono_set ha
    intro p hp
    exact abs_le.mpr ⟨hp.1.1.le, hp.1.2⟩
  have hb' : Integrable (fun p : ℝ × ℝ × ℝ => f ((b:ℂ)+(p.1:ℂ)*I) p.2)
      ((volume.restrict (Set.Ioc (-T) T)).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ, ← Measure.volume_eq_prod]
    exact hb.integrableOn
  have heqa : (∫ p : ℝ × ℝ × ℝ in {p | |p.1| ≤ T}, f ((a:ℂ)+(p.1:ℂ)*I) p.2) =
      ∫ p : ℝ × ℝ × ℝ in Set.Ioc (-T) T ×ˢ Set.univ, f ((a:ℂ)+(p.1:ℂ)*I) p.2 := by
    rw [goodDyad_truncate_fubini (fun t p => f ((a:ℂ)+(t:ℂ)*I) p) T hT.le ha]
    conv_rhs => rw [Measure.volume_eq_prod, ← Measure.restrict_prod_eq_prod_univ, integral_prod_symm _ ha']
    simp_rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  have heqb : (∫ p : ℝ × ℝ × ℝ in {p | |p.1| ≤ T}, f ((b:ℂ)+(p.1:ℂ)*I) p.2) =
      ∫ p : ℝ × ℝ × ℝ in Set.Ioc (-T) T ×ˢ Set.univ, f ((b:ℂ)+(p.1:ℂ)*I) p.2 := by
    rw [goodDyad_truncate_fubini (fun t p => f ((b:ℂ)+(t:ℂ)*I) p) T hT.le hb.integrableOn]
    conv_rhs => rw [Measure.volume_eq_prod, ← Measure.restrict_prod_eq_prod_univ, integral_prod_symm _ hb']
    simp_rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  have hr := goodDyad_product_rectangle_norm a b T f hab hT hhol ha' hb' hbottom htop
  rw [← heqa, ← heqb] at hr
  have ht := goodDyad_exterior_tail_norm (fun t p => f ((b:ℂ)+(t:ℂ)*I) p) T hb
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (∫ p : ℝ × ℝ × ℝ in {p | |p.1| ≤ T}, f ((b:ℂ)+(p.1:ℂ)*I) p.2) _).trans
    ((add_le_add ht hr).trans_eq (add_comm _ _))

lemma comparisonGoodDyad_original_envelope_bound {ι : Type*}
    (q : ι → ℝ) (principal : ι) (M W : ℂ → ℂ) (E : ι → ℂ → ℂ → ℂ → ℂ)
    (hM : comparisonRapidStripDecay M (2/5) 2)
    (hW : comparisonRapidStripDecay W (3/1000) 4)
    (d : ℝ) (hd : 0 ≤ d)
    (hE : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 0 < B ∧ ∀ u, u ≠ principal → 1 ≤ q u →
      ∀ ξ w z, ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
      w ∈ comparisonClosedStrip (3/1000) 4 → z ∈ comparisonClosedStrip (2/5) 2 →
      ‖E u ξ w z‖ ≤ B*(q u)^(1/2+δ)*(2+|w.im|)^d)
    (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 < B ∧ ∀ Z u ξ w z,
      1 ≤ Z → u ≠ principal → 1 ≤ q u → ξ.re = comparisonSigma₁ →
      w.re = 3/1000 → z.re = 2/5 →
      ‖comparisonFrequencyKernel q M W E Z u ξ w z‖ ≤
        B*Z^comparisonE comparisonSigma₁ (3/1000) (2/5)*(q u)^(1/10+δ)*
          comparisonHeightEnvelope (A+4) ξ.im w.im z.im := by
  obtain ⟨BE, hBE, hEb⟩ := hE δ hδ
  obtain ⟨BW, hBW, hWb⟩ := comparisonGaussianMellinWeight_polynomial_bound
    M W comparisonSigma₁ 4 (3/1000) 4 (2/5) 2 (A+4) d 0
    (by norm_num [comparisonSigma₁, comparisonDelta]) (by norm_num) (by norm_num)
    (by norm_num) (by linarith) hd (by norm_num) hM hW
  refine ⟨BE*BW, by positivity, ?_⟩
  intro Z u ξ w z hZ hu hq hξ hw hz
  have hξm : ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 := by
    norm_num [comparisonClosedStrip, hξ, comparisonSigma₁, comparisonDelta]
  have hwm : w ∈ comparisonClosedStrip (3/1000) 4 := by norm_num [comparisonClosedStrip, hw]
  have hzm : z ∈ comparisonClosedStrip (2/5) 2 := by norm_num [comparisonClosedStrip, hz]
  have he := hEb u hu hq ξ w z hξm hwm hzm
  have hweight : ‖comparisonGaussianMellinWeight M W ξ w z‖*(2+|w.im|)^d ≤
      BW*comparisonHeightEnvelope (A+4) ξ.im w.im z.im := by
    simpa using hWb ξ w z hξm hwm hzm
  have hqp : 0 < q u := by linarith
  have hQ : (q u)^(-(2/5:ℝ)) * (q u)^(1/2+δ) = (q u)^(1/10+δ) := by
    rw [← Real.rpow_add hqp]; congr 1; ring
  rw [goodDyad_kernel_norm q M W E Z u ξ w z (by linarith) hqp, hξ, hw, hz]
  calc
    _ ≤ Z^comparisonE comparisonSigma₁ (3/1000) (2/5)*
        ‖comparisonGaussianMellinWeight M W ξ w z‖*(q u)^(-(2/5:ℝ))*
        (BE*(q u)^(1/2+δ)*(2+|w.im|)^d) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = BE*Z^comparisonE comparisonSigma₁ (3/1000) (2/5)*(q u)^(1/10+δ)*
        (‖comparisonGaussianMellinWeight M W ξ w z‖*(2+|w.im|)^d) := by rw [← hQ]; ring
    _ ≤ BE*Z^comparisonE comparisonSigma₁ (3/1000) (2/5)*(q u)^(1/10+δ)*
        (BW*comparisonHeightEnvelope (A+4) ξ.im w.im z.im) :=
      mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = _ := by ring

lemma comparisonGoodDyad_envelope_tail_domination (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T B : ℝ) (f : ℝ → (ℝ × ℝ) → ℂ),
      1 ≤ T → 0 ≤ B →
      (∀ t p, ‖f t p‖ ≤ B * comparisonHeightEnvelope (A+D+4) t p.1 p.2 * (2+|t|)^D) →
      (∫ t : ℝ in {t | T < |t|}, ∫ p : ℝ × ℝ, ‖f t p‖) ≤ B*C*T^(-A) := by
  obtain ⟨C, hC, hb⟩ := goodDyad_envelope_tail A D hA hD
  refine ⟨C, hC, ?_⟩
  intro T B f hT hB hf
  have hi := goodDyad_weighted_integrable (A+2) D (by linarith) hD
  rw [Measure.volume_eq_prod] at hi
  have hi' : Integrable (fun t : ℝ => (∫ p : ℝ × ℝ,
      comparisonHeightEnvelope (A+D+4) t p.1 p.2)*(2+|t|)^D) := by
    simpa only [show A+2+D+2 = A+D+4 by ring, integral_mul_const] using hi.integral_prod_left
  have hp (t : ℝ) : Integrable (fun p : ℝ × ℝ =>
      comparisonHeightEnvelope (A+D+4) t p.1 p.2) := by
    obtain ⟨c, hc, hb⟩ := comparisonHeightEnvelope_convolution (A+D+2) (by linarith)
    simpa only [show A+D+2+2 = A+D+4 by ring] using (hb t).1
  calc
    _ ≤ ∫ t : ℝ in {t | T < |t|}, B*((∫ p : ℝ × ℝ,
        comparisonHeightEnvelope (A+D+4) t p.1 p.2)*(2+|t|)^D) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun t => integral_nonneg (fun p => norm_nonneg _)))
        (hi'.const_mul B).integrableOn
      filter_upwards [] with t
      calc
        _ ≤ ∫ p : ℝ × ℝ, B*comparisonHeightEnvelope (A+D+4) t p.1 p.2*(2+|t|)^D :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun p => norm_nonneg _))
            (((hp t).const_mul B).mul_const _) (Filter.Eventually.of_forall (hf t))
        _ = _ := by rw [integral_mul_const, integral_const_mul]; ring
    _ = B*(∫ t : ℝ in {t | T < |t|},
        (∫ p : ℝ × ℝ, comparisonHeightEnvelope (A+D+4) t p.1 p.2)*(2+|t|)^D) := integral_const_mul _ _
    _ ≤ _ := by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hb T hT) hB

lemma comparisonGoodDyad_horizontal_envelope_domination (A D : ℝ)
    (hA : 0 ≤ A) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b T B : ℝ) (f : ℂ → (ℝ × ℝ) → ℂ),
      a ≤ b → 1 ≤ T → 0 ≤ B →
      (∀ x ∈ Set.Ioc a b, ∀ p, ∀ t ∈ ({-T, T} : Set ℝ),
        ‖f ((x:ℂ)+(t:ℂ)*I) p‖ ≤
          B*comparisonHeightEnvelope (A+D+4) t p.1 p.2*(2+|t|)^D) →
      (∫ p : ℝ × ℝ × ℝ in Set.Ioc a b ×ˢ Set.univ,
        ‖f ((p.1:ℂ)+(-T:ℝ)*I) p.2‖ + ‖f ((p.1:ℂ)+(T:ℂ)*I) p.2‖) ≤
          2*(b-a)*B*C*T^(-A) := by
  obtain ⟨C, hC, hb⟩ := goodDyad_weighted_convolution (A+2) D (by linarith) hD
  refine ⟨C, hC, ?_⟩
  intro a b T B f hab hT hB hf
  let g : ℝ × ℝ → ℝ := fun p =>
    comparisonHeightEnvelope (A+D+4) (-T) p.1 p.2*(2+|-T|)^D +
    comparisonHeightEnvelope (A+D+4) T p.1 p.2*(2+|T|)^D
  have hgm : Integrable g := by
    have h₁ : Integrable (fun p : ℝ × ℝ => comparisonHeightEnvelope (A+D+4) (-T) p.1 p.2*(2+|-T|)^D) :=
      by simpa only [show A+2+D+2 = A+D+4 by ring] using (hb (-T)).1
    have h₂ : Integrable (fun p : ℝ × ℝ => comparisonHeightEnvelope (A+D+4) T p.1 p.2*(2+|T|)^D) :=
      by simpa only [show A+2+D+2 = A+D+4 by ring] using (hb T).1
    exact h₁.add h₂
  have hgc : (∫ p : ℝ × ℝ, g p) ≤ 2*C*T^(-A) := by
    rw [show (fun p => g p) = g from rfl]
    dsimp [g]
    rw [integral_add
      (by simpa only [show A+2+D+2 = A+D+4 by ring] using (hb (-T)).1)
      (by simpa only [show A+2+D+2 = A+D+4 by ring] using (hb T).1)]
    have hh := add_le_add (hb (-T)).2 (hb T).2
    simp only [abs_neg] at hh
    have ht : (1+|T|)^(-(A+2+2)) ≤ T^(-A) := by
      calc
        _ ≤ (1+|T|)^(-A) := Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg T]) (by linarith)
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [le_abs_self T]) (by linarith)
    calc
      _ ≤ C*(1+|T|)^(-(A+2+2)) + C*(1+|T|)^(-(A+2+2)) := by
        simpa only [show A+2+D+2 = A+D+4 by ring, abs_neg] using hh
      _ ≤ C*T^(-A)+C*T^(-A) := add_le_add
        (mul_le_mul_of_nonneg_left ht hC.le) (mul_le_mul_of_nonneg_left ht hC.le)
      _ = _ := by ring
  have hi : Integrable (fun p : ℝ × ℝ × ℝ => B*g p.2)
      ((volume.restrict (Set.Ioc a b)).prod volume) := by
    simpa using (integrableOn_const (C := B) (μ := volume) (s := Set.Ioc a b) (by simp [Real.volume_Ioc])).mul_prod hgm
  have hi' : Integrable (fun p : ℝ × ℝ × ℝ => B*g p.2)
      (volume.restrict (Set.Ioc a b ×ˢ Set.univ)) := by
    rwa [Measure.restrict_prod_eq_prod_univ, ← Measure.volume_eq_prod] at hi
  calc
    _ ≤ ∫ p : ℝ × ℝ × ℝ in Set.Ioc a b ×ˢ Set.univ, B*g p.2 := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun p => by positivity)) hi'
      filter_upwards [ae_restrict_mem (by measurability : MeasurableSet (Set.Ioc a b ×ˢ Set.univ))] with p hp
      have hh := add_le_add (hf p.1 hp.1 p.2 (-T) (by simp)) (hf p.1 hp.1 p.2 T (by simp))
      simpa only [g, mul_add, mul_assoc] using hh
    _ = (b-a)*B*(∫ p : ℝ × ℝ, g p) := by
      rw [Measure.volume_eq_prod, ← Measure.restrict_prod_eq_prod_univ]
      change (∫ p : ℝ × ℝ × ℝ, (fun _ : ℝ => B) p.1 * g p.2
        ∂(volume.restrict (Set.Ioc a b)).prod volume) = _
      rw [integral_prod _ hi]
      simp_rw [integral_const_mul]
      rw [integral_const]
      simp [Measure.real, Real.volume_Ioc, hab, smul_eq_mul, mul_assoc]
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hgc (mul_nonneg (sub_nonneg.mpr hab) hB)
      convert hh using 1 <;> ring

private lemma goodDyad_left_continuous {ι : Type*} (q : ι → ℝ)
    (M W : ℂ → ℂ) (E P : ι → ℂ → ℂ → ℂ → ℂ) (L : ι → ℂ → ℂ)
    (u : ι) (Z : ℝ) (Ωleft : Set (ℂ × ℂ × ℂ))
    (hP : DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => P u p.1 p.2.1 p.2.2) Ωleft)
    (hL : DifferentiableOn ℂ (L u) {ξ : ℂ | 0 < ξ.re})
    (hM : DifferentiableOn ℂ M {z : ℂ | 2/5-1/100000 < z.re})
    (hW : DifferentiableOn ℂ W {w : ℂ | 3/1000-1/100000 < w.re})
    (hfactor : ∀ ξ w z, (ξ,w,z) ∈ Ωleft → L u ξ ≠ 0 → E u ξ w z = P u ξ w z / L u ξ)
    (S : Set (ℝ × ℝ × ℝ)) (ξ : (ℝ × ℝ × ℝ) → ℂ) (hξ : Continuous ξ)
    (hmem : ∀ p ∈ S, (ξ p, (((3/1000:ℝ):ℂ)+p.2.1*I), (((2/5:ℝ):ℂ)+p.2.2*I)) ∈ Ωleft)
    (hpos : ∀ p ∈ S, 0 < (ξ p).re) (hnz : ∀ p ∈ S, L u (ξ p) ≠ 0) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => comparisonFrequencyKernel q M W E Z u
      (ξ p) (((3/1000:ℝ):ℂ)+p.2.1*I) (((2/5:ℝ):ℂ)+p.2.2*I)) S := by
  have hPc := hP.continuousOn.comp
    (show ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      (ξ p, (((3/1000:ℝ):ℂ)+p.2.1*I), (((2/5:ℝ):ℂ)+p.2.2*I))) S from
      (by fun_prop : Continuous _).continuousOn) hmem
  have hLc := hL.continuousOn.comp hξ.continuousOn hpos
  have hEc : ContinuousOn (fun p : ℝ × ℝ × ℝ => E u (ξ p)
      (((3/1000:ℝ):ℂ)+p.2.1*I) (((2/5:ℝ):ℂ)+p.2.2*I)) S := by
    apply (hPc.div hLc hnz).congr
    intro p hp
    exact hfactor _ _ _ (hmem p hp) (hnz p hp)
  have hMc := hM.continuousOn.comp
    (by fun_prop : ContinuousOn (fun p : ℝ × ℝ × ℝ => (((2/5:ℝ):ℂ)+p.2.2*I)) S)
    (by intro p hp; norm_num)
  have hWc := hW.continuousOn.comp
    (by fun_prop : ContinuousOn (fun p : ℝ × ℝ × ℝ => (((3/1000:ℝ):ℂ)+p.2.1*I)) S)
    (by intro p hp; norm_num)
  unfold comparisonFrequencyKernel comparisonRealPower
  apply ContinuousOn.mul _ hEc
  apply ContinuousOn.mul _ (by fun_prop)
  apply ContinuousOn.mul _ hWc
  apply ContinuousOn.mul _ hMc
  apply ContinuousOn.mul <;> fun_prop

private lemma goodDyad_finite_bound {ι : Type*} (q : ι → ℝ) (principal : ι)
    (K U δ B : ℝ) (C : Finset ι) (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hdy : comparisonFrequencyDyad q principal K U C) (f : ι → ℂ)
    (hf : ∀ u ∈ C, ‖f u‖ ≤ B * (q u)^(1/10+δ) * U^δ) :
    ‖∑ u ∈ C, f u‖ ≤ B*K*2^(1/10+δ)*U^(11/10+2*δ) := by
  have hUp : 0 < U := by linarith
  calc
    _ ≤ ∑ u ∈ C, ‖f u‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ C, B*(2*U)^(1/10+δ)*U^δ := by
      apply Finset.sum_le_sum
      intro u hu
      apply (hf u hu).trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hB
      exact Real.rpow_le_rpow (by linarith [(hdy.1 u hu).2.1])
        (hdy.1 u hu).2.2.le (by linarith)
    _ = (C.card:ℝ) * (B*(2*U)^(1/10+δ)*U^δ) := by simp
    _ ≤ (K*U) * (B*(2*U)^(1/10+δ)*U^δ) :=
      mul_le_mul_of_nonneg_right hdy.2 (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) hUp.le]
      have he : U*U^(1/10+δ)*U^δ = U^(11/10+2*δ) := by
        nth_rw 1 [← Real.rpow_one U]
        rw [← Real.rpow_add hUp, ← Real.rpow_add hUp]
        congr 1; ring
      linear_combination B*K*2^(1/10+δ)*he

private lemma goodDyad_edge_integrable (a b t A D B : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hB : 0 ≤ B) (f : (ℝ × ℝ × ℝ) → ℂ)
    (hc : ContinuousOn f (Set.Ioc a b ×ˢ Set.univ))
    (hb : ∀ p ∈ Set.Ioc a b ×ˢ Set.univ, ‖f p‖ ≤
      B*comparisonHeightEnvelope (A+D+2) t p.2.1 p.2.2*(2+|t|)^D) :
    Integrable f ((volume.restrict (Set.Ioc a b)).prod volume) := by
  obtain ⟨H, hH, hh⟩ := goodDyad_weighted_convolution A D hA hD
  have hi : Integrable (fun p : ℝ × ℝ × ℝ =>
      B*(comparisonHeightEnvelope (A+D+2) t p.2.1 p.2.2*(2+|t|)^D))
      ((volume.restrict (Set.Ioc a b)).prod volume) := by
    simpa using (integrableOn_const (C := B) (μ := volume) (s := Set.Ioc a b)
      (by simp [Real.volume_Ioc])).mul_prod (hh t).1
  rw [Measure.restrict_prod_eq_prod_univ, ← Measure.volume_eq_prod] at hi ⊢
  apply hi.mono' (hc.aestronglyMeasurable (by measurability))
  filter_upwards [ae_restrict_mem (by measurability : MeasurableSet (Set.Ioc a b ×ˢ Set.univ))] with p hp
  simpa only [mul_assoc] using hb p hp

private lemma goodDyad_row_hol {ι : Type*} (q : ι → ℝ) (M W : ℂ → ℂ)
    (E P : ι → ℂ → ℂ → ℂ → ℂ) (L : ι → ℂ → ℂ)
    (u : ι) (Z T : ℝ) (Ωleft : Set (ℂ × ℂ × ℂ))
    (hP : DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => P u p.1 p.2.1 p.2.2) Ωleft)
    (hL : DifferentiableOn ℂ (L u) {ξ : ℂ | 0 < ξ.re})
    (hleft : ∀ ξ w z, ξ ∈ comparisonClosedStrip (499/500) comparisonSigma₁ →
      w.re = 3/1000 → z.re = 2/5 → (ξ,w,z) ∈ Ωleft)
    (hfactor : ∀ ξ w z, (ξ,w,z) ∈ Ωleft → L u ξ ≠ 0 → E u ξ w z = P u ξ w z / L u ξ)
    (hnz : ∀ ξ, 499/500 ≤ ξ.re → |ξ.im| ≤ T → L u ξ ≠ 0)
    (w z : ℂ) (hw : w.re = 3/1000) (hz : z.re = 2/5) :
    DifferentiableOn ℂ (fun ξ => comparisonFrequencyKernel q M W E Z u ξ w z)
      {ξ : ℂ | 499/500 ≤ ξ.re ∧ ξ.re ≤ comparisonSigma₁ ∧ -T ≤ ξ.im ∧ ξ.im ≤ T} := by
  let S : Set ℂ := {ξ : ℂ | 499/500 ≤ ξ.re ∧ ξ.re ≤ comparisonSigma₁ ∧ -T ≤ ξ.im ∧ ξ.im ≤ T}
  have hSmem : ∀ ξ ∈ S, ξ ∈ comparisonClosedStrip (499/500) comparisonSigma₁ :=
    fun ξ hξ => ⟨hξ.1,hξ.2.1⟩
  have hSnz : ∀ ξ ∈ S, L u ξ ≠ 0 := by
    intro ξ hξ
    exact hnz ξ hξ.1 (abs_le.mpr ⟨hξ.2.2.1,hξ.2.2.2⟩)
  have hPd : DifferentiableOn ℂ (fun ξ => P u ξ w z) S :=
    hP.comp (by fun_prop : DifferentiableOn ℂ (fun ξ : ℂ => (ξ,w,z)) S)
      (fun ξ hξ => hleft ξ w z (hSmem ξ hξ) hw hz)
  have hLd : DifferentiableOn ℂ (L u) S :=
    hL.mono (fun ξ hξ => by dsimp [S] at hξ; dsimp; linarith [hξ.1])
  have hEd : DifferentiableOn ℂ (fun ξ => E u ξ w z) S := by
    apply (hPd.div hLd hSnz).congr
    intro ξ hξ
    exact hfactor ξ w z (hleft ξ w z (hSmem ξ hξ) hw hz) (hSnz ξ hξ)
  unfold comparisonFrequencyKernel
  have hp : Differentiable ℂ (fun ξ : ℂ => comparisonRealPower Z
      ((comparisonA:ℂ)/2 + ξ - 1 + (comparisonH₀:ℂ)*z + (comparisonB:ℂ)*(w-1))) := by
    unfold comparisonRealPower
    fun_prop
  have hg : Differentiable ℂ (fun ξ : ℂ => Complex.exp ((ξ+z-1)^2)) := by fun_prop
  exact (((((hp.differentiableOn.mul hg.differentiableOn).mul_const (M z)).mul_const (W w)).mul_const
    (comparisonRealPower (q u) (-z))).mul hEd)

set_option maxHeartbeats 1000000 in

theorem comparison_good_dyad_analytic
    {ι : Type*} (principal : ι) (q : ι → ℝ) (M W : ℂ → ℂ)
    (E P : ι → ℂ → ℂ → ℂ → ℂ) (L : ι → ℂ → ℂ)
    (good : ℝ → ι → Prop)
    (Ω : Set (ℂ × ℂ × ℂ)) (hΩ : IsOpen Ω)
    (hbox : ∀ ξ w z : ℂ,
      ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
      w ∈ comparisonClosedStrip (3 / 1000) 4 →
      z ∈ comparisonClosedStrip (2 / 5) 2 → (ξ, w, z) ∈ Ω)
    (hE : ∀ u : ι, u ≠ principal →
      DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => E u p.1 p.2.1 p.2.2) Ω)
    (hM : DifferentiableOn ℂ M {z : ℂ | 2 / 5 - 1 / 100000 < z.re})
    (hW : DifferentiableOn ℂ W {w : ℂ | 3 / 1000 - 1 / 100000 < w.re})
    (hMdecay : comparisonRapidStripDecay M (2 / 5) 2)
    (hWdecay : comparisonRapidStripDecay W (3 / 1000) 4)
    (hEBound : ∃ d : ℝ, 0 ≤ d ∧ ∀ δ : ℝ, 0 < δ →
      ∃ B : ℝ, 0 < B ∧ ∀ u : ι, u ≠ principal → 1 ≤ q u →
        ∀ ξ w z : ℂ,
          ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
          w ∈ comparisonClosedStrip (3 / 1000) 4 →
          z ∈ comparisonClosedStrip (2 / 5) 2 →
          ‖E u ξ w z‖ ≤ B * (q u) ^ (1 / 2 + δ) * (2 + |w.im|) ^ d)
    (Ωleft : Set (ℂ × ℂ × ℂ)) (hΩleft : IsOpen Ωleft)
    (hleft : ∀ ξ w z : ℂ,
      ξ ∈ comparisonClosedStrip (499 / 500) comparisonSigma₁ →
      w.re = 3 / 1000 → z.re = 2 / 5 → (ξ, w, z) ∈ Ωleft)
    (hP : ∀ u : ι, u ≠ principal →
      DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => P u p.1 p.2.1 p.2.2) Ωleft)
    (hL : ∀ (U : ℝ) (u : ι), 1 ≤ U → good U u →
      DifferentiableOn ℂ (L u) {ξ : ℂ | 0 < ξ.re})
    (hfactor : ∀ (u : ι) (ξ w z : ℂ), u ≠ principal →
      (ξ, w, z) ∈ Ωleft → L u ξ ≠ 0 → E u ξ w z = P u ξ w z / L u ξ)
    (A_F : ℝ) (hAF : 0 ≤ A_F)
    (hPBound : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 0 < B ∧
      ∀ (u : ι) (ξ w z : ℂ), u ≠ principal → 1 ≤ q u →
        ξ ∈ comparisonClosedStrip (499 / 500) comparisonSigma₁ →
        w.re = 3 / 1000 → z.re = 2 / 5 →
        ‖P u ξ w z‖ ≤ B * (q u) ^ (1 / 2 + δ) *
          (2 + |ξ.im|) ^ A_F * (2 + |w.im|) ^ A_F * (2 + |z.im|) ^ A_F)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hρsmall : ρ < min (1 / 10) (1 / (A_F + 1)))
    (hdetector : ∀ δ : ℝ, 0 < δ → ∃ B Udet : ℝ, 0 < B ∧ 1 ≤ Udet ∧
      ∀ (U : ℝ) (u : ι), Udet ≤ U → good U u → U ≤ q u → q u < 2 * U →
        ∀ ξ : ℂ, 499 / 500 ≤ ξ.re → |ξ.im| ≤ 2 * U ^ ρ →
          L u ξ ≠ 0 ∧ ‖(L u ξ)⁻¹‖ ≤ B * U ^ δ)
    (K : ℝ) (hK : 0 < K) :
    ∀ ε : ℝ, 0 < ε → ∃ Bcentral : ℝ, 0 < Bcentral ∧
      ∀ A₁ : ℝ, 0 < A₁ → ∃ Btail U₀ : ℝ, 0 < Btail ∧ 1 ≤ U₀ ∧
        ∀ (Z U : ℝ) (C : Finset ι), 1 ≤ Z → U₀ ≤ U →
          Z ^ (9 / 100 : ℝ) < U → U ≤ Z ^ (10001 / 100000 : ℝ) →
          comparisonFrequencyDyad q principal K U C → (∀ u ∈ C, good U u) →
          ∃ E_tail : ℂ,
            comparisonFrequencyIntegral q M W E C Z 4 4 2 =
              comparisonTruncatedFrequencyIntegral q M W E C Z
                (499 / 500) (3 / 1000) (2 / 5) (U ^ ρ) + E_tail ∧
            ‖comparisonTruncatedFrequencyIntegral q M W E C Z
                (499 / 500) (3 / 1000) (2 / 5) (U ^ ρ)‖ ≤
              Bcentral * Z ^ (comparisonE (499 / 500) (3 / 1000) (2 / 5)) *
                U ^ (11 / 10 + ε) ∧
            ‖E_tail‖ ≤
              Btail * Z ^ (comparisonE comparisonSigma₁ (3 / 1000) (2 / 5)) *
                U ^ (11 / 10 + ε - ρ * A₁) := by
  intro ε hε
  obtain ⟨Bcentral, Udet, hBc, hUdet, hcentral⟩ := goodDyad_central_estimate
    principal q M W E P L good A_F hAF hMdecay hWdecay
    (fun u ξ w z hu hξ hw hz hnz =>
      hfactor u ξ w z hu (hleft ξ w z hξ hw hz) hnz)
    hPBound ρ hdetector K hK ε hε
  refine ⟨Bcentral, hBc, ?_⟩
  intro A₁ hA₁

  suffices htail : ∃ Btail U₀ : ℝ, 0 < Btail ∧ 1 ≤ U₀ ∧ Udet ≤ U₀ ∧
      ∀ (Z U : ℝ) (C : Finset ι), 1 ≤ Z → U₀ ≤ U →
        Z ^ (9/100:ℝ) < U → U ≤ Z ^ (10001/100000:ℝ) →
        comparisonFrequencyDyad q principal K U C → (∀ u ∈ C, good U u) →
        ‖comparisonFrequencyIntegral q M W E C Z 4 4 2 -
          comparisonTruncatedFrequencyIntegral q M W E C Z
            (499/500) (3/1000) (2/5) (U^ρ)‖ ≤
          Btail * Z^(comparisonE comparisonSigma₁ (3/1000) (2/5)) *
            U^(11/10+ε-ρ*A₁) by
    obtain ⟨Btail, U₀, hBt, hU₀, hdet₀, ht⟩ := htail
    refine ⟨Btail, U₀, hBt, hU₀, ?_⟩
    intro Z U C hZ hU hZU hUZ hdy hg
    refine ⟨comparisonFrequencyIntegral q M W E C Z 4 4 2 -
      comparisonTruncatedFrequencyIntegral q M W E C Z
        (499/500) (3/1000) (2/5) (U^ρ), ?_, ?_, ?_⟩
    · abel
    · exact hcentral Z U C hZ (hdet₀.trans hU) hdy hg
    · exact ht Z U C hZ hU hZU hUZ hdy hg
  classical
  obtain ⟨d, hd, hEb⟩ := hEBound
  let ord : OrdinaryDyadProof.Input principal q M W E :=
    ⟨Ω, hΩ, hbox, hE, hM, hW, hMdecay, hWdecay, d, hd, hEb⟩
  obtain ⟨BL, UL, hBL, hUL, hLb⟩ := goodDyad_left_kernel_bound
    principal q M W E P L good A_F hAF hMdecay hWdecay
    (fun u ξ w z hu hξ hw hz hnz => hfactor u ξ w z hu (hleft ξ w z hξ hw hz) hnz)
    hPBound ρ hdetector (A₁+2) (ε/2) (by linarith) (by linarith)
  obtain ⟨BO, hBO, hOb⟩ := comparisonGoodDyad_original_envelope_bound
    q principal M W E hMdecay hWdecay d hd hEb A₁ (ε/2) hA₁.le (by linarith)
  obtain ⟨BD, UD, hBD, hUD, hDb⟩ := hdetector (ε/2) (by linarith)
  obtain ⟨CH, hCH, hHb⟩ := comparisonGoodDyad_horizontal_envelope_domination A₁ A_F hA₁.le hAF
  obtain ⟨CT, hCT, hTb⟩ := comparisonGoodDyad_envelope_tail_domination A₁ 0 hA₁.le (by norm_num)
  let a := comparisonE comparisonSigma₁ (3/1000) (2/5)
  let c := ‖(2*(Real.pi:ℂ))⁻¹^3‖+1
  let B := (BL+BO)*K*2^(1/10+ε/2)
  let H := 2*(comparisonSigma₁-499/500)*CH+CT
  refine ⟨c*B*H, max Udet (max UL UD), ?_, ?_, le_max_left _ _, ?_⟩
  · dsimp [c, B, H]; norm_num [comparisonSigma₁, comparisonDelta]; positivity
  · exact hUdet.trans (le_max_left _ _)
  intro Z U C hZ hU _ _ hdy hg
  have hUdet' : Udet ≤ U := (le_max_left _ _).trans hU
  have hUL' : UL ≤ U := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hU
  have hUD' : UD ≤ U := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hU
  have hU1 : 1 ≤ U := hUdet.trans hUdet'
  have hUp : 0 < U := by linarith
  have hT1 : 1 ≤ U^ρ := Real.one_le_rpow hU1 hρ.le
  have hTp : 0 < U^ρ := by positivity
  have hUDpow : 1 ≤ U^(ε/2) := Real.one_le_rpow hU1 (by linarith)
  let T := U^ρ
  let F : ℂ → (ℝ × ℝ) → ℂ := fun ξ p => ∑ u ∈ C,
    comparisonFrequencyKernel q M W E Z u ξ
      (((3/1000:ℝ):ℂ)+(p.1:ℂ)*I) (((2/5:ℝ):ℂ)+(p.2:ℂ)*I)
  let V := B*Z^a*U^(11/10+ε)
  have hV : 0 ≤ V := by dsimp [V, B]; positivity
  have envpos (t : ℝ) (p : ℝ × ℝ) :
      0 ≤ comparisonHeightEnvelope (A₁+A_F+4) t p.1 p.2*(2+|t|)^A_F := by
    unfold comparisonHeightEnvelope; positivity
  have aggregate (ξ : ℂ) (p : ℝ × ℝ) (g : ℝ) (hg0 : 0 ≤ g)
      (hf : ∀ u ∈ C, ‖comparisonFrequencyKernel q M W E Z u ξ
        (((3/1000:ℝ):ℂ)+(p.1:ℂ)*I) (((2/5:ℝ):ℂ)+(p.2:ℂ)*I)‖ ≤
        ((BL+BO)*Z^a*g)*(q u)^(1/10+ε/2)*U^(ε/2)) :
      ‖F ξ p‖ ≤ V*g := by
    have hh := goodDyad_finite_bound q principal K U (ε/2) ((BL+BO)*Z^a*g)
      C hU1 (by linarith) (by positivity) hdy
      (fun u => comparisonFrequencyKernel q M W E Z u ξ
        (((3/1000:ℝ):ℂ)+(p.1:ℂ)*I) (((2/5:ℝ):ℂ)+(p.2:ℂ)*I)) hf
    rw [show 11/10+2*(ε/2) = 11/10+ε by ring] at hh
    convert hh using 1 <;> dsimp [F, V, B] <;> ring
  have leftbound (ξ : ℂ) (p : ℝ × ℝ)
      (hξ : ξ ∈ comparisonClosedStrip (499/500) comparisonSigma₁) (ht : |ξ.im| ≤ T) :
      ‖F ξ p‖ ≤ V*comparisonHeightEnvelope (A₁+A_F+4) ξ.im p.1 p.2*(2+|ξ.im|)^A_F := by
    rw [mul_assoc]
    apply aggregate ξ p _ (envpos ξ.im p)
    intro u hu
    have hb := hLb U Z u ξ
      (((3/1000:ℝ):ℂ)+(p.1:ℂ)*I) (((2/5:ℝ):ℂ)+(p.2:ℂ)*I)
      hUL' hZ (hdy.1 u hu).1 (hg u hu) (hdy.1 u hu).2.1 (hdy.1 u hu).2.2 hξ
      (ht.trans (by dsimp [T]; linarith [Real.rpow_nonneg hUp.le ρ])) (by simp) (by simp)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hb
    rw [show A₁+2+A_F+2 = A₁+A_F+4 by ring] at hb
    have hzmono : Z^comparisonE ξ.re (3/1000) (2/5) ≤ Z^a := by
      apply Real.rpow_le_rpow_of_exponent_le hZ
      dsimp [comparisonE, a]
      linarith [hξ.2]
    have hbb : BL*Z^comparisonE ξ.re (3/1000) (2/5) ≤ (BL+BO)*Z^a :=
      mul_le_mul (by linarith) hzmono (by positivity) (by positivity)
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbb
        (Real.rpow_nonneg (show 0 ≤ q u by linarith [(hdy.1 u hu).2.1]) (1/10+ε/2))) (by positivity : 0 ≤ U^(ε/2))) (envpos ξ.im p)
    apply hb.trans
    convert hh using 1 <;> ring
  have originalbound (t : ℝ) (p : ℝ × ℝ) :
      ‖F ((comparisonSigma₁:ℂ)+(t:ℂ)*I) p‖ ≤
        V*comparisonHeightEnvelope (A₁+4) t p.1 p.2 := by
    apply aggregate _ _ _ (by unfold comparisonHeightEnvelope; positivity)
    intro u hu
    have hqp : 0 ≤ q u := by linarith [(hdy.1 u hu).2.1]
    have hb := hOb Z u ((comparisonSigma₁:ℂ)+(t:ℂ)*I)
      (((3/1000:ℝ):ℂ)+(p.1:ℂ)*I) (((2/5:ℝ):ℂ)+(p.2:ℂ)*I)
      hZ (hdy.1 u hu).1 (by linarith [(hdy.1 u hu).2.1]) (by simp) (by simp) (by simp)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hb
    have h₁ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (show BO ≤ BL+BO by linarith) (by positivity : 0 ≤ Z^a))
        (Real.rpow_nonneg (show 0 ≤ q u by linarith [(hdy.1 u hu).2.1]) (1/10+ε/2)))
      (by unfold comparisonHeightEnvelope; positivity : 0 ≤ comparisonHeightEnvelope (A₁+4) t p.1 p.2)
    have h₂ := mul_le_mul_of_nonneg_left hUDpow
      (by unfold comparisonHeightEnvelope; positivity : 0 ≤ (BL+BO)*Z^a*(q u)^(1/10+ε/2)*comparisonHeightEnvelope (A₁+4) t p.1 p.2)
    apply (hb.trans h₁).trans
    convert h₂ using 1 <;> dsimp [a] <;> ring
  have hnz (u : ι) (hu : u ∈ C) (ξ : ℂ) (hx : 499/500 ≤ ξ.re) (ht : |ξ.im| ≤ T) : L u ξ ≠ 0 :=
    (hDb U u hUD' (hg u hu) (hdy.1 u hu).2.1 (hdy.1 u hu).2.2 ξ hx
      (ht.trans (by dsimp [T]; linarith [Real.rpow_nonneg hUp.le ρ]))).1
  have hcont (S : Set (ℝ × ℝ × ℝ)) (ξ : (ℝ × ℝ × ℝ) → ℂ) (hc : Continuous ξ)
      (hm : ∀ p ∈ S, ξ p ∈ comparisonClosedStrip (499/500) comparisonSigma₁)
      (ht : ∀ p ∈ S, |(ξ p).im| ≤ T) : ContinuousOn (fun p : ℝ × ℝ × ℝ => F (ξ p) p.2) S := by
    apply continuousOn_finsetSum C
    intro u hu
    exact goodDyad_left_continuous q M W E P L u Z Ωleft (hP u (hdy.1 u hu).1)
      (hL U u hU1 (hg u hu)) hM hW
      (hfactor u · · · (hdy.1 u hu).1) S ξ hc
      (fun p hp => hleft _ _ _ (hm p hp) (by simp) (by simp))
      (fun p hp => by have := (hm p hp).1; linarith)
      (fun p hp => hnz u hu (ξ p) (hm p hp).1 (ht p hp))
  have ha : Integrable (fun p : ℝ × ℝ × ℝ => F (((499/500:ℝ):ℂ)+(p.1:ℂ)*I) p.2)
      (volume.restrict {p : ℝ × ℝ × ℝ | |p.1| ≤ T}) := by
    have hc := hcont {p : ℝ × ℝ × ℝ | |p.1| ≤ T}
      (fun p => (((499/500:ℝ):ℂ)+(p.1:ℂ)*I)) (by fun_prop)
      (by intro p hp; norm_num [comparisonClosedStrip, comparisonSigma₁, comparisonDelta])
      (by intro p hp; simpa using hp)
    have hi := goodDyad_weighted_integrable (A₁+2) A_F (by linarith) hAF
    rw [show A₁+2+A_F+2 = A₁+A_F+4 by ring] at hi
    apply (hi.const_mul V).integrableOn.mono' (hc.aestronglyMeasurable (by measurability))
    filter_upwards [ae_restrict_mem (by measurability : MeasurableSet {p : ℝ × ℝ × ℝ | |p.1| ≤ T})] with p hp
    have hb := leftbound (((499/500:ℝ):ℂ)+(p.1:ℂ)*I) p.2
      (by norm_num [comparisonClosedStrip, comparisonSigma₁, comparisonDelta]) (by simpa using hp)
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add, mul_assoc] using hb
  have hb : Integrable (fun p : ℝ × ℝ × ℝ => F ((comparisonSigma₁:ℂ)+(p.1:ℂ)*I) p.2) := by
    apply integrable_finset_sum C
    intro u hu
    exact ord.line_integrable Z hZ u (hdy.1 u hu).1
      (by linarith [(hdy.1 u hu).2.1]) comparisonSigma₁ (3/1000) (2/5)
      (by norm_num [comparisonSigma₁, comparisonDelta]) (by norm_num) (by norm_num)
  have edge_height (t : ℝ) (ht : t ∈ ({-T,T} : Set ℝ)) : |t| ≤ T := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl <;> simp [abs_of_nonneg (show 0 ≤ T from hTp.le)]
  have hedge (t : ℝ) (ht : t ∈ ({-T,T} : Set ℝ)) :
      Integrable (fun p : ℝ × ℝ × ℝ => F ((p.1:ℂ)+(t:ℂ)*I) p.2)
        ((volume.restrict (Set.Ioc (499/500) comparisonSigma₁)).prod volume) := by
    have ht' := edge_height t ht
    apply goodDyad_edge_integrable (499/500) comparisonSigma₁ t (A₁+2) A_F V (by linarith) hAF hV
    · apply hcont _ _ (by fun_prop)
      · intro p hp; simpa [comparisonClosedStrip] using And.intro hp.1.1.le hp.1.2
      · intro p hp; simpa using ht'
    · intro p hp
      have hh := leftbound ((p.1:ℂ)+(t:ℂ)*I) p.2
        (by simpa [comparisonClosedStrip] using And.intro hp.1.1.le hp.1.2) (by simpa using ht')
      simpa [show A₁+2+A_F+2 = A₁+A_F+4 by ring] using hh
  have hhol (p : ℝ × ℝ) : DifferentiableOn ℂ (fun ξ => F ξ p)
      {ξ : ℂ | 499/500 ≤ ξ.re ∧ ξ.re ≤ comparisonSigma₁ ∧ -T ≤ ξ.im ∧ ξ.im ≤ T} := by
    apply DifferentiableOn.fun_sum
    intro u hu
    exact goodDyad_row_hol q M W E P L u Z T Ωleft (hP u (hdy.1 u hu).1)
      (hL U u hU1 (hg u hu)) hleft (hfactor u · · · (hdy.1 u hu).1)
      (hnz u hu) _ _ (by simp) (by simp)
  have hr := goodDyad_rectangle_with_exterior (499/500) comparisonSigma₁ T F
    (by norm_num [comparisonSigma₁, comparisonDelta]) hTp hhol ha hb
    (hedge (-T) (by simp)) (hedge T (by simp))
  have hh := hHb (499/500) comparisonSigma₁ T V F
    (by norm_num [comparisonSigma₁, comparisonDelta]) hT1 hV (by
      intro x hx p t ht
      have hh := leftbound ((x:ℂ)+(t:ℂ)*I) p
        (by simpa [comparisonClosedStrip] using And.intro hx.1.le hx.2) (by simpa using edge_height t ht)
      simpa using hh)
  have ht := hTb T V (fun t p => F ((comparisonSigma₁:ℂ)+(t:ℂ)*I) p) hT1 hV (by
    intro t p
    simpa using originalbound t p)
  have hraw := hr.trans (add_le_add hh ht)
  have hs := ord.finite_shift Z hZ C (fun u hu => ⟨(hdy.1 u hu).1, by linarith [(hdy.1 u hu).2.1]⟩)
  rw [hs]
  unfold comparisonFrequencyIntegral comparisonTripleVerticalIntegral comparisonTruncatedFrequencyIntegral
  change ‖(2*(Real.pi:ℂ))⁻¹^3 * (∫ p : ℝ × ℝ × ℝ, F ((comparisonSigma₁:ℂ)+(p.1:ℂ)*I) p.2) -
    (2*(Real.pi:ℂ))⁻¹^3 * (∫ p : ℝ × ℝ × ℝ in {p | |p.1| ≤ T}, F (((499/500:ℝ):ℂ)+(p.1:ℂ)*I) p.2)‖ ≤ _
  rw [← mul_sub, norm_mul]
  have he : U^(11/10+ε)*T^(-A₁) = U^(11/10+ε-ρ*A₁) := by
    dsimp [T]
    rw [← Real.rpow_mul hUp.le, ← Real.rpow_add hUp]
    congr 1; ring
  calc
    _ ≤ ‖(2*(Real.pi:ℂ))⁻¹^3‖ *
      (2*(comparisonSigma₁-499/500)*V*CH*T^(-A₁)+V*CT*T^(-A₁)) :=
      mul_le_mul_of_nonneg_left hraw (norm_nonneg _)
    _ ≤ c * (2*(comparisonSigma₁-499/500)*V*CH*T^(-A₁)+V*CT*T^(-A₁)) := by
      apply mul_le_mul_of_nonneg_right (by dsimp [c]; linarith [norm_nonneg ((2*(Real.pi:ℂ))⁻¹^3)])
      norm_num [comparisonSigma₁, comparisonDelta]; positivity
    _ = _ := by
      dsimp [V, H]
      linear_combination c*B*Z^a*(2*(comparisonSigma₁-499/500)*CH+CT)*he

end
end DedekindZetaZeroFree
