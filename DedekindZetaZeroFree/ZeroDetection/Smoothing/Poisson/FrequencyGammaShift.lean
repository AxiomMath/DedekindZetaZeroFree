module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.FrequencyConvexity
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.GammaShift

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawDetectorShift31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open scoped Classical
open Set Filter MeasureTheory Complex
open scoped Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private lemma detector_entire_bounded (F : Type) [Field F] [NumberField F] (U : ℝ)
    (ω : Detector.PrimitiveFrequencyCharacter F) :
    Differentiable ℂ (DetectorDef.D F U ω.character) ∧
    ∃ N : ℝ, 0 < N ∧ ∀ z : ℂ, 0 ≤ z.re → ‖DetectorDef.D F U ω.character z‖ ≤ N := by
  let X : ℝ := U ^ DetectorDef.qExp
  let T := (Detector.ideals_bounded_norm_finite F X).toFinset
  have he (z : ℂ) : DetectorDef.D F U ω.character z = ∑ d ∈ T,
      (if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X then
        (Detector.idealMoebius F d : ℂ) * ω.character d *
          (Ideal.absNorm d : ℂ) ^ (-z) else 0) := by
    unfold DetectorDef.D
    apply finsum_eq_sum_of_support_subset
    intro d hd
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra hn
    exact hd (if_neg hn)
  have hdiff : Differentiable ℂ (DetectorDef.D F U ω.character) := by
    have : DetectorDef.D F U ω.character = fun z => ∑ d ∈ T,
      (if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X then
        (Detector.idealMoebius F d : ℂ) * ω.character d *
          (Ideal.absNorm d : ℂ) ^ (-z) else 0) := funext he
    rw [this]
    apply Differentiable.fun_sum
    intro d hd
    by_cases hn : d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X
    · simp only [if_pos hn]
      apply Differentiable.const_mul
      apply Differentiable.const_cpow differentiable_id.neg
      left
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hn.1
    · simp only [if_neg hn]
      exact differentiable_const _
  refine ⟨hdiff, (T.card : ℝ) + 1, by positivity, fun z hz => ?_⟩
  rw [he z]
  calc ‖∑ d ∈ T, (if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X then
        (Detector.idealMoebius F d : ℂ) * ω.character d *
          (Ideal.absNorm d : ℂ) ^ (-z) else 0)‖
      ≤ ∑ d ∈ T, ‖(if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X then
        (Detector.idealMoebius F d : ℂ) * ω.character d *
          (Ideal.absNorm d : ℂ) ^ (-z) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ T, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d _
        by_cases hn : d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X
        · rw [if_pos hn]
          have hnpos : 0 < Ideal.absNorm d :=
            Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn.1)
          have hn1 : (1 : ℝ) ≤ (Ideal.absNorm d : ℝ) := by exact_mod_cast hnpos
          have hμ : ‖(Detector.idealMoebius F d : ℂ)‖ ≤ 1 := by
            unfold Detector.idealMoebius UniqueFactorizationMonoid.moebius
            split <;> simp [Int.cast_pow]
          have hω := RayUnitary.ray_character_norm_le_one F _ ω.conductor_ne_zero ω.character d
          have hpow : ‖(Ideal.absNorm d : ℂ) ^ (-z)‖ ≤ 1 := by
            rw [Complex.norm_natCast_cpow_of_pos hnpos]
            simp only [Complex.neg_re]
            exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
          rw [norm_mul, norm_mul]
          have h := mul_le_mul (mul_le_mul hμ hω (norm_nonneg _) zero_le_one) hpow
            (norm_nonneg _) (by norm_num)
          simpa using h
        · rw [if_neg hn]
          simp
    _ = T.card := by simp
    _ ≤ (T.card : ℝ) + 1 := by linarith

private theorem contour_core
    (AD : SArithmeticData F) (ω : Detector.PrimitiveFrequencyCharacter F)
    (hnp : ¬ ω.character.IsPrincipal)
    (U : ℝ) (hU : 2 ≤ U)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hgs : ∀ z : ℂ, 1 < z.re →
      g z = Detector.idealLSeries F ω.character z)
    (β γ : ℝ) (hβ : DetectorDef.σ₀ ≤ β) (hβ1 : β ≤ 1)
    (hz : DetectorDef.IsLZero (ω) ((β : ℂ) + (γ : ℂ) * Complex.I)) :
    let s : ℂ := (β : ℂ) + (γ : ℂ) * Complex.I
    let f : ℂ → ℂ := fun v =>
      g (s + v) * DetectorDef.D F U ω.character (s + v)
    let X : ℝ := U ^ DetectorDef.r
    let a : ℝ := DetectorDef.c - β
    MeasureTheory.Integrable (fun t : ℝ =>
      Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
        f ((a : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)) ∧
    MeasureTheory.Integrable (fun t : ℝ =>
      Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
        f (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ∧
    (∫ t : ℝ, Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
        f (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ, Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
        f ((a : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨C0, hC0, hnorm⟩ : ∃ C0 : ℝ, 0 < C0 ∧
      (Ideal.absNorm ω.conductor : ℝ) ≤ C0 * U :=
    ⟨(Ideal.absNorm ω.conductor : ℝ) + 1, by positivity, by
      have := Nat.cast_nonneg (α := ℝ) (Ideal.absNorm ω.conductor)
      nlinarith⟩
  obtain ⟨A, hA, hbridge⟩ := detector_convexity_bridge F
    (primitive12_totallyComplex F AD.zeta12 AD.primitive_zeta12)
    C0 hC0
  obtain ⟨K, hK, hKb⟩ := hbridge 1 one_pos
  intro s f X a
  have hsre : s.re = β := by simp [s]
  have hsim : s.im = γ := by simp [s]
  have hc : DetectorDef.c = 1 / 100 := rfl
  have hσ : DetectorDef.σ₀ = 22 / 25 := rfl
  have ha1 : -1 < a := by simp only [a]; rw [hc]; linarith
  have ha0 : a < 0 := by simp only [a]; rw [hc]; rw [hσ] at hβ; linarith
  have hUp : 0 < U := by linarith
  have hXp : 0 < X := Real.rpow_pos_of_pos hUp _
  obtain ⟨hdiff, Nd, hNd, hNdb⟩ := detector_entire_bounded F U ω
  have hgL : ∀ w : ℂ, 0 < w.re → g w = (RowHeckeBridge.hecke AD ω hnp).L w :=
    RowHeckeBridge.entire_eq_hecke AD ω hnp hg hgs
  have hg0 : g s = 0 := by
    obtain ⟨hre, g', hg'an, hg'ser, hg's⟩ := hz
    have h1 := RowHeckeBridge.eq_hecke_of_analyticOn AD ω hnp hg'an hg'ser s hre
    rw [hgL s hre, ← h1]
    exact hg's
  have hf0 : f 0 = 0 := by
    show g (s + 0) * DetectorDef.D F U ω.character (s + 0) = 0
    rw [add_zero, hg0, zero_mul]
  have hfd : Differentiable ℂ f :=
    (hg.comp ((differentiable_const s).add differentiable_id)).mul
      (hdiff.comp ((differentiable_const s).add differentiable_id))
  have hbound (σ : ℝ) (hσ' : σ ∈ Set.Icc a (2:ℝ)) (t : ℝ) :
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (K * U ^ ((1 : ℝ) / 2 + 1) * Nd) * (2 + |γ + t|) ^ A := by
    have hre : (s + ((σ : ℂ) + (t : ℂ) * Complex.I)).re = β + σ := by simp [hsre]
    have him : (s + ((σ : ℂ) + (t : ℂ) * Complex.I)).im = γ + t := by simp [hsim]
    have hr1 : (3 / 1000 : ℝ) ≤ β + σ := by
      have := hσ'.1
      simp only [a] at this
      rw [hc] at this
      linarith
    have hr2 : β + σ ≤ 4 := by linarith [hσ'.2]
    have hkl := (hKb U hU ω.conductor ω.conductor_ne_zero
      ω.character ω.primitive hnorm
      (s + ((σ : ℂ) + (t : ℂ) * Complex.I)) (by rw [hre]; exact hr1)
      (by rw [hre]; exact hr2)).1 hnp (RowHeckeBridge.hecke AD ω hnp)
    rw [him] at hkl
    have hkl' : ‖g (s + ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤
        K * U ^ ((1 : ℝ) / 2 + 1) * (2 + |γ + t|) ^ A := by
      rw [hgL _ (by rw [hre]; linarith)]
      exact hkl
    have hdl := hNdb (s + ((σ : ℂ) + (t : ℂ) * Complex.I)) (by rw [hre]; linarith)
    calc ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        = ‖g (s + ((σ : ℂ) + (t : ℂ) * Complex.I))‖ *
          ‖DetectorDef.D F U ω.character (s + ((σ : ℂ) + (t : ℂ) * Complex.I))‖ :=
          norm_mul _ _
      _ ≤ (K * U ^ ((1 : ℝ) / 2 + 1) * (2 + |γ + t|) ^ A) * Nd :=
          mul_le_mul hkl' hdl (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hGrowth : ∃ M B : ℝ, 0 < M ∧ 0 ≤ B ∧
      ∀ σ : ℝ, σ ∈ Set.Icc a (2:ℝ) → ∀ t : ℝ,
        ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * (2 + |t|) ^ B := by
    refine ⟨K * U ^ ((1 : ℝ) / 2 + 1) * Nd * (2 + |γ|) ^ A, A, by positivity, hA, ?_⟩
    intro σ hσ' t
    have ht : 2 + |γ + t| ≤ (2 + |γ|) * (2 + |t|) := by
      nlinarith [abs_add_le γ t, abs_nonneg γ, abs_nonneg t,
        mul_nonneg (abs_nonneg γ) (abs_nonneg t)]
    calc
      _ ≤ (K * U ^ ((1 : ℝ) / 2 + 1) * Nd) * (2 + |γ + t|) ^ A := hbound σ hσ' t
      _ ≤ (K * U ^ ((1 : ℝ) / 2 + 1) * Nd) * ((2 + |γ|) * (2 + |t|)) ^ A := by
        gcongr
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring
  exact GammaZeroContour.gamma_zero_contour_generic a (2:ℝ) X f ha1 ha0 (by linarith) hXp hfd.differentiableOn
    hf0 hGrowth

theorem gamma_zero_contour_raw
    (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (U : ℝ) (hU : 2 ≤ U) (hUq : U ≤ frequencyNorm D.recipe u)
    (hUq2 : frequencyNorm D.recipe u < 2 * U)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hgs : ∀ z : ℂ, 1 < z.re →
      g z = Detector.idealLSeries F (RawFixed.FixedData.primMinus D u).character z)
    (β γ : ℝ) (hβ : DetectorDef.σ₀ ≤ β) (hβ1 : β ≤ 1)
    (hz : DetectorDef.IsLZero (RawFixed.FixedData.primMinus D u) ((β : ℂ) + (γ : ℂ) * Complex.I)) :
    let s : ℂ := (β : ℂ) + (γ : ℂ) * Complex.I
    let f : ℂ → ℂ := fun v =>
      g (s + v) * DetectorDef.D F U (RawFixed.FixedData.primMinus D u).character (s + v)
    let X : ℝ := U ^ DetectorDef.r
    let a : ℝ := DetectorDef.c - β
    MeasureTheory.Integrable (fun t : ℝ =>
      Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
        f ((a : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)) ∧
    MeasureTheory.Integrable (fun t : ℝ =>
      Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
        f (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ∧
    (∫ t : ℝ, Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
        f (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ, Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
        f ((a : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  exact contour_core D.recipe.A (RawFixed.FixedData.primMinus D u)
    (RawFixed.FixedData.prim_nonprincipal D u hu).2 U hU g hg hgs β γ hβ hβ1 hz

theorem shifted_gamma_norm :
    ∃ A_F : ℝ, 0 ≤ A_F ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        ∀ U : ℝ, 2 ≤ U → U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
        (∀ z : ℂ, 1 < z.re →
          g z = Detector.idealLSeries F (RawFixed.FixedData.primMinus D u).character z) →
        ∀ β γ : ℝ, DetectorDef.σ₀ ≤ β → β ≤ 1 →
          ‖∫ t : ℝ,
              Complex.Gamma (((DetectorDef.c - β : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
              (g (((β : ℂ) + (γ : ℂ) * Complex.I) +
                    (((DetectorDef.c - β : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
                DetectorDef.D F U (RawFixed.FixedData.primMinus D u).character
                  (((β : ℂ) + (γ : ℂ) * Complex.I) +
                    (((DetectorDef.c - β : ℝ) : ℂ) + (t : ℂ) * Complex.I))) *
              ((U ^ DetectorDef.r : ℝ) : ℂ) ^
                (((DetectorDef.c - β : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * U ^ (DetectorDef.qExp * (1 - DetectorDef.c) + (1 - DetectorDef.c) / 2 +
                DetectorDef.r * (DetectorDef.c - β) + ε) * (2 + |γ|) ^ A_F := by
  obtain ⟨A, hA, hconv⟩ := RawSharpConvexity31.minus_detector_line D
  obtain ⟨Ci, hCi, hinv⟩ := DetectorInverseBound.detector_inverse_bound F
  obtain ⟨CA, hCA, hmom⟩ := GammaShiftNorm.gamma_moment_shift A hA
  refine ⟨A, hA, fun ε hε => ?_⟩
  obtain ⟨Cc, hCc, hc⟩ := hconv ε hε
  refine ⟨Ci * Cc * CA, by positivity, ?_⟩
  intro u hu U hU hUq hUq2 g hg hgs β γ hβ hβ1
  have hcv : DetectorDef.c = 1 / 100 := rfl
  have hσ : DetectorDef.σ₀ = 22 / 25 := rfl
  rw [hσ] at hβ
  have hU0 : 0 < U := by linarith
  set a : ℝ := DetectorDef.c - β with ha
  have haI : a ∈ Set.Icc (-(99 / 100 : ℝ)) (-(87 / 100 : ℝ)) := by
    rw [ha, hcv]; constructor <;> linarith
  obtain ⟨hint, hle⟩ := hmom a haI γ
  set E : ℝ := DetectorDef.qExp * (1 - DetectorDef.c)
  have hpt : ∀ t : ℝ, ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
      (g (((β : ℂ) + (γ : ℂ) * Complex.I) + ((a : ℂ) + (t : ℂ) * Complex.I)) *
        DetectorDef.D F U (RawFixed.FixedData.primMinus D u).character (((β : ℂ) + (γ : ℂ) * Complex.I) +
          ((a : ℂ) + (t : ℂ) * Complex.I))) *
      ((U ^ DetectorDef.r : ℝ) : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (Ci * Cc * U ^ (E + (1 - DetectorDef.c) / 2 + DetectorDef.r * a + ε)) *
        (‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |γ + t|) ^ A) := by
    intro t
    have hs : ((β : ℂ) + (γ : ℂ) * Complex.I) + ((a : ℂ) + (t : ℂ) * Complex.I) =
        ((1 / 100 : ℝ) : ℂ) + ((γ + t : ℝ) : ℂ) * Complex.I := by
      rw [ha, hcv]; push_cast; ring
    have hs' : ((β : ℂ) + (γ : ℂ) * Complex.I) + ((a : ℂ) + (t : ℂ) * Complex.I) =
        ((DetectorDef.c : ℝ) : ℂ) + ((γ + t : ℝ) : ℂ) * Complex.I := by
      rw [hs, hcv]
    rw [hs']
    have h1 := hc u hu U hU hUq hUq2 g hg hgs (γ + t)
    rw [← hcv] at h1
    have h2 := hinv U hU (γ + t) (RawFixed.FixedData.primMinus D u)
    have hX : ‖((U ^ DetectorDef.r : ℝ) : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)‖ =
        U ^ (DetectorDef.r * a) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hU0 _)]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_self,
        add_zero]
      rw [← Real.rpow_mul hU0.le]
    have hexp : U ^ (E + (1 - DetectorDef.c) / 2 + DetectorDef.r * a + ε) =
        U ^ E * U ^ ((99 / 200 : ℝ) + ε) * U ^ (DetectorDef.r * a) := by
      rw [← Real.rpow_add hU0, ← Real.rpow_add hU0]
      congr 1
      rw [hcv]; ring
    rw [hexp, norm_mul, norm_mul, norm_mul, hX]
    have hG := norm_nonneg (Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I))
    have hP : 0 ≤ (2 + |γ + t|) ^ A := by positivity
    have hX0 : 0 ≤ U ^ (DetectorDef.r * a) := by positivity
    calc _ ≤ ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ *
          ((Cc * U ^ ((99 / 200 : ℝ) + ε) * (2 + |γ + t|) ^ A) * (Ci * U ^ E)) *
          U ^ (DetectorDef.r * a) := by
          gcongr
      _ = _ := by ring
  have hmeas : Integrable (fun t : ℝ =>
      (Ci * Cc * U ^ (E + (1 - DetectorDef.c) / 2 + DetectorDef.r * a + ε)) *
        (‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |γ + t|) ^ A)) :=
    hint.const_mul _
  refine (norm_integral_le_of_norm_le hmeas (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul]
  have hK : 0 ≤ Ci * Cc * U ^ (E + (1 - DetectorDef.c) / 2 + DetectorDef.r * a + ε) := by
    positivity
  calc _ ≤ (Ci * Cc * U ^ (E + (1 - DetectorDef.c) / 2 + DetectorDef.r * a + ε)) *
        (CA * (2 + |γ|) ^ A) := mul_le_mul_of_nonneg_left hle hK
    _ = _ := by ring

theorem detector_shift :
    ∃ A_F : ℝ, 0 ≤ A_F ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        ∀ U : ℝ, 2 ≤ U → U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
        ∀ β γ : ℝ, DetectorDef.σ₀ ≤ β → β ≤ 1 →
          DetectorDef.IsLZero (RawFixed.FixedData.primMinus D u)
            ((β : ℂ) + (γ : ℂ) * Complex.I) →
          ‖DetectorShift.smoothedSum F U β γ (RawFixed.FixedData.primMinus D u)‖ ≤
            C * U ^ (-(3 / 1250 : ℝ) + ε) * (2 + |γ|) ^ A_F := by
  obtain ⟨A, hA, hshift⟩ := shifted_gamma_norm D
  refine ⟨A, hA, fun ε hε => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hshift ε hε
  refine ⟨C, hC, ?_⟩
  intro u hu U hU hUq hUq2 β γ hβ hβ1 hz0
  have hz1 := hz0
  have hnp : ¬ (RawFixed.FixedData.primMinus D u).character.IsPrincipal :=
    (RawFixed.FixedData.prim_nonprincipal D u hu).2
  have hσ : DetectorDef.σ₀ = (22 / 25 : ℝ) := rfl
  have hβ22 : (22 / 25 : ℝ) ≤ β := by
    have h := hβ
    rw [hσ] at h
    exact h
  have hU0 : (0 : ℝ) < U := by linarith
  have hU1 : (1 : ℝ) ≤ U := by linarith

  obtain ⟨G, hGdiff, hGL⟩ := RowHeckeBridge.hecke_exists_entire D.recipe.A (RawFixed.FixedData.primMinus D u) hnp
  have hGs : ∀ z : ℂ, 1 < z.re →
      G z = Detector.idealLSeries F (RawFixed.FixedData.primMinus D u).character z := by
    intro z hz
    rw [hGL z (by linarith), RowHeckeBridge.hecke_eq_idealLSeries D.recipe.A (RawFixed.FixedData.primMinus D u) hnp z hz]
  obtain ⟨hre, g, hgan, hgs, hg0⟩ := hz0
  have hre' : 0 < ((β : ℂ) + (γ : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im]
    linarith
  have hGz : G ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 := by
    rw [hGL _ hre', ← RowHeckeBridge.eq_hecke_of_analyticOn D.recipe.A (RawFixed.FixedData.primMinus D u) hnp hgan
      hgs _ hre', hg0]

  have hzc := gamma_zero_contour_raw D u hu U hU hUq hUq2 G hGdiff hGs β γ hβ hβ1 hz1
  have hbnd := hbound u hu U hU hUq hUq2 G hGdiff hGs β γ hβ hβ1

  obtain ⟨_, _, hid⟩ := DetectorMellin.detector_mellin_identity F U hU (RawFixed.FixedData.primMinus D u) hnp β
    ⟨hβ, hβ1⟩ γ 2 (by norm_num)
  have hS : DetectorShift.smoothedSum F U β γ (RawFixed.FixedData.primMinus D u) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, DetectorMellin.mellinIntegrand F U (RawFixed.FixedData.primMinus D u) β γ
        (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := hid

  have hcp : ∀ v : ℂ, (U : ℂ) ^ ((DetectorDef.r : ℂ) * v) =
      (((U ^ DetectorDef.r : ℝ)) : ℂ) ^ v := by
    intro v
    rw [Complex.ofReal_cpow hU0.le, ← Complex.cpow_mul]
    all_goals
      rw [← Complex.ofReal_log hU0.le, ← Complex.ofReal_mul, Complex.ofReal_im]
      linarith [Real.pi_pos]
  have hpt : ∀ v : ℂ, 1 < ((β : ℂ) + (γ : ℂ) * Complex.I + v).re →
      DetectorMellin.mellinIntegrand F U (RawFixed.FixedData.primMinus D u) β γ v =
        Complex.Gamma v * (G ((β : ℂ) + (γ : ℂ) * Complex.I + v) *
          DetectorDef.D F U (RawFixed.FixedData.primMinus D u).character ((β : ℂ) + (γ : ℂ) * Complex.I + v)) *
          (((U ^ DetectorDef.r : ℝ)) : ℂ) ^ v := by
    intro v hv
    unfold DetectorMellin.mellinIntegrand
    rw [hGs _ hv, hcp v]
    ring
  have hint_eq : (∫ t : ℝ, DetectorMellin.mellinIntegrand F U (RawFixed.FixedData.primMinus D u) β γ
        (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ, Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
        (G ((β : ℂ) + (γ : ℂ) * Complex.I + (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
          DetectorDef.D F U (RawFixed.FixedData.primMinus D u).character
            ((β : ℂ) + (γ : ℂ) * Complex.I + (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) *
        (((U ^ DetectorDef.r : ℝ)) : ℂ) ^ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    congr 1
    funext t
    apply hpt
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.mul_im]
    linarith

  have hE : DetectorDef.qExp * (1 - DetectorDef.c) + (1 - DetectorDef.c) / 2 +
      DetectorDef.r * (DetectorDef.c - β) ≤ -(3 / 1250 : ℝ) := by
    simp only [DetectorDef.qExp, DetectorDef.c, DetectorDef.r]
    linarith
  have hpow : U ^ (DetectorDef.qExp * (1 - DetectorDef.c) + (1 - DetectorDef.c) / 2 +
      DetectorDef.r * (DetectorDef.c - β) + ε) ≤ U ^ (-(3 / 1250 : ℝ) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
  have hm : ‖∫ t : ℝ, DetectorMellin.mellinIntegrand F U (RawFixed.FixedData.primMinus D u) β γ
        (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      C * U ^ (-(3 / 1250 : ℝ) + ε) * (2 + |γ|) ^ A := by
    rw [hint_eq.trans hzc.2.2]
    exact (hbnd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hC.le) (by positivity)))
  have hπ : (1 : ℝ) ≤ ‖(2 * (Real.pi : ℂ))‖ := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hinv : ‖(2 * (Real.pi : ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hπ
  rw [hS, norm_mul]
  calc ‖(2 * (Real.pi : ℂ))⁻¹‖ * ‖∫ t : ℝ, DetectorMellin.mellinIntegrand F U (RawFixed.FixedData.primMinus D u) β γ
        (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 1 * ‖∫ t : ℝ, DetectorMellin.mellinIntegrand F U (RawFixed.FixedData.primMinus D u) β γ
        (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
        mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hm

end

end DedekindZetaZeroFree.Quantitative.RawDetectorShift31
