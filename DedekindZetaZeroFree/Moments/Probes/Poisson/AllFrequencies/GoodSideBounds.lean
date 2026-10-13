module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.GoodNestedIntegrals

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawGoodSideBounds31

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory Set Filter Complex
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open DedekindZetaZeroFree.Quantitative.RawDetectorHeightPrefix31
open DedekindZetaZeroFree.Quantitative.RawGoodNestedControls31
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

private theorem kernel_integrable_two :
    Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(2:ℝ))) := by
  apply integrable_one_add_norm
  simp

private theorem kernel_mass_nonneg : 0 ≤ ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ)) :=
  integral_nonneg (fun t => by positivity)

private theorem setIntegral_norm_le_weight {s : Set ℝ} (hs : MeasurableSet s) (f : ℝ → ℂ)
    (c : ℝ) (hc : 0 ≤ c) (h : ∀ t ∈ s, ‖f t‖ ≤ c * (1 + ‖t‖) ^ (-(2:ℝ))) :
    ‖∫ t in s, f t‖ ≤ c * ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ)) := by
  have hint : Integrable (fun t : ℝ => c * (1 + ‖t‖) ^ (-(2:ℝ))) :=
    kernel_integrable_two.const_mul c
  calc ‖∫ t in s, f t‖ ≤ ∫ t in s, c * (1 + ‖t‖) ^ (-(2:ℝ)) :=
        norm_integral_le_of_norm_le hint.integrableOn (ae_restrict_of_forall_mem hs h)
    _ ≤ ∫ t : ℝ, c * (1 + ‖t‖) ^ (-(2:ℝ)) :=
        setIntegral_le_integral hint (Eventually.of_forall (fun t => mul_nonneg hc (by positivity)))
    _ = c * ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ)) := integral_const_mul c _

private theorem norm_two_pi_inv : ‖(2 * (Real.pi : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
  have h : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [norm_inv, h, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

private theorem norm_two_pi_I_inv : ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
  have h : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [norm_inv, norm_mul, Complex.norm_I, mul_one, h, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

theorem central_bound (A ρ : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (hρ : HeightSpec D A ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ u : Frequency D.recipe,
      u ≠ principalFrequency D.recipe → U ≤ frequencyNorm D.recipe u →
      frequencyNorm D.recipe u < 2 * U → u ∉ FixedData.rawExceptionalSet D ρ U →
      ∀ Z : ℝ, 2 ≤ Z →
        ‖(2 * (Real.pi : ℂ))⁻¹ *
            (∫ t in Set.Icc (-(U ^ ρ)) (U ^ ρ),
              Iwz D u ((Scales.goodLine : ℂ) + (t : ℂ) * I) Scales.wLine Scales.zLine Z)‖ ≤
          C * Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε) := by
  obtain ⟨C1, hC1, U₀, hU₀, hb⟩ :=
    Iwz_decay_rect D A ρ hA hconv hρ ε hε 2 (by norm_num)
  have hK := kernel_mass_nonneg
  have hCpos : 0 < (2 * Real.pi)⁻¹ * (C1 * ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ))) + 1 := by
    have : 0 ≤ (2 * Real.pi)⁻¹ * (C1 * ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ))) :=
      mul_nonneg (by positivity) (mul_nonneg hC1.le hK)
    linarith
  refine ⟨_, hCpos, U₀, hU₀, ?_⟩
  intro U hU u hu1 hu2 hu3 hu4 Z hZ
  have hU1 : 1 ≤ U := by linarith
  have hUpos : 0 < U := by linarith
  have hUρ : 0 ≤ U ^ ρ := Real.rpow_nonneg hUpos.le _
  have hJ : ‖∫ t in Set.Icc (-(U ^ ρ)) (U ^ ρ),
      Iwz D u ((Scales.goodLine : ℂ) + (t : ℂ) * I) Scales.wLine Scales.zLine Z‖ ≤
      C1 * Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε) *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ)) := by
    apply setIntegral_norm_le_weight measurableSet_Icc _ _
    · exact mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg (by linarith) _))
        (Real.rpow_nonneg hUpos.le _)
    · intro t ht
      have hab : |t| ≤ U ^ ρ := abs_le.mpr ⟨ht.1, ht.2⟩
      have hre : ((Scales.goodLine : ℂ) + (t : ℂ) * I).re = Scales.goodLine := by simp
      have him : ((Scales.goodLine : ℂ) + (t : ℂ) * I).im = t := by simp
      have key := hb U hU u hu1 hu2 hu3 hu4 ((Scales.goodLine : ℂ) + (t : ℂ) * I) Z (by linarith)
        (by rw [hre]) (by rw [hre]; norm_num [Scales.goodLine, Scales.rightLine, Scales.contourOffset])
        (by rw [him]; linarith)
      rw [hre, him] at key
      rw [Real.norm_eq_abs]
      exact key
  calc ‖(2 * (Real.pi : ℂ))⁻¹ *
            (∫ t in Set.Icc (-(U ^ ρ)) (U ^ ρ),
              Iwz D u ((Scales.goodLine : ℂ) + (t : ℂ) * I) Scales.wLine Scales.zLine Z)‖
      = (2 * Real.pi)⁻¹ * ‖∫ t in Set.Icc (-(U ^ ρ)) (U ^ ρ),
              Iwz D u ((Scales.goodLine : ℂ) + (t : ℂ) * I) Scales.wLine Scales.zLine Z‖ := by
        rw [norm_mul, norm_two_pi_inv]
    _ ≤ (2 * Real.pi)⁻¹ * (C1 * Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) *
          U ^ ((1 / 25 : ℝ) + ε) * ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ))) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = ((2 * Real.pi)⁻¹ * (C1 * ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ)))) *
          (Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε)) := by ring
    _ ≤ ((2 * Real.pi)⁻¹ * (C1 * ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ))) + 1) *
          (Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε)) := by
        apply mul_le_mul_of_nonneg_right (by linarith)
        exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hUpos.le _)
    _ = _ := by ring

theorem horizontal_bound (A ρ : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (hρ : HeightSpec D A ρ) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ u : Frequency D.recipe,
      u ≠ principalFrequency D.recipe → U ≤ frequencyNorm D.recipe u →
      frequencyNorm D.recipe u < 2 * U → u ∉ FixedData.rawExceptionalSet D ρ U →
      ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) → ∀ Z : ℝ, 2 ≤ Z →
        ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
            (intervalIntegral
              (fun σ : ℝ =>
                Iwz D u ((σ : ℂ) + ((sgn * U ^ ρ : ℝ) : ℂ) * I) Scales.wLine Scales.zLine Z)
              Scales.goodLine Scales.rightLine volume)‖ ≤
          C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (-B) := by
  have hρpos : 0 < ρ := hρ.1
  have hMpos : 0 < (B + 1) / ρ := div_pos (by linarith) hρpos
  obtain ⟨C1, hC1, U₀, hU₀, hb⟩ :=
    Iwz_decay_rect D A ρ hA hconv hρ (1 / 100) (by norm_num) ((B + 1) / ρ) hMpos
  have hlen : 0 ≤ |Scales.rightLine - Scales.goodLine| := abs_nonneg _
  have hCpos : 0 < (2 * Real.pi)⁻¹ * (C1 * |Scales.rightLine - Scales.goodLine|) + 1 := by
    have : 0 ≤ (2 * Real.pi)⁻¹ * (C1 * |Scales.rightLine - Scales.goodLine|) :=
      mul_nonneg (by positivity) (mul_nonneg hC1.le hlen)
    linarith
  refine ⟨_, hCpos, U₀, hU₀, ?_⟩
  intro U hU u hu1 hu2 hu3 hu4 sgn hsgn Z hZ
  have hU1 : 1 ≤ U := by linarith
  have hUpos : 0 < U := by linarith
  have hUρ : 0 < U ^ ρ := Real.rpow_pos_of_pos hUpos _
  have hx : Scales.goodLine ≤ Scales.rightLine := by
    unfold Scales.goodLine Scales.rightLine Scales.contourOffset; norm_num
  have hpt : ∀ σ ∈ Set.uIoc Scales.goodLine Scales.rightLine,
      ‖Iwz D u ((σ : ℂ) + ((sgn * U ^ ρ : ℝ) : ℂ) * I) Scales.wLine Scales.zLine Z‖ ≤
        C1 * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + 1 / 100) *
          U ^ (-(B + 1)) := by
    intro σ hσ
    rw [Set.uIoc_of_le hx] at hσ
    obtain ⟨h1, h2⟩ := hσ
    have him : ((σ : ℂ) + ((sgn * U ^ ρ : ℝ) : ℂ) * I).im = sgn * U ^ ρ := by simp
    have hre : ((σ : ℂ) + ((sgn * U ^ ρ : ℝ) : ℂ) * I).re = σ := by simp
    have habs : |sgn * U ^ ρ| = U ^ ρ := by
      rcases hsgn with rfl | rfl
      · simp [abs_of_pos hUρ]
      · simp [abs_of_pos hUρ]
    have key := hb U hU u hu1 hu2 hu3 hu4 ((σ : ℂ) + ((sgn * U ^ ρ : ℝ) : ℂ) * I) Z
      (by linarith) (by rw [hre]; linarith [h1, Scales.goodLine]) (by rw [hre]; linarith)
      (by rw [him, habs]; linarith)
    rw [hre, him, habs] at key
    have hZE : Z ^ (Scales.kernelExponent σ Scales.wLine Scales.zLine) ≤
        Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by unfold Scales.kernelExponent; linarith)
    have hpow : (1 + U ^ ρ) ^ (-((B + 1) / ρ)) ≤ U ^ (-(B + 1)) := by
      calc (1 + U ^ ρ) ^ (-((B + 1) / ρ)) ≤ (U ^ ρ) ^ (-((B + 1) / ρ)) :=
            Real.rpow_le_rpow_of_nonpos hUρ (by linarith)
              (neg_nonpos.mpr (div_nonneg (by linarith) hρpos.le))
        _ = U ^ (-(B + 1)) := by
            rw [← Real.rpow_mul hUpos.le]
            congr 1
            field_simp
    have hC1U : 0 ≤ C1 * Z ^ (Scales.kernelExponent σ Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + 1 / 100) :=
      mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg (by linarith) _))
        (Real.rpow_nonneg hUpos.le _)
    calc _ ≤ C1 * Z ^ (Scales.kernelExponent σ Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + 1 / 100) *
            (1 + U ^ ρ) ^ (-((B + 1) / ρ)) := key
      _ ≤ C1 * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + 1 / 100) *
            U ^ (-(B + 1)) := by
        apply mul_le_mul _ hpow (Real.rpow_nonneg (by linarith) _)
        · exact mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg (by linarith) _))
            (Real.rpow_nonneg hUpos.le _)
        · apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUpos.le _)
          exact mul_le_mul_of_nonneg_left hZE hC1.le
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ => Iwz D u ((σ : ℂ) + ((sgn * U ^ ρ : ℝ) : ℂ) * I) Scales.wLine Scales.zLine Z)
    (a := Scales.goodLine) (b := Scales.rightLine) hpt
  have hUB : U ^ ((1 / 25 : ℝ) + 1 / 100) * U ^ (-(B + 1)) ≤ U ^ (-B) := by
    rw [← Real.rpow_add hUpos]
    apply Real.rpow_le_rpow_of_exponent_le hU1
    norm_num
    linarith
  have hW : Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) *
      (U ^ ((1 / 25 : ℝ) + 1 / 100) * U ^ (-(B + 1))) ≤
      Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (-B) :=
    mul_le_mul_of_nonneg_left hUB (Real.rpow_nonneg (by linarith) _)
  have hVnonneg : 0 ≤ Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (-B) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hUpos.le _)
  have hnonneg : 0 ≤ (2 * Real.pi)⁻¹ * (C1 * |Scales.rightLine - Scales.goodLine|) :=
    mul_nonneg (by positivity) (mul_nonneg hC1.le hlen)
  calc ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
            (intervalIntegral
              (fun σ : ℝ =>
                Iwz D u ((σ : ℂ) + ((sgn * U ^ ρ : ℝ) : ℂ) * I) Scales.wLine Scales.zLine Z)
              Scales.goodLine Scales.rightLine volume)‖
      = (2 * Real.pi)⁻¹ * ‖intervalIntegral
              (fun σ : ℝ =>
                Iwz D u ((σ : ℂ) + ((sgn * U ^ ρ : ℝ) : ℂ) * I) Scales.wLine Scales.zLine Z)
              Scales.goodLine Scales.rightLine volume‖ := by
        rw [norm_mul, norm_two_pi_I_inv]
    _ ≤ (2 * Real.pi)⁻¹ * ((C1 * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) *
            U ^ ((1 / 25 : ℝ) + 1 / 100) * U ^ (-(B + 1))) * |Scales.rightLine - Scales.goodLine|) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = ((2 * Real.pi)⁻¹ * (C1 * |Scales.rightLine - Scales.goodLine|)) *
          (Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) *
            (U ^ ((1 / 25 : ℝ) + 1 / 100) * U ^ (-(B + 1)))) := by ring
    _ ≤ ((2 * Real.pi)⁻¹ * (C1 * |Scales.rightLine - Scales.goodLine|) + 1) *
          (Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (-B)) := by
        apply mul_le_mul (by linarith) hW
          (mul_nonneg (Real.rpow_nonneg (by linarith) _)
            (mul_nonneg (Real.rpow_nonneg hUpos.le _) (Real.rpow_nonneg hUpos.le _)))
          hCpos.le
    _ = _ := by ring

theorem tail_bound (A ρ : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (hρ : HeightSpec D A ρ) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ u : Frequency D.recipe,
      u ≠ principalFrequency D.recipe → U ≤ frequencyNorm D.recipe u →
      frequencyNorm D.recipe u < 2 * U → u ∉ FixedData.rawExceptionalSet D ρ U →
      ∀ Z : ℝ, 2 ≤ Z →
        ‖(2 * (Real.pi : ℂ))⁻¹ *
            (∫ t in {t : ℝ | U ^ ρ < |t|},
              Iwz D u ((Scales.rightLine : ℂ) + (t : ℂ) * I) Scales.wLine Scales.zLine Z)‖ ≤
          C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (-B) := by
  have hρpos : 0 < ρ := hρ.1
  have hMpos : 0 < (B + 1) / ρ := div_pos (by linarith) hρpos
  have hMneg : -((B + 1) / ρ) ≤ 0 := neg_nonpos.mpr hMpos.le
  obtain ⟨C1, hC1, hb⟩ :=
    Iwz_decay_right D A hA hconv (1 / 100) (by norm_num) (2 + (B + 1) / ρ) (by linarith)
  have hK := kernel_mass_nonneg
  have hCpos : 0 < (2 * Real.pi)⁻¹ * (C1 * ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ))) + 1 := by
    have : 0 ≤ (2 * Real.pi)⁻¹ * (C1 * ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ))) :=
      mul_nonneg (by positivity) (mul_nonneg hC1.le hK)
    linarith
  refine ⟨_, hCpos, 2, le_rfl, ?_⟩
  intro U hU u hu1 hu2 hu3 hu4 Z hZ
  have hUpos : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hUρ : 0 < U ^ ρ := Real.rpow_pos_of_pos hUpos _
  have hJ : ‖∫ t in {t : ℝ | U ^ ρ < |t|},
      Iwz D u ((Scales.rightLine : ℂ) + (t : ℂ) * I) Scales.wLine Scales.zLine Z‖ ≤
      C1 * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + 1 / 100) *
        U ^ (-(B + 1)) * ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ)) := by
    apply setIntegral_norm_le_weight (measurableSet_lt measurable_const continuous_abs.measurable)
      _ _
    · exact mul_nonneg (mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg (by linarith) _))
        (Real.rpow_nonneg hUpos.le _)) (Real.rpow_nonneg hUpos.le _)
    · intro t ht
      have ht' : U ^ ρ < |t| := ht
      have hre : ((Scales.rightLine : ℂ) + (t : ℂ) * I).re = Scales.rightLine := by simp
      have him : ((Scales.rightLine : ℂ) + (t : ℂ) * I).im = t := by simp
      have key := hb U hU u hu1 hu2 hu3 ((Scales.rightLine : ℂ) + (t : ℂ) * I) Z (by linarith) hre
      rw [him] at key
      rw [Real.norm_eq_abs]
      have hsplit : (1 + |t|) ^ (-(2 + (B + 1) / ρ)) =
          (1 + |t|) ^ (-(2:ℝ)) * (1 + |t|) ^ (-((B + 1) / ρ)) := by
        rw [← Real.rpow_add (by positivity)]
        congr 1
        ring
      have hpowM : (1 + |t|) ^ (-((B + 1) / ρ)) ≤ U ^ (-(B + 1)) := by
        calc (1 + |t|) ^ (-((B + 1) / ρ)) ≤ (U ^ ρ) ^ (-((B + 1) / ρ)) :=
              Real.rpow_le_rpow_of_nonpos hUρ (by linarith) hMneg
          _ = U ^ (-(B + 1)) := by
              rw [← Real.rpow_mul hUpos.le]
              congr 1
              field_simp
      have hk2 : 0 ≤ (1 + |t|) ^ (-(2:ℝ)) := by positivity
      have hC0 : 0 ≤ C1 * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) :=
        mul_nonneg hC1.le (Real.rpow_nonneg (by linarith) _)
      rw [hsplit] at key
      have hC0' : 0 ≤ C1 * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) *
          U ^ ((1 / 25 : ℝ) + 1 / 100) := mul_nonneg hC0 (Real.rpow_nonneg hUpos.le _)
      calc _ ≤ C1 * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + 1 / 100) *
              ((1 + |t|) ^ (-(2:ℝ)) * (1 + |t|) ^ (-((B + 1) / ρ))) := key
        _ ≤ C1 * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + 1 / 100) *
              ((1 + |t|) ^ (-(2:ℝ)) * U ^ (-(B + 1))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpowM hk2) hC0'
        _ = C1 * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + 1 / 100) *
              U ^ (-(B + 1)) * (1 + |t|) ^ (-(2:ℝ)) := by ring
  have hUB : U ^ ((1 / 25 : ℝ) + 1 / 100) * U ^ (-(B + 1)) ≤ U ^ (-B) := by
    rw [← Real.rpow_add hUpos]
    apply Real.rpow_le_rpow_of_exponent_le hU1
    norm_num
    linarith
  have hW : Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + 1 / 100) *
      U ^ (-(B + 1)) ≤ Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (-B) := by
    calc _ = Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) *
          (U ^ ((1 / 25 : ℝ) + 1 / 100) * U ^ (-(B + 1))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hUB (Real.rpow_nonneg (by linarith) _)
  have hVnonneg : 0 ≤ Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (-B) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hUpos.le _)
  have hnonneg : 0 ≤ (2 * Real.pi)⁻¹ * (C1 * ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ))) :=
    mul_nonneg (by positivity) (mul_nonneg hC1.le hK)
  calc ‖(2 * (Real.pi : ℂ))⁻¹ *
            (∫ t in {t : ℝ | U ^ ρ < |t|},
              Iwz D u ((Scales.rightLine : ℂ) + (t : ℂ) * I) Scales.wLine Scales.zLine Z)‖
      = (2 * Real.pi)⁻¹ * ‖∫ t in {t : ℝ | U ^ ρ < |t|},
              Iwz D u ((Scales.rightLine : ℂ) + (t : ℂ) * I) Scales.wLine Scales.zLine Z‖ := by
        rw [norm_mul, norm_two_pi_inv]
    _ ≤ (2 * Real.pi)⁻¹ * (C1 * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) *
            U ^ ((1 / 25 : ℝ) + 1 / 100) * U ^ (-(B + 1)) * ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ))) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = ((2 * Real.pi)⁻¹ * (C1 * ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ)))) *
          (Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + 1 / 100) *
            U ^ (-(B + 1))) := by ring
    _ ≤ ((2 * Real.pi)⁻¹ * (C1 * ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ)))) *
          (Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (-B)) :=
        mul_le_mul_of_nonneg_left hW hnonneg
    _ ≤ ((2 * Real.pi)⁻¹ * (C1 * ∫ t : ℝ, (1 + ‖t‖) ^ (-(2:ℝ))) + 1) *
          (Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (-B)) :=
        mul_le_mul_of_nonneg_right (by linarith) hVnonneg
    _ = _ := by ring

end

end DedekindZetaZeroFree.Quantitative.RawGoodSideBounds31
