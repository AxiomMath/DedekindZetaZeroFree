module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.InitialKernel

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawCompactScale31

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawInitialKernel31
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def Einit : ℝ := Scales.kernelExponent 4 4 2

theorem Einit_pos : 0 < Einit := by
  unfold Einit Scales.kernelExponent Scales.xExponent Scales.smoothingExponent Scales.yExponent; norm_num

theorem norm_rawKernel_scale (u : Frequency D.recipe) (ξ w z : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) (hz : z.re = 2) (Z : ℝ) (hZ : 0 < Z) :
    ‖RawFixed.FixedData.rawKernel D u ξ w z Z‖ =
      (Z / 2) ^ Einit * ‖RawFixed.FixedData.rawKernel D u ξ w z 2‖ := by
  set s : ℂ := ((Scales.xExponent / 2 : ℝ) : ℂ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z + (Scales.yExponent : ℂ) * (w - 1)
    with hs
  set Rst : ℂ := Complex.exp ((ξ + z - 1) ^ 2) * D.M z * D.W1Hat w *
    (frequencyNorm D.recipe u : ℂ) ^ (-z) * RawFixed.FixedData.rawFactor D u ξ w z with hR
  have hK : ∀ Y : ℝ, RawFixed.FixedData.rawKernel D u ξ w z Y = (Y : ℂ) ^ s * Rst := by
    intro Y
    unfold RawFixed.FixedData.rawKernel
    rw [hs, hR]
    ring
  have hre : s.re = Einit := by
    rw [hs]
    simp [Einit, Scales.kernelExponent, hξ, hw, hz]
  have hN : ∀ Y : ℝ, 0 < Y →
      ‖RawFixed.FixedData.rawKernel D u ξ w z Y‖ = Y ^ Einit * ‖Rst‖ := by
    intro Y hY
    rw [hK, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY, hre]
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [hN Z hZ, hN 2 h2, Real.div_rpow hZ.le h2.le]
  have : (0 : ℝ) < 2 ^ Einit := Real.rpow_pos_of_pos h2 _
  field_simp

theorem norm_rawInitialIntegrand_scale (u : Frequency D.recipe) (Z : ℝ) (hZ : 0 < Z)
    (t : ℝ × ℝ × ℝ) :
    ‖rawInitialIntegrand D u Z t‖ = (Z / 2) ^ Einit * ‖rawInitialIntegrand D u 2 t‖ := by
  unfold rawInitialIntegrand
  exact norm_rawKernel_scale D u _ _ _ (by simp) (by simp) (by simp) Z hZ

theorem integral_norm_rawInitialIntegrand_scale (u : Frequency D.recipe) (Z : ℝ) (hZ : 0 < Z) :
    ∫ t : ℝ × ℝ × ℝ, ‖rawInitialIntegrand D u Z t‖ =
      (Z / 2) ^ Einit * ∫ t : ℝ × ℝ × ℝ, ‖rawInitialIntegrand D u 2 t‖ := by
  rw [← integral_const_mul]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun t => norm_rawInitialIntegrand_scale D u Z hZ t)

theorem norm_rawinitialRowIntegral_le (u : Frequency D.recipe) (Z : ℝ) :
    ‖rawinitialRowIntegral D u Z‖ ≤
      ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖ * ∫ t : ℝ × ℝ × ℝ, ‖rawInitialIntegrand D u Z t‖ := by
  unfold rawinitialRowIntegral
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)

theorem omittedSum_norm_le_scale :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z : ℝ, 0 < Z →
      ‖PoissonFrequencyDecomposition.omittedSum D Z‖ ≤ C * (Z / 2) ^ Einit := by
  have hsum := rawInitialIntegrand_norm_summable D 2 (by norm_num)
  set c : ℝ := ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖
  refine ⟨c * ∑' f : TwistedProbeRowDefinitions.TwistedRow D,
    ∫ t : ℝ × ℝ × ℝ, ‖rawInitialIntegrand D f.val 2 t‖,
    mul_nonneg (norm_nonneg _) (tsum_nonneg fun f => integral_nonneg fun t => norm_nonneg _),
    fun Z hZ => ?_⟩
  have hsub : Summable (fun f : TwistedProbeRowDefinitions.TwistedRow D =>
      ∫ t : ℝ × ℝ × ℝ, ‖rawInitialIntegrand D f.val 2 t‖) :=
    hsum.comp_injective Subtype.val_injective
  have hmaj : Summable (fun f : TwistedProbeRowDefinitions.TwistedRow D =>
      c * ((Z / 2) ^ Einit * ∫ t : ℝ × ℝ × ℝ, ‖rawInitialIntegrand D f.val 2 t‖)) :=
    (hsub.mul_left ((Z / 2) ^ Einit)).mul_left c
  rw [omittedSum_eq_twisted D Z hZ]
  have hle : ∀ f : TwistedProbeRowDefinitions.TwistedRow D,
      ‖rawinitialRowIntegral D f.val Z‖ ≤
        c * ((Z / 2) ^ Einit * ∫ t : ℝ × ℝ × ℝ, ‖rawInitialIntegrand D f.val 2 t‖) := by
    intro f
    refine (norm_rawinitialRowIntegral_le D f.val Z).trans ?_
    rw [integral_norm_rawInitialIntegrand_scale D f.val Z hZ]
  refine (norm_tsum_le_tsum_norm (hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) hle)).trans ?_
  refine ((hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) hle).tsum_le_tsum hle hmaj).trans ?_
  rw [tsum_mul_left, tsum_mul_left]
  apply le_of_eq
  ring

theorem omittedSum_norm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖PoissonFrequencyDecomposition.omittedSum D Z‖ ≤ C * Z ^ Scales.kernelExponent 4 4 2 := by
  obtain ⟨C, hC, h⟩ := omittedSum_norm_le_scale D
  have h2 : (0 : ℝ) < 2 ^ Einit := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨(C + 1) / 2 ^ Einit, by positivity, fun Z hZ => ?_⟩
  have hZ0 : 0 < Z := by linarith
  refine (h Z hZ0).trans ?_
  rw [Real.div_rpow hZ0.le (by norm_num)]
  change C * (Z ^ Einit / 2 ^ Einit) ≤ (C + 1) / 2 ^ Einit * Z ^ Einit
  have : (0 : ℝ) ≤ Z ^ Einit := Real.rpow_nonneg hZ0.le _
  rw [mul_div_assoc', div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ h2.le
  nlinarith

theorem omittedSum_locally_bounded (T : ℝ) (hT : 2 ≤ T) :
    ∃ M : ℝ, ∀ Z : ℝ, 2 ≤ Z → Z ≤ T → ‖PoissonFrequencyDecomposition.omittedSum D Z‖ ≤ M := by
  obtain ⟨C, hC, h⟩ := omittedSum_norm_le D
  refine ⟨C * T ^ Scales.kernelExponent 4 4 2, fun Z hZ hZT => (h Z hZ).trans ?_⟩
  have hE : 0 < Scales.kernelExponent 4 4 2 := Einit_pos
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by linarith) hZT hE.le) hC.le

theorem bound_all_of_bound_ge {f : ℝ → ℂ} {p Z₀ C : ℝ} (hp : 0 < p) (hZ₀ : 2 ≤ Z₀)
    (hloc : ∀ T : ℝ, 2 ≤ T → ∃ M : ℝ, ∀ Z : ℝ, 2 ≤ Z → Z ≤ T → ‖f Z‖ ≤ M)
    (hbd : ∀ Z : ℝ, Z₀ ≤ Z → ‖f Z‖ ≤ C * Z ^ p) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ Z : ℝ, 2 ≤ Z → ‖f Z‖ ≤ C' * Z ^ p := by
  obtain ⟨M, hM⟩ := hloc Z₀ hZ₀
  have h2 : (0 : ℝ) < 2 ^ p := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨max C 0 + |M| / 2 ^ p + 1, by positivity, fun Z hZ => ?_⟩
  have hZp : 0 ≤ Z ^ p := Real.rpow_nonneg (by linarith) _
  have hpos : 0 ≤ |M| / 2 ^ p := by positivity
  by_cases hZZ : Z₀ ≤ Z
  · refine (hbd Z hZZ).trans ?_
    nlinarith [le_max_left C 0, le_max_right C 0]
  · have hZZ' : Z ≤ Z₀ := (not_le.mp hZZ).le
    have h1 := hM Z hZ hZZ'
    have h3 : (2 : ℝ) ^ p ≤ Z ^ p := Real.rpow_le_rpow (by norm_num) hZ hp.le
    have h4 : |M| / 2 ^ p * 2 ^ p ≤ |M| / 2 ^ p * Z ^ p :=
      mul_le_mul_of_nonneg_left h3 hpos
    rw [div_mul_cancel₀ _ h2.ne'] at h4
    have := le_abs_self M
    nlinarith [le_max_right C 0, le_max_left C 0]

theorem omittedSum_bound_all_of_bound_ge {p Z₀ C : ℝ} (hp : 0 < p) (hZ₀ : 2 ≤ Z₀)
    (hbd : ∀ Z : ℝ, Z₀ ≤ Z → ‖PoissonFrequencyDecomposition.omittedSum D Z‖ ≤ C * Z ^ p) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖PoissonFrequencyDecomposition.omittedSum D Z‖ ≤ C' * Z ^ p :=
  bound_all_of_bound_ge hp hZ₀ (omittedSum_locally_bounded D) hbd

end

end DedekindZetaZeroFree.Quantitative.RawCompactScale31
