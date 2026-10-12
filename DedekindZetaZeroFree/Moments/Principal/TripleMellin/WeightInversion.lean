module

public import DedekindZetaZeroFree.Moments.Principal.TripleMellin.PoissonOrbitEvaluation

@[expose] public section

namespace DedekindZetaZeroFree.NormalizedProbe.TripleMellin
open TripleMellinRaw
noncomputable section
open MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem sheet_inversion (P : PrincipalData A σ η hS)
    (N : MellinNormalizationData A σ η hS P) (T : ℝ) (hT : 0 < T) :
    Integrable (fun τ : ℝ => (principalMellinWeights A σ η hS P).M
      (2 + (τ : ℂ) * Complex.I) * (T : ℂ) ^ (-2 - (τ : ℂ) * Complex.I)) ∧
    ProbeSheet.envelope A P.finiteTrace P.additiveMeasure P.domain.measure P.W0 T =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ τ : ℝ,
        (principalMellinWeights A σ η hS P).M (2 + (τ : ℂ) * Complex.I) *
          (T : ℂ) ^ (-2 - (τ : ℂ) * Complex.I) := by
  have h := probe_sheet_mellin_estimates_of_disintegration F A
    P.finiteTrace P.continuousTrace P.traceCompatible (finiteTrace_nontrivial P N)
    P.additiveMeasure P.multiplicativeMeasure P.domain.measure
    P.additiveHaar P.multiplicativeHaar P.domain.haar N.disintegration
    (Classical.arbitrary _) P.W0 P.W1 P.annular P.compactSupport P.supportUnits
  exact h.2.2.2.2.2.2.2 2 T (by norm_num) hT

theorem realWeight_inversion (P : PrincipalData A σ η hS) (T : ℝ) (hT : 0 < T) :
    Integrable (fun τ : ℝ => (principalMellinWeights A σ η hS P).W1Hat
      (4 + (τ : ℂ) * Complex.I) * (T : ℂ) ^ (-4 - (τ : ℂ) * Complex.I)) ∧
    (P.W1 T : ℂ) = ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ τ : ℝ,
      (principalMellinWeights A σ η hS P).W1Hat (4 + (τ : ℂ) * Complex.I) *
        (T : ℂ) ^ (-4 - (τ : ℂ) * Complex.I) := by
  have hconv := ProbeSheet.MellinProof.realWeight_mellin_convergent P.W1 (4 : ℂ)
  have heq : probeRealWeightMellin P.W1 = mellin (fun x => (P.W1 x : ℂ)) := by
    funext z
    exact (ProbeSheet.MellinProof.mellin_eq_explicit (fun x => (P.W1 x : ℂ)) z).symm
  have hdiff := ProbeSheet.MellinProof.realWeight_mellin_differentiable P.W1
  obtain ⟨C, hC, hb⟩ := ProbeSheet.MellinProof.realWeight_mellin_rapid_on_strip
    P.W1 4 4 2 (by norm_num)
  have hM := ProbeSheet.MellinProof.vertical_integrable_of_quadratic_decay
    (probeRealWeightMellin P.W1) 4 C
    ((hdiff.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (fun τ => hb 4 (by simp) τ)
  apply ProbeSheet.MellinProof.mellin_inversion_explicit
    (fun x => (P.W1 x : ℂ)) (probeRealWeightMellin P.W1) 4 T hT hconv hM
    (fun τ => congrFun heq.symm _) (Complex.continuous_ofReal.comp P.W1.smooth.continuous).continuousAt

theorem gaussian_inversion (T : ℝ) (hT : 0 < T) :
    Integrable (fun τ : ℝ => Complex.exp ((5 + (τ : ℂ) * Complex.I) ^ 2) *
      (T : ℂ) ^ (-5 - (τ : ℂ) * Complex.I)) ∧
    (thetaReflectionGaussian T : ℂ) = ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ τ : ℝ,
      Complex.exp ((5 + (τ : ℂ) * Complex.I) ^ 2) *
        (T : ℂ) ^ (-5 - (τ : ℂ) * Complex.I) := by
  let L : ℂ := Real.log T
  have hk (τ : ℝ) :
      Complex.exp ((5 + (τ : ℂ) * Complex.I) ^ 2) *
        (T : ℂ) ^ (-5 - (τ : ℂ) * Complex.I) =
      Complex.exp (- (τ : ℂ) ^ 2 + ((10 - L) * Complex.I) * τ + (25 - 5 * L)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hT)),
      ← Complex.ofReal_log hT.le, ← Complex.exp_add]
    congr 1
    dsimp [L]
    calc
      _ = (τ : ℂ) ^ 2 * Complex.I ^ 2 +
          ((10 - (Real.log T : ℂ)) * Complex.I) * τ + (25 - 5 * (Real.log T : ℂ)) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  simp_rw [hk]
  refine ⟨?_, ?_⟩
  · simpa using integrable_cexp_quadratic (b := (1 : ℂ)) (by norm_num)
      ((10 - L) * Complex.I) (25 - 5 * L)
  · have hi := integral_cexp_quadratic (b := (-1 : ℂ)) (by norm_num)
      ((10 - L) * Complex.I) (25 - 5 * L)
    simp only [neg_one_mul] at hi
    rw [hi]
    rw [thetaReflectionGaussian_of_pos T hT]
    have hexp : 25 - 5 * L - ((10 - L) * Complex.I) ^ 2 / (4 * (-1 : ℂ)) =
        -(L ^ 2) / 4 := by
      rw [mul_pow, Complex.I_sq]
      ring
    rw [hexp]
    have hsqrt : ((Real.pi : ℂ) / -(-1 : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
      simp only [neg_neg, div_one]
      have hh := Complex.ofReal_cpow Real.pi_pos.le (1 / 2 : ℝ)
      norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hh
      rw [← hh, Real.sqrt_eq_rpow]
    rw [hsqrt]
    have he : Complex.exp (-L ^ 2 / 4) =
        (Real.exp (-Real.log T ^ 2 / 4) : ℂ) := by
      dsimp [L]
      norm_cast
    rw [he]
    push_cast
    have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hs : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))
    have hs2 : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
      exact_mod_cast Real.sq_sqrt Real.pi_pos.le
    field_simp
    exact hs2.symm

end
end DedekindZetaZeroFree.NormalizedProbe.TripleMellin
