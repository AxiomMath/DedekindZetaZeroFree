module

public import DedekindZetaZeroFree.Moments.Principal.TripleMellin.OrbitReindexing
public import DedekindZetaZeroFree.Moments.Principal.TripleMellin.WeightInversion
public import DedekindZetaZeroFree.Moments.Principal.TripleMellin.HeightShear

@[expose] public section

namespace DedekindZetaZeroFree.NormalizedProbe.TripleMellin.TermRace
noncomputable section
open MeasureTheory
open TripleMellinRaw
open scoped NumberField Classical

lemma cpow_positive (x : ℝ) (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ s = comparisonRealPower x s := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx)),
    ← Complex.ofReal_log hx.le]
  simp [comparisonRealPower, mul_comm]

lemma power_neg_one (x : ℝ) (hx : 0 < x) :
    comparisonRealPower x (-1) = (x : ℂ)⁻¹ := by
  rw [← cpow_positive x hx, Complex.cpow_neg_one]

lemma power_half (x : ℝ) (hx : 0 < x) :
    comparisonRealPower x (1 / 2) = (Real.sqrt x : ℂ) := by
  rw [← cpow_positive x hx]
  have h := Complex.ofReal_cpow hx.le (1 / 2 : ℝ)
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  rw [← h, Real.sqrt_eq_rpow]

lemma power_neg_half (x : ℝ) (hx : 0 < x) :
    comparisonRealPower x (-1 / 2) = (Real.sqrt x : ℂ)⁻¹ := by
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring]
  simp only [comparisonRealPower, neg_mul, Complex.exp_neg]
  exact congrArg Inv.inv (power_half x hx)

lemma power_balance (X Y Z c n s r u : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (hc : 0 < c) (hn : 0 < n)
    (hs : 0 < s) (hr : 0 < r) (hu : 0 < u) (ξ w z : ℂ) :
    (((Real.sqrt X / Y : ℝ) : ℂ) / ((Real.sqrt c : ℂ) * n * (c * n ^ 3))) *
      ((c * n ^ 3 / Z : ℝ) : ℂ) ^ (-(ξ + z - 1)) *
      ((s / Y : ℝ) : ℂ) ^ (-w) *
      ((X * (u * r ^ 6) / (c * n ^ 3) : ℝ) : ℂ) ^ (-z) =
    comparisonRealPower X (1 / 2 - z) * comparisonRealPower Z (ξ + z - 1) *
      comparisonRealPower Y (w - 1) * comparisonRealPower u (-z) *
      comparisonRealPower c (-1 / 2 - ξ) * comparisonRealPower n (-1 - 3 * ξ) *
      comparisonRealPower s (-w) * comparisonRealPower r (-6 * z) := by
  have hq : 0 < c * n ^ 3 := by positivity
  rw [cpow_positive _ (div_pos hq hZ), cpow_positive _ (div_pos hs hY),
    cpow_positive _ (div_pos (mul_pos hX (mul_pos hu (pow_pos hr _))) hq)]
  push_cast
  rw [show (Real.sqrt X : ℂ) / Y / ((Real.sqrt c : ℂ) * n * (c * n ^ 3)) =
      comparisonRealPower X (1 / 2) * comparisonRealPower Y (-1) *
      comparisonRealPower c (-1 / 2) * comparisonRealPower n (-1) *
      comparisonRealPower (c * n ^ 3) (-1) by
    rw [power_half _ hX, power_neg_one _ hY, power_neg_half _ hc,
      power_neg_one _ hn, power_neg_one _ hq]
    push_cast
    ring]
  simp only [comparisonRealPower, ← Complex.exp_add]
  congr 1
  rw [Real.log_div (ne_of_gt hq) (ne_of_gt hZ),
    Real.log_div (ne_of_gt hs) (ne_of_gt hY),
    Real.log_div (by positivity : X * (u * r ^ 6) ≠ 0) (ne_of_gt hq),
    Real.log_mul (ne_of_gt hX) (by positivity : u * r ^ 6 ≠ 0),
    Real.log_mul (ne_of_gt hu) (by positivity : r ^ 6 ≠ 0),
    Real.log_mul (ne_of_gt hc) (by positivity : n ^ 3 ≠ 0), Real.log_pow, Real.log_pow]
  push_cast
  ring

lemma integral_three_product (g a b : ℝ → ℂ) :
    (∫ t : Fin 3 → ℝ, g (t 0) * a (t 1) * b (t 2)) =
      (∫ t, g t) * (∫ t, a t) * (∫ t, b t) := by
  have h := integral_fin_nat_prod_volume_eq_prod (n := 3)
    (![g, a, b] : Fin 3 → ℝ → ℂ)
  simpa [Fin.prod_univ_succ, mul_assoc] using h

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

lemma inversions_product (P : PrincipalData A σ η hS)
    (N : MellinNormalizationData A σ η hS P) (L S V : ℝ)
    (hL : 0 < L) (hS' : 0 < S) (hV : 0 < V) :
    (thetaReflectionGaussian L : ℂ) * (P.W1 S : ℂ) *
      ProbeSheet.envelope A P.finiteTrace P.additiveMeasure P.domain.measure P.W0 V =
      tripleMellinNormalization * ∫ t : Fin 3 → ℝ,
        (Complex.exp ((5 + (t 0 : ℂ) * Complex.I) ^ 2) *
          (L : ℂ) ^ (-5 - (t 0 : ℂ) * Complex.I)) *
        ((principalMellinWeights A σ η hS P).W1Hat (4 + (t 1 : ℂ) * Complex.I) *
          (S : ℂ) ^ (-4 - (t 1 : ℂ) * Complex.I)) *
        ((principalMellinWeights A σ η hS P).M (2 + (t 2 : ℂ) * Complex.I) *
          (V : ℂ) ^ (-2 - (t 2 : ℂ) * Complex.I)) := by
  rw [(gaussian_inversion L hL).2, (realWeight_inversion P S hS').2,
    (sheet_inversion P N V hV).2]
  rw [integral_three_product
    (fun τ : ℝ => Complex.exp ((5 + (τ : ℂ) * Complex.I) ^ 2) *
      (L : ℂ) ^ (-5 - (τ : ℂ) * Complex.I))
    (fun τ : ℝ => (principalMellinWeights A σ η hS P).W1Hat (4 + (τ : ℂ) * Complex.I) *
      (S : ℂ) ^ (-4 - (τ : ℂ) * Complex.I))
    (fun τ : ℝ => (principalMellinWeights A σ η hS P).M (2 + (τ : ℂ) * Complex.I) *
      (V : ℂ) ^ (-2 - (τ : ℂ) * Complex.I))]
  unfold tripleMellinNormalization
  ring

lemma inversions_sheared (P : PrincipalData A σ η hS)
    (N : MellinNormalizationData A σ η hS P) (L S V : ℝ)
    (hL : 0 < L) (hS' : 0 < S) (hV : 0 < V) :
    (thetaReflectionGaussian L : ℂ) * (P.W1 S : ℂ) *
      ProbeSheet.envelope A P.finiteTrace P.additiveMeasure P.domain.measure P.W0 V =
      tripleMellinNormalization * ∫ t : Fin 3 → ℝ,
        (Complex.exp (((4 + (t 0 : ℂ) * Complex.I) +
          (2 + (t 2 : ℂ) * Complex.I) - 1) ^ 2) *
          (L : ℂ) ^ (-((4 + (t 0 : ℂ) * Complex.I) +
            (2 + (t 2 : ℂ) * Complex.I) - 1))) *
        ((principalMellinWeights A σ η hS P).W1Hat (4 + (t 1 : ℂ) * Complex.I) *
          (S : ℂ) ^ (-(4 + (t 1 : ℂ) * Complex.I))) *
        ((principalMellinWeights A σ η hS P).M (2 + (t 2 : ℂ) * Complex.I) *
          (V : ℂ) ^ (-(2 + (t 2 : ℂ) * Complex.I))) := by
  rw [inversions_product P N L S V hL hS' hV]
  rw [← integral_heightShear]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [show (-5 - ((heightShear t) 0 : ℂ) * Complex.I) =
      -(5 + ((heightShear t) 0 : ℂ) * Complex.I) by ring, heightShear_line]
  simp only [heightShear, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero,
    Fin.reduceFinMk]
  congr 3 <;> simp <;> ring

lemma frequencySection_frequency (P : PrincipalData A σ η hS) (j : FrequencyIndex P) :
    frequencySection P (frequencyEquiv P j) = frequencyRow P j := by
  simp [frequencySection]

lemma term_inversion_race (P : PrincipalData A σ η hS)
    (N : MellinNormalizationData A σ η hS P)
    (X Y Z : {x : ℝ // 0 < x}) (i : MellinSeriesIndex P) :
    ProbePoissonOrbitFormula.term A σ η hS P (frequencySection P)
      X.val Y.val Z.val (orbitIndexEquiv P i) =
      tripleMellinNormalization * ∫ t : ℝ × ℝ × ℝ,
        initialTripleMellinSummand P X.val Y.val Z.val i t := by
  let c := A.exteriorNorm i.2.1.val
  let n := A.exteriorNorm i.2.2.1
  let s := A.exteriorNorm i.2.2.2.1
  let r := A.exteriorNorm i.2.2.2.2
  let u := (FiniteTransform.exteriorNorm A.R.toSubring i.1.val.val : ℝ)
  have hc : 0 < c := A.exteriorNorm_pos _
  have hn : 0 < n := A.exteriorNorm_pos _
  have hs : 0 < s := A.exteriorNorm_pos _
  have hr : 0 < r := A.exteriorNorm_pos _
  have hu : 0 < u := by
    have hq := ProbeOrbitNormSum.orbitNorm_pos A (frequencyOrbit P (i.1, i.2.2.2.2))
    rw [frequencyOrbit_norm] at hq
    exact (mul_pos_iff.mp hq).elim (fun h => h.1) (fun h => False.elim (not_lt_of_ge (pow_nonneg hr.le _) h.2))
  let C : ℂ := P.coefficients.gammaTwo i.2.1 *
    P.coefficients.theta (ThetaReflectionData.forwardModulus A P.coefficients i.2.1 i.2.2.1) *
    comparisonPoissonFiniteCoefficient F A P.coefficients i.2.1 i.2.2.1 i.2.2.2.1
      (i.1.val.val * P.coefficients.generator i.2.2.2.2 ^ 6)
  let B : ℂ := ((Real.sqrt X.val / Y.val : ℝ) : ℂ) / ((Real.sqrt c : ℂ) * n * (c * n ^ 3))
  have hq : 0 < c * n ^ 3 := by positivity
  have he := inversions_sheared P N (c * n ^ 3 / Z.val) (s / Y.val)
    (X.val * (u * r ^ 6) / (c * n ^ 3))
    (div_pos hq Z.property) (div_pos hs Y.property)
    (div_pos (mul_pos X.property (mul_pos hu (pow_pos hr _))) hq)
  have ht : ProbePoissonOrbitFormula.term A σ η hS P (frequencySection P)
      X.val Y.val Z.val (orbitIndexEquiv P i) =
      (C * B) * ((thetaReflectionGaussian (c * n ^ 3 / Z.val) : ℂ) *
        (P.W1 (s / Y.val) : ℂ) * ProbeSheet.envelope A P.finiteTrace P.additiveMeasure
          P.domain.measure P.W0 (X.val * (u * r ^ 6) / (c * n ^ 3))) := by
    unfold ProbePoissonOrbitFormula.term ProbePoissonOrbitFormula.orbitRow
    simp only [orbitIndexEquiv, Equiv.coe_fn_mk, frequencySection_frequency]
    rw [show ProbeOrbitNormSum.orbitMk A (frequencyRow P (i.1, i.2.2.2.2)) =
        frequencyOrbit P (i.1, i.2.2.2.2) by rfl, frequencyOrbit_norm]
    unfold ProbePoissonOrbitFormula.arithmeticFactor ProbePoissonOrbitFormula.qA
    dsimp [C, B, c, n, s, r, u, frequencyRow]
    push_cast
    ring
  rw [ht, he]
  rw [mul_left_comm (C * B), ← integral_const_mul]
  congr 1
  rw [← heightEquiv_preserving.integral_comp'
    (initialTripleMellinSummand P X.val Y.val Z.val i)]
  apply integral_congr_ae
  filter_upwards [] with t
  have hb := power_balance X.val Y.val Z.val c n s r u X.property Y.property Z.property
    hc hn hs hr hu (4 + (t 0 : ℂ) * Complex.I)
    (4 + (t 1 : ℂ) * Complex.I) (2 + (t 2 : ℂ) * Complex.I)
  unfold initialTripleMellinSummand tripleMellinWeight weightedSeparatedSummand
    comparisonEulerPoissonSummand
  simp only [initialMellinPoint, heightEquiv_apply]
  change (C * B) * _ = _
  dsimp [C]
  dsimp [c, n, s, r, u] at hb
  have hh := congrArg (fun v : ℂ => v *
    (P.coefficients.gammaTwo i.2.1 * P.coefficients.theta
      (ThetaReflectionData.forwardModulus A P.coefficients i.2.1 i.2.2.1) *
      comparisonPoissonFiniteCoefficient F A P.coefficients i.2.1 i.2.2.1 i.2.2.2.1
        (i.1.val.val * P.coefficients.generator i.2.2.2.2 ^ 6)) *
    Complex.exp (((4 + (t 0 : ℂ) * Complex.I) + (2 + (t 2 : ℂ) * Complex.I) - 1) ^ 2) *
    (principalMellinWeights A σ η hS P).W1Hat (4 + (t 1 : ℂ) * Complex.I) *
    (principalMellinWeights A σ η hS P).M (2 + (t 2 : ℂ) * Complex.I)) hb
  convert hh using 1 <;> dsimp [B, c, n, s, r, u, principalMellinWeights,
    comparisonMellinWeightsFromProbe, ThetaReflectionData.forwardModulus] <;> ring

end
end DedekindZetaZeroFree.NormalizedProbe.TripleMellin.TermRace
