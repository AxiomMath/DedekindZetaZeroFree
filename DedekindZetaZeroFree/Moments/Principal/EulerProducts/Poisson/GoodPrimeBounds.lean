module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.Domain

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.EulerGoodPrime

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.EulerDomain

section Helpers

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

lemma Q_ge_two (p : LocalFiniteSums.ExteriorPrime A) : 2 ≤ LocalFiniteSums.Q p := by
  change 2 ≤ (Ideal.absNorm p.val.asIdeal : ℝ)
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p.val

lemma Q_pos (p : LocalFiniteSums.ExteriorPrime A) : 0 < LocalFiniteSums.Q p :=
  lt_of_lt_of_le (by norm_num) (Q_ge_two p)

lemma norm_qPower_rpow (p : LocalFiniteSums.ExteriorPrime A) (s : ℂ) :
    ‖LocalFiniteSums.qPower p s‖ = LocalFiniteSums.Q p ^ s.re := by
  rw [Real.rpow_def_of_pos (Q_pos p)]
  simp [LocalFiniteSums.qPower, Complex.norm_exp, mul_comm]

lemma norm_V_eq (p : LocalFiniteSums.ExteriorPrime A) (z : ℂ) :
    ‖CorrectionFactors.V p z‖ = LocalFiniteSums.Q p ^ (-(6 * z.re)) := by
  unfold CorrectionFactors.V
  rw [norm_qPower_rpow]
  congr 1
  simp <;> ring

lemma chi_norm_le (p : LocalFiniteSums.ExteriorPrime A) (u : A.R) :
    ‖LocalFiniteSums.chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (LocalFiniteSums.primeIdeal p)) u)‖ ≤ 1 := by
  letI := A.exteriorResidue_finite (LocalFiniteSums.primeIdeal p)
  letI := Fintype.ofFinite (A.R ⧸ A.extendIdeal (LocalFiniteSums.primeIdeal p))ˣ
  by_cases hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (LocalFiniteSums.primeIdeal p)) u)
  · obtain ⟨v, hv⟩ := hu
    rw [← hv]
    have h := Complex.norm_eq_one_of_mem_rootsOfUnity
      ((LocalFiniteSums.chi (σ := σ) p).apply_mem_rootsOfUnity v)
    simpa only [MulChar.coe_equivToUnitHom] using h.le
  · simp [MulChar.map_nonunit _ hu]

lemma norm_W_le (p : LocalFiniteSums.ExteriorPrime A) (u : A.R) (w : ℂ) :
    ‖CorrectionFactors.W (σ := σ) p u w‖ ≤ LocalFiniteSums.Q p ^ (-w.re) := by
  unfold CorrectionFactors.W
  rw [norm_mul, norm_qPower_rpow]
  simp only [Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Q_pos p).le _) (chi_norm_le p u)

lemma eta_norm_le (p : LocalFiniteSums.ExteriorPrime A) : ‖η p.val.asIdeal‖ ≤ 1 := by
  by_cases h : η p.val.asIdeal = 0
  · simp [h]
  · exact (RayClassBridge.rayClassCharacter_norm_of_ne_zero F
      (primitive12_totallyComplex F A.zeta12 A.primitive_zeta12)
      A.modulus A.modulus_ne_zero η p.val.asIdeal h).le

lemma norm_D_le (p : LocalFiniteSums.ExteriorPrime A) (u : A.R) (ξ : ℂ) :
    ‖CorrectionFactors.D (σ := σ) (η := η) p u ξ‖ ≤ LocalFiniteSums.Q p ^ (-ξ.re) := by
  unfold CorrectionFactors.D
  rw [norm_mul, norm_mul, norm_star, norm_qPower_rpow]
  simp only [Complex.neg_re]
  have h := mul_le_one₀ (eta_norm_le (η := η) p) (norm_nonneg _) (chi_norm_le (σ := σ) p u)
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Q_pos p).le _) h

lemma norm_E_eq (C : A.GeneralArithmeticContext σ η hS) (p : LocalFiniteSums.ExteriorPrime A)
    (ξ z : ℂ) :
    ‖CorrectionFactors.E C p ξ z‖ = LocalFiniteSums.Q p ^ (4 - 6 * ξ.re - 6 * z.re) := by
  have hθ : ‖LocalFiniteSums.vartheta C p‖ = 1 := Circle.norm_coe _
  unfold CorrectionFactors.E
  rw [norm_mul, norm_mul, norm_pow, hθ, one_pow, one_mul, norm_qPower_rpow, norm_V_eq,
    ← Real.rpow_add (Q_pos p)]
  congr 1
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero]
  ring

lemma ne_zero_of_norm_lt_one (a : ℂ) (h : ‖a‖ < 1) : 1 - a ≠ 0 := by
  intro heq
  have : a = 1 := (sub_eq_zero.mp heq).symm
  simp [this] at h

lemma rpow_le_two_inv (δ' : ℝ) (hδ : 0 < δ') (Q : ℝ) (hQ : 2 ≤ Q) (a : ℝ) (ha : a ≤ -δ') :
    Q ^ a ≤ ((2 : ℝ) ^ δ')⁻¹ := by
  calc Q ^ a ≤ Q ^ (-δ') := Real.rpow_le_rpow_of_exponent_le (by linarith) ha
    _ = (Q ^ δ')⁻¹ := Real.rpow_neg (by linarith) δ'
    _ ≤ ((2 : ℝ) ^ δ')⁻¹ := inv_anti₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hQ hδ.le)

lemma inv_two_rpow_lt_one (δ' : ℝ) (hδ : 0 < δ') : ((2 : ℝ) ^ δ')⁻¹ < 1 := by
  rw [inv_lt_one₀ (by positivity)]
  exact Real.one_lt_rpow (by norm_num) hδ

lemma good_algebra (v w d e q : ℂ) (hv : 1 - v ≠ 0) (hw : 1 - w ≠ 0) (hd : 1 - d ≠ 0)
    (he : 1 - e ≠ 0) :
    (1 - v) * (1 - w) * (1 / (1 - v) + w / (1 - w) + e / (1 - e) * ((1 - q⁻¹) / (1 - v) + w)
      - d / (1 - e) * (1 + (q - 1) * w * v / (1 - v))) / (1 - d) - 1 =
    (-v * w + d * v + d * w - q * d * w * v + (q - 1) * d * w ^ 2 * v +
      e * ((1 - q⁻¹) + q⁻¹ * w - w ^ 2 + w ^ 2 * v - d)) / ((1 - e) * (1 - d)) := by
  field_simp
  ring

lemma numerator_norm_le (q : ℝ) (hq : 2 ≤ q) (v w d e : ℂ) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hd : ‖d‖ ≤ 1) :
    ‖-v * w + d * v + d * w - (q : ℂ) * d * w * v +
      ((q : ℂ) - 1) * d * w ^ 2 * v +
      e * ((1 - (q : ℂ)⁻¹) + (q : ℂ)⁻¹ * w - w ^ 2 + w ^ 2 * v - d)‖ ≤
      ‖v‖ * ‖w‖ + ‖d‖ * ‖v‖ + ‖d‖ * ‖w‖ + 3 * (q * (‖d‖ * ‖w‖ * ‖v‖)) + 6 * ‖e‖ := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hqn : ‖(q : ℂ)‖ = q := by simp [Complex.norm_real, abs_of_nonneg hq0]
  have hqi : ‖(q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, hqn]; exact inv_le_one_of_one_le₀ (by linarith)
  have hqm : ‖(q : ℂ) - 1‖ ≤ 2 * q := by
    have h := norm_sub_le (q : ℂ) 1
    rw [hqn, norm_one] at h; linarith
  have hw2 : ‖w ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg w) hw
  have hw2v : ‖w ^ 2 * v‖ ≤ 1 := by
    rw [norm_mul]; exact mul_le_one₀ hw2 (norm_nonneg _) hv
  have hB : ‖(1 - (q : ℂ)⁻¹) + (q : ℂ)⁻¹ * w - w ^ 2 + w ^ 2 * v - d‖ ≤ 6 := by
    have b1 := norm_sub_le (1 - (q : ℂ)⁻¹ + (q : ℂ)⁻¹ * w - w ^ 2 + w ^ 2 * v) d
    have b2 := norm_add_le (1 - (q : ℂ)⁻¹ + (q : ℂ)⁻¹ * w - w ^ 2) (w ^ 2 * v)
    have b3 := norm_sub_le (1 - (q : ℂ)⁻¹ + (q : ℂ)⁻¹ * w) (w ^ 2)
    have b4 := norm_add_le (1 - (q : ℂ)⁻¹) ((q : ℂ)⁻¹ * w)
    have b5 := norm_sub_le (1 : ℂ) ((q : ℂ)⁻¹)
    have b6 : ‖(q : ℂ)⁻¹ * w‖ ≤ 1 := by
      rw [norm_mul]; exact mul_le_one₀ hqi (norm_nonneg _) hw
    rw [norm_one] at b5
    linarith
  have hX : 0 ≤ ‖d‖ * ‖w‖ * ‖v‖ := by positivity
  have hP : ‖((q : ℂ) - 1) * d * w ^ 2 * v‖ ≤ 2 * (q * (‖d‖ * ‖w‖ * ‖v‖)) := by
    have h1 : ‖w ^ 2‖ ≤ ‖w‖ := by
      rw [norm_pow]; nlinarith [norm_nonneg w]
    rw [norm_mul, norm_mul, norm_mul]
    have hq1 : ‖(q : ℂ) - 1‖ ≤ 2 * q := hqm
    calc ‖(q : ℂ) - 1‖ * ‖d‖ * ‖w ^ 2‖ * ‖v‖ ≤ (2 * q) * ‖d‖ * ‖w‖ * ‖v‖ := by
          gcongr
      _ = 2 * (q * (‖d‖ * ‖w‖ * ‖v‖)) := by ring
  have hE : ‖e * ((1 - (q : ℂ)⁻¹) + (q : ℂ)⁻¹ * w - w ^ 2 + w ^ 2 * v - d)‖ ≤ 6 * ‖e‖ := by
    rw [norm_mul]
    calc ‖e‖ * ‖(1 - (q : ℂ)⁻¹) + (q : ℂ)⁻¹ * w - w ^ 2 + w ^ 2 * v - d‖ ≤ ‖e‖ * 6 :=
          mul_le_mul_of_nonneg_left hB (norm_nonneg e)
      _ = 6 * ‖e‖ := by ring
  have hmain := norm_add_le
    (-v * w + d * v + d * w - (q : ℂ) * d * w * v + ((q : ℂ) - 1) * d * w ^ 2 * v)
    (e * ((1 - (q : ℂ)⁻¹) + (q : ℂ)⁻¹ * w - w ^ 2 + w ^ 2 * v - d))
  have a1 := norm_add_le (-v * w + d * v + d * w - (q : ℂ) * d * w * v) (((q : ℂ) - 1) * d * w ^ 2 * v)
  have a2 := norm_sub_le (-v * w + d * v + d * w) ((q : ℂ) * d * w * v)
  have a3 := norm_add_le (-v * w + d * v) (d * w)
  have a4 := norm_add_le (-v * w) (d * v)
  have a5 : ‖-v * w‖ = ‖v‖ * ‖w‖ := by simp [norm_mul]
  have a6 : ‖(q : ℂ) * d * w * v‖ = q * (‖d‖ * ‖w‖ * ‖v‖) := by
    simp only [norm_mul, hqn]; ring
  have a7 : ‖d * v‖ = ‖d‖ * ‖v‖ := norm_mul _ _
  have a8 : ‖d * w‖ = ‖d‖ * ‖w‖ := norm_mul _ _
  linarith

lemma goodFactor_sub_one_eq (C : A.GeneralArithmeticContext σ η hS)
    (pr : LocalFiniteSums.ExteriorPrime A) (uu : A.R) (ξ w z : ℂ)
    (hnv : 1 - CorrectionFactors.V pr z ≠ 0)
    (hnw : 1 - CorrectionFactors.W (σ := σ) pr uu w ≠ 0)
    (hnd : 1 - CorrectionFactors.D (σ := σ) (η := η) pr uu ξ ≠ 0)
    (hne : 1 - CorrectionFactors.E C pr ξ z ≠ 0) :
    CorrectionFactors.goodFactor C pr uu ξ w z - 1 =
      (-CorrectionFactors.V pr z * CorrectionFactors.W (σ := σ) pr uu w +
        CorrectionFactors.D (σ := σ) (η := η) pr uu ξ * CorrectionFactors.V pr z +
        CorrectionFactors.D (σ := σ) (η := η) pr uu ξ * CorrectionFactors.W (σ := σ) pr uu w -
        ((LocalFiniteSums.Q pr : ℝ) : ℂ) * CorrectionFactors.D (σ := σ) (η := η) pr uu ξ *
          CorrectionFactors.W (σ := σ) pr uu w * CorrectionFactors.V pr z +
        (((LocalFiniteSums.Q pr : ℝ) : ℂ) - 1) * CorrectionFactors.D (σ := σ) (η := η) pr uu ξ *
          CorrectionFactors.W (σ := σ) pr uu w ^ 2 * CorrectionFactors.V pr z +
        CorrectionFactors.E C pr ξ z * ((1 - ((LocalFiniteSums.Q pr : ℝ) : ℂ)⁻¹) +
          ((LocalFiniteSums.Q pr : ℝ) : ℂ)⁻¹ * CorrectionFactors.W (σ := σ) pr uu w -
          CorrectionFactors.W (σ := σ) pr uu w ^ 2 +
          CorrectionFactors.W (σ := σ) pr uu w ^ 2 * CorrectionFactors.V pr z -
          CorrectionFactors.D (σ := σ) (η := η) pr uu ξ)) /
        ((1 - CorrectionFactors.E C pr ξ z) * (1 - CorrectionFactors.D (σ := σ) (η := η) pr uu ξ)) := by
  unfold CorrectionFactors.goodFactor CorrectionFactors.goodRational
  exact good_algebra _ _ _ _ _ hnv hnw hnd hne

lemma good_bound (C : A.GeneralArithmeticContext σ η hS) (pr : LocalFiniteSums.ExteriorPrime A)
    (uu : A.R) (ξ w z : ℂ) (ρ : ℝ) (hρ : ρ < 1)
    (hv : LocalFiniteSums.Q pr ^ (-(6 * z.re)) ≤ ρ)
    (hw : LocalFiniteSums.Q pr ^ (-w.re) ≤ ρ)
    (hd : LocalFiniteSums.Q pr ^ (-ξ.re) ≤ ρ)
    (he : LocalFiniteSums.Q pr ^ (4 - 6 * ξ.re - 6 * z.re) ≤ ρ) :
    ‖CorrectionFactors.goodFactor C pr uu ξ w z - 1‖ ≤
      6 / ((1 - ρ) * (1 - ρ)) *
        (LocalFiniteSums.Q pr ^ (-(6 * z.re)) * LocalFiniteSums.Q pr ^ (-w.re) +
          LocalFiniteSums.Q pr ^ (-ξ.re) * LocalFiniteSums.Q pr ^ (-(6 * z.re)) +
          LocalFiniteSums.Q pr ^ (-ξ.re) * LocalFiniteSums.Q pr ^ (-w.re) +
          LocalFiniteSums.Q pr * (LocalFiniteSums.Q pr ^ (-ξ.re) * LocalFiniteSums.Q pr ^ (-w.re) *
            LocalFiniteSums.Q pr ^ (-(6 * z.re))) +
          LocalFiniteSums.Q pr ^ (4 - 6 * ξ.re - 6 * z.re)) := by
  have hQ2 := Q_ge_two pr
  have hQ0 := Q_pos pr
  have hq0 : (0 : ℝ) ≤ LocalFiniteSums.Q pr := hQ0.le
  have hpow : ∀ a : ℝ, 0 ≤ LocalFiniteSums.Q pr ^ a := fun a => Real.rpow_nonneg hq0 a
  have hvn := norm_V_eq pr z
  have hwn := norm_W_le (σ := σ) (A := A) pr uu w
  have hdn := norm_D_le (σ := σ) (η := η) pr uu ξ
  have hen := norm_E_eq C pr ξ z
  have hvn1 : ‖CorrectionFactors.V pr z‖ ≤ ρ := hvn.le.trans hv
  have hwn1 : ‖CorrectionFactors.W (σ := σ) pr uu w‖ ≤ ρ := hwn.trans hw
  have hdn1 : ‖CorrectionFactors.D (σ := σ) (η := η) pr uu ξ‖ ≤ ρ := hdn.trans hd
  have hen1 : ‖CorrectionFactors.E C pr ξ z‖ ≤ ρ := hen.le.trans he
  have hρ0 : 0 < 1 - ρ := by linarith
  have hnv : 1 - CorrectionFactors.V pr z ≠ 0 :=
    ne_zero_of_norm_lt_one _ (lt_of_le_of_lt hvn1 hρ)
  have hnw : 1 - CorrectionFactors.W (σ := σ) pr uu w ≠ 0 :=
    ne_zero_of_norm_lt_one _ (lt_of_le_of_lt hwn1 hρ)
  have hnd : 1 - CorrectionFactors.D (σ := σ) (η := η) pr uu ξ ≠ 0 :=
    ne_zero_of_norm_lt_one _ (lt_of_le_of_lt hdn1 hρ)
  have hne : 1 - CorrectionFactors.E C pr ξ z ≠ 0 :=
    ne_zero_of_norm_lt_one _ (lt_of_le_of_lt hen1 hρ)
  rw [goodFactor_sub_one_eq C pr uu ξ w z hnv hnw hnd hne, norm_div, norm_mul]
  have hN := numerator_norm_le (LocalFiniteSums.Q pr) hQ2 (CorrectionFactors.V pr z)
    (CorrectionFactors.W (σ := σ) pr uu w) (CorrectionFactors.D (σ := σ) (η := η) pr uu ξ)
    (CorrectionFactors.E C pr ξ z) (by linarith) (by linarith) (by linarith)
  have t1 : ‖CorrectionFactors.V pr z‖ * ‖CorrectionFactors.W (σ := σ) pr uu w‖ ≤
      LocalFiniteSums.Q pr ^ (-(6 * z.re)) * LocalFiniteSums.Q pr ^ (-w.re) := by
    rw [hvn]; exact mul_le_mul_of_nonneg_left hwn (hpow _)
  have t2 : ‖CorrectionFactors.D (σ := σ) (η := η) pr uu ξ‖ * ‖CorrectionFactors.V pr z‖ ≤
      LocalFiniteSums.Q pr ^ (-ξ.re) * LocalFiniteSums.Q pr ^ (-(6 * z.re)) := by
    rw [hvn]; exact mul_le_mul_of_nonneg_right hdn (hpow _)
  have t3 : ‖CorrectionFactors.D (σ := σ) (η := η) pr uu ξ‖ *
      ‖CorrectionFactors.W (σ := σ) pr uu w‖ ≤
      LocalFiniteSums.Q pr ^ (-ξ.re) * LocalFiniteSums.Q pr ^ (-w.re) :=
    mul_le_mul hdn hwn (norm_nonneg _) (hpow _)
  have t4 : LocalFiniteSums.Q pr * (‖CorrectionFactors.D (σ := σ) (η := η) pr uu ξ‖ *
      ‖CorrectionFactors.W (σ := σ) pr uu w‖ * ‖CorrectionFactors.V pr z‖) ≤
      LocalFiniteSums.Q pr * (LocalFiniteSums.Q pr ^ (-ξ.re) * LocalFiniteSums.Q pr ^ (-w.re) *
        LocalFiniteSums.Q pr ^ (-(6 * z.re))) := by
    apply mul_le_mul_of_nonneg_left _ hq0
    rw [hvn]
    exact mul_le_mul t3 (le_refl _) (hpow _) (mul_nonneg (hpow _) (hpow _))
  have t5 : ‖CorrectionFactors.E C pr ξ z‖ ≤ LocalFiniteSums.Q pr ^ (4 - 6 * ξ.re - 6 * z.re) :=
    hen.le
  have n1 := mul_nonneg (hpow (-(6 * z.re))) (hpow (-w.re))
  have n2 := mul_nonneg (hpow (-ξ.re)) (hpow (-(6 * z.re)))
  have n3 := mul_nonneg (hpow (-ξ.re)) (hpow (-w.re))
  have n4 := mul_nonneg hq0 (mul_nonneg (mul_nonneg (hpow (-ξ.re)) (hpow (-w.re)))
    (hpow (-(6 * z.re))))
  have n5 := hpow (4 - 6 * ξ.re - 6 * z.re)
  have hNS : ‖-CorrectionFactors.V pr z * CorrectionFactors.W (σ := σ) pr uu w +
        CorrectionFactors.D (σ := σ) (η := η) pr uu ξ * CorrectionFactors.V pr z +
        CorrectionFactors.D (σ := σ) (η := η) pr uu ξ * CorrectionFactors.W (σ := σ) pr uu w -
        ((LocalFiniteSums.Q pr : ℝ) : ℂ) * CorrectionFactors.D (σ := σ) (η := η) pr uu ξ *
          CorrectionFactors.W (σ := σ) pr uu w * CorrectionFactors.V pr z +
        (((LocalFiniteSums.Q pr : ℝ) : ℂ) - 1) * CorrectionFactors.D (σ := σ) (η := η) pr uu ξ *
          CorrectionFactors.W (σ := σ) pr uu w ^ 2 * CorrectionFactors.V pr z +
        CorrectionFactors.E C pr ξ z * ((1 - ((LocalFiniteSums.Q pr : ℝ) : ℂ)⁻¹) +
          ((LocalFiniteSums.Q pr : ℝ) : ℂ)⁻¹ * CorrectionFactors.W (σ := σ) pr uu w -
          CorrectionFactors.W (σ := σ) pr uu w ^ 2 +
          CorrectionFactors.W (σ := σ) pr uu w ^ 2 * CorrectionFactors.V pr z -
          CorrectionFactors.D (σ := σ) (η := η) pr uu ξ)‖ ≤
      6 * (LocalFiniteSums.Q pr ^ (-(6 * z.re)) * LocalFiniteSums.Q pr ^ (-w.re) +
          LocalFiniteSums.Q pr ^ (-ξ.re) * LocalFiniteSums.Q pr ^ (-(6 * z.re)) +
          LocalFiniteSums.Q pr ^ (-ξ.re) * LocalFiniteSums.Q pr ^ (-w.re) +
          LocalFiniteSums.Q pr * (LocalFiniteSums.Q pr ^ (-ξ.re) * LocalFiniteSums.Q pr ^ (-w.re) *
            LocalFiniteSums.Q pr ^ (-(6 * z.re))) +
          LocalFiniteSums.Q pr ^ (4 - 6 * ξ.re - 6 * z.re)) := by
    linarith
  have hA : 1 - ρ ≤ ‖1 - CorrectionFactors.E C pr ξ z‖ := by
    have := norm_sub_norm_le (1 : ℂ) (CorrectionFactors.E C pr ξ z)
    rw [norm_one] at this; linarith
  have hB : 1 - ρ ≤ ‖1 - CorrectionFactors.D (σ := σ) (η := η) pr uu ξ‖ := by
    have := norm_sub_norm_le (1 : ℂ) (CorrectionFactors.D (σ := σ) (η := η) pr uu ξ)
    rw [norm_one] at this; linarith
  have hS0 : 0 ≤ LocalFiniteSums.Q pr ^ (-(6 * z.re)) * LocalFiniteSums.Q pr ^ (-w.re) +
          LocalFiniteSums.Q pr ^ (-ξ.re) * LocalFiniteSums.Q pr ^ (-(6 * z.re)) +
          LocalFiniteSums.Q pr ^ (-ξ.re) * LocalFiniteSums.Q pr ^ (-w.re) +
          LocalFiniteSums.Q pr * (LocalFiniteSums.Q pr ^ (-ξ.re) * LocalFiniteSums.Q pr ^ (-w.re) *
            LocalFiniteSums.Q pr ^ (-(6 * z.re))) +
          LocalFiniteSums.Q pr ^ (4 - 6 * ξ.re - 6 * z.re) := by linarith
  calc _ ≤ (6 * (LocalFiniteSums.Q pr ^ (-(6 * z.re)) * LocalFiniteSums.Q pr ^ (-w.re) +
          LocalFiniteSums.Q pr ^ (-ξ.re) * LocalFiniteSums.Q pr ^ (-(6 * z.re)) +
          LocalFiniteSums.Q pr ^ (-ξ.re) * LocalFiniteSums.Q pr ^ (-w.re) +
          LocalFiniteSums.Q pr * (LocalFiniteSums.Q pr ^ (-ξ.re) * LocalFiniteSums.Q pr ^ (-w.re) *
            LocalFiniteSums.Q pr ^ (-(6 * z.re))) +
          LocalFiniteSums.Q pr ^ (4 - 6 * ξ.re - 6 * z.re))) /
          ((1 - ρ) * (1 - ρ)) := by
        refine div_le_div₀ (by linarith) ?_ (mul_pos hρ0 hρ0) ?_
        · linarith
        · exact mul_le_mul hA hB hρ0.le (norm_nonneg _)
    _ = _ := by ring

end Helpers

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem localFactor_sub_one_le_five_terms (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : D.Row) (pr : LocalFiniteSums.ExteriorPrime D.recipe.A),
      (↑(u.toFrequency.j pr) : ℕ) = (0 : ℕ) → ∀ p ∈ OmegaStarMargin δ',
        ‖CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2 - 1‖ ≤
          C * (LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re)) * LocalFiniteSums.Q pr ^ (-p.2.1.re) +
            LocalFiniteSums.Q pr ^ (-p.1.re) * LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re)) +
            LocalFiniteSums.Q pr ^ (-p.1.re) * LocalFiniteSums.Q pr ^ (-p.2.1.re) +
            LocalFiniteSums.Q pr * (LocalFiniteSums.Q pr ^ (-p.1.re) *
              LocalFiniteSums.Q pr ^ (-p.2.1.re) * LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re))) +
            LocalFiniteSums.Q pr ^ (4 - 6 * p.1.re - 6 * p.2.2.re)) := by
  have hρ : ((2 : ℝ) ^ δ')⁻¹ < 1 := inv_two_rpow_lt_one δ' hδ'
  have hρ0 : 0 < 1 - ((2 : ℝ) ^ δ')⁻¹ := by linarith
  refine ⟨6 / ((1 - ((2 : ℝ) ^ δ')⁻¹) * (1 - ((2 : ℝ) ^ δ')⁻¹)),
    div_pos (by norm_num) (mul_pos hρ0 hρ0), ?_⟩
  intro u pr hj p hp
  simp only [OmegaStarMargin, Set.mem_setOf_eq] at hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hp
  have hQ2 := Q_ge_two pr
  unfold CorrectionFactors.localFactor
  rw [if_pos hj]
  exact good_bound D.context pr _ p.1 p.2.1 p.2.2 _ hρ
      (rpow_le_two_inv δ' hδ' _ hQ2 _ (by linarith))
      (rpow_le_two_inv δ' hδ' _ hQ2 _ (by linarith))
      (rpow_le_two_inv δ' hδ' _ hQ2 _ (by linarith))
      (rpow_le_two_inv δ' hδ' _ hQ2 _ (by linarith))

theorem localFactor_sub_one_le (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (u : D.Row) (pr : LocalFiniteSums.ExteriorPrime D.recipe.A),
        (↑(u.toFrequency.j pr) : ℕ) = (0 : ℕ) → ∀ p ∈ OmegaStarMargin δ',
          ‖CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2 - 1‖ ≤
            C * LocalFiniteSums.Q pr ^ (-1 - δ) := by
  obtain ⟨C0, hC0, hspec⟩ := localFactor_sub_one_le_five_terms D δ' hδ'
  refine ⟨5 * C0, δ', by linarith, hδ', ?_⟩
  intro u pr hj p hp
  have hQ2 := Q_ge_two pr
  have hQ0 := Q_pos pr
  have hQ1 : (1 : ℝ) ≤ LocalFiniteSums.Q pr := by linarith
  have hm : ∀ a : ℝ, a ≤ -1 - δ' →
      LocalFiniteSums.Q pr ^ a ≤ LocalFiniteSums.Q pr ^ (-1 - δ') :=
    fun a ha => Real.rpow_le_rpow_of_exponent_le hQ1 ha
  simp only [OmegaStarMargin, Set.mem_setOf_eq] at hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hp
  have T1 : LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re)) * LocalFiniteSums.Q pr ^ (-p.2.1.re) ≤
      LocalFiniteSums.Q pr ^ (-1 - δ') := by
    rw [← Real.rpow_add hQ0]; exact hm _ (by linarith)
  have T2 : LocalFiniteSums.Q pr ^ (-p.1.re) * LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re)) ≤
      LocalFiniteSums.Q pr ^ (-1 - δ') := by
    rw [← Real.rpow_add hQ0]; exact hm _ (by linarith)
  have T3 : LocalFiniteSums.Q pr ^ (-p.1.re) * LocalFiniteSums.Q pr ^ (-p.2.1.re) ≤
      LocalFiniteSums.Q pr ^ (-1 - δ') := by
    rw [← Real.rpow_add hQ0]; exact hm _ (by linarith)
  have e4 : LocalFiniteSums.Q pr * (LocalFiniteSums.Q pr ^ (-p.1.re) *
      LocalFiniteSums.Q pr ^ (-p.2.1.re) * LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re))) =
      LocalFiniteSums.Q pr ^ (1 + (-p.1.re + -p.2.1.re + -(6 * p.2.2.re))) := by
    rw [Real.rpow_add hQ0, Real.rpow_add hQ0, Real.rpow_add hQ0, Real.rpow_one]
  have T4 : LocalFiniteSums.Q pr * (LocalFiniteSums.Q pr ^ (-p.1.re) *
      LocalFiniteSums.Q pr ^ (-p.2.1.re) * LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re))) ≤
      LocalFiniteSums.Q pr ^ (-1 - δ') := by
    rw [e4]; exact hm _ (by linarith)
  have T5 : LocalFiniteSums.Q pr ^ (4 - 6 * p.1.re - 6 * p.2.2.re) ≤
      LocalFiniteSums.Q pr ^ (-1 - δ') := hm _ (by linarith)
  have hS : LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re)) * LocalFiniteSums.Q pr ^ (-p.2.1.re) +
      LocalFiniteSums.Q pr ^ (-p.1.re) * LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re)) +
      LocalFiniteSums.Q pr ^ (-p.1.re) * LocalFiniteSums.Q pr ^ (-p.2.1.re) +
      LocalFiniteSums.Q pr * (LocalFiniteSums.Q pr ^ (-p.1.re) *
        LocalFiniteSums.Q pr ^ (-p.2.1.re) * LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re))) +
      LocalFiniteSums.Q pr ^ (4 - 6 * p.1.re - 6 * p.2.2.re) ≤
      5 * LocalFiniteSums.Q pr ^ (-1 - δ') := by linarith
  have hmem : p ∈ OmegaStarMargin δ' := by
    simp only [OmegaStarMargin, Set.mem_setOf_eq]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  calc _ ≤ C0 * (LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re)) * LocalFiniteSums.Q pr ^ (-p.2.1.re) +
            LocalFiniteSums.Q pr ^ (-p.1.re) * LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re)) +
            LocalFiniteSums.Q pr ^ (-p.1.re) * LocalFiniteSums.Q pr ^ (-p.2.1.re) +
            LocalFiniteSums.Q pr * (LocalFiniteSums.Q pr ^ (-p.1.re) *
              LocalFiniteSums.Q pr ^ (-p.2.1.re) * LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re))) +
            LocalFiniteSums.Q pr ^ (4 - 6 * p.1.re - 6 * p.2.2.re)) :=
        hspec u pr hj p hmem
    _ ≤ C0 * (5 * LocalFiniteSums.Q pr ^ (-1 - δ')) := mul_le_mul_of_nonneg_left hS hC0.le
    _ = 5 * C0 * LocalFiniteSums.Q pr ^ (-1 - δ') := by ring

end

end DedekindZetaZeroFree.Quantitative.EulerGoodPrime
