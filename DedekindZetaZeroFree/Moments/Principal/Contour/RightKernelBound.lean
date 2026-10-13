module

public import DedekindZetaZeroFree.Moments.Principal.Contour.StripDefinitions
public import DedekindZetaZeroFree.Moments.Principal.Contour.KernelMajorants

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalRightKernelBound31

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel
  DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions DedekindZetaZeroFree.Quantitative.PrincipalStripBasicDefinitions
  DedekindZetaZeroFree.Quantitative.EulerDomain
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private lemma re_line (v s : ℝ) : ((v : ℂ) + (s : ℂ) * Complex.I).re = v := by simp

private lemma kern_norm (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 0 < Z) (ξ w z : ℂ) :
    ‖kern D u Z ξ w z‖ =
      Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * z.re + Scales.yExponent * (w.re - 1)) *
        ‖Complex.exp ((ξ + z - 1) ^ 2) * D.M z * D.W1Hat w‖ *
        (‖D.zetaSCont (6 * z)‖ * ‖D.Lpsi u w‖ * ‖EulerDomain.Hu D u ξ w z‖ *
          ‖D.Llam u ξ‖⁻¹) := by
  have hqc : ((D.q u : ℝ) : ℂ) = 1 := by
    rw [PrincipalResidueFormulas.q_principal D u hu]; simp
  have hZn : ∀ c : ℂ, ‖(Z : ℂ) ^ c‖ = Z ^ c.re :=
    fun c => Complex.norm_cpow_eq_rpow_re_of_pos hZ c
  have hre : ((((Scales.xExponent / 2 : ℝ) : ℂ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z +
      (Scales.yExponent : ℂ) * (w - 1)).re) =
      Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * z.re + Scales.yExponent * (w.re - 1) := by
    simp [Complex.mul_re]
  have e : kern D u Z ξ w z =
      (Z : ℂ) ^ ((((Scales.xExponent / 2 : ℝ) : ℂ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z +
        (Scales.yExponent : ℂ) * (w - 1))) *
        (Complex.exp ((ξ + z - 1) ^ 2) * D.M z * D.W1Hat w) *
        (D.zetaSCont (6 * z) * D.Lpsi u w * EulerDomain.Hu D u ξ w z * (D.Llam u ξ)⁻¹) := by
    unfold kern kernelWith rowContLocal
    rw [hqc, Complex.one_cpow]
    ring
  rw [e]
  simp only [norm_mul, norm_inv, hZn, hre] <;> ring

private lemma kern_bound (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ ξ w z : ℂ, Scales.rightLine - Scales.contourOffset / 2 ≤ ξ.re → ξ.re ≤ 5 →
      Scales.rightLine - Scales.contourOffset / 2 ≤ w.re → w.re ≤ 5 → z.re = 1 / 6 + Scales.contourOffset →
        ‖kern D u Z ξ w z‖ ≤ Cc * ‖Complex.exp ((ξ + z - 1) ^ 2) * D.M z * D.W1Hat w‖ := by
  have hq : D.q u = 1 := PrincipalResidueFormulas.q_principal D u hu
  have hx : Scales.rightLine = 1 + Scales.contourOffset := rfl
  have hd : Scales.contourOffset = 1 / 10000000 := rfl
  have hZ0 : 0 < Z := by linarith
  obtain ⟨Cz, hCz0, hCz⟩ := RightHeckeBounds.zetaSCont_norm_le_right D (1 + 6 * Scales.contourOffset)
    (by rw [hd]; norm_num)
  obtain ⟨Cp, hCp0, hCp⟩ := RightHeckeBounds.Lpsi_norm_le_right D (1 + Scales.contourOffset / 2)
    (by rw [hd]; norm_num)
  obtain ⟨Cl, hCl0, hCl⟩ := RightHeckeBounds.Llam_inv_norm_le_right D (1 + Scales.contourOffset / 2)
    (by rw [hd]; norm_num)
  obtain ⟨CH, hCH0, hCH⟩ := EulerSubpower.Hu_subpower D (1 / 100) (by norm_num) 1 one_pos
  set Mx : ℝ := |Scales.xExponent / 2| + 5 + |Scales.smoothingExponent * (1 / 6 + Scales.contourOffset)| + |Scales.yExponent| * 4 with hMx
  refine ⟨Z ^ Mx * (Cz * Cp * CH * Cl), by positivity, ?_⟩
  intro ξ w z hξ1 hξ5 hw1 hw5 hz
  rw [kern_norm D u hu Z hZ0 ξ w z]
  have h6re : (6 * z).re = 6 * z.re := by simp [Complex.mul_re]
  have bZ : ‖D.zetaSCont (6 * z)‖ ≤ Cz := hCz _ (by rw [h6re, hz]; linarith)
  have bP : ‖D.Lpsi u w‖ ≤ Cp := hCp u _ (by rw [hx] at hw1; linarith)
  have bL : ‖D.Llam u ξ‖⁻¹ ≤ Cl := by
    have := hCl u ξ (by rw [hx] at hξ1; linarith)
    rwa [norm_inv] at this
  have hmem : ((ξ, w, z) : Coordinates) ∈ OmegaStarMargin (1 / 100) := by
    simp only [OmegaStarMargin, Set.mem_setOf_eq]
    rw [hz]
    rw [hx, hd] at hξ1 hw1
    rw [hd]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have bH : ‖EulerDomain.Hu D u ξ w z‖ ≤ CH := by
    have := (hCH u _ hmem).2
    rwa [hq, Real.one_rpow, mul_one] at this
  have nZ := norm_nonneg (D.zetaSCont (6 * z))
  have nP := norm_nonneg (D.Lpsi u w)
  have nH := norm_nonneg (EulerDomain.Hu D u ξ w z)
  have nL : 0 ≤ ‖D.Llam u ξ‖⁻¹ := by positivity
  have hP4 : ‖D.zetaSCont (6 * z)‖ * ‖D.Lpsi u w‖ * ‖EulerDomain.Hu D u ξ w z‖ *
      ‖D.Llam u ξ‖⁻¹ ≤ Cz * Cp * CH * Cl :=
    mul_le_mul (mul_le_mul (mul_le_mul bZ bP nP hCz0.le) bH nH (by positivity)) bL nL
      (by positivity)
  have hP0 : 0 ≤ ‖D.zetaSCont (6 * z)‖ * ‖D.Lpsi u w‖ * ‖EulerDomain.Hu D u ξ w z‖ *
      ‖D.Llam u ξ‖⁻¹ := by positivity
  have hy1 : 1 ≤ w.re := by rw [hx, hd] at hw1; linarith
  have hb4 : |Scales.yExponent * (w.re - 1)| ≤ |Scales.yExponent| * 4 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _)
  have hξ0 : 0 ≤ ξ.re := by rw [hx, hd] at hξ1; linarith
  have hZe : Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * z.re + Scales.yExponent * (w.re - 1)) ≤ Z ^ Mx := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have b1 := le_abs_self (Scales.xExponent / 2)
    have b3 := le_abs_self (Scales.smoothingExponent * (1 / 6 + Scales.contourOffset))
    have b5 := le_abs_self (Scales.yExponent * (w.re - 1))
    rw [hz, hMx]
    linarith
  have hZE : 0 ≤ Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * z.re + Scales.yExponent * (w.re - 1)) :=
    Real.rpow_nonneg hZ0.le _
  have hW0 := norm_nonneg (Complex.exp ((ξ + z - 1) ^ 2) * D.M z * D.W1Hat w)
  have hc0 : 0 ≤ Cz * Cp * CH * Cl := by positivity
  calc _ ≤ Z ^ Mx * ‖Complex.exp ((ξ + z - 1) ^ 2) * D.M z * D.W1Hat w‖ *
        (Cz * Cp * CH * Cl) := by
        refine mul_le_mul ?_ hP4 hP0 (by positivity)
        exact mul_le_mul_of_nonneg_right hZe hW0
    _ = _ := by ring

theorem kern_differentiableOn (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 0 < Z) :
    DifferentiableOn ℂ (fun p : Coordinates => kern D u Z p.1 p.2.1 p.2.2)
      ((paddedBox₂ ∩ {p : Coordinates | Scales.rightLine - Scales.contourOffset / 2 < p.1.re} ∩
        {p : Coordinates | 1 / 6 + Scales.contourOffset / 2 < p.2.2.re}) \ {p : Coordinates | p.2.1 = 1}) :=
  PrincipalKernelMajorants.kernel_analytic_paddedBox₂ D u hu Z hZ

theorem kernel_weight_bound_strip (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ ξ : ℂ, Scales.rightLine - Scales.contourOffset / 2 ≤ ξ.re → ξ.re ≤ 5 →
      ∀ y : ℝ, Scales.rightLine - Scales.contourOffset / 2 ≤ y → y ≤ 5 → ∀ s t : ℝ,
        ‖kern D u Z ξ ((y : ℂ) + (t : ℂ) * Complex.I)
            (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (s : ℂ) * Complex.I)‖ ≤
          Cc * WeightConvolution.weightModulus D ξ (1 / 6 + Scales.contourOffset) y (s, t) := by
  obtain ⟨Cc, hCc, h⟩ := kern_bound D u hu Z hZ
  refine ⟨Cc, hCc, fun ξ h1 h2 y hy1 hy2 s t => ?_⟩
  exact h ξ _ _ h1 h2 (by rw [re_line]; exact hy1) (by rw [re_line]; exact hy2) (by exact re_line _ _)

theorem kernel_weight_bound (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∃ k : ℝ, 0 ≤ k ∧
      ∀ ξ : ℂ, Scales.rightLine - Scales.contourOffset / 2 ≤ ξ.re → ξ.re ≤ 5 → ∀ s t : ℝ,
        ‖kern D u Z ξ ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I)
            (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (s : ℂ) * Complex.I)‖ ≤
          Cc * WeightConvolution.weightModulus D ξ (1 / 6 + Scales.contourOffset) Scales.rightLine (s, t) *
            (2 + |s| + |t| + |ξ.im|) ^ k := by
  obtain ⟨Cc, hCc, h⟩ := kernel_weight_bound_strip D u hu Z hZ
  refine ⟨Cc, hCc, 0, le_rfl, fun ξ h1 h2 s t => ?_⟩
  have hx : Scales.rightLine = 1 + Scales.contourOffset := rfl
  have hd : Scales.contourOffset = 1 / 10000000 := rfl
  have := h ξ h1 h2 Scales.rightLine (by rw [hx, hd]; norm_num) (by rw [hx, hd]; norm_num) s t
  simpa using this

theorem kernel_factor_bound (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ w z : ℂ, Scales.rightLine ≤ ξ.re → ξ.re ≤ 4 →
      Scales.rightLine - Scales.contourOffset / 2 ≤ w.re → w.re ≤ 5 → z.re = 1 / 6 + Scales.contourOffset →
        ‖kern D u Z ξ w z‖ ≤
          C * ‖D.W1Hat w‖ * ‖D.M z‖ * Real.exp (-(ξ.im + z.im) ^ 2) := by
  obtain ⟨Cc, hCc, h⟩ := kern_bound D u hu Z hZ
  refine ⟨Cc * Real.exp 25, by positivity, fun ξ w z h1 h2 h3 h4 h5 => ?_⟩
  have hx : Scales.rightLine = 1 + Scales.contourOffset := rfl
  have hd : Scales.contourOffset = 1 / 10000000 := rfl
  have hb := h ξ w z (by linarith) (by linarith) h3 h4 h5
  have hre : ((ξ + z - 1) ^ 2).re = (ξ.re + z.re - 1) ^ 2 - (ξ.im + z.im) ^ 2 := by
    simp [pow_two, Complex.mul_re] <;> ring
  have hE : ‖Complex.exp ((ξ + z - 1) ^ 2)‖ ≤
      Real.exp 25 * Real.exp (-(ξ.im + z.im) ^ 2) := by
    have e1 : ‖Complex.exp ((ξ + z - 1) ^ 2)‖ =
        Real.exp ((ξ.re + z.re - 1) ^ 2) * Real.exp (-(ξ.im + z.im) ^ 2) := by
      rw [Complex.norm_exp, hre, ← Real.exp_add]
      congr 1
      try ring
    rw [e1]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    rw [h5, hd]
    rw [hx, hd] at h1
    have hlo : 0 ≤ ξ.re + (1 / 6 + 1 / 10000000) - 1 := by linarith
    have hhi : ξ.re + (1 / 6 + 1 / 10000000) - 1 ≤ 5 := by linarith
    nlinarith [mul_nonneg hlo (sub_nonneg.2 hhi)]
  rw [norm_mul, norm_mul] at hb
  have nM := norm_nonneg (D.M z)
  have nW := norm_nonneg (D.W1Hat w)
  calc _ ≤ _ := hb
    _ ≤ Cc * ((Real.exp 25 * Real.exp (-(ξ.im + z.im) ^ 2)) * ‖D.M z‖ * ‖D.W1Hat w‖) := by
        gcongr
    _ = _ := by ring

end

end DedekindZetaZeroFree.Quantitative.PrincipalRightKernelBound31
