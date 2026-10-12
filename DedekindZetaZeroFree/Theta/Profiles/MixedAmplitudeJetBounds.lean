module

public import DedekindZetaZeroFree.Theta.Profiles.InducedAmplitudeDerivativeBounds
import DedekindZetaZeroFree.Theta.Profiles.UnitRadiusAmplitudeJets

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.ThetaArchInducedMajorant

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxRotatedKernelEstimates
open scoped ContDiff Matrix.Norms.Elementwise

private def radialOrbit (t : ℝ) : ComplexGL2 :=
  weyl * diagonal (radialUnit (Real.exp t) 1) * weyl

private lemma radialOrbit_contDiff :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun t => (radialOrbit t : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have he : (fun t => (radialOrbit t : Matrix (Fin 2) (Fin 2) ℂ)) =
      (fun t => (!![1, 0; 0, (Real.exp t : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ)) := by
    funext t
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [radialOrbit, weyl, diagonal, radialUnit,
        Real.exp_pos, Matrix.mul_apply, Fin.sum_univ_two]
  rw [he]
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (1 : ℂ)))
  · simpa using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0 : ℂ)))
  · simpa using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0 : ℂ)))
  · simpa [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.contDiff_exp.comp Complex.ofRealCLM.contDiff).restrict_scalars ℝ

private def radialSectionDerivative (f : PrincipalSeries positiveParameter) :
    PrincipalSeries positiveParameter :=
  KPCplxLoweringOrbitDifferentiation.orbitDerivativeSection positiveParameter
    radialOrbit radialOrbit_contDiff f

private lemma radialOrbit_matrix (u : ℂˣ) (ρ : ℝ) (x : ℂ) (hρ : 0 < ρ) (t : ℝ) :
    (weyl * upperUnipotent x * diagonal (radialUnit ρ u) * weyl) * radialOrbit t =
      weyl * upperUnipotent x * diagonal (radialUnit (ρ * Real.exp t) u) * weyl := by
  apply Units.ext
  ext i k
  have ht : 0 < ρ * Real.exp t := mul_pos hρ (Real.exp_pos t)
  fin_cases i <;> fin_cases k <;>
    simp [radialOrbit, weyl, upperUnipotent, diagonal, radialUnit, hρ, ht,
      Real.exp_pos, Matrix.mul_apply, Fin.sum_univ_two, Complex.ofReal_mul]
  all_goals ring

private lemma radiusLogDerivative_section (β κ : ℂˣ) (f : PrincipalSeries positiveParameter)
    (u : ℂˣ) (ρ : ℝ) (x : ℂ) (hρ : 0 < ρ) :
    radiusLogDerivative (rotatedAmplitude β κ f u) ρ x =
      rotatedAmplitude β κ (radialSectionDerivative f) u ρ x := by
  let A := rotatedAmplitude β κ f u
  have hs0 := rotatedAmplitude_contDiffAt β κ f u (ρ, x) hρ
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℝ => A r x) ρ :=
    ContDiffAt.comp (f := fun r : ℝ => (r, x))
      (g := fun z : ℝ × ℂ => rotatedAmplitude β κ f u z.1 z.2)
      ρ hs0 (contDiffAt_id.prodMk (contDiffAt_const (c := x)))
  have hd := (hs.differentiableAt (by simp)).hasDerivAt
  have he : HasDerivAt (fun t : ℝ => ρ * Real.exp t) ρ 0 := by
    simpa using (Real.hasDerivAt_exp 0).const_mul ρ
  have hc := HasDerivAt.scomp (g₁ := fun r : ℝ => A r x) (0 : ℝ)
    (by simpa only [Real.exp_zero, mul_one] using hd) he
  have hf : (fun t : ℝ => A (ρ * Real.exp t) x) =
      (fun t : ℝ => (κ : ℂ) * (characterScale β / (2 * Real.pi) : ℂ) *
        f ((weyl * upperUnipotent ((characterRotation β : ℂ) * x) *
          diagonal (radialUnit ρ u) * weyl) * radialOrbit t)) := by
    funext t
    dsimp [A, rotatedAmplitude]
    rw [radialOrbit_matrix u ρ _ hρ]
  simp only [Function.comp_def] at hc
  rw [hf] at hc
  have hh := hc.deriv
  rw [deriv_const_mul_field] at hh
  change (ρ : ℂ) * deriv (fun r : ℝ => A r x) ρ = _
  dsimp [rotatedAmplitude, radialSectionDerivative,
    KPCplxLoweringOrbitDifferentiation.orbitDerivativeSection]
  rw [hh]
  simp

private lemma amplitude_scaling (β κ : ℂˣ) (f : PrincipalSeries positiveParameter)
    (u : ℂˣ) (ρ : ℝ) (x : ℂ) (hρ : 0 < ρ) :
    rotatedAmplitude β κ f u ρ x =
      (Real.rpow ρ (-(4 / 3 : ℝ)) : ℂ) *
        rotatedAmplitude β κ f u 1 (ρ⁻¹ • x) := by
  let r : ℂˣ := Units.mk0 (ρ : ℂ) (by exact_mod_cast hρ.ne')
  have hm : weyl * upperUnipotent ((characterRotation β : ℂ) * x) *
      diagonal (radialUnit ρ u) * weyl =
      upperTriangular 1 r 0 * (weyl * upperUnipotent ((characterRotation β : ℂ) * (ρ⁻¹ • x)) *
        diagonal (radialUnit 1 u) * weyl) := by
    apply Units.ext
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [weyl, upperUnipotent, diagonal, upperTriangular, radialUnit, hρ, r,
        Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul, Complex.ofReal_inv]
    all_goals field_simp [show (ρ : ℂ) ≠ 0 by exact_mod_cast hρ.ne']
  have hw : inductionWeight positiveParameter 1 r = Real.rpow ρ (-(4 / 3 : ℝ)) := by
    simp only [inductionWeight, complexAbs, r, Units.val_one, Units.val_mk0,
      norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
      one_div, inv_pow]
    change Real.rpow ((ρ ^ 2)⁻¹) (2⁻¹ + 6⁻¹) = _
    calc
      Real.rpow ((ρ ^ 2)⁻¹) (2⁻¹ + 6⁻¹) = Real.rpow (ρ ^ 2) (-(2⁻¹ + 6⁻¹)) :=
        (Real.rpow_neg_eq_inv_rpow (ρ ^ 2) (2⁻¹ + 6⁻¹)).symm
      _ = Real.rpow ρ (2 * (-(2⁻¹ + 6⁻¹))) :=
        (Real.rpow_natCast_mul hρ.le 2 (-(2⁻¹ + 6⁻¹))).symm
      _ = _ := by norm_num
  unfold rotatedAmplitude
  rw [hm, f.property.1, hw]
  ring

private lemma horizontal_iterate_slice (F : ℝ → ℂ → ℂ) (h : ℕ) (ρ : ℝ) (x : ℂ) :
    ((horizontalRealDerivative^[h]) F) ρ x =
      iteratedDeriv h (fun t : ℝ => F ρ ⟨t, x.im⟩) x.re := by
  induction h generalizing x with
  | zero => rfl
  | succ h ih =>
    rw [Function.iterate_succ_apply', horizontalRealDerivative, iteratedDeriv_succ]
    congr 1
    funext t
    simpa using ih (⟨t, x.im⟩ : ℂ)

private lemma horizontal_iterate_fderiv (F : ℂ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (h : ℕ) (x : ℂ) :
    iteratedDeriv h (fun t : ℝ => F ⟨t, x.im⟩) x.re =
      iteratedFDeriv ℝ h F x (fun _ : Fin h => (1 : ℂ)) := by
  let G := fun z : ℂ => F (z + (x.im : ℂ) * Complex.I)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := hF.comp (contDiff_id.add contDiff_const)
  have he : (fun t : ℝ => F ⟨t, x.im⟩) = G ∘ Complex.ofRealCLM := by
    funext t
    apply congrArg F
    apply Complex.ext <;> simp
  rw [iteratedDeriv, he, Complex.ofRealCLM.iteratedFDeriv_comp_right hG x.re (by simp)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Complex.ofRealCLM_apply, Complex.ofReal_one]
  rw [show G = fun z : ℂ => F (z + (x.im : ℂ) * Complex.I) from rfl,
    iteratedFDeriv_comp_add_right]
  congr 2
  apply Complex.ext <;> simp

private lemma radial_iterate_section (β κ : ℂˣ) (f : PrincipalSeries positiveParameter)
    (u : ℂˣ) (j : ℕ) (ρ : ℝ) (x : ℂ) (hρ : 0 < ρ) :
    ((radiusLogDerivative^[j]) (rotatedAmplitude β κ f u)) ρ x =
      rotatedAmplitude β κ ((radialSectionDerivative^[j]) f) u ρ x := by
  induction j generalizing ρ x with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (ρ : ℂ) * deriv _ ρ = _
    have he := Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hρ)
      (fun r hr => ih r x hr)
    rw [Filter.EventuallyEq.deriv_eq he]
    exact radiusLogDerivative_section β κ _ u ρ x hρ

private lemma amplitude_horizontal_jets (β κ : ℂˣ) (f : PrincipalSeries positiveParameter)
    (u : ℂˣ) (h : ℕ) (ρ : ℝ) (x : ℂ) (hρ : 0 < ρ) :
    ((horizontalRealDerivative^[h]) (rotatedAmplitude β κ f u)) ρ x =
      iteratedFDeriv ℝ h (rotatedAmplitude β κ f u ρ) x
        (fun _ : Fin h => (1 : ℂ)) := by
  rw [horizontal_iterate_slice]
  apply horizontal_iterate_fderiv
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact ContDiffAt.comp (f := fun z : ℂ => (ρ, z))
    (g := fun p : ℝ × ℂ => rotatedAmplitude β κ f u p.1 p.2)
    z (rotatedAmplitude_contDiffAt β κ f u (ρ, z) hρ)
    (contDiffAt_const.prodMk contDiffAt_id)

private lemma mixed_section (β κ : ℂˣ) (f : PrincipalSeries positiveParameter)
    (u : ℂˣ) (j h : ℕ) (ρ : ℝ) (x : ℂ) (hρ : 0 < ρ) :
    amplitudeDerivative β κ f u j h ρ x =
      ((horizontalRealDerivative^[h])
        (rotatedAmplitude β κ ((radialSectionDerivative^[j]) f) u)) ρ x := by
  unfold amplitudeDerivative
  induction h generalizing x with
  | zero => exact radial_iterate_section β κ f u j ρ x hρ
  | succ h ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    unfold horizontalRealDerivative
    congr 1
    funext t
    exact ih ⟨t, x.im⟩

private lemma amplitude_fderiv_scaling (β κ : ℂˣ) (f : PrincipalSeries positiveParameter)
    (u : ℂˣ) (h : ℕ) (ρ : ℝ) (x : ℂ) (hρ : 0 < ρ) :
    iteratedFDeriv ℝ h (rotatedAmplitude β κ f u ρ) x
        (fun _ : Fin h => (1 : ℂ)) =
      (Real.rpow ρ (-(4 / 3 : ℝ) - (h : ℝ)) : ℂ) *
        iteratedFDeriv ℝ h (rotatedAmplitude β κ f u 1)
          (ρ⁻¹ • x) (fun _ : Fin h => (1 : ℂ)) := by
  let F := rotatedAmplitude β κ f u 1
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact ContDiffAt.comp (f := fun z : ℂ => ((1 : ℝ), z))
      (g := fun p : ℝ × ℂ => rotatedAmplitude β κ f u p.1 p.2)
      z (rotatedAmplitude_contDiffAt β κ f u (1, z) (by norm_num))
      (contDiffAt_const.prodMk contDiffAt_id)
  have he : rotatedAmplitude β κ f u ρ =
      (Real.rpow ρ (-(4 / 3 : ℝ)) : ℂ) • (fun z : ℂ => F (ρ⁻¹ • z)) := by
    funext z
    exact amplitude_scaling β κ f u ρ z hρ
  have hS : ContDiff ℝ (h : WithTop ℕ∞) (fun z : ℂ => F (ρ⁻¹ • z)) :=
    ContDiff.comp (f := fun z : ℂ => ρ⁻¹ • z) (g := F)
      (hF.of_le (show (h : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp))
      (contDiff_id.const_smul ρ⁻¹)
  rw [he, iteratedFDeriv_const_smul_apply (f := fun z : ℂ => F (ρ⁻¹ • z))
    (a := (Real.rpow ρ (-(4 / 3 : ℝ)) : ℂ)) hS.contDiffAt,
    iteratedFDeriv_comp_const_smul ρ⁻¹ (hF.of_le (by simp))]
  simp only [smul_apply, Complex.real_smul]
  have hp : (Real.rpow ρ (-(4 / 3 : ℝ)) : ℂ) * (↑(ρ⁻¹ ^ h) : ℂ) =
      (Real.rpow ρ (-(4 / 3 : ℝ) - (h : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    calc
      Real.rpow ρ (-(4 / 3 : ℝ)) * ρ⁻¹ ^ h =
          Real.rpow ρ (-(4 / 3 : ℝ)) * Real.rpow ρ (-(h : ℝ)) := by
        congr 1
        calc
          ρ⁻¹ ^ h = (ρ ^ h)⁻¹ := inv_pow ρ h
          _ = (Real.rpow ρ (h : ℝ))⁻¹ := congrArg Inv.inv (Real.rpow_natCast ρ h).symm
          _ = Real.rpow ρ (-(h : ℝ)) := (Real.rpow_neg hρ.le (h : ℝ)).symm
      _ = _ := by
        convert (Real.rpow_add hρ (-(4 / 3 : ℝ)) (-(h : ℝ))).symm using 1
  simp only [smul_eq_mul]
  rw [← mul_assoc, hp]

private theorem amplitude_mixed_derivative_rescaling (β κ : ℂˣ)
    (f : PrincipalSeries positiveParameter) (u : ℂˣ) (j h : ℕ)
    (ρ : ℝ) (x : ℂ) (hρ : 0 < ρ) :
    amplitudeDerivative β κ f u j h ρ x =
      (Real.rpow ρ (-(4 / 3 : ℝ) - (h : ℝ)) : ℂ) *
        iteratedFDeriv ℝ h
          (fun z : ℂ => rotatedAmplitude β κ
            ((radialSectionDerivative^[j]) f) u 1 z)
          (ρ⁻¹ • x) (fun _ : Fin h => (1 : ℂ)) := by
  rw [mixed_section β κ f u j h ρ x hρ,
    amplitude_horizontal_jets β κ _ u h ρ x hρ,
    amplitude_fderiv_scaling β κ _ u h ρ x hρ]

private lemma rescaled_envelope (h : ℕ) (ρ : ℝ) (x : ℂ) (hρ : 0 < ρ) :
    Real.rpow ρ (-(4 / 3 : ℝ) - (h : ℝ)) *
      Real.rpow (1 + ‖ρ⁻¹ • x‖ ^ 2) (-(4 / 3 : ℝ) - (h : ℝ) / 2) =
    Real.rpow ρ (4 / 3 : ℝ) *
      Real.rpow (ρ ^ 2 + ‖x‖ ^ 2) (-(4 / 3 : ℝ) - (h : ℝ) / 2) := by
  have he : 1 + ‖ρ⁻¹ • x‖ ^ 2 = (ρ ^ 2 + ‖x‖ ^ 2) / ρ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ]
    field_simp
  simp only [he, Real.rpow_eq_pow]
  rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_two ρ,
    ← Real.rpow_mul hρ.le]
  rw [← mul_div_assoc, mul_comm (ρ ^ (-(4 / 3 : ℝ) - (h : ℝ))),
    mul_div_assoc, ← Real.rpow_sub hρ, mul_comm]
  congr 1
  congr 1
  ring

theorem norm_amplitudeDerivative_le (β κ : ℂˣ)
    (f : PrincipalSeries positiveParameter) :
    ∀ (j h : ℕ), j ≤ 2 → ∃ C : ℝ, 0 < C ∧
      ∀ (u : ℂˣ) (ρ : ℝ) (x : ℂ), ‖(u : ℂ)‖ = 1 → 0 < ρ →
        ‖amplitudeDerivative β κ f u j h ρ x‖ ≤
          C * Real.rpow ρ (4 / 3 : ℝ) *
            Real.rpow (ρ ^ 2 + ‖x‖ ^ 2) (-(4 / 3 : ℝ) - (h : ℝ) / 2) := by
  intro j h _
  obtain ⟨C, hC, hb⟩ := norm_iteratedFDeriv_rotatedAmplitude_one_le
    β κ ((radialSectionDerivative^[j]) f) h
  refine ⟨C, hC, ?_⟩
  intro u ρ x hu hρ
  rw [amplitude_mixed_derivative_rescaling
    β κ f u j h ρ x hρ, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hp : 0 < Real.rpow ρ (-(4 / 3 : ℝ) - (h : ℝ)) := by
    exact Real.rpow_pos_of_pos hρ _
  rw [abs_of_pos hp]
  have hj := (iteratedFDeriv ℝ h
    (fun z : ℂ => rotatedAmplitude β κ
      ((radialSectionDerivative^[j]) f) u 1 z)
    (ρ⁻¹ • x)).le_mul_prod_of_opNorm_le_of_le (hb u (ρ⁻¹ • x) hu)
      (show ∀ i : Fin h, ‖(fun _ : Fin h => (1 : ℂ)) i‖ ≤ (1 : ℝ) by simp)
  simp only [Finset.prod_const_one, mul_one] at hj
  calc
    _ ≤ Real.rpow ρ (-(4 / 3 : ℝ) - (h : ℝ)) *
        (C * Real.rpow (1 + ‖ρ⁻¹ • x‖ ^ 2) (-(4 / 3 : ℝ) - (h : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg hρ.le _)
    _ = C * (Real.rpow ρ (-(4 / 3 : ℝ) - (h : ℝ)) *
        Real.rpow (1 + ‖ρ⁻¹ • x‖ ^ 2) (-(4 / 3 : ℝ) - (h : ℝ) / 2)) := by ring
    _ = _ := by rw [rescaled_envelope h ρ x hρ]; ring

end DedekindZetaZeroFree.ThetaArchInducedMajorant
