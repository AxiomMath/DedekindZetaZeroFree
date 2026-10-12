module

public import DedekindZetaZeroFree.Theta.Whittaker.ComplexRootDerivativeVectors
public import DedekindZetaZeroFree.Arithmetic.LocalFields.PlacesAndCompletions
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ComplexWhittakerUniqueness

@[expose] public section

section

noncomputable section

namespace DedekindZetaZeroFree.ThetaArchInducedMajorant

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage
open KPCplxRotatedKernelEstimates MeasureTheory Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

def rotatedAmplitude (β : ℂˣ) (κ : ℂˣ)
    (f : PrincipalSeries positiveParameter) (u : ℂˣ) (ρ : ℝ) (x : ℂ) : ℂ :=
  (κ : ℂ) * (characterScale β / (2 * Real.pi) : ℂ) *
    f (weyl * upperUnipotent ((characterRotation β : ℂ) * x) *
      diagonal (radialUnit ρ u) * weyl)

def radiusLogDerivative (A : ℝ → ℂ → ℂ) : ℝ → ℂ → ℂ :=
  fun ρ x => (ρ : ℂ) * deriv (fun r : ℝ => A r x) ρ

def amplitudeDerivative (β : ℂˣ) (κ : ℂˣ)
    (f : PrincipalSeries positiveParameter) (u : ℂˣ)
    (j h : ℕ) (ρ : ℝ) (x : ℂ) : ℂ :=
  ((horizontalRealDerivative^[h])
    ((radiusLogDerivative^[j]) (rotatedAmplitude β κ f u))) ρ x

def HasInducedAmplitudeEstimates (β : ℂˣ) (κ : ℂˣ)
    (f : PrincipalSeries positiveParameter) : Prop :=
  (∀ u : ℂˣ, ‖(u : ℂ)‖ = 1 →
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => rotatedAmplitude β κ f u p.1 p.2)
      {p | 0 < p.1}) ∧
  (∀ (j h : ℕ), j ≤ 2 → ∃ C : ℝ, 0 < C ∧
    ∀ (u : ℂˣ) (ρ : ℝ) (x : ℂ), ‖(u : ℂ)‖ = 1 → 0 < ρ →
      ‖amplitudeDerivative β κ f u j h ρ x‖ ≤
        C * Real.rpow ρ (4 / 3 : ℝ) *
          Real.rpow (ρ ^ 2 + ‖x‖ ^ 2) (-(4 / 3 : ℝ) - (h : ℝ) / 2)) ∧
  (∀ (j h : ℕ), j ≤ 2 → ∀ (u : ℂˣ) (ρ : ℝ),
    ‖(u : ℂ)‖ = 1 → 0 < ρ →
      Integrable (amplitudeDerivative β κ f u j h ρ) euclideanArea ∧
      ∀ b : ℝ,
        Integrable (fun t : ℝ => amplitudeDerivative β κ f u j h ρ ⟨t, b⟩) ∧
        Tendsto (fun t : ℝ => amplitudeDerivative β κ f u j h ρ ⟨t, b⟩)
          atTop (𝓝 0) ∧
        Tendsto (fun t : ℝ => amplitudeDerivative β κ f u j h ρ ⟨t, b⟩)
          atBot (𝓝 0))

theorem rotated_jacquet_integral (β κ : ℂˣ) (f : PrincipalSeries positiveParameter) (u : ℂˣ) (ρ : ℝ) :
    (κ : ℂ) * KPCplxJacquetFunctional.jacquetIntegral β
      (pi positiveParameter (Matrix.ProjGenLinGroup.mk (diagonal (radialUnit ρ u) * weyl)) f) =
    ∫ x : ℂ, Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
      rotatedAmplitude β κ f u ρ x ∂euclideanArea := by
  let g := pi positiveParameter
    (Matrix.ProjGenLinGroup.mk (diagonal (radialUnit ρ u) * weyl)) f
  let F := fun x : ℂ => g (weyl * upperUnipotent x) *
    (character (β : ℂ) (-x) : ℂ)
  have hrot : (∫ x : ℂ, F x ∂characterHaar β) =
      ∫ x : ℂ, F ((characterRotation β : ℂ) * x) ∂characterHaar β := by
    have hi := (KPCplxJacquetFunctional.jacquetIntegral_integrable β g).aestronglyMeasurable
    have hm : Measure.map (fun x : ℂ => (characterRotation β : ℂ) * x)
      (characterHaar β) = characterHaar β := characterHaar_rotation β
    have hi' : AEStronglyMeasurable F (Measure.map
        (fun x : ℂ => (characterRotation β : ℂ) * x) (characterHaar β)) := by
      rw [hm]; exact hi
    have hh := integral_map (μ := characterHaar β)
      (φ := fun x : ℂ => (characterRotation β : ℂ) * x)
      (by fun_prop : Measurable (fun x : ℂ => (characterRotation β : ℂ) * x)).aemeasurable hi'
    rw [hm] at hh
    exact hh
  change (κ : ℂ) * (∫ x : ℂ, F x ∂characterHaar β) = _
  rw [hrot, characterHaar, integral_smul_measure, ENNReal.toReal_ofReal
    (le_of_lt (div_pos (characterScale_pos β) (by positivity)))]
  simp only [Complex.real_smul]
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  have hc : (character (β : ℂ) (-((characterRotation β : ℂ) * x)) : ℂ) =
      Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) := by
    rw [show -((characterRotation β : ℂ) * x) = (characterRotation β : ℂ) * (-x) by ring,
      character_rotated, Circle.coe_exp]
    simp only [Complex.neg_re]
    congr 1
    push_cast
    ring
  dsimp [F, g, rotatedAmplitude]
  rw [hc]
  change (κ : ℂ) * (((characterScale β / (2 * Real.pi) : ℝ) : ℂ) *
    (f ((weyl * upperUnipotent ((characterRotation β : ℂ) * x)) *
      (diagonal (radialUnit ρ u) * weyl)) * _)) = _
  simp only [mul_assoc, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

private lemma sliceEnvelopeReal_integrable (h : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    Integrable (fun t : ℝ => ρ ^ (4 / 3 : ℝ) *
      (ρ ^ 2 + t ^ 2) ^ (-(4 / 3 : ℝ) - (h : ℝ) / 2)) := by
  have hr : (Module.finrank ℝ ℝ : ℝ) < (8 / 3 : ℝ) + (h : ℝ) := by
    simp only [Module.finrank_self, Nat.cast_one]
    have hn : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
    linarith
  have hi : Integrable (fun t : ℝ => (1 + ‖t‖ ^ 2) ^
      (-(4 / 3 : ℝ) - (h : ℝ) / 2)) := by
    convert (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) hr) using 1 <;> ring
  have hj := (hi.comp_smul (inv_ne_zero hρ.ne')).const_mul
    (ρ ^ (-(4 / 3 : ℝ) - (h : ℝ)))
  apply hj.congr (Eventually.of_forall fun t => ?_)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ),
    Real.norm_eq_abs, sq_abs, smul_eq_mul]
  have he : ρ ^ 2 + t ^ 2 = ρ ^ 2 * (1 + (ρ⁻¹ * t) ^ 2) := by
    field_simp
  rw [he, Real.mul_rpow (sq_nonneg ρ) (by positivity)]
  rw [← Real.rpow_natCast_mul hρ.le, ← mul_assoc, ← Real.rpow_add hρ]
  congr 1
  ring

private lemma sliceEnvelope_integrable (h : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (b : ℝ) :
    Integrable (fun t : ℝ => rationalEnvelope h ρ ⟨t, b⟩) := by
  have hi := sliceEnvelopeReal_integrable h ρ hρ
  have hm : Continuous (fun t : ℝ => rationalEnvelope h ρ ⟨t, b⟩) := by
    unfold rationalEnvelope
    apply continuous_const.mul
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Real.continuousAt_rpow_const _ _ (Or.inl (by positivity))).comp
    simp only [Complex.sq_norm, Complex.normSq_mk]
    fun_prop
  apply hi.mono' hm.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  unfold rationalEnvelope
  have he : ρ ^ 2 + t ^ 2 ≤ ρ ^ 2 + ‖(⟨t, b⟩ : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mk]
    nlinarith [sq_nonneg b]
  have hp := Real.rpow_le_rpow_of_nonpos
    (show 0 < ρ ^ 2 + t ^ 2 by positivity) he
    (show -(4 / 3 : ℝ) - (h : ℝ) / 2 ≤ 0 by
      have hn : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
      linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hρ.le _)

private lemma sliceEnvelope_tendsto_atTop (h : ℕ) (ρ b : ℝ) :
    Tendsto (fun t : ℝ => rationalEnvelope h ρ ⟨t, b⟩) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => ρ ^ 2 + ‖(⟨t, b⟩ : ℂ)‖ ^ 2) atTop atTop := by
    simp only [Complex.sq_norm, Complex.normSq_mk]
    have hh : Tendsto (fun t : ℝ => t * t) atTop atTop := by
      simpa only [pow_two] using (tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by decide) :
        Tendsto (fun t : ℝ => t ^ 2) atTop atTop)
    exact (tendsto_const_nhds.add_atTop (hh.atTop_add tendsto_const_nhds))
  have hp := (tendsto_rpow_neg_atTop (show 0 < (4 / 3 : ℝ) + (h : ℝ) / 2 by
    have hn : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
    linarith)).comp ht
  convert hp.const_mul (ρ ^ (4 / 3 : ℝ)) using 1 <;> simp [rationalEnvelope, neg_add_rev, sub_eq_add_neg, add_comm]

private lemma sliceEnvelope_tendsto_atBot (h : ℕ) (ρ b : ℝ) :
    Tendsto (fun t : ℝ => rationalEnvelope h ρ ⟨t, b⟩) atBot (𝓝 0) := by
  have hh := (sliceEnvelope_tendsto_atTop h ρ b).comp tendsto_neg_atBot_atTop
  convert hh using 1
  funext t
  unfold rationalEnvelope
  simp only [Function.comp_apply, Complex.sq_norm, Complex.normSq_mk, neg_mul_neg]

lemma regularity_of_bound (h : ℕ) (ρ C : ℝ) (hρ : 0 < ρ)
    (F : ℂ → ℂ) (hm : AEStronglyMeasurable F KPCplxCharacterHaar.euclideanArea)
    (hs : ∀ b : ℝ, AEStronglyMeasurable (fun t : ℝ => F ⟨t, b⟩) volume)
    (hb : ∀ x : ℂ, ‖F x‖ ≤ C * rationalEnvelope h ρ x) :
    Integrable F KPCplxCharacterHaar.euclideanArea ∧
    ∀ b : ℝ, Integrable (fun t : ℝ => F ⟨t, b⟩) ∧
      Tendsto (fun t : ℝ => F ⟨t, b⟩) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => F ⟨t, b⟩) atBot (𝓝 0) := by
  refine ⟨((rationalEnvelope_integrable h ρ hρ).const_mul C).mono' hm
    (Eventually.of_forall hb), ?_⟩
  intro b
  refine ⟨((sliceEnvelope_integrable h ρ hρ b).const_mul C).mono' (hs b)
    (Eventually.of_forall fun t => hb ⟨t, b⟩), ?_, ?_⟩
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun t => hb ⟨t, b⟩)
      (by simpa using (sliceEnvelope_tendsto_atTop h ρ b).const_mul C)
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun t => hb ⟨t, b⟩)
      (by simpa using (sliceEnvelope_tendsto_atBot h ρ b).const_mul C)

private lemma matrixFunction_coe (f : ComplexGL2 → ℂ) (g : ComplexGL2) :
    matrixFunction f (g : Matrix (Fin 2) (Fin 2) ℂ) = f g := by
  unfold matrixFunction
  have hd : (g : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := (Matrix.GeneralLinearGroup.det g).ne_zero
  rw [dif_pos hd]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

private lemma smoothEval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℝ) (f : PrincipalSeries s) (q : E → ComplexGL2) (p : E)
    (hq : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (q x : Matrix (Fin 2) (Fin 2) ℂ)) p) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x => f (q x)) p := by
  have hf := ((principalSeries_mem_iff s f).mp f.property).2
  have hd : Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.det) := by
    simp_rw [Matrix.det_fin_two]
    fun_prop
  have ho : IsOpen {m : Matrix (Fin 2) (Fin 2) ℂ | m.det ≠ 0} :=
    isOpen_ne.preimage hd
  have hs := hf.contDiffAt (ho.mem_nhds (Matrix.GeneralLinearGroup.det (q p)).ne_zero)
  simpa only [Function.comp_def, matrixFunction_coe] using hs.comp p hq

private lemma smoothMul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q r : E → ComplexGL2) (p : E)
    (hq : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (q x : Matrix (Fin 2) (Fin 2) ℂ)) p)
    (hr : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (r x : Matrix (Fin 2) (Fin 2) ℂ)) p) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (q x * r x : Matrix (Fin 2) (Fin 2) ℂ)) p := by
  change ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (q x : Matrix (Fin 2) (Fin 2) ℂ) *
    (r x : Matrix (Fin 2) (Fin 2) ℂ)) p
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  apply ContDiffAt.sum
  intro l hl
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp hq i) l).mul
    (contDiffAt_pi.mp (contDiffAt_pi.mp hr l) j)

private lemma smoothUnip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : E → ℂ) (p : E) (hz : ContDiffAt ℝ (⊤ : ℕ∞) z p) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (upperUnipotent (z x) : Matrix (Fin 2) (Fin 2) ℂ)) p := by
  change ContDiffAt ℝ (⊤ : ℕ∞) (fun x => !![1, z x; 0, 1]) p
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp <;> first | exact contDiffAt_const | exact hz

private lemma smoothRadialDiag (u : ℂˣ) (p : ℝ × ℂ) (hp : 0 < p.1) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℝ × ℂ =>
      (diagonal (radialUnit z.1 u) : Matrix (Fin 2) (Fin 2) ℂ)) p := by
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × ℂ => !![(z.1 : ℂ) * (u : ℂ), 0; 0, 1]) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;> simp <;>
      first | exact contDiff_const | exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_const
  apply hm.contDiffAt.congr_of_eventuallyEq
  have he : ∀ᶠ z : ℝ × ℂ in nhds p, 0 < z.1 :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hp
  filter_upwards [he] with z hz
  change !![(radialUnit z.1 u : ℂ), 0; 0, 1] = _
  simp only [radialUnit, dif_pos hz, Units.val_mk0]

private lemma smoothRadial (F : ℝ → ℂ → ℂ)
    (hf : ∀ p : ℝ × ℂ, 0 < p.1 → ContDiffAt ℝ (⊤ : ℕ∞) F.uncurry p) :
    ∀ p : ℝ × ℂ, 0 < p.1 → ContDiffAt ℝ (⊤ : ℕ∞) (radiusLogDerivative F).uncurry p := by
  intro p hp
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : (ℝ × ℂ) × ℝ => F z.2 z.1.2) (p, p.1) := by
    exact (hf p hp).comp (p, p.1) (contDiffAt_snd.prodMk (contDiffAt_snd.comp (p, p.1) contDiffAt_fst))
  have hd : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℝ × ℂ => deriv (fun t : ℝ => F t z.2) z.1) p := by
    simpa only [fderiv_apply_one_eq_deriv] using
      ((ContDiffAt.fderiv (f := fun z : ℝ × ℂ => fun t : ℝ => F t z.2)
        (g := Prod.fst) (m := (⊤ : ℕ∞)) hs contDiffAt_fst (by simp)).clm_apply
        (contDiffAt_const (c := (1 : ℝ))))
  exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp p
    contDiffAt_fst).mul hd)

private lemma smoothHorizontal (F : ℝ → ℂ → ℂ)
    (hf : ∀ p : ℝ × ℂ, 0 < p.1 → ContDiffAt ℝ (⊤ : ℕ∞) F.uncurry p) :
    ∀ p : ℝ × ℂ, 0 < p.1 → ContDiffAt ℝ (⊤ : ℕ∞) (horizontalRealDerivative F).uncurry p := by
  intro p hp
  have hmk : ContDiff ℝ (⊤ : ℕ∞) (fun z : (ℝ × ℂ) × ℝ => (z.1.1, (⟨z.2, z.1.2.im⟩ : ℂ))) := by
    exact (contDiff_fst.fst).prodMk (by
      have hm := (Complex.ofRealCLM.contDiff.comp (contDiff_snd : ContDiff ℝ (⊤ : ℕ∞) (fun z : (ℝ × ℂ) × ℝ => z.2))).add
        ((Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp contDiff_fst.snd)).mul (contDiff_const (c := Complex.I)))
      convert hm using 1
      funext z
      apply Complex.ext <;> simp)
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : (ℝ × ℂ) × ℝ => F z.1.1 ⟨z.2, z.1.2.im⟩) (p, p.2.re) := by
    exact (hf p hp).comp (p, p.2.re) hmk.contDiffAt
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × ℂ => z.2.re) := Complex.reCLM.contDiff.comp contDiff_snd
  change ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℝ × ℂ => deriv (fun t : ℝ => F z.1 ⟨t, z.2.im⟩) z.2.re) p
  simpa only [fderiv_apply_one_eq_deriv] using
    ((ContDiffAt.fderiv (f := fun z : ℝ × ℂ => fun t : ℝ => F z.1 ⟨t, z.2.im⟩)
      (g := fun z => z.2.re) (m := (⊤ : ℕ∞)) hs hg.contDiffAt (by simp)).clm_apply
      (contDiffAt_const (c := (1 : ℝ))))

lemma rotatedAmplitude_contDiffAt (β κ : ℂˣ)
    (f : PrincipalSeries positiveParameter) (u : ℂˣ)
    (p : ℝ × ℂ) (hp : 0 < p.1) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : ℝ × ℂ => rotatedAmplitude β κ f u z.1 z.2) p := by
  have hq : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℝ × ℂ =>
      (weyl * upperUnipotent ((characterRotation β : ℂ) * z.2) *
        diagonal (radialUnit z.1 u) * weyl : Matrix (Fin 2) (Fin 2) ℂ)) p := by
    apply smoothMul
      (fun z : ℝ × ℂ => weyl * upperUnipotent ((characterRotation β : ℂ) * z.2) *
        diagonal (radialUnit z.1 u)) (fun _ => weyl) p
    · apply smoothMul
        (fun z : ℝ × ℂ => weyl * upperUnipotent ((characterRotation β : ℂ) * z.2))
        (fun z => diagonal (radialUnit z.1 u)) p
      · apply smoothMul (fun _ => weyl)
          (fun z : ℝ × ℂ => upperUnipotent ((characterRotation β : ℂ) * z.2)) p
        · exact contDiffAt_const
        · apply smoothUnip
          exact contDiffAt_const.mul contDiffAt_snd
      · exact smoothRadialDiag u p hp
    · exact contDiffAt_const
  exact contDiffAt_const.mul (smoothEval positiveParameter f _ p hq)

lemma amplitudeDerivative_contDiffAt (β κ : ℂˣ)
    (f : PrincipalSeries positiveParameter) (u : ℂˣ)
    (j h : ℕ) (p : ℝ × ℂ) (hp : 0 < p.1) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : ℝ × ℂ => amplitudeDerivative β κ f u j h z.1 z.2) p := by
  have hr : ∀ j : ℕ, ∀ p : ℝ × ℂ, 0 < p.1 →
      ContDiffAt ℝ (⊤ : ℕ∞)
        ((radiusLogDerivative^[j]) (rotatedAmplitude β κ f u)).uncurry p := by
    intro j
    induction j with
    | zero => exact rotatedAmplitude_contDiffAt β κ f u
    | succ j hj =>
      simpa only [Function.iterate_succ_apply'] using smoothRadial _ hj
  have hh : ∀ h : ℕ, ∀ p : ℝ × ℂ, 0 < p.1 →
      ContDiffAt ℝ (⊤ : ℕ∞) ((horizontalRealDerivative^[h])
        ((radiusLogDerivative^[j]) (rotatedAmplitude β κ f u))).uncurry p := by
    intro h
    induction h with
    | zero => exact hr j
    | succ h hh =>
      simpa only [Function.iterate_succ_apply'] using smoothHorizontal _ hh
  exact hh h p hp

lemma amplitudeDerivative_continuous (β κ : ℂˣ)
    (f : PrincipalSeries positiveParameter) (u : ℂˣ)
    (j h : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (amplitudeDerivative β κ f u j h ρ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact ((amplitudeDerivative_contDiffAt β κ f u j h (ρ, x) hρ).continuousAt).comp
    (continuous_const.prodMk continuous_id).continuousAt

lemma hasInducedAmplitudeEstimates_of_bounds
    (β κ : ℂˣ) (f : PrincipalSeries positiveParameter)
    (hSmooth : ∀ u : ℂˣ, ‖(u : ℂ)‖ = 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℂ => rotatedAmplitude β κ f u p.1 p.2)
        {p | 0 < p.1})
    (hBound : ∀ (j h : ℕ), j ≤ 2 → ∃ C : ℝ, 0 < C ∧
      ∀ (u : ℂˣ) (ρ : ℝ) (x : ℂ), ‖(u : ℂ)‖ = 1 → 0 < ρ →
        ‖amplitudeDerivative β κ f u j h ρ x‖ ≤
          C * Real.rpow ρ (4 / 3 : ℝ) *
            Real.rpow (ρ ^ 2 + ‖x‖ ^ 2) (-(4 / 3 : ℝ) - (h : ℝ) / 2))
    (hMeas : ∀ (j h : ℕ), j ≤ 2 → ∀ (u : ℂˣ) (ρ : ℝ),
      ‖(u : ℂ)‖ = 1 → 0 < ρ →
        AEStronglyMeasurable (amplitudeDerivative β κ f u j h ρ) euclideanArea ∧
        ∀ b : ℝ, AEStronglyMeasurable
          (fun t : ℝ => amplitudeDerivative β κ f u j h ρ ⟨t, b⟩) volume) :
    HasInducedAmplitudeEstimates β κ f := by
  refine ⟨hSmooth, hBound, ?_⟩
  intro j h hj u ρ hu hρ
  obtain ⟨C, _, hC⟩ := hBound j h hj
  obtain ⟨hm, hs⟩ := hMeas j h hj u ρ hu hρ
  apply regularity_of_bound h ρ C hρ _ hm hs
  intro x
  simpa only [rationalEnvelope, mul_assoc, Real.rpow_eq_pow] using hC u ρ x hu hρ

lemma hasInducedAmplitudeEstimates_of_pointwise_bounds
    (β κ : ℂˣ) (f : PrincipalSeries positiveParameter)
    (hBound : ∀ (j h : ℕ), j ≤ 2 → ∃ C : ℝ, 0 < C ∧
      ∀ (u : ℂˣ) (ρ : ℝ) (x : ℂ), ‖(u : ℂ)‖ = 1 → 0 < ρ →
        ‖amplitudeDerivative β κ f u j h ρ x‖ ≤
          C * Real.rpow ρ (4 / 3 : ℝ) *
            Real.rpow (ρ ^ 2 + ‖x‖ ^ 2) (-(4 / 3 : ℝ) - (h : ℝ) / 2)) :
    HasInducedAmplitudeEstimates β κ f := by
  refine hasInducedAmplitudeEstimates_of_bounds β κ f ?_ hBound ?_
  · intro u hu p hp
    exact (rotatedAmplitude_contDiffAt β κ f u p hp).contDiffWithinAt
  · intro j h hj u ρ hu hρ
    have hc := amplitudeDerivative_continuous β κ f u j h ρ hρ
    refine ⟨hc.aestronglyMeasurable, fun b => ?_⟩
    have hslice : Continuous (fun t : ℝ => (⟨t, b⟩ : ℂ)) := by
      have hm := Complex.ofRealCLM.continuous.add
        (continuous_const (y := (b : ℂ) * Complex.I))
      convert hm using 1
      funext t
      apply Complex.ext <;> simp
    exact (hc.comp hslice).aestronglyMeasurable

end DedekindZetaZeroFree.ThetaArchInducedMajorant

end

end
