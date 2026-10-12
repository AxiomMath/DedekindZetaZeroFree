module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Complex.SU2ActionAndReconstruction
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.RealParameterReconstruction

@[expose] public section

section

namespace DedekindZetaZeroFree.KPComplexStandardIntertwinerGerm

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open KPComplexIntertwinerParameterMajorant KPCplxIntertwinerEigenvalues
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Elementwise

def suMatrix (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![star b, -star a; a, b]
private lemma suMatrix_mem (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    suMatrix a b ∈ ComplexSU2 := by
  have h' : a * star a + b * star b = 1 := by
    change a * (starRingEnd ℂ) a + b * (starRingEnd ℂ) b = 1
    rw [Complex.mul_conj, Complex.mul_conj]
    norm_cast
    simpa [Complex.normSq_eq_norm_sq] using h
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [suMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, star_star]
    · change star b * b + star a * a = 1
      calc star b * b + star a * a = a * star a + b * star b := by ring
           _ = 1 := h'
    · ring
    · ring
    · exact h'
  · simp only [suMatrix, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    calc star b * b - -star a * a = a * star a + b * star b := by ring
      _ = 1 := h'
private lemma rep_open (z : ℂ) : ∃ k : ComplexSU2,
    bottomRowLine (complexSU2Embedding k) = projectiveOpen z := by
  let r : ℝ := Real.sqrt (1 + ‖z‖ ^ 2)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr2 : r ^ 2 = 1 + ‖z‖ ^ 2 := Real.sq_sqrt (by positivity)
  let a : ℂ := ((r : ℂ))⁻¹
  let b : ℂ := z / (r : ℂ)
  have hn : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by
    dsimp [a, b]
    rw [norm_inv, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    field_simp
    nlinarith
  let k : ComplexSU2 := ⟨suMatrix a b, suMatrix_mem a b hn⟩
  refine ⟨k, ?_⟩
  have ha : a ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')
  have hrat : b / a = z := by
    dsimp [a, b]
    field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
  change bottomRowLine (Matrix.GeneralLinearGroup.mkOfDetNeZero (suMatrix a b) _) = _
  simp [bottomRowLine, suMatrix, ha, hrat]

theorem compact_representative_exists (p : ComplexProjectiveLine) :
    ∃ k : ComplexSU2, bottomRowLine (complexSU2Embedding k) = p := by
  rcases projective_chart_cover p with ⟨z, rfl⟩ | ⟨u, rfl⟩
  · exact rep_open z
  · by_cases hu : u = 0
    · subst u
      refine ⟨1, ?_⟩
      simp [bottomRowLine]
    · rw [projective_chart_transition u hu]
      exact rep_open u⁻¹

noncomputable def compactRepresentative (p : ComplexProjectiveLine) : ComplexSU2 :=
  Classical.choose (compact_representative_exists p)

public theorem bottomRowLine_compactRepresentative (p : ComplexProjectiveLine) :
    bottomRowLine (complexSU2Embedding (compactRepresentative p)) = p :=
  Classical.choose_spec (compact_representative_exists p)

end DedekindZetaZeroFree.KPComplexStandardIntertwinerGerm

end

section

namespace DedekindZetaZeroFree.KPComplexStandardIntertwinerGerm

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open KPComplexIntertwinerParameterMajorant KPCplxIntertwinerEigenvalues
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Elementwise

def halfPlane : Set ℂ := {s | -(1 / 6 : ℝ) < s.re}

theorem halfPlane_open_connected : IsOpen halfPlane ∧ IsConnected halfPlane := by
  constructor
  · exact isOpen_lt continuous_const Complex.continuous_re
  · exact (convex_halfSpace_re_gt (-(1 / 6 : ℝ))).isConnected ⟨0, by norm_num [halfPlane]⟩

def smoothFunctions : Submodule ℂ (ComplexProjectiveLine → ℂ) where
  carrier := {f | ContDiff ℝ ∞ (f ∘ projectiveOpen) ∧
    ContDiff ℝ ∞ (f ∘ projectiveInfinity)}
  zero_mem' := ⟨contDiff_const, contDiff_const⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, hf.2.const_smul c⟩

def compactEquiv : CompactPicture ≃ smoothFunctions where
  toFun φ := ⟨φ.toFun, φ.open_smooth, φ.infinity_smooth⟩
  invFun f := ⟨f.val, f.property.1, f.property.2⟩
  left_inv φ := rfl
  right_inv f := rfl

instance compactAddCommGroup : AddCommGroup CompactPicture := compactEquiv.addCommGroup

def compactAddEquiv : CompactPicture ≃+ smoothFunctions where
  toEquiv := compactEquiv
  map_add' φ ψ := rfl

instance compactModule : Module ℂ CompactPicture := compactAddEquiv.module ℂ

private def vals (j : ℕ) (φ : CompactPicture) : Set ℝ :=
  {0} ∪ {r : ℝ | ∃ q : ℕ, q ≤ j ∧ ∃ z : ℂ,
    z ∈ Metric.closedBall (0 : ℂ) 1 ∧
      (r = ‖iteratedFDeriv ℝ q (φ ∘ projectiveOpen) z‖ ∨
       r = ‖iteratedFDeriv ℝ q (φ ∘ projectiveInfinity) z‖)}
private lemma vals_bdd (j : ℕ) (φ : CompactPicture) : BddAbove (vals j φ) := by
  have hb (q : ℕ) : ∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ q (φ ∘ projectiveOpen) z‖ ≤ C ∧
      ‖iteratedFDeriv ℝ q (φ ∘ projectiveInfinity) z‖ ≤ C := by
    have ho := (isCompact_closedBall (0 : ℂ) 1).image
      ((φ.open_smooth.continuous_iteratedFDeriv (m := q) (by simp)).norm)
    have hi := (isCompact_closedBall (0 : ℂ) 1).image
      ((φ.infinity_smooth.continuous_iteratedFDeriv (m := q) (by simp)).norm)
    rcases ho.bddAbove with ⟨a, ha⟩
    rcases hi.bddAbove with ⟨b, hb⟩
    refine ⟨max a b, fun z hz => ⟨?_, ?_⟩⟩
    · exact (ha ⟨z, hz, rfl⟩).trans (le_max_left _ _)
    · exact (hb ⟨z, hz, rfl⟩).trans (le_max_right _ _)
  induction j with
  | zero =>
    rcases hb 0 with ⟨C, hC⟩
    refine ⟨max 0 C, ?_⟩
    rintro r (hr | ⟨q, hq, z, hz, hr⟩)
    · simpa only [mem_singleton_iff.mp hr] using le_max_left (0 : ℝ) C
    · have hq0 : q = 0 := by omega
      subst q
      rcases hr with rfl | rfl
      · exact (hC z hz).1.trans (le_max_right _ _)
      · exact (hC z hz).2.trans (le_max_right _ _)
  | succ j ih =>
    rcases ih with ⟨A, hA⟩
    rcases hb (j+1) with ⟨C, hC⟩
    refine ⟨max A C, ?_⟩
    rintro r (hr | ⟨q, hq, z, hz, hr⟩)
    · exact (hA (Or.inl hr)).trans (le_max_left _ _)
    · by_cases hqj : q ≤ j
      · exact (hA (Or.inr ⟨q, hqj, z, hz, hr⟩)).trans (le_max_left _ _)
      · have heq : q = j + 1 := by omega
        subst q
        rcases hr with rfl | rfl
        · exact (hC z hz).1.trans (le_max_right _ _)
        · exact (hC z hz).2.trans (le_max_right _ _)
private lemma p_nonneg (j : ℕ) (φ : CompactPicture) : 0 ≤ sourceSeminorm j φ :=
  le_csSup (vals_bdd j φ) (Or.inl rfl)
private lemma p_le {j : ℕ} {φ : CompactPicture} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ q ≤ j, ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ q (φ ∘ projectiveOpen) z‖ ≤ C ∧
      ‖iteratedFDeriv ℝ q (φ ∘ projectiveInfinity) z‖ ≤ C) : sourceSeminorm j φ ≤ C := by
  apply csSup_le (show (vals j φ).Nonempty from ⟨0, Or.inl rfl⟩)
  rintro r (hr | ⟨q, hq, z, hz, hr⟩)
  · simpa only [mem_singleton_iff.mp hr] using hC
  · rcases hr with rfl | rfl
    · exact (h q hq z hz).1
    · exact (h q hq z hz).2
private lemma p_bounds (j : ℕ) (φ : CompactPicture) (q : ℕ) (hq : q ≤ j)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
      ‖iteratedFDeriv ℝ q (φ ∘ projectiveOpen) z‖ ≤ sourceSeminorm j φ ∧
      ‖iteratedFDeriv ℝ q (φ ∘ projectiveInfinity) z‖ ≤ sourceSeminorm j φ := by
  constructor
  · exact le_csSup (vals_bdd j φ) (Or.inr ⟨q, hq, z, hz, Or.inl rfl⟩)
  · exact le_csSup (vals_bdd j φ) (Or.inr ⟨q, hq, z, hz, Or.inr rfl⟩)
private lemma deriv_add (q : ℕ) (φ ψ : CompactPicture) (chart : ℂ → ComplexProjectiveLine)
    (hφ : ContDiff ℝ ∞ (φ ∘ chart)) (hψ : ContDiff ℝ ∞ (ψ ∘ chart)) (z : ℂ) :
    iteratedFDeriv ℝ q ((φ + ψ) ∘ chart) z =
      iteratedFDeriv ℝ q (φ ∘ chart) z + iteratedFDeriv ℝ q (ψ ∘ chart) z := by
  exact iteratedFDeriv_add_apply ((hφ.of_le (by simp)).contDiffAt)
    ((hψ.of_le (by simp)).contDiffAt)
private lemma deriv_smul (q : ℕ) (c : ℂ) (φ : CompactPicture) (chart : ℂ → ComplexProjectiveLine)
    (hφ : ContDiff ℝ ∞ (φ ∘ chart)) (z : ℂ) :
    iteratedFDeriv ℝ q ((c • φ) ∘ chart) z = c • iteratedFDeriv ℝ q (φ ∘ chart) z := by
  exact iteratedFDeriv_const_smul_apply ((hφ.of_le (by simp)).contDiffAt)
private lemma p_zero (j : ℕ) : sourceSeminorm j 0 = 0 := by
  apply le_antisymm _ (p_nonneg j 0)
  apply p_le le_rfl
  intro q hq z hz
  constructor <;> change ‖iteratedFDeriv ℝ q (fun _ : ℂ => (0 : ℂ)) z‖ ≤ 0 <;> simp
private lemma p_add (j : ℕ) (φ ψ : CompactPicture) :
    sourceSeminorm j (φ + ψ) ≤ sourceSeminorm j φ + sourceSeminorm j ψ := by
  apply p_le (add_nonneg (p_nonneg j φ) (p_nonneg j ψ))
  intro q hq z hz
  constructor
  · rw [deriv_add q φ ψ projectiveOpen φ.open_smooth ψ.open_smooth]
    exact (norm_add_le _ _).trans (add_le_add (p_bounds j φ q hq z hz).1
      (p_bounds j ψ q hq z hz).1)
  · rw [deriv_add q φ ψ projectiveInfinity φ.infinity_smooth ψ.infinity_smooth]
    exact (norm_add_le _ _).trans (add_le_add (p_bounds j φ q hq z hz).2
      (p_bounds j ψ q hq z hz).2)
private lemma p_smul_le (j : ℕ) (c : ℂ) (φ : CompactPicture) :
    sourceSeminorm j (c • φ) ≤ ‖c‖ * sourceSeminorm j φ := by
  apply p_le (mul_nonneg (norm_nonneg _) (p_nonneg j φ))
  intro q hq z hz
  constructor
  · rw [deriv_smul q c φ projectiveOpen φ.open_smooth, norm_smul]
    exact mul_le_mul_of_nonneg_left (p_bounds j φ q hq z hz).1 (norm_nonneg _)
  · rw [deriv_smul q c φ projectiveInfinity φ.infinity_smooth, norm_smul]
    exact mul_le_mul_of_nonneg_left (p_bounds j φ q hq z hz).2 (norm_nonneg _)
private lemma p_smul (j : ℕ) (c : ℂ) (φ : CompactPicture) :
    sourceSeminorm j (c • φ) = ‖c‖ * sourceSeminorm j φ := by
  by_cases hc : c = 0
  · subst c
    simp [p_zero]
  · apply le_antisymm (p_smul_le j c φ)
    have h := mul_le_mul_of_nonneg_left (p_smul_le j c⁻¹ (c • φ)) (norm_nonneg c)
    simpa [smul_smul, hc, norm_inv, ← mul_assoc] using h
private lemma p_neg (j : ℕ) (φ : CompactPicture) :
    sourceSeminorm j (-φ) = sourceSeminorm j φ := by
  simpa using p_smul j (-1) φ

theorem sourceSeminorm_laws (j : ℕ) :
    sourceSeminorm j 0 = 0 ∧
    (∀ φ ψ : CompactPicture, sourceSeminorm j (φ + ψ) ≤
      sourceSeminorm j φ + sourceSeminorm j ψ) ∧
    (∀ φ : CompactPicture, sourceSeminorm j (-φ) = sourceSeminorm j φ) ∧
    (∀ (c : ℂ) (φ : CompactPicture), sourceSeminorm j (c • φ) =
      ‖c‖ * sourceSeminorm j φ) := by
  exact ⟨p_zero j, p_add j, p_neg j, p_smul j⟩

noncomputable def compactSeminorm (j : ℕ) : Seminorm ℂ CompactPicture where
  toFun := sourceSeminorm j
  map_zero' := (sourceSeminorm_laws j).1
  add_le' := (sourceSeminorm_laws j).2.1
  neg' := (sourceSeminorm_laws j).2.2.1
  smul' := (sourceSeminorm_laws j).2.2.2

noncomputable instance compactTopology : TopologicalSpace CompactPicture :=
  (SeminormFamily.moduleFilterBasis compactSeminorm).topology

private theorem compact_withSeminorms : WithSeminorms compactSeminorm := ⟨rfl⟩

noncomputable instance compactTopologicalAddGroup : IsTopologicalAddGroup CompactPicture :=
  compact_withSeminorms.isTopologicalAddGroup

noncomputable instance compactContinuousSMul : ContinuousSMul ℂ CompactPicture :=
  compact_withSeminorms.continuousSMul

private theorem compact_pointwise :
    (∀ (φ ψ : CompactPicture) z, (φ + ψ) z = φ z + ψ z) ∧
    (∀ (c : ℂ) (φ : CompactPicture) z, (c • φ) z = c * φ z) := ⟨by intros; rfl, by intros; rfl⟩

noncomputable def backwardSection (s : ℂ) (φ : CompactPicture) (g : ComplexGL2) : ℂ :=
  Complex.exp (((2 / 3 : ℂ) - 2 * s) * (Real.log (rowRatio g) : ℂ)) *
    φ (bottomRowLine g)

private lemma rowRatio_pos (g : ComplexGL2) : 0 < rowRatio g := by
  have hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 :=
    (Matrix.GeneralLinearGroup.det g).ne_zero
  have hr : 0 < bottomRowNormSq g := by
    unfold bottomRowNormSq
    by_contra hn
    have he : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 = 0 :=
      le_antisymm (le_of_not_gt hn) (by positivity)
    have h0 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖]
    have h1 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖]
    apply hdet
    simp [Matrix.det_fin_two, h0, h1]
  exact div_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det g).ne_zero) hr

private theorem compactRepresentative_line (p : ComplexProjectiveLine) :
    bottomRowLine (complexSU2Embedding (compactRepresentative p)) = p :=
  Classical.choose_spec (compact_representative_exists p)

noncomputable def haarIntegral (β : ℂˣ) (s : ℂ) (φ : CompactPicture)
    (g : ComplexGL2) : ℂ :=
  ∫ x : ℂ, forwardSection s φ (weyl * upperUnipotent x * g) ∂characterHaar β

private lemma wn_matrix_continuous (g : ComplexGL2) :
    Continuous (fun x : ℂ => (weyl * upperUnipotent x * g : Matrix (Fin 2) (Fin 2) ℂ)) := by
  change Continuous (fun x : ℂ =>
    (!![0, 1; 1, 0] * !![1, x; 0, 1]) * (g : Matrix (Fin 2) (Fin 2) ℂ))
  fun_prop

private lemma wn_ratio_continuous (g : ComplexGL2) :
    Continuous (fun x : ℂ => rowRatio (weyl * upperUnipotent x * g)) := by
  have hm := wn_matrix_continuous g
  have hd : Continuous (fun x : ℂ =>
      ‖Matrix.det (weyl * upperUnipotent x * g : Matrix (Fin 2) (Fin 2) ℂ)‖) := by
    simp only [Matrix.det_fin_two]
    fun_prop
  have hb : Continuous (fun x : ℂ => bottomRowNormSq (weyl * upperUnipotent x * g)) := by
    unfold bottomRowNormSq
    fun_prop
  exact hd.div hb (fun x h => by
    have hp := rowRatio_pos (weyl * upperUnipotent x * g)
    simp [rowRatio, h] at hp)

private lemma wn_forward_continuous (s : ℂ) (φ : CompactPicture) (g : ComplexGL2) :
    Continuous (fun x : ℂ => forwardSection s φ (weyl * upperUnipotent x * g)) := by
  have hreal := (principalSeries_mem_iff positiveParameter (forwardSection 0 φ)).mp
    (by simpa using forwardSection_real_mem 0 φ)
  have hcont : Continuous (fun x : ℂ => forwardSection 0 φ (weyl * upperUnipotent x * g)) := by
    have hc := hreal.2.continuousOn.comp_continuous (wn_matrix_continuous g)
      (fun x => (Matrix.GeneralLinearGroup.det (weyl * upperUnipotent x * g)).ne_zero)
    convert hc using 1
    funext x
    dsimp [Function.comp_def, matrixFunction]
    have hn : Matrix.det (weyl * upperUnipotent x * g : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 :=
      (Matrix.GeneralLinearGroup.det (weyl * upperUnipotent x * g)).ne_zero
    rw [dif_pos hn]
    congr 1
    apply Units.ext
    rfl
  have hr := wn_ratio_continuous g
  have hl : Continuous (fun x : ℂ => (Real.log (rowRatio (weyl * upperUnipotent x * g)) : ℂ)) := by
    exact Complex.continuous_ofReal.comp (hr.log (fun x => (rowRatio_pos _).ne'))
  have heq : (fun x : ℂ => forwardSection s φ (weyl * upperUnipotent x * g)) =
      fun x => Complex.exp ((2 * s) * (Real.log (rowRatio (weyl * upperUnipotent x * g)) : ℂ)) *
        forwardSection 0 φ (weyl * upperUnipotent x * g) := by
    funext x
    unfold forwardSection
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [heq]
  exact (Complex.continuous_exp.comp (continuous_const.mul hl)).mul hcont

private def pointMatrixChart (g : ComplexGL2) : CompactMatrixChart 0 where
  domain := univ
  domain_open := isOpen_univ
  closedSet := {0}
  closedSet_compact := isCompact_singleton
  closedSet_subset := subset_univ _
  lift := fun _ => g
  lift_smooth := contDiffOn_const

private def pointDifferential : ChartDifferentialOperator 0 0 (univ : Set (Fin 0 → ℝ)) where
  coefficient := fun _ _ _ => 1
  coefficient_smooth := fun _ _ => contDiffOn_const

private lemma pointDerivative (m : ℕ) (s : ℂ) (φ : CompactPicture) (x : ℂ) (g : ComplexGL2) :
    mixedReconstructedDerivative (pointMatrixChart g) pointDifferential m s φ x 0 =
      iteratedDeriv m (fun t : ℂ => forwardSection t φ (weyl * upperUnipotent x * g)) s := by
  simp [mixedReconstructedDerivative, ChartDifferentialOperator.apply,
    pointDifferential, pointMatrixChart, iteratedFDeriv_zero_apply]

theorem haarIntegral_integrable (β : ℂˣ) (s : ℂ) (hs : s ∈ halfPlane)
    (φ : CompactPicture) (g : ComplexGL2) :
    Integrable (fun x : ℂ => forwardSection s φ (weyl * upperUnipotent x * g))
      (characterHaar β) := by
  obtain ⟨ε, δ, hε, hδ, hball, hmajor⟩ := compact_g_local_halfPlane_majorant s hs
  obtain ⟨C, N, hC, hbound⟩ := hmajor 0 0 (pointMatrixChart g) pointDifferential 0
  have henv : Integrable (planarEnvelope (1 + δ)) (characterHaar β) :=
    planarEnvelope_integrable (characterScale β / (2 * Real.pi)) (1 + δ)
      (div_pos (characterScale_pos β) (by positivity)) (by linarith)
  apply (henv.const_mul (C * sourceSeminorm N φ)).mono'
    (wn_forward_continuous s φ g).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have h := hbound s φ x 0 (Metric.mem_ball_self hε) (by simp [pointMatrixChart])
  simpa only [pointDerivative, iteratedDeriv_zero] using h

theorem haarIntegral_holomorphic (β : ℂˣ) (φ : CompactPicture) (g : ComplexGL2) :
    DifferentiableOn ℂ (fun s => haarIntegral β s φ g) halfPlane := by
  intro s hs
  obtain ⟨ε, δ, hε, hδ, hball, hmajor⟩ := compact_g_local_halfPlane_majorant s hs
  obtain ⟨C, N, hC, hbound⟩ := hmajor 0 0 (pointMatrixChart g) pointDifferential 1
  let F' : ℂ → ℂ → ℂ := fun t x =>
    (2 * (Real.log (rowRatio (weyl * upperUnipotent x * g)) : ℂ)) *
      forwardSection t φ (weyl * upperUnipotent x * g)
  have hderiv (t x : ℂ) :
      HasDerivAt (fun t => forwardSection t φ (weyl * upperUnipotent x * g)) (F' t x) t := by
    have H := (((hasDerivAt_const t (4 / 3 : ℂ)).add
      ((hasDerivAt_id t).const_mul 2)).mul_const
      (Real.log (rowRatio (weyl * upperUnipotent x * g)) : ℂ)).cexp.mul_const
        (φ (bottomRowLine (weyl * upperUnipotent x * g)))
    convert H using 1
    · funext y
      dsimp [forwardSection]
    · dsimp [F', forwardSection]
      ring_nf
  have hformula (t x : ℂ) :
      iteratedDeriv 1 (fun t => forwardSection t φ (weyl * upperUnipotent x * g)) t = F' t x := by
    simpa only [iteratedDeriv_one] using (hderiv t x).deriv
  have hmeas (t : ℂ) : AEStronglyMeasurable (F' t) (characterHaar β) := by
    have hl : Continuous (fun x : ℂ => (Real.log (rowRatio (weyl * upperUnipotent x * g)) : ℂ)) :=
      Complex.continuous_ofReal.comp ((wn_ratio_continuous g).log (fun x => (rowRatio_pos _).ne'))
    exact ((continuous_const.mul hl).mul (wn_forward_continuous t φ g)).aestronglyMeasurable
  have henv : Integrable (planarEnvelope (1 + δ)) (characterHaar β) :=
    planarEnvelope_integrable (characterScale β / (2 * Real.pi)) (1 + δ)
      (div_pos (characterScale_pos β) (by positivity)) (by linarith)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s hε)
    (Filter.Eventually.of_forall (fun t => (wn_forward_continuous t φ g).aestronglyMeasurable))
    (haarIntegral_integrable β s hs φ g) (hmeas s)
    (Filter.Eventually.of_forall (fun x t ht => by
      have hb := hbound t φ x 0 ht (by simp [pointMatrixChart])
      simpa only [pointDerivative, hformula] using hb))
    (henv.const_mul (C * sourceSeminorm N φ))
    (Filter.Eventually.of_forall (fun x t _ => hderiv t x))
  exact h.2.differentiableAt.differentiableWithinAt

noncomputable def compactRestrictionMap : CompactPicture →ₗ[ℂ] (ComplexSU2 → ℂ) where
  toFun φ k := φ (bottomRowLine (complexSU2Embedding k))
  map_add' φ ψ := rfl
  map_smul' c φ := rfl

noncomputable def compactHarmonic (ℓ : ℕ) : Submodule ℂ CompactPicture :=
  ((harmonicPolynomials ℓ).map polynomialCompactRestriction).comap compactRestrictionMap

theorem backwardSection_real_mem (t : ℝ) (φ : CompactPicture) :
    backwardSection (t : ℂ) φ ∈ principalSeriesSubmodule (negativeParameter - t) := by
  have hsection : backwardSection (t : ℂ) φ = forwardSection ((-(1 / 3 : ℝ) - t : ℝ) : ℂ) φ := by
    funext g
    unfold backwardSection forwardSection
    congr 2
    push_cast
    ring
  rw [hsection]
  convert forwardSection_real_mem (-(1 / 3 : ℝ) - t) φ using 1
  unfold positiveParameter negativeParameter
  ring

private theorem rowRatio_su2 (k : ComplexSU2) : rowRatio (complexSU2Embedding k) = 1 := by
  have hd : Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  have hu := (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1
  have hrow := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ => m 1 1)
    (Matrix.mem_unitaryGroup_iff.mp hu)
  have hn : ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
      ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 = 1 := by
    have hr := congrArg Complex.re hrow
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow] using hr
  unfold rowRatio bottomRowNormSq complexSU2Embedding
  simp [hn, hd]

noncomputable def zeroForward (φ : CompactPicture) : PrincipalSeries positiveParameter :=
  ⟨forwardSection 0 φ, by simpa using forwardSection_real_mem 0 φ⟩

noncomputable def zeroBackward (φ : CompactPicture) : PrincipalSeries negativeParameter :=
  ⟨backwardSection 0 φ, by simpa using backwardSection_real_mem 0 φ⟩

private theorem restriction_zeroForward (φ : CompactPicture) :
    compactRestriction positiveParameter (zeroForward φ) = compactRestrictionMap φ := by
  funext k
  change forwardSection 0 φ (complexSU2Embedding k) = φ _
  simp [forwardSection, rowRatio_su2]

private theorem restriction_zeroBackward (φ : CompactPicture) :
    compactRestriction negativeParameter (zeroBackward φ) = compactRestrictionMap φ := by
  funext k
  change backwardSection 0 φ (complexSU2Embedding k) = φ _
  simp [backwardSection, rowRatio_su2]

theorem zero_model_identifications :
    Function.Bijective zeroForward ∧ Function.Bijective zeroBackward ∧
    Continuous zeroForward ∧ Continuous zeroBackward ∧
    (∀ (φ : CompactPicture) (ℓ : ℕ),
      zeroForward φ ∈ harmonicKType positiveParameter ℓ ↔ φ ∈ compactHarmonic ℓ) ∧
    (∀ (φ : CompactPicture) (ℓ : ℕ),
      zeroBackward φ ∈ harmonicKType negativeParameter ℓ ↔ φ ∈ compactHarmonic ℓ) := by
  have hf := RepresentationTheory.KPComplexStandardIntertwinerGermProve.real_reconstruction_identification
    compactSeminorm compact_withSeminorms compact_pointwise (fun _ _ => rfl)
    positiveParameter zeroForward (by
      intro φ g
      change forwardSection 0 φ g = _
      unfold forwardSection positiveParameter
      congr 2 <;> norm_num)
  have hb := RepresentationTheory.KPComplexStandardIntertwinerGermProve.real_reconstruction_identification
    compactSeminorm compact_withSeminorms compact_pointwise (fun _ _ => rfl)
    negativeParameter zeroBackward (by
      intro φ g
      change backwardSection 0 φ g = _
      unfold backwardSection negativeParameter
      congr 2 <;> norm_num)
  refine ⟨hf.1, hb.1, hf.2, hb.2, ?_, ?_⟩
  · intro φ ℓ
    simp only [harmonicKType, compactHarmonic, Submodule.mem_comap,
      restriction_zeroForward]
  · intro φ ℓ
    simp only [harmonicKType, compactHarmonic, Submodule.mem_comap,
      restriction_zeroBackward]

def compactSpherical : CompactPicture := ⟨fun _ => 1, contDiff_const, contDiff_const⟩

noncomputable def ownedCore (t : ℝ) : Submodule ℂ (PrincipalSeries t) :=
  ⨆ ℓ : ℕ, harmonicKType t ℓ

noncomputable def thetaCore (β : ℂˣ) : Submodule ℂ (PrincipalSeries negativeParameter) :=
  KPCplxActualImage.imageSubmodule β ⊓ ownedCore negativeParameter

private theorem harmonic_image (β : ℂˣ) (ℓ : ℕ) :
    (harmonicKType positiveParameter ℓ).map (standardIntertwiner β).toLinearMap =
      harmonicKType negativeParameter ℓ := by
  apply le_antisymm
  · rintro f ⟨h, hh, rfl⟩
    exact (standardIntertwiner_harmonic_eigenvalue β ℓ h hh).1
  · intro f hf
    have hident := (harmonicKType_compact_identification positiveParameter negativeParameter ℓ).2
    have hmem : compactRestriction negativeParameter f ∈
        (harmonicKType positiveParameter ℓ).map (compactRestriction positiveParameter) := by
      rw [hident]
      exact ⟨f, hf, rfl⟩
    rcases hmem with ⟨h, hh, heq⟩
    have heigen := (standardIntertwiner_harmonic_eigenvalue β ℓ h hh).2
    have hne : (eigenvalue β ℓ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (eigenvalue_ne_zero β ℓ)
    refine ⟨(eigenvalue β ℓ : ℂ)⁻¹ • h,
      (harmonicKType positiveParameter ℓ).smul_mem _ hh, ?_⟩
    apply (harmonicKType_compact_identification negativeParameter positiveParameter ℓ).1
    change compactRestriction negativeParameter
      (standardIntertwiner β ((eigenvalue β ℓ : ℂ)⁻¹ • h)) = _
    rw [map_smul, map_smul, heigen, smul_smul, inv_mul_cancel₀ hne, one_smul, heq]

theorem actual_harishChandra_image (β : ℂˣ) :
    (ownedCore positiveParameter).map (standardIntertwiner β).toLinearMap = thetaCore β := by
  unfold ownedCore thetaCore
  rw [KPCplxActualImage.imageSubmodule_eq_top, top_inf_eq, Submodule.map_iSup]
  congr 1
  funext ℓ
  exact harmonic_image β ℓ

end DedekindZetaZeroFree.KPComplexStandardIntertwinerGerm

end
