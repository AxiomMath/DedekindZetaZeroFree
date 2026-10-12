module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.ComplexParameterMajorants

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace DedekindZetaZeroFree.RepresentationTheory.KPComplexStandardIntertwinerGermProve
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open DedekindZetaZeroFree.KPComplexIntertwinerParameterMajorant MeasureTheory Set
open scoped ContDiff Matrix.Norms.Elementwise

private lemma line_open (x : ℂ) :
    bottomRowLine (weyl * upperUnipotent x) = projectiveOpen x := by
  unfold bottomRowLine weyl upperUnipotent
  simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private lemma line_infinity (u : ℂ) :
    bottomRowLine (lowerUnipotent u) = projectiveInfinity u := by
  by_cases hu : u = 0
  · subst u
    simp [bottomRowLine, lowerUnipotent]
  · have hlo : (lowerUnipotent u : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; u, 1] := rfl
    unfold bottomRowLine
    rw [hlo]
    simp [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one, hu]
    exact (projective_chart_transition u hu).symm

private lemma ratio_pos (g : ComplexGL2) : 0 < rowRatio g := by
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

private lemma exp_eq_sphere (t : ℝ) (g : ComplexGL2) :
    Complex.exp ((1 + 2 * (t : ℂ)) * (Real.log (rowRatio g) : ℂ)) =
      sphericalSection t g := by
  change _ = ((rowRatio g ^ (1 + 2 * t) : ℝ) : ℂ)
  rw [Real.rpow_def_of_pos (ratio_pos g), Complex.ofReal_exp]
  congr 1
  push_cast
  ring

 lemma sphere_ne (t : ℝ) (g : ComplexGL2) : sphericalSection t g ≠ 0 := by
  rw [← exp_eq_sphere]
  exact Complex.exp_ne_zero _

private lemma open_injective : Function.Injective projectiveOpen := by
  intro x y h
  change Projectivization.mk ℂ ![1, x] (by intro he; simpa using congrFun he 0) =
    Projectivization.mk ℂ ![1, y] (by intro he; simpa using congrFun he 0) at h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp at h0 h1
  simpa [h0] using h1.symm

private lemma infinity_not_open (x : ℂ) : projectiveInfinity 0 ≠ projectiveOpen x := by
  intro h
  change Projectivization.mk ℂ ![0, 1] (by intro he; simpa using congrFun he 1) =
    Projectivization.mk ℂ ![1, x] (by intro he; simpa using congrFun he 0) at h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp at h0 h1
  simp [h0] at h1

 noncomputable def glue (F H : ℂ → ℂ) (p : ComplexProjectiveLine) : ℂ :=
  by
    classical
    exact if h : ∃ x, p = projectiveOpen x then F (Classical.choose h) else H 0

 lemma glue_open (F H : ℂ → ℂ) (x : ℂ) : glue F H (projectiveOpen x) = F x := by
  classical
  unfold glue
  rw [dif_pos ⟨x, rfl⟩]
  congr 1
  exact open_injective (Classical.choose_spec (show ∃ y, projectiveOpen x = projectiveOpen y from ⟨x, rfl⟩)).symm

 lemma glue_infinity (F H : ℂ → ℂ)
    (hFH : ∀ u, u ≠ 0 → H u = F u⁻¹) (u : ℂ) :
    glue F H (projectiveInfinity u) = H u := by
  classical
  by_cases hu : u = 0
  · subst u
    unfold glue
    rw [dif_neg]
    rintro ⟨x, hx⟩
    exact infinity_not_open x hx
  · rw [projective_chart_transition u hu, glue_open, hFH u hu]

 lemma quotient_transition (t : ℝ) (f : PrincipalSeries t) (u : ℂ) (hu : u ≠ 0) :
    infinityCoordinate f u / infinityCoordinate (sphericalSection t) u =
      openCoordinate f u⁻¹ / openCoordinate (sphericalSection t) u⁻¹ := by
  rw [coordinate_transition t f u hu, coordinate_transition t (sphericalSection t) u hu]
  apply mul_div_mul_left
  unfold transitionWeight
  exact_mod_cast (Real.rpow_pos_of_pos (norm_pos_iff.mpr hu) _).ne'

 noncomputable def inversePicture (t : ℝ) (f : PrincipalSeries t) : CompactPicture where
  toFun := glue (fun x => openCoordinate f x / openCoordinate (sphericalSection t) x)
    (fun u => infinityCoordinate f u / infinityCoordinate (sphericalSection t) u)
  open_smooth := by
    have he : glue (fun x => openCoordinate f x / openCoordinate (sphericalSection t) x)
        (fun u => infinityCoordinate f u / infinityCoordinate (sphericalSection t) u) ∘
        projectiveOpen = fun x => openCoordinate f x / openCoordinate (sphericalSection t) x := by
      funext x
      exact glue_open _ _ x
    rw [he]
    simpa only [div_eq_mul_inv] using! f.property.2.1.mul
      ((sphericalSection t).property.2.1.inv (fun x => sphere_ne t (weyl * upperUnipotent x)))
  infinity_smooth := by
    have he : glue (fun x => openCoordinate f x / openCoordinate (sphericalSection t) x)
        (fun u => infinityCoordinate f u / infinityCoordinate (sphericalSection t) u) ∘
        projectiveInfinity = fun u => infinityCoordinate f u / infinityCoordinate (sphericalSection t) u := by
      funext u
      exact glue_infinity _ _ (quotient_transition t f) u
    rw [he]
    simpa only [div_eq_mul_inv] using! f.property.2.2.mul
      ((sphericalSection t).property.2.2.inv (fun u => sphere_ne t (lowerUnipotent u)))

private lemma multiplier_bound (n : ℕ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (φ : CompactPicture) (chart : ℂ → ComplexProjectiveLine),
      (chart = projectiveOpen ∨ chart = projectiveInfinity) →
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        ‖iteratedFDeriv ℝ n (fun x => w x * φ (chart x)) z‖ ≤ C * sourceSeminorm n φ := by
  classical
  let B (i : ℕ) : ℝ := max 0 (sSup ((fun z : ℂ => ‖iteratedFDeriv ℝ i w z‖) ''
    Metric.closedBall (0 : ℂ) 1))
  have hb (i : ℕ) : BddAbove ((fun z : ℂ => ‖iteratedFDeriv ℝ i w z‖) ''
      Metric.closedBall (0 : ℂ) 1) :=
    (isCompact_closedBall (0 : ℂ) 1).bddAbove_image
      (hw.continuous_iteratedFDeriv (by simp)).norm.continuousOn
  have hB (i : ℕ) : 0 ≤ B i := le_max_left _ _
  have hbound (i : ℕ) (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
      ‖iteratedFDeriv ℝ i w z‖ ≤ B i :=
    (le_csSup (hb i) ⟨z, hz, rfl⟩).trans (le_max_right _ _)
  refine ⟨∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * B i, by positivity, ?_⟩
  intro φ chart hchart z hz
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ chart) := by
    rcases hchart with rfl | rfl
    · exact φ.open_smooth
    · exact φ.infinity_smooth
  have hsource (i : ℕ) : ‖iteratedFDeriv ℝ (n-i) (φ ∘ chart) z‖ ≤ sourceSeminorm n φ := by
    rcases hchart with rfl | rfl
    · exact norm_iteratedFDeriv_open_le_sourceSeminorm n (n-i) (Nat.sub_le _ _) φ z hz
    · exact norm_iteratedFDeriv_infinity_le_sourceSeminorm n (n-i) (Nat.sub_le _ _) φ z hz
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i w z‖ * ‖iteratedFDeriv ℝ (n-i) (φ ∘ chart) z‖ := by
      exact norm_iteratedFDeriv_mul_le hw hsmooth z (by simp)
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * B i * sourceSeminorm n φ := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hbound i z hz) (by positivity)
      · exact hsource i
      · positivity
      · positivity
    _ = _ := by rw [Finset.sum_mul]

theorem real_reconstruction_identification
    [AddCommGroup CompactPicture] [Module ℂ CompactPicture] [TopologicalSpace CompactPicture]
    (p : ℕ → Seminorm ℂ CompactPicture) (hp : WithSeminorms p)
    (hpoint : (∀ (φ ψ : CompactPicture) z, (φ + ψ) z = φ z + ψ z) ∧
      (∀ (c : ℂ) (φ : CompactPicture) z, (c • φ) z = c * φ z))
    (hseminorm : ∀ j φ, p j φ = sourceSeminorm j φ)
    (t : ℝ) (R : CompactPicture → PrincipalSeries t)
    (hR : ∀ φ g, R φ g =
      Complex.exp ((1 + 2 * (t : ℂ)) * (Real.log (rowRatio g) : ℂ)) * φ (bottomRowLine g)) :
    Function.Bijective R ∧ Continuous R := by
  classical
  have hformula (φ : CompactPicture) (g : ComplexGL2) :
      R φ g = sphericalSection t g * φ (bottomRowLine g) := by
    rw [hR, exp_eq_sphere]
  have hopen (φ : CompactPicture) : openCoordinate (R φ) =
      fun x => openCoordinate (sphericalSection t) x * φ (projectiveOpen x) := by
    funext x
    simp only [openCoordinate, hformula, line_open]
  have hinf (φ : CompactPicture) : infinityCoordinate (R φ) =
      fun u => infinityCoordinate (sphericalSection t) u * φ (projectiveInfinity u) := by
    funext u
    simp only [infinityCoordinate, hformula, line_infinity]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro φ ψ he
    have hvalues : ∀ p, φ p = ψ p := by
      intro p
      rcases projective_chart_cover p with ⟨x, rfl⟩ | ⟨u, rfl⟩
      · have h := congrArg (fun f : PrincipalSeries t => openCoordinate f x) he
        rw [hopen, hopen] at h
        exact mul_left_cancel₀ (sphere_ne t (weyl * upperUnipotent x)) h
      · have h := congrArg (fun f : PrincipalSeries t => infinityCoordinate f u) he
        rw [hinf, hinf] at h
        exact mul_left_cancel₀ (sphere_ne t (lowerUnipotent u)) h
    cases φ
    cases ψ
    congr 1
    funext p
    exact hvalues p
  · intro f
    refine ⟨inversePicture t f, openCoordinate_injective t ?_⟩
    change openCoordinate (R (inversePicture t f)) = openCoordinate f
    rw [hopen]
    funext x
    change openCoordinate (sphericalSection t) x *
      glue (fun x => openCoordinate f x / openCoordinate (sphericalSection t) x)
        (fun u => infinityCoordinate f u / infinityCoordinate (sphericalSection t) u)
        (projectiveOpen x) = openCoordinate f x
    rw [glue_open]
    exact mul_div_cancel₀ _ (sphere_ne t (weyl * upperUnipotent x))
  · let L : CompactPicture →ₗ[ℂ] PrincipalSeries t :=
      { toFun := R
        map_add' := by
          intro φ ψ
          apply Subtype.ext
          funext g
          change R (φ + ψ) g = R φ g + R ψ g
          rw [hformula, hformula, hformula, hpoint.1]
          ring
        map_smul' := by
          intro c φ
          apply Subtype.ext
          funext g
          change R (c • φ) g = c * R φ g
          rw [hformula, hformula, hpoint.2]
          ring }
    apply WithSeminorms.continuous_of_isBounded hp (show WithSeminorms (chartSeminorm t) from ⟨rfl⟩) L
    intro n
    obtain ⟨C, hC, hc⟩ := multiplier_bound n (openCoordinate (sphericalSection t))
      (sphericalSection t).property.2.1
    obtain ⟨D, hD, hd⟩ := multiplier_bound n (infinityCoordinate (sphericalSection t))
      (sphericalSection t).property.2.2
    refine ⟨{n}, ⟨max C D, le_max_of_le_left hC⟩, ?_⟩
    intro φ
    change chartSeminormValue t n (R φ) ≤ _
    simp only [Finset.sup_singleton, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, hseminorm]
    unfold chartSeminormValue
    apply max_le
    · apply csSup_le
      · exact ⟨‖iteratedFDeriv ℝ n (openCoordinate (R φ)) 0‖, 0,
          Metric.mem_closedBall_self (by norm_num), rfl⟩
      · rintro r ⟨z, hz, rfl⟩
        rw [hopen]
        exact (hc φ projectiveOpen (Or.inl rfl) z hz).trans
          (mul_le_mul_of_nonneg_right (le_max_left C D) (sourceSeminorm_nonneg n φ))
    · apply csSup_le
      · exact ⟨‖iteratedFDeriv ℝ n (infinityCoordinate (R φ)) 0‖, 0,
          Metric.mem_closedBall_self (by norm_num), rfl⟩
      · rintro r ⟨u, hu, rfl⟩
        rw [hinf]
        exact (hd φ projectiveInfinity (Or.inr rfl) u hu).trans
          (mul_le_mul_of_nonneg_right (le_max_right C D) (sourceSeminorm_nonneg n φ))
end DedekindZetaZeroFree.RepresentationTheory.KPComplexStandardIntertwinerGermProve
