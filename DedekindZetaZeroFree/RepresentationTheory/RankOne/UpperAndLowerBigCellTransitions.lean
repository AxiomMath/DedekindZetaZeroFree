module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.TranslatedBigCellCoordinates

@[expose] public section

noncomputable section
open scoped NumberField Classical Matrix.Norms.Elementwise
open NumberField
namespace DedekindZetaZeroFree.KPLiteralChamber

set_option maxHeartbeats 1200000

 def leftCoordinates (M : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℂ :=
  ![M 1 0 / M 0 0, (M 0 0)^2 / M.det, M 0 1 / M 0 0]

private theorem leftCoordinates_nonzero (M : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hM : M.val 0 0 ≠ 0) : leftCoordinates M.val 1 ≠ 0 := by
  simp only [leftCoordinates, Matrix.cons_val_one, Matrix.cons_val_zero]
  exact div_ne_zero (pow_ne_zero _ hM) (Matrix.GeneralLinearGroup.det_ne_zero M)

private theorem leftCoordinates_reconstruct (M : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hM : M.val 0 0 ≠ 0) :
    Matrix.ProjGenLinGroup.mk (leftMatrix (leftCoordinates M.val)) = Matrix.ProjGenLinGroup.mk M := by
  have hdet : M.val 0 0 * M.val 1 1 - M.val 0 1 * M.val 1 0 ≠ 0 := by
    simpa [Matrix.det_fin_two] using Matrix.GeneralLinearGroup.det_ne_zero M
  have hdet' : -(M.val 1 0 * M.val 0 1) + M.val 0 0 * M.val 1 1 ≠ 0 := by
    convert hdet using 1 <;> ring
  have he : leftMatrix (leftCoordinates M.val) =
      M * Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.mk0 (M.val 0 0) hM / M.det) := by
    apply Matrix.GeneralLinearGroup.ext
    rw [leftMatrix_val _ (leftCoordinates_nonzero M hM)]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Units.val_div_eq_div_val, Units.val_mk0]
    all_goals simp [leftCoordinates, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.scalar, Matrix.GeneralLinearGroup.val_det_apply]
    all_goals field_simp [hM, hdet, hdet'] <;> ring
    field_simp [hdet']
    ring
  rw [he, map_mul, Matrix.ProjGenLinGroup.mk_scalar, mul_one]

 def mirroredMatrix {F : Type} [Field F] [NumberField F]
    (a : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (x₀ x : KPGlobalResidualConstruction.ArchCoordinates F) (w : InfinitePlace F) :
    Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  a w * rightMatrix (x w) * (rightMatrix (x₀ w))⁻¹ * (a w)⁻¹

private theorem mirroredMatrix_base {F : Type} [Field F] [NumberField F]
    (a : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (x₀ : KPGlobalResidualConstruction.ArchCoordinates F) (w : InfinitePlace F) :
    mirroredMatrix a x₀ x₀ w = 1 := by
  unfold mirroredMatrix
  group

private theorem mirroredMatrix_smooth {F : Type} [Field F] [NumberField F]
    (a : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (x₀ : KPGlobalResidualConstruction.ArchCoordinates F) (w : InfinitePlace F) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (mirroredMatrix a x₀ x w).val)
      (KPGlobalResidualConstruction.archDomain F) := by
  let P := fun x : KPGlobalResidualConstruction.ArchCoordinates F =>
    (a w).val * (!![x w 1 + x w 0*x w 2, x w 0; x w 2, 1]) *
      ((rightMatrix (x₀ w))⁻¹).val * ((a w)⁻¹).val
  have hp : ContDiff ℝ (⊤ : ℕ∞) P := by
    unfold P
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    fun_prop
  exact hp.contDiffOn.congr (by
    intro x hx
    simp only [mirroredMatrix, Units.val_mul, rightMatrix_val _ (hx w)]
    rfl)

private theorem mirrored_coordinates {F : Type} [Field F] [NumberField F]
    (a : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (x₀ : KPGlobalResidualConstruction.ArchCoordinates F)
    (hx₀ : x₀ ∈ KPGlobalResidualConstruction.archDomain F) :
    ∃ (O : Set (KPGlobalResidualConstruction.ArchCoordinates F))
      (q : KPGlobalResidualConstruction.ArchCoordinates F →
        KPGlobalTorusBorelTwistCompatibility.GroupArch F),
      IsOpen O ∧ x₀ ∈ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) q O ∧
      Set.MapsTo q O (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) ∧
      ∀ x ∈ O, ∀ w, Matrix.ProjGenLinGroup.mk (leftMatrix (q x w)) =
        Matrix.ProjGenLinGroup.mk (mirroredMatrix a x₀ x w) := by
  let D := KPGlobalResidualConstruction.archDomain F
  let m := mirroredMatrix a x₀
  let O := D ∩ {x | ∀ w, (m x w).val 0 0 ≠ 0}
  let q := fun x w => leftCoordinates (m x w).val
  have hD : IsOpen D := KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F
  have hm (w : InfinitePlace F) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (m x w).val) D :=
    mirroredMatrix_smooth a x₀ w
  have he (w : InfinitePlace F) (i j : Fin 2) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (m x w).val i j) D :=
    (contDiffOn_pi.mp (contDiffOn_pi.mp (hm w) i)) j
  have hO : IsOpen O := by
    have ho : IsOpen (⋂ w, D ∩ {x | (m x w).val 0 0 ≠ 0}) := by
      apply isOpen_iInter_of_finite
      intro w
      exact (he w 0 0).continuousOn.isOpen_inter_preimage hD
        (isOpen_ne_fun continuous_id continuous_const)
    convert ho using 1
    ext x
    simp only [O, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hx w; exact ⟨hx.1, hx.2 w⟩
    · intro hx; exact ⟨(hx (Classical.choice inferInstance)).1, fun w => (hx w).2⟩
  refine ⟨O, q, hO, ?_, ?_, ?_, ?_⟩
  · refine ⟨hx₀, ?_⟩
    intro w
    simp [m, mirroredMatrix_base]
  · apply contDiffOn_pi.mpr; intro w
    apply contDiffOn_pi.mpr; intro i
    have hn : ∀ x ∈ O, (m x w).val 0 0 ≠ 0 := fun x hx => hx.2 w
    have hentry (i j : Fin 2) := (he w i j).mono (show O ⊆ D from fun _ hx => hx.1)
    have hdet : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (m x w).val.det) O := by
      simp only [Matrix.det_fin_two]
      exact ((hentry 0 0).mul (hentry 1 1)).sub ((hentry 0 1).mul (hentry 1 0))
    fin_cases i <;> simp [q, leftCoordinates]
    · simpa only [div_eq_mul_inv] using! (hentry 1 0).mul ((hentry 0 0).inv hn)
    · simpa only [div_eq_mul_inv] using! ((hentry 0 0).pow 2).mul
        (hdet.inv (fun x _ => Matrix.GeneralLinearGroup.det_ne_zero (m x w)))
    · simpa only [div_eq_mul_inv] using! (hentry 0 1).mul ((hentry 0 0).inv hn)
  · intro x hx w
    exact leftCoordinates_nonzero (m x w) (hx.2 w)
  · intro x hx w
    exact leftCoordinates_reconstruct (m x w) (hx.2 w)

theorem literal_right_to_left_chart_local_transition
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (g : KPLiteralRaw.G F ζ hζ)
    (x₀ : KPGlobalResidualConstruction.ArchCoordinates F)
    (hx₀ : x₀ ∈ KPGlobalResidualConstruction.archDomain F) :
    ∃ (O : Set (KPGlobalResidualConstruction.ArchCoordinates F))
      (q : KPGlobalResidualConstruction.ArchCoordinates F →
        KPGlobalTorusBorelTwistCompatibility.GroupArch F),
      IsOpen O ∧ x₀ ∈ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) q O ∧
      Set.MapsTo q O (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) ∧
      ∀ x ∈ O, g * KPGlobalResidualConstruction.archChart F ζ hζ x =
        KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ (q x) *
          (g * KPGlobalResidualConstruction.archChart F ζ hζ x₀) := by
  let S := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
  obtain ⟨e, he, _⟩ := PGLComplex.AdelicSlices.actual_product_splitting F ζ hζ
  let b := (e.symm g).1
  let c := (e.symm g).2
  have hg : g = S b * c.val := by
    change g = PGLComplex.AdelicSlices.archimedeanInsertion F ζ hζ b * c.val
    exact (e.apply_symm_apply g).symm.trans (he b c)
  let a : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ := fun w => (b w).out
  have hb : (fun w => Matrix.ProjGenLinGroup.mk (a w)) = b := by
    funext w
    exact Quotient.out_eq (b w)
  obtain ⟨O, q, hO, hxO, hq, hqD, hmat⟩ := mirrored_coordinates a x₀ hx₀
  refine ⟨O, q, hO, hxO, hq, hqD, ?_⟩
  intro x hx
  have hs := KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ
  let s : KPSmoothActualFlowData.GInfinity F →* KPLiteralRaw.G F ζ hζ :=
    { toFun := S, map_one' := hs.1, map_mul' := hs.2.1 }
  let r : KPGlobalResidualConstruction.ArchCoordinates F → KPSmoothActualFlowData.GInfinity F :=
    fun x w => Matrix.ProjGenLinGroup.mk (rightMatrix (x w))
  have hqS : KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ (q x) =
      s (b * r x * (r x₀)⁻¹ * b⁻¹) := by
    rw [left_insertion]
    apply congrArg S
    funext w
    rw [hmat x hx w]
    simp only [mirroredMatrix, map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, r]
    rw [congrFun hb w]
  have hc (d : KPSmoothActualFlowData.GInfinity F) : Commute (s d) c.val := by
    have h1 : e (d, 1) = s d := by
      change e (d, 1) = PGLComplex.AdelicSlices.archimedeanInsertion F ζ hζ d
      simpa only [Subgroup.coe_one, mul_one] using he d 1
    have h2 : e (1, c) = c.val := by
      rw [he]
      change s 1 * c.val = c.val
      rw [map_one, one_mul]
    rw [← h1, ← h2]
    exact (show Commute (d, (1 : PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ)) (1, c)
      by unfold Commute SemiconjBy; simp).map e.toMonoidHom
  rw [hg, right_insertion, right_insertion, hqS]
  change (s b * c.val) * s (r x) = s _ * ((s b * c.val) * s (r x₀))
  rw [mul_assoc (s b), (hc (r x)).eq.symm,
    mul_assoc (s b), (hc (r x₀)).eq.symm]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, ← map_mul]
  apply congrArg (fun d => s d * c.val)
  group

end DedekindZetaZeroFree.KPLiteralChamber

end
