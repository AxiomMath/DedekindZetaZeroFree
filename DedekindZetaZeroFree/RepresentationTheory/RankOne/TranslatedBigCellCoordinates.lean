module

public import DedekindZetaZeroFree.Eisenstein.Induction.UnipotentInvariance
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGLComplex.AdelicSlices

@[expose] public section

noncomputable section
open scoped NumberField Classical Matrix.Norms.Elementwise
open NumberField
set_option maxHeartbeats 1200000
namespace DedekindZetaZeroFree.KPLiteralChamber
open KPLiteralRaw
open KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem tuple_prod (a : RestrictedCover F ζ hζ)
    (ha : ∀ q, a (Sum.inr q) = 1) :
    a = ((Finset.univ : Finset (InfinitePlace F)).toList.map
      (fun w => localToRestricted F ζ hζ (Sum.inl w) (a (Sum.inl w)))).prod := by
  apply RestrictedProduct.ext
  intro v
  change a v = (RestrictedProduct.evalMonoidHom _ v) _
  rw [map_list_prod, List.map_map]
  cases v with
  | inl w =>
    simp only [Function.comp_def, localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply]
    simp only [RestrictedProduct.evalMonoidHom_apply, RestrictedProduct.coe_mulSingle_apply]
    have he : (fun x : InfinitePlace F => Pi.mulSingle (Sum.inl x) (a (Sum.inl x)) (Sum.inl w)) =
        fun x => if x = w then a (Sum.inl w) else 1 := by
      funext x
      by_cases h : x=w
      · subst x; simp
      · simp [Pi.mulSingle_apply, Sum.inl_injective.ne h, h]
    rw [he]
    rw [List.prod_map_eq_pow_single w _ (by intro x hx _; simp [hx])]
    rw [List.nodup_iff_count_le_one.mp (Finset.nodup_toList _) w |>.antisymm
      (Nat.succ_le_of_lt (List.count_pos_iff.mpr (by simp)))]
    simp
  | inr q =>
    simp [ha, localToRestricted, Function.comp_def, RestrictedProduct.coe_mulSingle_apply, Pi.mulSingle_apply]
def sectionTuple (r : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    RestrictedCover F ζ hζ :=
  ⟨fun v => match v with
    | Sum.inl w => KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
        (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom (r w))
    | Sum.inr _ => 1,
    Filter.Eventually.of_forall (by intro v; cases v <;> simp [compact])⟩
 theorem sectionTuple_insertion
    (r : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    scalarQuotient F ζ hζ (amalgamation F ζ hζ (sectionTuple F ζ hζ r)) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (r w)) := by
  rw [tuple_prod F ζ hζ (sectionTuple F ζ hζ r) (by intro q; rfl)]
  rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
  exact (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.2.2 r |>.symm
 def complexSectionHom (w : InfinitePlace F) :
    Matrix.GeneralLinearGroup (Fin 2) ℂ →* KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) where
  toFun r := KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
    (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom r)
  map_one' := by simp [KPLocalCover.sectionMap]; rfl
  map_mul' := by
    intro r s
    change KPLocalCover.CubicGL2Raw.mk _ 1 = KPLocalCover.CubicGL2Raw.mk _ _
    congr 1
    · simp
    · simp [KPLocalChartTopology.complex_sigmaTwo_eq_one]
 def diagonalUnit (x : ℂ) : ℂˣ := if h : x=0 then 1 else Units.mk0 x h
def rightMatrix (x : Fin 3 → ℂ) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  KubotaRankTwo.n ℂ (x 0) * KubotaRankTwo.d ℂ (diagonalUnit (x 1)) 1 *
    KPStandardLocalRootLifts.lowerN ℂ (x 2)
def leftMatrix (x : Fin 3 → ℂ) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  KPStandardLocalRootLifts.lowerN ℂ (x 0) * KubotaRankTwo.d ℂ (diagonalUnit (x 1)) 1 *
    KubotaRankTwo.n ℂ (x 2)
private theorem mapped_diagonalUnit (w : InfinitePlace F) (x : ℂ) :
    Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom (diagonalUnit x) =
      (if h : x=0 then (1 : (w.Completion)ˣ) else Units.mk0
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm x)
        (by
          intro hx
          apply h
          simpa using congrArg (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w)) hx)) := by
  by_cases hx : x=0
  · simp [diagonalUnit, hx]
  · simp only [diagonalUnit, hx, ↓reduceDIte]
    apply Units.ext; rfl
theorem sectionTuple_right (x : KPGlobalResidualConstruction.ArchCoordinates F) :
    scalarQuotient F ζ hζ (amalgamation F ζ hζ
      (sectionTuple F ζ hζ (fun w => rightMatrix (x w)))) =
      KPGlobalResidualConstruction.archChart F ζ hζ x := by
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inr q => rfl
  | inl w =>
    change complexSectionHom F ζ hζ w (rightMatrix (x w)) = _
    simp only [rightMatrix, map_mul]
    congr 1
    · congr 1
      · simp [complexSectionHom, KPStandardLocalRootLifts.N, KPLocalCover.sectionMap]
        apply Matrix.GeneralLinearGroup.ext; intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map]
      · simp [complexSectionHom, KPStandardLocalRootLifts.A, KPLocalCover.sectionMap]
        rw [← mapped_diagonalUnit F ζ hζ w (x w 1)]
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map]
    · simp [complexSectionHom, KPStandardLocalRootLifts.LowerN, KPLocalCover.sectionMap]
      apply Matrix.GeneralLinearGroup.ext; intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map, KPStandardLocalRootLifts.lowerN]
theorem sectionTuple_left (x : KPGlobalTorusBorelTwistCompatibility.GroupArch F) :
    scalarQuotient F ζ hζ (amalgamation F ζ hζ
      (sectionTuple F ζ hζ (fun w => leftMatrix (x w)))) =
      KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ x := by
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inr q => rfl
  | inl w =>
    change complexSectionHom F ζ hζ w (leftMatrix (x w)) = _
    simp only [leftMatrix, map_mul]
    congr 1
    · congr 1
      · simp [complexSectionHom, KPStandardLocalRootLifts.LowerN, KPLocalCover.sectionMap]
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map, KPStandardLocalRootLifts.lowerN]
      · simp [complexSectionHom, KPStandardLocalRootLifts.A, KPLocalCover.sectionMap]
        rw [← mapped_diagonalUnit F ζ hζ w (x w 1)]
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map]
    · simp [complexSectionHom, KPStandardLocalRootLifts.N, KPLocalCover.sectionMap]
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map]
theorem right_insertion (x : KPGlobalResidualConstruction.ArchCoordinates F) :
    KPGlobalResidualConstruction.archChart F ζ hζ x =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (rightMatrix (x w))) := by
  rw [← sectionTuple_right, sectionTuple_insertion]
theorem left_insertion (x : KPGlobalTorusBorelTwistCompatibility.GroupArch F) :
    KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ x =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (leftMatrix (x w))) := by
  rw [← sectionTuple_left, sectionTuple_insertion]
theorem rightMatrix_val (x : Fin 3 → ℂ) (hx : x 1 ≠ 0) :
    (rightMatrix x).val = !![x 1 + x 0*x 2, x 0; x 2, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rightMatrix, diagonalUnit, hx,
    KPStandardLocalRootLifts.lowerN, Matrix.mul_apply, Fin.sum_univ_two]
theorem leftMatrix_val (x : Fin 3 → ℂ) (hx : x 1 ≠ 0) :
    (leftMatrix x).val = !![x 1, x 1*x 2; x 0*x 1, 1+x 0*x 1*x 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leftMatrix, diagonalUnit, hx,
    KPStandardLocalRootLifts.lowerN, Matrix.mul_apply, Fin.sum_univ_two]
  ring
def rightCoordinates (M : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℂ :=
  ![M 0 1 / M 1 1, M.det / (M 1 1)^2, M 1 0 / M 1 1]
 theorem rightCoordinates_nonzero (M : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hM : M.val 1 1 ≠ 0) : rightCoordinates M.val 1 ≠ 0 := by
  simp only [rightCoordinates, Matrix.cons_val_one, Matrix.cons_val_zero]
  exact div_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero M) (pow_ne_zero _ hM)
theorem rightCoordinates_reconstruct (M : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hM : M.val 1 1 ≠ 0) :
    Matrix.ProjGenLinGroup.mk (rightMatrix (rightCoordinates M.val)) = Matrix.ProjGenLinGroup.mk M := by
  have he : rightMatrix (rightCoordinates M.val) =
      M * Matrix.GeneralLinearGroup.scalar (Fin 2) ((Units.mk0 (M.val 1 1) hM)⁻¹) := by
    apply Matrix.GeneralLinearGroup.ext
    rw [rightMatrix_val _ (rightCoordinates_nonzero M hM)]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Units.val_inv_eq_inv_val, Units.val_mk0]
    all_goals simp [rightCoordinates, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.scalar]
    all_goals field_simp <;> ring
  rw [he, map_mul, Matrix.ProjGenLinGroup.mk_scalar, mul_one]
 def transitionMatrix (a : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (z₀ z : KPGlobalTorusBorelTwistCompatibility.GroupArch F)
    (w : InfinitePlace F) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  (a w)⁻¹ * (leftMatrix (z₀ w))⁻¹ * leftMatrix (z w) * a w
private theorem transitionMatrix_base (a : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (z₀ : KPGlobalTorusBorelTwistCompatibility.GroupArch F) (w : InfinitePlace F) :
    transitionMatrix F a z₀ z₀ w = 1 := by unfold transitionMatrix; group
private theorem transitionMatrix_smooth
    (a : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (z₀ : KPGlobalTorusBorelTwistCompatibility.GroupArch F) (w : InfinitePlace F) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (transitionMatrix F a z₀ z w).val)
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  let P := fun z : KPGlobalTorusBorelTwistCompatibility.GroupArch F =>
    (a w)⁻¹.val * (leftMatrix (z₀ w))⁻¹.val *
      (!![z w 1, z w 1*z w 2; z w 0*z w 1, 1+z w 0*z w 1*z w 2]) * (a w).val
  have hp : ContDiff ℝ (⊤ : ℕ∞) P := by
    unfold P
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    fun_prop
  exact hp.contDiffOn.congr (by
    intro z hz
    simp only [transitionMatrix, Units.val_mul, leftMatrix_val _ (hz w)]
    rfl)
private theorem geometric_coordinates
    (a : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (z₀ : KPGlobalTorusBorelTwistCompatibility.GroupArch F)
    (hz₀ : z₀ ∈ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :
    ∃ (O : Set (KPGlobalTorusBorelTwistCompatibility.GroupArch F))
      (q : KPGlobalTorusBorelTwistCompatibility.GroupArch F → KPGlobalResidualConstruction.ArchCoordinates F),
      IsOpen O ∧ z₀ ∈ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) q O ∧
      Set.MapsTo q O (KPGlobalResidualConstruction.archDomain F) ∧
      ∀ z ∈ O, ∀ w, Matrix.ProjGenLinGroup.mk (rightMatrix (q z w)) =
        Matrix.ProjGenLinGroup.mk (transitionMatrix F a z₀ z w) := by
  let D := KPGlobalTorusBorelTwistCompatibility.groupArchDomain F
  let m := transitionMatrix F a z₀
  let O := D ∩ {z | ∀ w, (m z w).val 1 1 ≠ 0}
  let q := fun z w => rightCoordinates (m z w).val
  have hD : IsOpen D := KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F
  have hm (w : InfinitePlace F) : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (m z w).val) D :=
    transitionMatrix_smooth F a z₀ w
  have he (w : InfinitePlace F) (i j : Fin 2) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (m z w).val i j) D :=
    (contDiffOn_pi.mp (contDiffOn_pi.mp (hm w) i)) j
  have hO : IsOpen O := by
    have ho : IsOpen (⋂ w, D ∩ {z | (m z w).val 1 1 ≠ 0}) := by
      apply isOpen_iInter_of_finite
      intro w
      exact (he w 1 1).continuousOn.isOpen_inter_preimage hD
        (isOpen_ne_fun continuous_id continuous_const)
    convert ho using 1
    ext z
    simp only [O, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hz w; exact ⟨hz.1, hz.2 w⟩
    · intro hz; exact ⟨(hz (Classical.choice inferInstance)).1, fun w => (hz w).2⟩
  refine ⟨O, q, hO, ?_, ?_, ?_, ?_⟩
  · refine ⟨hz₀, ?_⟩
    intro w
    simp [m, transitionMatrix_base]
  · apply contDiffOn_pi.mpr; intro w
    apply contDiffOn_pi.mpr; intro i
    have hn : ∀ z ∈ O, (m z w).val 1 1 ≠ 0 := fun z hz => hz.2 w
    have hentry (i j : Fin 2) := (he w i j).mono (show O ⊆ D from fun _ hz => hz.1)
    have hdet : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (m z w).val.det) O := by
      simp only [Matrix.det_fin_two]
      exact ((hentry 0 0).mul (hentry 1 1)).sub ((hentry 0 1).mul (hentry 1 0))
    fin_cases i <;> simp [q, rightCoordinates]
    · simpa only [div_eq_mul_inv] using! (hentry 0 1).mul ((hentry 1 1).inv hn)
    · simpa only [div_eq_mul_inv] using! hdet.mul
        (((hentry 1 1).pow 2).inv (fun z hz => pow_ne_zero _ (hn z hz)))
    · simpa only [div_eq_mul_inv] using! (hentry 1 0).mul ((hentry 1 1).inv hn)
  · intro z hz w
    exact rightCoordinates_nonzero (m z w) (hz.2 w)
  · intro z hz w
    exact rightCoordinates_reconstruct (m z w) (hz.2 w)

theorem literal_group_chart_local_transition (g : G F ζ hζ)
    (z₀ : KPGlobalTorusBorelTwistCompatibility.GroupArch F)
    (hz₀ : z₀ ∈ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :
    ∃ (O : Set (KPGlobalTorusBorelTwistCompatibility.GroupArch F))
      (q : KPGlobalTorusBorelTwistCompatibility.GroupArch F → KPGlobalResidualConstruction.ArchCoordinates F),
      IsOpen O ∧ z₀ ∈ O ∧
      ContDiffOn ℝ (⊤ : ℕ∞) q O ∧
      Set.MapsTo q O (KPGlobalResidualConstruction.archDomain F) ∧
      ∀ z ∈ O, KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g =
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z₀ * g) *
          KPGlobalResidualConstruction.archChart F ζ hζ (q z) := by
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
  obtain ⟨O, q, hO, hzO, hq, hqD, hmat⟩ := geometric_coordinates F a z₀ hz₀
  refine ⟨O, q, hO, hzO, hq, hqD, ?_⟩
  intro z hz
  have hs := KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ
  let s : KPSmoothActualFlowData.GInfinity F →* KPLiteralRaw.G F ζ hζ :=
    { toFun := S
      map_one' := hs.1
      map_mul' := hs.2.1 }
  let l : KPGlobalTorusBorelTwistCompatibility.GroupArch F → KPSmoothActualFlowData.GInfinity F :=
    fun z w => Matrix.ProjGenLinGroup.mk (leftMatrix (z w))
  have hqS : KPGlobalResidualConstruction.archChart F ζ hζ (q z) =
      s (b⁻¹ * (l z₀)⁻¹ * l z * b) := by
    rw [right_insertion]
    apply congrArg S
    funext w
    rw [hmat z hz w]
    simp only [transitionMatrix, map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, l]
    rw [congrFun hb w]
  have hc : Commute (s (b⁻¹ * (l z₀)⁻¹ * l z * b)) c.val := by
    have h1 (d : KPSmoothActualFlowData.GInfinity F) : e (d, 1) = s d := by
      change e (d, 1) = PGLComplex.AdelicSlices.archimedeanInsertion F ζ hζ d
      simpa only [Subgroup.coe_one, mul_one] using he d 1
    have h2 : e (1, c) = c.val := by
      rw [he]
      change S 1 * c.val = c.val
      change s 1 * c.val = c.val
      rw [map_one, one_mul]
    rw [← h1, ← h2]
    exact (show Commute (b⁻¹ * (l z₀)⁻¹ * l z * b, (1 : PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ))
      (1, c) by unfold Commute SemiconjBy; simp).map e.toMonoidHom
  rw [hg, left_insertion, left_insertion, hqS]
  change s (l z) * (s b * c.val) = (s (l z₀) * (s b * c.val)) * s _
  have hcomm : c.val * s (b⁻¹ * (l z₀)⁻¹ * l z * b) =
      s (b⁻¹ * (l z₀)⁻¹ * l z * b) * c.val := hc.eq.symm
  calc
    _ = (s (l z₀) * s b * s (b⁻¹ * (l z₀)⁻¹ * l z * b)) * c.val := by
      rw [← mul_assoc (s (l z)), ← map_mul, ← map_mul, ← map_mul]
      apply congrArg (fun d => s d * c.val)
      group
    _ = _ := by rw [mul_assoc (s (l z₀) * s b), ← hcomm]; group

end DedekindZetaZeroFree.KPLiteralChamber

end
