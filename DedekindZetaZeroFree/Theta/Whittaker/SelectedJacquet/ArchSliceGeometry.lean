module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.TranslatedBigCellCoordinates

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal
open KPLiteralChamber
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming sectionTuple_insertion → sectionTuple_insertion

 def diagonalUnit (x : ℂ) : ℂˣ := if h : x = 0 then 1 else Units.mk0 x h

private theorem mapped_diagonalUnit
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : InfinitePlace F) (x : ℂ) :
    Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom (diagonalUnit x) =
      (if h : x = 0 then (1 : (w.Completion)ˣ) else Units.mk0
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm x)
        (by
          intro hx
          apply h
          simpa using congrArg (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w)) hx)) := by
  by_cases hx : x = 0
  · simp [diagonalUnit, hx]
  · simp only [diagonalUnit, hx, ↓reduceDIte]
    apply Units.ext
    rfl

 def lowerCoordinates
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (u : ℂ) :
    KPGlobalTorusBorelTwistCompatibility.GroupArch F :=
  fun v => ![if v = w then u else 0, 1, 0]

 theorem lowerCoordinates_smooth
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    ContDiff ℝ (⊤ : ℕ∞) (lowerCoordinates F w) := by
  apply contDiff_pi.mpr
  intro v
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [lowerCoordinates] <;> (try split_ifs) <;> fun_prop

 theorem lowerCoordinates_insertion
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : InfinitePlace F) (u : ℂ) :
    KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ (lowerCoordinates F w u) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update (fun _ => 1) w
          (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.lowerUnipotent u))) := by
  rw [KPLiteralChamber.left_insertion]
  congr 1
  funext v
  by_cases hv : v = w
  · subst v
    simp only [Function.update_self]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    rw [KPLiteralChamber.leftMatrix_val _ (by simp [lowerCoordinates])]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerCoordinates, KPCplxCharacterHaar.lowerUnipotent]
  · simp only [Function.update_of_ne hv]
    rw [← map_one Matrix.ProjGenLinGroup.mk]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    rw [KPLiteralChamber.leftMatrix_val _ (by simp [lowerCoordinates])]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [lowerCoordinates, hv]

 theorem update_left_mul
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    (a : KPSmoothActualFlowData.GInfinity F)
    (g h : Matrix.ProjGenLinGroup (Fin 2) ℂ) :
    Function.update (fun _ => 1) w g * Function.update a w h =
      Function.update a w (g * h) := by
  funext v
  by_cases hv : v = w <;> simp [hv]

 theorem weyl_upper (u : ℂ) :
    KPCplxCharacterHaar.weyl * KPCplxCharacterHaar.upperUnipotent u =
      KPCplxCharacterHaar.lowerUnipotent u * KPCplxCharacterHaar.weyl := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [KPCplxCharacterHaar.weyl,
    KPCplxCharacterHaar.upperUnipotent, KPCplxCharacterHaar.lowerUnipotent,
    Matrix.mul_apply, Fin.sum_univ_two]

 def singleDiagonal (F : Type) [Field F] [NumberField F]
    (w : InfinitePlace F) (z : ℂˣ) : KPGlobalTorusFunctionData.TorusArch F :=
  Function.update (fun _ => 1) w z

 theorem diagonal_insertion
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (z : KPGlobalTorusFunctionData.TorusArch F) :
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z).val =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ (diagonalUnit (z w)) 1)) := by
  rw [← sectionTuple_insertion]
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ _) = _
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inr q => rfl
  | inl w =>
    change KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w) _ = _
    unfold KPStandardLocalRootLifts.A
    rw [← mapped_diagonalUnit F ζ hζ]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map]

 def singleAdele (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (w : InfinitePlace F) (u : ℂ) :
    KPGlobalTorusFunctionData.Adeles F :=
  (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)).symm u), 0)

 theorem unipotent_insertion
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : InfinitePlace F) (u : ℂ) :
    KPGlobalTorusFunctionData.N F ζ hζ (singleAdele F ζ hζ w u) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update (fun _ => 1) w
          (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.upperUnipotent u))) := by
  let r : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 :=
    fun v => KPCplxCharacterHaar.upperUnipotent (if v = w then u else 0)
  have he : (fun v => Matrix.ProjGenLinGroup.mk (r v)) =
      Function.update (fun _ => 1) w (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.upperUnipotent u)) := by
    funext v
    by_cases hv : v = w
    · subst v
      simp [r]
    · have hzero : KPCplxCharacterHaar.upperUnipotent 0 = 1 := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [KPCplxCharacterHaar.upperUnipotent]
      simp [r, hv, hzero]
  rw [← he, ← sectionTuple_insertion]
  unfold KPGlobalTorusFunctionData.N
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inr q =>
    change KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) 0 = 1
    exact KPStandardLocalRootLifts.N_zero F ζ hζ (Sum.inr q)
  | inl v =>
    change KPStandardLocalRootLifts.N F ζ hζ (Sum.inl v) _ = _
    unfold KPStandardLocalRootLifts.N
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    by_cases hv : v = w
    · subst v
      fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map,
        singleAdele, KPAdelicCoverRestrictedProduct.adeleEval, r,
        KPCplxCharacterHaar.upperUnipotent, Pi.single_apply, RingHom.comp_apply, RingHom.fst, Pi.evalRingHom_apply]
      change Pi.single w _ w = _
      simp
    · fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map,
        singleAdele, KPAdelicCoverRestrictedProduct.adeleEval, r, hv,
        KPCplxCharacterHaar.upperUnipotent, Pi.single_apply, RingHom.comp_apply, RingHom.fst, Pi.evalRingHom_apply]
      change Pi.single w _ v = 0
      simp [Pi.single_apply, hv]

 theorem upper_projective (a d : ℂˣ) (b : ℂ) :
    Matrix.ProjGenLinGroup.mk (KPCplxPrincipalSeriesCharts.upperTriangular a d b) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ (a / d) 1 *
        KPCplxCharacterHaar.upperUnipotent (b / a)) := by
  apply (Matrix.ProjGenLinGroup.mk_eq_mk_iff).mpr
  refine ⟨Units.mk0 ((d : ℂ)⁻¹) (inv_ne_zero d.ne_zero), ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [KPCplxPrincipalSeriesCharts.upperTriangular, KPCplxCharacterHaar.upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]
  field_simp

 theorem compact_insertion
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : InfinitePlace F) (h : KPCplxCharacterHaar.ComplexSU2) :
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (Function.update (fun _ => 1) w
        (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding h))) =
      KPGlobalResidualConstruction.complexCompactLift F ζ hζ w h := by
  let r : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 :=
    Function.update (fun _ => 1) w (KPCplxCharacterHaar.complexSU2Embedding h)
  have he : (fun v => Matrix.ProjGenLinGroup.mk (r v)) =
      Function.update (fun _ => 1) w (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding h)) := by
    funext v
    by_cases hv : v = w <;> simp [r, hv]
  rw [← he, (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.2.2]
  rw [List.prod_map_eq_pow_single w _ (by
    intro v hv _
    simp only [r, Function.update_of_ne hv, map_one]
    change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl v) 1) = 1
    simp)]
  have hc : ((Finset.univ : Finset (InfinitePlace F)).toList.count w) = 1 := by
    exact (List.nodup_iff_count_le_one.mp (Finset.nodup_toList _) w).antisymm
      (Nat.succ_le_of_lt (List.count_pos_iff.mpr (by simp)))
  simp only [hc, pow_one, r, Function.update_self]
  rfl

 theorem insertion_commutes_finite
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) c.val := by
  let r : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 := fun w => (a w).out
  have he : (fun w => Matrix.ProjGenLinGroup.mk (r w)) = a := by
    funext w
    exact Quotient.out_eq (a w)
  rw [← he, ← sectionTuple_insertion]
  obtain ⟨x, hx, hxc⟩ := Subgroup.mem_map.mp c.property
  have hcomm : Commute (sectionTuple F ζ hζ r) x := by
    change sectionTuple F ζ hζ r * x = x * sectionTuple F ζ hζ r
    apply RestrictedProduct.ext
    intro v
    cases v with
    | inl w =>
      have hw : x (Sum.inl w) = 1 := Subgroup.mem_iInf.mp hx w
      change _ * x (Sum.inl w) = x (Sum.inl w) * _
      rw [hw, mul_one, one_mul]
    | inr q =>
      change 1 * x (Sum.inr q) = x (Sum.inr q) * 1
      simp
  exact hxc ▸ hcomm.map
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ))

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal

end
