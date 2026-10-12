module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.SixRealLieWordExpansion
public import DedekindZetaZeroFree.Eisenstein.Induction.TensorProducts.FinitePureCoreExpansion
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightWords.SupportLocality
public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.RightInvariantFieldCoordinates

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingGeometry

theorem matrixExp_single_slot
    (F : Type) [Field F] [NumberField F] (w : NumberField.InfinitePlace F)
    (i : Fin 3) (j : Fin 2) (t : ℝ) :
    KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single (w, i, j) 1) =
      Function.update (fun _ => (1 : Matrix.ProjGenLinGroup (Fin 2) ℂ)) w
        (Matrix.ProjGenLinGroup.mk
          (KPSmoothActualFlowData.matrixExponential ((t : ℂ) • slotLieMatrix i j))) := by
  funext v
  have he : KPSmoothLocalQuotientCharts.lieMatrix F (t • Pi.single (w, i, j) 1) v =
      if v = w then (t : ℂ) • slotLieMatrix i j else 0 := by
    by_cases hv : v = w
    · subst v
      ext a b
      fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
        simp [KPSmoothLocalQuotientCharts.lieMatrix, slotLieMatrix, Pi.single_apply,
          Complex.ext_iff]
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [KPSmoothLocalQuotientCharts.lieMatrix, slotLieMatrix, Pi.single_apply, hv,
          Complex.ext_iff]
  simp only [KPSmoothLocalQuotientCharts.matrixExp, he]
  by_cases hv : v = w
  · subst v
    simp [KPSmoothActualFlowData.matrixExponential]
  · simp [hv]

theorem actualRight_single_slot
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (b : Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))
    (f : KPGlobalTorusFunctionData.G F ζ hζ → ℂ) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    KPContActualSphericalRightFieldIdentification.actualRight F ζ hζ b f g =
      deriv (fun t : ℝ => f (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update (fun _ => (1 : Matrix.ProjGenLinGroup (Fin 2) ℂ))
          (KPContActualSphericalRightFieldIdentification.lieEnumeration F b).1
          (Matrix.ProjGenLinGroup.mk (KPSmoothActualFlowData.matrixExponential
            ((t : ℂ) • slotLieMatrix
              (KPContActualSphericalRightFieldIdentification.lieEnumeration F b).2.1
              (KPContActualSphericalRightFieldIdentification.lieEnumeration F b).2.2)))))) 0 := by
  unfold KPContActualSphericalRightFieldIdentification.actualRight
  congr 1
  funext t
  rw [matrixExp_single_slot]

 theorem insertion_commutes_finite
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) c.val := by
  apply DedekindZetaZeroFree.RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite
    F ζ hζ a ⟨c.val, ?_⟩
  obtain ⟨x, hx, he⟩ := c.property
  exact Subgroup.mem_map.mpr ⟨x, fun w => Subgroup.mem_iInf.mp hx w, he⟩

 theorem update_mul_single
    (F : Type) [Field F] [NumberField F] (w : NumberField.InfinitePlace F)
    (a : KPSmoothActualFlowData.GInfinity F)
    (g h : Matrix.ProjGenLinGroup (Fin 2) ℂ) :
    Function.update a w g * Function.update (fun _ => 1) w h =
      Function.update a w (g * h) := by
  funext v
  by_cases hv : v = w <;> simp [hv]

theorem slice_actualRight_native
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : NumberField.InfinitePlace F) (i : Fin 3) (j : Fin 2)
    (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (h : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter)
    (hf : ∀ g : KPCplxCharacterHaar.ComplexGL2,
      h (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val) = f g)
    (g : KPCplxCharacterHaar.ComplexGL2) :
    KPContActualSphericalRightFieldIdentification.actualRight F ζ hζ
      ((KPContActualSphericalRightFieldIdentification.lieEnumeration F).symm (w, i, j)) h
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val) =
      KPContHolomorphicKGeneration.rightLieFunction (slotLieMatrix i j) f g := by
  rw [actualRight_single_slot]
  simp only [Equiv.apply_symm_apply]
  unfold KPContHolomorphicKGeneration.rightLieFunction
  rw [← DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.CasimirHessian.rightDerivative_fderiv]
  congr 1
  funext t
  let e := Matrix.ProjGenLinGroup.mk
    (KPSmoothActualFlowData.matrixExponential ((t : ℂ) • slotLieMatrix i j))
  have hc := insertion_commutes_finite F ζ hζ
    (Function.update (fun _ => 1) w e) c
  have hm := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1
  have he : (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val) *
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (Function.update (fun _ => 1) w e) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update a w (Matrix.ProjGenLinGroup.mk
          (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • slotLieMatrix i j)))) * c.val := by
    rw [mul_assoc, hc.eq.symm, ← mul_assoc, ← hm, update_mul_single, ← map_mul]
  exact (congrArg h he).trans (hf _)

theorem slice_actualRightWord_native
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : NumberField.InfinitePlace F) (r : List (Fin 3 × Fin 2))
    (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (h : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter)
    (hf : ∀ g : KPCplxCharacterHaar.ComplexGL2,
      h (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val) = f g)
    (g : KPCplxCharacterHaar.ComplexGL2) :
    KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ
      (r.map (fun ij => (KPContActualSphericalRightFieldIdentification.lieEnumeration F).symm
        (w, ij.1, ij.2))) h
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val) =
      KPContHolomorphicKGeneration.rightWord KPCplxPrincipalSeriesCharts.positiveParameter
        (r.map (fun ij => slotLieMatrix ij.1 ij.2)) f g := by
  induction r generalizing h f g with
  | nil => exact hf g
  | cons ij r ih =>
    simp only [List.map_cons, KPContActualSphericalRightFieldIdentification.actualRightWord,
      KPContHolomorphicKGeneration.rightWord, List.foldr_cons]
    apply slice_actualRight_native F ζ hζ w ij.1 ij.2 a c
      (KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ
        (r.map (fun ij => (KPContActualSphericalRightFieldIdentification.lieEnumeration F).symm
          (w, ij.1, ij.2))) h)
      (KPContHolomorphicKGeneration.rightWord KPCplxPrincipalSeriesCharts.positiveParameter
        (r.map (fun ij => slotLieMatrix ij.1 ij.2)) f)
      (fun g => ih h f hf g) g

def nativeSlotRight (i : Fin 3) (j : Fin 2)
    (f : KPCplxCharacterHaar.ComplexGL2 → ℂ) (g : KPCplxCharacterHaar.ComplexGL2) : ℂ :=
  deriv (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential
    ((t : ℂ) • slotLieMatrix i j))) 0

def nativeSlotWord (r : List (Fin 3 × Fin 2))
    (f : KPCplxCharacterHaar.ComplexGL2 → ℂ) : KPCplxCharacterHaar.ComplexGL2 → ℂ :=
  r.foldr (fun ij => nativeSlotRight ij.1 ij.2) f

theorem actualRight_pure_tensor
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : NumberField.InfinitePlace F) (i : Fin 3) (j : Fin 2)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) (C : ℂ)
    (h : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (f : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 → ℂ)
    (hf : ∀ a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2,
      h (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun v => Matrix.ProjGenLinGroup.mk (a v)) * c.val) = C * ∏ v, f v (a v))
    (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    KPContActualSphericalRightFieldIdentification.actualRight F ζ hζ
      ((KPContActualSphericalRightFieldIdentification.lieEnumeration F).symm (w, i, j)) h
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun v => Matrix.ProjGenLinGroup.mk (a v)) * c.val) =
      C * ∏ v, (Function.update f w
        (nativeSlotRight i j (f w))) v (a v) := by
  rw [actualRight_single_slot]
  simp only [Equiv.apply_symm_apply]
  have he (t : ℝ) :
      h ((KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun v => Matrix.ProjGenLinGroup.mk (a v)) * c.val) *
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (Function.update (fun _ => 1) w (Matrix.ProjGenLinGroup.mk
            (KPSmoothActualFlowData.matrixExponential ((t : ℂ) • slotLieMatrix i j))))) =
      C * (f w (a w * KPSmoothActualFlowData.matrixExponential
        ((t : ℂ) • slotLieMatrix i j))) * ∏ v ∈ Finset.univ.erase w, f v (a v) := by
    let e := KPSmoothActualFlowData.matrixExponential ((t : ℂ) • slotLieMatrix i j)
    have hc := insertion_commutes_finite F ζ hζ
      (Function.update (fun _ => 1) w (Matrix.ProjGenLinGroup.mk e)) c
    have hm := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1
    have ha : (fun v => Matrix.ProjGenLinGroup.mk (a v)) *
        Function.update (fun _ => 1) w (Matrix.ProjGenLinGroup.mk e) =
        (fun v => Matrix.ProjGenLinGroup.mk ((Function.update a w (a w * e)) v)) := by
      funext v
      by_cases hv : v = w <;> simp [hv, map_mul]
    rw [mul_assoc, hc.eq.symm, ← mul_assoc, ← hm, ha, hf]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
    simp only [Function.update_self]
    rw [mul_assoc]
    congr 2
    apply Finset.prod_congr rfl
    intro v hv
    simp [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
  rw [show (fun t : ℝ => h _) = (fun t : ℝ =>
      C * (f w (a w * KPSmoothActualFlowData.matrixExponential
        ((t : ℂ) • slotLieMatrix i j))) * ∏ v ∈ Finset.univ.erase w, f v (a v)) from funext he]
  rw [deriv_mul_const_field, deriv_const_mul_field]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
  simp only [Function.update_self]
  rw [mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro v hv
  simp [Function.update_of_ne (Finset.ne_of_mem_erase hv)]

def wordAtSlot {F : Type} [Field F] [NumberField F]
    (v : NumberField.InfinitePlace F)
    (r : List (KPContActualSphericalRightFieldIdentification.LieIndex F)) :
    List (Fin 3 × Fin 2) :=
  r.filterMap (fun b => if b.1 = v then some b.2 else none)

theorem actualRightWord_pure_tensor
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (r : List (KPContActualSphericalRightFieldIdentification.LieIndex F))
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) (C : ℂ)
    (h : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (f : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 → ℂ)
    (hf : ∀ a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2,
      h (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun v => Matrix.ProjGenLinGroup.mk (a v)) * c.val) = C * ∏ v, f v (a v))
    (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ
      (r.map (KPContActualSphericalRightFieldIdentification.lieEnumeration F).symm) h
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun v => Matrix.ProjGenLinGroup.mk (a v)) * c.val) =
      C * ∏ v, nativeSlotWord (wordAtSlot v r) (f v) (a v) := by
  induction r generalizing h f a with
  | nil => simpa [wordAtSlot, nativeSlotWord,
      KPContActualSphericalRightFieldIdentification.actualRightWord] using hf a
  | cons b r ih =>
    simp only [List.map_cons, KPContActualSphericalRightFieldIdentification.actualRightWord]
    rw [actualRight_pure_tensor F ζ hζ b.1 b.2.1 b.2.2 c C _
      (fun v => nativeSlotWord (wordAtSlot v r) (f v)) (fun a => ih h f hf a)]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    by_cases he : v = b.1
    · subst v
      simp [wordAtSlot, nativeSlotWord]
    · simp [wordAtSlot, nativeSlotWord, he, Ne.symm he]

theorem nativeSlotWord_principal_series
    (r : List (Fin 3 × Fin 2))
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter)
    (g : KPCplxCharacterHaar.ComplexGL2) :
    nativeSlotWord r f g =
      KPContHolomorphicKGeneration.rightWord KPCplxPrincipalSeriesCharts.positiveParameter
        (r.map (fun ij => slotLieMatrix ij.1 ij.2)) f g := by
  induction r generalizing f g with
  | nil => rfl
  | cons ij r ih =>
    change nativeSlotRight ij.1 ij.2 (nativeSlotWord r f) g =
      KPContHolomorphicKGeneration.rightLieDerivative KPCplxPrincipalSeriesCharts.positiveParameter
        (slotLieMatrix ij.1 ij.2)
        (KPContHolomorphicKGeneration.rightWord KPCplxPrincipalSeriesCharts.positiveParameter
          (r.map (fun ij => slotLieMatrix ij.1 ij.2)) f) g
    unfold nativeSlotRight
    have he : nativeSlotWord r f =
        (KPContHolomorphicKGeneration.rightWord KPCplxPrincipalSeriesCharts.positiveParameter
          (r.map (fun ij => slotLieMatrix ij.1 ij.2)) f :
          KPCplxCharacterHaar.ComplexGL2 → ℂ) := funext (ih f)
    rw [he, DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.CasimirHessian.rightDerivative_fderiv]
    rfl

theorem actualRightWord_principal_tensor
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (r : List (KPContActualSphericalRightFieldIdentification.LieIndex F))
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) (C : ℂ)
    (h : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (f : NumberField.InfinitePlace F →
      KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter)
    (hf : ∀ a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2,
      h (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun v => Matrix.ProjGenLinGroup.mk (a v)) * c.val) = C * ∏ v, f v (a v))
    (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ
      (r.map (KPContActualSphericalRightFieldIdentification.lieEnumeration F).symm) h
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun v => Matrix.ProjGenLinGroup.mk (a v)) * c.val) =
      C * ∏ v, KPContHolomorphicKGeneration.rightWord
        KPCplxPrincipalSeriesCharts.positiveParameter
        ((wordAtSlot v r).map (fun ij => slotLieMatrix ij.1 ij.2)) (f v) (a v) := by
  rw [actualRightWord_pure_tensor F ζ hζ r c C h (fun v => (f v : _ → ℂ)) hf a]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  exact nativeSlotWord_principal_series _ _ _

private theorem finite_arch_projection_eq_one
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ c.val = 1 := by
  apply PGLComplex.AdelicSlicesRaw.finiteSubgroup_le_archProjection_ker F ζ hζ
  obtain ⟨x, hx, he⟩ := c.property
  exact Subgroup.mem_map.mpr ⟨x, fun w => Subgroup.mem_iInf.mp hx w, he⟩

private theorem alpha_arch_finite_formula
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    KPContFlatSourceRecipe.alpha F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) =
      (∑ w, KPContFlatLogNormSmooth.complexMatrixLogNorm (a w)) +
        KPContFlatSourceRecipe.alpha F ζ hζ c.val := by
  have hc := finite_arch_projection_eq_one F ζ hζ c
  have hα := KPContFlatLogNormSmooth.alpha_eq_arch_sum_add_finite F ζ hζ c.val
  have hαc : KPContFlatLogNormSmooth.finiteLogNorm F ζ hζ c.val =
      KPContFlatSourceRecipe.alpha F ζ hζ c.val := by
    have h1 : KPContFlatLogNormSmooth.complexProjectiveLogNorm 1 = 0 := by
      rw [← map_one (Matrix.ProjGenLinGroup.mk), KPContFlatLogNormSmooth.complexProjectiveLogNorm_mk]
      norm_num [KPContFlatLogNormSmooth.complexMatrixLogNorm]
    rw [hc] at hα
    simpa only [Pi.one_apply, h1, Finset.sum_const_zero, zero_add,
      KPContFlatSourceRecipe.alpha] using hα.symm
  unfold KPContFlatSourceRecipe.alpha
  rw [show KPSmoothActualFlowData.archimedeanInsertion F ζ hζ =
    PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ from rfl]
  rw [KPContFlatLogNormSmooth.alpha_eq_arch_sum_add_finite, map_mul,
    PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion, hc, mul_one]
  have hfin : KPContFlatLogNormSmooth.finiteComponent F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) = c.val := by
    rw [show KPSmoothActualFlowData.archimedeanInsertion F ζ hζ =
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ from rfl]
    unfold KPContFlatLogNormSmooth.finiteComponent
    rw [map_mul, PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion, hc, mul_one]
    group
  have hfin' : KPContFlatLogNormSmooth.finiteLogNorm F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) =
      KPContFlatLogNormSmooth.finiteLogNorm F ζ hζ c.val := by
    unfold KPContFlatLogNormSmooth.finiteLogNorm
    rw [hfin]
    have hcc : KPContFlatLogNormSmooth.finiteComponent F ζ hζ c.val = c.val := by
      unfold KPContFlatLogNormSmooth.finiteComponent
      rw [hc, show PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ 1 = 1 from
        (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1]
      simp
    rw [hcc]
  rw [show PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ =
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ from rfl, hfin', hαc]
  congr 1
  exact Finset.sum_congr rfl (fun w _ => KPContFlatLogNormSmooth.complexProjectiveLogNorm_mk (a w))

private theorem flatR_pure_tensor_formula
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) (C : ℂ)
    (f : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 → ℂ)
    (hf : ∀ a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2,
      t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) = C * ∏ w, f w (a w))
    (s : ℂ) (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    (KPContFlatSourceRecipe.flatR F ζ hζ s t).val
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) =
      (Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ c.val : ℂ))*C) *
        ∏ w, (Complex.exp (s * (KPContFlatLogNormSmooth.complexMatrixLogNorm (a w) : ℂ))*f w (a w)) := by
  rw [KPContFlatSourceRecipe.flatR_formula, alpha_arch_finite_formula F ζ hζ, hf]
  push_cast
  rw [mul_add, Complex.exp_add, Finset.prod_mul_distrib, ← Complex.exp_sum]
  simp only [Finset.mul_sum]
  ring

private theorem complex_spherical_twist (s : ℂ) (g : KPCplxCharacterHaar.ComplexGL2) :
    Complex.exp (s * (KPContFlatLogNormSmooth.complexMatrixLogNorm g : ℂ)) *
      KPCplxPrincipalSeriesCharts.sphericalSection KPCplxPrincipalSeriesCharts.positiveParameter g =
        KPContHolomorphicKGeneration.complexSpherical s g := by
  have hr : 0 < ‖((g : Matrix (Fin 2) (Fin 2) ℂ).det)‖ /
      (‖g 1 0‖^2+‖g 1 1‖^2) := by
    have hsq := KPContFlatLogNormSmooth.complexMatrixLogNorm_argument_pos g
    have hn : 0 ≤ ‖((g : Matrix (Fin 2) (Fin 2) ℂ).det)‖ /
        (‖g 1 0‖^2+‖g 1 1‖^2) := by positivity
    nlinarith
  rw [← KPContHolomorphicKGeneration.complexSpherical_zero]
  unfold KPContFlatLogNormSmooth.complexMatrixLogNorm KPContHolomorphicKGeneration.complexSpherical
  dsimp only [KPCplxPrincipalSeriesCharts.bottomRowNormSq]
  rw [Real.log_pow, ← Complex.exp_add]
  push_cast
  congr 1
  change s * (2 * (Real.log (‖((g : Matrix (Fin 2) (Fin 2) ℂ).det)‖ /
    (‖g 1 0‖^2+‖g 1 1‖^2)) : ℂ)) + _ = _
  have hdet : ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ) =
      (g : Matrix (Fin 2) (Fin 2) ℂ).det := rfl
  rw [hdet]
  ring

private theorem spherical_word_matrix_smooth (w : KPContHolomorphicKGeneration.RealLieWord) (s : ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (KPCplxPrincipalSeriesCharts.matrixFunction (KPContHolomorphicKGeneration.complexSphericalWord w s))
      {g | g.det ≠ 0} := by
  obtain ⟨n,p,h,hh,he⟩ := ActualRaisingLocal.sphericalWord_polynomial_smooth_factors w
  have hs : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun g => s * (KPContFlatLogNormSmooth.complexMatrixLogNorm g : ℂ)) {g | g.det ≠ 0} := by
    apply ContDiffOn.mul contDiffOn_const
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn
      (KPContFlatLogNormSmooth.complexMatrixLogNorm_contDiffOn.of_le (by simp))
  have hf := ((KPCplxPrincipalSeriesCharts.principalSeries_mem_iff _ _).mp
    (KPCplxPrincipalSeriesCharts.sphericalSection KPCplxPrincipalSeriesCharts.positiveParameter).property).2
  have hsum : ContDiffOn ℝ (⊤ : ℕ∞) (fun g => ∑ j, (p j).eval s * h j g) {g | g.det ≠ 0} := by
    apply ContDiffOn.sum
    intro j hj
    exact contDiffOn_const.mul (hh j)
  apply ((hs.cexp.mul hf).mul hsum).congr
  intro g hg
  let a := Matrix.GeneralLinearGroup.mkOfDetNeZero g hg
  have hm (f : KPCplxCharacterHaar.ComplexGL2 → ℂ) :
      KPCplxPrincipalSeriesCharts.matrixFunction f g = f a := by
    simp only [KPCplxPrincipalSeriesCharts.matrixFunction]
    rw [dite_eq_left (show g.det ≠ 0 from hg)]
  rw [hm, he, ← complex_spherical_twist]
  rw [hm (KPCplxPrincipalSeriesCharts.sphericalSection KPCplxPrincipalSeriesCharts.positiveParameter)]
  rfl

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
private theorem parameter_path_hasDeriv_components (g : KPCplxCharacterHaar.ComplexGL2)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ i j, HasDerivAt (fun t : ℝ => ((g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M)) i j) (((g : Matrix (Fin 2) (Fin 2) ℂ) * M) i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) M (0 : ℝ)
  have hmat := h.const_mul (g : Matrix (Fin 2) (Fin 2) ℂ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hmat
  intro i j
  have hi := (ContinuousLinearMap.proj i : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Fin 2 → ℂ).hasFDerivAt.comp_hasDerivAt 0 hmat
  have hj := (ContinuousLinearMap.proj j : (Fin 2 → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt 0 hi
  have he : (fun t : ℝ => (t : ℂ) • M) = fun t => t • M := by
    funext t; ext i j; simp [Complex.real_smul]
  convert hj using 1
  · funext t
    change ((g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M)) i j =
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp (t • M)) i j
    rw [congrFun he t]
  · rfl

open scoped Matrix.Norms.Elementwise in
private theorem rightDerivative_smooth_fderiv (f : KPCplxCharacterHaar.ComplexGL2 → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (KPCplxPrincipalSeriesCharts.matrixFunction f) {g | g.det ≠ 0})
    (g : KPCplxCharacterHaar.ComplexGL2) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    deriv (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))) 0 =
      fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f) (g : Matrix (Fin 2) (Fin 2) ℂ)
        ((g : Matrix (Fin 2) (Fin 2) ℂ) * M) := by
  have hmat : HasDerivAt (fun t : ℝ => (g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M))
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * M) 0 :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (parameter_path_hasDeriv_components g M i))
  have hcont : Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.det) := by fun_prop
  have hh := (hf.differentiableOn (by simp)).differentiableAt
    ((isOpen_ne.preimage hcont).mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g))
  have hc := hh.hasFDerivAt.comp_hasDerivAt_of_eq 0 hmat (by simp)
  have heq : (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))) =
      KPCplxPrincipalSeriesCharts.matrixFunction f ∘ (fun t : ℝ => (g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M)) := by
    funext t
    have hu := Matrix.GeneralLinearGroup.det_ne_zero (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))
    have he : ((g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M)) : Matrix (Fin 2) (Fin 2) ℂ) =
        (g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M) := by congr 1
    dsimp only [Function.comp_def]
    rw [← he]
    unfold KPCplxPrincipalSeriesCharts.matrixFunction
    rw [dif_pos (show ((g : Matrix (Fin 2) (Fin 2) ℂ) *
      (KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M) : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 from by
        simpa only [Units.val_mul] using hu)]
    apply congrArg f
    apply Units.ext
    rfl
  rw [heq]
  exact hc.deriv

open scoped Matrix.Norms.Elementwise in

private theorem nativeSlotWord_complex_spherical
    (r : List (Fin 3 × Fin 2)) (s : ℂ) (g : KPCplxCharacterHaar.ComplexGL2) :
    nativeSlotWord r (KPContHolomorphicKGeneration.complexSpherical s) g =
      KPContHolomorphicKGeneration.complexSphericalWord
        (r.map (fun ij => slotLieMatrix ij.1 ij.2)) s g := by
  induction r generalizing g with
  | nil => rfl
  | cons ij r ih =>
    change nativeSlotRight ij.1 ij.2 (nativeSlotWord r (KPContHolomorphicKGeneration.complexSpherical s)) g =
      KPContHolomorphicKGeneration.rightLieFunction (slotLieMatrix ij.1 ij.2)
        (KPContHolomorphicKGeneration.complexSphericalWord (r.map (fun ij => slotLieMatrix ij.1 ij.2)) s) g
    have he : nativeSlotWord r (KPContHolomorphicKGeneration.complexSpherical s) =
        KPContHolomorphicKGeneration.complexSphericalWord (r.map (fun ij => slotLieMatrix ij.1 ij.2)) s := funext ih
    unfold nativeSlotRight
    rw [he, rightDerivative_smooth_fderiv _ (spherical_word_matrix_smooth _ _)]
    rfl

theorem actualRightWord_flat_spherical_tensor
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) (C : ℂ)
    (ht : ∀ a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2,
      t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) = C *
        ∏ w, KPCplxPrincipalSeriesCharts.sphericalSection KPCplxPrincipalSeriesCharts.positiveParameter (a w))
    (r : List (KPContActualSphericalRightFieldIdentification.LieIndex F))
    (s : ℂ) (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ
      (r.map (KPContActualSphericalRightFieldIdentification.lieEnumeration F).symm)
      ((KPContFlatSourceRecipe.flatR F ζ hζ s t).val)
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) =
      (Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ c.val : ℂ))*C) *
        ∏ w, KPContHolomorphicKGeneration.complexSphericalWord
          ((wordAtSlot w r).map (fun ij => slotLieMatrix ij.1 ij.2)) s (a w) := by
  have hf : ∀ a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2,
      (KPContFlatSourceRecipe.flatR F ζ hζ s t).val
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) =
        (Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ c.val : ℂ))*C) *
          ∏ w, KPContHolomorphicKGeneration.complexSpherical s (a w) := by
    intro a
    rw [flatR_pure_tensor_formula F ζ hζ t c C _ ht]
    simp_rw [complex_spherical_twist]
  rw [actualRightWord_pure_tensor F ζ hζ r c _ _ _ hf]
  simp_rw [nativeSlotWord_complex_spherical]

theorem sourceCore_le_scalarSmooth
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    KPMsRationalCompactCrossPairing.sourceCore F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ) ≤
      KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) := by
  unfold KPMsRationalCompactCrossPairing.sourceCore KPGlobalEisensteinData.hcHeckeCore
  exact iSup_le fun _ => iSup_le fun _ => inf_le_left.trans inf_le_left

theorem source_common_level
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ)) :
    ∃ U : KPMsRationalCompactCrossPairing.Level F ζ hζ,
      t ∈ KPContFlatCommonLevelKernel.CommonLevel F ζ hζ U ∧
      KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤ (KPContFlatSourceRecipe.D F ζ hζ).K ∧
      ∀ s g (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
        (KPContFlatSourceRecipe.flatR F ζ hζ s t).val (g * u.val) =
          (KPContFlatSourceRecipe.flatR F ζ hζ s t).val g := by
  obtain ⟨V, hV⟩ := KPGlobalResidualKernel.ScatteringResidue.scalarSmooth_exists_right_level
    (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) t.val
    (sourceCore_le_scalarSmooth F ζ hζ t.property)
  obtain ⟨K, hK⟩ := KPCompactFiniteLevel.exists_level F ζ hζ
  let U : KPMsRationalCompactCrossPairing.Level F ζ hζ :=
    ⟨V.toOpenSubgroup ⊓ K.toOpenSubgroup, V.isCompact.inter_right K.toOpenSubgroup.isClosed⟩
  have hUV : KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤
      KPGlobalTorusFunctionData.globalLevel F ζ hζ V := Subgroup.map_mono inf_le_left
  have hUK : KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤
      KPGlobalTorusFunctionData.globalLevel F ζ hζ K := Subgroup.map_mono inf_le_right
  have halpha (g : KPGlobalTorusFunctionData.G F ζ hζ)
      (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U) :
      KPContFlatSourceRecipe.alpha F ζ hζ (g * u.val) = KPContFlatSourceRecipe.alpha F ζ hζ g :=
    KPContFlatFullProductIwasawa.alpha_mul_compact F ζ hζ g ⟨u.val, hK (hUK u.property)⟩
  refine ⟨U, ?_, hUK.trans hK, ?_⟩
  · intro g u
    refine ⟨hV g ⟨u.val, hUV u.property⟩, ?_⟩
    rw [halpha g u, sub_self, Complex.ofReal_zero, zero_mul]
  · intro s g u
    rw [KPContFlatSourceRecipe.flatR_formula, KPContFlatSourceRecipe.flatR_formula,
      halpha g u, hV g ⟨u.val, hUV u.property⟩]

theorem spherical_source_reconstruction
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (ht : t ∈ KPContFlatCommonLevelKernel.rightKInfinityFixed F ζ hζ) :
    ∃ (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
      (v : KPContActualSphericalFlatStage.Stage F ζ hζ U),
      ∀ s g, (KPContFlatSourceRecipe.flatR F ζ hζ s t).val g =
        KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ []
          ((KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val) g := by
  obtain ⟨U, hU, _, _⟩ := source_common_level F ζ hζ t
  exact ⟨U, ⟨t, hU, ht⟩, fun _ _ => rfl⟩

theorem actual_source_flat_finite_pure_core
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ)) :
    ∃ (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
      (n : ℕ) (v : Fin n → KPContActualSphericalFlatStage.Stage F ζ hζ U)
      (f : Fin n → NumberField.InfinitePlace F →
        KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter),
      KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤ (KPContFlatSourceRecipe.D F ζ hζ).K ∧
      (∀ j w, KPContHolomorphicKGeneration.IsKFinite KPCplxPrincipalSeriesCharts.positiveParameter (f j w)) ∧
      ∀ (s : ℂ) (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
        (c : KPGlobalTorusFunctionData.finitePart F ζ hζ),
        (KPContFlatSourceRecipe.flatR F ζ hζ s t).val
          (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
            (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) =
          ∑ j, (KPContFlatSourceRecipe.flatR F ζ hζ s (v j).val).val c.val *
            ∏ w, Complex.exp (s * (KPContFlatLogNormSmooth.complexMatrixLogNorm (a w) : ℂ)) * f j w (a w) := by
  obtain ⟨U,n,v,f,hU,hf,he⟩ := actual_source_finite_pure_core F ζ hζ t
  refine ⟨U,n,v,f,hU,hf,?_⟩
  intro s a c
  rw [KPContFlatSourceRecipe.flatR_formula, alpha_arch_finite_formula F ζ hζ, he,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [KPContFlatSourceRecipe.flatR_formula, Finset.prod_mul_distrib, ← Complex.exp_sum]
  push_cast
  rw [mul_add, Complex.exp_add, Finset.mul_sum]
  ring

 def raisingTracelessCoordinates (X : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℂ :=
  ![(X 0 0 - X 1 1)/2, X 0 1, X 1 0]

open ActualRaisingLocal.SphericalReseeding in

private theorem source_finite_pure_with_spherical_formula
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ)) :
    ∃ (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
      (n : ℕ) (v : Fin n → KPContActualSphericalFlatStage.Stage F ζ hζ U)
      (f : Fin n → NumberField.InfinitePlace F →
        KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter),
      KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤ (KPContFlatSourceRecipe.D F ζ hζ).K ∧
      (∀ j w, KPContHolomorphicKGeneration.IsKFinite KPCplxPrincipalSeriesCharts.positiveParameter (f j w)) ∧
      (∀ (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
        (c : KPGlobalTorusFunctionData.finitePart F ζ hζ),
        t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) =
          ∑ j, (v j).val.val.val c.val * ∏ w, f j w (a w)) ∧
      ∀ j (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
        (c : KPGlobalTorusFunctionData.finitePart F ζ hζ),
        (v j).val.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) =
          (v j).val.val.val c.val * ∏ w, KPCplxPrincipalSeriesCharts.sphericalSection
            KPCplxPrincipalSeriesCharts.positiveParameter (a w) := by
  obtain ⟨U₀,htU,hUK,_⟩ := source_common_level F ζ hζ t
  obtain ⟨n,m,k,A,f,hf,he⟩ := actual_source_uniform_finite_evaluation_separation F ζ hζ t
  have hb := fun j : Fin n => actual_source_finite_evaluation_spherical_reseeding F ζ hζ t
    U₀ htU hUK m k (A j)
  choose V v hV hVK hv hvfiber using hb
  let H := U₀.toOpenSubgroup ⊓ Finset.univ.inf (fun j : Fin n => (V j).toOpenSubgroup)
  let U : KPMsRationalCompactCrossPairing.Level F ζ hζ :=
    ⟨H, U₀.isCompact.of_isClosed_subset H.isClosed (fun _ hx => hx.1)⟩
  have hUU : U.toOpenSubgroup ≤ U₀.toOpenSubgroup := inf_le_left
  have hUV (j : Fin n) : U.toOpenSubgroup ≤ (V j).toOpenSubgroup :=
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ j))
  have hglobal (j : Fin n) : KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤
      KPGlobalTorusFunctionData.globalLevel F ζ hζ (V j) := Subgroup.map_mono (hUV j)
  let vv : Fin n → KPContActualSphericalFlatStage.Stage F ζ hζ U := fun j =>
    ⟨(v j).val, (fun g u => (v j).property.1 g ⟨u.val,hglobal j u.property⟩), (v j).property.2⟩
  have hInsertion : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (fun w => Matrix.ProjGenLinGroup.mk (1 : KPCplxCharacterHaar.ComplexGL2)) = 1 := by
    have h := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1
    convert h using 1
    congr 1
  refine ⟨U,n,vv,f,(Subgroup.map_mono hUU).trans hUK,hf,?_,?_⟩
  rotate_left
  · intro j a c
    have hv1 := hv j (fun _ => 1) c
    simp only [sphericalProduct_one, one_mul, hInsertion] at hv1
    rw [hv j a c, mul_comm, ← hv1]
    rfl
  intro a c
  rw [he]
  apply Finset.sum_congr rfl
  intro j hj
  have hc := hv j (fun _ => 1) c
  simp only [sphericalProduct_one, one_mul] at hc
  rw [hInsertion,one_mul] at hc
  exact congrArg (fun z => z * ∏ w, f j w (a w)) hc.symm

 def LocalClears (f : KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter) : Prop :=
  ∃ (n : ℕ) (r : Fin n → List (Fin 3 × Fin 2)) (q : ℂ → ℂ) (b : Fin n → ℂ → ℂ),
    AnalyticOnNhd ℂ q Set.univ ∧ q 0 = 1 ∧ (∀ j, AnalyticOnNhd ℂ (b j) Set.univ) ∧
    ∀ (s : ℂ) (g : KPCplxCharacterHaar.ComplexGL2), q s * Complex.exp (s * (KPContFlatLogNormSmooth.complexMatrixLogNorm g : ℂ)) * f g =
      ∑ j, b j s * KPContHolomorphicKGeneration.complexSphericalWord
        ((r j).map (fun ij => slotLieMatrix ij.1 ij.2)) s g

private theorem harmonic_local_clears (ℓ : ℕ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter)
    (hf : f ∈ KPCplxIntertwinerEigenvalues.harmonicKType KPCplxPrincipalSeriesCharts.positiveParameter ℓ) :
    LocalClears f := by
  obtain ⟨n,W,q,b,hq,hq0,hb,he⟩ := ActualRaisingLocal.local_harmonic_cleared_word_reconstruction ℓ f hf
  have hex := fun j : Fin n => complex_spherical_word_six_real_expansion (W j)
  choose m r c hr using hex
  let I := Σ j : Fin n, Fin (m j)
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, fun k => r (e.symm k).1 (e.symm k).2, q,
    fun k s => b (e.symm k).1 s*c (e.symm k).1 (e.symm k).2, hq,hq0,
    fun k => (hb _).mul analyticOnNhd_const, ?_⟩
  intro s g
  have hlog : (KPContFlatLogNormSmooth.complexMatrixLogNorm g : ℂ) =
      2*(Real.log (‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ /
        KPCplxPrincipalSeriesCharts.bottomRowNormSq g) : ℂ) := by
    unfold KPContFlatLogNormSmooth.complexMatrixLogNorm KPCplxPrincipalSeriesCharts.bottomRowNormSq
    rw [Real.log_pow]; push_cast; rfl
  rw [hlog, show s*(2*(Real.log _ : ℂ)) = 2*s*(Real.log _ : ℂ) by ring, he]
  simp_rw [hr, Finset.mul_sum]
  have hsum := Fintype.sum_sigma (fun k : I => b k.1 s*c k.1 k.2 *
    KPContHolomorphicKGeneration.complexSphericalWord
      ((r k.1 k.2).map (fun ij => slotLieMatrix ij.1 ij.2)) s g)
  simp_rw [← mul_assoc]
  rw [← hsum]
  exact (Equiv.sum_comp e.symm _).symm

private theorem clears_zero : LocalClears (0 : KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter) := by
  refine ⟨0, fun k => Fin.elim0 k, fun _ => 1, fun k => Fin.elim0 k,
    analyticOnNhd_const, rfl, fun k => Fin.elim0 k, ?_⟩
  intro s g
  simp

private theorem clears_add
    (f h : KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter)
    (hf : LocalClears f) (hh : LocalClears h) : LocalClears (f+h) := by
  obtain ⟨n,r,q,b,hq,hq0,hb,he⟩ := hf
  obtain ⟨m,u,p,d,hp,hp0,hd,hf⟩ := hh
  let I := Fin n ⊕ Fin m
  let e := Fintype.equivFin I
  let rr : I → List (Fin 3 × Fin 2) := Sum.elim r u
  let bb : I → ℂ → ℂ := Sum.elim (fun j s => p s*b j s) (fun j s => q s*d j s)
  refine ⟨Fintype.card I, rr ∘ e.symm, fun s => q s*p s, fun j => bb (e.symm j),
    hq.mul hp, by simp [hq0,hp0], ?_, ?_⟩
  · intro j
    change AnalyticOnNhd ℂ (bb (e.symm j)) Set.univ
    cases e.symm j with
    | inl k => exact hp.mul (hb k)
    | inr k => exact hq.mul (hd k)
  · intro s g
    have heq : (q s*p s)*Complex.exp (s*(KPContFlatLogNormSmooth.complexMatrixLogNorm g : ℂ))*(f+h) g =
        p s*(q s*Complex.exp (s*(KPContFlatLogNormSmooth.complexMatrixLogNorm g : ℂ))*f g) +
        q s*(p s*Complex.exp (s*(KPContFlatLogNormSmooth.complexMatrixLogNorm g : ℂ))*h g) := by
      change _ * _ * (f g+h g) = _; ring
    rw [heq, he, hf, Finset.mul_sum, Finset.mul_sum]
    have hsum := Equiv.sum_comp e.symm (fun j : I => bb j s *
      KPContHolomorphicKGeneration.complexSphericalWord ((rr j).map (fun ij => slotLieMatrix ij.1 ij.2)) s g)
    change _ = ∑ j, bb (e.symm j) s * KPContHolomorphicKGeneration.complexSphericalWord
      ((rr (e.symm j)).map (fun ij => slotLieMatrix ij.1 ij.2)) s g
    rw [hsum, Fintype.sum_sum_type]
    apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl; intro j hj; dsimp [rr,bb]; ring
    · apply Finset.sum_congr rfl; intro j hj; dsimp [rr,bb]; ring

private theorem kfinite_local_clears
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter)
    (hf : KPContHolomorphicKGeneration.IsKFinite KPCplxPrincipalSeriesCharts.positiveParameter f) :
    LocalClears f := by
  obtain ⟨I,a,ha,he⟩ := RepresentationTheory.KPContHolomorphicKGenerationProve.kFinite_finite_harmonic_decomposition _ f hf
  rw [← he]
  clear he
  induction I using Finset.induction_on with
  | empty => simpa using clears_zero
  | @insert ℓ I hℓ ih =>
    rw [Finset.sum_insert hℓ]
    exact clears_add _ _ (harmonic_local_clears ℓ (a ℓ) (ha ℓ (Finset.mem_insert_self ℓ I)))
      (ih (fun k hk => ha k (Finset.mem_insert_of_mem hk)))

 def assembledWord {F : Type} [Field F] [NumberField F]
    (l : List (NumberField.InfinitePlace F)) (r : NumberField.InfinitePlace F → List (Fin 3 × Fin 2)) :
    List (KPContActualSphericalRightFieldIdentification.LieIndex F) :=
  l.flatMap (fun v => (r v).map (fun ij => (v,ij)))

private theorem assembledWord_slot {F : Type} [Field F] [NumberField F]
    (l : List (NumberField.InfinitePlace F)) (hl : l.Nodup)
    (r : NumberField.InfinitePlace F → List (Fin 3 × Fin 2)) (v : NumberField.InfinitePlace F) :
    wordAtSlot v (assembledWord l r) = if v ∈ l then r v else [] := by
  induction l with
  | nil => simp [assembledWord,wordAtSlot]
  | cons a l ih =>
    have hal : a ∉ l := (List.nodup_cons.mp hl).1
    have hll := (List.nodup_cons.mp hl).2
    have hfilter : wordAtSlot v ((r a).map (fun ij => (a,ij))) = if a = v then r a else [] := by
      unfold wordAtSlot
      rw [List.filterMap_map]
      by_cases h : a = v
      · subst a
        simp only [Function.comp_def, ite_true]
        change List.filterMap (some ∘ id) (r v) = r v
        rw [List.filterMap_eq_map, List.map_id]
      · simp only [Function.comp_def, h, ite_false]
        simp
    change wordAtSlot v (((r a).map (fun ij => (a,ij))) ++ assembledWord l r) = _
    unfold wordAtSlot at ⊢
    rw [List.filterMap_append]
    change wordAtSlot v ((r a).map (fun ij => (a,ij))) ++ wordAtSlot v (assembledWord l r) = _
    rw [hfilter, ih hll]
    by_cases hav : a = v
    · subst a; simp [hal]
    · simp [hav, Ne.symm hav]

private theorem assembled_all_slots {F : Type} [Field F] [NumberField F]
    (r : NumberField.InfinitePlace F → List (Fin 3 × Fin 2)) (v : NumberField.InfinitePlace F) :
    wordAtSlot v (assembledWord Finset.univ.toList r) = r v := by
  rw [assembledWord_slot _ (Finset.nodup_toList _) r v]
  simp

private theorem analytic_finite_prod {I : Type*} (l : Finset I) (f : I → ℂ → ℂ)
    (hf : ∀ i ∈ l, AnalyticOnNhd ℂ (f i) Set.univ) :
    AnalyticOnNhd ℂ (fun s => ∏ i ∈ l, f i s) Set.univ := by
  classical
  induction l using Finset.induction_on with
  | empty => simpa using (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) Set.univ)
  | @insert i l hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i l)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem actual_cleared_spherical_derivative_reconstruction
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ
      (KPContFlatSourceRecipe.D F ζ hζ)) :
    ∃ (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
      (n : ℕ) (v : Fin n → KPContActualSphericalFlatStage.Stage F ζ hζ U)
      (w : Fin n → List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)))
      (q : ℂ → ℂ) (b : Fin n → ℂ → ℂ),
      AnalyticOnNhd ℂ q KPContinuation.spectralDomain ∧ q 0 = 1 ∧
      (∀ j, AnalyticOnNhd ℂ (b j) KPContinuation.spectralDomain) ∧
      ∀ s ∈ KPContinuation.spectralDomain, ∀ g,
        q s * (KPContFlatSourceRecipe.flatR F ζ hζ s t).val g =
          ∑ j, b j s * KPContActualSphericalRightFieldIdentification.actualRightWord
            F ζ hζ (w j)
            ((KPContFlatSourceRecipe.flatR F ζ hζ s (v j).val).val) g := by
  obtain ⟨U,n,v,f,hU,hf,ht,hv⟩ := source_finite_pure_with_spherical_formula F ζ hζ t
  have hc := fun j w => kfinite_local_clears (f j w) (hf j w)
  choose m r q b hq hq0 hb he using hc
  let Q : ℂ → ℂ := fun s => ∏ j : Fin n, ∏ w : NumberField.InfinitePlace F, q j w s
  let P : Fin n → ℂ → ℂ := fun j s => ∏ w : NumberField.InfinitePlace F, q j w s
  let E : Fin n → ℂ → ℂ := fun j s => ∏ k ∈ Finset.univ.erase j, P k s
  let I := Σ j : Fin n, (w : NumberField.InfinitePlace F) → Fin (m j w)
  let e := Fintype.equivFin I
  let rr : I → List (KPContActualSphericalRightFieldIdentification.LieIndex F) :=
    fun k => assembledWord Finset.univ.toList (fun w => r k.1 w (k.2 w))
  let B : I → ℂ → ℂ := fun k s => E k.1 s * ∏ w : NumberField.InfinitePlace F, b k.1 w (k.2 w) s
  have hP j : AnalyticOnNhd ℂ (P j) Set.univ := analytic_finite_prod _ _ (fun w _ => hq j w)
  have hE j : AnalyticOnNhd ℂ (E j) Set.univ := analytic_finite_prod _ _ (fun k _ => hP k)
  have hQ : AnalyticOnNhd ℂ Q Set.univ := analytic_finite_prod _ _ (fun j _ => hP j)
  refine ⟨U,Fintype.card I, fun k => v (e.symm k).1,
    fun k => (rr (e.symm k)).map (KPContActualSphericalRightFieldIdentification.lieEnumeration F).symm,
    Q, fun k => B (e.symm k), hQ.mono (Set.subset_univ _), ?_, ?_, ?_⟩
  · simp [Q,hq0]
  · intro k
    exact ((hE (e.symm k).1).mul
      (analytic_finite_prod _ _ (fun w _ => hb (e.symm k).1 w ((e.symm k).2 w)))).mono (Set.subset_univ _)
  · intro s hs g
    let c : KPGlobalTorusFunctionData.finitePart F ζ hζ :=
      ⟨KPContFlatLogNormSmooth.finiteComponent F ζ hζ g, KPContFlatLogNormSmooth.finiteComponent_mem F ζ hζ g⟩
    let a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 :=
      fun w => (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w).out
    have hg : g = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val := by
      have ha : (fun w => Matrix.ProjGenLinGroup.mk (a w)) = PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g := by
        funext w; exact Quotient.out_eq _
      rw [ha]
      dsimp [c, KPContFlatLogNormSmooth.finiteComponent]
      rw [show KPSmoothActualFlowData.archimedeanInsertion F ζ hζ =
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ from rfl]
      group
    rw [hg, KPContFlatSourceRecipe.flatR_formula, alpha_arch_finite_formula F ζ hζ, ht, Finset.mul_sum]
    have hterm (j : Fin n) :
      Q s * (Complex.exp (s * ((∑ w, KPContFlatLogNormSmooth.complexMatrixLogNorm (a w)) +
          KPContFlatSourceRecipe.alpha F ζ hζ c.val : ℝ)) *
            ((v j).val.val.val c.val * ∏ w, f j w (a w))) =
        ∑ k : (w : NumberField.InfinitePlace F) → Fin (m j w),
          B ⟨j,k⟩ s * KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ
            ((rr ⟨j,k⟩).map (KPContActualSphericalRightFieldIdentification.lieEnumeration F).symm)
            ((KPContFlatSourceRecipe.flatR F ζ hζ s (v j).val).val)
            (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
              (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) := by
      have hQP : Q s = E j s * P j s := (Finset.prod_erase_mul Finset.univ (fun k => P k s) (Finset.mem_univ j)).symm
      have hprod := congrArg (fun z : ℂ => z) (Finset.prod_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
        rfl (fun w hw => he j w s (a w)))
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hprod
      change P j s * (∏ w, Complex.exp (s * (KPContFlatLogNormSmooth.complexMatrixLogNorm (a w) : ℂ))) *
          (∏ w, f j w (a w)) = _ at hprod
      rw [Fintype.prod_sum] at hprod
      have hweight : Complex.exp (s * ((∑ w, KPContFlatLogNormSmooth.complexMatrixLogNorm (a w)) +
          KPContFlatSourceRecipe.alpha F ζ hζ c.val : ℝ)) =
          Complex.exp (s*(KPContFlatSourceRecipe.alpha F ζ hζ c.val : ℂ))*
            ∏ w, Complex.exp (s*(KPContFlatLogNormSmooth.complexMatrixLogNorm (a w) : ℂ)) := by
        push_cast; rw [mul_add, Complex.exp_add, ← Complex.exp_sum]; simp only [Finset.mul_sum]; ring
      rw [hQP,hweight]
      calc
        _ = (E j s * (Complex.exp (s*(KPContFlatSourceRecipe.alpha F ζ hζ c.val : ℂ)) * (v j).val.val.val c.val)) *
            (P j s * (∏ w, Complex.exp (s*(KPContFlatLogNormSmooth.complexMatrixLogNorm (a w) : ℂ))) *
              (∏ w, f j w (a w))) := by ring
        _ = _ := by
          rw [hprod, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          rw [actualRightWord_flat_spherical_tensor F ζ hζ (v j).val c _ (fun a => hv j a c) (rr ⟨j,k⟩) s a]
          simp only [rr, assembled_all_slots, B]
          rw [Finset.prod_mul_distrib]
          ring
    rw [Finset.mul_sum]
    change ∑ j, Q s * (Complex.exp (s * ((∑ w, KPContFlatLogNormSmooth.complexMatrixLogNorm (a w)) +
      KPContFlatSourceRecipe.alpha F ζ hζ c.val : ℝ)) * ((v j).val.val.val c.val * ∏ w, f j w (a w))) = _
    simp_rw [hterm]
    have hsum := Fintype.sum_sigma (fun k : I => B k s * KPContActualSphericalRightFieldIdentification.actualRightWord
      F ζ hζ ((rr k).map (KPContActualSphericalRightFieldIdentification.lieEnumeration F).symm)
      ((KPContFlatSourceRecipe.flatR F ζ hζ s (v k.1).val).val)
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val))
    rw [← hsum]
    exact (Equiv.sum_comp e.symm _).symm

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingGeometry

end
