module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.RadialCovector

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
namespace DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

section JetCalculus

 def bottomRowJet (c d : ℂ) (r : ℝ) : Fin 6 → ℝ :=
  ![-4 * r * (Complex.normSq c - Complex.normSq d) / (Complex.normSq c + Complex.normSq d),
    0,
    -4 * r * (c * star d).re / (Complex.normSq c + Complex.normSq d),
    4 * r * (c * star d).im / (Complex.normSq c + Complex.normSq d),
    -4 * r * (c * star d).re / (Complex.normSq c + Complex.normSq d),
    -4 * r * (c * star d).im / (Complex.normSq c + Complex.normSq d)]

 theorem normSq_hasDerivAt {z : ℝ → ℂ} {v : ℂ} {t : ℝ} (hz : HasDerivAt z v t) :
    HasDerivAt (fun s => Complex.normSq (z s)) (2 * (v * star (z t)).re) t := by
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hz
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hz
  have h := (hre.mul hre).add (him.mul him)
  convert h using 1
  · ext s; simp [Complex.normSq_apply]
  · simp [Complex.mul_re, Complex.star_def]; ring

open scoped Matrix.Norms.Operator in
 theorem matrix_path_components (g X : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ i j, HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X)) i j)
      ((g * X) i j) 0 := by
  have h := ((hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (f := fun t : ℝ => (t : ℂ)) 0 Complex.ofRealCLM.hasDerivAt
  have hmat := h.const_mul g
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, ContinuousLinearMap.coe_restrictScalars, ContinuousLinearMap.toSpanSingleton_apply, one_smul, zero_smul, NormedSpace.exp_zero, mul_one, one_mul] at hmat
  intro i j
  have hi := (ContinuousLinearMap.proj i : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Fin 2 → ℂ).hasFDerivAt.comp_hasDerivAt 0 hmat
  have hj := (ContinuousLinearMap.proj j : (Fin 2 → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt 0 hi
  change HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X)) i j)
    ((g * (ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ
      (NormedSpace.exp (((0 : ℝ) : ℂ) • X) * X))) 1) i j) 0 at hj
  simpa using hj

 def matrixHeightSquared (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Complex.normSq g.det / (Complex.normSq (g 1 0) + Complex.normSq (g 1 1))^2

open scoped Matrix.Norms.Operator in
private theorem matrix_det_basis_jet (g : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 6) :
    HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) •
      KPSmoothActualFlowData.basisMatrix j)).det) 0 0 := by
  have h := matrix_path_components g (KPSmoothActualFlowData.basisMatrix j)
  have hd := ((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0))
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one] at hd
  convert hd using 1
  · ext t; simp only [Matrix.det_fin_two, Pi.sub_apply, Pi.mul_apply]
  · fin_cases j <;> simp [KPSmoothActualFlowData.basisMatrix,
      KPSmoothActualFlowData.sl2Matrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

open scoped Matrix.Norms.Operator in
 theorem matrix_bottom_basis_jet (g : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 6) :
    HasDerivAt (fun t : ℝ => Complex.normSq ((g * NormedSpace.exp ((t : ℂ) •
      KPSmoothActualFlowData.basisMatrix j)) 1 0) +
      Complex.normSq ((g * NormedSpace.exp ((t : ℂ) •
      KPSmoothActualFlowData.basisMatrix j)) 1 1))
    (![2 * (Complex.normSq (g 1 0) - Complex.normSq (g 1 1)), 0,
      2 * (g 1 0 * star (g 1 1)).re, -2 * (g 1 0 * star (g 1 1)).im,
      2 * (g 1 0 * star (g 1 1)).re, 2 * (g 1 0 * star (g 1 1)).im] j) 0 := by
  have h := matrix_path_components g (KPSmoothActualFlowData.basisMatrix j)
  have hd := (normSq_hasDerivAt (h 1 0)).add (normSq_hasDerivAt (h 1 1))
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one] at hd
  convert hd using 1
  fin_cases j <;> simp [KPSmoothActualFlowData.basisMatrix,
    KPSmoothActualFlowData.sl2Matrix, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring

open scoped Matrix.Norms.Operator in
 theorem matrix_height_squared_basis_jet (g : Matrix (Fin 2) (Fin 2) ℂ)
    (hbot : Complex.normSq (g 1 0) + Complex.normSq (g 1 1) ≠ 0) (j : Fin 6) :
    HasDerivAt (fun t : ℝ => matrixHeightSquared
      (g * NormedSpace.exp ((t : ℂ) • KPSmoothActualFlowData.basisMatrix j)))
      (bottomRowJet (g 1 0) (g 1 1) (matrixHeightSquared g) j) 0 := by
  have hdet := normSq_hasDerivAt (matrix_det_basis_jet g j)
  have hden := matrix_bottom_basis_jet g j
  have hd := hdet.div (hden.pow 2) (by simpa using pow_ne_zero 2 hbot)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one,
    zero_mul, Complex.zero_re, mul_zero, zero_sub] at hd
  convert hd using 1
  · rfl
  · fin_cases j <;> simp [bottomRowJet, matrixHeightSquared] <;> field_simp <;> ring

 theorem gl_bottom_nonzero (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    Complex.normSq (g 1 0) + Complex.normSq (g 1 1) ≠ 0 := by
  have hp := KPArch.actionDenominator_pos g (0,0)
  simpa [KPArch.actionDenominator, KPArch.height, Complex.sq_norm, add_comm] using ne_of_gt hp

 theorem matrix_height_squared_action (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    matrixHeightSquared g = Real.exp (2 * (KPArch.action g (0,0)).2) := by
  rw [two_mul, Real.exp_add, ← pow_two]
  change matrixHeightSquared g = (KPArch.height (KPArch.action g (0,0)))^2
  rw [KPArch.action_height]
  simp [matrixHeightSquared, KPArch.height, div_pow, Complex.sq_norm, add_comm]

private theorem matrix_height_squared_scalar (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (u : ℂˣ) :
    matrixHeightSquared ((g * Matrix.GeneralLinearGroup.scalar (Fin 2) u : Matrix.GeneralLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = matrixHeightSquared g := by
  rw [matrix_height_squared_action, matrix_height_squared_action,
    (KPArch.action_laws g (Matrix.GeneralLinearGroup.scalar (Fin 2) u) (0,0)).2,
    KPArch.scalar_action]

private theorem matrix_height_squared_pgl_out (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    matrixHeightSquared (Matrix.ProjGenLinGroup.mk g).out = matrixHeightSquared g := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp
    (show Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk (Matrix.ProjGenLinGroup.mk g).out from
      (Quotient.out_eq _).symm)
  rw [← hu, matrix_height_squared_scalar]

 def pglHeightSquared (g : Matrix.ProjGenLinGroup (Fin 2) ℂ) : ℝ :=
  Real.exp (2 * (KPArch.action g.out (0,0)).2)

open scoped Matrix.Norms.Operator in
private theorem pgl_height_squared_basis_jet (g : Matrix.ProjGenLinGroup (Fin 2) ℂ) (j : Fin 6) :
    HasDerivAt (fun t : ℝ => pglHeightSquared (g *
      Matrix.ProjGenLinGroup.mk (KPSmoothActualFlowData.matrixExponential ((t : ℂ) •
        KPSmoothActualFlowData.basisMatrix j))))
      (bottomRowJet (g.out 1 0) (g.out 1 1) (pglHeightSquared g) j) 0 := by
  have h := matrix_height_squared_basis_jet (g.out : Matrix (Fin 2) (Fin 2) ℂ)
    (gl_bottom_nonzero g.out) j
  have heq : (fun t : ℝ => pglHeightSquared (g *
      Matrix.ProjGenLinGroup.mk (KPSmoothActualFlowData.matrixExponential ((t : ℂ) •
        KPSmoothActualFlowData.basisMatrix j)))) =
      (fun t : ℝ => matrixHeightSquared ((g.out : Matrix (Fin 2) (Fin 2) ℂ) *
        NormedSpace.exp ((t : ℂ) • KPSmoothActualFlowData.basisMatrix j))) := by
    funext t
    rw [pglHeightSquared, ← matrix_height_squared_action]
    have ho : Matrix.ProjGenLinGroup.mk g.out = g := Quotient.out_eq g
    conv_lhs => rw [← ho, ← map_mul, matrix_height_squared_pgl_out]
    rfl
  rw [heq]
  simpa [pglHeightSquared, ← matrix_height_squared_action] using h

variable (F : Type) [Field F] [NumberField F]
 def globalPglHeightSquared (g : KPSmoothActualFlowData.GInfinity F) : ℝ :=
  ∏ w, pglHeightSquared (g w)

open scoped Matrix.Norms.Operator in
 theorem flow_apply (w v : NumberField.InfinitePlace F) (j : Fin 6) (t : ℝ) :
    KPSmoothActualFlowData.flow F (w,j) t v =
      if v = w then Matrix.ProjGenLinGroup.mk
        (KPSmoothActualFlowData.matrixExponential ((t : ℂ) • KPSmoothActualFlowData.basisMatrix j))
      else 1 := by
  unfold KPSmoothActualFlowData.flow KPSmoothActualFlowData.exponential
  by_cases hv : v = w
  · simp only [hv, ↓reduceIte]
    congr 2
    ext a b
    fin_cases a <;> fin_cases b <;> fin_cases j <;>
      simp [KPSmoothActualFlowData.sl2Matrix, KPSmoothActualFlowData.basisMatrix,
        Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul] <;> ring
  · simp only [hv, ↓reduceIte]
    have hz : KPSmoothActualFlowData.sl2Matrix (fun i => if (v,i) = (w,j) then t else 0) = 0 := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [KPSmoothActualFlowData.sl2Matrix, hv]
    rw [hz]
    change Matrix.ProjGenLinGroup.mk ((NormedSpace.isUnit_exp (0 : Matrix (Fin 2) (Fin 2) ℂ)).unit) = 1
    have hunit : (NormedSpace.isUnit_exp (0 : Matrix (Fin 2) (Fin 2) ℂ)).unit = 1 := by
      apply Units.ext; simp
    rw [hunit, map_one]

private theorem bottomRowJet_mul (c d : ℂ) (r s : ℝ) (j : Fin 6) :
    bottomRowJet c d (r * s) j = r * bottomRowJet c d s j := by
  fin_cases j <;> simp [bottomRowJet] <;> ring

open scoped Matrix.Norms.Operator in
private theorem global_height_squared_basis_jet (g : KPSmoothActualFlowData.GInfinity F)
    (w : NumberField.InfinitePlace F) (j : Fin 6) :
    HasDerivAt (fun t : ℝ => globalPglHeightSquared F (g * KPSmoothActualFlowData.flow F (w,j) t))
      (bottomRowJet ((g w).out 1 0) ((g w).out 1 1) (globalPglHeightSquared F g) j) 0 := by
  let C := ∏ v ∈ Finset.univ.erase w, pglHeightSquared (g v)
  have heq : (fun t : ℝ => globalPglHeightSquared F (g * KPSmoothActualFlowData.flow F (w,j) t)) =
      (fun t : ℝ => C * pglHeightSquared (g w * Matrix.ProjGenLinGroup.mk
        (KPSmoothActualFlowData.matrixExponential ((t : ℂ) • KPSmoothActualFlowData.basisMatrix j)))) := by
    funext t
    rw [globalPglHeightSquared, ← Finset.prod_erase_mul _ _ (Finset.mem_univ w)]
    congr 1
    · apply Finset.prod_congr rfl
      intro v hv
      simp only [Pi.mul_apply, flow_apply, (Finset.mem_erase.mp hv).1, ↓reduceIte, mul_one]
    · simp only [Pi.mul_apply, flow_apply, ↓reduceIte]
  rw [heq]
  have h := (pgl_height_squared_basis_jet (g w) j).const_mul C
  convert h using 1
  rw [globalPglHeightSquared, ← Finset.prod_erase_mul _ _ (Finset.mem_univ w)]
  exact bottomRowJet_mul _ _ _ _ _

variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem projection_insertion (g : KPSmoothActualFlowData.GInfinity F) :
    KPSmoothLocalQuotientCharts.archProjection F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ g) = g := by
  exact PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion F ζ hζ g

 def upstairsHeightSquared (q : Cover F ζ hζ) : ℝ :=
  globalPglHeightSquared F (KPSmoothLocalQuotientCharts.archProjection F ζ hζ q)

open scoped Matrix.Norms.Operator in
private theorem upstairs_height_squared_basis_jet (c g : Cover F ζ hζ)
    (w : NumberField.InfinitePlace F) (j : Fin 6) :
    HasDerivAt (fun t : ℝ => upstairsHeightSquared F ζ hζ
      (c⁻¹ * (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F (w,j) t))))
      (bottomRowJet ((KPSmoothLocalQuotientCharts.archProjection F ζ hζ (c⁻¹ * g) w).out 1 0)
        ((KPSmoothLocalQuotientCharts.archProjection F ζ hζ (c⁻¹ * g) w).out 1 1)
        (upstairsHeightSquared F ζ hζ (c⁻¹ * g)) j) 0 := by
  simpa only [upstairsHeightSquared, ← mul_assoc, map_mul, projection_insertion] using
    global_height_squared_basis_jet F (KPSmoothLocalQuotientCharts.archProjection F ζ hζ (c⁻¹ * g)) w j

private theorem global_height_literal (ζ₀ : F) (hζ₀ : IsPrimitiveRoot ζ₀ 12) (g : KPSmoothActualFlowData.GInfinity F) :
    globalPglHeightSquared F g =
      Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) *
        KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
          (fun i => KPArch.action (g (KPCusp.complexPlace F i)).out (0,0))) := by
  have hd := (KPArch.complex_places_of_primitive_twelfth_root F ζ₀ hζ₀).2.2
  have hdn : (KPCuspLogShape.dimension F : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  unfold globalPglHeightSquared pglHeightSquared KPCuspLogShape.meanHeight
  rw [← Real.exp_sum, ← Finset.mul_sum]
  congr 1
  let he : NumberField.InfinitePlace F ≃ Fin (KPCuspLogShape.dimension F) :=
    { toFun := fun w => Fintype.equivFin {w : NumberField.InfinitePlace F // w.IsComplex}
        ⟨w, KPHilbert.infinite_isComplex F ζ₀ hζ₀ w⟩
      invFun := KPCusp.complexPlace F
      left_inv := by intro w; exact congrArg Subtype.val (Equiv.symm_apply_apply _ _)
      right_inv := by
        intro i
        exact (Fintype.equivFin {w : NumberField.InfinitePlace F // w.IsComplex}).apply_symm_apply i }
  have hs : (∑ w : NumberField.InfinitePlace F, (KPArch.action (g w).out (0,0)).2) =
      ∑ i : Fin (KPCuspLogShape.dimension F), (KPArch.action (g (KPCusp.complexPlace F i)).out (0,0)).2 := by
    change (∑ w, (KPArch.action (g w).out (0,0)).2) =
      ∑ i, (KPArch.action (g (he.symm i)).out (0,0)).2
    exact (Equiv.sum_comp he.symm (fun w => (KPArch.action (g w).out (0,0)).2)).symm
  rw [hs]
  field_simp

end JetCalculus

private theorem normalRadial_eq_upstairs (c a : Cover F ζ hζ) :
    normalRadial c a = upstairsHeightSquared F ζ hζ (c⁻¹ * a) := by
  unfold normalRadial upstairsHeightSquared
  exact (global_height_literal F ζ hζ
    (KPSmoothLocalQuotientCharts.archProjection F ζ hζ (c⁻¹ * a))).symm

 theorem normalRadialJet_eq_bottomRowJet (c g : Cover F ζ hζ)
    (w : NumberField.InfinitePlace F) (l : Fin 6) :
    normalRadialJet c w l g =
      bottomRowJet ((KPSmoothLocalQuotientCharts.archProjection F ζ hζ (c⁻¹ * g) w).out 1 0)
        ((KPSmoothLocalQuotientCharts.archProjection F ζ hζ (c⁻¹ * g) w).out 1 1)
        (normalRadial c g) l := by
  unfold normalRadialJet
  have hfun : (fun t : ℝ => normalRadial c (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F (w,l) t))) =
      (fun t : ℝ => upstairsHeightSquared F ζ hζ
        (c⁻¹ * (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (KPSmoothActualFlowData.flow F (w,l) t)))) := by
    funext t
    rw [normalRadial_eq_upstairs]
  rw [hfun, (upstairs_height_squared_basis_jet F ζ hζ c g w l).deriv,
    ← normalRadial_eq_upstairs]

end DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient

end
