module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSectionContinuityAndExponentialJets
public import DedekindZetaZeroFree.Eisenstein.Sections.FullProductFlatFamily
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions

@[expose] public section

noncomputable section
open scoped Classical NumberField Matrix

namespace DedekindZetaZeroFree.KPContinuation.ChamberFlatSource
namespace ChartMatrix

open KPAdelicCoverRestrictedProduct
open NumberField

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def diagonalUnit (x : ℂ) : ℂˣ := if h : x = 0 then 1 else Units.mk0 x h

def chartMatrix (x : Fin 3 → ℂ) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  KubotaRankTwo.n ℂ (x 0) * KubotaRankTwo.d ℂ (diagonalUnit (x 1)) 1 *
    KPStandardLocalRootLifts.lowerN ℂ (x 2)

theorem chartMatrix_val (x : Fin 3 → ℂ) (hx : x 1 ≠ 0) :
    (chartMatrix x).val = !![x 1 + x 0 * x 2, x 0; x 2, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chartMatrix, diagonalUnit, hx,
    KPStandardLocalRootLifts.lowerN, Matrix.mul_apply, Fin.sum_univ_two]

 def sectionTuple (r : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    RestrictedCover F ζ hζ :=
  ⟨fun v => match v with
    | Sum.inl w => KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
        (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom (r w))
    | Sum.inr _ => 1,
    Filter.Eventually.of_forall (by intro v; cases v <;> simp [compact])⟩

private theorem tuple_prod (a : RestrictedCover F ζ hζ)
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
      by_cases h : x = w
      · subst x; simp
      · simp [Pi.mulSingle_apply, Sum.inl_injective.ne h, h]
    rw [he]
    rw [List.prod_map_eq_pow_single w _ (by intro x hx _; simp [hx])]
    rw [List.nodup_iff_count_le_one.mp (Finset.nodup_toList _) w |>.antisymm
      (Nat.succ_le_of_lt (List.count_pos_iff.mpr (by simp)))]
    simp
  | inr q =>
    simp [ha, localToRestricted, Function.comp_def, RestrictedProduct.coe_mulSingle_apply,
      Pi.mulSingle_apply]

private theorem sectionTuple_insertion
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

private theorem mapped_diagonalUnit (w : InfinitePlace F) (x : ℂ) :
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
    apply Units.ext; rfl

private theorem sectionTuple_right (x : KPGlobalResidualConstruction.ArchCoordinates F) :
    scalarQuotient F ζ hζ (amalgamation F ζ hζ
      (sectionTuple F ζ hζ (fun w => chartMatrix (x w)))) =
      KPGlobalResidualConstruction.archChart F ζ hζ x := by
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inr q => rfl
  | inl w =>
    change complexSectionHom F ζ hζ w (chartMatrix (x w)) = _
    simp only [chartMatrix, map_mul]
    congr 1
    · congr 1
      · simp [complexSectionHom, KPStandardLocalRootLifts.N, KPLocalCover.sectionMap]
        apply Matrix.GeneralLinearGroup.ext; intro i j; fin_cases i <;> fin_cases j <;>
          simp [Matrix.GeneralLinearGroup.map]
      · simp [complexSectionHom, KPStandardLocalRootLifts.A, KPLocalCover.sectionMap]
        rw [← mapped_diagonalUnit F ζ hζ w (x w 1)]
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map]
    · simp [complexSectionHom, KPStandardLocalRootLifts.LowerN, KPLocalCover.sectionMap]
      apply Matrix.GeneralLinearGroup.ext; intro i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.map, KPStandardLocalRootLifts.lowerN]

theorem archChart_eq_insertion_chartMatrix
    (x : KPGlobalResidualConstruction.ArchCoordinates F) :
    KPGlobalResidualConstruction.archChart F ζ hζ x =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (chartMatrix (x w))) := by
  rw [← sectionTuple_right F ζ hζ x, sectionTuple_insertion F ζ hζ]

end ChartMatrix
end DedekindZetaZeroFree.KPContinuation.ChamberFlatSource

end

section

noncomputable section
open scoped Classical NumberField BigOperators Topology ContDiff Matrix Matrix.Norms.Operator

namespace DedekindZetaZeroFree.KPContinuation.ChamberFlatSource

namespace ChartMatrix

open KPAdelicCoverRestrictedProduct
open NumberField

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def chartCoordinates (M : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℂ :=
  ![M 0 1 / M 1 1, M.det / (M 1 1) ^ 2, M 1 0 / M 1 1]

theorem chartCoordinates_nonzero (M : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hM : M.val 1 1 ≠ 0) : chartCoordinates M.val 1 ≠ 0 := by
  simp only [chartCoordinates, Matrix.cons_val_one, Matrix.cons_val_zero]
  exact div_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero M) (pow_ne_zero _ hM)

theorem chartCoordinates_reconstruct (M : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hM : M.val 1 1 ≠ 0) :
    Matrix.ProjGenLinGroup.mk (chartMatrix (chartCoordinates M.val)) =
      Matrix.ProjGenLinGroup.mk M := by
  have he : chartMatrix (chartCoordinates M.val) =
      M * Matrix.GeneralLinearGroup.scalar (Fin 2) ((Units.mk0 (M.val 1 1) hM)⁻¹) := by
    apply Matrix.GeneralLinearGroup.ext
    rw [chartMatrix_val _ (chartCoordinates_nonzero M hM)]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Units.val_inv_eq_inv_val, Units.val_mk0]
    all_goals simp [chartCoordinates, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.scalar]
    all_goals field_simp <;> ring
  rw [he, map_mul, Matrix.ProjGenLinGroup.mk_scalar, mul_one]

end ChartMatrix

open KPGlobalResidualConstruction
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private def flowMatrix (b : KPSmoothActualFlowData.B F) (t : ℝ)
    (v : NumberField.InfinitePlace F) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  KPSmoothActualFlowData.matrixExponential
    (KPSmoothActualFlowData.sl2Matrix (fun j => if (v,j) = b then t else 0))
private def theta (b : KPSmoothActualFlowData.B F) (t : ℝ) : ArchCoordinates F :=
  fun v => ChartMatrix.chartCoordinates (flowMatrix F b t v).val
private theorem flowMatrix_zero (b : KPSmoothActualFlowData.B F) (v : NumberField.InfinitePlace F) :
    flowMatrix F b 0 v = 1 := by
  apply Units.ext
  change (NormedSpace.exp _) = (1 : Matrix (Fin 2) (Fin 2) ℂ)
  rw [show KPSmoothActualFlowData.sl2Matrix (fun j => if (v,j) = b then (0 : ℝ) else 0) = 0 by
    ext i j; fin_cases i <;> fin_cases j <;> simp [KPSmoothActualFlowData.sl2Matrix]]
  exact NormedSpace.exp_zero
private theorem theta_zero (b : KPSmoothActualFlowData.B F) : theta F b 0 = archBase F := by
  funext v i
  rw [theta, flowMatrix_zero]
  fin_cases i <;> simp [ChartMatrix.chartCoordinates, archBase]
private theorem flowEntry_smooth (b : KPSmoothActualFlowData.B F)
    (v : NumberField.InfinitePlace F) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val i j) := by
  letI : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAlgebra
  let L : ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    { toFun := fun t => KPSmoothActualFlowData.sl2Matrix (fun j => if (v,j) = b then t else 0)
      map_add' := by intro x y; ext i j; fin_cases i <;> fin_cases j <;>
        simp [KPSmoothActualFlowData.sl2Matrix]; all_goals split_ifs <;> simp <;> ring
      map_smul' := by intro x y; ext i j; fin_cases i <;> fin_cases j <;>
        simp [KPSmoothActualFlowData.sl2Matrix]; all_goals split_ifs <;> simp <;> ring }
  let ev : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have he : ContDiff ℝ (⊤ : ℕ∞) (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ → _) :=
    (show AnalyticOnNhd ℝ (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ → _) Set.univ from fun _ _ => NormedSpace.exp_analytic _).contDiff
  exact ev.toContinuousLinearMap.contDiff.comp (he.comp L.toContinuousLinearMap.contDiff)

private theorem theta_smooth (b : KPSmoothActualFlowData.B F) :
    ContDiffAt ℝ (⊤ : ℕ∞) (theta F b) 0 := by
  apply contDiffAt_pi.mpr; intro v
  apply contDiffAt_pi.mpr; intro i
  have hc (i j : Fin 2) : ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val i j) 0 :=
    (flowEntry_smooth F b v i j).contDiffAt
  have hn : (flowMatrix F b 0 v).val 1 1 ≠ 0 := by rw [flowMatrix_zero]; simp
  fin_cases i <;> simp only [theta, ChartMatrix.chartCoordinates, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  · change ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val 0 1 / (flowMatrix F b t v).val 1 1) 0
    simpa only [div_eq_mul_inv] using! (hc 0 1).mul ((hc 1 1).inv hn)
  · change ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val.det / (flowMatrix F b t v).val 1 1 ^ 2) 0
    simp only [Matrix.det_fin_two]
    simpa only [div_eq_mul_inv] using! (((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))).mul
      (((hc 1 1).pow 2).inv (pow_ne_zero _ hn))
  · change ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val 1 0 / (flowMatrix F b t v).val 1 1) 0
    simpa only [div_eq_mul_inv] using! (hc 1 0).mul ((hc 1 1).inv hn)
private theorem theta_chart (b : KPSmoothActualFlowData.B F) :
    ∀ᶠ t in nhds (0 : ℝ), KPGlobalResidualConstruction.archChart F ζ hζ (theta F b t) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t) := by
  have hn : ∀ᶠ t in nhds (0 : ℝ), ∀ v : NumberField.InfinitePlace F,
      (flowMatrix F b t v).val 1 1 ≠ 0 := by
    rw [Filter.eventually_all]
    intro v
    have hc : ContinuousAt (fun t => (flowMatrix F b t v).val 1 1) 0 :=
      (flowEntry_smooth F b v 1 1).continuous.continuousAt
    exact hc.eventually_ne (by rw [flowMatrix_zero]; simp)
  filter_upwards [hn] with t ht
  rw [ChartMatrix.archChart_eq_insertion_chartMatrix]
  congr 1
  funext v
  exact ChartMatrix.chartCoordinates_reconstruct (flowMatrix F b t v) (ht v)
private def chartProduct (p : ArchCoordinates F × ArchCoordinates F) : ArchCoordinates F := fun q =>
  ![p.1 q 0 + p.1 q 1 * p.2 q 0 / (1 + p.1 q 2 * p.2 q 0),
    p.1 q 1 * p.2 q 1 / (1 + p.1 q 2 * p.2 q 0)^2,
    p.2 q 2 + p.1 q 2 * p.2 q 1 / (1 + p.1 q 2 * p.2 q 0)]
private theorem chartProduct_base_right (x : ArchCoordinates F) :
    chartProduct F (x,archBase F) = x := by
  funext q i
  fin_cases i <;> simp [chartProduct, archBase]
private def transport (b : KPSmoothActualFlowData.B F) (p : ArchCoordinates F × ℝ) : ArchCoordinates F :=
  chartProduct F (p.1, theta F b p.2)
private def field (b : KPSmoothActualFlowData.B F) (x : ArchCoordinates F) : ArchCoordinates F :=
  fderiv ℝ (transport F b) (x,0) (0,1)
private theorem transport_zero (b : KPSmoothActualFlowData.B F) (x : ArchCoordinates F) :
    transport F b (x,0) = x := by
  simp [transport, theta_zero, chartProduct_base_right]
private theorem transport_smooth (b : KPSmoothActualFlowData.B F)
    (V : Set (ArchCoordinates F)) (hVo : IsOpen V) (hb : archBase F ∈ V)
    (hμ : ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (V ×ˢ V)) (x : ArchCoordinates F) (hx : x ∈ V) :
    ContDiffAt ℝ (⊤ : ℕ∞) (transport F b) (x,0) := by
  have hpair : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ArchCoordinates F × ℝ => (p.1,theta F b p.2)) (x,0) :=
    contDiffAt_fst.prodMk ((theta_smooth F b).comp (x,0) contDiffAt_snd)
  exact (hμ.contDiffAt ((hVo.prod hVo).mem_nhds ⟨hx, by simpa [theta_zero] using hb⟩)).comp (x,0) hpair
private theorem field_smooth (b : KPSmoothActualFlowData.B F)
    (V : Set (ArchCoordinates F)) (hVo : IsOpen V) (hb : archBase F ∈ V)
    (hμ : ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (V ×ˢ V)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (field F b) V := by
  intro x hx
  have ht := transport_smooth F b V hVo hb hμ x hx
  have hd := (ht.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).comp x
    (contDiffAt_id.prodMk contDiffAt_const)
  exact (hd.clm_apply contDiffAt_const).contDiffWithinAt
private theorem transport_hasDeriv (b : KPSmoothActualFlowData.B F)
    (V : Set (ArchCoordinates F)) (hVo : IsOpen V) (hb : archBase F ∈ V)
    (hμ : ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (V ×ˢ V)) (x : ArchCoordinates F) (hx : x ∈ V) :
    HasDerivAt (fun t => transport F b (x,t)) (field F b x) 0 := by
  have ht := (transport_smooth F b V hVo hb hμ x hx).differentiableAt (by simp)
  exact ht.hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_const 0 x).prodMk (hasDerivAt_id 0))

section Generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem variable_jet_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : E → ℂ) (n : ℕ) (d : Fin n → E → E)
    (x v : E) (hu : ContDiffAt ℝ (⊤ : ℕ∞) u x)
    (hd : ∀ i, DifferentiableAt ℝ (d i) x) :
    fderiv ℝ (fun y => iteratedFDeriv ℝ n u y (fun i => d i y)) x v =
      iteratedFDeriv ℝ (n+1) u x (Fin.cons v (fun i => d i x)) +
        ∑ i, iteratedFDeriv ℝ n u x (Function.update (fun i => d i x) i (fderiv ℝ (d i) x v)) := by
  have ht : DifferentiableAt ℝ (iteratedFDeriv ℝ n u) x :=
    (hu.iteratedFDeriv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  have hh := (ht.hasFDerivAt.continuousMultilinearMap_apply (fun i => (hd i).hasFDerivAt)).fderiv
  rw [hh]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousMultilinearMap.apply_apply, ContinuousLinearMap.sum_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply]
  rw [iteratedFDeriv_succ_apply_left]
  simp
private def coordWord {ι : Type*} (fields : ι → E → E) : List ι → (E → ℂ) → E → ℂ
  | [], u => u
  | b :: w, u => fun x => fderiv ℝ (coordWord fields w u) x (fields b x)
private theorem coordWord_smooth {ι : Type*} (fields : ι → E → E) (U : Set E)
    (hU : IsOpen U) (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (w : List ι) (u : E → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordWord fields w u) U := by
  induction w with
  | nil => exact hu
  | cons b w ih => exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply (hf b)
private def directionJet (t : Σ n : ℕ, Fin n → E → E) (u : E → ℂ) (x : E) : ℂ :=
  iteratedFDeriv ℝ t.1 u x (fun i => t.2 i x)
private theorem list_fderiv {α : Type*} (ts : List α) (f : α → E → ℂ) (x : E)
    (hf : ∀ t ∈ ts, DifferentiableAt ℝ (f t) x) :
    HasFDerivAt (fun y => (ts.map (fun t => f t y)).sum)
      (ts.map (fun t => fderiv ℝ (f t) x)).sum x := by
  induction ts with
  | nil => simpa using hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) x
  | cons t ts ih =>
    exact ((hf t (by simp)).hasFDerivAt.fun_add
      (ih (fun r hr => hf r (by simp [hr]))))
private theorem coordWord_expansion {ι : Type*} (fields : ι → E → E) (U : Set E)
    (hU : IsOpen U) (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U) (w : List ι) :
    ∃ ts : List (Σ n : ℕ, Fin n → E → E),
      (∀ t ∈ ts, t.1 ≤ w.length ∧ ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (t.2 i) U) ∧
      ∀ u : E → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) u U → ∀ x ∈ U,
        coordWord fields w u x = (ts.map (fun t => directionJet t u x)).sum := by
  induction w with
  | nil =>
    refine ⟨[⟨0, Fin.elim0⟩], ?_, ?_⟩
    · intro t ht; simp only [List.mem_singleton] at ht; subst t
      exact ⟨by simp, fun i => Fin.elim0 i⟩
    · intro u hu x hx; simp [coordWord, directionJet]
  | cons b w ih =>
    obtain ⟨ts, hts, heq⟩ := ih
    let expand : (Σ n : ℕ, Fin n → E → E) → List (Σ n : ℕ, Fin n → E → E) := fun t =>
      ⟨t.1+1, Fin.cons (fields b) t.2⟩ :: (List.finRange t.1).map (fun i =>
        ⟨t.1, Function.update t.2 i (fun x => fderiv ℝ (t.2 i) x (fields b x))⟩)
    refine ⟨ts.flatMap expand, ?_, ?_⟩
    · intro t ht
      obtain ⟨r, hr, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨hn, hd⟩ := hts r hr
      simp only [expand, List.mem_cons, List.mem_map] at ht
      rcases ht with rfl | ⟨i, hi, rfl⟩
      · refine ⟨Nat.succ_le_succ hn, ?_⟩
        intro i; refine Fin.cases (hf b) (fun j => hd j) i
      · refine ⟨hn.trans (Nat.le_succ _), ?_⟩
        intro j
        by_cases h : j = i
        · subst j; simp only [Function.update_self]
          exact ((hd i).fderiv_of_isOpen hU (by simp)).clm_apply (hf b)
        · simpa only [Function.update_of_ne h] using hd j
    · intro u hu x hx
      have he : coordWord fields w u =ᶠ[nhds x]
          (fun y => (ts.map (fun t => directionJet t u y)).sum) :=
        Filter.Eventually.mono (hU.mem_nhds hx) (fun y hy => heq u hu y hy)
      simp only [coordWord]
      rw [he.fderiv_eq]
      have ht (t : Σ n : ℕ, Fin n → E → E) (hm : t ∈ ts) :
          DifferentiableAt ℝ (directionJet t u) x :=
        let huAt := hu.contDiffAt (hU.mem_nhds hx)
        let hjet : DifferentiableAt ℝ (iteratedFDeriv ℝ t.1 u) x :=
          (huAt.iteratedFDeriv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
        (hjet.hasFDerivAt.continuousMultilinearMap_apply (fun i =>
          ((((hts t hm).2 i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt)).differentiableAt
      rw [(list_fderiv ts (fun t => directionJet t u) x ht).fderiv]
      rw [show (ts.flatMap expand).map (fun t => directionJet t u x) =
          (ts.map (fun t => (expand t).map (fun r => directionJet r u x))).flatten by
        simp [List.flatMap, List.map_flatten, List.map_map, Function.comp_def]]
      rw [List.sum_flatten, List.map_map]
      rw [show ((ts.map (fun t => fderiv ℝ (directionJet t u) x)).sum) (fields b x) =
          (ts.map (fun t => fderiv ℝ (directionJet t u) x (fields b x))).sum by
        simpa only [List.map_map, Function.comp_def, ContinuousLinearMap.apply_apply] using
          map_list_sum (ContinuousLinearMap.apply ℝ ℂ (fields b x)) (ts.map (fun t => fderiv ℝ (directionJet t u) x))]
      congr 1
      apply List.map_congr_left
      intro t htmem
      change fderiv ℝ (fun y => iteratedFDeriv ℝ t.1 u y (fun i => t.2 i y)) x (fields b x) = _
      rw [variable_jet_derivative u t.1 t.2 x (fields b x)
        (hu.contDiffAt (hU.mem_nhds hx)) (fun i =>
          (((hts t htmem).2 i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
      simp only [expand, directionJet, List.map_cons, List.sum_cons, List.map_map,
        ← List.ofFn_eq_map, List.sum_ofFn]
      apply congrArg₂ (fun a b : ℂ => a + b)
      · congr 1; funext i; refine Fin.cases rfl (fun j => rfl) i
      · change _ = (List.map (fun r => iteratedFDeriv ℝ r.1 u x (fun i => r.2 i x))
          (List.ofFn (fun i : Fin t.1 => (⟨t.1, Function.update t.2 i
            (fun x => fderiv ℝ (t.2 i) x (fields b x))⟩ : Σ n : ℕ, Fin n → E → E)))).sum
        rw [List.map_ofFn, List.sum_ofFn]
        apply Finset.sum_congr rfl
        intro i hi
        congr 1; funext j
        by_cases h : j = i
        · subst j; simp
        · simp [h]

end Generic
private theorem literal_word_in_chart
    (φ : KPLiteralRaw.Flat F ζ hζ (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K)
    (V : Set (ArchCoordinates F)) (hVo : IsOpen V) (hb : archBase F ∈ V)
    (hVD : V ⊆ archDomain F)
    (hμ : ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (V ×ˢ V))
    (hprod : ∀ y ∈ V, ∀ x ∈ V, archChart F ζ hζ (chartProduct F (y,x)) =
      archChart F ζ hζ y * archChart F ζ hζ x)
    (w : List (KPSmoothActualFlowData.B F)) (s : ℂ) (g : KPLiteralRaw.G F ζ hζ) :
    ∀ x ∈ V,
      w.foldr (fun b v => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 v)
        (φ.val s) (g * archChart F ζ hζ x) =
      coordWord (field F) w (fun y => φ.val s (g * archChart F ζ hζ y)) x := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => φ.val s (g * archChart F ζ hζ y)) V :=
    (((φ.property.1 s).1.2.1 g)).mono hVD
  have hf := fun b => field_smooth F b V hVo hb hμ
  induction w with
  | nil => intro x hx; rfl
  | cons b w ih =>
    intro x hx
    let u := fun y => φ.val s (g * archChart F ζ hζ y)
    let q := coordWord (field F) w u
    have hq : ContDiffOn ℝ (⊤ : ℕ∞) q V := coordWord_smooth (field F) V hVo hf w u hu
    have hqt := ((hq.contDiffAt (hVo.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have htr := transport_hasDeriv F b V hVo hb hμ x hx
    have htr0 := transport_zero F b x
    have hder : HasDerivAt (fun t => q (transport F b (x,t)))
        (fderiv ℝ q x (field F b x)) 0 := by
      have hh := (show HasFDerivAt q (fderiv ℝ q x) (transport F b (x,0)) from htr0.symm ▸ hqt).comp_hasDerivAt 0 htr
      simpa only [htr0, Function.comp_def] using! hh
    have he : (fun t : ℝ =>
        w.foldr (fun b v => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 v)
          (φ.val s) ((g * archChart F ζ hζ x) *
            KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t)))
        =ᶠ[nhds 0] (fun t => q (transport F b (x,t))) := by
      have htV : ∀ᶠ t in nhds (0 : ℝ), theta F b t ∈ V :=
        (theta_smooth F b).continuousAt.eventually (by simpa [theta_zero] using hVo.mem_nhds hb)
      have hpV : ∀ᶠ t in nhds (0 : ℝ), transport F b (x,t) ∈ V :=
        htr.continuousAt.eventually (by simpa only [htr0] using (show ∀ᶠ y in nhds x, y ∈ V from hVo.mem_nhds hx))
      filter_upwards [theta_chart F ζ hζ b, htV, hpV] with t ht htV hpV
      rw [← ht, mul_assoc, ← hprod x hx (theta F b t) htV]
      exact ih (transport F b (x,t)) hpV
    change deriv _ 0 = fderiv ℝ q x (field F b x)
    rw [he.deriv_eq]
    exact hder.deriv

theorem actual_rightWord_jet_expansion_uniform
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : List (KPSmoothActualFlowData.B F)) :
    ∃ (n : ℕ) (a : Fin n → ℝ) (j : Fin n → KPGlobalResidualConstruction.Jet F),
      (∀ i, (j i).1 ≤ w.length) ∧
      ∀ (φ : KPLiteralRaw.Flat F ζ hζ (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K)
        (s : ℂ) (g : KPLiteralRaw.G F ζ hζ),
        w.foldr (fun b v => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 v)
          (φ.val s) g =
            ∑ i, (a i : ℂ) * KPLiteralChamber.rightJet F ζ hζ (j i) (φ.val s) g := by
  obtain ⟨V, hVo, hb, hVD, hμ, hmaps, hprod, hthick, hcomm⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product F ζ hζ
  change ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (V ×ˢ V) at hμ
  change ∀ y ∈ V, ∀ x ∈ V, archChart F ζ hζ (chartProduct F (y,x)) =
    archChart F ζ hζ y * archChart F ζ hζ x at hprod
  obtain ⟨ts, hts, heq⟩ := coordWord_expansion (field F) V hVo
    (fun b => field_smooth F b V hVo hb hμ) w
  let j : Fin ts.length → Jet F := fun i =>
    ⟨(ts.get i).1, fun k => (ts.get i).2 k (archBase F)⟩
  refine ⟨ts.length, fun _ => 1, j, ?_, ?_⟩
  · intro i
    exact (hts (ts.get i) (List.get_mem ts i)).1
  · intro φ s g
    have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => φ.val s (g * archChart F ζ hζ y)) V :=
      (((φ.property.1 s).1.2.1 g)).mono hVD
    have hword := literal_word_in_chart F ζ hζ φ V hVo hb hVD hμ hprod w s g (archBase F) hb
    rw [KPInterface.ResidueConstruction.Raw.archChart_base, mul_one] at hword
    rw [hword, heq _ hu _ hb]
    simp only [Complex.ofReal_one, one_mul, KPLiteralChamber.rightJet]
    change (ts.map (fun t => directionJet t (fun y => φ.val s (g * archChart F ζ hζ y)) (archBase F))).sum = _
    conv_lhs => rw [← List.ofFn_get ts, List.map_ofFn, List.sum_ofFn]
    rfl

end DedekindZetaZeroFree.KPContinuation.ChamberFlatSource

end
end
