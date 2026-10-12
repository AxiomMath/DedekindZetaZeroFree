module

public import DedekindZetaZeroFree.Eisenstein.Sections.FlatRightWordJets

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff Matrix.Norms.Operator
open Filter
namespace DedekindZetaZeroFree.KPActualReflectionData.NativeFlowJet
open KPGlobalResidualConstruction KPContinuation.ChamberFlatSource
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def flowMatrix (b : KPSmoothActualFlowData.B F) (t : ℝ) (w : NumberField.InfinitePlace F) :
    Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  KPSmoothActualFlowData.matrixExponential
    (KPSmoothActualFlowData.sl2Matrix (fun j => if (w,j) = b then t else 0))

def flowChart (b : KPSmoothActualFlowData.B F) (t : ℝ) : ArchCoordinates F :=
  fun w => ChartMatrix.chartCoordinates (flowMatrix F b t w).val

 theorem flowMatrix_zero (b : KPSmoothActualFlowData.B F) (w : NumberField.InfinitePlace F) :
    flowMatrix F b 0 w = 1 := by
  apply Units.ext
  change NormedSpace.exp _ = (1 : Matrix (Fin 2) (Fin 2) ℂ)
  rw [show KPSmoothActualFlowData.sl2Matrix (fun j => if (w,j) = b then (0 : ℝ) else 0) = 0 by
    ext i j; fin_cases i <;> fin_cases j <;> simp [KPSmoothActualFlowData.sl2Matrix]]
  exact NormedSpace.exp_zero

@[simp] theorem flowChart_zero (b : KPSmoothActualFlowData.B F) : flowChart F b 0 = archBase F := by
  funext w i
  rw [flowChart, flowMatrix_zero]
  fin_cases i <;> simp [ChartMatrix.chartCoordinates, archBase]

private theorem flowEntry_smooth (b : KPSmoothActualFlowData.B F)
    (w : NumberField.InfinitePlace F) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t w).val i j) := by
  letI : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAlgebra
  let L : ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    { toFun := fun t => KPSmoothActualFlowData.sl2Matrix (fun j => if (w,j) = b then t else 0)
      map_add' := by intro x y; ext i j; fin_cases i <;> fin_cases j <;>
        simp [KPSmoothActualFlowData.sl2Matrix]; all_goals split_ifs <;> simp <;> ring
      map_smul' := by intro x y; ext i j; fin_cases i <;> fin_cases j <;>
        simp [KPSmoothActualFlowData.sl2Matrix]; all_goals split_ifs <;> simp <;> ring }
  let ev : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have he : ContDiff ℝ (⊤ : ℕ∞) (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ → _) :=
    (show AnalyticOnNhd ℝ (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ → _) Set.univ from
      fun _ _ => NormedSpace.exp_analytic _).contDiff
  exact ev.toContinuousLinearMap.contDiff.comp (he.comp L.toContinuousLinearMap.contDiff)

theorem flowChart_smooth (b : KPSmoothActualFlowData.B F) :
    ContDiffAt ℝ (⊤ : ℕ∞) (flowChart F b) 0 := by
  apply contDiffAt_pi.mpr
  intro w
  apply contDiffAt_pi.mpr
  intro i
  have hc (i j : Fin 2) : ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t w).val i j) 0 :=
    (flowEntry_smooth F b w i j).contDiffAt
  have hn : (flowMatrix F b 0 w).val 1 1 ≠ 0 := by rw [flowMatrix_zero]; simp
  fin_cases i <;> simp only [flowChart, ChartMatrix.chartCoordinates, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  · simpa only [div_eq_mul_inv] using! (hc 0 1).mul ((hc 1 1).inv hn)
  · simp only [Matrix.det_fin_two]
    simpa only [div_eq_mul_inv] using! (((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))).mul
      (((hc 1 1).pow 2).inv (pow_ne_zero _ hn))
  · simpa only [div_eq_mul_inv] using! (hc 1 0).mul ((hc 1 1).inv hn)

def flowDirection (b : KPSmoothActualFlowData.B F) : ArchCoordinates F := deriv (flowChart F b) 0

theorem flowChart_hasDeriv (b : KPSmoothActualFlowData.B F) :
    HasDerivAt (flowChart F b) (flowDirection F b) 0 :=
  ((flowChart_smooth F b).differentiableAt (by simp)).hasDerivAt

theorem flowChart_reconstruct (b : KPSmoothActualFlowData.B F) :
    ∀ᶠ t in nhds (0 : ℝ), archChart F ζ hζ (flowChart F b t) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t) := by
  have hn : ∀ᶠ t in nhds (0 : ℝ), ∀ w : NumberField.InfinitePlace F,
      (flowMatrix F b t w).val 1 1 ≠ 0 := by
    rw [Filter.eventually_all]
    intro w
    exact (flowEntry_smooth F b w 1 1).continuous.continuousAt.eventually_ne
      (by rw [flowMatrix_zero]; simp)
  filter_upwards [hn] with t ht
  rw [ChartMatrix.archChart_eq_insertion_chartMatrix]
  congr 1
  funext w
  exact ChartMatrix.chartCoordinates_reconstruct (flowMatrix F b t w) (ht w)

end DedekindZetaZeroFree.KPActualReflectionData.NativeFlowJet

end
