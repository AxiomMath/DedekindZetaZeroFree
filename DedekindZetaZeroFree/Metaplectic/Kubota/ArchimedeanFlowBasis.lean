module

public import DedekindZetaZeroFree.Metaplectic.Kubota.PositiveFlowFirstJet
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.FiniteDegreeEnergyEstimates

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.RootDerivatives.FlowBasis
open KPGlobalResidualConstruction KPActualReflectionData.NativeFlowJet
variable (F : Type) [Field F] [NumberField F]
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open _root_.DedekindZetaZeroFree.KPSmoothCoreCasimirEnergy renaming matrix_path_hasDeriv_components → matrix_path_hasDeriv_components
private theorem flow_entry_hasDeriv
    (b : KPSmoothActualFlowData.B F) (w : NumberField.InfinitePlace F) (i j : Fin 2) :
    HasDerivAt (fun t : ℝ => (flowMatrix F b t w).val i j)
      ((if w = b.1 then KPSmoothActualFlowData.basisMatrix b.2 else 0) i j) 0 := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := if w = b.1 then KPSmoothActualFlowData.basisMatrix b.2 else 0
  have h := matrix_path_hasDeriv_components (1 : KPCplxCharacterHaar.ComplexGL2) M i j
  simp only [Units.val_one, one_mul] at h
  convert h using 1
  funext t
  change NormedSpace.exp (KPSmoothActualFlowData.sl2Matrix (fun k => if (w,k) = b then t else 0)) i j = NormedSpace.exp ((t : ℂ) • M) i j
  have he : KPSmoothActualFlowData.sl2Matrix (fun k => if (w,k) = b then t else 0) = (t : ℂ) • M := by
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp [KPSmoothActualFlowData.sl2Matrix, KPSmoothActualFlowData.basisMatrix, M, Prod.ext_iff]
    all_goals split_ifs <;> simp_all <;> ring
  rw [he]
open _root_.DedekindZetaZeroFree.KPActualReflectionData.NativeFlowJet renaming flowMatrix_zero → flowMatrix_zero
private theorem flow_direction_formula (b : KPSmoothActualFlowData.B F)
    (w : NumberField.InfinitePlace F) :
    flowDirection F b w = if w = b.1 then
      ![KPSmoothActualFlowData.basisMatrix b.2 0 1,
        2 * KPSmoothActualFlowData.basisMatrix b.2 0 0,
        KPSmoothActualFlowData.basisMatrix b.2 1 0] else 0 := by
  have hentry := flow_entry_hasDeriv F b w
  have hd := flowChart_hasDeriv F b
  have hw := (hasDerivAt_pi.mp hd) w
  funext i
  have hi := (hasDerivAt_pi.mp hw) i
  have h0 : (flowMatrix F b 0 w).val = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by rw [flowMatrix_zero]; rfl
  let M := if w = b.1 then KPSmoothActualFlowData.basisMatrix b.2 else 0
  have hden : (flowMatrix F b 0 w).val 1 1 ≠ 0 := by rw [h0]; simp
  have hh : HasDerivAt (fun t => (flowChart F b t w) i)
      (![M 0 1, M 0 0 - M 1 1, M 1 0] i) 0 := by
    fin_cases i
    · simpa [flowChart, KPContinuation.ChamberFlatSource.ChartMatrix.chartCoordinates, h0, M, Pi.div_apply]
        using! (hentry 0 1).div (hentry 1 1) hden
    · have hdet := ((hentry 0 0).mul (hentry 1 1)).sub ((hentry 0 1).mul (hentry 1 0))
      have h := hdet.div ((hentry 1 1).pow 2) (pow_ne_zero 2 hden)
      convert h using 1
      · funext t
        simp [flowChart, KPContinuation.ChamberFlatSource.ChartMatrix.chartCoordinates, Matrix.det_fin_two]
      · simp [h0, M]; ring
    · simpa [flowChart, KPContinuation.ChamberFlatSource.ChartMatrix.chartCoordinates, h0, M, Pi.div_apply]
        using! (hentry 1 0).div (hentry 1 1) hden
  rw [hi.unique hh]
  by_cases hw : w = b.1
  · simp [M, hw]
    fin_cases i <;> simp [KPSmoothActualFlowData.basisMatrix, KPSmoothActualFlowData.sl2Matrix] <;> ring
  · fin_cases i <;> simp [M, hw]

def coefficients (X : ArchCoordinates F) (b : KPSmoothActualFlowData.B F) : ℝ :=
  ![(X b.1 1).re / 2, (X b.1 1).im / 2, (X b.1 0).re, (X b.1 0).im,
    (X b.1 2).re, (X b.1 2).im] b.2

theorem directions_span (X : ArchCoordinates F) :
    X = ∑ b : KPSmoothActualFlowData.B F, coefficients F X b • flowDirection F b := by
  have hlocal (u w : NumberField.InfinitePlace F) (i : Fin 3) :
      (∑ j : Fin 6, coefficients F X (u,j) • flowDirection F (u,j) w i) =
        if u = w then X u i else 0 := by
    simp only [flow_direction_formula]
    by_cases hw : w = u
    · subst w
      fin_cases i <;>
        simp [coefficients, KPSmoothActualFlowData.basisMatrix,
          KPSmoothActualFlowData.sl2Matrix, Fin.sum_univ_six, Complex.real_smul,
          Complex.ext_iff] <;> constructor <;> ring
    · have huw : u ≠ w := Ne.symm hw
      simp [hw, huw]
  funext w i
  simp only [Finset.sum_apply, Pi.smul_apply, Fintype.sum_prod_type, hlocal,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
end DedekindZetaZeroFree.RootDerivatives.FlowBasis

end
