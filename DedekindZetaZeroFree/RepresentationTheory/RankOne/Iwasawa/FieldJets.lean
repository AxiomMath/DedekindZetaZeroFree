module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.BottomRowRadialContraction

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Matrix.Norms.Operator Classical
namespace DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes.IwasawaFieldJets
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming matrix_path_components → matrix_path_components
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming matrix_bottom_basis_jet → matrix_bottom_basis_jet
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming matrix_height_squared_basis_jet → matrix_height_squared_basis_jet
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming matrixHeightSquared → matrixHeightSquared
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming matrix_height_squared_action → matrix_height_squared_action
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming gl_bottom_nonzero → gl_bottom_nonzero
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming bottomRowJet → bottomRowJet

def bottomDenominator (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Complex.normSq (g 1 0) + Complex.normSq (g 1 1)

def bottomDenominatorJet (g : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 6) : ℝ :=
  ![2 * (Complex.normSq (g 1 0) - Complex.normSq (g 1 1)), 0,
    2 * (g 1 0 * star (g 1 1)).re, -2 * (g 1 0 * star (g 1 1)).im,
    2 * (g 1 0 * star (g 1 1)).re, 2 * (g 1 0 * star (g 1 1)).im] i

def horizontalNumerator (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  g 0 0 * star (g 1 0) + g 0 1 * star (g 1 1)

def horizontalNumeratorJet (g : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 6) : ℂ :=
  let h := g * KPSmoothActualFlowData.basisMatrix i
  h 0 0 * star (g 1 0) + g 0 0 * star (h 1 0) +
    (h 0 1 * star (g 1 1) + g 0 1 * star (h 1 1))

def horizontalFieldJet (g : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 6) : ℂ :=
  (horizontalNumeratorJet g i * (bottomDenominator g : ℂ) -
    horizontalNumerator g * (bottomDenominatorJet g i : ℂ)) /
      (bottomDenominator g : ℂ)^2

def verticalFieldJet (g : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 6) : ℝ :=
  -bottomDenominatorJet g i / bottomDenominator g

 theorem horizontalNumerator_hasDerivAt (g : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 6) :
    HasDerivAt (fun t : ℝ => horizontalNumerator
      (g * NormedSpace.exp ((t : ℂ) • KPSmoothActualFlowData.basisMatrix i)))
      (horizontalNumeratorJet g i) 0 := by
  have h := matrix_path_components g (KPSmoothActualFlowData.basisMatrix i)
  have hd := ((h 0 0).mul (h 1 0).star).add ((h 0 1).mul (h 1 1).star)
  convert hd using 1
  · funext t
    rfl
  · simp only [horizontalNumeratorJet, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one]

 theorem bottomDenominator_hasDerivAt (g : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 6) :
    HasDerivAt (fun t : ℝ => bottomDenominator
      (g * NormedSpace.exp ((t : ℂ) • KPSmoothActualFlowData.basisMatrix i)))
      (bottomDenominatorJet g i) 0 :=
  matrix_bottom_basis_jet g i

private theorem actual_horizontal_formula (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    (KPArch.action g (0,0)).1 = horizontalNumerator g / (bottomDenominator g : ℂ) := by
  simp [KPArch.action, KPArch.actionDenominator, KPArch.height,
    horizontalNumerator, bottomDenominator, Complex.sq_norm, add_comm]

theorem actual_horizontal_field_hasDerivAt
    (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (i : Fin 6) :
    HasDerivAt (fun t : ℝ => (KPArch.action
      (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • KPSmoothActualFlowData.basisMatrix i)) (0,0)).1)
      (horizontalFieldJet g i) 0 := by
  have hD := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (bottomDenominator_hasDerivAt g i)
  have hN := horizontalNumerator_hasDerivAt g i
  have hn : (bottomDenominator g : ℂ) ≠ 0 := by
    exact_mod_cast gl_bottom_nonzero g
  have h := hN.div hD (by simpa using hn)
  convert h using 1
  · funext t
    exact actual_horizontal_formula _
  · simp only [horizontalFieldJet, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero,
      mul_one, Complex.ofRealCLM_apply, Function.comp_def]

private theorem actual_vertical_formula (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    (KPArch.action g (0,0)).2 = Real.log (matrixHeightSquared g) / 2 := by
  rw [matrix_height_squared_action]
  rw [Real.log_exp]
  ring

theorem actual_vertical_field_hasDerivAt
    (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (i : Fin 6) :
    HasDerivAt (fun t : ℝ => (KPArch.action
      (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • KPSmoothActualFlowData.basisMatrix i)) (0,0)).2)
      (verticalFieldJet g i) 0 := by
  have hs := matrix_height_squared_basis_jet (g : Matrix (Fin 2) (Fin 2) ℂ) (gl_bottom_nonzero g) i
  have hn : matrixHeightSquared g ≠ 0 := by
    rw [matrix_height_squared_action]
    exact Real.exp_ne_zero _
  have hd := (hs.log (by simpa using hn)).div_const 2
  convert hd using 1
  · funext t
    exact actual_vertical_formula _
  · simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one]
    unfold verticalFieldJet bottomDenominatorJet bottomDenominator
    fin_cases i <;> simp [bottomRowJet] <;> field_simp <;> ring

theorem actual_six_field_hasDerivAt
    (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (i : Fin 6) :
    HasDerivAt (fun t : ℝ => KPArch.action
      (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • KPSmoothActualFlowData.basisMatrix i)) (0,0))
      (horizontalFieldJet g i, verticalFieldJet g i) 0 := by
  exact (actual_horizontal_field_hasDerivAt g i).prodMk (actual_vertical_field_hasDerivAt g i)
 theorem pgl_action_out (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : KPArch.H3) :
    KPArch.action (Matrix.ProjGenLinGroup.mk g).out z = KPArch.action g z := by
  obtain ⟨a,ha⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp
    (show Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk (Matrix.ProjGenLinGroup.mk g).out from
      (Quotient.out_eq _).symm)
  rw [← ha, (KPArch.action_laws g (Matrix.GeneralLinearGroup.scalar (Fin 2) a) z).2,
    KPArch.scalar_action]

open _root_.DedekindZetaZeroFree.KPArch renaming action_contDiff → action_contDiff

open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming flow_apply → flow_apply
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming projection_insertion → projection_insertion

end DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes.IwasawaFieldJets

end
