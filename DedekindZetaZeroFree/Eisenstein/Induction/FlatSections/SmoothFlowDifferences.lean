module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Complex.OperatorWordBounds

@[expose] public section

noncomputable section
open scoped Classical Topology Matrix.Norms.Operator
open Filter
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts KPCplxCharacterHaar
open _root_.DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve renaming instNormedAddCommGroupHarmonicLieRawMat → instNormedAddCommGroupRawMat
open _root_.DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve renaming instNormedSpaceRealHarmonicLieRawMat → instNormedSpaceRealRawMat
attribute [-instance] instNormedAddCommGroupRawMat instNormedSpaceRealRawMat
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem source_flow_smooth_operator (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ=>(KPSmoothActualFlowData.matrixExponential ((t:ℂ) • X) : Matrix (Fin 2) (Fin 2) ℂ)) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ=>NormedSpace.exp ((t:ℂ) • X))
  have hh : ContDiff ℝ (⊤ : ℕ∞) (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) :=
    contDiff_iff_contDiffAt.mpr (fun a=>(NormedSpace.exp_analytic (𝕂:=ℝ) a).contDiffAt)
  exact hh.comp (Complex.ofRealCLM.contDiff.smul contDiff_const)

theorem source_flow_entry (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ=>(KPSmoothActualFlowData.matrixExponential ((t:ℂ) • X) : Matrix (Fin 2) (Fin 2) ℂ) i j) := by
  let ev : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ :=
    { toFun := fun a=>a i j
      map_add' := by intros;rfl
      map_smul' := by intros;rfl
      cont := (continuous_apply j).comp (continuous_apply i) }
  exact ev.contDiff.comp (source_flow_smooth_operator X)

open scoped Matrix.Norms.Elementwise in
theorem source_flow_smooth (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ=>(KPSmoothActualFlowData.matrixExponential ((t:ℂ) • X) : Matrix (Fin 2) (Fin 2) ℂ)) :=
  contDiff_pi.mpr (fun i=>contDiff_pi.mpr (fun j=>source_flow_entry X i j))

theorem source_flow_difference (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) (f : PrincipalSeries s) :
    Tendsto (fun t : ℝ=>(t:ℂ)⁻¹ •
      (KPCplxPrincipalSeriesCharts.rightTranslate s (KPSmoothActualFlowData.matrixExponential ((t:ℂ) • X)) f-f))
      (𝓝[≠] 0) (𝓝 (NativeComplexHCOperators.derivative s X f)) := by
  have hz : KPSmoothActualFlowData.matrixExponential ((0:ℂ) • X)=1 := by
    apply Units.ext
    simp [KPSmoothActualFlowData.matrixExponential]
  obtain ⟨D,hD,hd⟩ := KPCplxLoweringOrbitDifferentiation.smooth_matrix_orbit_derivative s
    (fun t=>KPSmoothActualFlowData.matrixExponential ((t:ℂ) • X)) (source_flow_smooth X) hz f
  have he : D=NativeComplexHCOperators.derivative s X f := by
    apply Subtype.ext
    funext g
    exact (hd g).unique (NativeComplexHCOperators.hasDerivAt_flow s X f g)
  simpa only [he] using hD
attribute [instance] instNormedAddCommGroupRawMat instNormedSpaceRealRawMat
end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
