module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalCyclicity
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.TensorProducts.IntegralQuotientActions

@[expose] public section

noncomputable section
open scoped Classical Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.HCGeneration
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar KPCplxIntertwinerEigenvalues
open KPGlobalResidualConstruction NativeComplexHCOperators KPLiteralTensor
local notation "J" => KPCplxIntertwinerEigenvalues.standardIntertwiner
local notation "rt" => KPCplxPrincipalSeriesCharts.rightTranslate

def harmonicPlusDerivative (i : Fin 6) : Module.End ℂ harmonicPlus :=
  (derivative positiveParameter (KPSmoothActualFlowData.basisMatrix i)).restrict
    (fun f hf => by
      exact derivative_preserves_harmonic_core positiveParameter _
        (basisMatrix_trace_zero i) f hf)

theorem standardIntertwiner_native_orbit_derivative (β : ℂˣ)
    (γ : ℝ → ComplexGL2)
    (hγ : ContDiff ℝ (⊤ : ℕ∞) (fun t => (γ t : Matrix (Fin 2) (Fin 2) ℂ)))
    (hzero : γ 0 = 1)
    (f df : PrincipalSeries positiveParameter) (dh : PrincipalSeries negativeParameter)
    (hdf : ∀ g : ComplexGL2, HasDerivAt (fun t : ℝ => f (g * γ t)) (df g) 0)
    (hdh : ∀ g : ComplexGL2,
      HasDerivAt (fun t : ℝ => (standardIntertwiner β f) (g * γ t)) (dh g) 0) :
    standardIntertwiner β df = dh := by
  obtain ⟨D, hD, hscalar⟩ := KPCplxLoweringOrbitDifferentiation.smooth_matrix_orbit_derivative
    positiveParameter γ hγ hzero f
  have hDdf : D = df := by
    apply Subtype.ext
    funext g
    exact (hscalar g).unique (hdf g)
  subst D
  have heq (t : ℝ) :
      J β ((t : ℂ)⁻¹ • (rt positiveParameter (γ t) f - f)) =
      (t : ℂ)⁻¹ • (rt negativeParameter (γ t) (J β f) - J β f) := by
    rw [map_smul, map_sub, ← pi_mk, standardIntertwiner_equivariant, pi_mk]
  have hlimit := ((J β).continuous.tendsto df).comp hD
  simp only [Function.comp_def, heq] at hlimit
  apply KPCplxHarmonicPropagation.orbit_limit_eq_of_pointwise_derivative
    negativeParameter (fun t => Matrix.ProjGenLinGroup.mk (γ t))
    (by rw [hzero]; exact map_one _) (J β f)
  · simpa only [pi_mk] using hlimit
  · intro g
    simpa only [pi_mk, KPCplxPrincipalSeriesCharts.rightTranslate] using hdh g

theorem harmonicQuotient_native_orbit_derivative
    (γ : ℝ → ComplexGL2)
    (hγ : ContDiff ℝ (⊤ : ℕ∞) (fun t => (γ t : Matrix (Fin 2) (Fin 2) ℂ)))
    (hzero : γ 0 = 1)
    (f df : harmonicPlus) (dh : complexCore)
    (hdf : ∀ g : ComplexGL2, HasDerivAt (fun t : ℝ => f.val (g * γ t)) (df.val g) 0)
    (hdh : ∀ g : ComplexGL2, HasDerivAt
      (fun t : ℝ => (harmonicQuotient f).val (g * γ t)) (dh.val g) 0) :
    harmonicQuotient df = dh := by
  apply Subtype.ext
  exact standardIntertwiner_native_orbit_derivative (1 : ℂˣ) γ hγ hzero f.val df.val dh.val hdf hdh

open scoped Matrix.Norms.Operator in

theorem native_exponential_curve_smooth (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
      (KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X) : Matrix (Fin 2) (Fin 2) ℂ)) := by
  letI : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAlgebra
  have h : ContDiff ℝ (⊤ : ℕ∞) (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ → _) :=
    (show AnalyticOnNhd ℝ (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ → _) Set.univ from
      fun _ _ => NormedSpace.exp_analytic _).contDiff
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t : ℂ) • X) :=
    Complex.ofRealCLM.contDiff.smul contDiff_const
  have hc := h.comp hs
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  let ev : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun m => m i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact ev.toContinuousLinearMap.contDiff.comp hc

theorem harmonicPlusDerivative_intertwines (i : Fin 6) (f : harmonicPlus) :
    harmonicQuotient (harmonicPlusDerivative i f) =
      operators i (harmonicQuotient f) := by
  apply harmonicQuotient_native_orbit_derivative
    (fun t => KPSmoothActualFlowData.matrixExponential
      ((t : ℂ) • KPSmoothActualFlowData.basisMatrix i))
    (native_exponential_curve_smooth _) (by
      apply Units.ext
      change NormedSpace.exp ((↑(0 : ℝ) : ℂ) • KPSmoothActualFlowData.basisMatrix i) =
        (1 : Matrix (Fin 2) (Fin 2) ℂ)
      simp)
  · exact hasDerivAt_flow _ _ _
  · exact operators_hasDerivAt i (harmonicQuotient f)

def harmonicPlusGenerator : ComplexGenerator → Module.End ℂ harmonicPlus
  | Sum.inl k => FourierContinuation.TensorActionSource.harmonicSourceAction k
  | Sum.inr i => harmonicPlusDerivative i

theorem harmonicPlusGenerator_intertwines (a : ComplexGenerator) (f : harmonicPlus) :
    harmonicQuotient (harmonicPlusGenerator a f) = complexGenerator a (harmonicQuotient f) := by
  cases a with
  | inl k => exact FourierContinuation.TensorActionSource.harmonicSourceQuotient_intertwines k f
  | inr i => exact harmonicPlusDerivative_intertwines i f

end DedekindZetaZeroFree.FourierContinuation.HCGeneration

end
