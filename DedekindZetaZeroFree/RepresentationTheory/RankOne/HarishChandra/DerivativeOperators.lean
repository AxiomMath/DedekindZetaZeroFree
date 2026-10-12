module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.HolomorphicKTypeGeneration
public import DedekindZetaZeroFree.Theta.Profiles.LocalTensorActions
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.FiniteDegreeEnergyEstimates

@[expose] public section

noncomputable section
open scoped Classical Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeComplexHCOperators
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPContHolomorphicKGeneration
 abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
private theorem inv_open : IsOpen {m : Mat | m.det ≠ 0} :=
  isOpen_ne.preimage (by fun_prop : Continuous (fun m : Mat => m.det))
 theorem mf_gl (f : ComplexGL2 → ℂ) (g : ComplexGL2) : matrixFunction f (g : Mat) = f g := by
  simp only [matrixFunction]
  rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero g)]
  congr 1
  exact Units.ext rfl
 theorem mf_add (f h : ComplexGL2 → ℂ) : matrixFunction (f+h) = matrixFunction f + matrixFunction h := by
  funext m
  simp only [matrixFunction, Pi.add_apply]
  split <;> simp
 theorem mf_smul (c : ℂ) (f : ComplexGL2 → ℂ) : matrixFunction (c • f) = c • matrixFunction f := by
  funext m
  simp only [matrixFunction, Pi.smul_apply]
  split <;> simp
 theorem mf_diff (s : ℝ) (f : PrincipalSeries s) (g : ComplexGL2) :
    DifferentiableAt ℝ (matrixFunction (f : ComplexGL2 → ℂ)) (g : Mat) :=
  ((((principalSeries_mem_iff s _).mp f.property).2).contDiffAt
    (inv_open.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g))).differentiableAt (by simp)

def derivative (s : ℝ) (X : Mat) : Module.End ℂ (PrincipalSeries s) where
  toFun := rightLieDerivative s X
  map_add' f h := by
    apply Subtype.ext
    funext g
    change rightLieFunction X (f+h) g = rightLieFunction X f g + rightLieFunction X h g
    rw [rightLieFunction, mf_add, fderiv_add (mf_diff s f g) (mf_diff s h g)]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext g
    change rightLieFunction X (c • f) g = c • rightLieFunction X f g
    rw [rightLieFunction, mf_smul, fderiv_const_smul (mf_diff s f g) c]
    rfl

@[simp] theorem derivative_apply (s : ℝ) (X : Mat) (f : PrincipalSeries s) (g : ComplexGL2) :
    derivative s X f g = rightLieFunction X f g := rfl

open scoped Matrix.Norms.Operator in

theorem hasDerivAt_flow (s : ℝ) (X : Mat) (f : PrincipalSeries s) (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X)))
      (derivative s X f g) 0 := by
  have hm : HasDerivAt (fun t : ℝ => (g : Mat) * NormedSpace.exp ((t : ℂ) • X))
      ((g : Mat) * X) 0 := by
    have h := (((hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (f := fun t : ℝ => (t : ℂ)) 0 Complex.ofRealCLM.hasDerivAt)
    have ht := h.const_mul (g : Mat)
    change HasDerivAt (fun t : ℝ => (g : Mat) * NormedSpace.exp ((t : ℂ) • X))
      ((g : Mat) * ((1 : ℂ) • (NormedSpace.exp ((0 : ℂ) • X) * X))) 0 at ht
    simpa only [one_smul, zero_smul, NormedSpace.exp_zero, one_mul] using ht
  have hc := (mf_diff s f g).hasFDerivAt.comp_hasDerivAt_of_eq 0 hm (by simp)
  have heq : (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) =
      matrixFunction f ∘ (fun t : ℝ => (g : Mat) * NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    exact (mf_gl f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))).symm
  rw [heq]
  exact hc

def direction (s : ℝ) (f : PrincipalSeries s) : Mat →ₗ[ℝ] PrincipalSeries s where
  toFun X := derivative s X f
  map_add' X Y := by
    apply Subtype.ext
    funext g
    simp only [derivative_apply, rightLieFunction, Matrix.mul_add, map_add]
    rfl
  map_smul' c X := by
    apply Subtype.ext
    funext g
    simp only [derivative_apply, rightLieFunction, Matrix.mul_smul, map_smul]
    rfl

private theorem cartan_derivative (s : ℝ) (b : KPSmoothCoreCasimirEnergy.LocalBasis)
    (f : PrincipalSeries s) :
    derivative s (KPSmoothCoreCasimirEnergy.cartanMatrix b) f =
      KPSmoothCoreCasimirEnergy.localDerivative s b f := by
  apply Subtype.ext
  funext g
  exact (hasDerivAt_flow s _ f g).deriv.symm

theorem derivative_preserves_harmonic_core (s : ℝ) (X : Mat) (hX : Matrix.trace X = 0)
    (f : PrincipalSeries s) (hf : f ∈ KPSmoothCoreCasimirEnergy.localHC s) :
    derivative s X f ∈ KPSmoothCoreCasimirEnergy.localHC s := by
  obtain ⟨c, hc⟩ := KPSmoothCoreCasimirEnergy.cartan_basis_normalization.2.2.2.2.2 X hX
  have hreal : X = ∑ b, c b • KPSmoothCoreCasimirEnergy.cartanMatrix b := by
    exact hc
  change direction s f X ∈ KPSmoothCoreCasimirEnergy.localHC s
  rw [hreal, map_sum]
  apply Submodule.sum_mem
  intro b hb
  rw [map_smul]
  rw [← algebraMap_smul ℂ (c b)]
  apply (KPSmoothCoreCasimirEnergy.localHC s).smul_mem
  rw [show direction s f (KPSmoothCoreCasimirEnergy.cartanMatrix b) =
    KPSmoothCoreCasimirEnergy.localDerivative s b f from cartan_derivative s b f]
  exact KPSmoothCoreCasimirEnergy.local_derivative_preserves_HC s b ⟨f, hf⟩

theorem basisMatrix_trace_zero (i : Fin 6) : Matrix.trace (KPSmoothActualFlowData.basisMatrix i) = 0 := by
  simp [Matrix.trace, Fin.sum_univ_two, KPSmoothActualFlowData.basisMatrix,
    KPSmoothActualFlowData.sl2Matrix]

theorem derivative_preserves_complexCore (i : Fin 6) (f : complexCore) :
    derivative negativeParameter (KPSmoothActualFlowData.basisMatrix i) f.val ∈ complexCore := by
  have heq : complexCore = KPSmoothCoreCasimirEnergy.localHC negativeParameter := by
    simp only [complexCore, KPCplxActualImage.imageSubmodule_eq_top, top_inf_eq,
      KPSmoothCoreCasimirEnergy.localHC]
  have hf : f.val ∈ KPSmoothCoreCasimirEnergy.localHC negativeParameter := by
    simpa only [heq] using f.property
  simpa only [← heq] using
    derivative_preserves_harmonic_core _ _ (basisMatrix_trace_zero i) f.val hf

def operators (i : Fin 6) : Module.End ℂ complexCore :=
  (derivative negativeParameter (KPSmoothActualFlowData.basisMatrix i)).restrict
    (fun f hf => derivative_preserves_complexCore i ⟨f, hf⟩)

theorem operators_hasDerivAt (i : Fin 6) (f : complexCore) (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => f.val.val
      (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • KPSmoothActualFlowData.basisMatrix i)))
      ((operators i f).val.val g) 0 := hasDerivAt_flow _ _ _ _

end DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeComplexHCOperators

end
