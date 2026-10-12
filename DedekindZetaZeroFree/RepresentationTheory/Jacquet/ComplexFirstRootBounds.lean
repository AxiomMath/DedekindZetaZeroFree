module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ComplexWhittakerLine

@[expose] public section

noncomputable section
attribute [local instance] ContinuousLinearMap.addCommGroup
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPActualReflectionData.StandardLocalSource
open NumberField KPReferenceChange.StandardComplexImage
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage
open KPInterface.ResidueConstruction.Raw
local instance : AddCommGroup (Theta frequency) := inferInstance
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F) (w : InfinitePlace F)

theorem complexJacquet_mem :
    KPCplxJacquetFunctional.thetaJacquetFunctional frequency ∈
      localWhittakerSpace _ (Theta frequency) (complexRootAction A w)
        (complexRawPsi w).toAddChar.toMonoidHom := by
  intro t h
  change (KPCplxJacquetFunctional.thetaJacquetFunctional frequency)
    (complexRootAction A w (Multiplicative.ofAdd t.toAdd) h) =
    (complexRawPsi w).toAddChar t.toAdd * _
  rw [complexRootAction_apply, complexRawPsi_trace, trace_character]
  exact KPCplxJacquetFunctional.thetaJacquetFunctional_covariance frequency _ _

private theorem scalar_of_line {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ V) (hW : Module.finrank ℂ W = 1) (J : V) (hJ : J ∈ W)
    (hJne : J ≠ 0) (ell : V) (hell : ell ∈ W) (hne : ell ≠ 0) :
    ∃ t : ℂ, t ≠ 0 ∧ ell = t • J := by
  have hjne : (⟨J, hJ⟩ : W) ≠ 0 := fun hz => hJne (congrArg (fun z : W => (z : V)) hz)
  obtain ⟨t, ht⟩ := exists_smul_eq_of_finrank_eq_one hW hjne (⟨ell, hell⟩ : W)
  have he := congrArg (fun z : W => (z : V)) ht
  refine ⟨t, ?_, he.symm⟩
  intro hz
  apply hne
  simpa [hz] using he.symm

theorem complexWhittaker_scalar
    (ell : Theta frequency →L[ℂ] ℂ)
    (hell : ell ∈ localWhittakerSpace _ (Theta frequency) (complexRootAction A w)
      (complexRawPsi w).toAddChar.toMonoidHom) (hne : ell ≠ 0) :
    ∃ t : ℂ, t ≠ 0 ∧ ell = t • KPCplxJacquetFunctional.thetaJacquetFunctional frequency := by
  have hd : Module.finrank ℂ (localWhittakerSpace _ (Theta frequency) (complexRootAction A w)
      (complexRawPsi w).toAddChar.toMonoidHom) = 1 := complex_whittakerLine A w
  have hmem : KPCplxJacquetFunctional.thetaJacquetFunctional frequency ∈
      localWhittakerSpace (Multiplicative (KPHilbert.Completion F (Sum.inl w)))
        (Theta frequency) (complexRootAction A w)
        (complexRawPsi w).toAddChar.toMonoidHom := complexJacquet_mem A w
  exact scalar_of_line _ hd _ hmem
    (KPCplxJacquetFunctional.thetaJacquetFunctional_ne_zero frequency) ell hell hne

theorem complexJacquet_actualDiagonal (h : Theta frequency) (y : ℂˣ) :
    KPCplxJacquetFunctional.thetaJacquetFunctional frequency
      (action A w (KPPGLLocalCover.A F A.zeta12 A.primitive_zeta12 (Sum.inl w)
        (Units.map (coordinate A w).symm.toRingHom.toMonoidHom y)) h) =
      KPCplxRootDerivativeVectors.whittakerValue frequency h y := by
  rw [KPPGLLocalCover.A, ← standard_diagonal, action_splitMatrix]
  have hu : Units.map (coordinate A w).toMonoidHom
      (Units.map (coordinate A w).symm.toRingHom.toMonoidHom y) = y := by
    apply Units.ext
    exact (coordinate A w).apply_symm_apply _
  rw [hu]
  rfl

end DedekindZetaZeroFree.KPActualReflectionData.StandardLocalSource

end
