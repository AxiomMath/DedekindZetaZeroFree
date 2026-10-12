module

public import DedekindZetaZeroFree.Adeles.Units.SupportedIdeles.Coordinates

@[expose] public section

open scoped NumberField NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SupportedChartNorm
open SupportedChartDefinitions
noncomputable section
variable {F : Type} [Field F] [NumberField F]

theorem local_norm (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    ‖(x : v.adicCompletion F)‖ =
      ((FiniteIdeleGroup.primeNorm v : ℝ≥0) : ℝ) ^
        (-(FiniteIdeleGroup.localOrder v x).toAdd) := by
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
  simp [FiniteIdeleGroup.localOrder_apply, FiniteIdeleGroup.primeNorm]

theorem finite_norm (S : Finset (HeightOneSpectrum (𝓞 F))) (a : FiniteIdeleGroup F)
    (ha : a ∈ FiniteIdeleGroup.supportedAt (K := F) (S : Set _)) :
    (∏ v : {v // v ∈ S}, ‖(a v.val : v.val.adicCompletion F)‖) =
      (((FiniteIdeleGroup.absoluteNorm a : ℝ≥0) : ℝ))⁻¹ := by
  classical
  have hs : (FiniteIdeleGroup.valuationVector a).toAdd.support ⊆ S := by
    intro v hv
    by_contra h
    exact (Finsupp.mem_support_iff.mp hv)
      ((FiniteIdeleGroup.localOrder_eq_zero_iff v (a v)).mpr (ha v h))
  rw [FiniteIdeleGroup.absoluteNorm_apply, Finsupp.prod]
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, NNReal.coe_prod, NNReal.coe_zpow]
  simp_rw [local_norm, zpow_neg]
  rw [← Finset.prod_subtype S (p := fun v => v ∈ S) (by simp)
    (fun v => (((FiniteIdeleGroup.primeNorm v : ℝ≥0) : ℝ) ^
      (FiniteIdeleGroup.localOrder v (a v)).toAdd)⁻¹)]
  rw [Finset.prod_inv_distrib]
  congr 1
  symm
  apply Finset.prod_subset hs
  intro v hv hvs
  simp [Finsupp.notMem_support_iff.mp hvs, FiniteIdeleGroup.valuationVector_apply]

theorem archimedean_norm (A : SArithmeticData F) (a : InfiniteIdeleGroup F) :
    (∏ w : InfinitePlace F, ‖(ContinuousMulEquiv.piUnits a w : w.Completion)‖ ^ 2) =
      ((InfiniteIdeleGroup.archimedeanNorm a : ℝ≥0) : ℝ) := by
  simp only [InfiniteIdeleGroup.archimedeanNorm_apply, Units.coe_prod,
    Units.val_pow_eq_pow_val, nnnormUnitHom_val, NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm]
  apply Finset.prod_congr rfl
  intro w _
  rw [InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place w))]
  rfl

theorem supported_norm (A : SArithmeticData F) (a : IdeleGroup F)
    (ha : a ∈ IdeleGroup.supportedAt (K := F) (A.Sf : Set _)) :
    A.norm (SupportedChartDefinitions.sCoordinatesRaw A a) = (((IdeleGroup.absoluteNorm a : ℝ≥0) : ℝ))⁻¹ := by
  change (∏ w : InfinitePlace F, ‖(ContinuousMulEquiv.piUnits a.1 w : w.Completion)‖ ^ 2) *
    (∏ v : {v // v ∈ A.Sf}, ‖(a.2 v.val : v.val.adicCompletion F)‖) = _
  rw [archimedean_norm A, finite_norm A.Sf a.2 ha, IdeleGroup.absoluteNorm_apply]
  simp [mul_comm]
end
end DedekindZetaZeroFree.SupportedChartNorm
