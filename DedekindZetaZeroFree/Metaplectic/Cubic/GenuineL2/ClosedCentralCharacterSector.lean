module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Quotients.CentralHaarInvariance

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPContSectorClosedLpSubspace

open KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)

abbrev CoveredL2 := Lp ℂ 2 (coveredMeasure F ζ hζ R U)

def T (ε : rootsOfUnity 3 F) :
    CoveredL2 F ζ hζ R U ≃ₗᵢ[ℂ] CoveredL2 F ζ hζ R U where
  __ := Lp.compMeasurePreservingₗᵢ ℂ (z F ζ hζ U ε)
    (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε)
  invFun := Lp.compMeasurePreserving (z F ζ hζ U ε⁻¹)
    (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε⁻¹)
  left_inv := by
    intro u
    change Lp.compMeasurePreserving (z F ζ hζ U ε⁻¹)
        (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε⁻¹)
        (Lp.compMeasurePreserving (z F ζ hζ U ε)
          (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε) u) = u
    rw [← Lp.compMeasurePreserving_comp_apply u
      (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε)
      (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε⁻¹)]
    have hfun : (z F ζ hζ U ε) ∘ (z F ζ hζ U ε⁻¹) = id := by
      funext x
      exact smul_inv_smul (ε : rootsOfUnity 3 F) x
    simp only [hfun]
    exact Lp.compMeasurePreserving_id_apply u
  right_inv := by
    intro u
    change Lp.compMeasurePreserving (z F ζ hζ U ε)
        (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε)
        (Lp.compMeasurePreserving (z F ζ hζ U ε⁻¹)
          (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε⁻¹) u) = u
    rw [← Lp.compMeasurePreserving_comp_apply u
      (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε⁻¹)
      (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε)]
    have hfun : (z F ζ hζ U ε⁻¹) ∘ (z F ζ hζ U ε) = id := by
      funext x
      exact inv_smul_smul (ε : rootsOfUnity 3 F) x
    simp only [hfun]
    exact Lp.compMeasurePreserving_id_apply u

theorem T_coeFn (ε : rootsOfUnity 3 F) (u : CoveredL2 F ζ hζ R U) :
    (T F ζ hζ R U ε u : CoveredSpherical F ζ hζ U → ℂ) =ᵐ[
      coveredMeasure F ζ hζ R U] (u : CoveredSpherical F ζ hζ U → ℂ) ∘ z F ζ hζ U ε :=
  Lp.coeFn_compMeasurePreserving u
    (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε)

def H : Submodule ℂ (CoveredL2 F ζ hζ R U) :=
  ⨅ ε : rootsOfUnity 3 F,
    LinearMap.ker
      (((T F ζ hζ R U ε).toLinearIsometry.toContinuousLinearMap -
        (chi F ζ hζ ε : ℂ) • ContinuousLinearMap.id ℂ (CoveredL2 F ζ hζ R U)).toLinearMap)

theorem H_isClosed : IsClosed (H F ζ hζ R U : Set (CoveredL2 F ζ hζ R U)) := by
  unfold H
  rw [Submodule.coe_iInf]
  exact isClosed_iInter (fun ε => ContinuousLinearMap.isClosed_ker _)

instance instCompleteSpaceH : CompleteSpace (H F ζ hζ R U) := by
  exact (H_isClosed F ζ hζ R U).isComplete.completeSpace_coe

instance instInnerProductSpaceH : InnerProductSpace ℂ (H F ζ hζ R U) :=
  inferInstanceAs (InnerProductSpace ℂ ↥(H F ζ hζ R U))

theorem mem_H_iff (u : CoveredL2 F ζ hζ R U) :
    u ∈ H F ζ hζ R U ↔ ∀ ε : rootsOfUnity 3 F,
      (u : CoveredSpherical F ζ hζ U → ℂ) ∘ z F ζ hζ U ε =ᵐ[
        coveredMeasure F ζ hζ R U]
          (chi F ζ hζ ε : ℂ) • (u : CoveredSpherical F ζ hζ U → ℂ) := by
  simp only [H]
  rw [Submodule.mem_iInf]
  constructor
  · intro h ε
    have hker : (((T F ζ hζ R U ε).toLinearIsometry.toContinuousLinearMap -
        (chi F ζ hζ ε : ℂ) • ContinuousLinearMap.id ℂ (CoveredL2 F ζ hζ R U)) u) = 0 :=
      LinearMap.mem_ker.mp (h ε)
    have heq : T F ζ hζ R U ε u = (chi F ζ hζ ε : ℂ) • u := sub_eq_zero.mp hker
    refine (T_coeFn F ζ hζ R U ε u).symm.trans ?_
    rw [heq]
    exact Lp.coeFn_smul (chi F ζ hζ ε : ℂ) u
  · intro h ε
    rw [LinearMap.mem_ker]
    have heq : T F ζ hζ R U ε u = (chi F ζ hζ ε : ℂ) • u := by
      rw [Lp.ext_iff]
      exact ((T_coeFn F ζ hζ R U ε u).trans (h ε)).trans
        (Lp.coeFn_smul (chi F ζ hζ ε : ℂ) u).symm
    show T F ζ hζ R U ε u - (chi F ζ hζ ε : ℂ) • u = 0
    rw [heq, sub_self]

end DedekindZetaZeroFree.KPContSectorClosedLpSubspace

namespace DedekindZetaZeroFree

open KPContSectorCoveredQuotientVocabulary KPContSectorFixedPushforwardSupport
open KPContSectorClosedLpSubspace

end DedekindZetaZeroFree

end
