module

public import DedekindZetaZeroFree.Eisenstein.Induction.Archimedean.PrincipalSeriesSlices
public import DedekindZetaZeroFree.Eisenstein.Induction.Cubic.SphericalLevelKernels

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal.SphericalReseeding
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def evalCoefficient
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    {m : ℕ} (k : Fin m → KPContSectorArchSphericalFibers.KInfinity F)
    (A : Fin m → ℂ) (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) : ℂ :=
  ∑ ν, A ν * t.val.val
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val * c.val)

def sphericalProduct
    (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) : ℂ :=
  ∏ w, KPCplxPrincipalSeriesCharts.sphericalSection
    KPCplxPrincipalSeriesCharts.positiveParameter (a w)

def fibreValue
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (e : KPGlobalTorusFunctionData.E F ζ hζ) : ℂ :=
  (KPGlobalTorusFunctionData.deltaHalf F ζ hζ e)⁻¹ * t.val.val (e.val * g)

theorem fibreValue_eq_owned_lift
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (T : KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (hT : KPGlobalTorusBorelTwistCompatibility.scalarSection F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) T = t.val)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (e : KPGlobalTorusFunctionData.E F ζ hζ) :
    fibreValue F ζ hζ t g e = (T.val.val g).val.val e := by
  rw [KPGlobalTorusBorelTwistCompatibility.scalar_transitivity, hT]
  rfl

@[simp] theorem sphericalProduct_one : sphericalProduct F (fun _ => 1) = 1 := by
  simp [sphericalProduct, KPCplxPrincipalSeriesCharts.sphericalSection_one]

private theorem insertion_commutes_finite
    (r : KPSmoothActualFlowData.GInfinity F)
    (a : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ r) a.val := by
  have ht : a.val ∈ ActualFiniteFactor.tupleFactor F ζ hζ := by
    obtain ⟨b, hb, he⟩ := a.property
    refine ⟨b, ?_, he⟩
    intro w
    exact (Subgroup.mem_iInf.mp hb) w
  have ha : a.val ∈ ActualFiniteFactor.finiteSubgroup F ζ hζ := by
    rw [ActualFiniteFactor.finiteSubgroup_eq_tupleFactor]
    exact ht
  exact ActualFiniteFactor.archInsertion_commutes F ζ hζ r ⟨a.val, ha⟩

variable (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
variable {m : ℕ} (k : Fin m → KPContSectorArchSphericalFibers.KInfinity F) (A : Fin m → ℂ)

theorem evalCoefficient_right_level
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (htU : t ∈ KPContFlatCommonLevelKernel.CommonLevel F ζ hζ U)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) (u : U.toOpenSubgroup) :
    evalCoefficient F ζ hζ t k A (c * u.val) = evalCoefficient F ζ hζ t k A c := by
  apply Finset.sum_congr rfl
  intro ν _
  congr 1
  change t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val *
    (c.val * u.val.val)) = _
  rw [← mul_assoc]
  exact (htU _ ⟨u.val.val, Subgroup.mem_map_of_mem
    (KPGlobalTorusFunctionData.finitePart F ζ hζ).subtype u.property⟩).1

theorem evalCoefficient_finite_borel_covariance
    (h : (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).H)
    (x : KPGlobalTorusFunctionData.Adeles F)
    (b : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (hb : b.val = h.val.val * KPGlobalTorusFunctionData.N F ζ hζ x)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    evalCoefficient F ζ hζ t k A (b * c) =
      (KPGlobalTorusFunctionData.deltaHalf F ζ hζ h.val *
        ((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).character h : ℂ)) *
      evalCoefficient F ζ hζ t k A c := by
  rw [evalCoefficient, evalCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  have hc := insertion_commutes_finite F ζ hζ (k ν).val b
  change A ν * t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val *
    (b.val * c.val)) = _
  rw [← mul_assoc, hc.eq, mul_assoc, hb, t.val.property h x]
  ring

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal.SphericalReseeding

end
