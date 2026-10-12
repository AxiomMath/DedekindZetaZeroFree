module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RestrictedTensors.OperatorWordEvaluation
public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.QuotientL2
public import DedekindZetaZeroFree.Adeles.Quotients.Residual.DifferentialWords

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open MomentSources KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12

include N in
theorem restrictedSlot_residue_word_l2
    (D : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (HR : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (HP : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (M : NativeMeasuredSource F ζ hζ HR HP)

    (dk : Measure (KPMsGreenFlux.K F)) [IsProbabilityMeasure dk] [dk.IsHaarMeasure]
    (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
    (x : ∀j : s.val, LiteralSource.Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val)
    (b : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))) :
    ∃orders : Finset ℕ, ∃B : ℝ, 0<B ∧ ∀v : complexCore,
      lpNorm (ResidualOutputSobolev.quotientWord b
        (LiteralSource.coreResidueQuotient R P C (restrictedSlotTensor R.A P C s x w hw v)))
        2 HR.quotientHaar ≤ B*(orders.sup coreSeminorm) v := by
  obtain ⟨J₀,os₀,B₀,hB₀,hJ₀,hx⟩ := restrictedSlot_quotient_residue_l2 R N P C D HR HP M  dk s x w hw
  obtain ⟨y,a,ha,hseminorm⟩ := restrictedSlot_native_word R P C N s x w hw b
  obtain ⟨J,os,B,hB,hJ,hy⟩ := restrictedSlot_quotient_residue_l2 R N P C D HR HP M  dk s y w hw
  obtain ⟨orders,Cd,hCd,hc⟩ := hseminorm os
  have hCdpos : 0 < (Cd : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hCd)
  refine ⟨orders,B*Cd,mul_pos hB hCdpos,?_⟩
  intro v
  have he := LiteralSource.coreResidueQuotient_word_of_raw R P C _ _ b
    (hx v).2.1 (hy (HCGeneration.complexWord a v)).2.1 (ha v)
  rw [he]
  exact ((hy (HCGeneration.complexWord a v)).2.2.trans
    (mul_le_mul_of_nonneg_left (hc v) hB.le)).trans_eq (mul_assoc B (Cd:ℝ) _).symm

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
