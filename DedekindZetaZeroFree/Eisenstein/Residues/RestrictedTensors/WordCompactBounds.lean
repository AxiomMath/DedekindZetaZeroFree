module

public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.CompactResidueBounds

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
theorem restrictedSlot_residue_word_compact_bound
    (D : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (HR : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (HP : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (M : NativeMeasuredSource F ζ hζ HR HP)

    (dk : Measure (KPMsGreenFlux.K F)) [IsProbabilityMeasure dk] [dk.IsHaarMeasure]
    (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
    (x : ∀j : s.val, LiteralSource.Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val)
    (b : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)))
    (K : Set (KPLiteralRaw.G F ζ hζ)) (hK : IsCompact K) :
    ∃orders : Finset ℕ, ∃B : ℝ, 0<B ∧ ∀v : complexCore, ∀g∈K,
      ‖KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ b
        (LiteralSource.coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v)) g‖ ≤
        B*(orders.sup coreSeminorm) v := by
  obtain ⟨y,a,ha,hseminorm⟩ := restrictedSlot_native_word R P C N s x w hw b
  obtain ⟨os,B,hB,hy⟩ := restrictedSlot_residue_compact_bound R N P C D HR HP M  dk s y w hw K hK
  obtain ⟨orders,Cd,hCd,hc⟩ := hseminorm os
  have hCdpos : 0 < (Cd : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hCd)
  refine ⟨orders,B*Cd,mul_pos hB hCdpos,?_⟩
  intro v g hg
  rw [ha]
  exact ((hy (HCGeneration.complexWord a v) g hg).trans
    (mul_le_mul_of_nonneg_left (hc v) hB.le)).trans_eq (mul_assoc B (Cd:ℝ) _).symm

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
