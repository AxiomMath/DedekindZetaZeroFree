module

public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.UniformL2
public import DedekindZetaZeroFree.Eisenstein.Residues.ResidualRepresentations.QuotientRealization

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
theorem restrictedSlot_quotient_residue_l2
    (D : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (HR : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (HP : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (M : NativeMeasuredSource F ζ hζ HR HP)

    (dk : Measure (KPMsGreenFlux.K F)) [IsProbabilityMeasure dk] [dk.IsHaarMeasure]
    (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
    (x : ∀j : s.val, LiteralSource.Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val) :
    ∃J : Level F ζ hζ, ∃orders : Finset ℕ, ∃B : ℝ, 0<B ∧
      (∀(v : complexCore) g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ J →
        LiteralSource.coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v) (g*u) =
        LiteralSource.coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v) g) ∧
      ∀v : complexCore,
        (LiteralSource.coreResidueQuotient R P C (restrictedSlotTensor R.A P C s x w hw v)
          ∈ ResidualWeakEnergy.smoothAllWordL2 HR) ∧
        (∀g, LiteralSource.coreResidueQuotient R P C (restrictedSlotTensor R.A P C s x w hw v)
          (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) =
          LiteralSource.coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v) g) ∧
        lpNorm (LiteralSource.coreResidueQuotient R P C (restrictedSlotTensor R.A P C s x w hw v))
          2 HR.quotientHaar ≤ B*(orders.sup coreSeminorm) v := by
  obtain ⟨J,orders,B,hB,hJ,h⟩ := restrictedSlot_uniform_residue_l2 R N P C D HR HP M  dk s x w hw
  refine ⟨J,orders,B,hB,hJ,?_⟩
  intro v
  obtain ⟨f,hfx,hf⟩ := h v
  have he := LiteralSource.coreResidueQuotient_eq_of_lift R P C _ f.val hfx
  rw [he]
  exact ⟨f.property,hfx,hf⟩

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
