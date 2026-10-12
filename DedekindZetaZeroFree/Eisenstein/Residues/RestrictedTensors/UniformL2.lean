module

public import DedekindZetaZeroFree.Theta.Periods.Cusps.RestrictedSlotPairingBounds
public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.UniformBoundaryLevel
public import DedekindZetaZeroFree.Eisenstein.Residues.BoundaryPairings.NormIdentity
public import DedekindZetaZeroFree.Eisenstein.Residues.Pairings.ScalarL2Norm

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
theorem restrictedSlot_uniform_residue_l2
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
      ∀v : complexCore, ∃f : ResidualWeakEnergy.smoothAllWordL2 HR,
        (∀g, f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) =
          LiteralSource.coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v) g) ∧
        lpNorm f.val 2 HR.quotientHaar ≤ B*(orders.sup coreSeminorm) v := by
  obtain ⟨J,hs,hx⟩ := restrictedSlot_uniform_source_residue_level R P C s x w hw
  obtain ⟨orders,B,hB,hbound⟩ := restrictedSlot_boundary_pair_bound R N P C HR HP  s x w hw J dk
  refine ⟨J,orders,Real.sqrt B,Real.sqrt_pos.mpr hB,hx,?_⟩
  intro v
  obtain ⟨f,hfx,hpair⟩ := LiteralSource.exists_core_norm_boundary_identity R P C D HR HP M
    N  J dk (restrictedSlotTensor R.A P C s x w hw v) (hs v) (hx v)
  refine ⟨f,hfx,?_⟩
  have hb := hbound v
  rw [←hpair] at hb
  exact ResidualScalarNorm.lpNorm_le_of_pairing_bound f.val (f.property []).2 B
    ((orders.sup coreSeminorm) v) hB.le (apply_nonneg _ _) hb

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
