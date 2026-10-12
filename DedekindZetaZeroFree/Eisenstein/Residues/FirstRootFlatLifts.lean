module

public import DedekindZetaZeroFree.Eisenstein.Residues.FirstRootLifts
public import DedekindZetaZeroFree.Eisenstein.Residues.FirstRootFlatPreimageGerms
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.FirstRootHarishChandraHeckeRecovery

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical Topology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

end DedekindZetaZeroFree.ThetaExpansion

end

section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem first_root_flat_lift_exists
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R)
    (J : FirstRootProjected R N A B)
    (hNative : RootDerivatives.SourceNativeLie R J.base.factorization) : Nonempty (FirstRootLift R N A B J) := by
  classical
  obtain ⟨Q, T, hdq, hpin, hsource, htheta, hperiod, hflat⟩ :=
    first_root_realization_exists  R hR N A B J
  obtain ⟨hcore, hfrozen⟩ := first_root_fixed_stage_tensors_exists R N A B J hNative
  obtain ⟨hhc, _, _⟩ := first_root_hc_span_recovery R N A B J hNative T
    hdq hpin hsource hperiod hfrozen
  choose s x hs hx hell hnx hpx using hfrozen
  let D := J.base.factorization
  let D' : SourceFactorization R Q T := {
    finiteData := D.finiteData
    references := D.references
    bad := D.bad
    bad_exact := D.bad_exact
    ell := D.ell
    reference_value := D.reference_value
    scalarSlot := D.scalarSlot
    coreMap := D.coreMap
    selected := fun v => RestrictedTensorSimple.stageInclusion _ D.references D.bad (s v)
      (PiTensorProduct.tprod ℂ (x v))
    selected_eq := fun v => (hx v).trans (hpin v).symm
    selected_frozen_stage := fun v => ⟨s v, x v, hs v, rfl⟩
    core_injective := D.core_injective
    core_same_residue := fun z => ⟨hhc (D.core_same_residue z).1, (D.core_same_residue z).2⟩
    finite_intertwining := D.finite_intertwining
    complex_intertwining := D.complex_intertwining
    product_integrable := by rw [hdq]; exact D.product_integrable
    product_exact := by rw [hdq]; exact D.product_exact
    spherical_reference := D.spherical_reference
    detected_tensor := by rw [hdq]; exact D.detected_tensor
    period_integrable := fun v g => FourierContinuation.theta_period_integrable T v g
    detected := by obtain ⟨v, _⟩ := D.detected; exact ⟨v, hperiod v⟩ }
  let C : JointExteriorCoefficientSources R N := {
    aligned := hR
    transport := N
    transport_exact := rfl
    sources := Q
    realization := T
    factorization := D'
    localHaarTransport := fun q => by
      have hh := J.base.localHaarTransport q
      rw [J.base.transport_exact] at hh
      exact hh
    exterior := ⟨J.base.exterior.rational_exact, J.base.exterior.crt_product,
      J.base.exterior.local_exact⟩ }
  exact ⟨⟨C, hdq, hpin⟩⟩

end DedekindZetaZeroFree.ThetaExpansion

end
end
