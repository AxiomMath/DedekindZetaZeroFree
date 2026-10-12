module

public import DedekindZetaZeroFree.Theta.Profiles.RepeatedScalarRealization
public import DedekindZetaZeroFree.Theta.Whittaker.SphericalArchimedeanProduct
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.SphericalCoreGeneration
public import DedekindZetaZeroFree.Theta.Profiles.ResidualSourceRealization

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages MomentSources ThetaExpansion TensorActionSource
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)

variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)

variable
    (hR : RootAligned R) (N : TraceHaarTransport R) (hC : C.exceptional = R.A.Sf)
    (u : ∀ j : bad R.A P C, Plus R.A P C j.val)
    (hspherical : ∀ z (p : KPFinitePlace F), p ∉ R.A.Sf →
      ∀ k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p),
        k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) →
      ∀ g, (coreFlatInsertion R P C (RestrictedTensorSimple.stageInclusion _ _ _ ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ u))).val z
        (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) k)) =
        (coreFlatInsertion R P C (RestrictedTensorSimple.stageInclusion _ _ _ ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ u))).val z g)
    (hx : fourier R (KPWildKernelUpperBound.quotientHaar F)
      (coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _
        ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ u))) 1 ≠ 0)

local notation "DC" => canonicalCovariantNative R P C μ hμ  hR N hC u hspherical hx
set_option quotPrecheck false
local notation "HC" => (DC).toGenerated.tensorHC
local notation "H" => actualImageData R P C μ hμ

open RootDerivatives ComplexLines
local notation "DL" => canonicalTensorLocalLines R P C μ hμ  hR N hC u hspherical hx

def canonicalStage08 : JointExteriorCoefficientSources R N :=
  currentStage08 R hR (FourierContinuation.jointHaarFactorizedSources_of_factorization (DL).toJointRealizedFlatSources (DL).factorization)

set_option quotPrecheck false
local notation "A8" => canonicalStage08 R P C μ hμ  hR N hC u hspherical hx

theorem canonicalStage08_native : SourceNativeLie R (A8).factorization := by
  exact canonicalCovariantNative_native R P C μ hμ  hR N hC u hspherical hx

theorem canonical_spherical_transport : Nonempty (SphericalTransportData R (A8)) := by
  let D := (DL).factorization
  let K := Classical.choice (prepared_spherical_tensor_exists R D)
  obtain ⟨L,hr,hL,hn⟩ := factorization_trace_forms (DL)
    (canonicalTensorLocalLines_trace R P C μ hμ  hR N hC u hspherical hx)
  have hw (w:InfinitePlace F) : Sum.inl w∈K.stage.val := by
    rw [K.stage_exact]
    exact (D.bad_exact _).mpr (Or.inl ⟨w,rfl⟩)
  have hQ : ∃Q0:AdmissibleFlatSources R,∃T0:Realization R Q0,∀v,T0.theta v=K.value := by
    have hs : K.stage=⟨bad R.A P C,le_rfl⟩ := Subtype.ext K.stage_exact
    have H0 := actual_initial_repeated_realization R P C μ hμ N  hR hC
    have Hs : ∀ (s:RestrictedTensorSimple.Level (bad R.A P C))
        (x:∀j:s.val,actualLocal R (actualImageData R P C μ hμ) j.val),
        s.val=bad R.A P C → ∃Q0:AdmissibleFlatSources R,∃T0:Realization R Q0,∀v,
          T0.theta v=actualCoreResidue R P C μ hμ N
            (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ x)) := by
      intro s x hs
      have he:s=⟨bad R.A P C,le_rfl⟩ := Subtype.ext hs
      subst s
      exact H0 x
    exact Hs K.stage K.entries K.stage_exact
  obtain ⟨Q0,T0,hT0⟩ := hQ
  refine ⟨{ tensor := K
            localForm := L
            restriction := hr
            whittaker := fun w=>traceWhittaker_actual (R:=R) w (L w) (hL w)
            seed_nonzero := hn
            period_nonzero := prepared_spherical_period_ne_zero D K L hr hn
            source_detected := factorization_source_detected D
            arch_product := ?_
            core_generated := core_spherical_generated_of_realization D K
              (canonicalStage08_native R P C μ hμ  hR N hC u hspherical hx) T0 hT0 }⟩
  intro y
  exact actual_spherical_arch_product R P C μ hμ N  K.stage K.entries hw
    (fun w=>K.spherical w (hw w)) L hL hn (prepared_spherical_period_product D K L hr) y
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
