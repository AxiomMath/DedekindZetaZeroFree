module

public import DedekindZetaZeroFree.Eisenstein.Residues.Boundary.AngularCoordinates

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPMsActualAngularSource
open _root_.DedekindZetaZeroFree.KPMsRationalCompactCrossPairingProof.ScalarAngularDescent renaming eqv_eval → eqv_eval
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
local notation "Source" => KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ)
local notation "K" => KPMsGreenFlux.K F

def boundaryAverage (dk : Measure K) (f : Source) (x : V) (g : G F ζ hζ) : ℂ :=
  ∫k, boundaryProduct R P C f x (g*KPMsGreenFlux.compactInsertion F ζ hζ k) ∂dk

theorem boundaryAverage_continuous (dk : Measure K) [IsFiniteMeasure dk] (f : Source) (x : V) :
    Continuous (boundaryAverage R P C dk f x) := by
  let : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  let : CompactSpace KPCplxPrincipalSeriesCharts.compactSubgroup :=
    isCompact_iff_compactSpace.mp KPCplxPrincipalSeriesCharts.compactSubgroup_isCompact
  have hk : Continuous (KPMsGreenFlux.compactInsertion F ζ hζ) := by
    apply (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
    exact continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i))
  unfold boundaryAverage
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k:=Set.univ) isCompact_univ
  · exact ((boundaryProduct_continuous R P C f x).comp
      (continuous_fst.mul (hk.comp continuous_snd))).continuousOn
  · intro p k hp hk
    exact False.elim (hk (Set.mem_univ k))

theorem boundaryAverage_rational_unipotent (dk : Measure K) (f : Source) (x : V)
    (y : Fˣ) (a : KPGlobalTorusFunctionData.Adeles F) (g : G F ζ hζ) :
    boundaryAverage R P C dk f x (((KPGlobalTorusFunctionData.s F ζ hζ y).val *
      KPGlobalTorusFunctionData.N F ζ hζ a)*g)=boundaryAverage R P C dk f x g := by
  unfold boundaryAverage
  apply integral_congr_ae
  filter_upwards with k
  rw [mul_assoc,boundaryProduct_rational_unipotent]

def boundaryFullAverage (D : Iwasawa F ζ hζ) (dk : Measure K) (f : Source) (x : V) :
    FullOmega F ζ hζ D → ℂ :=
  Quotient.lift (fun g : NormOne F ζ hζ D => boundaryAverage R P C dk f x g.val) (by
    intro a b hab
    apply eqv_eval (v := fun g : NormOne F ζ hζ D => boundaryAverage R P C dk f x g.val) ?_ hab
    rintro a b ⟨y,t,hb⟩
    rw [hb,boundaryAverage_rational_unipotent])

theorem boundaryFullAverage_continuous (D : Iwasawa F ζ hζ)
    (dk : Measure K) [IsFiniteMeasure dk] (f : Source) (x : V) :
    Continuous (boundaryFullAverage R P C D dk f x) :=
  ((boundaryAverage_continuous R P C dk f x).comp continuous_subtype_val).quotient_lift _
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
