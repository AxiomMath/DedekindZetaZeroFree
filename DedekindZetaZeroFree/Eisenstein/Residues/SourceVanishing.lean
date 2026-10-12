module

public import DedekindZetaZeroFree.Eisenstein.Residues.Boundary.RadialHomogeneity

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPContFlatArchDiagonalMultiplier KPMsActualAngularSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "G" => KPGlobalTorusFunctionData.G F ζ hζ
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
local notation "Source" => KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ)

open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CanonicalStageBounds renaming literal_bounded_entire_stage → literal_bounded_entire_stage

theorem literal_source_zero_exists (K : Subgroup G)
    (hK : KPLiteralRaw.IwasawaCompact F ζ hζ K) (f : KPLiteralRaw.Flat F ζ hζ K) :
    ∃ t : Source, ∀g, (KPContFlatSourceRecipe.flatR F ζ hζ 0 t).val g = f.val 0 g := by
  obtain ⟨n,ι,p,T,J,hi,hp,hs,hT,hJ,he⟩ := literal_bounded_entire_stage F ζ hζ K hK f
  exact ⟨ι (p 0),he 0⟩

theorem core_source_zero_exists (x : V) :
    ∃ t : Source, ∀g, (KPContFlatSourceRecipe.flatR F ζ hζ 0 t).val g =
      quotientCoreEvaluator R.A P C x g := by
  obtain ⟨t,ht⟩ := literal_source_zero_exists R (ThetaExpansion.fullProductCompact R)
    (ThetaExpansion.full_product_compact_iwasawa R)
    (TensorActionSource.asLiteralFlat (coreFlatInsertion R P C x))
  refine ⟨t,?_⟩
  intro g
  exact (ht g).trans (congrFun (coreFlatInsertion_zero R P C x) g)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
