module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residual.UpperCompactWordExpansion

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open CurrentRepairedLocalBinding MomentSources KPGlobalTorusFiniteStages
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar KPGlobalResidualConstruction
open KPContActualSphericalRightFieldIdentification CurrentComplexBoundary
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
local instance : SecondCountableTopology compactSubgroup := by
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
    change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
    infer_instance
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  letI : SecondCountableTopology ComplexGL2 := Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology ComplexPGL2 :=
    inferInstanceAs (SecondCountableTopology (ComplexGL2 ⧸ Subgroup.center _))
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "Core" => RestrictedTensorSimple.Core (LiteralSource.Plus R.A P C) (LiteralSource.plusReference R.A P C) (LiteralSource.bad R.A P C)
include N in
theorem compact_source_upper_derivative_adjoint
    (ρ : Measure ComplexSU2) [IsProbabilityMeasure ρ] [ρ.IsHaarMeasure]
    (dk : Measure (KPMsGreenFlux.K F)) [IsProbabilityMeasure dk] [dk.IsHaarMeasure]
    (ν : InfinitePlace F → Measure compactSubgroup) [∀i,IsProbabilityMeasure (ν i)] [∀i,(ν i).IsHaarMeasure]
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (x : Core) (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (w : List (Fin (groupDimension F))) :
    (∫k,t.val.val (KPMsGreenFlux.compactInsertion F ζ hζ k*c.val) *
      star (actualRightWord F ζ hζ w.reverse (originalUpper R (LiteralSource.coreResidue R P C x))
        (KPMsGreenFlux.compactInsertion F ζ hζ k*c.val)) ∂dk) =
    (-1 : ℂ)^w.length * (∫k,actualRightWord F ζ hζ w t.val.val
      (KPMsGreenFlux.compactInsertion F ζ hζ k*c.val) *
      star (originalUpper R (LiteralSource.coreResidue R P C x)
        (KPMsGreenFlux.compactInsertion F ζ hζ k*c.val)) ∂dk) := by
  have hms : KPMsGreenFlux.instMeasurableSpaceK F = (MeasurableSpace.pi : MeasurableSpace (InfinitePlace F → compactSubgroup)) := by
    exact (@BorelSpace.measurable_eq (InfinitePlace F → compactSubgroup) _ MeasurableSpace.pi (Pi.borelSpace)).symm
  revert dk
  rw [hms]
  intro dk hdk hhaar
  obtain ⟨n,d,f,ht⟩ := source_compact_word_expansion F ζ hζ t c
  obtain ⟨m,e,g,hx⟩ := upper_compact_word_expansion R N P C  x c
  have ht0 := ht []
  have hx0 := hx []
  simp only [actualRightWord, List.map_nil, slotWords, matrixWord] at ht0 hx0
  have hn : negativeParameter = -positiveParameter := by norm_num [negativeParameter,positiveParameter]
  subst_vars
  have H := finiteCompact_word_adjoint ρ dk ν positiveParameter (w.map (matrixLetter F)) d e f g
  simp only [List.length_map, ←List.map_reverse] at H
  simp_rw [ht w,hx0]
  simp_rw [ht0,hx w.reverse]
  have hs : (-1 : ℂ)^w.length * (-1 : ℂ)^w.length = 1 := by
    rw [←mul_pow]; norm_num
  calc
    _ = ((-1 : ℂ)^w.length * (-1 : ℂ)^w.length) * _ := by rw [hs,one_mul]
    _ = _ := by rw [mul_assoc,←H]
end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
