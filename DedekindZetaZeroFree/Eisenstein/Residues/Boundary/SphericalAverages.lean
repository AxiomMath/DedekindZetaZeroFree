module

public import DedekindZetaZeroFree.Eisenstein.Residues.Boundary.QuotientAverages

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open _root_.DedekindZetaZeroFree.KPContSectorArchSphericalFibers renaming mem_KInfinity_iff_stab → mem_KInfinity_iff_stab
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FiniteSlabFullAngularHaar renaming compactSubgroup_eq_origin_stabilizer → compactSubgroup_eq_origin_stabilizer
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "Core" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
local notation "K" => KPMsGreenFlux.K F

theorem spherical_source_compact
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (k : K) :
    (KPContFlatSourceRecipe.flatR F ζ hζ 0 v.val).val
      (g*KPMsGreenFlux.compactInsertion F ζ hζ k) =
    (KPContFlatSourceRecipe.flatR F ζ hζ 0 v.val).val g := by
  rw [KPContFlatSourceRecipe.flatR_zero]
  let a : KPContSectorArchSphericalFibers.KInfinity F := ⟨fun w => (k w).val, by
    apply (mem_KInfinity_iff_stab F _).mpr
    intro i
    rw [← compactSubgroup_eq_origin_stabilizer]
    exact (k (KPCusp.complexPlace F i)).property⟩
  exact v.property.2 g a

theorem boundaryAverage_spherical
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (dk : Measure K) (v : KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (x : Core) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    boundaryAverage R P C dk v.val x g =
      (KPContFlatSourceRecipe.flatR F ζ hζ 0 v.val).val g *
      star (∫k, KPGlobalResidualConstruction.upperConstantTerm F ζ hζ
        (KPWildKernelUpperBound.quotientHaar F) (coreResidue R P C x)
        (g*KPMsGreenFlux.compactInsertion F ζ hζ k) ∂dk) := by
  unfold boundaryAverage boundaryProduct
  simp_rw [spherical_source_compact R U v g]
  rw [integral_const_mul]
  congr 1
  simp only [KPGlobalResidualConstruction.upperConstantTerm, Complex.star_def]
  exact integral_conj
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
