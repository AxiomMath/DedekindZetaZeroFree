module

public import DedekindZetaZeroFree.Metaplectic.Kubota.DisjointArchimedeanActions

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open MomentSources KPSmoothActualFlowData
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def archPartial (t : Finset (InfinitePlace F))
    (a : InfinitePlace F → KPCplxCharacterHaar.ComplexPGL2) : MomentSources.Group R :=
  archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12 (fun w => if w ∈ t then a w else 1)

theorem archPartial_empty (a : InfinitePlace F → KPCplxCharacterHaar.ComplexPGL2) :
    archPartial R ∅ a = 1 := by
  simp only [archPartial,Finset.notMem_empty,ite_false]
  exact (archimedean_insertion_properties F R.A.zeta12 R.A.primitive_zeta12).1

theorem archPartial_insert (t : Finset (InfinitePlace F)) (w : InfinitePlace F) (hw : w ∉ t)
    (a : InfinitePlace F → KPCplxCharacterHaar.ComplexPGL2) :
    archPartial R (insert w t) a = archPartial R t a * projectiveSlot R w (a w) := by
  unfold archPartial projectiveSlot
  rw [←(archimedean_insertion_properties F R.A.zeta12 R.A.primitive_zeta12).2.1]
  congr 1
  funext u
  by_cases hu : u = w
  · subst u
    simp [hw]
  · simp [hu]

theorem archPartial_projection_not_mem (t : Finset (InfinitePlace F)) (w : InfinitePlace F)
    (hw : w ∉ t) (a : InfinitePlace F → KPCplxCharacterHaar.ComplexPGL2) :
    PGLComplex.AdelicSlicesRaw.archProjection F R.A.zeta12 R.A.primitive_zeta12
      (archPartial R t a) w = 1 := by
  change PGLComplex.AdelicSlicesRaw.archProjection F R.A.zeta12 R.A.primitive_zeta12
    (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12
      (fun u => if u ∈ t then a u else 1)) w = 1
  rw [PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
  simp [hw]

theorem archPartial_univ (a : InfinitePlace F → KPCplxCharacterHaar.ComplexPGL2) :
    archPartial R Finset.univ a = archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12 a := by
  simp [archPartial]

end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
