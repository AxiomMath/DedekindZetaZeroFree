module

public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarSections.FlatInsertion

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open _root_.DedekindZetaZeroFree.RestrictedTensorSimple renaming inclusion_insert → inclusion_insert
open KPLiteralRaw KPGlobalTorusFiniteStages KPLocalPrincipalSeries
open KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def cofactorSourceLevel (E : Finset (KPFinitePlace F)) (hE : C.exceptional ⊆ E) :
    RestrictedTensorSimple.Level (bad R.A P C) :=
  ⟨Finset.univ.disjSum E, by
    intro p hp
    rcases p with w | q
    · simp
    · exact Finset.inr_mem_disjSum.mpr (hE (Finset.inr_mem_disjSum.mp hp))⟩

def cofactorSourceTuple (E : Finset (KPFinitePlace F)) (hE : C.exceptional ⊆ E)
    (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
      (C.canonical q.val).iwasawa .plus) :
    ∀ j : (cofactorSourceLevel R P C E hE).val, Plus R.A P C j.val :=
  fun j ↦ match j with
  | ⟨Sum.inl w, _⟩ => plusReference R.A P C (Sum.inl w)
  | ⟨Sum.inr q, hq⟩ =>
    compactTrivialization (C.canonical q).borel (C.polarization q)
      (C.canonical q).iwasawa .plus 0 (φ ⟨q, Finset.inr_mem_disjSum.mp hq⟩)

def cofactorSourceCore (E : Finset (KPFinitePlace F)) (hE : C.exceptional ⊆ E)
    (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
      (C.canonical q.val).iwasawa .plus) :=
  RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
    (cofactorSourceLevel R P C E hE) (PiTensorProduct.tprod ℂ (cofactorSourceTuple R P C E hE φ))

def cofactorExtendedTuple (E : Finset (KPFinitePlace F)) (hE : C.exceptional ⊆ E)
    (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
      (C.canonical q.val).iwasawa .plus)
    (t : RestrictedTensorSimple.Level (bad R.A P C)) :
    ∀ j : t.val, Plus R.A P C j.val := fun j ↦
      if h : j.val ∈ (cofactorSourceLevel R P C E hE).val then
        cofactorSourceTuple R P C E hE φ ⟨j.val,h⟩ else plusReference R.A P C j.val

theorem coreFlatInsertion_raw (x : RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)) (z : ℂ) (g : Raw R.A) :
    (coreFlatInsertion R P C x).val z
      (scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) =
      Complex.exp (z * (ThetaExpansion.iwasawaLogHeight R
        (scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) : ℂ)) *
        rawCoreInsertion R.A P C x g := by
  rfl

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
