module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section

def rmKummerPrimitiveTwo (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) : (primitiveRoots 2 F).Nonempty :=
  ⟨h12.choose ^ 6, (mem_primitiveRoots (by decide)).2
    (((mem_primitiveRoots (by decide)).1 h12.choose_spec).pow
      (by decide) (by decide : 12 = 6 * 2))⟩

theorem rmKummerTwo_ne_zero (F : Type) [Field F] [NumberField F] : (2 : F) ≠ 0 := by
  norm_num

def rmKummerComplexEmbedding (F : Type) [Field F] [NumberField F] : F →+* ℂ :=
  Classical.choice inferInstance

def rmKummerQuadraticRootsComplexEquiv (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) :
    rootsOfUnity 2 F ≃* rootsOfUnity 2 ℂ :=
  rootsOfUnityEquivOfPrimitiveRoots (rmKummerComplexEmbedding F).injective
    (rmKummerPrimitiveTwo F h12)

def rmKummerQuadraticRootsDescent (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (E : Type*) [Field E] [Algebra F E] :
    rootsOfUnity 2 E ≃* rootsOfUnity 2 F :=
  (rootsOfUnityEquivOfPrimitiveRoots (algebraMap F E).injective
    (rmKummerPrimitiveTwo F h12)).symm

def rmKummerQuadraticRootsComplexMap (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (E : Type*) [Field E] [Algebra F E] :
    rootsOfUnity 2 E →* ℂˣ :=
  (rootsOfUnity 2 ℂ).subtype.comp
    (((rmKummerQuadraticRootsDescent F h12 E).trans
      (rmKummerQuadraticRootsComplexEquiv F h12)).toMonoidHom)

theorem rmKummerQuadraticRootsComplexMap_injective (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (E : Type*) [Field E] [Algebra F E] :
    Function.Injective (rmKummerQuadraticRootsComplexMap F h12 E) := by
  intro z w h
  apply ((rmKummerQuadraticRootsDescent F h12 E).trans
    (rmKummerQuadraticRootsComplexEquiv F h12)).injective
  exact Subtype.ext h

theorem rmKummerQuadraticRootsComplexMap_pow_two (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (E : Type*) [Field E] [Algebra F E]
    (z : rootsOfUnity 2 E) : (rmKummerQuadraticRootsComplexMap F h12 E z) ^ 2 = 1 := by
  exact (((rmKummerQuadraticRootsDescent F h12 E).trans
    (rmKummerQuadraticRootsComplexEquiv F h12)) z).property

end
end DedekindZetaZeroFree
