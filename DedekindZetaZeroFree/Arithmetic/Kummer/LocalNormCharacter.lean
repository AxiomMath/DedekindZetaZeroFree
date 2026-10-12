module

public import DedekindZetaZeroFree.Arithmetic.Kummer.LocalNorms.QuadraticRootCharacter
public import DedekindZetaZeroFree.Arithmetic.Kummer.LocalNorms.ArtinComparison

@[expose] public section

set_option maxRecDepth 2048

namespace DedekindZetaZeroFree.RMKummerLocalNormCharacter

noncomputable section
open scoped NumberField TensorProduct Classical
open IsDedekindDomain

def lambda (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) : (v.adicCompletion F)ˣ →* ℂˣ :=
  (RMKummerConductor.kappa F h12 x).comp
    (GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom
      F (RMKummerConductor.E F h12 x) v)

def localToRay (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →*
      ClassFieldTheory.RayClassGroup
        (M F (RMKummerConductor.m F h12 x)
          (RMKummerConductor.m_ne_bot F h12 x)) :=
  let m := M F (RMKummerConductor.m F h12 x)
    (RMKummerConductor.m_ne_bot F h12 x)
  (ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele F m).symm.toMonoidHom.comp
    ((QuotientGroup.mk'
      (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F m).congruenceSubgroup).comp
        (IdeleGroup.finitePlaceIdeleClass v))

theorem lambda_continuous (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (lambda F h12 x v : (v.adicCompletion F)ˣ → ℂˣ) := by
  exact (RMKummerLocalNormRoot.kappa_continuous F h12 x).comp
    (RMKummerLocalNormArtin.arithmeticLocalArtin_continuous F
      (RMKummerConductor.E F h12 x) v)

theorem lambda_ker (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (lambda F h12 x v).ker =
      ClassFieldTheory.finitePlaceTensorNormSubgroup F (RMKummerConductor.E F h12 x) v := by
  rw [← RMKummerLocalNormArtin.arithmeticLocalArtin_ker F
    (RMKummerConductor.E F h12 x) v]
  ext t
  change RMKummerConductor.kappa F h12 x
    (GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom
      F (RMKummerConductor.E F h12 x) v t) = 1 ↔ _
  rw [← map_one (RMKummerConductor.kappa F h12 x)]
  exact (RMKummerLocalNormRoot.kappa_injective F h12 x).eq_iff

theorem lambda_ker_eq_norm_range (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (lambda F h12 x v).ker =
      (Units.map (Algebra.norm (v.adicCompletion F)
        (S := v.adicCompletion F ⊗[F] (RMKummerConductor.E F h12 x)))).range := by
  exact lambda_ker F h12 x v

theorem lambda_pow_two (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    lambda F h12 x v t ^ 2 = 1 := by
  exact RMKummerLocalNormRoot.kappa_pow_two F h12 x _

theorem rho_localToRay (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    RMKummerConductor.rho F h12 x (localToRay F h12 x v t) =
      lambda F h12 x v t := by
  apply congrArg (RMKummerConductor.kappa F h12 x)
  exact RMKummerLocalNormArtin.transported_normConductorArtin_local F
    (RMKummerConductor.E F h12 x)
    (M F (RMKummerConductor.m F h12 x) (RMKummerConductor.m_ne_bot F h12 x))
    (RMKummerConductor.modulus_eq_normConductor F h12 x) v t

end
end DedekindZetaZeroFree.RMKummerLocalNormCharacter
