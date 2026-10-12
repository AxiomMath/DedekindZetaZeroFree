module

public import DedekindZetaZeroFree.LFunctions.Hecke.PrimeArtinValues

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField
open IsDedekindDomain

theorem inertiaRestrictIntermediate
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    (E : IntermediateField K L)
    (wE : HeightOneSpectrum (𝓞 ↥E)) (wL : HeightOneSpectrum (𝓞 L))
    (hwL : wL.asIdeal.LiesOver wE.asIdeal) :
    (Ideal.inertia (L ≃ₐ[K] L) wL.asIdeal).map (AlgEquiv.restrictNormalHom ↥E) =
      Ideal.inertia (↥E ≃ₐ[K] ↥E) wE.asIdeal := by
  let H := fixingSubgroup (L ≃ₐ[K] L) (E : Set L)
  letI : wL.asIdeal.LiesOver wE.asIdeal := hwL
  haveI : IsGaloisGroup H E L := by dsimp [H]; infer_instance
  haveI : IsGaloisGroup H (𝓞 E) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing H (𝓞 E) (𝓞 L) E L
  haveI : Algebra.IsInvariant (𝓞 E) (𝓞 L) H := inferInstance
  apply Ideal.map_inertia_of_surjective (AlgEquiv.restrictNormalHom ↥E) H
    wE.asIdeal wL.asIdeal
    (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥E) L)
  · intro g hg
    change g.restrictNormal E = 1
    exact (AlgEquiv.restrictNormal_eq_one_iff E g).mpr
      ((mem_fixingSubgroup_iff (L ≃ₐ[K] L)).mp hg)
  · intro g x
    apply NumberField.RingOfIntegers.ext
    change algebraMap E L ((g.restrictNormal E) (x : E)) =
      g (algebraMap E L (x : E))
    exact AlgEquiv.restrictNormal_commutes g E (x : E)

end DedekindZetaZeroFree.AbelianQuotient
