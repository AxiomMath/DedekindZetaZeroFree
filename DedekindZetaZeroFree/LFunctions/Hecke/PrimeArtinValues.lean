module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField

abbrev ComplexDual (G : Type*) [Group G] := G →* ℂˣ

noncomputable instance instFintypeComplexDual (G : Type*) [CommGroup G] [Finite G] :
    Fintype (ComplexDual G) := by
  letI : Fintype G := Fintype.ofFinite G
  exact Fintype.ofEquiv G
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ).some.toEquiv.symm

noncomputable def primeArtinValue
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    (ρ : ComplexDual (L ≃ₐ[K] L))
    (W : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) : ℂ := by
  classical
  exact if Ideal.inertia (L ≃ₐ[K] L) W.asIdeal ≤ ρ.ker then
    (ρ (ClassFieldTheory.arithmeticFrobeniusAt (K := K) W) : ℂ) else 0

end DedekindZetaZeroFree.AbelianQuotient
