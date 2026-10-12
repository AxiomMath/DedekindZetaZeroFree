module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveConductorLowerBound
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.ConductorSupportUpperBound
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.ExistsAbelianConductor
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.AbelianConductorFiniteSupport

@[expose] public section

open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.LargeSieve

theorem quadratic_primitive_ramification
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I)
    (hn : ¬η.IsPrincipal) (hp : η.IsPrimitive)
    (d : QuadraticRayExtensionData η)
    (p : HeightOneSpectrum (𝓞 F)) :
    p.asIdeal ⊔ f ≠ ⊤ ↔
      ∃ Q : HeightOneSpectrum (𝓞 d.extension),
        Q.asIdeal.LiesOver p.asIdeal ∧
          ¬ Algebra.IsUnramifiedAt (𝓞 F) Q.asIdeal := by
  obtain ⟨c, hc⟩ := ClassFieldTheory.exists_abelianConductor F d.extension
  constructor
  · intro hbad
    exact (hc.mem_finiteSupport_iff_exists_ramified p).mp
      (RootNumber.primitive_conductor_support_lower F hF f hf η hq hn hp d c hc p hbad)
  · rintro ⟨Q, hQ, hram⟩
    exact RootNumber.conductor_support_upper F hF f hf η hq hn d c hc p
      ((hc.mem_finiteSupport_iff_exists_ramified p).mpr ⟨Q, hQ, hram⟩)

end DedekindZetaZeroFree.LargeSieve
