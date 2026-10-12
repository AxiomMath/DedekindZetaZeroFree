module

public import DedekindZetaZeroFree.Adeles.Quotients.Additive.FiniteLevelDetection
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.Tori.CharacterSeparation

@[expose] public section

namespace DedekindZetaZeroFree.AdelicSeparation

open scoped NumberField
open NumberField IsDedekindDomain

theorem additiveAdeleQuotient_characters_separate
    (F : Type) [Field F] [NumberField F]
    (x y : AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) (hxy : x ≠ y) :
    ∃ χ : AddChar (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) Circle,
      Continuous χ ∧ χ x ≠ χ y := by
  obtain ⟨K, hKc, hKo, hKxy⟩ := nonzero_survives_finiteLevel F (x - y)
    (sub_ne_zero.mpr hxy)
  let p := QuotientAddGroup.mk' (finiteLevelImage K)
  have hp : p x ≠ p y := by
    intro h
    apply hKxy
    change p (x - y) = 0
    rw [map_sub, h, sub_self]
  obtain ⟨e⟩ := (finiteLevel_single_torus K hKc hKo).2.2.2
  obtain ⟨ψ, hψ, hψxy⟩ := unitAddTorus_characters_separate (e (p x)) (e (p y))
    (fun h => hp (e.injective h))
  let χ := ψ.compAddMonoidHom (e.toAddEquiv.toAddMonoidHom.comp p)
  refine ⟨χ, ?_, hψxy⟩
  exact hψ.comp (e.continuous.comp (QuotientAddGroup.continuous_mk (N := finiteLevelImage K)))

end DedekindZetaZeroFree.AdelicSeparation
