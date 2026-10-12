module

public import DedekindZetaZeroFree.Metaplectic.Weil.QuadraticFourierOperatorsAndPhases

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.OddEvaluation

variable {F : Type} [Field F] [NumberField F]

abbrev Residue (v : HeightOneSpectrum (𝓞 F)) :=
  IsLocalRing.ResidueField (v.adicCompletionIntegers F)

abbrev residueFintype (v : HeightOneSpectrum (𝓞 F)) : Fintype (Residue v) :=
  @Fintype.ofFinite _ (SArithmeticData.exteriorLocalResidue_finite v)

attribute [local instance] residueFintype

abbrev localUnit (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletionIntegers F)ˣ →* (v.adicCompletion F)ˣ :=
  Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom

abbrev uniformizer (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) :
    (v.adicCompletion F)ˣ :=
  Units.mk0 (π : v.adicCompletion F) (by
    intro h
    exact hπ.ne_zero (Subtype.ext h))

abbrev conductor (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ) : Prop :=
  (∀ x : v.adicCompletionIntegers F,
    ResidueTrace.localTraceCharacter v
      (((uniformizer v π hπ)^c : (v.adicCompletion F)ˣ) *
        (x : v.adicCompletion F)) = 1) ∧
  ∃ x : v.adicCompletionIntegers F,
    ResidueTrace.localTraceCharacter v
      (((uniformizer v π hπ)^(c-1) : (v.adicCompletion F)ˣ) *
        (x : v.adicCompletion F)) ≠ 1

abbrev theta (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (x : Residue v) : Circle :=
  ((ResidueTrace.localTraceCharacter v).compAddMonoidHom
    (AddMonoidHom.mulLeft (((uniformizer v π hπ)^c :
      (v.adicCompletion F)ˣ) : v.adicCompletion F)))
    (((Classical.choose (IsLocalRing.residue_surjective x) :
      v.adicCompletionIntegers F) : v.adicCompletion F) / (π : v.adicCompletion F))

abbrev quadratic (v : HeightOneSpectrum (𝓞 F))
    (x : Residue v) : ℂ := (quadraticChar (Residue v) x : ℂ)

abbrev epsilon (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ) : ℂ :=
  (∑ x : Residue v, (theta v π hπ c (x^2) : ℂ)) /
    (Real.sqrt (Fintype.card (Residue v)) : ℂ)

end DedekindZetaZeroFree.OddEvaluation

end
