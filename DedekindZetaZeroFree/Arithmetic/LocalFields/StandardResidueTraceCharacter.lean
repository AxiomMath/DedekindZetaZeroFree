module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.ReciprocityAndGenuineCharacterConventions
public import DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData
public import DedekindZetaZeroFree.Adeles.Characters.StandardAdditiveCharacter
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.CodifferentTraceDuality

@[expose] public section

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.PrincipalMellinSource.ProfileCore.FixedSupport

variable {F : Type} [Field F] [NumberField F]

abbrev StandardResidue (p : KPFinitePlace F) :=
  IsLocalRing.ResidueField (p.adicCompletionIntegers F)

def standardReduction (p : KPFinitePlace F) :
    p.adicCompletionIntegers F →+* StandardResidue p := IsLocalRing.residue _

def standardResidueFieldEquiv (p : KPFinitePlace F) :
    StandardResidue p ≃+* (𝓞 F ⧸ p.asIdeal) :=
  (GlobalClassFieldTheory.ClassFieldAxiom.ringOfIntegersQuotientEquivAdicResidueField p).symm

instance standardResidueFinite (p : KPFinitePlace F) : Finite (StandardResidue p) := by
  letI := Ideal.finiteQuotientOfFreeOfNeBot p.asIdeal p.ne_bot
  exact Finite.of_equiv (𝓞 F ⧸ p.asIdeal) (standardResidueFieldEquiv p).symm.toEquiv

end DedekindZetaZeroFree.PrincipalMellinSource.ProfileCore.FixedSupport

end
