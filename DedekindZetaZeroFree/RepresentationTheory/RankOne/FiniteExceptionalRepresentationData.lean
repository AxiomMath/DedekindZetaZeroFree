module

public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.OrbitMapInjectivity
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Cubic.ExceptionalImagesAndDualWhittaker
public import DedekindZetaZeroFree.Theta.Whittaker.DiagonalCharacterTransport
public import DedekindZetaZeroFree.Algebra.DualTestsForIndependentVectors
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ReverseFiniteMinor.FrequencyNormalization
public import DedekindZetaZeroFree.CharacterSums.Gauss.TameIntertwiningResidueCharacters
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ReverseFiniteMinor.FrequencyTransport
public import DedekindZetaZeroFree.Metaplectic.Weil.ReverseIntertwiningPolarizationNaturality
public import DedekindZetaZeroFree.Algebra.RangeRankFromDiagonalPairings
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.TameTwistedCoinvariantRank
public import DedekindZetaZeroFree.Algebra.QuotientRankBounds
public import DedekindZetaZeroFree.Eisenstein.Induction.UnramifiedCompactFixedSections

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPLocalExceptionalConstruction

open KPLocalPrincipalSeries KPLocalStoneVonNeumann
open KPRankOneShellContinuation KPRankOneForwardTestVector

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

variable (S : CanonicalFiniteInducingData F ζ hζ q)

def actualGoodCompactSplit
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) :
    KPTameCompact.K0 F q →* ActualCover F ζ hζ q :=
  (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
    (KPGoodCompactSplitting.kStar F ζ hζ q ht)

end
end DedekindZetaZeroFree.KPLocalExceptionalConstruction
