module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.OppositeCompositionVanishing
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.UnramifiedSphericalImage
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.TameBruhatTestDuality

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneOppositeZero KPRankOneForwardTestVector
open KPTameJacquetTestDuality
open KPTameValuationCoordinates

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)

variable (coordinates : ∀ ε : Sign,
  sectionSpace S.borel P ε 0 ≃ₗ[ℂ] scalarSections F ζ hζ q S P hP ε)

variable (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (ξ : (valuation (LocalField F q)).integer) (hξ : IsPrimitiveRoot ξ 3)

def deformedTest (f : scalarSections F ζ hζ q S P hP .minus) (s : ℂ) :
    sectionSpace S.borel P .minus (sourceParameter .minus s) :=
  compactTrivialization S.borel P S.iwasawa .minus (sourceParameter .minus s)
    ((compactTrivialization S.borel P S.iwasawa .minus 0).symm
      ((coordinates .minus).symm f))

def HasStableIntegral (π : (LocalField F q)ˣ) (g : LocalField F q → ℂ) (z : ℂ) : Prop :=
  ∃ r₀ : ℕ, ∀ r ≥ r₀,
    IntegrableOn g (expandingBall F q π r) μ ∧
      (∫ x in expandingBall F q π r, g x ∂μ) = z

def diagonalLift (π : (LocalField F q)ˣ) (f : DiagonalValuations) :
    ActualCover F ζ hζ q :=
  KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
    (KPLocalCover.sectionMap F ζ hζ (Sum.inr q)
      (KubotaRankTwo.d (LocalField F q) (π ^ f.1) (π ^ f.2)))

def testSupport (a : ActualCover F ζ hζ q) (m : ℕ) : Set (ActualCover F ζ hζ q) :=
  {g | ∃ (b : BL F ζ hζ q S P) (k : ActualCover F ζ hζ q),
    k ∈ splitCongruenceSet F ζ hζ q m ∧
      g = b * a * k * KPPGLLocalCover.W F ζ hζ (Sum.inr q)}

def IsMinusTest (a : ActualCover F ζ hζ q) (m : ℕ)
    (f : scalarSections F ζ hζ q S P hP .minus) : Prop :=
  (∀ k ∈ splitCongruenceSet F ζ hζ q m,
    scalarAction F ζ hζ q S P hP .minus k f = f) ∧
  Function.support f.val ⊆ testSupport F ζ hζ q S P a m ∧
  f.val (a * KPPGLLocalCover.W F ζ hζ (Sum.inr q)) = 1

def lowShell : Set (LocalField F q) := (valuation (LocalField F q)).integer

def conductorOneShell (π : (LocalField F q)ˣ) : Set (LocalField F q) :=
  expandingBall F q π 1 \ lowShell F q

end DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw

end
