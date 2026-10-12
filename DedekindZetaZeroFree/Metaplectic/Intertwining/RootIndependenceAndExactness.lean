module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.FiniteExceptionalRepresentationData

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace DedekindZetaZeroFree.KPLocalTameIntertwiningBlock
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneForwardTestVector KPRankOneOppositeZero

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))

section LegacyRootCompatibility
variable (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (ξ ξ' : (valuation (LocalField F q)).integer)
  (hξ : IsPrimitiveRoot ξ 3) (hξ' : IsPrimitiveRoot ξ' 3)

end LegacyRootCompatibility

def rawInducingAlias (S : CanonicalFiniteInducingData F ζ hζ q) :
    KPExceptionalRaw.RawFiniteInducingData F ζ hζ q where
  D := S.D
  groupD := S.groupD
  finiteD := S.finiteD
  cubeClassEquiv := S.cubeClassEquiv
  heisenberg := S.heisenberg
  borel := S.borel
  borel_eq := S.borel_eq
  torus_full := S.torus_full
  coordinate_lift := S.coordinate_lift
  cube_class := S.cube_class
  center_exact := S.center_exact
  cube_actual := S.cube_actual
  central := S.central
  central_actual := S.central_actual
  central_character := S.central_character
  center_parameterization := S.center_parameterization
  prescribed_center := S.prescribed_center
  split_scalars := S.split_scalars
  polarization := S.polarization
  iwasawa := S.iwasawa
  openCell := S.openCell
  openCell_ordinary := S.openCell_ordinary

end DedekindZetaZeroFree.KPLocalTameIntertwiningBlock

end
