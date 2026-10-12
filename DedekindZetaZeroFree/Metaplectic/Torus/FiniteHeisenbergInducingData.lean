module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.OpenBruhatCellCorrespondence
public import DedekindZetaZeroFree.Metaplectic.Torus.Cubic.CubeClassesAndCenterCoordinates
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.CubicBeta.JointStripIntegrability
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ExceptionalFactorSeparation

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLocalExceptionalConstruction
open KPLocalPrincipalSeries KPLocalStoneVonNeumann
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

abbrev LocalField := q.adicCompletion F
abbrev ActualCover := KPRankOneOpenCellKernel.Cover F ζ hζ q

instance localValuativeRel : ValuativeRel (LocalField F q) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F q
instance localNonarchimedean : IsNonarchimedeanLocalField (LocalField F q) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q
instance localMeasurableSpace : MeasurableSpace (LocalField F q) :=
  borel (LocalField F q)
instance localBorelSpace : BorelSpace (LocalField F q) := ⟨rfl⟩

abbrev actualTorus := KPLocalSmoothRepresentation.Torus F ζ hζ q
abbrev actualBorel := KPLocalSmoothRepresentation.Borel F ζ hζ q
abbrev actualCubeClasses := KPLocalTorus.CubeClasses (LocalField F q)ˣ

def ordinaryIota : rootsOfUnity 3 F →* ℂˣ :=
  (KPLocalCover.coefficientEmbedding F ζ hζ).comp (KPLocalCover.threeToSix F)

structure CanonicalFiniteInducingData where
  D : Type
  [groupD : CommGroup D]
  [finiteD : Finite D]
  cubeClassEquiv : D ≃* actualCubeClasses F q
  heisenberg : LocalHeisenbergData (actualTorus F ζ hζ q) D
  borel : LocalBorelData (K := LocalField F q) (G := ActualCover F ζ hζ q) heisenberg
  borel_eq : borel.B = actualBorel F ζ hζ q
  torus_full : ∀ t : actualTorus F ζ hζ q,
    (borel.torus t : ActualCover F ζ hζ q) = (t : ActualCover F ζ hζ q)
  coordinate_lift : ∀ t : actualTorus F ζ hζ q, ∀ y : (LocalField F q)ˣ,
    (t : ActualCover F ζ hζ q) = KPPGLLocalCover.A F ζ hζ (Sum.inr q) y →
      borel.coordinate t = y
  cube_class : ∀ t : actualTorus F ζ hζ q,
    cubeClassEquiv (heisenberg.π t) =
      QuotientGroup.mk (borel.coordinate t)
  center_exact : heisenberg.C = Subgroup.center (actualTorus F ζ hζ q)
  cube_actual : ∀ y : (LocalField F q)ˣ,
    ((borel.cubeLift y : actualTorus F ζ hζ q) : ActualCover F ζ hζ q) =
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) (y ^ 3)
  central : rootsOfUnity 3 F →* heisenberg.C
  central_actual : ∀ e,
    ((central e : actualTorus F ζ hζ q) : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e
  central_character : ∀ e, heisenberg.ω (central e) = ordinaryIota F ζ hζ e
  center_parameterization : ∀ c : heisenberg.C,
    ∃ (e : rootsOfUnity 3 F) (x y : (LocalField F q)ˣ),
      c = central e * borel.cubeLift (x / y)
  prescribed_center : ∀ (e : rootsOfUnity 3 F) (x y : (LocalField F q)ˣ),
    (heisenberg.ω (central e * borel.cubeLift (x / y)) : ℂ) =
      (ordinaryIota F ζ hζ e : ℂ) * normPower (LocalField F q) (x ^ 3 / y ^ 3) (1 / 6)
  split_scalars : ∀ z : (LocalField F q)ˣ,
    KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) z) = 1
  polarization : Polarization heisenberg
  iwasawa : IwasawaData borel
  openCell : ∀ P : Polarization heisenberg,
    KPRankOneOpenCellKernel.Binding F ζ hζ q borel P
  openCell_ordinary : ∀ P : Polarization heisenberg,
    (openCell P).eta = ordinaryIota F ζ hζ

attribute [instance] CanonicalFiniteInducingData.groupD CanonicalFiniteInducingData.finiteD

end
end DedekindZetaZeroFree.KPLocalExceptionalConstruction
