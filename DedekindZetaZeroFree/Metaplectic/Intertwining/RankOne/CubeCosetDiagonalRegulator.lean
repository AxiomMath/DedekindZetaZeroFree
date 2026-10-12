module

public import DedekindZetaZeroFree.Metaplectic.Torus.CenterInductionDiagonalAction
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.IteratedCenterKernelsAndCubeCosets

@[expose] public section

section

namespace DedekindZetaZeroFree.KPRankOneLiftedRegulatedDiagonalAlgebra

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H D : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)

def sourceTranslation (a b u v : (LocalField F q)ˣ) : LocalField F q :=
  (a : LocalField F q) * (u : LocalField F q) ^ 3 +
    (b : LocalField F q) * (v : LocalField F q) ^ 3

def reverseIncrement (b v : (LocalField F q)ˣ) : (LocalField F q)ˣ := b * v ^ 3

def doubleKernel (B : Binding F ζ hζ q A P)
    (rep : D → H) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (z lam : ℂ) (h : H)
    (a b u v : (LocalField F q)ˣ) : ℂ :=
  let ξ := a * u ^ 3
  let η := reverseIncrement F q b v
  (B.eta (kappa F ζ hζ q η 0) : ℂ) *
    (B.eta (kappa F ζ hζ q ξ (η : LocalField F q)) : ℂ) *
    normPower (LocalField F q) (η ^ 2) (-z) *
    normPower (LocalField F q) (ξ ^ 2) z *
    ((centerTorus F ζ hζ q T A .minus (B.rootTorus η))
      ((centerTorus F ζ hζ q T A .plus (B.rootTorus ξ))
        ((centerCoordinates T rep hrep).symm
          (φ (sourceTranslation F q a b u v) • Pi.single d (1 : ℂ))))).val h *
    normPower (LocalField F q) η lam

end

end DedekindZetaZeroFree.KPRankOneLiftedRegulatedDiagonalAlgebra

end
