module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.DoubleKernelFactorization

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain ValuativeRel
noncomputable section
namespace DedekindZetaZeroFree.KPActualResidueSources.UcProposal
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPRankOneOpenCellKernel
open KPRankOneLiftedRegulatedDiagonalAlgebra KPRankOneCenterInducedDiagonalComparison
open KPActualScalarBinding
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
variable [DecidableEq S.D]

def actualUc (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (c : (LocalField F q)ˣ) (s : ℂ) (h : KPExceptionalRaw.actualTorus F ζ hζ q) : ℂ :=
  doubleKernel F ζ hζ q S.heisenberg S.borel P (S.openCell P)
    rep hrep d (fun _ => 1) s 0 h 1 c 1 1

end DedekindZetaZeroFree.KPActualResidueSources.UcProposal

end
