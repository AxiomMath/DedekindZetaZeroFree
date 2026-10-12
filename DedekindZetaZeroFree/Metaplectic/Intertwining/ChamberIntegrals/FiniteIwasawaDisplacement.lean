module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Residues.ArchimedeanTraceCofactor

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.FiniteDisplacement
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPLocalExceptionalConstruction

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem compact_extension_displacement
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (φ : compactPicture S.borel P S.iwasawa .plus) (s : ℂ)
    (g : ActualCover F ζ hζ q) :
    (compactTrivialization S.borel P S.iwasawa .plus s φ).val g =
      normPower (LocalField F q) (S.borel.coordinate
        (S.borel.retract (S.iwasawa.borelPart g))) s •
        (compactTrivialization S.borel P S.iwasawa .plus 0 φ).val g := by
  change (inducingScalar S.borel s (S.iwasawa.borelPart g)) •
      (borelAction S.borel P .plus (S.iwasawa.borelPart g)) (φ.val (S.iwasawa.compactPart g)) = _
  change _ = normPower (LocalField F q) _ s •
    ((inducingScalar S.borel 0 (S.iwasawa.borelPart g)) •
      (borelAction S.borel P .plus (S.iwasawa.borelPart g)) (φ.val (S.iwasawa.compactPart g)))
  simp only [inducingScalar, normPower, zero_mul, Complex.exp_zero, mul_one, smul_smul]
  rw [mul_comm]

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.FiniteDisplacement

end
