module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.FiniteGroupInsertionAndTorusLifts

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace DedekindZetaZeroFree.KPLiteralScalarHCFiniteCharacter
open KPGlobalProductPolarizationCharacter KPGlobalTorusBorelTwistCompatibility
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P)
open _root_.DedekindZetaZeroFree.KPGlobalProductPolarizationCharacter renaming rawCoordinate_val → rawCoordinate_val

theorem rawCoordinate_eq_one (x : rawB F ζ hζ P.localData) (v : KPHilbert.Place F)
    (hv : x.val v = 1) : rawCoordinate F ζ hζ P.localData x v = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  rw [rawCoordinate_val, hv, map_one]
  rfl

theorem lambdaB_single_finite
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (b : B F ζ hζ P.localData) (x : rawB F ζ hζ P.localData)
    (hs : ∀ v : KPHilbert.Place F, v ≠ Sum.inr q → x.val v = 1)
    (hx : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = b.val.val) :
    lambdaB F ζ hζ P.localData P.adjustment b =
      adjustedLocalValue F ζ hζ P.localData P.adjustment (Sum.inr q)
        (rawCoordinate F ζ hζ P.localData x (Sum.inr q)) := by
  rw [lambdaB_raw_formula F ζ hζ P.localData P.adjustment b x hx]
  apply finprod_eq_single
  intro v hv
  rw [rawCoordinate_eq_one F ζ hζ P x v (hs v hv)]
  simp only [adjustedLocalValue, map_one, one_mul]
  convert map_one (P.adjustment.chi v) using 1
  congr 1
  apply Subtype.ext
  exact map_one _

theorem lambdaB_single_finite_heisenberg
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (b : B F ζ hζ P.localData) (x : rawB F ζ hζ P.localData)
    (a : (C.polarization q).L.comap (C.canonical q).heisenberg.π)
    (hs : ∀ v : KPHilbert.Place F, v ≠ Sum.inr q → x.val v = 1)
    (hx : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = b.val.val)
    (ha : a.val.val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (x.val (Sum.inr q))) :
    lambdaB F ζ hζ P.localData P.adjustment b = (C.polarization q).ωL a := by
  rw [lambdaB_single_finite F ζ hζ P q b x hs hx]
  symm
  apply C.character_matches q a (rawCoordinate F ζ hζ P.localData x (Sum.inr q))
  exact ha.trans (rawCoordinate_val F ζ hζ P.localData x (Sum.inr q)).symm

variable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
variable (f : Flat F ζ hζ K)

end DedekindZetaZeroFree.KPLiteralScalarHCFiniteCharacter

end
