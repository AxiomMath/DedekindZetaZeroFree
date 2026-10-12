module

public import DedekindZetaZeroFree.Metaplectic.Weil.CubicCorrection.ExtensionData
public import DedekindZetaZeroFree.CharacterSums.DavenportHasse.PrimeGaussIdentities

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

theorem corrected_primeGaussLaws
    (A : SArithmeticData F) (hS : A.ContainsTraceBadPlaces) (σ : F →+* ℂ)
    (H : A.V → A.V → Fˣ) (B : Subgroup A.V)
    (hActual : ∀ x y : A.G, H (QuotientGroup.mk' A.sixthPowers x)
      (QuotientGroup.mk' A.sixthPowers y) = (A.H_S x y : Fˣ))
    (hB : A.IsSUnitIsotropicComplement H B)
    (W : CorrectedWeilExtension A H B σ hS) :
    (∀ (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F))
      (hIv : I.val = v.asIdeal) (p : A.R) (hp : A.Generates I p)
      (a : Fˣ) (ha : A.IsAllowed B a) (hap : (a : F) = (p : F)),
        A.idealGauss σ hS I p hp 2 ^ 3 =
          -DHCubic.lambda F A (σ.comp (algebraMap (DHCubic.E0 F A) F)) I.val) ∧
    (∀ (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F))
      (hIv : I.val = v.asIdeal) (p : A.R) (hp : A.Generates I p)
      (a : Fˣ) (ha : A.IsAllowed B a) (hap : (a : F) = (p : F))
      (x : NumberField.IdeleGroup (𝓞 F) F), A.RepresentsExteriorIdeal I x →
        A.idealGauss σ hS I p hp 1 * A.idealGauss σ hS I p hp 2 =
          -DHCubic.lambda F A (σ.comp (algebraMap (DHCubic.E0 F A) F)) I.val *
            (W.G (QuotientGroup.mk x) : ℂ)) := by
  constructor
  · intro I v hIv p hp a ha hap
    exact (primeGaussIdentities A hS σ B I v hIv p hp a ha hap).1
  · intro I v hIv p hp a ha hap x hx
    obtain ⟨hcub, hdup⟩ := primeGaussIdentities A hS σ B I v hIv p hp a ha hap
    rw [hdup, hcub, W.prime I v hIv p hp a ha hap x hx]
    ring

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection
