module

public import DedekindZetaZeroFree.Eisenstein.Sections.FullProductFlatFamily
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData
public import DedekindZetaZeroFree.Metaplectic.Torus.GlobalInduction

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal

namespace DedekindZetaZeroFree.KPContFlatSourceRecipe

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev D := KPContFlatFullProductIwasawa.iwasawaData F ζ hζ

abbrev alpha := KPContFlatFullProductIwasawa.alpha F ζ hζ

end DedekindZetaZeroFree.KPContFlatSourceRecipe

end

section

noncomputable section
set_option maxHeartbeats 10000000
open scoped Classical NumberField NNReal

namespace DedekindZetaZeroFree.KPContFlatSourceRecipe

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev P₀ := KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ

theorem sourcePolarization_zero :
    KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0 = P₀ F ζ hζ := by
  unfold KPMsRationalCompactCrossPairing.sourcePolarization
  unfold KPGlobalTorusBorelTwistCompatibility.twist
  congr 1
  ext h
  change ((P₀ F ζ hζ).character h : ℂ) *
    KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ 0 h.val =
      ((P₀ F ζ hζ).character h : ℂ)
  simp [KPGlobalTorusBorelTwistCompatibility.normPower]

private theorem scalarCastValue
    (Q Q' : KPGlobalTorusFunctionData.Polarization F ζ hζ) (h : Q = Q')
    (f : KPGlobalTorusFunctionData.BorelFunctions F ζ hζ Q)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    (((congrArg (fun T => ↥(KPGlobalTorusFunctionData.BorelFunctions F ζ hζ T))
      h).mp f).val g) = f.val g := by
  cases h
  rfl

def baseSection (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (D F ζ hζ)) :
    KPGlobalTorusFunctionData.BorelFunctions F ζ hζ (P₀ F ζ hζ) :=
  (congrArg (fun Q => ↥(KPGlobalTorusFunctionData.BorelFunctions F ζ hζ Q))
    (sourcePolarization_zero F ζ hζ)).mp f.val

@[simp] theorem baseSection_formula
    (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (D F ζ hζ))
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    (baseSection F ζ hζ f).val g = f.val.val g := by
  exact scalarCastValue F ζ hζ _ _ (sourcePolarization_zero F ζ hζ) f.val g

def flatR (s : ℂ) :
    KPMsRationalCompactCrossPairing.Vplus F ζ hζ (D F ζ hζ) →ₗ[ℂ]
      KPMsRationalCompactCrossPairing.Source F ζ hζ s where
  toFun f := ⟨fun g => Complex.exp (s * (alpha F ζ hζ g : ℂ)) * f.val.val g,
    by
      intro h x g
      have hf := f.val.property h x g
      have ha := KPContFlatFullProductIwasawa.alpha_borel_mul F ζ hζ h.val x g
      change Complex.exp (s * (alpha F ζ hζ
        ((h.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) : ℂ)) *
          f.val.val ((h.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) = _
      change alpha F ζ hζ ((h.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
        Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ h.val : ℝ≥0) : ℝ)) +
          alpha F ζ hζ g at ha
      rw [ha, Complex.ofReal_add, mul_add, Complex.exp_add, hf]
      change (Complex.exp (s * (Real.log
        (((KPGlobalTorusFunctionData.delta F ζ hζ h.val : ℝ≥0) : ℝ)) : ℂ)) *
          Complex.exp (s * (alpha F ζ hζ g : ℂ))) *
        (KPGlobalTorusFunctionData.deltaHalf F ζ hζ h.val *
          ((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).character h : ℂ) *
            f.val.val g) =
        KPGlobalTorusFunctionData.deltaHalf F ζ hζ h.val *
          ((P₀ F ζ hζ).character h *
            KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ s h.val : ℂ) *
              (Complex.exp (s * (alpha F ζ hζ g : ℂ)) * f.val.val g)
      change _ = KPGlobalTorusFunctionData.deltaHalf F ζ hζ h.val *
        (((P₀ F ζ hζ).character h : ℂ) *
          KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ s h.val) * _
      have hc : ((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).character h : ℂ) =
          ((P₀ F ζ hζ).character h : ℂ) := by
        change ((P₀ F ζ hζ).character h : ℂ) *
          KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ 0 h.val = _
        simp [KPGlobalTorusBorelTwistCompatibility.normPower]
      rw [hc]
      unfold KPGlobalTorusBorelTwistCompatibility.normPower
      ring⟩
  map_add' := by
    intro f j
    apply Subtype.ext
    funext g
    change _ * (f.val.val g + j.val.val g) = _
    exact mul_add _ _ _
  map_smul' := by
    intro c f
    apply Subtype.ext
    funext g
    change _ * (c * f.val.val g) = c * (_ * f.val.val g)
    ring

theorem flatR_formula (s : ℂ)
    (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (D F ζ hζ))
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    (flatR F ζ hζ s f).val g =
      Complex.exp (s * (alpha F ζ hζ g : ℂ)) * f.val.val g := by rfl

theorem flatR_zero
    (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (D F ζ hζ)) :
    flatR F ζ hζ 0 f = f.val := by
  apply Subtype.ext
  funext g
  simp [flatR_formula]

theorem flatR_compact (s : ℂ)
    (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (D F ζ hζ))
    (k : (D F ζ hζ).K) :
    (flatR F ζ hζ s f).val k.val = f.val.val k.val := by
  have ha : alpha F ζ hζ k.val = 0 := by
    have h := KPContFlatFullProductIwasawa.alpha_mul_compact F ζ hζ 1 k
    simpa using h
  simp [flatR_formula, ha]

variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

end DedekindZetaZeroFree.KPContFlatSourceRecipe

namespace DedekindZetaZeroFree

end DedekindZetaZeroFree

end
end
