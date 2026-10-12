module

public import DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
namespace DedekindZetaZeroFree.KPLiteralChamber
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
private theorem sqrt_eq_halfPower (r : ℝ) (hr : 0 < r) :
    (Real.sqrt r : ℂ) = KPGlobalExceptionalParameter.realLogPower r (1 / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr, Complex.ofReal_exp]
  unfold KPGlobalExceptionalParameter.realLogPower
  congr 1
  push_cast
  ring
 theorem normalized_multiplier (s : ℂ) (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    KPGlobalExceptionalParameter.realLogPower
      (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) (1 / 2 + s) =
    KPGlobalTorusFunctionData.deltaHalf F ζ hζ t *
      KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ s t := by
  have hr : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) := by
    exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero _))
  unfold KPGlobalTorusFunctionData.deltaHalf
  rw [sqrt_eq_halfPower _ hr]
  unfold KPGlobalExceptionalParameter.realLogPower KPGlobalTorusBorelTwistCompatibility.normPower
  rw [add_mul, Complex.exp_add]

def literalSource (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K) (s : ℂ) :
    KPMsRationalCompactCrossPairing.Source F ζ hζ s := by
  refine ⟨f.val s, ?_⟩
  intro r x g
  have h := (f.property.1 s).2 r x g
  rw [normalized_multiplier] at h
  change _ = KPGlobalTorusFunctionData.deltaHalf F ζ hζ r.val *
    ((KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) *
      KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ s r.val) * f.val s g
  rw [h]
  ring

theorem literal_unipotent_invariance (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K) (s : ℂ)
    (x : KPAdeles F) (g : G F ζ hζ) :
    f.val s (KPGlobalTorusFunctionData.N F ζ hζ x * g) = f.val s g := by
  have h := (f.property.1 s).2 1 x g
  simpa [KPGlobalExceptionalParameter.realLogPower] using h
end DedekindZetaZeroFree.KPLiteralChamber

end
