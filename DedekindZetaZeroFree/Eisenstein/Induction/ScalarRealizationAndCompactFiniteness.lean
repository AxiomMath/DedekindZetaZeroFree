module

public import DedekindZetaZeroFree.Eisenstein.Residues.MetaplecticRealizations
public import DedekindZetaZeroFree.Metaplectic.Torus.BorelTwistCompatibility

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField MeasureTheory
set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.EisensteinReferenceSections.SeedScalarTransport
open KPGlobalTorusBorelTwistCompatibility
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance (P : Polarization F ζ hζ) : TopologicalSpace (Induced F ζ hζ P) :=
  inducedTopology F ζ hζ P

def scalar (P : Polarization F ζ hζ) :
    Induced F ζ hζ P →ₗ[ℂ] (G F ζ hζ → ℂ) :=
  (KPGlobalTorusFunctionData.BorelFunctions F ζ hζ P).subtype.comp
    (scalarSection F ζ hζ P)

@[simp] theorem scalar_apply (P : Polarization F ζ hζ)
    (f : Induced F ζ hζ P) (g : G F ζ hζ) :
    scalar F ζ hζ P f g = (scalarSection F ζ hζ P f).val g := rfl

theorem normalized_multiplier (s : ℂ) (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    KPGlobalExceptionalParameter.realLogPower
      (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) (1 / 2 + s) =
    KPGlobalTorusFunctionData.deltaHalf F ζ hζ t * normPower F ζ hζ s t := by
  have hr : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) := by
    exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hh : (Real.sqrt (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) : ℂ) =
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) (1 / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr, Complex.ofReal_exp]
    unfold KPGlobalExceptionalParameter.realLogPower
    congr 1
    push_cast
    ring
  unfold KPGlobalTorusFunctionData.deltaHalf
  rw [hh]
  unfold KPGlobalExceptionalParameter.realLogPower normPower
  rw [add_mul, Complex.exp_add]

variable (C : ModelData F ζ hζ) (s : ℂ)

def inducedEquiv :
    Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) ≃ₗ[ℂ]
      Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) where
  toLinearMap := (borelP F ζ hζ C s).toLinearMap
  invFun := borelQ F ζ hζ C s
  left_inv := borelQ_borelP F ζ hζ C s
  right_inv := borelP_borelQ F ζ hζ C s

end DedekindZetaZeroFree.EisensteinReferenceSections.SeedScalarTransport

end
