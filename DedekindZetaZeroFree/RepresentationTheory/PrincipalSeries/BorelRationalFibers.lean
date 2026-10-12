module

public import DedekindZetaZeroFree.Eisenstein.Residues.MetaplecticRealizations
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarFiberSmoothInverse

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPLiteralRaw
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def inducedBorel (f : Functions F ζ hζ) (hf : Induced F ζ hζ 0 f) :
    KPGlobalTorusFunctionData.BorelFunctions F ζ hζ
      (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ) :=
  ⟨f, by
    intro r x g
    have hd : KPGlobalTorusFunctionData.deltaHalf F ζ hζ r.val =
        KPGlobalExceptionalParameter.realLogPower
          (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1/2 : ℂ) := by
      unfold KPGlobalTorusFunctionData.deltaHalf KPGlobalExceptionalParameter.realLogPower
      have hδ : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) := by
        exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero _))
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hδ, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    change f ((r.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ r.val *
        (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) * f g
    simpa only [add_zero, hd] using hf.2 r x g⟩

def inducedRationalFiber (f : Functions F ζ hζ) (hf : Induced F ζ hζ 0 f)
    (g : KPLiteralRaw.G F ζ hζ) : ↥(smoothRationalFiber F ζ hζ) := by
  refine ⟨KPActualReflectionData.ScalarFiberInverse.fiber F ζ hζ (inducedBorel A f hf) g, ?_⟩
  obtain ⟨J,hJ⟩ := hf.1.2.2
  exact KPActualReflectionData.SmoothScalarInverse.fiber_mem_smoothUnion
    F ζ hζ (inducedBorel A f hf) J (fun a j => hJ a j.val j.property) g

@[simp] theorem inducedRationalFiber_apply (f : Functions F ζ hζ)
    (hf : Induced F ζ hζ 0 f) (g : KPLiteralRaw.G F ζ hζ)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    (inducedRationalFiber A f hf g).val.val t =
      (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ * f (t.val * g) := rfl

theorem inducedRationalFiber_one (f : Functions F ζ hζ)
    (hf : Induced F ζ hζ 0 f) (g : KPLiteralRaw.G F ζ hζ) :
    (inducedRationalFiber A f hf g).val.val 1 = f g := by
  rw [inducedRationalFiber_apply]
  simp [KPGlobalTorusFunctionData.deltaHalf]

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
