module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.BorelRationalFibers

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPActualReflectionData.ScalarFiberInverse renaming fiber_covariance → fiber_covariance
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false

def inducedVector (f : Functions F ζ hζ) (hf : Induced F ζ hζ 0 f) :
    KPGlobalTorusBorelTwistCompatibility.InducedFunctions F ζ hζ
      (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ) :=
  ⟨inducedRationalFiber A f hf, by
    intro t x g
    apply Subtype.ext
    apply Subtype.ext
    funext u
    exact fiber_covariance F ζ hζ (inducedBorel A f hf) t x g u⟩

@[simp] theorem inducedVector_apply (f : Functions F ζ hζ) (hf : Induced F ζ hζ 0 f)
    (g : G F ζ hζ) (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    ((inducedVector A f hf).val g).val.val t =
      (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ * f (t.val * g) := rfl

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
