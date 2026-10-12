module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ProductSections.ScalarCovariance
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.HarishChandraSectionExtraction

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages KPGlobalTorusBorelTwistCompatibility
open KPLiteralScalarHCExtraction
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
attribute [local instance] KPGlobalTorusPeriodizationInverse.modelTopology
local instance (Q : Polarization F ζ hζ) : TopologicalSpace (KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ Q) :=
  inducedTopology F ζ hζ Q

theorem originalProductFiber_HC (K : Subgroup (KPLiteralRaw.G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (g : KPLiteralRaw.G F ζ hζ) (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    (originalProductFiber A P (f.val 0) (f.property.1 0) g).val.val t =
      ((productHCSection F ζ hζ K hK P f).val.val g).val.val t := by
  have hz : (normTwist F ζ hζ (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ) 0).symm
      ((zeroHCSection F ζ hζ K hK f).val.val g) =
      inducedRationalFiber A (f.val 0) (f.property.1 0) g := by
    apply Subtype.ext
    apply Subtype.ext
    funext u
    rw [normTwist_inverse_formula,zeroHCSection_fiber]
    simp only [normPower,neg_zero,zero_mul,Complex.exp_zero,one_mul]
    rfl
  change _ = ((borelQ F ζ hζ P 0 (zeroHCSection F ζ hζ K hK f)).val.val g).val.val t
  rw [borelQ_fiberwise]
  change _ = (normTwist F ζ hζ (KPGlobalTorusBorelTwistCompatibility.productModel F ζ hζ P) 0
    (KPGlobalTorusPeriodizationInverse.averaging F ζ hζ P
      ((normTwist F ζ hζ (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ) 0).symm
        ((zeroHCSection F ζ hζ K hK f).val.val g)))).val.val t
  rw [normTwist_formula,hz]
  simp only [normPower,zero_mul,Complex.exp_zero,one_mul]
  rfl

theorem originalProductScalar_HC (K : Subgroup (KPLiteralRaw.G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    originalProductScalar A P (f.val 0) (f.property.1 0) = productHCScalar F ζ hζ K hK P f := by
  funext g
  exact originalProductFiber_HC A P K hK f g 1
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
