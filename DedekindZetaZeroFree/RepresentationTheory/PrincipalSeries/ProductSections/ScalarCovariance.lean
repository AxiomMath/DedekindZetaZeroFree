module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.InducedVectors
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.FiniteBorelReduction

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages KPGlobalTorusPeriodizationInverse
open KPLiteralScalarHCFiniteInsertion KPLiteralScalarHCFiniteCharacter KPLiteralScalarHCFiniteBorel
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
attribute [local instance] KPGlobalTorusPeriodizationInverse.modelTopology

def originalProductFiber (f : Functions F ζ hζ) (hf : KPLiteralRaw.Induced F ζ hζ 0 f)
    (g : G F ζ hζ) : ProductSmooth F ζ hζ P :=
  averaging F ζ hζ P (inducedRationalFiber A f hf g)

def originalProductScalar (f : Functions F ζ hζ) (hf : KPLiteralRaw.Induced F ζ hζ 0 f) :
    Functions F ζ hζ := fun g => (originalProductFiber A P f hf g).val.val 1

theorem originalProductFiber_covariance (f : Functions F ζ hζ)
    (hf : KPLiteralRaw.Induced F ζ hζ 0 f)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F) (g : G F ζ hζ) :
    originalProductFiber A P f hf ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x)*g) =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ t •
      KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ
        (KPGlobalTorusPeriodizationInverse.productModel F ζ hζ P) t (originalProductFiber A P f hf g) := by
  have h := (inducedVector A f hf).property t x g
  unfold originalProductFiber
  change averaging F ζ hζ P ((inducedVector A f hf).val _) = _
  rw [h,map_smul,averaging_intertwines]
  rfl

theorem originalProductScalar_borel (f : Functions F ζ hζ)
    (hf : KPLiteralRaw.Induced F ζ hζ 0 f)
    (b : KPGlobalProductPolarizationCharacter.B F ζ hζ P.localData)
    (x : KPAdeles F) (g : G F ζ hζ) :
    originalProductScalar A P f hf ((b.val.val * KPGlobalTorusFunctionData.N F ζ hζ x)*g) =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val *
        (KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P.localData P.adjustment b : ℂ) *
        originalProductScalar A P f hf g := by
  unfold originalProductScalar
  rw [originalProductFiber_covariance]
  change KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val *
    (originalProductFiber A P f hf g).val.val (1*b.val) = _
  rw [one_mul]
  have h := (originalProductFiber A P f hf g).val.property b 1
  change (originalProductFiber A P f hf g).val.val (b.val*1) = _ at h
  rw [mul_one] at h
  rw [h]
  exact (mul_assoc _ _ _).symm

theorem originalProductScalar_root (f : Functions F ζ hζ)
    (hf : KPLiteralRaw.Induced F ζ hζ 0 f) (x : KPAdeles F) (g : G F ζ hζ) :
    originalProductScalar A P f hf (KPGlobalTorusFunctionData.N F ζ hζ x*g) =
      originalProductScalar A P f hf g := by
  simpa [KPGlobalTorusFunctionData.deltaHalf] using
    originalProductScalar_borel A P f hf 1 x g

theorem originalProductScalar_finite_polarized (f : Functions F ζ hζ)
    (hf : KPLiteralRaw.Induced F ζ hζ 0 f) (q : KPFinitePlace F)
    (a : (C.polarization q).L.comap (C.canonical q).heisenberg.π) (g : G F ζ hζ) :
    originalProductScalar A P f hf ((finiteInsertion F ζ hζ q a.val.val).val*g) =
      KPLocalPrincipalSeries.deltaHalf (C.canonical q).borel ((C.canonical q).borel.torus a.val) *
        ((C.polarization q).ωL a : ℂ) * originalProductScalar A P f hf g := by
  obtain ⟨b,x,hb,hs,hx,ha,hd⟩ := polarized_torus_lift F ζ hζ P C q a
  have h := originalProductScalar_borel A P f hf b 0 g
  have hn : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  rw [hn,mul_one,hb,hd,lambdaB_single_finite_heisenberg F ζ hζ P C q b x a hs hx ha] at h
  exact h

theorem originalProductScalar_finite_borel (f : Functions F ζ hζ)
    (hf : KPLiteralRaw.Induced F ζ hζ 0 f) (q : KPFinitePlace F)
    (b : (C.canonical q).borel.B)
    (hb : (C.canonical q).heisenberg.π ((C.canonical q).borel.retract b) ∈ (C.polarization q).L)
    (g : G F ζ hζ) :
    originalProductScalar A P f hf ((finiteInsertion F ζ hζ q b.val).val*g) =
      KPLocalPrincipalSeries.deltaHalf (C.canonical q).borel b *
        ((C.polarization q).ωL ⟨(C.canonical q).borel.retract b,hb⟩ : ℂ) *
        originalProductScalar A P f hf g := by
  obtain ⟨u,hu⟩ := finiteInsertion_canonical_borel F ζ hζ q (C.canonical q) b
  rw [hu,mul_assoc,originalProductScalar_root]
  simpa only [← canonical_borel_half_torus F ζ hζ q (C.canonical q) b] using
    originalProductScalar_finite_polarized A P C f hf q
      ⟨(C.canonical q).borel.retract b,hb⟩ g
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
