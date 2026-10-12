module

public import DedekindZetaZeroFree.Theta.Unfolding.OrbitExtractionDefinitions

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources ThetaExpansion.SignedExpansion
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def orbitFrequency (i : OrbitIndex R) : Fˣ := Quotient.out i.1 * i.2.val

theorem orbitFrequency_class (i : OrbitIndex R) :
    (QuotientGroup.mk (orbitFrequency R i) : ThetaReflectionData.Frequency R.A) = i.1 := by
  change QuotientGroup.mk' (ThetaReflectionData.rationalGamma R.A) _ = _
  rw [orbitFrequency, map_mul]
  have h : QuotientGroup.mk' (ThetaReflectionData.rationalGamma R.A) i.2.val = 1 :=
    (QuotientGroup.eq_one_iff _).mpr i.2.property
  rw [h]
  exact (mul_one ((QuotientGroup.mk' (ThetaReflectionData.rationalGamma R.A))
    (Quotient.out i.1))).trans (Quotient.out_eq i.1)

theorem orbitFrequency_injective : Function.Injective (orbitFrequency R) := by
  intro i j h
  have hc : i.1 = j.1 := by
    rw [← orbitFrequency_class R i, ← orbitFrequency_class R j, h]
  apply Prod.ext hc
  apply Subtype.ext
  apply mul_left_cancel (a := (Quotient.out i.1 : Fˣ))
  simpa only [orbitFrequency, hc] using h

theorem orbitFrequency_surjective : Function.Surjective (orbitFrequency R) := by
  intro a
  let ξ : ThetaReflectionData.Frequency R.A := QuotientGroup.mk a
  let r : Fˣ := Quotient.out ξ
  have hr : (QuotientGroup.mk r : ThetaReflectionData.Frequency R.A) = QuotientGroup.mk a :=
    Quotient.out_eq ξ
  have hm : a / r ∈ ThetaReflectionData.rationalGamma R.A :=
    QuotientGroup.eq_iff_div_mem.mp hr.symm
  refine ⟨(ξ, ⟨a / r, hm⟩), ?_⟩
  change r * (a / r) = a
  simp [div_eq_mul_inv, mul_comm]

def orbitFrequencyEquiv : OrbitIndex R ≃ Fˣ :=
  Equiv.ofBijective (orbitFrequency R)
    ⟨orbitFrequency_injective R, orbitFrequency_surjective R⟩

theorem hasSum_orbitFrequency_iff (f : Fˣ → ℂ) (s : ℂ) :
    HasSum (fun i : OrbitIndex R => f (orbitFrequency R i)) s ↔ HasSum f s :=
  (orbitFrequencyEquiv R).hasSum_iff

end DedekindZetaZeroFree.OrbitExpansion

end
