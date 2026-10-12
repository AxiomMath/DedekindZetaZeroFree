module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.FrozenTensor

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open MomentSources NumberField
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)

lemma diagonal_one : diagonal R 1 = 1 := by
  have ha : KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 1 = 1 := by
    apply RestrictedProduct.ext
    intro p
    simp [KPRationalAdelicSplitting.ATuple, KPRationalAdelicSplitting.ACoordinates]
  simp [diagonal, MomentSources.localIdele, KPRationalAdelicSplitting.localIdele,
    KPRationalAdelicSplitting.pglA, KPRationalAdelicSplitting.A, ha]

theorem forward_period_value (v : R.A.UnitQuotient) :
    MomentSources.fourier R C.sources.dq (C.realization.theta v) 1 =
      (KThird (4 * Real.pi) : ℂ) ^ Fintype.card (InfinitePlace F) := by
  have hf := C.forward v 1
  rw [diagonal_one] at hf
  rw [hf]
  unfold Packet.forwardProfile
  have hcut : ∀ p : R.A.Sf, (1 : R.A.G).2 p ∈ C.packet.cutoff p :=
    fun p => (C.packet.cutoff p).one_mem
  rw [if_pos hcut]
  simp [Packet.scale, DHCubic.angular]

theorem forward_scalar_pos :
    0 < KThird (4 * Real.pi) ^ Fintype.card (InfinitePlace F) := by
  exact pow_pos (KThird_pos _ (by positivity)) _

theorem forward_period_norm (v : R.A.UnitQuotient) :
    ‖MomentSources.fourier R C.sources.dq (C.realization.theta v) 1‖ =
      KThird (4 * Real.pi) ^ Fintype.card (InfinitePlace F) := by
  rw [forward_period_value, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (KThird_pos _ (by positivity))]

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
