module

public import DedekindZetaZeroFree.Theta.Periods.PureTensorDetection

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
variable {Q : AdmissibleFlatSources R}

theorem fourier_left_root (μ : Measure (KPAdditiveQuotient F)) [μ.IsAddHaarMeasure]
    (θ : Functions R)
    (hθ : ∀ (t : F) (g : Group R), θ
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (algebraMap F (KPAdeles F) t) * g) = θ g)
    (a : KPAdeles F) (g : Group R)
    (_hi : Integrable (fun q => θ
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (Quotient.out q) * g) * star (adelicTraceQuotientCharacter F q : ℂ)) μ) :
    fourier R μ θ (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 a * g) =
      (adelicTraceQuotientCharacter F (QuotientAddGroup.mk a) : ℂ) * fourier R μ θ g := by
  let f : KPAdditiveQuotient F → ℂ := fun q => θ
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)
  have hrep (b : KPAdeles F) : f (QuotientAddGroup.mk b) = θ
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 b * g) := by
    have hout : (QuotientAddGroup.mk (Quotient.out
        (QuotientAddGroup.mk b : KPAdditiveQuotient F)) : KPAdditiveQuotient F) =
        QuotientAddGroup.mk b := Quotient.out_eq _
    obtain ⟨t, ht⟩ := QuotientAddGroup.eq_iff_sub_mem.mp hout
    have hb : Quotient.out (QuotientAddGroup.mk b : KPAdditiveQuotient F) =
        algebraMap F (KPAdeles F) t + b := by rw [ht]; abel
    dsimp [f]
    rw [hb, KPGlobalTorusFunctionData.N_add, mul_assoc, hθ]
  let b : KPAdditiveQuotient F := QuotientAddGroup.mk a
  have hshift (q : KPAdditiveQuotient F) : θ
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) *
        (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 a * g)) = f (q + b) := by
    have hq : q + b = (QuotientAddGroup.mk (Quotient.out q + a) : KPAdditiveQuotient F) := by
      rw [QuotientAddGroup.mk_add]
      exact congrArg (fun z : KPAdditiveQuotient F => z + b) (Quotient.out_eq q).symm
    rw [hq, hrep, KPGlobalTorusFunctionData.N_add, mul_assoc]
  let χ := adelicTraceQuotientCharacter F
  have hχ (q : KPAdditiveQuotient F) : star (χ q : ℂ) =
      (χ b : ℂ) * star (χ (q + b) : ℂ) := by
    rw [AddChar.map_add_eq_mul, Circle.coe_mul, star_mul]
    have hcancel : (χ b : ℂ) * star (χ b : ℂ) = 1 := by
      change (χ b : ℂ) * (starRingEnd ℂ) (χ b : ℂ) = 1
      rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
    calc
      star (χ q : ℂ) = 1 * star (χ q : ℂ) := (one_mul _).symm
      _ = _ := by rw [← hcancel]; ring
  change (∫ q : KPAdditiveQuotient F, θ
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) *
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 a * g)) *
      star (χ q : ℂ) ∂μ) = (χ b : ℂ) * ∫ q, f q * star (χ q : ℂ) ∂μ
  calc
    _ = ∫ q : KPAdditiveQuotient F, (χ b : ℂ) *
        (f (q + b) * star (χ (q + b) : ℂ)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with q
      rw [hshift q, hχ q]
      ring
    _ = _ := by
      rw [integral_const_mul]
      exact congrArg (fun z : ℂ => (χ b : ℂ) * z)
        (integral_add_right_eq_self (μ := μ)
          (fun q : KPAdditiveQuotient F => f q * star (χ q : ℂ)) b)

theorem finite_root_injection (q : KPFinitePlace F) (t : q.adicCompletion F) :
    KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12
        (Sum.inr q) (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t)) =
      KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.localAdele F (Sum.inr q) t) := by
  exact (congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12
    R.A.primitive_zeta12) (KPRationalAdelicSplitting.N_local F R.A.zeta12
      R.A.primitive_zeta12 (Sum.inr q) t)).symm

end DedekindZetaZeroFree.FourierContinuation

end
