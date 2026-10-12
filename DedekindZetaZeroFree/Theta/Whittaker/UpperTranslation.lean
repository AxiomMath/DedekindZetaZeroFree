module

public import DedekindZetaZeroFree.Theta.Periods.UpperCurveDifferentiation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped NumberField Classical Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem integrand_out_add (f : Functions R)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (x : KPAdeles F) (q : KPAdditiveQuotient F) (g : Group R) :
    f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q + x) * g) =
      f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (Quotient.out (q + QuotientAddGroup.mk x : KPAdditiveQuotient F)) * g) := by
  have he : (QuotientAddGroup.mk (Quotient.out q + x) : KPAdditiveQuotient F) =
      q + QuotientAddGroup.mk x := by
    change QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F) (Quotient.out q + x) = _
    rw [map_add]; congr 1; exact Quotient.out_eq q
  simpa only [he] using (integrand_mk R f hr (Quotient.out q + x) g).symm

theorem fourier_upper_translation (dq : Measure (KPAdditiveQuotient F))
    (hHaar : dq.IsAddHaarMeasure) (hprob : dq Set.univ = 1) (f : Functions R)
    (hf : Continuous f)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (x : KPAdeles F) (g : Group R) :
    MomentSources.fourier R dq f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) =
      (adelicTraceCharacter F x : ℂ) * MomentSources.fourier R dq f g := by
  letI := hHaar
  have hi := fourier_integrable R dq hprob f hf hr g
  have hit := fourier_integrable R dq hprob f hf hr
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g)
  let a : KPAdditiveQuotient F := QuotientAddGroup.mk x
  have hχ : (adelicTraceQuotientCharacter F a : ℂ) = (adelicTraceCharacter F x : ℂ) := rfl
  have he (q : KPAdditiveQuotient F) : star (adelicTraceQuotientCharacter F q : ℂ) =
      (adelicTraceCharacter F x : ℂ) * star (adelicTraceQuotientCharacter F (q + a) : ℂ) := by
    rw [AddChar.map_add_eq_mul, Circle.coe_mul, star_mul, hχ]
    have hn : (adelicTraceCharacter F x : ℂ) * star (adelicTraceCharacter F x : ℂ) = 1 := by
      have h := Complex.mul_conj' (adelicTraceCharacter F x : ℂ)
      rw [Circle.norm_coe, Complex.ofReal_one, one_pow] at h
      exact h
    calc
      _ = 1 * star (adelicTraceQuotientCharacter F q : ℂ) := (one_mul _).symm
      _ = _ := by rw [← hn]; ring
  unfold MomentSources.fourier
  have harg (q : KPAdditiveQuotient F) :
      f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) *
        (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g)) =
      f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out (q+a)) * g) := by
    rw [← mul_assoc, ← KPGlobalTorusFunctionData.N_add]
    exact integrand_out_add R f hr x q g
  calc
    _ = ∫ q, (adelicTraceCharacter F x : ℂ) •
      (f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out (q+a)) * g) *
        star (adelicTraceQuotientCharacter F (q+a) : ℂ)) ∂dq := by
      apply integral_congr_ae
      filter_upwards [] with q
      rw [harg q, he q]
      simp only [smul_eq_mul]; ring
    _ = _ := by
      rw [integral_smul, smul_eq_mul]
      congr 1
      exact integral_add_right_eq_self (fun q : KPAdditiveQuotient F =>
        f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
          star (adelicTraceQuotientCharacter F q : ℂ)) a

theorem diagonal_upper (y : KPAdelicCoverRestrictedProduct.Ideles F) (x : KPAdeles F) :
    KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12 y *
      KPRationalAdelicSplitting.pglN F R.A.zeta12 R.A.primitive_zeta12 x =
    KPRationalAdelicSplitting.pglN F R.A.zeta12 R.A.primitive_zeta12 ((y : KPAdeles F) * x) *
      KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12 y := by
  have h := KPRationalAdelicSplitting.quotient_upper_diagonal F R.A.zeta12 R.A.primitive_zeta12
    ((y : KPAdeles F) * x) y
  have he : (y : KPAdeles F) * x * (↑y⁻¹ : KPAdeles F) = x := by
    rw [mul_comm (y : KPAdeles F) x, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  rw [he] at h
  exact h.symm

end DedekindZetaZeroFree.RootDerivatives

end
