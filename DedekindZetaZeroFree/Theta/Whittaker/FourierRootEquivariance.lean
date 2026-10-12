module

public import DedekindZetaZeroFree.Theta.Whittaker.NormalizedFiniteWeylPeriods

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem core_rational_root {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)
    (x : RestrictedTensorSimple.Core (actualLocal R C.factorization.finiteData)
      C.factorization.references C.factorization.bad) (t : F) (g : Group R) :
    C.factorization.coreMap x
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (algebraMap F (KPAdeles F) t) * g) = C.factorization.coreMap x g := by
  rw [← KPLiteralExceptionalResidue.rationalLift_unipotent]
  exact (C.factorization.core_same_residue x).2.2.1 _ _

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

theorem selected_ell_root {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)
    (v : R.A.UnitQuotient) (s : RestrictedTensorSimple.Level C.factorization.bad)
    (x : ∀ p : s.val, actualLocal R C.factorization.finiteData p)
    (hx : C.factorization.selected v = RestrictedTensorSimple.stageInclusion _
      C.factorization.references C.factorization.bad s (PiTensorProduct.tprod ℂ x))
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (t : q.adicCompletion F) (b : actualLocal R C.factorization.finiteData (Sum.inr q)) :
    C.factorization.ell (Sum.inr q)
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
        R.A.primitive_zeta12 q (C.factorization.finiteData q).inducing
        (C.factorization.finiteData q).inducing.polarization
        (C.factorization.finiteData q).haar (C.factorization.finiteData q).haar_integer
        (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t) b) =
      (adelicTraceQuotientCharacter F (QuotientAddGroup.mk
        (KPRationalAdelicSplitting.localAdele F (Sum.inr q) t)) : ℂ) *
        C.factorization.ell (Sum.inr q) b := by
  let i : s.val := ⟨Sum.inr q, hq⟩
  let y := Function.update x i b
  let core := RestrictedTensorSimple.stageInclusion _ C.factorization.references
    C.factorization.bad s (PiTensorProduct.tprod ℂ y)
  letI := C.sources.quotientHaar
  have hf := fourier_left_root R C.sources.dq (C.factorization.coreMap core)
    (core_rational_root R C core)
    (KPRationalAdelicSplitting.localAdele F (Sum.inr q) t) 1
    (by simpa only [mul_one] using C.factorization.product_integrable s y)
  rw [mul_one, ← finite_root_injection R] at hf
  rw [finite_translate_period R C s y q hq,
    C.factorization.product_exact] at hf
  have hu := dependent_prod_update (fun p : s.val => C.factorization.ell p) y i
    (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
      R.A.primitive_zeta12 q (C.factorization.finiteData q).inducing
      (C.factorization.finiteData q).inducing.polarization
      (C.factorization.finiteData q).haar (C.factorization.finiteData q).haar_integer
      (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t) (y i))
  dsimp only [i, KPPGLLocalCover.N] at hu
  rw [hu] at hf
  have hyprod : (∏ p : s.val, C.factorization.ell p (y p)) =
      C.factorization.ell (Sum.inr q) b * ∏ p ∈ Finset.univ.erase i, C.factorization.ell p (y p) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [y, Function.update_self]
    rfl
  rw [hyprod] at hf
  have hrest : (∏ p ∈ Finset.univ.erase i, C.factorization.ell p (y p)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    dsimp [y]
    rw [Function.update_of_ne (Finset.mem_erase.mp hp).1]
    exact selected_tensor_nonzero R C v s x hx p
  change _ * (∏ p ∈ Finset.univ.erase i, C.factorization.ell p (y p)) =
    _ * (_ * (∏ p ∈ Finset.univ.erase i, C.factorization.ell p (y p))) at hf
  rw [← mul_assoc] at hf
  have hh := mul_right_cancel₀ hrest hf
  simpa only [y, i, Function.update_self, KPPGLLocalCover.N] using hh

end DedekindZetaZeroFree.SheetRescaling

end
