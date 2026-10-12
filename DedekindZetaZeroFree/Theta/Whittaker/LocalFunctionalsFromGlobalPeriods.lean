module

public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData
public import DedekindZetaZeroFree.Eisenstein.Induction.RationalBorelCovariance
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.CodifferentTraceDuality

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.StoredWhittaker
open MomentSources NumberField MeasureTheory
open scoped Classical Topology NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)

theorem finite_translate_period
    (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    fourier R Q.dq
      (D.coreMap (RestrictedTensorSimple.stageInclusion _
        D.references D.bad s (PiTensorProduct.tprod ℂ x)))
      (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12
          (Sum.inr q) a)) =
    ∏ p : s.val, D.ell p
      (Function.update x ⟨Sum.inr q, hq⟩
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
          R.A.primitive_zeta12 q (D.finiteData q).inducing
          (D.finiteData q).inducing.polarization
          (D.finiteData q).haar (D.finiteData q).haar_integer
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
          (x ⟨Sum.inr q, hq⟩)) p) := by
  rw [← D.product_exact s]
  unfold MomentSources.fourier
  apply integral_congr_ae
  filter_upwards [] with t
  rw [D.finite_intertwining q a s hq x]
  simp only [mul_one]

theorem dependent_prod_update {I : Type*} [Fintype I] [DecidableEq I] {V : I → Type*}
    (f : ∀ i, V i → ℂ) (x : ∀ i, V i) (i : I) (b : V i) :
    (∏ j, f j (Function.update x i b j)) =
      f i b * ∏ j ∈ Finset.univ.erase i, f j (x j) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => f j (Function.update x i b j)) (Finset.mem_univ i)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact congrArg (f j) (Function.update_of_ne (Finset.mem_erase.mp hj).1 b x)

theorem core_rational_root
    (x : RestrictedTensorSimple.Core (actualLocal R D.finiteData)
      D.references D.bad) (t : F) (g : Group R) :
    D.coreMap x
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (algebraMap F (KPAdeles F) t) * g) = D.coreMap x g := by
  rw [← KPLiteralExceptionalResidue.rationalLift_unipotent]
  exact (D.core_same_residue x).2.2.1 _ _

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

theorem ell_root_at_level (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hx : ∀ p : s.val, D.ell p (x p) ≠ 0)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (t : q.adicCompletion F) (b : actualLocal R D.finiteData (Sum.inr q)) :
    D.ell (Sum.inr q)
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
        R.A.primitive_zeta12 q (D.finiteData q).inducing
        (D.finiteData q).inducing.polarization
        (D.finiteData q).haar (D.finiteData q).haar_integer
        (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t) b) =
      (adelicTraceQuotientCharacter F (QuotientAddGroup.mk
        (KPRationalAdelicSplitting.localAdele F (Sum.inr q) t)) : ℂ) *
        D.ell (Sum.inr q) b := by
  let i : s.val := ⟨Sum.inr q, hq⟩
  let y := Function.update x i b
  let core := RestrictedTensorSimple.stageInclusion _ D.references
    D.bad s (PiTensorProduct.tprod ℂ y)
  let := Q.quotientHaar
  have hf := fourier_left_root R Q.dq (D.coreMap core)
    (core_rational_root R D core)
    (KPRationalAdelicSplitting.localAdele F (Sum.inr q) t) 1
    (by simpa only [mul_one] using D.product_integrable s y)
  rw [mul_one, ← finite_root_injection R] at hf
  rw [finite_translate_period R D s y q hq,
    D.product_exact] at hf
  have hu := dependent_prod_update (fun p : s.val => D.ell p) y i
    (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
      R.A.primitive_zeta12 q (D.finiteData q).inducing
      (D.finiteData q).inducing.polarization
      (D.finiteData q).haar (D.finiteData q).haar_integer
      (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t) (y i))
  dsimp only [i, KPPGLLocalCover.N] at hu
  rw [hu] at hf
  have hyprod : (∏ p : s.val, D.ell p (y p)) =
      D.ell (Sum.inr q) b * ∏ p ∈ Finset.univ.erase i, D.ell p (y p) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [y, Function.update_self]
    rfl
  rw [hyprod] at hf
  have hrest : (∏ p ∈ Finset.univ.erase i, D.ell p (y p)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    dsimp [y]
    rw [Function.update_of_ne (Finset.mem_erase.mp hp).1]
    exact hx p
  change _ * (∏ p ∈ Finset.univ.erase i, D.ell p (y p)) =
    _ * (_ * (∏ p ∈ Finset.univ.erase i, D.ell p (y p))) at hf
  rw [← mul_assoc] at hf
  have hh := mul_right_cancel₀ hrest hf
  simpa only [y, i, Function.update_self, KPPGLLocalCover.N] using hh

theorem exists_nonzero_value (p : KPHilbert.Place F) :
    ∃ b : actualLocal R D.finiteData p, D.ell p b ≠ 0 := by
  classical
  by_cases hp : p ∈ D.bad
  · obtain ⟨s, x, hs, hx⟩ := D.detected_tensor
    rw [D.product_exact] at hx
    have hps : p ∈ s.val := hs.symm ▸ hp
    exact ⟨x ⟨p, hps⟩, (Finset.prod_ne_zero_iff.mp hx) ⟨p, hps⟩ (Finset.mem_univ _)⟩
  · exact ⟨D.references p, by rw [D.reference_value p hp]; exact one_ne_zero⟩

theorem ell_finite_root (q : KPFinitePlace F) (t : q.adicCompletion F)
    (b : actualLocal R D.finiteData (Sum.inr q)) :
    D.ell (Sum.inr q)
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
        R.A.primitive_zeta12 q (D.finiteData q).inducing
        (D.finiteData q).inducing.polarization
        (D.finiteData q).haar (D.finiteData q).haar_integer
        (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t) b) =
      (ResidueTrace.localTraceCharacter q t : ℂ) * D.ell (Sum.inr q) b := by
  classical
  let s : RestrictedTensorSimple.Level D.bad :=
    ⟨insert (Sum.inr q) D.bad, Finset.subset_insert _ _⟩
  choose x hx using fun p : s.val => exists_nonzero_value R D p
  have hq : Sum.inr q ∈ s.val := Finset.mem_insert_self _ _
  have h := ell_root_at_level R D s x hx q hq t b
  have htrace : adelicTraceQuotientCharacter F (QuotientAddGroup.mk
      (KPRationalAdelicSplitting.localAdele F (Sum.inr q) t)) =
      ResidueTrace.localTraceCharacter q t := by
    rw [CodifferentResidueSieve.localTraceCharacter_eq_localFiniteCharacter]
    exact (adelicTraceQuotientCharacter_mk F _).trans
      (adelicTraceCharacter_finite_single F q t)
  rwa [htrace] at h

end DedekindZetaZeroFree.ExteriorWhittakerValues.StoredWhittaker

end
