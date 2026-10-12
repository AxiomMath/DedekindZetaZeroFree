module

public import DedekindZetaZeroFree.Theta.Periods.ExteriorDigitExtraction

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)
abbrev localRho (p : KPFinitePlace F) :=
  KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
    p (D.finiteData p).inducing (D.finiteData p).inducing.polarization
    (D.finiteData p).haar (D.finiteData p).haar_integer
private lemma norm_rep_left {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (ell : V →ₗ[ℂ] ℂ) (n g : G) (φ : V) (c : ℂ)
    (h : ell (ρ n (ρ g φ)) = c * ell (ρ g φ)) (hc : ‖c‖ = 1) :
    ‖ell (ρ (n * g) φ)‖ = ‖ell (ρ g φ)‖ := by
  rw [map_mul, Module.End.mul_apply, h, norm_mul, hc, one_mul]
lemma local_ell_left_root_norm (p : KPFinitePlace F) (t : p.adicCompletion F)
    (g : KPPGLLocalCover.CubicPGL2 F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (φ : actualLocal R D.finiteData (Sum.inr p)) :
    ‖D.ell (Sum.inr p) (localRho R D p
      (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) t * g) φ)‖ =
    ‖D.ell (Sum.inr p) (localRho R D p g φ)‖ := by
  exact norm_rep_left (localRho R D p) (D.ell (Sum.inr p)) _ g φ _
    (ExteriorWhittakerValues.StoredWhittaker.ell_finite_root R D p t (localRho R D p g φ))
    (Circle.norm_coe _)
end DedekindZetaZeroFree.OrbitFrequencies
end

noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)

private lemma norm_rep_central {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (ell : V →ₗ[ℂ] ℂ) (a b z c : G) (φ : V) (u : ℂ)
    (he : a * b = z * c) (hg : ρ z (ρ c φ) = u • ρ c φ) (hu : ‖u‖ = 1) :
    ‖ell (ρ (a * b) φ)‖ = ‖ell (ρ c φ)‖ := by
  rw [he, map_mul, Module.End.mul_apply, hg, map_smul, norm_smul, hu, one_mul]

lemma local_ell_torus_product_norm (p : KPFinitePlace F)
    (x y : (p.adicCompletion F)ˣ)
    (φ : actualLocal R D.finiteData (Sum.inr p)) :
    ‖D.ell (Sum.inr p) (localRho R D p
      (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) x *
       KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) y) φ)‖ =
    ‖D.ell (Sum.inr p) (localRho R D p
      (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) (x * y)) φ)‖ := by
  have hc : ‖(KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12
      (KPHilbert.B3 F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) x y ^ 2) : ℂ)‖ = 1 := by
    apply Complex.norm_eq_one_of_pow_eq_one (n := 3) _ (by decide)
    let ε := KPHilbert.B3 F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) x y ^ 2
    have he : ε ^ 3 = 1 := Subtype.ext ε.property
    have h := congrArg (KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12) he
    simpa only [ε, map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun z : ℂˣ => (z : ℂ)) h
  exact norm_rep_central (localRho R D p) (D.ell (Sum.inr p)) _ _ _ _ φ _
    (KPPGLLocalCover.A_mul F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) x y)
    (KPRankOneShellRepair.actualCanonicalImage_ordinary_genuine F R.A.zeta12
      R.A.primitive_zeta12 p (D.finiteData p).inducing (D.finiteData p).inducing.polarization
      (D.finiteData p).haar (D.finiteData p).haar_integer _ _) hc

private lemma norm_rep_bruhat {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (ell : V →ₗ[ℂ] ℂ) (a w n n' b l c : G) (φ : V)
    (he : a * w * n = n' * (a * b * l))
    (hr : ‖ell (ρ (n' * (a * b * l)) φ)‖ = ‖ell (ρ (a * b * l) φ)‖)
    (ht : ‖ell (ρ (a * b) (ρ l φ))‖ = ‖ell (ρ c (ρ l φ))‖) :
    ‖ell (ρ (a * w * n) φ)‖ = ‖ell (ρ c (ρ l φ))‖ := by
  rw [he, hr, map_mul, Module.End.mul_apply, ht]

theorem local_ell_bruhat_norm (p : KPFinitePlace F) (x H : (p.adicCompletion F)ˣ)
    (φ : actualLocal R D.finiteData (Sum.inr p)) :
    ‖D.ell (Sum.inr p) (localRho R D p
      (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) x *
       KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) *
       KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) (H : p.adicCompletion F)) φ)‖ =
    ‖D.ell (Sum.inr p) (localRho R D p
      (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) (x * -(H⁻¹ ^ 2)))
      (localRho R D p
        (KPPGLLocalCover.LowerN F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)
          (H⁻¹ : (p.adicCompletion F)ˣ)) φ))‖ := by
  have hcomm := KPCorrectedBruhatLifts.quotient_upper_diagonal F R.A.zeta12
    R.A.primitive_zeta12 (Sum.inr p) ((H⁻¹ : p.adicCompletion F) * (x : p.adicCompletion F)) x
  have hx : (H⁻¹ : p.adicCompletion F) * (x : p.adicCompletion F) /
      (x : p.adicCompletion F) = (H⁻¹ : p.adicCompletion F) := by simp
  rw [hx] at hcomm
  have he :
      KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) x *
      KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) *
      KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) (H : p.adicCompletion F) =
      KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)
        ((H⁻¹ : p.adicCompletion F) * (x : p.adicCompletion F)) *
      (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) x *
       KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) (-(H⁻¹ ^ 2)) *
       KPPGLLocalCover.LowerN F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) (H⁻¹ : (p.adicCompletion F)ˣ)) := by
    rw [mul_assoc, KPCorrectedBruhatLifts.quotient_weyl_upper]
    simp only [← mul_assoc]
    rw [hcomm]
    simp only [mul_assoc, Units.val_inv_eq_inv_val]
  exact norm_rep_bruhat (localRho R D p) (D.ell (Sum.inr p)) _ _ _ _ _ _ _ φ he
    (local_ell_left_root_norm R D p _ _ φ)
    (local_ell_torus_product_norm R D p x (-(H⁻¹ ^ 2)) _)

private lemma norm_rep_map_three {G H V : Type*} [Group G] [Group H]
    [AddCommGroup V] [Module ℂ V] (f : G →* H) (ρ : Representation ℂ H V)
    (ell : V →ₗ[ℂ] ℂ) (a b c d : G) (φ : V)
    (h : ‖ell (ρ (f a * f b * f c) φ)‖ = ‖ell (ρ (f d) φ)‖) :
    ‖ell (ρ (f (a * b * c)) φ)‖ = ‖ell (ρ (f d) φ)‖ := by
  simpa only [map_mul] using h

theorem local_ell_bruhat_norm_of_compact (p : ThetaBranch.ExteriorPrime R.A)
    (x H : (p.val.adicCompletion F)ˣ)
    (hc : KPStandardLocalRootLifts.LowerN F R.A.zeta12 R.A.primitive_zeta12
      (Sum.inr p.val) (H⁻¹ : (p.val.adicCompletion F)ˣ) ∈
      KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)) :
    ‖OrbitExpansion.exteriorSlotValue R D p.val
      (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) x *
       KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
       KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (H : p.val.adicCompletion F))‖ =
    ‖OrbitExpansion.exteriorSlotValue R D p.val
      (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (x * -(H⁻¹ ^ 2)))‖ := by
  have h := local_ell_bruhat_norm R D p.val x H (D.references (Sum.inr p.val))
  have hf := (D.spherical_reference p.val p.property).2 _ hc
  change localRho R D p.val
    (KPPGLLocalCover.LowerN F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
      (H⁻¹ : (p.val.adicCompletion F)ˣ)) (D.references (Sum.inr p.val)) = _ at hf
  rw [hf] at h
  exact norm_rep_map_three
    (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
    (localRho R D p.val) (D.ell (Sum.inr p.val)) _ _ _ _ (D.references (Sum.inr p.val)) h

end DedekindZetaZeroFree.OrbitFrequencies
end

noncomputable section
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)

lemma exterior_upper_mem (p : ThetaBranch.ExteriorPrime R.A) (t : KPTameCompact.O F p.val) :
    KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) t ∈
      KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) := by
  change _ ∈ KPAdelicCoverRestrictedProduct.finiteCompact F R.A.zeta12 R.A.primitive_zeta12 p.val
  rw [KPAdelicCoverRestrictedProduct.finiteCompact, dite_eq_right (ExteriorWhittakerValues.exterior_not_bad p)]
  refine ⟨KPStandardLocalRootLifts.integralN F p.val t, ?_⟩
  exact (KPStandardLocalRootLifts.N_eq_compact F R.A.zeta12 R.A.primitive_zeta12 p.val
    (fun h => ExteriorWhittakerValues.exterior_not_bad p (Or.inr h)) t).symm

lemma exterior_lower_mem (p : ThetaBranch.ExteriorPrime R.A) (t : KPTameCompact.O F p.val) :
    KPStandardLocalRootLifts.LowerN F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) t ∈
      KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) := by
  change _ ∈ KPAdelicCoverRestrictedProduct.finiteCompact F R.A.zeta12 R.A.primitive_zeta12 p.val
  rw [KPAdelicCoverRestrictedProduct.finiteCompact, dite_eq_right (ExteriorWhittakerValues.exterior_not_bad p)]
  refine ⟨KPStandardLocalRootLifts.integralLowerN F p.val t, ?_⟩
  exact (KPStandardLocalRootLifts.LowerN_eq_compact F R.A.zeta12 R.A.primitive_zeta12 p.val
    (fun h => ExteriorWhittakerValues.exterior_not_bad p (Or.inr h)) t).symm

lemma exterior_weyl_mem (p : ThetaBranch.ExteriorPrime R.A) :
    KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) ∈
      KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) := by
  change _ ∈ KPAdelicCoverRestrictedProduct.finiteCompact F R.A.zeta12 R.A.primitive_zeta12 p.val
  rw [KPAdelicCoverRestrictedProduct.finiteCompact, dite_eq_right (ExteriorWhittakerValues.exterior_not_bad p)]
  refine ⟨KPStandardLocalRootLifts.integralW F p.val, ?_⟩
  exact (KPStandardLocalRootLifts.W_eq_compact F R.A.zeta12 R.A.primitive_zeta12 p.val
    (fun h => ExteriorWhittakerValues.exterior_not_bad p (Or.inr h))).symm

private lemma slot_right_fixed {G H V : Type*} [Group G] [Group H]
    [AddCommGroup V] [Module ℂ V] (f : G →* H) (ρ : Representation ℂ H V)
    (ell : V →ₗ[ℂ] ℂ) (a k : G) (v : V) (hk : ρ (f k) v = v) :
    ell (ρ (f (a * k)) v) = ell (ρ (f a) v) := by
  rw [map_mul, map_mul, Module.End.mul_apply, hk]

theorem exterior_integral_digit_value (p : ThetaBranch.ExteriorPrime R.A)
    (x : (p.val.adicCompletion F)ˣ) (t : KPTameCompact.O F p.val) :
    OrbitExpansion.exteriorSlotValue R D p.val
      (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) x *
       KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
       KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) t) =
    OrbitExpansion.exteriorSlotValue R D p.val
      (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) x) := by
  have hc := (KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)).mul_mem
    (exterior_weyl_mem R p) (exterior_upper_mem R p t)
  have hf := (D.spherical_reference p.val p.property).2 _ hc
  have h := slot_right_fixed
    (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
    (localRho R D p.val) (D.ell (Sum.inr p.val))
    (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) x)
    (KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
     KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) t)
    (D.references (Sum.inr p.val)) hf
  simpa only [mul_assoc] using h

theorem exterior_nonintegral_digit_norm (p : ThetaBranch.ExteriorPrime R.A)
    (x H : (p.val.adicCompletion F)ˣ)
    (hH : (H⁻¹ : p.val.adicCompletion F) ∈ KPTameCompact.O F p.val) :
    ‖OrbitExpansion.exteriorSlotValue R D p.val
      (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) x *
       KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
       KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (H : p.val.adicCompletion F))‖ =
    ‖OrbitExpansion.exteriorSlotValue R D p.val
      (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (x * -(H⁻¹ ^ 2)))‖ :=
  local_ell_bruhat_norm_of_compact R D p x H (by
    simpa only [Units.val_inv_eq_inv_val] using exterior_lower_mem R p ⟨_, hH⟩)
end DedekindZetaZeroFree.OrbitFrequencies
end
