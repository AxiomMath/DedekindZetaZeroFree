module

public import DedekindZetaZeroFree.Theta.Digits.WeylPeriodExtraction
public import DedekindZetaZeroFree.Theta.Digits.CompactRightCorrections

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory
open ThetaExpansion.SignedExpansion
open scoped Classical NumberField
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_rationalUnit → eval_rationalUnit
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_localIdele → eval_localIdele
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

private theorem value_right_fixed {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (ell : V →ₗ[ℂ] ℂ) (r : V) (a b k : G)
    (h : a = b * k) (hk : ρ k r = r) : ell (ρ a r) = ell (ρ b r) := by
  rw [h, map_mul, Module.End.mul_apply, hk]

 theorem exteriorDigitFactor_eq_slot {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : ThetaBranch.ExteriorPrime R.A) :
    exteriorDigitFactor R C m x d p = exteriorSlotValue R C.factorization p.val
      (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) *
       KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
       KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
         (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p.val) (digitParameter R m d))) := by
  unfold exteriorDigitFactor exteriorSlotValue
  congr 3
  congr 1
  change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) _ * _ * _ = _
  have h := eval_localIdele F (Sum.inr p.val) (Sum.inr p.val)
    (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)
  simp only [Pi.mulSingle_eq_same] at h
  change Units.map (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p.val)).toMonoidHom
    (KPRationalAdelicSplitting.localIdele F (Sum.inr p.val)
      (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)) = _ at h
  exact congrArg (fun z => KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) z *
    KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
    KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
      (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p.val) (digitParameter R m d))) h

 theorem exteriorDigitFactor_reindex {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (m : ThetaReflectionData.Row R.A) (x : Fˣ) (u : R.A.U)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : ThetaBranch.ExteriorPrime R.A) :
    exteriorDigitFactor R C m (u.val ^ 6 * x) (DigitMasks.digitReindex R m u d) p =
      exteriorDigitFactor R C m x d p := by
  rw [exteriorDigitFactor_eq_slot, exteriorDigitFactor_eq_slot]
  let v : KPHilbert.Place F := Sum.inr p.val
  let a := Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x
  let b := Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom u.val
  let n := KPAdelicCoverRestrictedProduct.adeleEval F v (digitParameter R m d)
  let n' := KPAdelicCoverRestrictedProduct.adeleEval F v (digitParameter R m (DigitMasks.digitReindex R m u d))
  let k := DigitMasks.digitRightTuple R m u (1 : R.A.G) d v
  let P := KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 v
  let A := fun z => KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 v z
  let W := KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 v
  let N := fun z => KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 v z
  have hk : P k = (N n')⁻¹ * A (b ^ 6) * N n := by
    change P (DigitMasks.digitRightTuple R m u 1 d (Sum.inr p.val)) = _
    unfold DigitMasks.digitRightTuple
    rw [RestrictedProduct.mul_apply, RestrictedProduct.mul_apply, RestrictedProduct.inv_apply,
      RestrictedProduct.mul_apply, RestrictedProduct.mul_apply]
    unfold DigitMasks.diagonalTuple
    rw [sDiagonal_exterior R _ p.val p.property, sDiagonal_exterior R _ p.val p.property]
    simp only [one_mul, map_mul, map_inv]
    congr 2
    change P (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 v _) = _
    have he := eval_rationalUnit F v (u.val ^ 6)
    change Units.map (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p.val)).toMonoidHom
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom (u.val ^ 6)) = _ at he
    have he' := congrArg (fun z => P (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 v z)) he
    exact he'.trans (congrArg A (map_pow _ u.val 6))
  have hA (z : (p.val.adicCompletion F)ˣ) : A (b ^ 6 * z) = A (b ^ 6) * A z := by
    change KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 v _ = _
    unfold KPPGLLocalCover.A
    rw [DigitMasks.local_A_pow_six_mul, map_mul]
    rfl
  have hcomm : A (b ^ 6) * A a = A a * A (b ^ 6) := by
    rw [← hA]
    change A _ = A a * A (b ^ 6)
    rw [mul_comm (b ^ 6) a, KPPGLLocalCover.A_mul]
    have hh := ((KPHilbert.B3_laws F R.A.zeta12 R.A.primitive_zeta12 v).2.2.2.2.1 a (b ^ 2)).2
    rw [← pow_mul] at hh
    norm_num only at hh
    rw [hh, one_pow, map_one, one_mul]
  have hW : A (b ^ 6) * W = W * A ((b ^ 6)⁻¹) := by
    have h := KPCorrectedBruhatLifts.quotient_weyl_diagonal F R.A.zeta12 R.A.primitive_zeta12 v (b ^ 6)⁻¹
    simpa only [inv_inv] using h.symm
  have hInv : A ((b ^ 6)⁻¹) = (A (b ^ 6))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← hA, mul_inv_cancel]
    exact congrArg P (KPStandardLocalRootLifts.A_one F R.A.zeta12 R.A.primitive_zeta12 v)
  have he : A (b ^ 6 * a) * W * N n' = (A a * W * N n) * P k⁻¹ := by
    rw [hA, hcomm, mul_assoc (A a) (A (b ^ 6)) W, hW, hInv, map_inv, hk]
    generalize A a = aa, W = ww, A (b ^ 6) = bb, N n = nn, N n' = mm
    group
  let ρ := KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
    p.val (C.factorization.finiteData p.val).inducing (C.factorization.finiteData p.val).inducing.polarization
    (C.factorization.finiteData p.val).haar (C.factorization.finiteData p.val).haar_integer
  have hfix : ρ (P k⁻¹) (C.factorization.references v) = C.factorization.references v :=
    (C.factorization.spherical_reference p.val p.property).2 _
      (DigitMasks.exteriorFactor_le_compact R v ((DigitMasks.exteriorFactor R v).inv_mem
        (DigitMasks.digitRightTuple_exterior R m u 1 d p.val p.property)))
  have hv := value_right_fixed ρ (C.factorization.ell v) (C.factorization.references v)
    (A (b ^ 6 * a) * W * N n') (A a * W * N n) (P k⁻¹) he hfix
  have hl : P (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 v
      (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom (u.val ^ 6 * x)) *
      KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 v *
      KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 v n') = A (b ^ 6 * a) * W * N n' := by
    rw [map_mul, map_mul, map_mul, map_pow]
    rfl
  have hr : P (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 v a *
      KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 v *
      KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 v n) = A a * W * N n := by
    rw [map_mul, map_mul]
    rfl
  exact (congrArg (fun g => C.factorization.ell v (ρ g (C.factorization.references v))) hl).trans
    (hv.trans (congrArg (fun g => C.factorization.ell v (ρ g (C.factorization.references v))) hr).symm)

 theorem exteriorDigitCoefficient_sixth {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (m : ThetaReflectionData.Row R.A) (x : Fˣ) (u : R.A.U) :
    exteriorDigitCoefficient R C m (u.val ^ 6 * x) = exteriorDigitCoefficient R C m x := by
  unfold exteriorDigitCoefficient
  rw [← (DigitMasks.digitReindex R m u).sum_comp]
  simp_rw [DigitMasks.digitWeight_reindex, exteriorDigitFactor_reindex]

 theorem exteriorDigitCoefficient_gamma {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (m : ThetaReflectionData.Row R.A) (x : Fˣ) (γ : ThetaReflectionData.rationalGamma R.A) :
    exteriorDigitCoefficient R C m (γ.val * x) = exteriorDigitCoefficient R C m x := by
  obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp γ.property
  rw [← he]
  exact exteriorDigitCoefficient_sixth R C m x ⟨u, hu⟩

end DedekindZetaZeroFree.OrbitExpansion

end
