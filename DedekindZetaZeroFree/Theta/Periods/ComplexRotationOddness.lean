module

public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.IdeleInsertion
open NumberField MeasureTheory
open scoped Classical
open MomentSources ThetaProfileHaarSheets ThetaSheetExactUnfolding
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_localIdele → eval_localIdele
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def infiniteInsertion (A : SArithmeticData F) (w : InfinitePlace F)
    (z : w.Completionˣ) : A.G :=
  (Function.update (fun u : InfinitePlace F => (1 : u.Completionˣ)) w z, 1)

lemma localIdele_mul (y z : R.A.G) :
    MomentSources.localIdele R (y * z) = MomentSources.localIdele R y * MomentSources.localIdele R z := by
  simp only [MomentSources.localIdele, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply,
    KPRationalAdelicSplitting.localIdele, map_mul, Finset.prod_mul_distrib]
  ac_rfl

lemma localIdele_insertion (w : InfinitePlace F) (z : w.Completionˣ) :
    MomentSources.localIdele R (infiniteInsertion R.A w z) =
      KPRationalAdelicSplitting.localIdele F (Sum.inl w) z := by
  unfold MomentSources.localIdele
  have hf : (∏ p : R.A.Sf, KPRationalAdelicSplitting.localIdele F (Sum.inr p.val)
      ((infiniteInsertion R.A w z).2 p)) = 1 := by
    simp [infiniteInsertion, KPRationalAdelicSplitting.localIdele]
  rw [hf, mul_one, Finset.prod_eq_single w]
  · simp [infiniteInsertion]
  · intro b _ hb
    simp [infiniteInsertion, hb, KPRationalAdelicSplitting.localIdele]
  · simp

lemma pglA_complex_mul (w : InfinitePlace F) (z : w.Completionˣ)
    (y : KPAdelicCoverRestrictedProduct.Ideles F) :
    KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
      (KPRationalAdelicSplitting.localIdele F (Sum.inl w) z * y) =
    KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
      (KPRationalAdelicSplitting.localIdele F (Sum.inl w) z) *
        KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12 y := by
  unfold KPRationalAdelicSplitting.pglA KPRationalAdelicSplitting.A
  rw [← map_mul, ← map_mul]
  congr 2
  apply RestrictedProduct.ext
  intro v
  change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 v
    (Units.map (KPAdelicCoverRestrictedProduct.adeleEval F v) (_ * y)) =
      KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 v _ *
        KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 v _
  rw [map_mul]
  have he := eval_localIdele F (Sum.inl w) v z
  have he' : Units.map (KPAdelicCoverRestrictedProduct.adeleEval F v)
      (KPRationalAdelicSplitting.localIdele F (Sum.inl w) z) =
      Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) (Sum.inl w) z v := he
  rw [he']
  by_cases hv : v = Sum.inl w
  · subst v
    rw [KPStandardLocalRootLifts.A_mul]
    simp [KPHilbert.B3, KPHilbert.B6_infinite]
  · simp [Pi.mulSingle_eq_of_ne hv]

lemma diagonal_insertion (w : InfinitePlace F) (z : w.Completionˣ) (y : R.A.G) :
    diagonal R (infiniteInsertion R.A w z * y) =
      KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.localIdele F (Sum.inl w) z) * diagonal R y := by
  unfold diagonal
  rw [localIdele_mul, localIdele_insertion, pglA_complex_mul]

lemma upper_signedArgument_rotation {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (C : ResidualConstantTerm R Q T) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (w : InfinitePlace F)
    (z : w.Completionˣ) (hz : ‖(z : w.Completion)‖ = 1) (y : R.A.G)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    upper R Q.dq (T.theta v)
      (signedArgument R m b (infiniteInsertion R.A w z * y) d) =
    upper R Q.dq (T.theta v) (signedArgument R m b y d) := by
  cases b
  · simp only [signedArgument, Bool.false_eq_true, if_false, diagonal_insertion]
    rw [← mul_assoc, KPRationalAdelicSplitting.quotient_weyl_diagonal]
    simp only [mul_assoc]
    have he : (KPRationalAdelicSplitting.localIdele F (Sum.inl w) z)⁻¹ =
        KPRationalAdelicSplitting.localIdele F (Sum.inl w) z⁻¹ := by
      simp [KPRationalAdelicSplitting.localIdele]
    rw [he, C.radial]
    simp [Units.val_inv_eq_inv_val, norm_inv, hz]
  · simp only [signedArgument, if_true, one_mul, diagonal_insertion, mul_assoc]
    rw [C.radial]
    simp [hz]

lemma upperDigits_rotation {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (C : ResidualConstantTerm R Q T) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (w : InfinitePlace F)
    (z : w.Completionˣ) (hz : ‖(z : w.Completion)‖ = 1) (y : R.A.G) :
    upperDigits R Q T v m b (infiniteInsertion R.A w z * y) =
      upperDigits R Q T v m b y := by
  unfold upperDigits
  apply Finset.sum_congr rfl
  intro d _
  rw [upper_signedArgument_rotation R C v m b w z hz]

lemma branch_neg_one {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (w : InfinitePlace F) :
    P.branch v (infiniteInsertion R.A w (-1)) = -1 := by
  rw [P.branch_exact v _ (fun p => by
    simpa [infiniteInsertion] using (P.cutoff p).one_mem)]
  rw [Finset.prod_eq_single w]
  · rcases P.first_root v w with h | h <;>
      simp [infiniteInsertion, h, DHCubic.angular,
        InfinitePlace.Completion.extensionEmbedding]
  · intro b _ hb
    simp [infiniteInsertion, hb, DHCubic.angular]
  · simp

lemma insertion_class_eq_one (w : InfinitePlace F) (z : w.Completionˣ) :
    QuotientGroup.mk' R.A.sixthPowers (infiniteInsertion R.A w z) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  obtain ⟨r, hr⟩ := R.A.infinite_unit_isPower w 6 (Or.inr (Or.inr rfl)) z
  refine ⟨infiniteInsertion R.A w r, ?_⟩
  apply Prod.ext
  · funext u
    by_cases hu : u = w
    · subst u
      simpa [infiniteInsertion] using hr
    · simp [infiniteInsertion, hu]
  · funext p
    simp [infiniteInsertion]

lemma weightedUpper_neg_one {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (P : Packet R Q) (C : ResidualConstantTerm R Q T) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (w : InfinitePlace F) (y : R.A.G) :
    weightedUpper R Q T P v m b (infiniteInsertion R.A w (-1) * y) =
      -weightedUpper R Q T P v m b y := by
  unfold weightedUpper
  rw [map_mul, insertion_class_eq_one,
    one_mul (QuotientGroup.mk' R.A.sixthPowers y), map_mul, branch_neg_one, upperDigits_rotation R C v m b w (-1) (by simp)]
  simp only [neg_one_mul, inv_neg]
  ring
end DedekindZetaZeroFree.IdeleInsertion

end
