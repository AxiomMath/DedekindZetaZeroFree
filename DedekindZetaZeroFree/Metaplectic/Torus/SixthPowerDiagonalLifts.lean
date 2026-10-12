module

public import DedekindZetaZeroFree.Theta.Digits.SixthPowerReindexing
public import DedekindZetaZeroFree.Theta.Periods.RationalDiagonalInvariance
public import DedekindZetaZeroFree.Theta.Periods.ComplexRotationOddness

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.DigitMasks
open MomentSources NumberField
open scoped Classical BigOperators
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_localIdele → eval_localIdele
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem local_A_pow_six_mul (w : KPHilbert.Place F)
    (x y : (KPHilbert.Completion F w)ˣ) :
    KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 w (x ^ 6 * y) =
      KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 w (x ^ 6) *
        KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 w y := by
  rw [KPStandardLocalRootLifts.A_mul]
  have hb : KPHilbert.B3 F R.A.zeta12 R.A.primitive_zeta12 w (x ^ 6) y = 1 := by
    rw [show x ^ 6 = (x ^ 2) ^ 3 by rw [← pow_mul]]
    exact ((KPHilbert.B3_laws F R.A.zeta12 R.A.primitive_zeta12 w).2.2.2.2.1 _ _).1
  rw [hb, one_pow, map_one, one_mul]

private theorem eval_localIdele_raw (v w : KPHilbert.Place F)
    (y : (KPHilbert.Completion F v)ˣ) :
    Units.map (KPAdelicCoverRestrictedProduct.adeleEval F w)
      (KPRationalAdelicSplitting.localIdele F v y) =
      Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) v y w := by
  apply Units.ext
  exact congrArg Units.val (eval_localIdele F v w y)

private theorem eval_selected_localIdele (y : R.A.G) (v : KPHilbert.Place F) :
    Units.map (KPAdelicCoverRestrictedProduct.adeleEval F v)
      (MomentSources.localIdele R y) =
    (∏ w : InfinitePlace F,
      Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) (Sum.inl w) (y.1 w) v) *
    ∏ p : R.A.Sf,
      Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) (Sum.inr p.val) (y.2 p) v := by
  rw [MomentSources.localIdele, map_mul, map_prod, map_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro w _
    exact eval_localIdele_raw _ _ _
  · apply Finset.prod_congr rfl
    intro p _
    exact eval_localIdele_raw _ _ _

theorem localIdele_arch (y : R.A.G) (w : InfinitePlace F) :
    Units.map (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w)) (MomentSources.localIdele R y) = y.1 w := by
  rw [eval_selected_localIdele]
  have hf : (∏ p : R.A.Sf,
      Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) (Sum.inr p.val) (y.2 p) (Sum.inl w)) = 1 := by simp
  rw [hf, mul_one, Finset.prod_eq_single w]
  · exact Pi.mulSingle_eq_same _ _
  · intro b _ hb
    exact Pi.mulSingle_eq_of_ne (Sum.inl_injective.ne hb.symm) _
  · simp

theorem localIdele_finite (y : R.A.G) (p : KPFinitePlace F) (hp : p ∈ R.A.Sf) :
    Units.map (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p)) (MomentSources.localIdele R y) =
      y.2 ⟨p, hp⟩ := by
  rw [eval_selected_localIdele]
  have hf : (∏ w : InfinitePlace F,
      Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) (Sum.inl w) (y.1 w) (Sum.inr p)) = 1 := by simp
  rw [hf, one_mul, Finset.prod_eq_single (⟨p, hp⟩ : R.A.Sf)]
  · simp
  · intro b _ hb
    simp [Pi.mulSingle_eq_of_ne (show Sum.inr p ≠ Sum.inr b.val from fun h =>
      hb (Subtype.ext (Sum.inr_injective h.symm)))]
  · simp

theorem localIdele_exterior (y : R.A.G) (p : KPFinitePlace F) (hp : p ∉ R.A.Sf) :
    Units.map (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p)).toMonoidHom (MomentSources.localIdele R y) = 1 := by
  have he := eval_selected_localIdele R y (Sum.inr p)
  apply he.trans
  have hf : (∏ w : InfinitePlace F,
      Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) (Sum.inl w) (y.1 w) (Sum.inr p)) = 1 := by simp
  rw [hf, one_mul]
  apply Finset.prod_eq_one
  intro b _
  apply Pi.mulSingle_eq_of_ne
  intro h
  apply hp
  have he : p = b.val := Sum.inr_injective h
  exact he.symm ▸ b.property

end DedekindZetaZeroFree.DigitMasks

end
