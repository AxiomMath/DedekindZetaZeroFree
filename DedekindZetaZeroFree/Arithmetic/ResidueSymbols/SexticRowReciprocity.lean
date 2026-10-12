module

public import DedekindZetaZeroFree.Theta.Unfolding.ForwardFiberSupport
public import DedekindZetaZeroFree.Arithmetic.Units.DyadicRowUnitClasses

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open ThetaExpansion.SignedExpansion
open scoped NumberField Classical
open _root_.DedekindZetaZeroFree.ThetaBranch renaming ord_mul → ThetaBranch.ord_mul
open _root_.DedekindZetaZeroFree.ThetaBranch renaming ord_zpow → ThetaBranch.ord_zpow
open _root_.DedekindZetaZeroFree.ThetaBranch renaming char_order → ThetaBranch.char_order
open _root_.DedekindZetaZeroFree.ThetaBranch renaming char_pow_six → ThetaBranch.char_pow_six
open _root_.DedekindZetaZeroFree.ThetaBranch.CanonicalCoordinateProof renaming ratio_mem_sunit → ThetaBranch.CanonicalCoordinateProof.ratio_mem_sunit
open _root_.DedekindZetaZeroFree.ThetaBranch.CanonicalCoordinateProof renaming idealEquiv → ThetaBranch.CanonicalCoordinateProof.idealEquiv
open _root_.DedekindZetaZeroFree.ThetaBranch.CanonicalCoordinateProof renaming squarefree_of_exponents_le_one → ThetaBranch.CanonicalCoordinateProof.squarefree_of_exponents_le_one
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def forwardIdeal (c : ExteriorSquarefreeIdeal R.A.cS) (n : R.A.Exterior) : R.A.Exterior :=
  ⟨c.val.val * n.val ^ 3, mul_ne_zero c.val.property.1 (pow_ne_zero 3 n.property.1), by
    rw [Ideal.mul_sup_eq_of_coprime_left c.val.property.2]
    exact Ideal.pow_sup_eq_top n.property.2⟩

def forwardGenerator (c : ExteriorSquarefreeIdeal R.A.cS) (n : R.A.Exterior) : Fˣ :=
  R.probe.allowed.generator c.val * R.probe.allowed.generator n ^ 3

lemma forwardGenerator_val (c : ExteriorSquarefreeIdeal R.A.cS) (n : R.A.Exterior) :
    (forwardGenerator R c n : F) =
      (ThetaReflectionData.forwardModulus R.A R.probe.coefficients c n : F) := by
  simp only [forwardGenerator, ThetaReflectionData.forwardModulus, Units.val_mul,
    Units.val_pow_eq_pow_val, R.probe.sameGenerator]
  rfl

lemma forwardGenerator_allowed (c : ExteriorSquarefreeIdeal R.A.cS) (n : R.A.Exterior) :
    ThetaReflectionData.rationalClass R.A (forwardGenerator R c n) ∈ R.probe.correction.B := by
  rw [forwardGenerator, map_mul, map_pow, ← R.probe.sameComplement]
  exact R.probe.allowed.B.mul_mem (R.probe.allowed.allowed c.val)
    (R.probe.allowed.B.pow_mem (R.probe.allowed.allowed n) 3)

lemma forwardGenerator_integral (c : ExteriorSquarefreeIdeal R.A.cS) (n : R.A.Exterior) :
    (forwardGenerator R c n : F) ∈ R.A.R := by
  rw [forwardGenerator_val]
  exact (ThetaReflectionData.forwardModulus R.A R.probe.coefficients c n).property

lemma allowed_frequency_eq (a b : Fˣ)
    (ha : ThetaReflectionData.rationalClass R.A a ∈ R.probe.allowed.B)
    (hb : ThetaReflectionData.rationalClass R.A b ∈ R.probe.allowed.B)
    (ho : ∀ p : ThetaBranch.ExteriorPrime R.A, ThetaBranch.order p.val a = ThetaBranch.order p.val b) :
    (QuotientGroup.mk a : ThetaReflectionData.Frequency R.A) = QuotientGroup.mk b := by
  let e : R.A.U := ⟨a / b, ThetaBranch.CanonicalCoordinateProof.ratio_mem_sunit R.A a b ho⟩
  have he : ThetaReflectionData.rationalClass R.A e.val ∈ R.probe.allowed.B := by
    change ThetaReflectionData.rationalClass R.A (a / b) ∈ _
    rw [map_div]
    exact R.probe.allowed.B.div_mem ha hb
  have hg := allowed_unit_mem_gamma R e he
  exact QuotientGroup.eq_iff_div_mem.mpr hg

lemma forwardGenerator_order (c : ExteriorSquarefreeIdeal R.A.cS) (n : R.A.Exterior)
    (p : ThetaBranch.ExteriorPrime R.A) :
    ThetaBranch.order p.val (forwardGenerator R c n) =
      (idealPrimeExponent p.val.asIdeal c.val.val : ℤ) +
        3 * (idealPrimeExponent p.val.asIdeal n.val : ℤ) := by
  rw [forwardGenerator, ThetaBranch.ord_mul, ← zpow_natCast, ThetaBranch.ord_zpow, ThetaBranch.generator_order,
    ThetaBranch.generator_order]
  norm_num

lemma row_primes_eq_support (m : ThetaReflectionData.Row R.A)
    (D : ThetaBranch.RowFactorization R.A R.probe.allowed m) :
    ThetaDigitAverage.rowPrimes R.A m.val m.property = ThetaBranch.support D.rowIdeal.val := by
  ext p
  have hs : p ∈ ThetaBranch.support D.rowIdeal.val ↔ idealPrimeExponent p.asIdeal D.rowIdeal.val ≠ 0 := by
    simp only [ThetaBranch.support, Finset.mem_preimage, idealPrimeSupport,
      idealPrimeExponent, Multiset.mem_toFinset, Multiset.count_ne_zero]
  rw [hs]
  by_cases hp : p ∈ R.A.Sf
  · have hz : idealPrimeExponent p.asIdeal D.rowIdeal.val = 0 := by
      by_contra hn
      exact ThetaBranch.support_outside R.A D.rowIdeal p (hs.mpr hn) hp
    simp [ThetaDigitAverage.rowPrimes, ThetaDigitAverage.RowPrimes, hp, hz]
  · have hv : p.valuation F (m.val : F) = WithZero.exp (-(idealPrimeExponent p.asIdeal D.rowIdeal.val : ℤ)) :=
      SIntegerLocalization.generator_valuation R.A.Sf D.rowIdeal.val D.rowIdeal.property.1
        m.val D.row_generates.1 D.row_generates.2 p hp
    simp only [ThetaDigitAverage.rowPrimes, Set.Finite.mem_toFinset,
      ThetaDigitAverage.RowPrimes, Set.mem_setOf_eq, hp, not_false_eq_true, true_and, hv]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega

lemma forwardMask_eq_rowIdeal_character (m : ThetaReflectionData.Row R.A)
    (D : ThetaBranch.RowFactorization R.A R.probe.allowed m) (a : Fˣ) (r : R.A.R)
    (hr : (a : F) = (r : F))
    (ha : ∀ p ∈ ThetaDigitAverage.rowPrimes R.A m.val m.property, ThetaBranch.order p a = 0) :
    forwardMask R m a = NormalizedProbe.exteriorSexticRowCharacter R.A R.σ D.rowIdeal r := by
  have hr0 : r ≠ 0 := by
    intro h
    exact a.ne_zero (hr.trans (congrArg (fun t : R.A.R => (t : F)) h))
  have hs := row_primes_eq_support R m D
  unfold forwardMask NormalizedProbe.exteriorSexticRowCharacter
  rw [dif_neg hr0]
  apply Finset.prod_bij (fun p _ =>
    (⟨p.val, hs ▸ p.property⟩ : {p // p ∈ ThetaBranch.support D.rowIdeal.val}))
  · intro p hp
    exact Finset.mem_attach _ _
  · intro p hp q hq he
    exact Subtype.ext (congrArg (fun q : {p // p ∈ ThetaBranch.support D.rowIdeal.val} => q.val) he)
  · intro q hq
    exact ⟨⟨q.val, hs.symm ▸ q.property⟩, Finset.mem_univ _, rfl⟩
  intro p hp
  have hn := ThetaBranch.unitResidue_ne_zero p.val a (ha p.val p.property)
  rw [sexticUnitPower, if_pos (isUnit_iff_ne_zero.mpr hn)]
  have hv : p.val.valuation F (m.val : F) = WithZero.exp (-(idealPrimeExponent p.val.asIdeal D.rowIdeal.val : ℤ)) :=
    SIntegerLocalization.generator_valuation R.A.Sf _ D.rowIdeal.property.1 m.val
      D.row_generates.1 D.row_generates.2 p.val
      ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
  have hj : (ThetaDigitAverage.rowExponent R.A m.val p.val).val =
      idealPrimeExponent p.val.asIdeal D.rowIdeal.val % 6 := by
    simp only [ThetaDigitAverage.rowExponent, hv, WithZero.log_exp, neg_neg,
      Int.toNat_natCast]
  rw [hj]
  have hp' : p.val ∉ R.A.Sf :=
    ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
  have hpow := pow_eq_pow_mod (idealPrimeExponent p.val.asIdeal D.rowIdeal.val)
    (ThetaBranch.char_pow_six _ (ThetaBranch.char_order R.A R.σ ⟨p.val, hp'⟩) _ hn)
  refine hpow.symm.trans ?_
  have he : a = ThetaReflectionData.rowUnit R.A ⟨r, hr0⟩ := Units.ext hr
  rw [he]
  rfl

lemma exteriorCharacter_eq_sextic (I : R.A.Exterior) (r : R.A.R) :
    NormalizedProbe.exteriorSexticRowCharacter R.A R.σ I r = R.σ (R.A.sexticResidue I r) := by
  rw [NormalizedProbe.exteriorSexticRowCharacter_eq_sexticResiduePowerChar]
  simp only [SArithmeticData.sexticResiduePowerChar,
    show SArithmeticData.sexticExponent (1 : ℤ) = 1 from rfl, pow_one]
  let q := Ideal.Quotient.mk (R.A.extendIdeal I) r
  change MulChar.ofUnitHom _ q = R.σ (MulChar.ofUnitHom (R.A.sexticResidueFamily I) q)
  by_cases hq : IsUnit q
  · rw [← hq.unit_spec, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
    rfl
  · rw [MulChar.map_nonunit _ hq, MulChar.map_nonunit _ hq, map_zero]

lemma forwardMask_eq_sextic (m : ThetaReflectionData.Row R.A)
    (D : ThetaBranch.RowFactorization R.A R.probe.allowed m) (a : Fˣ) (r : R.A.R)
    (hr : (a : F) = (r : F)) :
    forwardMask R m a = R.σ (R.A.sexticResidue D.rowIdeal r) := by
  by_cases ha : ∀ p ∈ ThetaDigitAverage.rowPrimes R.A m.val m.property, ThetaBranch.order p a = 0
  · rw [forwardMask_eq_rowIdeal_character R m D a r hr ha, exteriorCharacter_eq_sextic]
  · push Not at ha
    obtain ⟨p, hp, ha⟩ := ha
    have hm : forwardMask R m a = 0 := by
      unfold forwardMask
      apply Finset.prod_eq_zero (Finset.mem_univ (⟨p, hp⟩ : ThetaDigitAverage.rowPrimes R.A m.val m.property))
      simp only [ThetaBranch.unitResidue, dif_neg ha, sexticUnitPower,
        isUnit_iff_ne_zero, ne_eq, not_true_eq_false, ↓reduceIte]
    have hr0 : r ≠ 0 := by
      intro h
      exact a.ne_zero (hr.trans (congrArg (fun t : R.A.R => (t : F)) h))
    have hp' : p ∈ ThetaBranch.support D.rowIdeal.val := row_primes_eq_support R m D ▸ hp
    have he : 0 < idealPrimeExponent p.asIdeal D.rowIdeal.val := by
      apply Multiset.count_pos.mpr
      simpa only [ThetaBranch.support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using hp'
    have hc : NormalizedProbe.exteriorSexticRowCharacter R.A R.σ D.rowIdeal r = 0 := by
      unfold NormalizedProbe.exteriorSexticRowCharacter
      rw [dif_neg hr0]
      apply Finset.prod_eq_zero (Finset.mem_attach _ (⟨p, hp'⟩ : {p // p ∈ ThetaBranch.support D.rowIdeal.val}))
      have har : a = ThetaReflectionData.rowUnit R.A ⟨r, hr0⟩ := Units.ext hr
      change ThetaBranch.symbol R.A R.σ ⟨p, _⟩ (ThetaReflectionData.rowUnit R.A ⟨r, hr0⟩) ^ _ = 0
      rw [← har]
      simp only [ThetaBranch.symbol, ThetaBranch.unitResidue, dif_neg ha, MulChar.map_zero,
        zero_pow he.ne']
    rw [hm, ← exteriorCharacter_eq_sextic, hc]

lemma forwardMask_mul_L (m : ThetaReflectionData.Row R.A)
    (D : ThetaBranch.RowFactorization R.A R.probe.allowed m)
    (I : R.A.Exterior) (r : R.A.R) (a : Fˣ) (hr : R.A.Generates I r)
    (har : (a : F) = (r : F))
    (ha : ThetaReflectionData.rationalClass R.A a ∈ R.probe.correction.B) :
    forwardMask R m a * Characters.L R (QuotientGroup.mk D.epsilon) a =
      (R.A.correctionLS R.probe.correction.Λ R.probe.correction.G R.probe.correction.η_id
        (R.A.diagonal a) : ℂ) * R.σ (R.A.sexticResidue I m.val) := by
  have hrec := ArithmeticContext.actual_hilbert_sextic_reciprocity R.A
    R.probe.correction.H R.probe.correction.B R.probe.correction.H_actual
    R.probe.correction.B_complement
  let r₀ := R.probe.coefficients.generator D.rowIdeal
  let a₀ := R.probe.allowed.generator D.rowIdeal
  have hba₀ : R.A.IsAllowed R.probe.correction.B a₀ := by
    change ThetaReflectionData.rationalClass R.A a₀ ∈ _
    rw [← R.probe.sameComplement]
    exact R.probe.allowed.allowed D.rowIdeal
  have hm : m.val = (R.A.unitEquiv D.epsilon : R.A.R) * r₀ := by
    apply Subtype.ext
    have he := congrArg (fun u : Fˣ => (u : F)) D.row_eq
    change (m.val : F) = (D.epsilon.val : F) * (a₀ : F) at he
    change (m.val : F) = (D.epsilon.val : F) * (r₀ : F)
    rwa [R.probe.sameGenerator] at he
  have ht := hrec.2.2.1 I D.rowIdeal r r₀ a a₀ D.epsilon hr
    (R.probe.coefficients.generates D.rowIdeal) har (R.probe.sameGenerator D.rowIdeal) ha hba₀
  rw [← hm] at ht
  have hu := hrec.2.1 I r a D.epsilon hr har ha
  have hu' : R.A.sexticResidue I (R.A.unitEquiv D.epsilon : R.A.R) =
      ((R.A.H_S (R.A.diagonal D.epsilon.val) (R.A.diagonal a) : Fˣ) : F) := by
    rw [hu]
    exact congrArg (fun z : Fˣ => (z : F)) (R.probe.correction.H_actual _ _)
  rw [forwardMask_eq_sextic R m D a r har, Characters.compatible R |>.2 D.epsilon a,
    ht, map_mul, hu']
  ring

end DedekindZetaZeroFree.OrbitExpansion

end
