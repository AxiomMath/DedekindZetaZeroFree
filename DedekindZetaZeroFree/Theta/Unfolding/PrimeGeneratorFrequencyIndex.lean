module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.SexticRowReciprocity

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open ThetaExpansion.SignedExpansion
open scoped NumberField Classical
open _root_.DedekindZetaZeroFree.ThetaBranch.CanonicalCoordinateProof renaming idealEquiv → ThetaBranch.CanonicalCoordinateProof.idealEquiv

open _root_.DedekindZetaZeroFree.ThetaBranch.CanonicalCoordinateProof renaming order_eq_of_frequency_eq → ThetaBranch.CanonicalCoordinateProof.order_eq_of_frequency_eq
open _root_.DedekindZetaZeroFree.ThetaBranch.CanonicalCoordinateProof renaming exterior_ideal_of_exponents → ThetaBranch.CanonicalCoordinateProof.exterior_ideal_of_exponents
open _root_.DedekindZetaZeroFree.ThetaBranch.CanonicalCoordinateProof renaming squarefree_of_exponents_le_one → ThetaBranch.CanonicalCoordinateProof.squarefree_of_exponents_le_one
open _root_.DedekindZetaZeroFree.ExteriorWhittakerValues.NumericalSpherical renaming ord_prod → ord_prod
open _root_.DedekindZetaZeroFree.ExteriorWhittakerValues.NumericalSpherical renaming ord_pow → ord_pow
open _root_.DedekindZetaZeroFree.ExteriorWhittakerValues.NumericalSpherical renaming prime_ord → prime_ord
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

abbrev ForwardIndex := ExteriorSquarefreeIdeal R.A.cS × R.A.Exterior

def forwardFrequency (j : ForwardIndex R) : ThetaReflectionData.Frequency R.A :=
  QuotientGroup.mk (forwardGenerator R j.1 j.2)

lemma forwardFrequency_injective : Function.Injective (forwardFrequency R) := by
  intro j k he
  have ho (p : ThetaBranch.ExteriorPrime R.A) :=
    ThetaBranch.CanonicalCoordinateProof.order_eq_of_frequency_eq R.A _ _ he p
  simp only [forwardGenerator_order] at ho
  have hj := ExteriorWhittakerValues.NumericalSpherical.squarefree_exps R.A j.1
  have hk := ExteriorWhittakerValues.NumericalSpherical.squarefree_exps R.A k.1
  have hex (p : ThetaBranch.ExteriorPrime R.A) :
      idealPrimeExponent p.val.asIdeal j.1.val.val = idealPrimeExponent p.val.asIdeal k.1.val.val ∧
      idealPrimeExponent p.val.asIdeal j.2.val = idealPrimeExponent p.val.asIdeal k.2.val := by
    have := ho p
    have := hj p
    have := hk p
    omega
  apply Prod.ext
  · apply Subtype.ext
    apply (ThetaBranch.CanonicalCoordinateProof.idealEquiv R.A).injective
    ext p
    exact (hex p).1
  · apply (ThetaBranch.CanonicalCoordinateProof.idealEquiv R.A).injective
    ext p
    exact (hex p).2

lemma forwardFrequency_exists (a : Fˣ)
    (ha : ThetaReflectionData.rationalClass R.A a ∈ R.probe.correction.B)
    (ho : ∀ p : ThetaBranch.ExteriorPrime R.A,
      0 ≤ ThetaBranch.order p.val a ∧ (ThetaBranch.order p.val a % 3 = 0 ∨ ThetaBranch.order p.val a % 3 = 1)) :
    ∃ j : ForwardIndex R, forwardFrequency R j = QuotientGroup.mk a := by
  let e := fun p : ThetaBranch.ExteriorPrime R.A => (ThetaBranch.order p.val a).toNat % 3
  let f := fun p : ThetaBranch.ExteriorPrime R.A => (ThetaBranch.order p.val a).toNat / 3
  have he : {p | e p ≠ 0}.Finite := (exterior_order_support_finite R a).subset (by
    intro p hp hn; exact hp (by simp [e, hn]))
  have hf : {p | f p ≠ 0}.Finite := (exterior_order_support_finite R a).subset (by
    intro p hp hn; exact hp (by simp [f, hn]))
  obtain ⟨c, hc⟩ := ThetaBranch.CanonicalCoordinateProof.exterior_ideal_of_exponents R.A e he
  obtain ⟨n, hn⟩ := ThetaBranch.CanonicalCoordinateProof.exterior_ideal_of_exponents R.A f hf
  have hsf : Squarefree c.val := by
    apply ThetaBranch.CanonicalCoordinateProof.squarefree_of_exponents_le_one R.A c
    intro p
    rw [hc]
    dsimp [e]
    have h := ho p
    have ht := Int.toNat_of_nonneg h.1
    omega
  let j : ForwardIndex R := (⟨c, hsf⟩, n)
  refine ⟨j, ?_⟩
  apply allowed_frequency_eq R
  · rw [R.probe.sameComplement]; exact forwardGenerator_allowed R _ _
  · rwa [R.probe.sameComplement]
  intro p
  rw [forwardGenerator_order, hc, hn]
  dsimp [e, f]
  have ht := Int.toNat_of_nonneg (ho p).1
  omega

lemma forwardExterior_supported {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (a : Fˣ) (ha : forwardExterior R C a ≠ 0) (p : ThetaBranch.ExteriorPrime R.A) :
    0 ≤ ThetaBranch.order p.val a ∧
      (ThetaBranch.order p.val a % 3 = 0 ∨ ThetaBranch.order p.val a % 3 = 1) := by
  have hp : C.factorization.exteriorValue R p a ≠ 0 := by
    intro hz
    exact ha (finprod_eq_zero _ p hz (forwardExterior_finite R C a))
  rw [C.exterior.rational_exact] at hp
  unfold ThetaBranch.sphericalFactor sexticSphericalCoefficient at hp
  split_ifs at hp <;> simp_all <;> omega

lemma forwardGenerator_primeProduct (c : ExteriorSquarefreeIdeal R.A.cS) (n : R.A.Exterior)
    (P : Finset (ThetaBranch.ExteriorPrime R.A))
    (hc : ∀ p ∉ P, idealPrimeExponent p.val.asIdeal c.val.val = 0)
    (hn : ∀ p ∉ P, idealPrimeExponent p.val.asIdeal n.val = 0) :
    (QuotientGroup.mk (forwardGenerator R c n) : ThetaReflectionData.Frequency R.A) =
      QuotientGroup.mk (∏ p ∈ P, R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) ^
        (idealPrimeExponent p.val.asIdeal c.val.val + 3 * idealPrimeExponent p.val.asIdeal n.val)) := by
  apply allowed_frequency_eq R
  · rw [R.probe.sameComplement]; exact forwardGenerator_allowed R c n
  · rw [map_prod]
    have hm (T : Finset (ThetaBranch.ExteriorPrime R.A)) :
        (∏ p ∈ T, ThetaReflectionData.rationalClass R.A
          (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) ^
            (idealPrimeExponent p.val.asIdeal c.val.val + 3 * idealPrimeExponent p.val.asIdeal n.val))) ∈
          R.probe.allowed.B := by
      induction T using Finset.induction_on with
      | empty => simpa using R.probe.allowed.B.one_mem
      | @insert p T hp ih =>
        rw [Finset.prod_insert hp]
        apply R.probe.allowed.B.mul_mem
        · rw [map_pow]; exact R.probe.allowed.B.pow_mem (R.probe.allowed.allowed _) _
        · exact ih
    exact hm P
  intro p
  rw [forwardGenerator_order, ord_prod]
  simp_rw [ord_pow, prime_ord]
  by_cases hp : p ∈ P
  · simp [hp]
  · simp [hp, hc p hp, hn p hp]

lemma forwardExterior_eq_of_frequency_eq {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (a b : Fˣ) (he : (QuotientGroup.mk a : ThetaReflectionData.Frequency R.A) = QuotientGroup.mk b) :
    forwardExterior R C a = forwardExterior R C b := by
  let γ : ThetaReflectionData.rationalGamma R.A := ⟨a / b, QuotientGroup.eq_iff_div_mem.mp he⟩
  have h : a = b * γ.val := by dsimp [γ]; simp
  rw [h, forwardExterior_gamma]

lemma forwardMask_eq_of_frequency_eq (m : ThetaReflectionData.Row R.A)
    (a b : Fˣ) (he : (QuotientGroup.mk a : ThetaReflectionData.Frequency R.A) = QuotientGroup.mk b) :
    forwardMask R m a = forwardMask R m b := by
  let γ : ThetaReflectionData.rationalGamma R.A := ⟨a / b, QuotientGroup.eq_iff_div_mem.mp he⟩
  have h : a = b * γ.val := by dsimp [γ]; simp
  rw [h, forwardMask_gamma]

lemma L_eq_of_frequency_eq {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (a b : Fˣ)
    (he : (QuotientGroup.mk a : ThetaReflectionData.Frequency R.A) = QuotientGroup.mk b) :
    Characters.L R v a = Characters.L R v b := by
  let γ : ThetaReflectionData.rationalGamma R.A := ⟨a / b, QuotientGroup.eq_iff_div_mem.mp he⟩
  have h : a = b * γ.val := by dsimp [γ]; simp
  rw [← packet_branch_rational R C.packet, h, map_mul, map_mul,
    packet_branch_gamma, mul_one, packet_branch_rational]

open _root_.DedekindZetaZeroFree.ThetaBranch.CanonicalCoefficientProof renaming extSupport → ThetaBranch.CanonicalCoefficientProof.extSupport
open _root_.DedekindZetaZeroFree.ThetaBranch.CanonicalCoefficientProof renaming mem_extSupport → ThetaBranch.CanonicalCoefficientProof.mem_extSupport
open _root_.DedekindZetaZeroFree.ThetaBranch.CanonicalCoefficientProof renaming ext_prod_val → ThetaBranch.CanonicalCoefficientProof.ext_prod_val
open _root_.DedekindZetaZeroFree.ThetaBranch.CanonicalCoefficientProof renaming ideal_factorization → ThetaBranch.CanonicalCoefficientProof.ideal_factorization
open _root_.DedekindZetaZeroFree.ThetaBranch.CanonicalCoefficientProof renaming support_prod → ThetaBranch.CanonicalCoefficientProof.support_prod
open _root_.DedekindZetaZeroFree.ThetaBranch.CanonicalCoefficientProof renaming exp_zero → ThetaBranch.CanonicalCoefficientProof.exp_zero
 alias ThetaBranch.extSupport := ThetaBranch.CanonicalCoefficientProof.extSupport

private alias ThetaBranch.exp_zero := ThetaBranch.CanonicalCoefficientProof.exp_zero

lemma exterior_factorization (I : R.A.Exterior) (P : Finset (ThetaBranch.ExteriorPrime R.A))
    (hP : ThetaBranch.extSupport R.A I ⊆ P) :
    I.val = ∏ p ∈ P, p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal I.val := by
  have h : (∏ p ∈ ThetaBranch.extSupport R.A I,
      p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal I.val) = I.val := by
    unfold ThetaBranch.extSupport
    exact (ThetaBranch.CanonicalCoefficientProof.ext_prod_val R.A I
      (fun p => p.asIdeal ^ idealPrimeExponent p.asIdeal I.val)).trans
      ((ThetaBranch.CanonicalCoefficientProof.support_prod I.val I.property.1
        (fun p => p ^ idealPrimeExponent p I.val)).trans
        (ThetaBranch.CanonicalCoefficientProof.ideal_factorization I.val I.property.1).symm)
  refine h.symm.trans (Finset.prod_subset hP ?_)
  intro p hp hn
  have hs : p.val ∉ ThetaBranch.support I.val := by
    simpa only [ThetaBranch.extSupport, ThetaBranch.CanonicalCoefficientProof.mem_extSupport] using hn
  rw [ThetaBranch.exp_zero _ _ hs, pow_zero]

lemma forwardExterior_generator {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (c : ExteriorSquarefreeIdeal R.A.cS) (n : R.A.Exterior) :
    forwardExterior R C (forwardGenerator R c n) = R.probe.coefficients.gammaTwo c /
      ((Real.sqrt (R.A.exteriorNorm c.val) : ℂ) * (R.A.exteriorNorm n : ℂ)) := by
  let P := ThetaBranch.extSupport R.A c.val ∪ ThetaBranch.extSupport R.A n
  have hc (p : ThetaBranch.ExteriorPrime R.A) (hp : p ∉ P) :
      idealPrimeExponent p.val.asIdeal c.val.val = 0 := by
    apply ThetaBranch.exp_zero
    exact fun h => hp (Finset.mem_union_left _
      (by simpa only [ThetaBranch.extSupport, ThetaBranch.CanonicalCoefficientProof.mem_extSupport] using h))
  have hn (p : ThetaBranch.ExteriorPrime R.A) (hp : p ∉ P) :
      idealPrimeExponent p.val.asIdeal n.val = 0 := by
    apply ThetaBranch.exp_zero
    exact fun h => hp (Finset.mem_union_right _
      (by simpa only [ThetaBranch.extSupport, ThetaBranch.CanonicalCoefficientProof.mem_extSupport] using h))
  let b := ∏ p ∈ P, R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) ^
        (idealPrimeExponent p.val.asIdeal c.val.val + 3 * idealPrimeExponent p.val.asIdeal n.val)
  have he : (QuotientGroup.mk (forwardGenerator R c n) : ThetaReflectionData.Frequency R.A) = QuotientGroup.mk b :=
    forwardGenerator_primeProduct R c n P hc hn
  rw [forwardExterior_eq_of_frequency_eq R C _ b he]
  rw [forwardExterior_eq_prod R C b P (by
    intro p hp
    apply (order_eq_zero_iff _ _).mp
    rw [← ThetaBranch.CanonicalCoordinateProof.order_eq_of_frequency_eq R.A _ _ he p,
      forwardGenerator_order, hc p hp, hn p hp]
    simp)]
  exact C.exterior.crt_product c n P
    (exterior_factorization R c.val P Finset.subset_union_left)
    (exterior_factorization R n P Finset.subset_union_right)

lemma forwardModulus_generates (c : ExteriorSquarefreeIdeal R.A.cS) (n : R.A.Exterior) :
    R.A.Generates (forwardIdeal R c n) (ThetaReflectionData.forwardModulus R.A R.probe.coefficients c n) := by
  constructor
  · exact mul_ne_zero (R.probe.coefficients.generates c.val).1
      (pow_ne_zero 3 (R.probe.coefficients.generates n).1)
  · change Ideal.span {R.probe.coefficients.generator c.val * R.probe.coefficients.generator n ^ 3} = _
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow,
      (R.probe.coefficients.generates c.val).2, (R.probe.coefficients.generates n).2]
    exact (by unfold forwardIdeal SArithmeticData.extendIdeal; rw [Ideal.map_mul, Ideal.map_pow])

lemma forwardGenerator_norm (c : ExteriorSquarefreeIdeal R.A.cS) (n : R.A.Exterior) :
    (q R.A (forwardGenerator R c n)).val = R.A.exteriorNorm c.val * R.A.exteriorNorm n ^ 3 := by
  change R.A.norm (R.A.diagonal (forwardGenerator R c n)) = _
  rw [R.A.generator_norm (forwardIdeal R c n) _ (forwardModulus_generates R c n) _
    (forwardGenerator_val R c n)]
  simp only [SArithmeticData.exteriorNorm, forwardIdeal, idealNorm, map_mul, map_pow,
    Nat.cast_mul, Nat.cast_pow]

lemma forwardGenerator_rowCharacter (c : ExteriorSquarefreeIdeal R.A.cS) (n : R.A.Exterior)
    (m : R.A.R) : ThetaReflectionData.forwardRowCharacter R.A R.probe.coefficients c n m =
      R.σ (R.A.sexticResidue (forwardIdeal R c n) m) := by
  rw [show ThetaReflectionData.forwardRowCharacter R.A R.probe.coefficients c n m =
    NormalizedProbe.exteriorSexticRowCharacter R.A R.σ (forwardIdeal R c n) m from
      R.probe.exteriorCharacters _ _ _ (forwardModulus_generates R c n), exteriorCharacter_eq_sextic]

lemma forwardGenerator_theta (c : ExteriorSquarefreeIdeal R.A.cS) (n : R.A.Exterior) :
    R.probe.coefficients.theta (ThetaReflectionData.forwardModulus R.A R.probe.coefficients c n) =
      (R.A.correctionLS R.probe.correction.Λ R.probe.correction.G R.probe.correction.η_id
        (R.A.diagonal (forwardGenerator R c n)) : ℂ) := by
  rw [R.probe.theta_principal ⟨_, (forwardModulus_generates R c n).1⟩]
  have he : ThetaReflectionData.rowUnit R.A
    ⟨ThetaReflectionData.forwardModulus R.A R.probe.coefficients c n,
      (forwardModulus_generates R c n).1⟩ = forwardGenerator R c n :=
    Units.ext (forwardGenerator_val R c n).symm
  rw [he, R.probe.principalIdele]

end DedekindZetaZeroFree.OrbitExpansion

end
