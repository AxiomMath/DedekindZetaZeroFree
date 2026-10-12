module

public import DedekindZetaZeroFree.Adeles.Characters.CubicIdelePairing
public import DedekindZetaZeroFree.Arithmetic.Kummer.HilbertPairingLagrangianComplement
public import DedekindZetaZeroFree.Metaplectic.Torus.CubicIdeleQuotientCompactness

@[expose] public section

section

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.RepresentationTheory.KPPrincipalCubic
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]

def rawPrincipalClass : Fˣ →* KPGlobalCubicIdelePairing.D F :=
  (QuotientGroup.mk' (CubicCharacters.cubes (KPGlobalCubicIdelePairing.Ideles F))).comp
    (IdeleGroup.unitEmbedding (𝓞 F) F)

def rawFinitePrimes (S : Finset (KPHilbert.Place F)) : Finset (HeightOneSpectrum (𝓞 F)) :=
  S.biUnion (fun v => match v with | Sum.inl _ => ∅ | Sum.inr q => {q})

abbrev rawSUnits (S : Finset (KPHilbert.Place F)) :=
  (rawFinitePrimes F S : Set (HeightOneSpectrum (𝓞 F))).unit F

def rawClassKillingS (S : Finset (KPHilbert.Place F)) : Prop :=
  KPGlobalCubicIdelePairing.AdmissibleS F S ∧
  (∀ q : HeightOneSpectrum (𝓞 F), (6 : 𝓞 F) ∈ q.asIdeal → Sum.inr q ∈ S) ∧
  Subsingleton (ClassGroup
    ((rawFinitePrimes F S : Set (HeightOneSpectrum (𝓞 F))).integer F))

def rawFiniteClass (S : Finset (KPHilbert.Place F)) :
    Fˣ →* KPGlobalCubicIdelePairing.FiniteSClasses F S where
  toFun a v := KPGlobalCubicIdelePairing.localClass F v.val
    (Units.map (algebraMap F (KPHilbert.Completion F v.val)).toMonoidHom a)
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

def rawBetaS (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (S : Finset (KPHilbert.Place F))
    (x y : KPGlobalCubicIdelePairing.FiniteSClasses F S) : rootsOfUnity 3 F :=
  ∏ v ∈ S.attach, KPGlobalCubicIdelePairing.localPairing F ζ hζ v.val (x v) (y v)

end
end DedekindZetaZeroFree.RepresentationTheory.KPPrincipalCubic

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPPrincipalCubic
noncomputable section
open scoped NumberField
open NumberField
set_option autoImplicit false

theorem principal_pairing_trivial (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (a b : Fˣ) :
    KPGlobalCubicIdelePairing.beta3 F ζ hζ
      (rawPrincipalClass F a) (rawPrincipalClass F b) = 1 := by
  change KPGlobalCubicIdelePairing.beta3 F ζ hζ
    (QuotientGroup.mk' _ (IdeleGroup.unitEmbedding (𝓞 F) F a))
    (QuotientGroup.mk' _ (IdeleGroup.unitEmbedding (𝓞 F) F b)) = 1
  rw [KPGlobalCubicIdelePairing.beta3_idele_formula]
  convert (KPHilbert.B3_productFormula F ζ hζ a b).2 using 1
  apply finprod_congr
  intro v
  cases v <;> rfl

end
end DedekindZetaZeroFree.RepresentationTheory.KPPrincipalCubic

end

section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.RepresentationTheory.KPPrincipalCubic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
 theorem mem_fp (F : Type) [Field F] [NumberField F]
    (S : Finset (KPHilbert.Place F)) (q : HeightOneSpectrum (𝓞 F)) :
    q ∈ rawFinitePrimes F S ↔ Sum.inr q ∈ S := by
  simp only [rawFinitePrimes, Finset.mem_biUnion]
  constructor
  · rintro ⟨v, hv, h⟩
    cases v with
    | inl w => simp at h
    | inr r => simp only [Finset.mem_singleton] at h; subst r; exact hv
  · intro h; exact ⟨Sum.inr q, h, by simp⟩
 def data (F : Type) [Field F] [NumberField F] (ζ : F)
    (hζ : IsPrimitiveRoot ζ 12) (S : Finset (KPHilbert.Place F))
    (hS : rawClassKillingS F S) : SArithmeticData F where
  zeta12 := ζ
  primitive_zeta12 := hζ
  Sf := rawFinitePrimes F S
  S₀ := ∅
  bad_subset := Finset.empty_subset _
  modulus := ⊤
  modulus_ne_zero := top_ne_bot
  above_six q hq := (mem_fp F S q).mpr (hS.2.1 q hq)
  modulus_support q hq := False.elim (q.isPrime.ne_top (top_le_iff.mp hq))
 def classesEquiv (F : Type) [Field F] [NumberField F] (ζ : F)
    (hζ : IsPrimitiveRoot ζ 12) (S : Finset (KPHilbert.Place F))
    (hS : rawClassKillingS F S) :
    KPGlobalCubicIdelePairing.FiniteSClasses F S ≃*
      SArithmeticData.Vn F (data F ζ hζ S hS) 3 where
  toFun x := by
    intro v
    cases v with
    | inl w => exact x ⟨Sum.inl w, hS.1.1 w⟩
    | inr q => exact x ⟨Sum.inr q.val, (mem_fp F S q.val).mp q.property⟩
  invFun y := by
    rintro ⟨v,hv⟩
    cases v with
    | inl w => exact y (Sum.inl w)
    | inr q => exact y (Sum.inr ⟨q, (mem_fp F S q).mpr hv⟩)
  left_inv x := by ext ⟨v,hv⟩; cases v <;> rfl
  right_inv y := by ext v; cases v <;> rfl
  map_mul' x y := by ext v; cases v <;> rfl
private theorem classes_unit (F : Type) [Field F] [NumberField F] (ζ : F)
    (hζ : IsPrimitiveRoot ζ 12) (S : Finset (KPHilbert.Place F))
    (hS : rawClassKillingS F S) (u : rawSUnits F S) :
    classesEquiv F ζ hζ S hS (rawFiniteClass F S u.val) =
      SArithmeticData.GaussCorrection.unitPrimeHom (data F ζ hζ S hS) 3 u := by
  ext v; cases v <;> rfl
private theorem local_compare (F : Type) [Field F] [NumberField F] (ζ : F)
    (hζ : IsPrimitiveRoot ζ 12) (S : Finset (KPHilbert.Place F))
    (hS : rawClassKillingS F S) (q : HeightOneSpectrum (𝓞 F))
    (a b : KPGlobalCubicIdelePairing.LocalD F (Sum.inr q)) :
    KPGlobalCubicIdelePairing.localPairing F ζ hζ (Sum.inr q) a b =
      (data F ζ hζ S hS).actualLocalHilbert q 3 (Or.inr (Or.inl rfl)) a b := by
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      change KPHilbert.B3 F ζ hζ (Sum.inr q) a b = _
      rw [KPHilbert.B3_canonical]
      rfl
private theorem pairing_compare (F : Type) [Field F] [NumberField F] (ζ : F)
    (hζ : IsPrimitiveRoot ζ 12) (S : Finset (KPHilbert.Place F))
    (hS : rawClassKillingS F S) (x y : KPGlobalCubicIdelePairing.FiniteSClasses F S) :
    rawBetaS F ζ hζ S x y =
      (data F ζ hζ S hS).H_Sn 3 (Or.inr (Or.inl rfl))
        (classesEquiv F ζ hζ S hS x) (classesEquiv F ζ hζ S hS y) := by
  let A := data F ζ hζ S hS
  unfold rawBetaS
  rw [SArithmeticData.H_Sn_apply]
  symm
  let i (q : ↥A.Sf) : ↥S := ⟨Sum.inr q.val, (mem_fp F S q.val).mp q.property⟩
  apply Finset.prod_bij_ne_one (fun q _ _ => i q)
  · intros; exact Finset.mem_attach _ _
  · intro a ha hna b hb hnb hab
    apply Subtype.ext
    exact Sum.inr_injective (congrArg Subtype.val hab)
  · rintro ⟨v,hv⟩ hmem hn
    cases v with
    | inl w =>
      exfalso
      apply hn
      induction (x ⟨Sum.inl w,hv⟩) using QuotientGroup.induction_on with
      | H a =>
        induction (y ⟨Sum.inl w,hv⟩) using QuotientGroup.induction_on with
        | H b => simp [KPGlobalCubicIdelePairing.localPairing, KPHilbert.B3, KPHilbert.B6, KPHilbert.squareToThree]
    | inr q =>
      let a : ↥A.Sf := ⟨q, (mem_fp F S q).mpr hv⟩
      have hna : A.actualLocalHilbert a.val 3 (Or.inr (Or.inl rfl))
          (classesEquiv F ζ hζ S hS x (Sum.inr a))
          (classesEquiv F ζ hζ S hS y (Sum.inr a)) ≠ 1 := by
        rw [← local_compare F ζ hζ S hS]
        exact hn
      exact ⟨a, Finset.mem_univ _, hna, rfl⟩
  · intro a ha hna
    exact (local_compare F ζ hζ S hS a.val (x (i a)) (y (i a))).symm
private theorem prime_criterion {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (hCl : Subsingleton (ClassGroup A.R))
    (x : SArithmeticData.Vn F A 3) :
    (∀ u : A.U, A.H_Sn 3 (Or.inr (Or.inl rfl)) x
      (SArithmeticData.GaussCorrection.unitPrimeHom A 3 u) = 1) ↔
      ∃ u : A.U, SArithmeticData.GaussCorrection.unitPrimeHom A 3 u = x := by
  let P := A.H_Sn 3 (Or.inr (Or.inl rfl))
  let E := SArithmeticData.GaussCorrection.primeUnitImage A 3
  have hE (e : SArithmeticData.Vn F A 3) : e ∈ E ↔
      ∃ u : A.U, SArithmeticData.GaussCorrection.unitPrimeHom A 3 u = e := by
    constructor
    · rintro ⟨q,hq⟩
      induction q using QuotientGroup.induction_on with
      | H u => exact ⟨u,hq⟩
    · rintro ⟨u,rfl⟩
      exact ⟨QuotientGroup.mk' _ u,rfl⟩
  have hi := SArithmeticData.GaussCorrection.primeUnitImage_isotropic A 3 (Or.inr rfl)
  constructor
  · intro hx
    obtain ⟨B, hc, hBi, hs⟩ :=
      SArithmeticData.GaussCorrection.actualPrimeComplement A hCl 3 (Or.inr rfl)
    obtain ⟨⟨e,b⟩, hab, _⟩ := hs x
    have hx' (y : SArithmeticData.Vn F A 3) (hy : y ∈ E) : P y x = 1 := by
      obtain ⟨u,rfl⟩ := (hE y).mp hy
      rw [SArithmeticData.GaussCorrection.actualPrime_skew, hx u, inv_one]
    have hb (y : SArithmeticData.Vn F A 3) (hy : y ∈ E) : P y b.val = 1 := by
      have := hx' y hy
      rw [← hab, map_mul, hi y hy e e.property, one_mul] at this
      exact this
    have hb1 : b.val = 1 := by
      apply SArithmeticData.GaussCorrection.actualPrime_right_nondegenerate A 3 (Or.inr rfl)
      intro y
      obtain ⟨⟨a,c⟩, hay, _⟩ := hs y
      rw [← hay]
      change P (a.val * c.val) b.val = 1
      rw [SArithmeticData.H_Sn_mul_left, hb a.val a.property, hBi c.val c.property b.val b.property, mul_one]
    apply (hE x).mp
    rw [← hab, hb1, mul_one]
    exact e.property
  · rintro ⟨u,rfl⟩ v
    exact hi _ ((hE _).mpr ⟨u,rfl⟩) _ ((hE _).mpr ⟨v,rfl⟩)

theorem finite_sunit_orthogonality_iff (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (S : Finset (KPHilbert.Place F))
    (hS : rawClassKillingS F S) (x : KPGlobalCubicIdelePairing.FiniteSClasses F S) :
    (∀ u : rawSUnits F S, rawBetaS F ζ hζ S x (rawFiniteClass F S u.val) = 1) ↔
      ∃ u : rawSUnits F S, rawFiniteClass F S u.val = x := by
  have hc := prime_criterion (data F ζ hζ S hS) hS.2.2 (classesEquiv F ζ hζ S hS x)
  constructor
  · intro hx
    obtain ⟨u,hu⟩ := hc.mp (by
      intro u
      rw [← classes_unit, ← pairing_compare]
      exact hx u)
    refine ⟨u, (classesEquiv F ζ hζ S hS).injective ?_⟩
    rw [classes_unit]
    exact hu
  · rintro ⟨u,rfl⟩ v
    rw [pairing_compare, classes_unit, classes_unit]
    exact hc.mpr ⟨u,(classes_unit F ζ hζ S hS u).symm⟩ v
end
end DedekindZetaZeroFree.RepresentationTheory.KPPrincipalCubic

end

section

open scoped NumberField Classical BigOperators nonZeroDivisors
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.RepresentationTheory.KPPrincipalCubic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
variable (F : Type) [Field F] [NumberField F]

private lemma finite_mem (S : Finset (KPHilbert.Place F)) (q : HeightOneSpectrum (𝓞 F)) :
    q ∈ rawFinitePrimes F S ↔ Sum.inr q ∈ S := by
  simp only [rawFinitePrimes, Finset.mem_biUnion]
  constructor
  · rintro ⟨v, hv, hq⟩
    cases v with
    | inl w => simp at hq
    | inr p => simpa using (Finset.mem_singleton.mp hq) ▸ hv
  · intro h; exact ⟨Sum.inr q, h, by simp⟩

private lemma principal_unit (S : Finset (KPHilbert.Place F)) (u : rawSUnits F S)
    (v : KPHilbert.Place F) (hv : v ∉ S) :
    KPGlobalCubicIdelePairing.classComparison F (rawPrincipalClass F u.val) v ∈
      KPGlobalCubicIdelePairing.U F v := by
  cases v with
  | inl w => exact Subgroup.mem_top _
  | inr q =>
    have hu := u.property q (by simpa [finite_mem] using hv)
    letI : ValuativeRel (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
    letI : (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
    let z := Units.map (algebraMap F (q.adicCompletion F)).toMonoidHom u.val
    have hz : ValuativeRel.valuation (q.adicCompletion F) (z : q.adicCompletion F) = 1 := by
      rw [← (ValuativeRel.isEquiv (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ))) (ValuativeRel.valuation (q.adicCompletion F))).eq_one_iff_eq_one]
      change Valued.v (algebraMap F (q.adicCompletion F) (u.val : F)) = 1
      exact (q.valuedAdicCompletion_eq_valuation' (u.val : F)).trans hu
    have mem (a : (q.adicCompletion F)ˣ) (ha : ValuativeRel.valuation _ (a : q.adicCompletion F) = 1) :
        (a : q.adicCompletion F) ∈ (ValuativeRel.valuation (q.adicCompletion F)).integer := by
      rw [Valuation.mem_integer_iff, ha]
    let w : KPHilbert.LocalIntegerUnits F q :=
      ⟨⟨(z : q.adicCompletion F), mem z hz⟩,
       ⟨((z⁻¹ : (q.adicCompletion F)ˣ) : q.adicCompletion F), mem z⁻¹ (by simpa using congrArg Inv.inv hz)⟩,
       by apply Subtype.ext; exact z.val_inv,
       by apply Subtype.ext; exact z.inv_val⟩
    exact ⟨_, ⟨w, rfl⟩, rfl⟩
private lemma exists_classkill (T : Finset (KPHilbert.Place F)) :
    ∃ S : Finset (KPHilbert.Place F), T ⊆ S ∧ rawClassKillingS F S := by
  let bad := (KPAdelicCoverRestrictedProduct.bad_finite F).toFinset
  obtain ⟨Sf, hSf, hsix, _, hp⟩ := exists_principalizing_finite_set F
    (rawFinitePrimes F T ∪ bad) ⊤ top_ne_bot
  let S := (Finset.univ : Finset (InfinitePlace F)).image Sum.inl ∪ Sf.image Sum.inr
  have hfin : rawFinitePrimes F S = Sf := by
    ext q
    rw [finite_mem]
    simp [S]
  have hCl : Subsingleton (ClassGroup ((Sf : Set (HeightOneSpectrum (𝓞 F))).integer F)) := by
    have hOne : ∀ C : ClassGroup ((Sf : Set (HeightOneSpectrum (𝓞 F))).integer F), C = 1 := by
      intro C
      refine ClassGroup.induction F (fun I => ?_) C
      obtain ⟨a, ha⟩ := hp _ I.isUnit
      apply ClassGroup.mk_eq_one_iff.mpr
      rw [show (I : Submodule ((Sf : Set (HeightOneSpectrum (𝓞 F))).integer F) F) = Submodule.span _ {(a : F)} by
        change ((I : FractionalIdeal ((Sf : Set (HeightOneSpectrum (𝓞 F))).integer F)⁰ F) : Submodule ((Sf : Set (HeightOneSpectrum (𝓞 F))).integer F) F) = _
        rw [ha, FractionalIdeal.coe_spanSingleton]]
      exact ⟨⟨(a : F), rfl⟩⟩
    exact ⟨fun C D => (hOne C).trans (hOne D).symm⟩
  refine ⟨S, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
  · intro v hv
    cases v with
    | inl w => simp [S]
    | inr q =>
      have hq : q ∈ Sf := hSf (Finset.mem_union_left _ ((finite_mem F T q).mpr hv))
      simp [S, hq]
  · intro w; simp [S]
  · intro q hq
    have hm : q ∈ Sf := hSf (Finset.mem_union_right _ (by simpa [bad] using hq))
    simp [S, hm]
  · intro q hq; simp [S, hsix q hq]
  · change Subsingleton (ClassGroup ((rawFinitePrimes F S : Set (HeightOneSpectrum (𝓞 F))).integer F))
    rw [hfin]; exact hCl

private lemma principal_closed :
    IsClosed ((rawPrincipalClass F).range : Set (KPGlobalCubicIdelePairing.D F)) := by
  apply (QuotientGroup.isQuotientMap_mk (CubicCharacters.cubes (KPGlobalCubicIdelePairing.Ideles F))).isClosed_preimage.mp
  have heq : (QuotientGroup.mk ⁻¹' ((rawPrincipalClass F).range : Set (KPGlobalCubicIdelePairing.D F))) =
      (KPCubicIdele.rationalCubes F : Set _) := by
    ext x
    change (∃ a : Fˣ, rawPrincipalClass F a = QuotientGroup.mk x) ↔ x ∈ KPCubicIdele.rationalCubes F
    rw [KPCubicIdele.mem_rationalCubes_iff]
    constructor
    · rintro ⟨a, ha⟩
      have hmem : x / IdeleGroup.unitEmbedding (𝓞 F) F a ∈ CubicCharacters.cubes (KPGlobalCubicIdelePairing.Ideles F) := QuotientGroup.eq_iff_div_mem.mp ha.symm
      obtain ⟨b, hb⟩ := hmem
      refine ⟨a, b, ?_⟩
      change b ^ 3 = x / IdeleGroup.unitEmbedding (𝓞 F) F a at hb
      rw [hb]; simp
    · rintro ⟨a, b, rfl⟩
      refine ⟨a, ?_⟩
      change QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _
      rw [map_mul, show QuotientGroup.mk' (CubicCharacters.cubes (KPGlobalCubicIdelePairing.Ideles F)) (b ^ 3) = 1 from (QuotientGroup.eq_one_iff _).mpr ⟨b, rfl⟩, mul_one]
  rw [heq]
  exact KPCubicIdele.rationalCubes_isClosed F

private lemma beta_finite (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (KPHilbert.Place F)) (hS : KPGlobalCubicIdelePairing.AdmissibleS F S)
    (x : KPGlobalCubicIdelePairing.D F)
    (hxu : ∀ v, v ∉ S → KPGlobalCubicIdelePairing.classComparison F x v ∈ KPGlobalCubicIdelePairing.U F v)
    (u : rawSUnits F S) :
    KPGlobalCubicIdelePairing.beta3 F ζ hζ x (rawPrincipalClass F u.val) =
      rawBetaS F ζ hζ S (fun v => KPGlobalCubicIdelePairing.classComparison F x v.val) (rawFiniteClass F S u.val) := by
  have hout (v : KPHilbert.Place F) (hv : v ∉ S) :
      KPGlobalCubicIdelePairing.localPairing F ζ hζ v
        (KPGlobalCubicIdelePairing.classComparison F x v)
        (KPGlobalCubicIdelePairing.classComparison F (rawPrincipalClass F u.val) v) = 1 := by
    cases v with
    | inl w => exact False.elim (hv (hS.1 w))
    | inr q =>
      exact KPGlobalCubicIdelePairing.tame_unit_isotropic F ζ hζ q
        (fun h => hv (hS.2 q h)) _ _ (hxu _ hv) (principal_unit F S u _ hv)
  unfold KPGlobalCubicIdelePairing.beta3 KPGlobalCubicIdelePairing.restrictedBeta
  rw [finprod_eq_prod_of_mulSupport_subset _ (by
    intro v hv
    by_contra hn
    exact hv (hout v hn))]
  unfold rawBetaS
  rw [← Finset.prod_attach S]
  apply Finset.prod_congr rfl
  intro v hv
  rcases v with ⟨v, hv⟩
  cases v <;> rfl

theorem principal_of_finite_orthogonality (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hfinite : ∀ (S : Finset (KPHilbert.Place F)), rawClassKillingS F S →
      ∀ x : KPGlobalCubicIdelePairing.FiniteSClasses F S,
        (∀ u : rawSUnits F S, rawBetaS F ζ hζ S x (rawFiniteClass F S u.val) = 1) →
          ∃ u : rawSUnits F S, rawFiniteClass F S u.val = x)
    (x : KPGlobalCubicIdelePairing.D F)
    (hx : ∀ a : Fˣ, KPGlobalCubicIdelePairing.beta3 F ζ hζ x (rawPrincipalClass F a) = 1) :
    ∃ a : Fˣ, rawPrincipalClass F a = x := by
  obtain ⟨e, he⟩ := KPGlobalCubicIdelePairing.restricted_cube_quotient F
  let z := KPGlobalCubicIdelePairing.classComparison F x
  let T := (Filter.mem_cofinite.mp z.property).toFinset
  have hT : ∀ v, v ∉ T → z v ∈ KPGlobalCubicIdelePairing.U F v := by
    intro v hv
    by_contra h
    apply hv
    exact (Filter.mem_cofinite.mp z.property).mem_toFinset.mpr h
  have approx (I : Finset (KPHilbert.Place F)) :
      ∃ a : Fˣ, (∀ v ∈ I, KPGlobalCubicIdelePairing.classComparison F (rawPrincipalClass F a) v = z v) ∧
        ∀ v, v ∉ T → KPGlobalCubicIdelePairing.classComparison F (rawPrincipalClass F a) v ∈ KPGlobalCubicIdelePairing.U F v := by
    obtain ⟨S, hS, hkill⟩ := exists_classkill F (I ∪ T)
    have hxu : ∀ v, v ∉ S → z v ∈ KPGlobalCubicIdelePairing.U F v := by
      intro v hv
      exact hT v (fun h => hv (hS (Finset.mem_union_right _ h)))
    obtain ⟨u, hu⟩ := hfinite S hkill (fun v => z v.val) (fun u => by
      rw [← beta_finite F ζ hζ S hkill.1 x hxu u]
      exact hx u.val)
    have hucoord (v : KPHilbert.Place F) (hv : v ∈ S) :
        KPGlobalCubicIdelePairing.classComparison F (rawPrincipalClass F u.val) v = z v := by
      have h := congrFun hu ⟨v, hv⟩
      cases v <;> exact h
    refine ⟨u.val, ?_, ?_⟩
    · intro v hv; exact hucoord v (hS (Finset.mem_union_left _ hv))
    · intro v hv
      by_cases hvs : v ∈ S
      · rw [hucoord v hvs]; exact hT v hv
      · exact principal_unit F S u v hvs
  let A : (v : KPHilbert.Place F) → Set (KPGlobalCubicIdelePairing.LocalD F v) := fun v => (KPGlobalCubicIdelePairing.U F v : Set _)
  let Stage := RestrictedProduct (KPGlobalCubicIdelePairing.LocalD F) A (Filter.principal (T : Set _)ᶜ)
  let inc : Stage → KPGlobalCubicIdelePairing.RestrictedClasses F :=
    RestrictedProduct.inclusion _ A (Filter.le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite)
  let zz : Stage := ⟨z, hT⟩
  have hzclosed : IsClosed (e '' ((rawPrincipalClass F).range : Set _)) :=
    e.toHomeomorph.isClosedMap _ (principal_closed F)
  have hsclosed : IsClosed (inc ⁻¹' (e '' ((rawPrincipalClass F).range : Set _))) :=
    hzclosed.preimage (RestrictedProduct.continuous_inclusion (Filter.le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite))
  have hcl : zz ∈ closure (inc ⁻¹' (e '' ((rawPrincipalClass F).range : Set _))) := by
    rw [mem_closure_iff_nhds]
    intro N hN
    have hn := (RestrictedProduct.isEmbedding_coe_of_principal (R := KPGlobalCubicIdelePairing.LocalD F) (A := A) (S := (T : Set _)ᶜ)).isInducing.nhds_eq_comap zz
    rw [hn, Filter.mem_comap] at hN
    obtain ⟨M, hM, hMN⟩ := hN
    rw [nhds_pi, Filter.mem_pi'] at hM
    obtain ⟨I, t, ht, hMt⟩ := hM
    obtain ⟨a, ha, hau⟩ := approx I
    let aa : Stage := ⟨KPGlobalCubicIdelePairing.classComparison F (rawPrincipalClass F a), hau⟩
    refine ⟨aa, hMN (hMt ?_), ?_⟩
    · intro v hv
      change KPGlobalCubicIdelePairing.classComparison F (rawPrincipalClass F a) v ∈ t v
      rw [ha v hv]
      exact mem_of_mem_nhds (ht v)
    · exact ⟨rawPrincipalClass F a, ⟨a, rfl⟩, he _⟩
  rw [hsclosed.closure_eq] at hcl
  obtain ⟨b, hb, hbe⟩ := hcl
  have hbx : b = x := e.injective (hbe.trans (he x).symm)
  exact hbx ▸ hb

end
end DedekindZetaZeroFree.RepresentationTheory.KPPrincipalCubic

end

section

open scoped NumberField Classical BigOperators nonZeroDivisors
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalPrincipalCubicLagrangian

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def principalClass : Fˣ →* KPGlobalCubicIdelePairing.D F :=
  (QuotientGroup.mk' (CubicCharacters.cubes (KPGlobalCubicIdelePairing.Ideles F))).comp
    (IdeleGroup.unitEmbedding (𝓞 F) F)

def A : Subgroup (KPGlobalCubicIdelePairing.D F) := (principalClass F).range

def annihilator (H : Subgroup (KPGlobalCubicIdelePairing.D F)) :
    Set (KPGlobalCubicIdelePairing.D F) :=
  {x | ∀ y ∈ H, KPGlobalCubicIdelePairing.beta3 F ζ hζ x y = 1}

include ζ hζ

theorem principal_discrete : DiscreteTopology (A F) := by
  letI := KPGlobalCubicIdelePairing.hausdorff F
  letI := KPGlobalCubicIdelePairing.locally_compact F
  have hclosed : IsClosed (A F : Set (KPGlobalCubicIdelePairing.D F)) := by
    apply (QuotientGroup.isQuotientMap_mk
      (CubicCharacters.cubes (KPGlobalCubicIdelePairing.Ideles F))).isClosed_preimage.mp
    have heq : (QuotientGroup.mk ⁻¹' (A F : Set (KPGlobalCubicIdelePairing.D F))) =
        (KPCubicIdele.rationalCubes F : Set _) := by
      ext x
      change (∃ a : Fˣ, principalClass F a = QuotientGroup.mk x) ↔ _
      change (∃ a : Fˣ, principalClass F a = QuotientGroup.mk x) ↔
        x ∈ KPCubicIdele.rationalCubes F
      rw [KPCubicIdele.mem_rationalCubes_iff]
      constructor
      · rintro ⟨a, ha⟩
        have hmem : x / IdeleGroup.unitEmbedding (𝓞 F) F a ∈
            CubicCharacters.cubes (KPGlobalCubicIdelePairing.Ideles F) :=
          QuotientGroup.eq_iff_div_mem.mp ha.symm
        obtain ⟨b, hb⟩ := hmem
        refine ⟨a, b, ?_⟩
        change b ^ 3 = x / IdeleGroup.unitEmbedding (𝓞 F) F a at hb
        rw [hb]
        simp
      · rintro ⟨a, b, rfl⟩
        refine ⟨a, ?_⟩
        change QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _
        rw [map_mul, show QuotientGroup.mk' (CubicCharacters.cubes
          (KPGlobalCubicIdelePairing.Ideles F)) (b ^ 3) = 1 from
          (QuotientGroup.eq_one_iff _).mpr ⟨b, rfl⟩, mul_one]
    rw [heq]
    exact KPCubicIdele.rationalCubes_isClosed F
  letI : LocallyCompactSpace (A F) := hclosed.locallyCompactSpace
  letI : Countable F := (Module.Free.chooseBasis ℚ F).repr.injective.countable
  letI : Countable Fˣ := Units.val_injective.countable
  letI : Countable (A F) := (principalClass F).rangeRestrict_surjective.countable
  obtain ⟨a, b, hb⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun a : A F => ({a} : Set (A F))) (fun _ => isClosed_singleton)
    (by ext x; simp)
  have ha : IsOpen ({a} : Set (A F)) := by
    have hi := interior_subset hb
    have heq : interior ({a} : Set (A F)) = {a} := by
      apply Set.Subset.antisymm interior_subset
      have hba : b = a := hi
      simpa [hba] using hb
    rw [← heq]
    exact isOpen_interior
  exact discreteTopology_iff_isOpen_singleton_one.mpr (by
    have h := ha.preimage (continuous_const_mul a)
    have heq : (fun x : A F => a * x) ⁻¹' {a} = {1} := by
      ext x
      simp
    rwa [heq] at h)

theorem principal_cocompact :
    CompactSpace (KPGlobalCubicIdelePairing.D F ⧸ A F) := by
  let q := QuotientGroup.mk' (CubicCharacters.cubes (KPGlobalCubicIdelePairing.Ideles F))
  let f := (QuotientGroup.mk' (A F)).comp q
  have hk : KPCubicIdele.rationalCubes F ≤ f.ker := by
    apply sup_le
    · rintro x ⟨a, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
    · rintro x ⟨a, rfl⟩
      change f (a ^ 3) = 1
      change QuotientGroup.mk' (A F) (q (a ^ 3)) = 1
      have ha : q (a ^ 3) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
      rw [ha, map_one]
  let g := QuotientGroup.lift (KPCubicIdele.rationalCubes F) f hk
  have hg : Continuous g := by
    apply (QuotientGroup.isQuotientMap_mk (KPCubicIdele.rationalCubes F)).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp QuotientGroup.continuous_mk
  have hs : Function.Surjective g :=
    QuotientGroup.lift_surjective_of_surjective (N := KPCubicIdele.rationalCubes F) f
      ((QuotientGroup.mk'_surjective (A F)).comp
        (QuotientGroup.mk'_surjective (CubicCharacters.cubes
          (KPGlobalCubicIdelePairing.Ideles F)))) hk
  letI := (KPCubicIdele.cubicClasses_compact_hausdorff F).1
  exact hs.compactSpace hg

theorem principal_self_annihilating : annihilator F ζ hζ (A F) = (A F : Set _) := by
  ext x
  constructor
  · intro hx
    exact RepresentationTheory.KPPrincipalCubic.principal_of_finite_orthogonality F ζ hζ
      (fun S hS x hx =>
        (RepresentationTheory.KPPrincipalCubic.finite_sunit_orthogonality_iff F ζ hζ S hS x).mp hx)
      x (fun a => hx (principalClass F a) ⟨a, rfl⟩)
  · rintro ⟨a, rfl⟩ y ⟨b, rfl⟩
    exact RepresentationTheory.KPPrincipalCubic.principal_pairing_trivial F ζ hζ a b

end
end DedekindZetaZeroFree.KPGlobalPrincipalCubicLagrangian

end

section

open scoped NumberField Classical BigOperators nonZeroDivisors
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalPrincipalCubicLagrangian

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

include ζ hζ

omit ζ hζ

def finitePrimes (S : Finset (KPHilbert.Place F)) : Finset (HeightOneSpectrum (𝓞 F)) :=
  S.biUnion (fun v => match v with | Sum.inl _ => ∅ | Sum.inr q => {q})

abbrev SIntegers (S : Finset (KPHilbert.Place F)) :=
  (finitePrimes F S : Set (HeightOneSpectrum (𝓞 F))).integer F

def ClassKillingS (S : Finset (KPHilbert.Place F)) : Prop :=
  KPGlobalCubicIdelePairing.AdmissibleS F S ∧
  (∀ q : HeightOneSpectrum (𝓞 F), (6 : 𝓞 F) ∈ q.asIdeal → Sum.inr q ∈ S) ∧
  Subsingleton (ClassGroup (SIntegers F S))

abbrev DS (S : Finset (KPHilbert.Place F)) :=
  KPGlobalCubicIdelePairing.FiniteSClasses F S

def finitePrincipalClass (S : Finset (KPHilbert.Place F)) : Fˣ →* DS F S where
  toFun a v := KPGlobalCubicIdelePairing.localClass F v.val
    (Units.map (algebraMap F (KPHilbert.Completion F v.val)).toMonoidHom a)
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

include ζ hζ

end
end DedekindZetaZeroFree.KPGlobalPrincipalCubicLagrangian

end
