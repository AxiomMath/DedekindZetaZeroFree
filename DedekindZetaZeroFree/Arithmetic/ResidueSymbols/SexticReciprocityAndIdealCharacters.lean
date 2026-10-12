module

public import DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerResidueQuotientEquivalence
public import DedekindZetaZeroFree.Arithmetic.Ideals.AllowedGenerators

@[expose] public section

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.ResidueReciprocity

noncomputable section
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]

theorem exists_exterior_prime_sextic_character (A : SArithmeticData F)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hI : I.val = v.asIdeal) :
    ∃ c : (A.R ⧸ A.extendIdeal I)ˣ →* Fˣ,
      (∀ x, c x ^ 6 = 1) ∧
      (∀ x : (A.R ⧸ A.extendIdeal I)ˣ,
        ∃ j : ℕ, j < 6 ∧ (c x : F) = A.zeta12 ^ (2 * j) ∧
          Ideal.Quotient.mk (A.extendIdeal I)
            (algebraMap (𝓞 F) A.R (A.primitive_zeta12.toInteger ^ (2 * j))) =
          (x : A.R ⧸ A.extendIdeal I) ^
            ((Nat.card (A.R ⧸ A.extendIdeal I) - 1) / 6)) := by
  have hv : v ∉ A.Sf := by
    intro hv
    have hh := (A.exterior_iff ⟨I.val, I.property.1⟩).mp I.property.2 v hv
    rw [hI, sup_idem] at hh
    exact v.isPrime.ne_top hh
  have hn := A.exterior_norm_mod_twelve v hv
  have hc : (Ideal.absNorm I.val).Coprime 6 := by
    rw [hI]
    rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one]
    have : Ideal.absNorm v.asIdeal % 6 = 1 := by omega
    rw [Nat.gcd_rec, this]
    simp
  have hnt : Ideal.absNorm I.val ≠ 1 := by
    intro h
    exact v.isPrime.ne_top (hI ▸ (Ideal.absNorm_eq_one_iff.mp h))
  letI : I.val.IsMaximal := hI ▸ v.isMaximal
  let Q := 𝓞 F ⧸ I.val
  letI : Field Q := Ideal.Quotient.field I.val
  let E := ArithGaussCRT.exteriorQuotientEquiv A I
  have hcard : Nat.card (A.R ⧸ A.extendIdeal I) = Ideal.absNorm I.val :=
    (Nat.card_congr E.toEquiv).symm
  have hd : 6 ∣ Nat.card Q - 1 := by
    change 6 ∣ Ideal.absNorm I.val - 1
    rw [hI]
    omega
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Fintype Qˣ := Fintype.ofFinite Qˣ
  let z := A.primitive_zeta12.toInteger ^ 2
  have hz : IsPrimitiveRoot z 6 :=
    A.primitive_zeta12.toInteger_isPrimitiveRoot.pow (by decide) (by decide : 12 = 2 * 6)
  have hzq : IsPrimitiveRoot (Ideal.Quotient.mk I.val z) 6 := hz.idealQuotient_mk hnt hc
  let r : rootsOfUnity 6 (𝓞 F) →* rootsOfUnity 6 Q :=
    (Ideal.rootsOfUnityMapQuot I.val 6).codRestrict _ (by
      intro t
      rw [mem_rootsOfUnity]
      rw [← map_pow]
      have ht : t ^ 6 = 1 := by
        apply Subtype.ext
        exact (mem_rootsOfUnity 6 t.val).mp t.property
      rw [ht, map_one])
  have hr : Function.Bijective r := by
    constructor
    · intro a b hab
      apply Ideal.rootsOfUnityMapQuot_injective 6 hnt hc
      exact congrArg Subtype.val hab
    · intro t
      obtain ⟨j, hj, he⟩ := hzq.eq_pow_of_pow_eq_one (show (t.val : Q) ^ 6 = 1 by
        exact congrArg Units.val ((mem_rootsOfUnity 6 t.val).mp t.property))
      refine ⟨hz.toRootsOfUnity ^ j, ?_⟩
      apply Subtype.ext
      apply Units.ext
      change Ideal.Quotient.mk I.val ((hz.toRootsOfUnity.val : 𝓞 F) ^ j) = (t.val : Q)
      simpa only [map_pow, hz.val_toRootsOfUnity_coe] using he
  let e := MulEquiv.ofBijective r hr
  let k := (Nat.card (A.R ⧸ A.extendIdeal I) - 1) / 6
  have hp (x : Qˣ) : (x ^ k) ^ 6 = 1 := by
    rw [← pow_mul]
    have hk : k * 6 = Fintype.card Qˣ := by
      rw [← Nat.card_eq_fintype_card]
      rw [Nat.card_units Q]
      change ((Nat.card (A.R ⧸ A.extendIdeal I) - 1) / 6) * 6 = Nat.card Q - 1
      rw [hcard]
      exact Nat.div_mul_cancel hd
    rw [hk]
    exact pow_card_eq_one
  let p : Qˣ →* rootsOfUnity 6 Q := (powMonoidHom k).codRestrict _ (by
    intro x
    exact (mem_rootsOfUnity 6 _).mpr (hp x))
  let g : rootsOfUnity 6 (𝓞 F) →* Fˣ :=
    (Units.map (algebraMap (𝓞 F) F).toMonoidHom).comp (rootsOfUnity 6 (𝓞 F)).subtype
  let c : (A.R ⧸ A.extendIdeal I)ˣ →* Fˣ :=
    g.comp (e.symm.toMonoidHom.comp (p.comp (Units.map E.symm.toMonoidHom)))
  refine ⟨c, ?_, ?_⟩
  · intro x
    change g (e.symm (p (Units.map E.symm.toMonoidHom x))) ^ 6 = 1
    rw [← map_pow]
    have ht : e.symm (p (Units.map E.symm.toMonoidHom x)) ^ 6 = 1 := by
      apply Subtype.ext
      exact (mem_rootsOfUnity 6 _).mp (e.symm _).property
    rw [ht, map_one]
  · intro x
    let t := e.symm (p (Units.map E.symm.toMonoidHom x))
    obtain ⟨j, hj, he⟩ := hz.eq_pow_of_pow_eq_one (show (t.val : 𝓞 F) ^ 6 = 1 by
      exact congrArg Units.val ((mem_rootsOfUnity 6 t.val).mp t.property))
    refine ⟨j, hj, ?_, ?_⟩
    · change (algebraMap (𝓞 F) F) (t.val : 𝓞 F) = _
      rw [← he]
      rw [map_pow, map_pow]
      change ((A.primitive_zeta12.toInteger : F) ^ 2) ^ j = _
      exact (congrArg (fun a : F => (a ^ 2) ^ j) A.primitive_zeta12.coe_toInteger).trans (pow_mul _ _ _).symm
    · have ht : r t = p (Units.map E.symm.toMonoidHom x) := e.apply_symm_apply _
      have hte := congrArg (fun a : rootsOfUnity 6 Q => (a.val : Q)) ht
      change Ideal.Quotient.mk I.val (t.val : 𝓞 F) = (E.symm (x : A.R ⧸ A.extendIdeal I)) ^ k at hte
      rw [← he] at hte
      have hh := congrArg E hte
      calc
        Ideal.Quotient.mk (A.extendIdeal I)
          (algebraMap (𝓞 F) A.R (A.primitive_zeta12.toInteger ^ (2 * j))) =
            E (Ideal.Quotient.mk I.val (z ^ j)) := by
              rw [show z ^ j = A.primitive_zeta12.toInteger ^ (2 * j) from (pow_mul _ _ _).symm]
              exact (ArithGaussCRT.exteriorQuotientEquiv_mk A I _).symm
        _ = (x : A.R ⧸ A.extendIdeal I) ^ k := by
              simpa only [map_pow, E.apply_symm_apply] using hh

end
end DedekindZetaZeroFree.ResidueReciprocity

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.ResidueReciprocity

noncomputable section
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]

set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {R : Type*} [CommRing R]
private lemma unit_iff (I : Ideal R) (x : R) :
    IsUnit (Ideal.Quotient.mk I x) ↔ Ideal.span {x} ⊔ I = ⊤ := by
  rw [isUnit_iff_exists_inv, Ideal.eq_top_iff_one]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hm : x * z - 1 ∈ I := Ideal.Quotient.eq.mp (by simpa using hy)
    have hx : x * z ∈ Ideal.span {x} ⊔ I := Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr ⟨z, rfl⟩)
    have hd : x * z - 1 ∈ Ideal.span {x} ⊔ I := Ideal.mem_sup_right hm
    simpa using (Ideal.span {x} ⊔ I).sub_mem hx hd
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp ha
    refine ⟨Ideal.Quotient.mk I z, ?_⟩
    have hh := congrArg (Ideal.Quotient.mk I) hab
    simpa [Ideal.Quotient.eq_zero_iff_mem.mpr hb] using hh
private lemma unit_prod (s : Multiset (Ideal R)) (x : R) :
    IsUnit (Ideal.Quotient.mk s.prod x) ↔ ∀ q ∈ s, IsUnit (Ideal.Quotient.mk q x) := by
  constructor
  · intro hx q hq
    have hle : s.prod ≤ q := by
      obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hq
      simpa using (Ideal.mul_le_left : q * t.prod ≤ q)
    simpa using hx.map (Ideal.Quotient.factor hle)
  · intro h
    rw [unit_iff]
    exact Ideal.sup_multiset_prod_eq_top (fun q hq => (unit_iff q x).mp (h q hq))
end

noncomputable section
variable (A : SArithmeticData F)
local notation "ext" => Ideal.map (algebraMap (𝓞 F) A.R)
 def ph
    (p : (I : A.Exterior) → (v : HeightOneSpectrum (𝓞 F)) →
      I.val = v.asIdeal → ((A.R ⧸ A.extendIdeal I)ˣ →* Fˣ))
    (q : Ideal (𝓞 F)) : (A.R ⧸ ext q)ˣ →* Fˣ :=
  if h : q ≠ ⊥ ∧ q ⊔ A.cS = ⊤ ∧ q.IsPrime then
    p ⟨q, h.1, h.2.1⟩ ⟨q, h.2.2, h.1⟩ rfl
  else 1
private lemma factor_le (I : A.Exterior) (q : Ideal (𝓞 F))
    (hq : q ∈ normalizedFactors I.val) : I.val ≤ q :=
  (Ideal.mem_normalizedFactors_iff I.property.1).mp hq |>.2
 def pull (I : A.Exterior) (q : Ideal (𝓞 F))
    (p : (I : A.Exterior) → (v : HeightOneSpectrum (𝓞 F)) →
      I.val = v.asIdeal → ((A.R ⧸ A.extendIdeal I)ˣ →* Fˣ)) :
    (A.R ⧸ A.extendIdeal I)ˣ →* Fˣ :=
  if h : I.val ≤ q then
    (ph A p q).comp (Units.map (Ideal.Quotient.factor (Ideal.map_mono h)).toMonoidHom)
  else 1
 def chars
    (p : (I : A.Exterior) → (v : HeightOneSpectrum (𝓞 F)) →
      I.val = v.asIdeal → ((A.R ⧸ A.extendIdeal I)ˣ →* Fˣ))
    (I : A.Exterior) : (A.R ⧸ A.extendIdeal I)ˣ →* Fˣ :=
  ((normalizedFactors I.val).map (fun q => pull A I q p)).prod
private lemma ph_pow
    (p : (I : A.Exterior) → (v : HeightOneSpectrum (𝓞 F)) →
      I.val = v.asIdeal → ((A.R ⧸ A.extendIdeal I)ˣ →* Fˣ))
    (hp : ∀ I v hI x, p I v hI x ^ 6 = 1)
    (q : Ideal (𝓞 F)) (x : (A.R ⧸ ext q)ˣ) : ph A p q x ^ 6 = 1 := by
  by_cases h : q ≠ ⊥ ∧ q ⊔ A.cS = ⊤ ∧ q.IsPrime
  · simp only [ph, dif_pos h]
    exact hp _ _ _ _
  · simp [ph, h]
private lemma chars_pow
    (p : (I : A.Exterior) → (v : HeightOneSpectrum (𝓞 F)) →
      I.val = v.asIdeal → ((A.R ⧸ A.extendIdeal I)ˣ →* Fˣ))
    (hp : ∀ I v hI x, p I v hI x ^ 6 = 1)
    (I : A.Exterior) (x : (A.R ⧸ A.extendIdeal I)ˣ) : chars A p I x ^ 6 = 1 := by
  have hv (q : Ideal (𝓞 F)) : (pull A I q p x) ^ 6 = 1 := by
    by_cases h : I.val ≤ q
    · simp only [pull, dif_pos h, MonoidHom.comp_apply]
      exact ph_pow A p hp _ _
    · simp [pull, h]
  change ((Multiset.map (fun q => pull A I q p) (normalizedFactors I.val)).prod x) ^ 6 = 1
  have hhom (s : Multiset ((A.R ⧸ A.extendIdeal I)ˣ →* Fˣ)) :
      s.prod x = (s.map (· x)).prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons f s ih => simp [ih]
  rw [hhom, ← Multiset.prod_map_pow, Multiset.map_map]
  apply Multiset.prod_eq_one
  intro y hy
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hy
  exact hv q
private lemma chars_prime
    (p : (I : A.Exterior) → (v : HeightOneSpectrum (𝓞 F)) →
      I.val = v.asIdeal → ((A.R ⧸ A.extendIdeal I)ˣ →* Fˣ))
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hI : I.val = v.asIdeal) :
    chars A p I = p I v hI := by
  rcases I with ⟨i, hi⟩
  change i = v.asIdeal at hI
  have hp : Irreducible i := by
    rw [hI]
    exact ((Ideal.prime_iff_isPrime v.ne_bot).mpr v.isPrime).irreducible
  simp only [chars, normalizedFactors_irreducible hp, normalize_eq,
    Multiset.map_singleton, Multiset.prod_singleton]
  have hh : i ≠ ⊥ ∧ i ⊔ A.cS = ⊤ ∧ i.IsPrime :=
    ⟨hi.1, hi.2, hI ▸ v.isPrime⟩
  simp only [pull, dif_pos (le_refl i), ph, dif_pos hh]
  have hv : (⟨i, hh.2.2, hh.1⟩ : HeightOneSpectrum (𝓞 F)) = v := by
    apply HeightOneSpectrum.ext
    exact hI
  subst v
  ext x
  have hu : Units.map (Ideal.Quotient.factor (Ideal.map_mono (le_refl i))).toMonoidHom x = x := by
    apply Units.ext
    simp [Ideal.Quotient.factor_eq]
  change ((p ⟨i, hi⟩ _ hI) _ : F) = ((p ⟨i, hi⟩ _ hI) x : F)
  congr 2
private lemma map_prod (s : Multiset (Ideal (𝓞 F))) :
    (s.map (fun q => ext q)).prod = ext s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp [Ideal.map_top]
  | @cons q s ih => simp [ih, Ideal.map_mul]
private lemma unit_factors (I : A.Exterior) (x : A.R) :
    IsUnit (Ideal.Quotient.mk (A.extendIdeal I) x) ↔
      ∀ q ∈ normalizedFactors I.val, IsUnit (Ideal.Quotient.mk (ext q) x) := by
  have he : ((normalizedFactors I.val).map (fun q => ext q)).prod = A.extendIdeal I := by
    rw [map_prod, Ideal.prod_normalizedFactors_eq_self I.property.1]
    rfl
  rw [← he, unit_prod]
  simp only [Multiset.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h q hq
    exact h _ q hq rfl
  · intro h j q hq hj
    subst j
    exact h q hq
private lemma pull_value
    (p : (I : A.Exterior) → (v : HeightOneSpectrum (𝓞 F)) →
      I.val = v.asIdeal → ((A.R ⧸ A.extendIdeal I)ˣ →* Fˣ))
    (I : A.Exterior) (q : Ideal (𝓞 F)) (hq : q ∈ normalizedFactors I.val)
    (x : A.R) (hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) x)) :
    (pull A I q p hx.unit : F) =
      MulChar.ofUnitHom (ph A p q) (Ideal.Quotient.mk (ext q) x) := by
  have hle := factor_le A I q hq
  simp only [pull, dif_pos hle, MonoidHom.comp_apply]
  have hu : ((Units.map (Ideal.Quotient.factor (Ideal.map_mono hle)).toMonoidHom hx.unit) :
      A.R ⧸ ext q) = Ideal.Quotient.mk (ext q) x := by
    change (Ideal.Quotient.factor (Ideal.map_mono hle)) (hx.unit : A.R ⧸ A.extendIdeal I) = _
    rw [hx.unit_spec]
    exact Ideal.Quotient.factor_mk _ x
  rw [← hu, MulChar.ofUnitHom_coe]
  rfl
private lemma chars_raw
    (p : (I : A.Exterior) → (v : HeightOneSpectrum (𝓞 F)) →
      I.val = v.asIdeal → ((A.R ⧸ A.extendIdeal I)ˣ →* Fˣ))
    (I : A.Exterior) (x : A.R) :
    MulChar.ofUnitHom (chars A p I) (Ideal.Quotient.mk (A.extendIdeal I) x) =
      ((normalizedFactors I.val).map
        (fun q => MulChar.ofUnitHom (ph A p q) (Ideal.Quotient.mk (ext q) x))).prod := by
  by_cases hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) x)
  · rw [← hx.unit_spec, MulChar.ofUnitHom_coe]
    have hhom (s : Multiset ((A.R ⧸ A.extendIdeal I)ˣ →* Fˣ)) :
        (s.prod hx.unit : F) = (s.map (fun f => (f hx.unit : F))).prod := by
      induction s using Multiset.induction_on with
      | empty => simp
      | @cons f s ih => simp [ih]
    change (((normalizedFactors I.val).map (fun q => pull A I q p)).prod hx.unit : F) = _
    rw [hhom, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl (fun q hq => pull_value A p I q hq x hx)
  · rw [MulChar.map_nonunit _ hx]
    have hfail : ∃ q ∈ normalizedFactors I.val, ¬ IsUnit (Ideal.Quotient.mk (ext q) x) := by
      simpa only [not_forall, exists_prop] using mt (unit_factors A I x).mpr hx
    obtain ⟨q, hq, hqu⟩ := hfail
    symm
    apply Multiset.prod_eq_zero
    exact Multiset.mem_map.mpr ⟨q, hq, MulChar.map_nonunit _ hqu⟩
private lemma chars_mul
    (p : (I : A.Exterior) → (v : HeightOneSpectrum (𝓞 F)) →
      I.val = v.asIdeal → ((A.R ⧸ A.extendIdeal I)ˣ →* Fˣ))
    (I J K : A.Exterior) (hK : K.val = I.val * J.val) (x : A.R) :
    MulChar.ofUnitHom (chars A p K) (Ideal.Quotient.mk (A.extendIdeal K) x) =
      MulChar.ofUnitHom (chars A p I) (Ideal.Quotient.mk (A.extendIdeal I) x) *
      MulChar.ofUnitHom (chars A p J) (Ideal.Quotient.mk (A.extendIdeal J) x) := by
  rw [chars_raw, chars_raw, chars_raw]
  rw [hK, normalizedFactors_mul I.property.1 J.property.1, Multiset.map_add, Multiset.prod_add]
end

theorem extend_exterior_prime_sextic_characters (A : SArithmeticData F)
    (p : (I : A.Exterior) → (v : HeightOneSpectrum (𝓞 F)) →
      I.val = v.asIdeal → ((A.R ⧸ A.extendIdeal I)ˣ →* Fˣ))
    (hp : ∀ I v hI x, p I v hI x ^ 6 = 1) :
    ∃ C : (I : A.Exterior) → ((A.R ⧸ A.extendIdeal I)ˣ →* Fˣ),
      (∀ I x, C I x ^ 6 = 1) ∧
      (∀ I v hI, C I = p I v hI) ∧
      (∀ (I J K : A.Exterior), K.val = I.val * J.val →
        ∀ x : A.R,
          MulChar.ofUnitHom (C K) (Ideal.Quotient.mk (A.extendIdeal K) x) =
            MulChar.ofUnitHom (C I) (Ideal.Quotient.mk (A.extendIdeal I) x) *
              MulChar.ofUnitHom (C J) (Ideal.Quotient.mk (A.extendIdeal J) x)) := by
  refine ⟨chars A p, chars_pow A p hp, chars_prime A p, ?_⟩
  intro I J K hK x
  exact chars_mul A p I J K hK x

end
end DedekindZetaZeroFree.ResidueReciprocity

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SArithmeticData

noncomputable section
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]

abbrev SexticResidueFamily (A : SArithmeticData F) :=
  (I : A.Exterior) → (A.R ⧸ A.extendIdeal I)ˣ →* Fˣ

def residueValue (A : SArithmeticData F) (C : A.SexticResidueFamily)
    (I : A.Exterior) (x : A.R) : F :=
  MulChar.ofUnitHom (C I) (Ideal.Quotient.mk (A.extendIdeal I) x)

def IsNormalizedSexticResidueFamily (A : SArithmeticData F)
    (C : A.SexticResidueFamily) : Prop :=
  (∀ (I : A.Exterior) (x : (A.R ⧸ A.extendIdeal I)ˣ), C I x ^ 6 = 1) ∧
  (∀ (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)), I.val = v.asIdeal →
    ∀ x : (A.R ⧸ A.extendIdeal I)ˣ,
      ∃ j : ℕ, j < 6 ∧ (C I x : F) = A.zeta12 ^ (2 * j) ∧
        Ideal.Quotient.mk (A.extendIdeal I)
          (algebraMap (𝓞 F) A.R (A.primitive_zeta12.toInteger ^ (2 * j))) =
        (x : A.R ⧸ A.extendIdeal I) ^
          ((Nat.card (A.R ⧸ A.extendIdeal I) - 1) / 6)) ∧
  (∀ (I J K : A.Exterior), K.val = I.val * J.val →
    ∀ x : A.R, A.residueValue C K x = A.residueValue C I x * A.residueValue C J x)

theorem residueFamily_ext (A : SArithmeticData F) {C D : A.SexticResidueFamily}
    (h : ∀ I x, A.residueValue C I x = A.residueValue D I x) : C = D := by
  funext I
  apply MonoidHom.ext
  intro x
  apply Units.ext
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (x : A.R ⧸ A.extendIdeal I)
  have he := h I r
  unfold residueValue at he
  rw [hr, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe] at he
  exact he

theorem residueValue_top (A : SArithmeticData F) (C : A.SexticResidueFamily)
    (I : A.Exterior) (hI : I.val = ⊤) (x : A.R) : A.residueValue C I x = 1 := by
  have ht : A.extendIdeal I = ⊤ := by simpa only [extendIdeal, hI] using
    (Ideal.map_top (algebraMap (𝓞 F) A.R))
  have he : Ideal.Quotient.mk (A.extendIdeal I) x = 1 := by
    rw [← map_one (Ideal.Quotient.mk (A.extendIdeal I)), Ideal.Quotient.eq]
    rw [ht]
    trivial
  simp [residueValue, he]

theorem residueFamily_ext_of_prime_values (A : SArithmeticData F)
    {C D : A.SexticResidueFamily}
    (hC : ∀ (I J K : A.Exterior), K.val = I.val * J.val →
      ∀ x, A.residueValue C K x = A.residueValue C I x * A.residueValue C J x)
    (hD : ∀ (I J K : A.Exterior), K.val = I.val * J.val →
      ∀ x, A.residueValue D K x = A.residueValue D I x * A.residueValue D J x)
    (hp : ∀ (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)), I.val = v.asIdeal →
      ∀ x, A.residueValue C I x = A.residueValue D I x) : C = D := by
  apply residueFamily_ext
  intro I x
  have hall : ∀ (a : Ideal (𝓞 F)) (J : A.Exterior), J.val = a →
      A.residueValue C J x = A.residueValue D J x := by
    intro a
    induction a using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
      intro J hJ
      exact (J.prop.1 hJ).elim
    | h₂ a ha =>
      intro J hJ
      have ht : J.val = ⊤ := hJ.trans (Ideal.isUnit_iff.mp ha)
      rw [residueValue_top A C J ht, residueValue_top A D J ht]
    | h₃ a p ha hp' ih =>
      intro J hJ
      have haS : a ⊔ A.cS = ⊤ := by
        apply top_unique
        rw [← J.prop.2]
        apply sup_le_sup_right
        rw [hJ]
        exact Ideal.mul_le_right
      have hpS : p ⊔ A.cS = ⊤ := by
        apply top_unique
        rw [← J.prop.2]
        apply sup_le_sup_right
        rw [hJ]
        exact Ideal.mul_le_left
      let Ia : A.Exterior := ⟨a, ha, haS⟩
      let Ip : A.Exterior := ⟨p, hp'.ne_zero, hpS⟩
      rw [hC Ip Ia J hJ x, hD Ip Ia J hJ x, ih Ia rfl,
        hp Ip (HeightOneSpectrum.ofPrime hp') rfl x]
  exact hall I.val I rfl

private theorem primitiveRoot_mod_ideal_of_unit_order {R : Type} [CommRing R] [IsDomain R]
    (I : Ideal R) (hI : I ≠ ⊤) (z : R) (h : IsPrimitiveRoot z 6)
    (hunit : IsUnit (6 : R)) :
    IsPrimitiveRoot ((Ideal.Quotient.mk I) z) 6 := by
  letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  apply (IsPrimitiveRoot.iff_def _ _).mpr
  refine ⟨by rw [← map_pow, h.pow_eq_one, map_one], ?_⟩
  intro l hl
  apply h.dvd_of_pow_eq_one l
  by_contra hn
  have hd : z ^ l - 1 ∣ (6 : R) :=
    sub_one_dvd_natCast_of_pow_eq_one
      (by rw [← pow_mul, mul_comm, pow_mul, h.pow_eq_one, one_pow]) hn
  have hu : IsUnit (z ^ l - 1) := isUnit_of_dvd_unit hd hunit
  have hz : (Ideal.Quotient.mk I) (z ^ l - 1) = 0 := by
    simpa only [map_sub, map_pow, map_one, hl, sub_self]
  exact (hu.map (Ideal.Quotient.mk I)).ne_zero hz

theorem residue_six_isUnit (A : SArithmeticData F) : IsUnit (6 : A.R) := by
  let u : Fˣ := Units.mk0 (6 : F) (by norm_num)
  let su : A.U := ⟨u, fun v hv => (v.valuation_eq_one_iff_notMem (K := F)).mpr
    (fun h => hv (A.above_six v h))⟩
  convert (A.unitEquiv su).isUnit using 1
  apply Subtype.ext
  rfl

theorem residue_extendIdeal_ne_top (A : SArithmeticData F) (I : A.Exterior)
    (hI : I.val ≠ ⊤) : A.extendIdeal I ≠ ⊤ := by
  let T : A.Exterior := ⟨⊤, top_ne_bot, by simp⟩
  have hT : A.extendIdeal T = ⊤ := by
    exact Ideal.map_top _
  intro h
  apply hI
  have he : A.exteriorIdealEquiv I = A.exteriorIdealEquiv T := by
    apply Subtype.ext
    rw [A.exteriorIdealEquiv_apply, A.exteriorIdealEquiv_apply, h, hT]
  exact congrArg Subtype.val (A.exteriorIdealEquiv.injective he)

theorem exterior_sextic_primitive (A : SArithmeticData F) (I : A.Exterior)
    (hI : I.val ≠ ⊤) :
    IsPrimitiveRoot (Ideal.Quotient.mk (A.extendIdeal I)
      (algebraMap (𝓞 F) A.R (A.primitive_zeta12.toInteger ^ 2))) 6 := by
  apply primitiveRoot_mod_ideal_of_unit_order _ (residue_extendIdeal_ne_top A I hI)
  · apply IsPrimitiveRoot.map_of_injective
    · exact A.primitive_zeta12.toInteger_isPrimitiveRoot.pow
        (by decide) (by decide : 12 = 2 * 6)
    · intro x y h
      apply RingOfIntegers.ext
      exact congrArg (fun t : A.R => (t : F)) h
  · exact residue_six_isUnit A

theorem normalized_sextic_residue_family_unique (A : SArithmeticData F)
    {C D : A.SexticResidueFamily}
    (hC : A.IsNormalizedSexticResidueFamily C)
    (hD : A.IsNormalizedSexticResidueFamily D) : C = D := by
  apply residueFamily_ext_of_prime_values A hC.2.2 hD.2.2
  intro I v hI x
  let q := Ideal.Quotient.mk (A.extendIdeal I)
  by_cases hx : IsUnit (q x)
  · lift q x to (A.R ⧸ A.extendIdeal I)ˣ using hx with u hu
    obtain ⟨i, hi, hCi, hri⟩ := hC.2.1 I v hI u
    obtain ⟨j, hj, hDj, hrj⟩ := hD.2.1 I v hI u
    have hp := exterior_sextic_primitive A I (by rw [hI]; exact v.isPrime.ne_top)
    have hij : i = j := hp.pow_inj hi hj (by
      simpa only [← map_pow, pow_mul, map_pow] using hri.trans hrj.symm)
    unfold residueValue
    rw [← hu, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
    exact hCi.trans (by rw [hij]; exact hDj.symm)
  · unfold residueValue
    rw [MulChar.map_nonunit _ hx, MulChar.map_nonunit _ hx]

theorem existsUnique_normalized_sextic_residue_family (A : SArithmeticData F) :
    ∃! C : A.SexticResidueFamily, A.IsNormalizedSexticResidueFamily C := by
  have hprime := ResidueReciprocity.exists_exterior_prime_sextic_character A
  choose p hp6 hpn using hprime
  obtain ⟨C, h6, hp, hm⟩ :=
    ResidueReciprocity.extend_exterior_prime_sextic_characters A p hp6
  have hC : A.IsNormalizedSexticResidueFamily C := by
    refine ⟨h6, ?_, hm⟩
    intro I v hI x
    rw [hp I v hI]
    exact hpn I v hI x
  exact ⟨C, hC, fun D hD => A.normalized_sextic_residue_family_unique hD hC⟩

def sexticResidueFamily (A : SArithmeticData F) : A.SexticResidueFamily :=
  Classical.choose (A.existsUnique_normalized_sextic_residue_family.exists)

theorem sexticResidueFamily_normalized (A : SArithmeticData F) :
    A.IsNormalizedSexticResidueFamily A.sexticResidueFamily :=
  Classical.choose_spec (A.existsUnique_normalized_sextic_residue_family.exists)

def sexticResidue (A : SArithmeticData F) (I : A.Exterior) (x : A.R) : F :=
  A.residueValue A.sexticResidueFamily I x

theorem sexticResidue_neg_one (A : SArithmeticData F) (I : A.Exterior) :
    A.sexticResidue I (-1) = 1 := by
  let z : 𝓞 F := A.primitive_zeta12.toInteger
  have hz : z ^ 6 = -1 := by
    apply RingOfIntegers.ext
    change A.zeta12 ^ 6 = -1
    exact A.zeta12_pow_six
  let q := (Ideal.Quotient.mk (A.extendIdeal I)).comp (algebraMap (𝓞 F) A.R)
  let v := Units.map q.toMonoidHom
    ((A.primitive_zeta12.toInteger_isPrimitiveRoot.isUnit (by decide)).unit)
  have hv : (v : A.R ⧸ A.extendIdeal I) = q z := rfl
  have hpow : (MulChar.ofUnitHom (A.sexticResidueFamily I)) (q z) ^ 6 = 1 := by
    rw [← hv, MulChar.ofUnitHom_coe]
    exact congrArg Units.val (A.sexticResidueFamily_normalized.1 I v)
  have hn : q z ^ 6 = Ideal.Quotient.mk (A.extendIdeal I) (-1) := by
    rw [← map_pow, hz]
    simp only [RingHom.comp_apply, map_neg, map_one]
  unfold sexticResidue residueValue
  rw [← hn, map_pow, hpow]

def SexticReciprocitySpec (A : SArithmeticData F)
    (B : Subgroup A.V) (H : A.V → A.V → Fˣ) : Prop :=
  (∀ (I J : A.Exterior) (a b : A.R) (ua ub : Fˣ),
    A.Generates I a → A.Generates J b →
    (ua : F) = (a : F) → (ub : F) = (b : F) →
    A.IsAllowed B ua → A.IsAllowed B ub → I.val ⊔ J.val = ⊤ →
    A.sexticResidue I b = A.sexticResidue J a) ∧
  (∀ (I : A.Exterior) (a : A.R) (ua : Fˣ) (ε : A.U),
    A.Generates I a → (ua : F) = (a : F) → A.IsAllowed B ua →
    A.sexticResidue I (A.unitEquiv ε : A.R) =
      (H (A.sClass ε.val) (A.sClass ua) : Fˣ)) ∧
  (∀ (I J : A.Exterior) (a b : A.R) (ua ub : Fˣ) (ε : A.U),
    A.Generates I a → A.Generates J b →
    (ua : F) = (a : F) → (ub : F) = (b : F) →
    A.IsAllowed B ua → A.IsAllowed B ub →
    A.sexticResidue I ((A.unitEquiv ε : A.R) * b) =
      A.sexticResidue I (A.unitEquiv ε : A.R) * A.sexticResidue J a) ∧
  (∀ (I J : A.Exterior) (a b : A.R),
    A.Generates I a → A.Generates J b → I.val ⊔ J.val ≠ ⊤ →
      A.sexticResidue I b = 0 ∧ A.sexticResidue J a = 0)

theorem sexticResidue_sixth_unit_translate (A : SArithmeticData F)
    (I : A.Exterior) (x : A.R) (u : A.U) :
    A.sexticResidue I (x * (A.unitEquiv u : A.R) ^ 6) = A.sexticResidue I x := by
  let q := Ideal.Quotient.mk (A.extendIdeal I)
  let v := Units.map q.toMonoidHom (A.unitEquiv u)
  have hv : (v : A.R ⧸ A.extendIdeal I) = q (A.unitEquiv u : A.R) := rfl
  have hpow : (MulChar.ofUnitHom (A.sexticResidueFamily I)) (q (A.unitEquiv u : A.R)) ^ 6 = 1 := by
    rw [← hv, MulChar.ofUnitHom_coe]
    exact congrArg Units.val (A.sexticResidueFamily_normalized.1 I v)
  change (MulChar.ofUnitHom (A.sexticResidueFamily I)) (q (x * (A.unitEquiv u : A.R) ^ 6)) = _
  rw [map_mul, map_pow, map_mul, map_pow, hpow]
  exact _root_.mul_one _

end
end DedekindZetaZeroFree.SArithmeticData

end
