module

public import DedekindZetaZeroFree.Arithmetic.Units.SUnitLagrangianComplements
public import DedekindZetaZeroFree.Arithmetic.LocalFields.SexticHilbertPairing
public import DedekindZetaZeroFree.Arithmetic.Units.LocalPowerInjection
public import DedekindZetaZeroFree.Arithmetic.Units.SUnitPowerQuotientDimensions

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]
set_option maxHeartbeats 800000

section LinearAlgebra

variable (n : ℕ) (G C : Type*) [CommGroup G] [CommGroup C]
  [Module (ZMod n) (Additive G)]

def bihomBilinForm (H : G →* G →* C) (coeff : Additive C ≃+ ZMod n) :
    LinearMap.BilinForm (ZMod n) (Additive G) :=
  AddMonoidHom.toZModLinearMap n
    { toFun := fun x => AddMonoidHom.toZModLinearMap n
        (coeff.toAddMonoidHom.comp (H x.toMul).toAdditive)
      map_zero' := by
        ext y
        simp
      map_add' := by
        intro x z
        ext y
        simp }

@[simp] theorem bihomBilinForm_apply
    (H : G →* G →* C) (coeff : Additive C ≃+ ZMod n) (x y : Additive G) :
    bihomBilinForm n G C H coeff x y = coeff (Additive.ofMul (H x.toMul y.toMul)) := rfl

@[simp] theorem bihomBilinForm_eq_zero_iff
    (H : G →* G →* C) (coeff : Additive C ≃+ ZMod n) (x y : Additive G) :
    bihomBilinForm n G C H coeff x y = 0 ↔ H x.toMul y.toMul = 1 := by
  change coeff (Additive.ofMul (H x.toMul y.toMul)) = 0 ↔ _
  rw [← coeff.map_zero, coeff.injective.eq_iff]
  rfl

theorem bihomBilinForm_alternating
    (H : G →* G →* C) (coeff : Additive C ≃+ ZMod n)
    (hAlt : ∀ x : G, H x x = 1) :
    (bihomBilinForm n G C H coeff).IsAlt := by
  intro x
  exact (bihomBilinForm_eq_zero_iff n G C H coeff x x).2 (hAlt x.toMul)

theorem bihomBilinForm_nondegenerate
    (H : G →* G →* C) (coeff : Additive C ≃+ ZMod n)
    (hLeft : ∀ x : G, (∀ y : G, H x y = 1) → x = 1)
    (hRight : ∀ y : G, (∀ x : G, H x y = 1) → y = 1) :
    (bihomBilinForm n G C H coeff).Nondegenerate := by
  constructor
  · intro x hx
    change x.toMul = 1
    apply hLeft x.toMul
    intro y
    exact (bihomBilinForm_eq_zero_iff n G C H coeff x (Additive.ofMul y)).1
      (hx (Additive.ofMul y))
  · intro y hy
    change y.toMul = 1
    apply hRight y.toMul
    intro x
    exact (bihomBilinForm_eq_zero_iff n G C H coeff (Additive.ofMul x) y).1
      (hy (Additive.ofMul x))

theorem bihomBilinForm_isotropic_iff
    (H : G →* G →* C) (coeff : Additive C ≃+ ZMod n)
    (E : Submodule (ZMod n) (Additive G)) :
    E ≤ (bihomBilinForm n G C H coeff).orthogonal E ↔
      ∀ x ∈ E, ∀ y ∈ E, H x.toMul y.toMul = 1 := by
  constructor
  · intro h x hx y hy
    exact (bihomBilinForm_eq_zero_iff n G C H coeff x y).1 (h hy x hx)
  · intro h y hy x hx
    exact (bihomBilinForm_eq_zero_iff n G C H coeff x y).2 (h x hx y hy)

end LinearAlgebra

theorem complement_of_half_dimension
    (K M : Type*) [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (H : LinearMap.BilinForm K M)
    (hAlt : H.IsAlt) (hPerfect : H.Nondegenerate) (E : Submodule K M)
    (hIso : E ≤ H.orthogonal E)
    (hDim : Module.finrank K M = 2 * Module.finrank K E) :
    ∃ B : Submodule K M,
      IsCompl E B ∧ H.orthogonal B = B ∧
      (∀ x ∈ B, ∀ y ∈ B, H x y = 0) ∧
      (∀ v : M, ∃! p : E × B, (p.1 : M) + (p.2 : M) = v) := by
  apply DedekindZetaZeroFree.exists_lagrangian_complement K M H hAlt hPerfect E
  symm
  apply Submodule.eq_of_le_of_finrank_le hIso
  rw [H.finrank_orthogonal hPerfect E, hDim]
  omega

section SubgroupTransfer

variable (n : ℕ) (G : Type*) [CommGroup G] [Module (ZMod n) (Additive G)]

def bilinSubgroup (E : Submodule (ZMod n) (Additive G)) : Subgroup G :=
  AddSubgroup.toSubgroup' E.toAddSubgroup

@[simp] theorem mem_bilinSubgroup
    (E : Submodule (ZMod n) (Additive G)) (x : G) :
    x ∈ bilinSubgroup n G E ↔ Additive.ofMul x ∈ E := Iff.rfl

theorem bilinSubgroup_isCompl
    (E B : Submodule (ZMod n) (Additive G)) (hc : IsCompl E B) :
    IsCompl (bilinSubgroup n G E) (bilinSubgroup n G B) :=
  AddSubgroup.toSubgroup'.isCompl ((AddSubgroup.toZModSubmodule n).symm.isCompl hc)

theorem bilinSubgroup_unique_factorization
    (E B : Submodule (ZMod n) (Additive G)) (hc : IsCompl E B) :
    ∀ v : G, ∃! p : bilinSubgroup n G E × bilinSubgroup n G B,
      (p.1 : G) * (p.2 : G) = v := by
  intro v
  obtain ⟨p, hp, huniq⟩ := Submodule.existsUnique_add_of_isCompl_prod hc (Additive.ofMul v)
  refine ⟨(⟨p.1.val.toMul, p.1.property⟩, ⟨p.2.val.toMul, p.2.property⟩), ?_, ?_⟩
  · exact congrArg Additive.toMul hp
  · intro q hq
    have heq := huniq (⟨Additive.ofMul q.1.val, q.1.property⟩,
      ⟨Additive.ofMul q.2.val, q.2.property⟩) (congrArg Additive.ofMul hq)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun p : E × B => p.1.val.toMul) heq
    · apply Subtype.ext
      exact congrArg (fun p : E × B => p.2.val.toMul) heq

theorem bihom_exists_isotropic_complement
    [Fact (Nat.Prime n)] [FiniteDimensional (ZMod n) (Additive G)]
    (C : Type*) [CommGroup C] (H : G →* G →* C)
    (coeff : Additive C ≃+ ZMod n)
    (hAlt : ∀ x : G, H x x = 1)
    (hLeft : ∀ x : G, (∀ y : G, H x y = 1) → x = 1)
    (hRight : ∀ y : G, (∀ x : G, H x y = 1) → y = 1)
    (E : Subgroup G) (hIso : ∀ x ∈ E, ∀ y ∈ E, H x y = 1)
    (hDim : Module.finrank (ZMod n) (Additive G) =
      2 * Module.finrank (ZMod n) (AddSubgroup.toZModSubmodule n E.toAddSubgroup)) :
    ∃ B : Subgroup G, IsCompl E B ∧
      (∀ x ∈ B, ∀ y ∈ B, H x y = 1) ∧
      (∀ v : G, ∃! p : E × B, (p.1 : G) * (p.2 : G) = v) := by
  let E' := AddSubgroup.toZModSubmodule n E.toAddSubgroup
  have hi : E' ≤ (bihomBilinForm n G C H coeff).orthogonal E' := by
    apply (bihomBilinForm_isotropic_iff n G C H coeff E').2
    intro x hx y hy
    exact hIso x.toMul hx y.toMul hy
  obtain ⟨B, hc, _, hb, _⟩ := complement_of_half_dimension (ZMod n) (Additive G)
    (bihomBilinForm n G C H coeff) (bihomBilinForm_alternating n G C H coeff hAlt)
    (bihomBilinForm_nondegenerate n G C H coeff hLeft hRight) E' hi hDim
  refine ⟨bilinSubgroup n G B, bilinSubgroup_isCompl n G E' B hc, ?_,
    bilinSubgroup_unique_factorization n G E' B hc⟩
  intro x hx y hy
  exact (bihomBilinForm_eq_zero_iff n G C H coeff (Additive.ofMul x)
    (Additive.ofMul y)).1 (hb _ hx _ hy)

end SubgroupTransfer

 def rawPairing (A : SArithmeticData F) : A.G →* A.G →* Fˣ :=
  MonoidHom.mk' (fun x => MonoidHom.mk' (fun y => (A.H_S x y : Fˣ))
    (fun y z => congrArg Subtype.val (A.H_S_mul_right x y z))) (by
      intro x z
      apply MonoidHom.ext
      intro y
      exact congrArg Subtype.val (A.H_S_mul_left x z y))

 theorem rawPairing_ker (A : SArithmeticData F) :
    A.sixthPowers ≤ (rawPairing A).ker := by
  intro x hx
  obtain ⟨z, hz⟩ := (MonoidHom.mem_range.mp hx : ∃ z : A.G, (powMonoidHom 6) z = x)
  change rawPairing A x = 1
  rw [← hz, powMonoidHom_apply]
  apply MonoidHom.ext
  intro y
  change rawPairing A (z ^ 6) y = 1
  rw [map_pow]
  change (A.H_S z y : Fˣ) ^ 6 = 1
  exact (mem_rootsOfUnity 6 _).mp (A.H_S z y).property

 def leftPairing (A : SArithmeticData F) : A.V →* A.G →* Fˣ :=
  QuotientGroup.lift A.sixthPowers (rawPairing A) (rawPairing_ker A)

 theorem leftPairing_ker (A : SArithmeticData F) (v : A.V) :
    A.sixthPowers ≤ (leftPairing A v).ker := by
  induction v using QuotientGroup.induction_on with
  | H x =>
    intro y hy
    obtain ⟨z, hz⟩ := (MonoidHom.mem_range.mp hy : ∃ z : A.G, (powMonoidHom 6) z = y)
    change rawPairing A x y = 1
    rw [← hz, powMonoidHom_apply]
    rw [map_pow]
    change (A.H_S x z : Fˣ) ^ 6 = 1
    exact (mem_rootsOfUnity 6 _).mp (A.H_S x z).property

def actualQuotientPairing (A : SArithmeticData F) (v w : A.V) : Fˣ :=
  QuotientGroup.lift A.sixthPowers (leftPairing A v) (leftPairing_ker A v) w

@[simp] theorem actualQuotientPairing_mk (A : SArithmeticData F) (x y : A.G) :
    actualQuotientPairing A (QuotientGroup.mk' A.sixthPowers x)
      (QuotientGroup.mk' A.sixthPowers y) = (A.H_S x y : Fˣ) := rfl

theorem quotientUniqueMul_of_isCompl {G : Type*} [CommGroup G]
    (E B : Subgroup G) (hB : IsCompl E B)
    (v : G) : ∃! p : E × B, (p.1 : G) * (p.2 : G) = v := by
  have h : E.IsComplement' B := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hB.disjoint
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, ha, b, hb, hab⟩ := (Subgroup.mem_sup (s := E) (t := B) (x := x)).mp (show x ∈ E ⊔ B by rw [hB.sup_eq_top]; trivial)
    exact ⟨a, ha, b, hb, hab⟩
  exact h.existsUnique v

def pairToVnEquiv (A : SArithmeticData F) (n : ℕ) :
    A.LocalPowerClasses n ≃* Vn F A n where
  toFun x v := match v with
    | Sum.inl w => x.1 w
    | Sum.inr v => x.2 v
  invFun x := (fun w => x (Sum.inl w), fun v => x (Sum.inr v))
  left_inv x := rfl
  right_inv x := by funext v; cases v <;> rfl
  map_mul' x y := by funext v; cases v <;> rfl

def quotientToVnEquiv (A : SArithmeticData F) (n : ℕ) :
    PowerQuotient A.G n ≃* Vn F A n :=
  (A.localPowerQuotientEquiv n).trans (pairToVnEquiv A n)

@[simp] theorem quotientToVnEquiv_mk (A : SArithmeticData F) (n : ℕ) (x : A.G) :
    quotientToVnEquiv A n (QuotientGroup.mk' (powMonoidHom (α := A.G) n).range x) =
      (fun p => match p with
        | Sum.inl w => QuotientGroup.mk' (powMonoidHom (α := w.Completionˣ) n).range (x.1 w)
        | Sum.inr v => QuotientGroup.mk' (powMonoidHom (α := (v.val.adicCompletion F)ˣ) n).range (x.2 v)) := rfl

def unitPrimeHom (A : SArithmeticData F) (n : ℕ) : A.U →* Vn F A n :=
  (quotientToVnEquiv A n).toMonoidHom.comp
    ((QuotientGroup.mk' (powMonoidHom (α := A.G) n).range).comp
      (A.diagonal.comp A.U.subtype))

def unitQuotientPrimeHom (A : SArithmeticData F) (n : ℕ) :
    PowerQuotient A.U n →* Vn F A n :=
  QuotientGroup.lift _ (unitPrimeHom A n) (by
    rintro x ⟨y, rfl⟩
    change unitPrimeHom A n (y ^ n) = 1
    rw [map_pow]
    ext v
    exact powerQuotient_pow_eq_one _ _ _)

theorem unitQuotientPrimeHom_injective (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) (n : ℕ) (hn : n = 2 ∨ n = 3) :
    Function.Injective (unitQuotientPrimeHom A n) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro q hq
  change q = 1
  induction q using QuotientGroup.induction_on with
  | H ε =>
    have h : unitPrimeHom A n ε = 1 := hq
    have hinf (w : InfinitePlace F) : ∃ b : w.Completionˣ, b ^ n = (A.diagonal ε.val).1 w := by
      have hw := congrFun h (Sum.inl w)
      have hh : (QuotientGroup.mk' (powMonoidHom (α := w.Completionˣ) n).range) ((A.diagonal ε.val).1 w) = 1 := hw
      exact MonoidHom.mem_range.mp ((QuotientGroup.eq_one_iff _).mp hh)
    have hfin (v : {v // v ∈ A.Sf}) : ∃ b : (v.val.adicCompletion F)ˣ, b ^ n = (A.diagonal ε.val).2 v := by
      have hv := congrFun h (Sum.inr v)
      have hh : (QuotientGroup.mk' (powMonoidHom (α := (v.val.adicCompletion F)ˣ) n).range) ((A.diagonal ε.val).2 v) = 1 := hv
      exact MonoidHom.mem_range.mp ((QuotientGroup.eq_one_iff _).mp hh)
    have hmem : n ∈ ({2, 3, 6} : Finset ℕ) := by rcases hn with rfl | rfl <;> simp
    obtain ⟨b, hb⟩ := local_power_injection F A hCl n hmem ε ⟨hinf, hfin⟩
    exact (QuotientGroup.eq_one_iff ε).mpr (MonoidHom.mem_range.mpr ⟨b, hb⟩)

def primeUnitImage (A : SArithmeticData F) (n : ℕ) : Subgroup (Vn F A n) :=
  (unitQuotientPrimeHom A n).range

def primeUnitLinearMap (A : SArithmeticData F) (n : ℕ) :
    Additive (PowerQuotient A.U n) →ₗ[ZMod n] Additive (Vn F A n) :=
  (unitQuotientPrimeHom A n).toAdditive.toZModLinearMap n

lemma primeUnitImage_submodule_eq_range (A : SArithmeticData F) (n : ℕ) :
    AddSubgroup.toZModSubmodule n (primeUnitImage A n).toAddSubgroup =
      (primeUnitLinearMap A n).range := by
  ext x
  rfl

lemma primeUnitImage_finrank (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) (n : ℕ) (hn : n = 2 ∨ n = 3)
    [Fact (Nat.Prime n)] :
    Module.finrank (ZMod n) (AddSubgroup.toZModSubmodule n (primeUnitImage A n).toAddSubgroup) =
      InfinitePlace.nrComplexPlaces F + A.Sf.card := by
  rw [primeUnitImage_submodule_eq_range]
  have hInjective : Function.Injective (primeUnitLinearMap A n) :=
    unitQuotientPrimeHom_injective A hCl n hn
  rw [LinearMap.finrank_range_of_inj hInjective]
  let e := LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv A.U A.Rˣ n A.unitEquiv
  let el := addEquivToZModLinearEquiv n _ _ e.toAdditive
  exact el.finrank_eq.trans (finrank_sunitPowerQuotient F A n hn)

lemma primeUnitImage_halfdim (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) (n : ℕ) (hn : n = 2 ∨ n = 3)
    [Fact (Nat.Prime n)] :
    Module.finrank (ZMod n) (Additive (Vn F A n)) =
      2 * Module.finrank (ZMod n) (AddSubgroup.toZModSubmodule n (primeUnitImage A n).toAddSubgroup) := by
  rw [Vn_finrank_complex F A n hn, primeUnitImage_finrank A hCl n hn, Nat.add_comm]

lemma unitPrimeHom_isotropic (A : SArithmeticData F) (n : ℕ+) (hn : (n : ℕ) = 2 ∨ (n : ℕ) = 3)
    (a b : A.U) : A.H_Sn n (hn.elim Or.inl (fun h => Or.inr (Or.inl h)))
      (unitPrimeHom A n a) (unitPrimeHom A n b) = 1 := by
  let x : A.V := QuotientGroup.mk' A.sixthPowers (A.diagonal a.val)
  let y : A.V := QuotientGroup.mk' A.sixthPowers (A.diagonal b.val)
  have h : A.H_S6 x y = 1 := A.H_S_sunit_isotropy a b
  rcases hn with h2 | h3
  · have hn2 : n = 2 := Subtype.ext h2
    subst n
    apply Subtype.ext
    have ht := A.H_S6_cube_eq_quadratic x y
    have hh : (A.H_S6 x y : Fˣ) = 1 := congrArg Subtype.val h
    rw [hh, one_pow] at ht
    exact ht.symm
  · have hn3 : n = 3 := Subtype.ext h3
    subst n
    apply Subtype.ext
    have ht := A.H_S6_square_eq_cubic x y
    have hh : (A.H_S6 x y : Fˣ) = 1 := congrArg Subtype.val h
    rw [hh, one_pow] at ht
    exact ht.symm

lemma primeUnitImage_isotropic (A : SArithmeticData F) (n : ℕ+) (hn : (n : ℕ) = 2 ∨ (n : ℕ) = 3) :
    ∀ x ∈ primeUnitImage A n, ∀ y ∈ primeUnitImage A n,
      A.H_Sn n (hn.elim Or.inl (fun h => Or.inr (Or.inl h))) x y = 1 := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hy
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b => exact unitPrimeHom_isotropic A n hn a b

lemma actualPrime_skew (A : SArithmeticData F) (n : ℕ+) (hn : IsLocalRootOrder n)
    (x y : Vn F A n) : A.H_Sn n hn x y = (A.H_Sn n hn y x)⁻¹ := by
  rw [H_Sn_apply, H_Sn_apply, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro v _
  exact A.actualLocalHilbert_skew v.val n hn _ _

lemma actualPrime_left_nondegenerate (A : SArithmeticData F) (n : ℕ+)
    (hn : (n : ℕ) = 2 ∨ (n : ℕ) = 3) (x : Vn F A n)
    (hx : ∀ y, A.H_Sn n (hn.elim Or.inl (fun h => Or.inr (Or.inl h))) x y = 1) : x = 1 := by
  apply (A.H_Sn_perfect n hn).1
  apply MonoidHom.ext
  intro y
  simpa only [map_one, MonoidHom.one_apply] using hx y

lemma actualPrime_right_nondegenerate (A : SArithmeticData F) (n : ℕ+)
    (hn : (n : ℕ) = 2 ∨ (n : ℕ) = 3) (y : Vn F A n)
    (hy : ∀ x, A.H_Sn n (hn.elim Or.inl (fun h => Or.inr (Or.inl h))) x y = 1) : y = 1 := by
  apply actualPrime_left_nondegenerate A n hn y
  intro x
  rw [actualPrime_skew, hy, inv_one]

lemma actualPrimeComplement (A : SArithmeticData F) (hCl : Subsingleton (ClassGroup A.R))
    (n : ℕ+) (hn : (n : ℕ) = 2 ∨ (n : ℕ) = 3) [Fact (Nat.Prime (n : ℕ))] :
    ∃ B : Subgroup (Vn F A n), IsCompl (primeUnitImage A n) B ∧
      (∀ x ∈ B, ∀ y ∈ B, A.H_Sn n (hn.elim Or.inl (fun h => Or.inr (Or.inl h))) x y = 1) ∧
      (∀ v : Vn F A n, ∃! p : primeUnitImage A n × B, (p.1 : Vn F A n) * (p.2 : Vn F A n) = v) := by
  letI := Vn_module_finite F A n hn
  exact bihom_exists_isotropic_complement n (Vn F A n) (rootsOfUnity n F)
    (A.H_Sn n (hn.elim Or.inl (fun h => Or.inr (Or.inl h))))
    (A.hilbertRootsZModEquiv n (hn.elim Or.inl (fun h => Or.inr (Or.inl h)))).symm
    (A.H_Sn_alternating n hn) (actualPrime_left_nondegenerate A n hn)
    (actualPrime_right_nondegenerate A n hn) (primeUnitImage A n)
    (primeUnitImage_isotropic A n hn) (primeUnitImage_halfdim A hCl n hn)

lemma E_eq_prime_product (A : SArithmeticData F) :
    A.E = ((primeUnitImage A 2).prod (primeUnitImage A 3)).comap A.VnSixthCRT.toMonoidHom := by
  ext v
  constructor
  · intro hv
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hv
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨MonoidHom.mem_range.mpr ⟨QuotientGroup.mk' _ ⟨a, ha⟩, rfl⟩,
      MonoidHom.mem_range.mpr ⟨QuotientGroup.mk' _ ⟨a, ha⟩, rfl⟩⟩
  · intro hv
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hv.1
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hv.2
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        change unitPrimeHom A 2 a = (A.VnSixthCRT v).1 at ha
        change unitPrimeHom A 3 b = (A.VnSixthCRT v).2 at hb
        have h2 (q : Vn F A 2) : q ^ 2 = 1 := by
          ext p; exact powerQuotient_pow_eq_one _ _ _
        have h3 (q : Vn F A 3) : q ^ 3 = 1 := by
          ext p; exact powerQuotient_pow_eq_one _ _ _
        let c := a ^ 3 * b ^ 4
        have hc : QuotientGroup.mk' A.sixthPowers (A.diagonal c.val) = v := by
          apply A.VnSixthCRT.injective
          apply Prod.ext
          · change unitPrimeHom A 2 c = (A.VnSixthCRT v).1
            rw [map_mul, map_pow, map_pow, ha,
              show (unitPrimeHom A 2 b) ^ 4 = 1 by rw [show 4 = 2 * 2 from rfl, pow_mul, h2],
              mul_one, pow_succ, h2, one_mul]
          · change unitPrimeHom A 3 c = (A.VnSixthCRT v).2
            rw [map_mul, map_pow, map_pow, hb, h3, one_mul, pow_succ, h3, one_mul]
        rw [← hc]
        exact Subgroup.mem_map.mpr ⟨A.diagonal c.val,
          Subgroup.mem_map.mpr ⟨c.val, c.property, rfl⟩, rfl⟩

lemma subgroupProd_isCompl {G H : Type*} [CommGroup G] [CommGroup H]
    (E B : Subgroup G) (D C : Subgroup H) (hEB : IsCompl E B) (hDC : IsCompl D C) :
    IsCompl (E.prod D) (B.prod C) := by
  constructor
  · apply Subgroup.disjoint_def.mpr
    intro x hx hy
    exact Prod.ext (Subgroup.disjoint_def.mp hEB.disjoint hx.1 hy.1)
      (Subgroup.disjoint_def.mp hDC.disjoint hx.2 hy.2)
  · apply codisjoint_iff.mpr
    apply top_unique
    intro x _
    obtain ⟨a, ha, b, hb, hab⟩ := (Subgroup.mem_sup (s := E) (t := B) (x := x.1)).mp (by rw [hEB.sup_eq_top]; trivial)
    obtain ⟨c, hc, d, hd, hcd⟩ := (Subgroup.mem_sup (s := D) (t := C) (x := x.2)).mp (by rw [hDC.sup_eq_top]; trivial)
    exact Subgroup.mem_sup.mpr ⟨(a, c), ⟨ha, hc⟩, (b, d), ⟨hb, hd⟩, Prod.ext hab hcd⟩

lemma actualQuotientPairing_eq_H_S6 (A : SArithmeticData F) (x y : A.V) :
    actualQuotientPairing A x y = (A.H_S6 x y : Fˣ) := by
  induction x using QuotientGroup.induction_on with
  | H x =>
    induction y using QuotientGroup.induction_on with
    | H y => rfl

theorem actualComplement (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) :
    ∃ (H : A.V → A.V → Fˣ) (B : Subgroup A.V),
      (∀ x y : A.G, H (QuotientGroup.mk' A.sixthPowers x)
        (QuotientGroup.mk' A.sixthPowers y) = (A.H_S x y : Fˣ)) ∧
        A.IsSUnitIsotropicComplement H B := by
  obtain ⟨B₂, h₂, hi₂, _⟩ := actualPrimeComplement A hCl 2 (Or.inl rfl)
  obtain ⟨B₃, h₃, hi₃, _⟩ := actualPrimeComplement A hCl 3 (Or.inr rfl)
  let B := (B₂.prod B₃).comap A.VnSixthCRT.toMonoidHom
  have hc : IsCompl A.E B := by
    rw [E_eq_prime_product]
    exact A.VnSixthCRT.comapSubgroup.isCompl
      (subgroupProd_isCompl _ _ _ _ h₂ h₃)
  refine ⟨actualQuotientPairing A, B, actualQuotientPairing_mk A, hc, ?_, quotientUniqueMul_of_isCompl (G := A.V) A.E B hc⟩
  intro x hx y hy
  rw [actualQuotientPairing_eq_H_S6]
  have hpair := A.H_S6_coefficientCRT x y
  have h2 := hi₂ (A.VnSixthCRT x).1 hx.1 (A.VnSixthCRT y).1 hy.1
  have h3 := hi₃ (A.VnSixthCRT x).2 hx.2 (A.VnSixthCRT y).2 hy.2
  have hsym : hilbertRootsSixthCRT (A.H_S6 x y) = 1 := by
    rw [hpair, h2, h3]
    rfl
  have hh : A.H_S6 x y = 1 := hilbertRootsSixthCRT.injective (hsym.trans (map_one _).symm)
  exact congrArg Subtype.val hh

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection
