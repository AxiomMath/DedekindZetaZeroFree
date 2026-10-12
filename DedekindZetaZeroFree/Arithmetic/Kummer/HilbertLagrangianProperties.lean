module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.SexticHilbertPairing
public import DedekindZetaZeroFree.Arithmetic.Units.SUnitLagrangianComplements
public import DedekindZetaZeroFree.Arithmetic.Units.SUnitPowerQuotientDimensions
public import DedekindZetaZeroFree.Arithmetic.Units.LocalPowerInjection

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.ArithmeticContext
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]

private lemma selfOrth_of_split {G C : Type*} [CommGroup G] [CommGroup C]
    (P : G →* G →* C) (L M : Subgroup G)
    (hL : ∀ x ∈ L, ∀ y ∈ L, P x y = 1)
    (hM : ∀ x ∈ M, ∀ y ∈ M, P x y = 1)
    (hsplit : ∀ x : G, ∃ e : L, ∃ b : M, (e : G) * b = x)
    (hn : ∀ x : G, (∀ y, P y x = 1) → x = 1) :
    ∀ x : G, x ∈ L ↔ ∀ y ∈ L, P y x = 1 := by
  intro x
  constructor
  · intro hx y hy; exact hL y hy x hx
  · intro hx
    obtain ⟨e, b, rfl⟩ := hsplit x
    have hb (y : G) (hy : y ∈ L) : P y (b : G) = 1 := by
      have := hx y hy
      simpa only [map_mul, hL y hy e e.property, one_mul] using this
    have hb1 : (b : G) = 1 := hn b (by
      intro y
      obtain ⟨u, v, rfl⟩ := hsplit y
      change P ((u : G) * v) (b : G) = 1
      rw [map_mul, MonoidHom.mul_apply, hb u u.property, hM v v.property b b.property,
        one_mul])
    simpa [hb1] using e.property

private lemma primary_mem (A : SArithmeticData F) (ℓ : ℕ) (L : Subgroup A.V)
    (x : A.PrimarySpace ℓ) : x ∈ A.primarySubspace ℓ L ↔ x.val.toMul ∈ L := Iff.rfl

private lemma primary_pow (A : SArithmeticData F) (ℓ : ℕ) (x : A.PrimarySpace ℓ) :
    x.val.toMul ^ ℓ = 1 := by
  have hx : (ℓ : ℤ) • x.val = 0 := x.property
  change Additive.ofMul (x.val.toMul ^ (ℓ : ℤ)) = 0 at hx
  have h := congrArg Additive.toMul hx
  change x.val.toMul ^ (ℓ : ℤ) = 1 at h
  simpa only [zpow_natCast] using h

private lemma primary_mk (A : SArithmeticData F) (ℓ : ℕ) (x : A.V) (hx : x ^ ℓ = 1) :
    Additive.ofMul x ∈ A.PrimarySpace ℓ := by
  change (ℓ : ℤ) • Additive.ofMul x = 0
  change Additive.ofMul (x ^ (ℓ : ℤ)) = 0
  apply Additive.toMul.injective
  change x ^ (ℓ : ℤ) = 1
  simpa only [zpow_natCast] using hx

private lemma primary_selfOrth (A : SArithmeticData F) (P : A.V →* A.V →* Fˣ)
    (L : Subgroup A.V) (hL : A.IsSelfOrthogonal (fun x y => P x y) L)
    (ℓ k t : ℕ) (hk : k = 1 + t * ℓ) (h6 : 6 ∣ k * ℓ) :
    ∀ x : A.PrimarySpace ℓ, x ∈ A.primarySubspace ℓ L ↔
      ∀ y : A.PrimarySpace ℓ, y ∈ A.primarySubspace ℓ L → P y.val.toMul x.val.toMul = 1 := by
  intro x
  rw [primary_mem]
  constructor
  · intro hx y hy; exact (hL x.val.toMul).mp hx y.val.toMul ((primary_mem A ℓ L y).mp hy)
  · intro hx
    apply (hL x.val.toMul).mpr
    intro y hy
    have hyk : (y ^ k) ^ ℓ = 1 := by
      rw [← pow_mul]
      obtain ⟨d, hd⟩ := h6
      rw [hd, pow_mul, powerQuotient_pow_eq_one A.G 6 y, one_pow]
    let z : A.PrimarySpace ℓ := ⟨Additive.ofMul (y ^ k), primary_mk A ℓ _ hyk⟩
    have hz : z ∈ A.primarySubspace ℓ L := (primary_mem A ℓ L z).mpr (L.pow_mem hy k)
    have hzP : P y x.val.toMul ^ k = 1 := by
      have h := hx z hz
      change P (y ^ k) x.val.toMul = 1 at h
      simpa only [map_pow, MonoidHom.pow_apply] using h
    have hp : P y x.val.toMul ^ ℓ = 1 := by
      rw [← map_pow, primary_pow, map_one]
    rw [hk, pow_add, pow_one, Nat.mul_comm t ℓ, pow_mul, hp, one_pow, mul_one] at hzP
    exact hzP

private lemma primary_compl (A : SArithmeticData F) (L M : Subgroup A.V)
    (hc : IsCompl L M) (ℓ : ℕ)
    (hsplit : ∀ x : A.V, ∃ e : L, ∃ b : M, (e : A.V) * b = x) :
    IsCompl (A.primarySubspace ℓ L) (A.primarySubspace ℓ M) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hy
    apply Subtype.ext
    apply Additive.toMul.injective
    change x.val.toMul = 1
    exact Subgroup.disjoint_def.mp hc.disjoint
      ((primary_mem A ℓ L x).mp hx) ((primary_mem A ℓ M x).mp hy)
  · apply codisjoint_iff.mpr
    rw [Submodule.eq_top_iff']
    intro x
    obtain ⟨e, b, he⟩ := hsplit x.val.toMul
    have hp : (e : A.V) ^ ℓ * (b : A.V) ^ ℓ = 1 := by
      calc
        (e : A.V) ^ ℓ * (b : A.V) ^ ℓ = ((e : A.V) * (b : A.V)) ^ ℓ :=
          (mul_pow (e : A.V) (b : A.V) ℓ).symm
        _ = x.val.toMul ^ ℓ := congrArg (fun a : A.V => a ^ ℓ) he
        _ = 1 := primary_pow A ℓ x
    have hep : (e : A.V) ^ ℓ = 1 := by
      apply Subgroup.disjoint_def.mp hc.disjoint (L.pow_mem e.property ℓ)
      have heq : (e : A.V) ^ ℓ = ((b : A.V) ^ ℓ)⁻¹ := (eq_inv_iff_mul_eq_one).mpr hp
      rw [heq]
      exact M.inv_mem (M.pow_mem b.property ℓ)
    have hbp : (b : A.V) ^ ℓ = 1 := by
      rw [hep] at hp
      exact (one_mul ((b : A.V) ^ ℓ)).symm.trans hp
    let u : A.PrimarySpace ℓ := ⟨Additive.ofMul (e : A.V), primary_mk A ℓ _ hep⟩
    let v : A.PrimarySpace ℓ := ⟨Additive.ofMul (b : A.V), primary_mk A ℓ _ hbp⟩
    have huv : u + v = x := by
      apply Subtype.ext
      apply Additive.toMul.injective
      exact he
    rw [← huv]
    exact Submodule.add_mem_sup ((primary_mem A ℓ L u).mpr e.property)
      ((primary_mem A ℓ M v).mpr b.property)

theorem actual_hilbert_lagrangian_properties (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R))
    (H : A.V → A.V → Fˣ) (B : Subgroup A.V)
    (hActual : ∀ x y : A.G,
      H (QuotientGroup.mk' A.sixthPowers x) (QuotientGroup.mk' A.sixthPowers y) =
        (A.H_S x y : Fˣ))
    (hB : A.IsSUnitIsotropicComplement H B) :
    A.IsSelfOrthogonal H A.E ∧
      A.PrimaryLagrangianComplementSpec H B 2 ∧
      A.PrimaryLagrangianComplementSpec H B 3 := by
  let P : A.V →* A.V →* Fˣ :=
    { toFun := fun x => (rootsOfUnity 6 F).subtype.comp (A.H_S6 x)
      map_one' := by ext y; simp
      map_mul' := by intro x z; ext y; simp [map_mul, MonoidHom.mul_apply] }
  have hP (x y : A.V) : H x y = P x y := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective A.sixthPowers x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective A.sixthPowers y
    exact hActual a b
  have hswap (x y : A.V) : P x y = (P y x)⁻¹ := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective A.sixthPowers x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective A.sixthPowers y
    exact congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ)) (A.H_S_skew a b)
  have hn (x : A.V) (hx : ∀ y, P y x = 1) : x = 1 := by
    apply A.H_S6_perfect.1
    apply MonoidHom.ext
    intro y
    apply Subtype.ext
    have hxy : P x y = 1 := by rw [hswap, hx, inv_one]
    change (A.H_S6 x y : Fˣ) = (A.H_S6 1 y : Fˣ)
    change (A.H_S6 x y : Fˣ) = 1 at hxy
    simpa only [map_one, MonoidHom.one_apply, OneMemClass.coe_one] using hxy
  have hE : ∀ x ∈ A.E, ∀ y ∈ A.E, P x y = 1 := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hb
    exact congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ)) (A.H_S_sunit_isotropy ⟨u, hu⟩ ⟨v, hv⟩)
  have hBi : ∀ x ∈ B, ∀ y ∈ B, P x y = 1 := by
    intro x hx y hy
    rw [← hP]
    exact hB.2.1 x hx y hy
  have hs : ∀ x : A.V, ∃ e : A.E, ∃ b : B, (e : A.V) * b = x := by
    intro x
    obtain ⟨p, hp, _⟩ := hB.2.2 x
    exact ⟨p.1, p.2, hp⟩
  have hs' : ∀ x : A.V, ∃ b : B, ∃ e : A.E, (b : A.V) * e = x := by
    intro x
    obtain ⟨e, b, hb⟩ := hs x
    refine ⟨b, e, ?_⟩
    calc
      (b : A.V) * (e : A.V) = (e : A.V) * (b : A.V) := mul_comm (b : A.V) (e : A.V)
      _ = x := hb
  have hEL : A.IsSelfOrthogonal (fun x y => P x y) A.E := by
    unfold SArithmeticData.IsSelfOrthogonal
    exact selfOrth_of_split (G := A.V) (C := Fˣ) P A.E B hE hBi hs hn
  have hBL : A.IsSelfOrthogonal (fun x y => P x y) B := by
    unfold SArithmeticData.IsSelfOrthogonal
    exact selfOrth_of_split (G := A.V) (C := Fˣ) P B A.E hBi hE hs' hn
  have hprim (ℓ k t : ℕ) (hk : k = 1 + t * ℓ) (h6 : 6 ∣ k * ℓ) :
      A.PrimaryLagrangianComplementSpec H B ℓ := by
    refine ⟨primary_compl A A.E B hB.1 ℓ hs, ?_, ?_⟩
    · simpa only [hP] using primary_selfOrth A P A.E hEL ℓ k t hk h6
    · simpa only [hP] using primary_selfOrth A P B hBL ℓ k t hk h6
  refine ⟨?_, hprim 2 3 1 (by decide) (by decide), hprim 3 4 1 (by decide) (by decide)⟩
  intro x
  simpa only [hP] using hEL x

end
end DedekindZetaZeroFree.ArithmeticContext
