module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree.FinitePolarization

open scoped Classical commutatorElement

def IsIsotropic {V : Type*} [CommGroup V]
    (b : V →* (V →* rootsOfUnity 3 ℂ)) (L : Subgroup V) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, b x y = 1

def IsMaximalIsotropic {V : Type*} [CommGroup V]
    (b : V →* (V →* rootsOfUnity 3 ℂ)) (L : Subgroup V) : Prop :=
  IsIsotropic b L ∧ ∀ M : Subgroup V, L ≤ M → IsIsotropic b M → M = L

def orthogonal {V : Type*} [CommGroup V] (b : V →* (V →* rootsOfUnity 3 ℂ))
    (L : Subgroup V) : Subgroup V :=
  ⨅ l : L, (b (l : V)).ker

lemma mem_orthogonal {V : Type*} [CommGroup V] {b : V →* (V →* rootsOfUnity 3 ℂ)}
    {L : Subgroup V} {x : V} : x ∈ orthogonal b L ↔ ∀ l : L, b (l : V) x = 1 := by
  simp [orthogonal]

lemma pairing_swap_inv {V : Type*} [CommGroup V] (b : V →* (V →* rootsOfUnity 3 ℂ))
    (halt : ∀ v : V, b v v = 1) (x y : V) : b y x = (b x y)⁻¹ := by
  have h := halt (y * x)
  simp only [map_mul, MonoidHom.mul_apply] at h
  simp only [halt, one_mul, mul_one] at h
  exact eq_inv_of_mul_eq_one_right h

theorem orthogonal_eq_of_isMaximalIsotropic {V : Type*} [CommGroup V]
    (b : V →* (V →* rootsOfUnity 3 ℂ)) (halt : ∀ v : V, b v v = 1) {L : Subgroup V}
    (hL : IsMaximalIsotropic b L) : orthogonal b L = L := by
  refine le_antisymm ?_ ?_
  · intro x hx
    by_contra hxL
    have hx' : ∀ l : L, b (l : V) x = 1 := mem_orthogonal.mp hx
    have hxiso : ∀ l ∈ L, ∀ n : ℤ, b l (x ^ n) = 1 := by
      intro l hl n
      rw [MonoidHom.map_zpow, hx' ⟨l, hl⟩, one_zpow]
    have h1 : ∀ m ∈ L, ∀ n : ℤ, b (x ^ n) m = 1 := by
      intro m hm n
      rw [pairing_swap_inv b halt m (x ^ n), hxiso m hm n, inv_one]
    have h2 : ∀ n p : ℤ, b (x ^ n) (x ^ p) = 1 := by
      intro n p
      rw [MonoidHom.map_zpow]
      have : b (x ^ n) x = 1 := by
        rw [pairing_swap_inv b halt x (x ^ n), MonoidHom.map_zpow, halt x, one_zpow, inv_one]
      rw [this, one_zpow]
    have hiso : IsIsotropic b (L ⊔ Subgroup.zpowers x) := by
      intro u hu v hv
      rw [Subgroup.mem_sup] at hu hv
      obtain ⟨l, hl, u', hu', rfl⟩ := hu
      obtain ⟨m, hm, v', hv', rfl⟩ := hv
      rw [Subgroup.mem_zpowers_iff] at hu' hv'
      obtain ⟨n, rfl⟩ := hu'
      obtain ⟨p, rfl⟩ := hv'
      simp only [map_mul, MonoidHom.mul_apply, hL.1 l hl m hm, hxiso l hl p, h1 m hm n, h2 n p,
        mul_one, one_mul]
    have hLM : L ⊔ Subgroup.zpowers x = L := hL.2 _ le_sup_left hiso
    exact hxL (hLM ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  · intro x hx
    rw [mem_orthogonal]
    intro l
    exact hL.1 (l : V) l.2 x hx

def preimageProjection {H V : Type*} [Group H] [CommGroup V]
    (π : H →* V) (A : Subgroup V) : A.comap π →* A where
  toFun a := ⟨π a, a.property⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

def inducedSpace {H : Type*} [Group H] (A : Subgroup H) (χ : A →* ℂˣ) :
    Submodule ℂ (H → ℂ) where
  carrier := {f | ∀ a : A, ∀ g : H, f ((a : H) * g) = (χ a : ℂ) * f g}
  zero_mem' := by simp
  add_mem' := by
    intro f h hf hh a g
    simp only [Pi.add_apply, hf a g, hh a g, mul_add]
  smul_mem' := by
    intro c f hf a g
    simp only [Pi.smul_apply, smul_eq_mul, hf a g]
    ring

end DedekindZetaZeroFree.FinitePolarization

section

namespace DedekindZetaZeroFree.FinitePolarization

open scoped Classical commutatorElement

structure HeisenbergData (H V : Type*) [Group H] [CommGroup V] [Fintype V] where
  C : Subgroup H
  central : C ≤ Subgroup.center H
  π : H →* V
  quotient_surjective : Function.Surjective π
  quotient_kernel : π.ker = C
  exponent_three : ∀ v : V, v ^ 3 = 1
  ω : C →* ℂˣ
  faithful : Function.Injective ω
  pairing : V →* (V →* rootsOfUnity 3 ℂ)
  alternating : ∀ v : V, pairing v v = 1
  perfect : Function.Bijective pairing
  commutator_mem : ∀ x y : H, ⁅x, y⁆ ∈ C
  commutator_pairing : ∀ x y : H,
    ω ⟨⁅x, y⁆, commutator_mem x y⟩ = (pairing (π x) (π y) : ℂˣ)

structure PolarizationData {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) where
  L : Subgroup V
  N : Subgroup V
  maximal_L : IsMaximalIsotropic D.pairing L
  maximal_N : IsMaximalIsotropic D.pairing N
  χL : L.comap D.π →* ℂˣ
  χN : N.comap D.π →* ℂˣ
  central_L : ∀ a : L.comap D.π, ∀ ha : (a : H) ∈ D.C,
    χL a = D.ω ⟨(a : H), ha⟩
  central_N : ∀ a : N.comap D.π, ∀ ha : (a : H) ∈ D.C,
    χN a = D.ω ⟨(a : H), ha⟩
  agree_on_intersection : ∀ a : H, ∀ hL : D.π a ∈ L, ∀ hN : D.π a ∈ N,
    χL ⟨a, hL⟩ = χN ⟨a, hN⟩

abbrev PolarizationData.intersection {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    {D : HeisenbergData H V} (T : PolarizationData D) : Subgroup V := T.L ⊓ T.N

abbrev PolarizationIndex {V : Type*} [CommGroup V] (A J : Subgroup V) :=
  A ⧸ J.subgroupOf A

structure LiftSection {H V : Type*} [Group H] [CommGroup V]
    (π : H →* V) (A J : Subgroup V) where
  lift : PolarizationIndex A J → A.comap π
  represents : ∀ i : PolarizationIndex A J,
    QuotientGroup.mk (preimageProjection π A (lift i)) = i

theorem liftSection_nonempty {H V : Type*} [Group H] [CommGroup V]
    (π : H →* V) (hπ : Function.Surjective π) (A J : Subgroup V) :
    Nonempty (LiftSection π A J) := by
  classical
  have hproj : Function.Surjective (preimageProjection π A) := by
    intro a
    obtain ⟨h, hh⟩ := hπ (a : V)
    exact ⟨⟨h, by rw [Subgroup.mem_comap]; exact hh ▸ a.2⟩, by ext; exact hh⟩
  have hsurj : Function.Surjective
      (fun a : A.comap π => QuotientGroup.mk' (J.subgroupOf A) (preimageProjection π A a)) :=
    (QuotientGroup.mk'_surjective (J.subgroupOf A)).comp hproj
  exact ⟨{ lift := fun i => Function.surjInv hsurj i,
           represents := fun i => by
             simpa [QuotientGroup.coe_mk'] using Function.surjInv_eq hsurj i }⟩

private lemma term_congr {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) (A B J : Subgroup V) (hJ : J = A ⊓ B)
    (χA : A.comap D.π →* ℂˣ) (χB : B.comap D.π →* ℂˣ)
    (hagree : ∀ a : H, ∀ hA : D.π a ∈ A, ∀ hB : D.π a ∈ B,
      χA ⟨a, hA⟩ = χB ⟨a, hB⟩)
    (f : inducedSpace (B.comap D.π) χB) (g : H) {x y : A.comap D.π}
    (h : QuotientGroup.mk' (J.subgroupOf A) (preimageProjection D.π A x) =
      QuotientGroup.mk' (J.subgroupOf A) (preimageProjection D.π A y)) :
    (χA y : ℂ)⁻¹ * (f : H → ℂ) ((y : H) * g) =
      (χA x : ℂ)⁻¹ * (f : H → ℂ) ((x : H) * g) := by
  rw [QuotientGroup.mk'_eq_mk'] at h
  obtain ⟨z, hz, hzy⟩ := h
  rw [Subgroup.mem_subgroupOf] at hz
  have hzAB : (z : V) ∈ A ⊓ B := by rw [← hJ]; exact hz
  obtain ⟨hzA, hzB⟩ := hzAB
  have hzv : (D.π (x : H)) * (z : V) = D.π (y : H) := by
    have h' := congrArg Subtype.val hzy
    simpa [preimageProjection] using h'
  set c : H := (y : H) * (x : H)⁻¹ with hc
  have hpc : D.π c = (z : V) := by
    rw [hc, map_mul, map_inv, ← hzv]
    rw [mul_comm (D.π (x : H)) (z : V), mul_assoc, mul_inv_cancel, mul_one]
  have hcA : D.π c ∈ A := by rw [hpc]; exact hzA
  have hcB : D.π c ∈ B := by rw [hpc]; exact hzB
  set cL : A.comap D.π := ⟨c, hcA⟩ with hcLdef
  set cN : B.comap D.π := ⟨c, hcB⟩ with hcNdef
  have hcLval : (cL : H) = c := by rw [hcLdef]
  have hcNval : (cN : H) = c := by rw [hcNdef]
  have hag : χA cL = χB cN := by
    rw [hcLdef, hcNdef]
    exact hagree c hcA hcB
  have hyx : (y : H) = c * (x : H) := by rw [hc]; group
  have hchi : χA y = χA cL * χA x := by
    have hy : y = cL * x := by
      apply Subtype.ext
      show (y : H) = (cL : H) * (x : H)
      rw [hcLval]
      exact hyx
    rw [hy, map_mul]
  have hf : (f : H → ℂ) ((y : H) * g) = (χB cN : ℂ) * (f : H → ℂ) ((x : H) * g) := by
    have h := f.property cN ((x : H) * g)
    rw [hcNval, ← mul_assoc, ← hyx] at h
    exact h
  rw [hchi, hf]
  have hvu : (↑(χA cL * χA x) : ℂ) = (χA cL : ℂ) * (χA x : ℂ) := by simp
  rw [hvu, show (χB cN : ℂ) = (χA cL : ℂ) from by rw [hag]]
  have hne : (χA cL : ℂ) ≠ 0 := Units.ne_zero _
  have hne2 : (χA x : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

noncomputable def countingAverage {H V : Type*} [Group H] [CommGroup V]
    [Fintype V] (π : H →* V) (A J : Subgroup V) (χ : A.comap π →* ℂˣ)
    (r : LiftSection π A J) (f : H → ℂ) (g : H) : ℂ :=
  ∑ i : PolarizationIndex A J, (χ (r.lift i) : ℂ)⁻¹ * f ((r.lift i : H) * g)

noncomputable def probabilityAverage {H V : Type*} [Group H] [CommGroup V]
    [Fintype V] (π : H →* V) (A J : Subgroup V) (χ : A.comap π →* ℂˣ)
    (r : LiftSection π A J) (f : H → ℂ) (g : H) : ℂ :=
  (Fintype.card (PolarizationIndex A J) : ℂ)⁻¹ *
    ∑ i : PolarizationIndex A J, (χ (r.lift i) : ℂ)⁻¹ * f ((r.lift i : H) * g)

private theorem average_left_covariant {H V : Type*} [Group H] [CommGroup V]
    [Fintype V] (D : HeisenbergData H V) (A B J : Subgroup V) (hJ : J = A ⊓ B)
    (χA : A.comap D.π →* ℂˣ) (χB : B.comap D.π →* ℂˣ)
    (hagree : ∀ a : H, ∀ hA : D.π a ∈ A, ∀ hB : D.π a ∈ B,
      χA ⟨a, hA⟩ = χB ⟨a, hB⟩)
    (r : LiftSection D.π A J) (f : inducedSpace (B.comap D.π) χB)
    (a : A.comap D.π) (g : H) :
    countingAverage D.π A J χA r f ((a : H) * g) =
      (χA a : ℂ) * countingAverage D.π A J χA r f g := by
  classical
  let q := QuotientGroup.mk' (J.subgroupOf A) (preimageProjection D.π A a)
  let e : PolarizationIndex A J ≃ PolarizationIndex A J := Equiv.mulRight q
  unfold countingAverage
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv e
  intro i
  have he : QuotientGroup.mk' (J.subgroupOf A)
      (preimageProjection D.π A (r.lift i * a)) =
      QuotientGroup.mk' (J.subgroupOf A) (preimageProjection D.π A (r.lift (e i))) := by
    simp only [map_mul, QuotientGroup.coe_mk', r.represents]
    rfl
  have ht := term_congr D A B J hJ χA χB hagree f g he
  simp only [map_mul, Units.val_mul, Subgroup.coe_mul] at ht
  simp only [← mul_assoc]
  rw [mul_assoc (χA a : ℂ), ht]
  have ha : (χA a : ℂ) ≠ 0 := Units.ne_zero _
  have hi : (χA (r.lift i) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

theorem counting_left_covariant {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) (T : PolarizationData D)
    (r : LiftSection D.π T.L T.intersection)
    (f : inducedSpace (T.N.comap D.π) T.χN) (a : T.L.comap D.π) (g : H) :
    countingAverage D.π T.L T.intersection T.χL r f ((a : H) * g) =
      (T.χL a : ℂ) * countingAverage D.π T.L T.intersection T.χL r f g := by
  exact average_left_covariant D T.L T.N T.intersection rfl T.χL T.χN
    T.agree_on_intersection r f a g

theorem probability_left_covariant {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) (T : PolarizationData D)
    (s : LiftSection D.π T.N T.intersection)
    (h : inducedSpace (T.L.comap D.π) T.χL) (a : T.N.comap D.π) (g : H) :
    probabilityAverage D.π T.N T.intersection T.χN s h ((a : H) * g) =
      (T.χN a : ℂ) * probabilityAverage D.π T.N T.intersection T.χN s h g := by
  change _ * countingAverage D.π T.N T.intersection T.χN s h ((a : H) * g) = _
  rw [average_left_covariant D T.N T.L T.intersection
    (by simp [PolarizationData.intersection, inf_comm]) T.χN T.χL
    (fun a hN hL => (T.agree_on_intersection a hL hN).symm) s h a g]
  unfold probabilityAverage countingAverage
  ring

noncomputable def P {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) (T : PolarizationData D)
    (r : LiftSection D.π T.L T.intersection)
    (f : inducedSpace (T.N.comap D.π) T.χN) : inducedSpace (T.L.comap D.π) T.χL :=
  ⟨countingAverage D.π T.L T.intersection T.χL r f,
    counting_left_covariant D T r f⟩

noncomputable def Q {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) (T : PolarizationData D)
    (s : LiftSection D.π T.N T.intersection)
    (h : inducedSpace (T.L.comap D.π) T.χL) : inducedSpace (T.N.comap D.π) T.χN :=
  ⟨probabilityAverage D.π T.N T.intersection T.χN s h,
    probability_left_covariant D T s h⟩

private lemma pairing_flip {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) (x y : V) : D.pairing x y * D.pairing y x = 1 := by
  have h := D.alternating (x * y)
  simp only [map_mul, MonoidHom.mul_apply, D.alternating, one_mul, mul_one] at h
  simpa only [mul_comm] using h
private lemma maximal_orthogonal {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) (A : Subgroup V) (hA : IsMaximalIsotropic D.pairing A)
    (v : V) (hv : ∀ a ∈ A, D.pairing v a = 1) : v ∈ A := by
  let S : Set V := (A : Set V) ∪ {v}
  have hs : ∀ x ∈ S, ∀ y ∈ S, D.pairing x y = 1 := by
    intro x hx y hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hA.1 x hx y hy
    · have hyv : y = v := hy
      subst y
      have hf := pairing_flip D x v
      rw [hv x hx, mul_one] at hf
      exact hf
    · have hxv : x = v := hx
      subst x
      exact hv y hy
    · have hxv : x = v := hx
      have hyv : y = v := hy
      subst x; subst y
      exact D.alternating v
  have hgen : IsIsotropic D.pairing (Subgroup.closure S) := by
    intro x hx y hy
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      induction hy using Subgroup.closure_induction with
      | mem y hy => exact hs x hx y hy
      | one => simp
      | mul y z hy hz iy iz => simp [iy, iz]
      | inv y hy iy => simp [iy]
    | one => simp
    | mul x z hx hz ix iz => simp [ix, iz]
    | inv x hx ix => simp [ix]
  have hcl := hA.2 (Subgroup.closure S)
    (fun a ha => Subgroup.subset_closure (Or.inl ha)) hgen
  rw [← hcl]
  exact Subgroup.subset_closure (Or.inr rfl)
private lemma character_sum {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂˣ) : (∑ x, (χ x : ℂ)) = if χ = 1 then (Fintype.card G : ℂ) else 0 := by
  classical
  split_ifs with h
  · simp [h]
  · obtain ⟨x, hx⟩ : ∃ x, (χ x : ℂ) ≠ 1 := by
      by_contra hn
      push Not at hn
      apply h
      ext x
      exact hn x
    have hs : ∑ y, (χ y : ℂ) = (χ x : ℂ) * ∑ y, (χ y : ℂ) := by
      rw [Finset.mul_sum]
      symm
      exact Fintype.sum_equiv (Equiv.mulLeft x) _ _ (by intro y; simp [map_mul])
    have hm : ((χ x : ℂ) - 1) * ∑ y, (χ y : ℂ) = 0 := by
      linear_combination -hs
    exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hx)

open scoped Classical
private lemma restricted_sum {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) (A : Subgroup V) (hA : IsMaximalIsotropic D.pairing A)
    (v : V) : (∑ a : A, ((D.pairing v a : ℂˣ) : ℂ)) =
      if v ∈ A then (Fintype.card A : ℂ) else 0 := by
  classical
  let χ : A →* ℂˣ := (rootsOfUnity 3 ℂ).subtype.comp ((D.pairing v).domRestrict A)
  have hc : χ = 1 ↔ v ∈ A := by
    constructor
    · intro hh
      apply maximal_orthogonal D A hA v
      intro a ha
      have he := DFunLike.congr_fun hh (⟨a, ha⟩ : A)
      exact Subtype.ext he
    · intro hv
      ext a
      simpa [χ] using congrArg (fun t : rootsOfUnity 3 ℂ => ((t : ℂˣ) : ℂ)) (hA.1 v hv a a.2)
  change (∑ a : A, (χ a : ℂ)) = _
  rw [character_sum]
  simp only [hc]
open scoped Classical
private lemma full_sum {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) (v : V) : (∑ a : V, ((D.pairing v a : ℂˣ) : ℂ)) =
      if v = 1 then (Fintype.card V : ℂ) else 0 := by
  classical
  let χ : V →* ℂˣ := (rootsOfUnity 3 ℂ).subtype.comp (D.pairing v)
  have hc : χ = 1 ↔ v = 1 := by
    constructor
    · intro hh
      apply D.perfect.1
      apply MonoidHom.ext
      intro a
      simpa using (Subtype.ext (DFunLike.congr_fun hh a) : D.pairing v a = 1)
    · rintro rfl
      simp [χ]
  change (∑ a : V, (χ a : ℂ)) = _
  rw [character_sum]
  simp only [hc]
private lemma maximal_card_square {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) (A : Subgroup V) (hA : IsMaximalIsotropic D.pairing A) :
    Fintype.card A ^ 2 = Fintype.card V := by
  have hs : (∑ v : V, ∑ a : A, ((D.pairing v a : ℂˣ) : ℂ)) =
      (Fintype.card A : ℂ) ^ 2 := by
    simp_rw [restricted_sum D A hA]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
    have hc : (Finset.univ.filter fun v : V => v ∈ A).card = Fintype.card A := by
      exact (Fintype.card_subtype _).symm
    rw [hc]
    ring
  have ht : (∑ v : V, ∑ a : A, ((D.pairing v a : ℂˣ) : ℂ)) =
      (Fintype.card V : ℂ) := by
    rw [Finset.sum_comm]
    have hflip : ∀ a : A, (∑ v : V, ((D.pairing v a : ℂˣ) : ℂ)) =
        (∑ v : V, ((D.pairing (a : V) v : ℂˣ) : ℂ)) := by
      intro a
      apply Fintype.sum_equiv (Equiv.inv V)
      intro v
      have hf := pairing_flip D v a
      have he : D.pairing v a = D.pairing (a : V) v⁻¹ := by
        rw [map_inv]
        exact eq_inv_of_mul_eq_one_left hf
      rw [he]
      rfl
    simp_rw [hflip, full_sum]
    have he : ∀ a : A, ((a : V) = 1) ↔ a = 1 := by
      intro a
      change ((a : V) = ((1 : A) : V)) ↔ a = 1
      exact Subtype.val_injective.eq_iff
    simp only [he]
    simp
  have he : (Fintype.card A : ℂ) ^ 2 = (Fintype.card V : ℂ) := hs.symm.trans ht
  exact_mod_cast he
open scoped Classical

theorem exact_quotient_cardinality {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) (T : PolarizationData D) :
    Fintype.card (PolarizationIndex T.L T.intersection) =
      Fintype.card (PolarizationIndex T.N T.intersection) ∧
    0 < Fintype.card (PolarizationIndex T.N T.intersection) := by
  have hcard : Fintype.card T.L = Fintype.card T.N := by
    have hL := maximal_card_square D T.L T.maximal_L
    have hN := maximal_card_square D T.N T.maximal_N
    nlinarith
  have hL := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (T.intersection.subgroupOf T.L)
  have hN := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (T.intersection.subgroupOf T.N)
  have heL : Nat.card (T.intersection.subgroupOf T.L) = Nat.card T.intersection :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have heN : Nat.card (T.intersection.subgroupOf T.N) = Nat.card T.intersection :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [heL] at hL
  rw [heN] at hN
  simp only [Nat.card_eq_fintype_card] at hL hN
  refine ⟨?_, Fintype.card_pos⟩
  have hj : 0 < Fintype.card T.intersection := Fintype.card_pos
  nlinarith

private lemma quotient_pairing_sum {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) (A J : Subgroup V) (hJA : J ≤ A)
    (hA : IsMaximalIsotropic D.pairing A)
    (r : LiftSection D.π A J) (v : V) (hv : ∀ j ∈ J, D.pairing v j = 1) :
    (∑ i : PolarizationIndex A J, ((D.pairing v (D.π (r.lift i)) : ℂˣ) : ℂ)) =
      if v ∈ A then (Fintype.card (PolarizationIndex A J) : ℂ) else 0 := by
  let φ : A →* ℂˣ := (rootsOfUnity 3 ℂ).subtype.comp ((D.pairing v).domRestrict A)
  have hJ : J.subgroupOf A ≤ φ.ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val (hv a ha)
  let χ := QuotientGroup.lift (J.subgroupOf A) φ hJ
  have hc : χ = 1 ↔ v ∈ A := by
    constructor
    · intro hh
      apply maximal_orthogonal D A hA v
      intro a ha
      have he := DFunLike.congr_fun hh (QuotientGroup.mk (⟨a, ha⟩ : A))
      exact Subtype.ext he
    · intro hvA
      apply MonoidHom.ext
      intro i
      induction i using QuotientGroup.induction_on with
      | H a =>
        exact congrArg Subtype.val (hA.1 v hvA a a.2)
  have he : ∀ i : PolarizationIndex A J,
      ((D.pairing v (D.π (r.lift i)) : ℂˣ) : ℂ) = (χ i : ℂ) := by
    intro i
    conv_rhs => rw [← r.represents i]
    rfl
  simp_rw [he]
  rw [character_sum]
  simp only [hc]
open scoped Classical commutatorElement
private lemma commute_covariance {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) (A : Subgroup V) (χA : A.comap D.π →* ℂˣ)
    (hcentral : ∀ a : A.comap D.π, ∀ ha : (a : H) ∈ D.C,
      χA a = D.ω ⟨(a : H), ha⟩)
    (h : inducedSpace (A.comap D.π) χA) (x : A.comap D.π) (y g : H) :
    (h : H → ℂ) (y * ((x : H) * g)) =
      ((D.pairing (D.π y) (D.π x) : ℂˣ) : ℂ) * (χA x : ℂ) * (h : H → ℂ) (y * g) := by
  let c : H := ⁅y, (x : H)⁆
  have hcC : c ∈ D.C := D.commutator_mem y x
  have hcA : c ∈ A.comap D.π := by
    have hcK : c ∈ D.π.ker := D.quotient_kernel.symm ▸ hcC
    change D.π c ∈ A
    rw [MonoidHom.mem_ker.mp hcK]
    exact A.one_mem
  let ca : A.comap D.π := ⟨c, hcA⟩
  have hca : χA ca = (D.pairing (D.π y) (D.π x) : ℂˣ) := by
    rw [hcentral ca hcC]
    exact D.commutator_pairing y x
  have he : y * ((x : H) * g) = c * ((x : H) * (y * g)) := by
    dsimp [c]
    rw [commutatorElement_def]
    group
  rw [he, h.property ca, h.property x, hca, ← mul_assoc]
open scoped Classical commutatorElement
private lemma lift_mem_iff {H V : Type*} [Group H] [CommGroup V]
    (π : H →* V) (A B : Subgroup V) (r : LiftSection π B (A ⊓ B))
    (i : PolarizationIndex B (A ⊓ B)) : π (r.lift i) ∈ A ↔ i = 1 := by
  have hr := r.represents i
  constructor
  · intro h
    rw [← hr]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨h, (r.lift i).2⟩
  · intro hi
    rw [hi] at hr ⊢
    exact ((QuotientGroup.eq_one_iff _).mp hr).1
open scoped Classical commutatorElement
private lemma counting_composition {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) (A B : Subgroup V)
    (hA : IsMaximalIsotropic D.pairing A) (hB : IsMaximalIsotropic D.pairing B)
    (χA : A.comap D.π →* ℂˣ) (χB : B.comap D.π →* ℂˣ)
    (hcentral : ∀ a : A.comap D.π, ∀ ha : (a : H) ∈ D.C,
      χA a = D.ω ⟨(a : H), ha⟩)
    (hagree : ∀ a : H, ∀ hA : D.π a ∈ A, ∀ hB : D.π a ∈ B,
      χA ⟨a, hA⟩ = χB ⟨a, hB⟩)
    (r : LiftSection D.π A (A ⊓ B)) (s : LiftSection D.π B (A ⊓ B))
    (h : inducedSpace (A.comap D.π) χA) (g : H) :
    countingAverage D.π A (A ⊓ B) χA r
      (countingAverage D.π B (A ⊓ B) χB s h) g =
      (Fintype.card (PolarizationIndex A (A ⊓ B)) : ℂ) * (h : H → ℂ) g := by
  unfold countingAverage
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ (j : PolarizationIndex B (A ⊓ B)) (i : PolarizationIndex A (A ⊓ B)),
      (χA (r.lift i) : ℂ)⁻¹ * ((χB (s.lift j) : ℂ)⁻¹ *
        (h : H → ℂ) ((s.lift j : H) * ((r.lift i : H) * g))) =
      ((D.pairing (D.π (s.lift j)) (D.π (r.lift i)) : ℂˣ) : ℂ) *
        ((χB (s.lift j) : ℂ)⁻¹ * (h : H → ℂ) ((s.lift j : H) * g)) := by
    intro j i
    rw [commute_covariance D A χA hcentral h]
    have hn : (χA (r.lift i) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  simp_rw [hterm, ← Finset.sum_mul]
  have hp : ∀ j : PolarizationIndex B (A ⊓ B),
      ∀ v ∈ A ⊓ B, D.pairing (D.π (s.lift j)) v = 1 := by
    intro j v hv
    exact hB.1 _ (s.lift j).2 v hv.2
  simp_rw [quotient_pairing_sum D A (A ⊓ B) inf_le_left hA r _ (hp _)]
  simp_rw [lift_mem_iff D.π A B s]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hz : D.π (s.lift 1) ∈ A := (lift_mem_iff D.π A B s 1).mpr rfl
  let x : A.comap D.π := ⟨s.lift 1, hz⟩
  have hx : χA x = χB (s.lift 1) := hagree _ hz (s.lift 1).2
  rw [h.property x, hx]
  have hn : (χB (s.lift 1) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

theorem P_Q {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) (T : PolarizationData D)
    (r : LiftSection D.π T.L T.intersection)
    (s : LiftSection D.π T.N T.intersection)
    (h : inducedSpace (T.L.comap D.π) T.χL) : P D T r (Q D T s h) = h := by
  apply Subtype.ext
  funext g
  change countingAverage D.π T.L T.intersection T.χL r
    (fun y => (Fintype.card (PolarizationIndex T.N T.intersection) : ℂ)⁻¹ *
      countingAverage D.π T.N T.intersection T.χN s h y) g = (h : H → ℂ) g
  have he : countingAverage D.π T.L T.intersection T.χL r
      (fun y => (Fintype.card (PolarizationIndex T.N T.intersection) : ℂ)⁻¹ *
        countingAverage D.π T.N T.intersection T.χN s h y) g =
      (Fintype.card (PolarizationIndex T.N T.intersection) : ℂ)⁻¹ *
        countingAverage D.π T.L T.intersection T.χL r
          (countingAverage D.π T.N T.intersection T.χN s h) g := by
    unfold countingAverage
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he, counting_composition D T.L T.N T.maximal_L T.maximal_N T.χL T.χN
    T.central_L T.agree_on_intersection r s h g, (exact_quotient_cardinality D T).1]
  have hn : (Fintype.card (PolarizationIndex T.N T.intersection) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem Q_P {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : HeisenbergData H V) (T : PolarizationData D)
    (r : LiftSection D.π T.L T.intersection)
    (s : LiftSection D.π T.N T.intersection)
    (f : inducedSpace (T.N.comap D.π) T.χN) : Q D T s (P D T r f) = f := by
  apply Subtype.ext
  funext g
  change (Fintype.card (PolarizationIndex T.N T.intersection) : ℂ)⁻¹ *
    countingAverage D.π T.N T.intersection T.χN s
      (countingAverage D.π T.L T.intersection T.χL r f) g = (f : H → ℂ) g
  have he : countingAverage D.π T.N T.intersection T.χN s
      (countingAverage D.π T.L T.intersection T.χL r f) g =
      (Fintype.card (PolarizationIndex T.N T.intersection) : ℂ) * (f : H → ℂ) g := by
    have hswap : T.N ⊓ T.L = T.intersection := inf_comm _ _
    generalize hj : T.intersection = J at s r ⊢
    rw [hj] at hswap
    subst J
    exact counting_composition D T.N T.L T.maximal_N T.maximal_L T.χN T.χL
      T.central_N (fun a hN hL => (T.agree_on_intersection a hL hN).symm) s r f g
  rw [he]
  have hn : (Fintype.card (PolarizationIndex T.N T.intersection) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end DedekindZetaZeroFree.FinitePolarization

end
