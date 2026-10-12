module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree
namespace CubicCharacters

abbrev Mu3 := rootsOfUnity 3 ℂ

abbrev Character (U : Type*) [CommGroup U] [TopologicalSpace U] := U →ₜ* Mu3

def cubes (U : Type*) [CommGroup U] : Subgroup U :=
  (powMonoidHom (α := U) 3).range

noncomputable def levelIndex {U : Type*} [CommGroup U] (V : ℕ → Subgroup U) (j : ℕ) : ℕ :=
  (cubes U ⊔ V j).index

noncomputable def conductor {U : Type*} [CommGroup U] [TopologicalSpace U]
    (V : ℕ → Subgroup U) (χ : Character U) : ℕ :=
  sInf {j | V j ≤ χ.toMonoidHom.ker}

private lemma cube (z : Mu3) : z ^ 3 = 1 := by
  apply Subtype.ext
  exact (mem_rootsOfUnity 3 _).mp z.property

private lemma homCard (Q : Type*) [CommGroup Q] [Finite Q]
    (hp : ∀ q : Q, q ^ 3 = 1) : Nat.card (Q →* Mu3) = Nat.card Q := by
  let e : (Q →* Mu3) ≃ (Q →* ℂˣ) :=
    { toFun := fun f => (rootsOfUnity 3 ℂ).subtype.comp f
      invFun := fun f => f.codRestrict (rootsOfUnity 3 ℂ) (fun q => by
        rw [mem_rootsOfUnity, ← map_pow, hp, map_one])
      left_inv := fun f => by ext q; rfl
      right_inv := fun f => by ext q; rfl }
  letI : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) :=
    HasEnoughRootsOfUnity.of_dvd ℂ (Monoid.exponent_dvd_of_forall_pow_eq_one hp)
  exact (Nat.card_congr e).trans (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ)

lemma killsCube {U : Type*} [CommGroup U] (χ : U →* Mu3) :
    cubes U ≤ χ.ker := by
  rintro x ⟨y, rfl⟩
  change χ (y ^ 3) = 1
  rw [map_pow, cube]

noncomputable def levelEquiv {U : Type*} [CommGroup U] [TopologicalSpace U]
    [IsTopologicalGroup U] (V : Subgroup U) (hopen : IsOpen (V : Set U)) :
    {χ : Character U // V ≤ χ.toMonoidHom.ker} ≃ ((U ⧸ (cubes U ⊔ V)) →* Mu3) := by
  let H := cubes U ⊔ V
  letI : DiscreteTopology (U ⧸ H) := QuotientGroup.discreteTopology
    (Subgroup.isOpen_mono le_sup_right hopen)
  exact
    { toFun := fun χ => QuotientGroup.lift H χ.val.toMonoidHom
        (sup_le (killsCube _) χ.property)
      invFun := fun f => ⟨⟨f.comp (QuotientGroup.mk' H),
        (continuous_of_discreteTopology (f := f)).comp QuotientGroup.continuous_mk⟩,
        fun x hx => by
          change f (x : U ⧸ H) = 1
          rw [(QuotientGroup.eq_one_iff x).mpr ((show V ≤ H from le_sup_right) hx), map_one]⟩
      left_inv := fun χ => by apply Subtype.ext; ext x; rfl
      right_inv := fun f => by
        apply MonoidHom.ext
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
        rfl }

private lemma levelCount {U : Type*} [CommGroup U] [TopologicalSpace U]
    [IsTopologicalGroup U] (V : Subgroup U) (hopen : IsOpen (V : Set U))
    [hfin : (cubes U ⊔ V).FiniteIndex] :
    Finite {χ : Character U // V ≤ χ.toMonoidHom.ker} ∧
    Nat.card {χ : Character U // V ≤ χ.toMonoidHom.ker} = (cubes U ⊔ V).index := by
  let H := cubes U ⊔ V
  have hp : ∀ q : U ⧸ H, q ^ 3 = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ((show cubes U ≤ H from le_sup_left) ⟨x, rfl⟩)
  letI : Finite ((U ⧸ H) →* Mu3) := Finite.of_injective
    (fun f : (U ⧸ H) →* Mu3 => (f : (U ⧸ H) → Mu3)) DFunLike.coe_injective
  exact ⟨Finite.of_equiv _ (levelEquiv V hopen).symm,
    (Nat.card_congr (levelEquiv V hopen)).trans (homCard (U ⧸ H) hp)⟩

end CubicCharacters

open CubicCharacters Filter
open scoped Topology

theorem kp_filtered_cubic_character_count
    {U : Type*} [CommGroup U] [TopologicalSpace U] [IsTopologicalGroup U] [T2Space U]
    (V : ℕ → Subgroup U)
    (hzero : V 0 = ⊤)
    (hdescending : Antitone V)
    (hopen : ∀ j, IsOpen (V j : Set U))
    (hfinite : ∀ j, (V j).FiniteIndex)
    (hbasis : ∀ W ∈ 𝓝 (1 : U), ∃ j, (V j : Set U) ⊆ W)
    (hquotientFinite : ∀ j, (cubes U ⊔ V j).FiniteIndex)
    (N : ℕ)
    (hstable : ∀ j, N ≤ j → levelIndex V j = levelIndex V N) :
    Finite (Character U) ∧
    (∀ χ : Character U, ∃ j, V j ≤ χ.toMonoidHom.ker) ∧
    (∀ χ : Character U, V (conductor V χ) ≤ χ.toMonoidHom.ker) ∧
    (∀ χ : Character U, conductor V χ ≤ N) ∧
    (∀ j, Nat.card {χ : Character U // conductor V χ ≤ j} = levelIndex V j) ∧
    (∀ j, 1 ≤ j → Nat.card {χ : Character U // conductor V χ = j} =
      levelIndex V j - levelIndex V (j - 1)) ∧
    (∀ χ : Character U, conductor V χ = 0 ↔ χ = 1) ∧
    Nat.card {χ : Character U // conductor V χ = 0} = 1 := by
  classical
  have hex : ∀ χ : Character U, ∃ j, V j ≤ χ.toMonoidHom.ker := by
    intro χ
    have ho : IsOpen (χ.toMonoidHom.ker : Set U) :=
      (isOpen_discrete {1}).preimage χ.continuous
    exact hbasis _ (ho.mem_nhds (by simp))
  have hmin : ∀ χ : Character U, V (conductor V χ) ≤ χ.toMonoidHom.ker :=
    fun χ => Nat.sInf_mem (hex χ)
  have hiff : ∀ (χ : Character U) (j : ℕ),
      conductor V χ ≤ j ↔ V j ≤ χ.toMonoidHom.ker := by
    intro χ j
    exact ⟨fun h => le_trans (hdescending h) (hmin χ), fun h => Nat.sInf_le h⟩
  have hcount : ∀ j, Finite {χ : Character U // conductor V χ ≤ j} ∧
      Nat.card {χ : Character U // conductor V χ ≤ j} = levelIndex V j := by
    intro j
    letI := hquotientFinite j
    let e := Equiv.subtypeEquivRight (fun χ => hiff χ j)
    have hc := levelCount (V j) (hopen j)
    letI := hc.1
    exact ⟨Finite.of_equiv _ e.symm, (Nat.card_congr e).trans hc.2⟩
  have hbound : ∀ χ : Character U, conductor V χ ≤ N := by
    intro χ
    let k := max N (conductor V χ)
    letI := (hcount k).1
    letI := (hcount N).1
    let f : {χ : Character U // conductor V χ ≤ N} →
        {χ : Character U // conductor V χ ≤ k} :=
      fun χ => ⟨χ.val, le_trans χ.property (le_max_left _ _)⟩
    have hf : Function.Bijective f :=
      (Nat.bijective_iff_injective_and_card f).mpr
        ⟨fun a b h => Subtype.ext (congrArg
            (fun c : {χ : Character U // conductor V χ ≤ k} => c.val) h),
          (hcount N).2.trans ((hstable k (le_max_left _ _)).symm.trans (hcount k).2.symm)⟩
    obtain ⟨ψ, hψ⟩ := hf.2 ⟨χ, le_max_right _ _⟩
    have he : ψ.val = χ := congrArg Subtype.val hψ
    simpa [he] using ψ.property
  letI := (hcount N).1
  letI : Finite (Character U) := Finite.of_injective
    (fun χ : Character U => (⟨χ, hbound χ⟩ : {χ : Character U // conductor V χ ≤ N}))
    (fun a b h => congrArg Subtype.val h)
  have hdiff : ∀ j, 1 ≤ j → Nat.card {χ : Character U // conductor V χ = j} =
      levelIndex V j - levelIndex V (j - 1) := by
    intro j hj
    have hs : {χ : Character U | conductor V χ = j} =
        {χ | conductor V χ ≤ j} \ {χ | conductor V χ ≤ j - 1} := by
      ext χ
      simp only [Set.mem_setOf_eq, Set.mem_diff]
      omega
    change ({χ : Character U | conductor V χ = j}).ncard = _
    rw [hs, Set.ncard_sdiff]
    · exact congrArg₂ (· - ·) (hcount j).2 (hcount (j - 1)).2
    · intro χ hχ
      exact le_trans hχ (Nat.sub_le _ _)
  have hzerochar : ∀ χ : Character U, conductor V χ = 0 ↔ χ = 1 := by
    intro χ
    rw [← Nat.le_zero, hiff, hzero]
    constructor
    · intro h
      apply ContinuousMonoidHom.ext
      intro x
      exact h (show x ∈ (⊤ : Subgroup U) from trivial)
    · rintro rfl
      intro x hx
      rfl
  have hzcard : Nat.card {χ : Character U // conductor V χ = 0} = 1 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hzerochar)]
    simp
  exact ⟨inferInstance, hex, hmin, hbound, fun j => (hcount j).2,
    hdiff, hzerochar, hzcard⟩

end DedekindZetaZeroFree
