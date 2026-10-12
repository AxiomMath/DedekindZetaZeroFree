module

public import DedekindZetaZeroFree.Metaplectic.Torus.LocalCubicHeisenbergPairing
public import DedekindZetaZeroFree.RepresentationTheory.Heisenberg.FinitePolarizationAveraging

@[expose] public section

namespace DedekindZetaZeroFree.KPLocalPolarization

open DedekindZetaZeroFree.FinitePolarization

def IsMaximalAbelian {H : Type*} [Group H] (A : Subgroup H) : Prop :=
  (∀ x ∈ A, ∀ y ∈ A, Commute x y) ∧
    ∀ B : Subgroup H, A ≤ B → (∀ x ∈ B, ∀ y ∈ B, Commute x y) → B = A

theorem exists_maximal_isotropic {D : Type*} [CommGroup D] [Finite D]
    (b : D →* (D →* rootsOfUnity 3 ℂ)) :
    ∃ L : Subgroup D, IsMaximalIsotropic b L := by
  classical
  have hne : {L : Subgroup D | IsIsotropic b L}.Nonempty := by
    refine ⟨⊥, ?_⟩
    intro x hx y hy
    simp only [Subgroup.mem_bot] at hx hy
    subst x; subst y
    simp
  obtain ⟨L, hL, hmax⟩ := Set.Finite.exists_maximal
    (Set.toFinite {L : Subgroup D | IsIsotropic b L}) hne
  exact ⟨L, hL, fun M hLM hM => le_antisymm (hmax hM hLM) hLM⟩

theorem preimage_maximal_abelian {H D : Type*} [Group H] [CommGroup D]
    (π : H →* D) (hπ : Function.Surjective π)
    (b : D →* (D →* rootsOfUnity 3 ℂ))
    (hcommute : ∀ x y : H, Commute x y ↔ b (π x) (π y) = 1)
    (L : Subgroup D) (hL : IsMaximalIsotropic b L) :
    IsMaximalAbelian (L.comap π) := by
  refine ⟨fun x hx y hy => (hcommute x y).2 (hL.1 (π x) hx (π y) hy), ?_⟩
  intro B hLB hB
  have hBL : B.map π = L := by
    apply hL.2
    · intro d hd
      obtain ⟨x, rfl⟩ := hπ d
      exact Subgroup.mem_map.mpr ⟨x, hLB hd, rfl⟩
    · intro x hx y hy
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
      exact (hcommute u v).1 (hB u hu v hv)
  apply le_antisymm _ hLB
  intro x hx
  show π x ∈ L
  rw [← hBL]
  exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

theorem continuous_character_extension {H : Type*} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H]
    (C A : Subgroup H) (hCA : C ≤ A) (hCopen : IsOpen (C : Set H))
    (hAabelian : ∀ x ∈ A, ∀ y ∈ A, Commute x y)
    (ω : C →ₜ* ℂˣ) :
    ∃ ωA : A →ₜ* ℂˣ, ∀ a : A, ∀ ha : (a : H) ∈ C,
      ωA a = ω ⟨(a : H), ha⟩ := by
  classical
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := fun x y => Subtype.ext (hAabelian x x.2 y y.2).eq }
  letI : CommGroup C :=
    { (inferInstance : Group C) with
      mul_comm := fun x y => Subtype.ext (hAabelian x (hCA x.2) y (hCA y.2)).eq }
  letI : DivisibleBy (Additive ℂˣ) ℕ := divisibleByOfSMulRightSurj _ _ (by
    intro n hn a
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, zero_pow (Nat.pos_of_ne_zero hn).ne'] at hz
      exact a.toMul.ne_zero hz.symm
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    change Additive.ofMul ((Units.mk0 z hz0) ^ n) = a
    apply congrArg Additive.ofMul
    apply Units.ext
    exact hz)
  letI : DivisibleBy (Additive ℂˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  let i : C →* A := Subgroup.inclusion hCA
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun a : A => (a : H)) h
  obtain ⟨f, hf⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    i.toAdditive hi ω.toMonoidHom.toAdditive
  let fM : A →* ℂˣ :=
    { toFun := fun a => (f (Additive.ofMul a)).toMul
      map_one' := f.map_zero
      map_mul' := f.map_add }
  have hext : ∀ c : C, fM (i c) = ω c := by
    intro c
    exact congrArg Additive.toMul (DFunLike.congr_fun hf (Additive.ofMul c))
  have hfcont : Continuous fM := by
    apply continuous_of_continuousAt_one fM
    have hiind : Topology.IsInducing i := (Topology.IsEmbedding.inclusion hCA).isInducing
    have hirange : Set.range i = {a : A | (a : H) ∈ C} := by
      ext a
      constructor
      · rintro ⟨c, rfl⟩
        exact c.2
      · intro ha
        exact ⟨⟨a, ha⟩, rfl⟩
    have hmem : Set.range i ∈ nhds (i (1 : C)) := by
      rw [hirange]
      exact (hCopen.preimage continuous_subtype_val).mem_nhds C.one_mem
    have hc : Continuous (fM ∘ i) := by
      have heq : fM ∘ i = ω := funext hext
      rw [heq]
      exact ω.continuous
    have hcat := (hiind.continuousAt_iff' hmem).mp (hc.continuousAt (x := (1 : C)))
    simpa only [map_one] using hcat
  refine ⟨⟨fM, hfcont⟩, ?_⟩
  intro a ha
  exact hext ⟨(a : H), ha⟩

theorem exists_continuous_maximal_polarization {H D : Type*}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CommGroup D] [Finite D]
    (π : H →* D) (hπ : Function.Surjective π)
    (C : Subgroup H) (hC : π.ker = C) (hCopen : IsOpen (C : Set H))
    (b : D →* (D →* rootsOfUnity 3 ℂ))
    (hcommute : ∀ x y : H, Commute x y ↔ b (π x) (π y) = 1)
    (ω : C →ₜ* ℂˣ) :
    ∃ L : Subgroup D, IsMaximalIsotropic b L ∧
      IsMaximalAbelian (L.comap π) ∧
      ∃ ωL : L.comap π →ₜ* ℂˣ,
        ∀ a : L.comap π, ∀ ha : (a : H) ∈ C, ωL a = ω ⟨(a : H), ha⟩ := by
  obtain ⟨L, hL⟩ := exists_maximal_isotropic b
  have hA := preimage_maximal_abelian π hπ b hcommute L hL
  refine ⟨L, hL, hA, ?_⟩
  apply continuous_character_extension C (L.comap π) _ hCopen hA.1 ω
  intro x hx
  show π x ∈ L
  have hxker : x ∈ π.ker := by rw [hC]; exact hx
  rw [MonoidHom.mem_ker] at hxker
  rw [hxker]
  exact L.one_mem

end DedekindZetaZeroFree.KPLocalPolarization
