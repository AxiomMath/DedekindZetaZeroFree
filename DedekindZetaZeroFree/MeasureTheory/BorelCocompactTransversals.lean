module

public import DedekindZetaZeroFree.Geometry.DiscreteCocompactQuotientSlices
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section

namespace DedekindZetaZeroFree

open Set

theorem exists_measurable_relativelyCompact_exact_transversal_of_finite_slices
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) (n : ℕ) (V : Fin n → Set G)
    (hopen : ∀ i : Fin n, IsOpen (V i))
    (hcompact : ∀ i : Fin n, IsCompact (closure (V i)))
    (hinj : ∀ i : Fin n, Set.InjOn (QuotientGroup.mk : G → G ⧸ Γ) (V i))
    (hcover : (⋃ i : Fin n, (QuotientGroup.mk : G → G ⧸ Γ) '' V i) = Set.univ) :
    ∃ D : Set G, MeasurableSet D ∧ IsCompact (closure D) ∧
      ∀ y : G, ∃! γ : Γ, (γ : G) * y ∈ D := by
  classical

  set Rem : Fin n → Set G :=
    fun i => ⋃ (j : Fin n) (_ : j < i) (γ : Γ), {x : G | (γ : G) * x ∈ V j} with hRem
  set D : Set G := ⋃ i : Fin n, V i \ Rem i with hD
  have hRem_mem : ∀ (i : Fin n) (x : G),
      x ∈ Rem i ↔ ∃ (j : Fin n) (_ : j < i) (γ : Γ), (γ : G) * x ∈ V j := by
    intro i x
    rw [hRem]
    simp only [mem_iUnion, mem_setOf_eq]
  have hRem_open : ∀ i : Fin n, IsOpen (Rem i) := by
    intro i
    rw [hRem]
    refine isOpen_iUnion (fun j => isOpen_iUnion (fun _ => isOpen_iUnion (fun γ => ?_)))
    exact (hopen j).preimage (continuous_const.mul continuous_id)
  refine ⟨D, ?_, ?_, ?_⟩
  ·
    rw [hD]
    refine MeasurableSet.iUnion (fun i => ?_)
    exact ((hopen i).measurableSet.diff (hRem_open i).measurableSet)
  ·
    have hsub : D ⊆ ⋃ i : Fin n, closure (V i) := by
      rw [hD]
      refine iUnion_mono (fun i => ?_)
      exact Subset.trans diff_subset subset_closure
    exact IsCompact.of_isClosed_subset (isCompact_iUnion (fun i => hcompact i))
      isClosed_closure (closure_minimal hsub (isClosed_iUnion_of_finite fun i => isClosed_closure))
  ·
    intro y
    have hex : ∃ i : Fin n, (QuotientGroup.mk : G → G ⧸ Γ) y ∈
        (QuotientGroup.mk : G → G ⧸ Γ) '' V i := by
      have h : (QuotientGroup.mk y) ∈ ⋃ i : Fin n, (QuotientGroup.mk : G → G ⧸ Γ) '' V i := by
        rw [hcover]
        exact Set.mem_univ _
      exact Set.mem_iUnion.mp h

    obtain ⟨i₀, hi₀mem, hi₀min⟩ :
        ∃ i : Fin n, (QuotientGroup.mk : G → G ⧸ Γ) y ∈ (QuotientGroup.mk : G → G ⧸ Γ) '' V i ∧
          ∀ j : Fin n, j < i → (QuotientGroup.mk : G → G ⧸ Γ) y ∉
            (QuotientGroup.mk : G → G ⧸ Γ) '' V j :=
      ⟨Fin.find (fun i : Fin n => (QuotientGroup.mk : G → G ⧸ Γ) y ∈
          (QuotientGroup.mk : G → G ⧸ Γ) '' V i) hex,
        Fin.find_spec hex, fun j hj => Fin.find_min hex hj⟩
    obtain ⟨v, hv, hqv⟩ := hi₀mem

    have hmemΓ : v * y⁻¹ ∈ Γ :=
      (QuotientGroup.eq_one_iff (v * y⁻¹)).mp (by
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hqv, mul_inv_cancel])
    refine ⟨⟨v * y⁻¹, hmemΓ⟩, ?_, ?_⟩
    · have hvD : v ∈ D := by
        rw [hD]
        refine Set.mem_iUnion.mpr ⟨i₀, hv, ?_⟩
        rw [hRem_mem]
        rintro ⟨j, hj, γ, hγ⟩
        refine hi₀min j hj ⟨(γ : G) * v, hγ, ?_⟩
        have h1 : ((γ : G) : G ⧸ Γ) = 1 := (QuotientGroup.eq_one_iff (γ : G)).mpr γ.2
        simpa only [QuotientGroup.mk_mul, h1, one_mul] using hqv
      simpa only [Subtype.coe_mk, mul_assoc, inv_mul_cancel, mul_one] using hvD
    · intro γ' hγ'
      rw [hD] at hγ'
      obtain ⟨i', hi'V, hi'not⟩ := Set.mem_iUnion.mp hγ'
      rw [hRem_mem] at hi'not
      have hii : i' = i₀ := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        ·
          refine hi₀min i' hlt ⟨(γ' : G) * y, hi'V, ?_⟩
          have h1 : ((γ' : G) : G ⧸ Γ) = 1 := (QuotientGroup.eq_one_iff (γ' : G)).mpr γ'.2
          simpa only [QuotientGroup.mk_mul, h1, one_mul]
        ·
          refine hi'not ⟨i₀, hlt, ⟨(⟨v * y⁻¹, hmemΓ⟩ : Γ) * γ'⁻¹, ?_⟩⟩
          have hprod : (((⟨v * y⁻¹, hmemΓ⟩ : Γ) * γ'⁻¹ : Γ) : G) * ((γ' : G) * y) = v := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk, mul_assoc,
              inv_mul_cancel_left, inv_mul_cancel, mul_one]
          rwa [hprod]
      rw [hii] at hi'V
      have hEq : (γ' : G) * y = v := by
        refine (hinj i₀) hi'V hv ?_
        have h1 : ((γ' : G) : G ⧸ Γ) = 1 := (QuotientGroup.eq_one_iff (γ' : G)).mpr γ'.2
        simpa only [QuotientGroup.mk_mul, h1, one_mul] using hqv.symm
      have hvy : ((⟨v * y⁻¹, hmemΓ⟩ : Γ) : G) * y = v := by
        simp only [Subtype.coe_mk, mul_assoc, inv_mul_cancel, mul_one]
      exact Subtype.ext (mul_right_cancel (hEq.trans hvy.symm))

end DedekindZetaZeroFree
