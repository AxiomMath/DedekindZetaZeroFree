module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree
namespace KPChamberLattice

open NumberField Module

private theorem lattice_count {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (b : Basis ι ℝ E) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ∀ s : Set E, (∀ x ∈ s, x ∈ Submodule.span ℤ (Set.range b) ∧ ‖x‖ ≤ R) →
        s.Finite ∧ (s.ncard : ℝ) ≤ C * R ^ Fintype.card ι := by
  classical
  let L := b.equivFunL.toContinuousLinearMap
  let A : ℝ := ‖L‖ + 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨(2 * A + 3) ^ Fintype.card ι, by positivity, ?_⟩
  intro R hR s hs
  let N : ℤ := ⌈A * R⌉
  let t := Fintype.piFinset (fun _ : ι => Finset.Icc (-N) N)
  let f : E → ι → ℤ := fun x i => ⌊b.repr x i⌋
  have hrepr (x : E) (hx : x ∈ s) (i : ι) : (f x i : ℝ) = b.repr x i := by
    obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ x).mp (hs x hx).1 i
    simpa [f, ← hz] using (Int.floor_intCast (R := ℝ) z)
  have hf : Set.MapsTo f s (t : Set (ι → ℤ)) := by
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    have hb : |b.repr x i| ≤ A * R := by
      calc
        |b.repr x i| = ‖L x i‖ := by simp [L, Basis.equivFunL_apply, Real.norm_eq_abs]
        _ ≤ ‖L x‖ := norm_le_pi_norm _ _
        _ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
        _ ≤ A * R := mul_le_mul (by dsimp [A]; linarith) (hs x hx).2
          (norm_nonneg _) (le_of_lt hA)
    have hn : A * R ≤ (N : ℝ) := Int.le_ceil _
    simp only [Finset.mem_Icc]
    constructor
    · apply (Int.cast_le (R := ℝ)).mp
      rw [Int.cast_neg, hrepr x hx i]
      linarith [(abs_le.mp hb).1]
    · apply (Int.cast_le (R := ℝ)).mp
      rw [hrepr x hx i]
      exact (abs_le.mp hb).2.trans hn
  have hinj : Set.InjOn f s := by
    intro x hx y hy hxy
    apply b.ext_elem
    intro i
    rw [← hrepr x hx i, ← hrepr y hy i, congrFun hxy i]
  have hN : 0 ≤ N := Int.ceil_nonneg (mul_nonneg hA.le (by linarith))
  have hc : ((Finset.Icc (-N) N).card : ℝ) ≤ (2 * A + 3) * R := by
    have he := Int.card_Icc_of_le (-N) N (by omega)
    have he' : ((Finset.Icc (-N) N).card : ℝ) = 2 * (N : ℝ) + 1 := by
      have heR : ((Finset.Icc (-N) N).card : ℝ) = (N : ℝ) + 1 - -(N : ℝ) := by exact_mod_cast he
      linarith
    rw [he']
    have hn : (N : ℝ) < A * R + 1 := Int.ceil_lt_add_one _
    nlinarith
  refine ⟨Set.Finite.of_injOn hf hinj t.finite_toSet, ?_⟩
  calc
    (s.ncard : ℝ) ≤ ((t : Set (ι → ℤ)).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard_of_injOn f hf hinj t.finite_toSet
    _ = ((Finset.Icc (-N) N).card : ℝ) ^ Fintype.card ι := by
      rw [Set.ncard_coe_finset]
      dsimp only [t]
      rw [Fintype.card_piFinset]
      simp only [Finset.prod_const, Finset.card_univ, Nat.cast_pow]
    _ ≤ ((2 * A + 3) * R) ^ Fintype.card ι :=
      pow_le_pow_left₀ (by positivity) hc _
    _ = (2 * A + 3) ^ Fintype.card ι * R ^ Fintype.card ι := mul_pow _ _ _

open scoped Classical in
private theorem mixed_norm_bound (F : Type*) [Field F] [NumberField F]
    (x : F) (R : ℝ) (hR : 0 ≤ R) (hx : ∀ φ : F →+* ℂ, ‖φ x‖ ≤ R) :
    ‖mixedEmbedding F x‖ ≤ R := by
  classical
  apply norm_prod_le_iff.mpr
  constructor
  · apply pi_norm_le_iff_of_nonneg hR |>.mpr
    intro w
    rw [← mixedEmbedding.normAtPlace_apply_of_isReal w.prop,
      mixedEmbedding.normAtPlace_apply, ← InfinitePlace.norm_embedding_eq]
    exact hx _
  · apply pi_norm_le_iff_of_nonneg hR |>.mpr
    intro w
    rw [← mixedEmbedding.normAtPlace_apply_of_isComplex w.prop,
      mixedEmbedding.normAtPlace_apply, ← InfinitePlace.norm_embedding_eq]
    exact hx _

def idealPairBox (F : Type*) [Field F] [NumberField F]
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (R : ℝ) : Set (F × F) :=
  {p | p.1 ∈ J ∧ p.2 ∈ J ∧
    ∀ φ : F →+* ℂ, ‖φ p.1‖ ≤ R ∧ ‖φ p.2‖ ≤ R}

end KPChamberLattice

open NumberField Module KPChamberLattice

theorem kp_chamber_lattice_box_count (F : Type*) [Field F] [NumberField F]
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (hJ : J ≠ 0) :
    ∃ C_J : ℝ, 0 < C_J ∧ ∀ R : ℝ, 1 ≤ R →
      (KPChamberLattice.idealPairBox F J R).Finite ∧
      ((KPChamberLattice.idealPairBox F J R).ncard : ℝ) ≤
        C_J * R ^ (2 * Module.finrank ℚ F) := by
  classical
  let I : (FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)ˣ :=
    (isUnit_iff_ne_zero.mpr hJ).unit
  have hI : (I : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) = J :=
    IsUnit.unit_spec _
  let b := mixedEmbedding.fractionalIdealLatticeBasis F I
  let B := b.prod b
  have hd : Fintype.card (Module.Free.ChooseBasisIndex ℤ I ⊕
      Module.Free.ChooseBasisIndex ℤ I) = 2 * Module.finrank ℚ F := by
    rw [Fintype.card_sum, ← Module.finrank_eq_card_basis b, mixedEmbedding.finrank]
    omega
  obtain ⟨C, hC, hbound⟩ := lattice_count B
  refine ⟨C, hC, ?_⟩
  intro R hR
  let s : Set (F × F) := {p | p.1 ∈ J ∧ p.2 ∈ J ∧
      ∀ φ : F →+* ℂ, ‖φ p.1‖ ≤ R ∧ ‖φ p.2‖ ≤ R}
  let f : F × F → mixedEmbedding.mixedSpace F × mixedEmbedding.mixedSpace F :=
    fun p => (mixedEmbedding F p.1, mixedEmbedding F p.2)
  have hinj : Function.Injective f := by
    intro p q hpq
    apply Prod.ext
    · exact mixedEmbedding_injective F (congrArg Prod.fst hpq)
    · exact mixedEmbedding_injective F (congrArg Prod.snd hpq)
  have hspan (x : F) (hx : x ∈ J) :
      mixedEmbedding F x ∈ Submodule.span ℤ (Set.range b) := by
    apply (mixedEmbedding.mem_span_fractionalIdealLatticeBasis F I).mpr
    exact ⟨x, by simpa [hI] using hx, rfl⟩
  have him : ∀ x ∈ f '' s,
      x ∈ Submodule.span ℤ (Set.range B) ∧ ‖x‖ ≤ R := by
    rintro _ ⟨p, hp, rfl⟩
    constructor
    · apply (B.mem_span_iff_repr_mem ℤ (f p)).mpr
      intro i
      cases i with
      | inl i =>
        simpa [B, Basis.prod_repr_inl, f] using
          (b.mem_span_iff_repr_mem ℤ _).mp (hspan p.1 hp.1) i
      | inr i =>
        simpa [B, Basis.prod_repr_inr, f] using
          (b.mem_span_iff_repr_mem ℤ _).mp (hspan p.2 hp.2.1) i
    · apply norm_prod_le_iff.mpr
      exact ⟨mixed_norm_bound F p.1 R (by linarith) (fun φ => (hp.2.2 φ).1),
        mixed_norm_bound F p.2 R (by linarith) (fun φ => (hp.2.2 φ).2)⟩
  obtain ⟨hfin, hc⟩ := hbound R hR (f '' s) him
  have hsfin : s.Finite := Set.Finite.of_injOn (Set.mapsTo_image f s) hinj.injOn hfin
  refine ⟨hsfin, ?_⟩
  change (s.ncard : ℝ) ≤ _
  rw [Set.ncard_image_of_injective s hinj, hd] at hc
  exact hc

end DedekindZetaZeroFree

end
