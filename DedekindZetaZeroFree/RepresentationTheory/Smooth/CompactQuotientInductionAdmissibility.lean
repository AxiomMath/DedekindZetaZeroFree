module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.EquivariantSmoothSections

@[expose] public section

namespace DedekindZetaZeroFree

open scoped Topology NNReal

section CompactQuotient

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [AddCommGroup E] [Module ℂ E]
    (H : Subgroup G) (τ : Representation ℂ H E) (d : H →* (ℝ≥0)ˣ)

theorem section_doubleCoset_finite_of_compact_quotient
    (hH : IsClosed (H : Set G))
    (hquotient : IsCompact (Set.univ : Set (SectionCosetSpace H)))
    (J : OpenSubgroup G) :
    Finite (DoubleCoset.Quotient (H : Set G) (J : Set G)) := by
  classical
  let q : G → SectionCosetSpace H := Quotient.mk (QuotientGroup.rightRel H)
  let O : G → Set (SectionCosetSpace H) := fun g => q '' ((fun u => g * u) '' (J : Set G))
  have hopen : ∀ g, IsOpen (O g) := fun g =>
    isOpenMap_quotient_mk'_mul _ (isOpenMap_mul_left g _ J.isOpen)
  have hcover : (Set.univ : Set (SectionCosetSpace H)) ⊆ ⋃ g, O g := by
    intro x _
    obtain ⟨g, rfl⟩ := Quotient.mk_surjective x
    exact Set.mem_iUnion.mpr ⟨g, ⟨g, ⟨1, J.one_mem, mul_one g⟩, rfl⟩⟩
  obtain ⟨s, hs⟩ := hquotient.elim_finite_subcover O hopen hcover
  apply Finite.of_surjective (fun a : s => DoubleCoset.mk H (J : Subgroup G) a.val)
  intro x
  let g := x.out
  obtain ⟨a, ha, y, ⟨u, hu, rfl⟩, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ (q g)))
  have hrel : g * (a * u)⁻¹ ∈ H :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hx)
  refine ⟨⟨a, ha⟩, ?_⟩
  rw [← DoubleCoset.out_eq' x, DoubleCoset.eq]
  exact ⟨g * (a * u)⁻¹, hrel, u, hu, by simp [g, mul_assoc]⟩

theorem section_finite_doubleCoset_representatives
    (hH : IsClosed (H : Set G))
    (hquotient : IsCompact (Set.univ : Set (SectionCosetSpace H)))
    (J : OpenSubgroup G) :
    ∃ (n : ℕ) (r : Fin n → G),
      Function.Bijective (fun i => DoubleCoset.mk H (J : Subgroup G) (r i)) := by
  classical
  letI := section_doubleCoset_finite_of_compact_quotient H hH hquotient J
  letI := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (J : Set G))
  let e := (Fintype.equivFin (DoubleCoset.Quotient (H : Set G) (J : Set G))).symm
  refine ⟨Fintype.card (DoubleCoset.Quotient (H : Set G) (J : Set G)),
    fun i => (e i).out, ?_⟩
  simpa only [DoubleCoset.out_eq'] using e.bijective

end CompactQuotient

section Evaluation

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup E] [Module ℂ E]
    (H : Subgroup G) (τ : Representation ℂ H E) (d : H →* (ℝ≥0)ˣ)

def smoothIndFixedEvaluation {ι : Type*} (J : Subgroup G) (r : ι → G) :
    fixedSubmodule (V := SmoothInd H τ d) (smoothIndRepresentation H τ d) J →ₗ[ℂ] (ι → E) where
  toFun f i := f.val.val.val (r i)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem smoothIndFixedEvaluation_apply {ι : Type*}
    (J : Subgroup G) (r : ι → G)
    (f : fixedSubmodule (V := SmoothInd H τ d) (smoothIndRepresentation H τ d) J) (i : ι) :
    smoothIndFixedEvaluation H τ d J r f i = f.val.val.val (r i) := rfl

theorem smoothIndFixedEvaluation_injective {ι : Type*}
    (J : Subgroup G) (r : ι → G)
    (hr : Function.Surjective (fun i => DoubleCoset.mk H J (r i))) :
    Function.Injective (smoothIndFixedEvaluation H τ d J r) := by
  intro x y hxy
  have hfix (z : fixedSubmodule (V := SmoothInd H τ d)
      (smoothIndRepresentation H τ d) J) (a j : G) (hj : j ∈ J) :
      z.val.val.val (a * j) = z.val.val.val a := by
    have he := z.property ⟨j, hj⟩
    exact congrArg (fun (t : SmoothInd H τ d) => t.val.val a) he
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  obtain ⟨i, hi⟩ := hr (DoubleCoset.mk H J g)
  obtain ⟨a, ha, j, hj, hg⟩ := DoubleCoset.eq.mp hi
  let aH : H := ⟨a, ha⟩
  have hg' : g = (aH : G) * r i * j := hg
  rw [hg', mul_assoc, x.val.val.property aH, y.val.val.property aH]
  congr 1
  calc
    x.val.val.val (r i * j) = x.val.val.val (r i) := hfix x (r i) j hj
    _ = y.val.val.val (r i) := congrFun hxy i
    _ = y.val.val.val (r i * j) := (hfix y (r i) j hj).symm

end Evaluation

section Admissibility

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [AddCommGroup E] [Module ℂ E]
    (H : Subgroup G) (τ : Representation ℂ H E) (d : H →* (ℝ≥0)ˣ)

theorem smoothInd_open_fixed_finite_of_compact_quotient
    [Module.Finite ℂ E]
    (hH : IsClosed (H : Set G))
    (hquotient : IsCompact (Set.univ : Set (SectionCosetSpace H)))
    (J : OpenSubgroup G) :
    Module.Finite ℂ
      (fixedSubmodule (V := SmoothInd H τ d) (smoothIndRepresentation H τ d) (J : Subgroup G)) := by
  obtain ⟨n, r, hr⟩ := section_finite_doubleCoset_representatives H hH hquotient J
  exact Module.Finite.of_injective (smoothIndFixedEvaluation H τ d (J : Subgroup G) r)
    (smoothIndFixedEvaluation_injective H τ d (J : Subgroup G) r hr.2)

theorem smoothInd_admissible_of_compact_quotient
    [Module.Finite ℂ E]
    (hH : IsClosed (H : Set G))
    (hquotient : IsCompact (Set.univ : Set (SectionCosetSpace H))) :
    Admissible (G := G) (V := SmoothInd H τ d) (smoothIndRepresentation H τ d) := by
  intro J
  exact smoothInd_open_fixed_finite_of_compact_quotient H τ d hH hquotient J.toOpenSubgroup

end Admissibility

end DedekindZetaZeroFree
