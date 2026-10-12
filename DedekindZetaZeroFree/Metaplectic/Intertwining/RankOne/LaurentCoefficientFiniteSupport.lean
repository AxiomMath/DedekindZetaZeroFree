module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.LaurentCoefficientOperator

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation

private theorem finite_detection {V I : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (l : I → V →ₗ[ℂ] ℂ)
    (hl : ∀ v, (∀ i, l i v = 0) → v = 0) :
    ∃ d : Finset I, ∀ v, (∀ i ∈ d, l i v = 0) → v = 0 := by
  classical
  let p : Finset I → Submodule ℂ V := fun d => ⨅ i ∈ d, (l i).ker
  obtain ⟨a, ha, hmin⟩ := WellFoundedLT.exists_minimal (α := Submodule ℂ V) inferInstance
    (Set.range p) ⟨p ∅, ∅, rfl⟩
  obtain ⟨d, rfl⟩ := ha
  refine ⟨d, ?_⟩
  intro v hv
  apply hl v
  intro i
  have hle : p (insert i d) ≤ p d := iInf_le_iInf_of_subset (Finset.subset_insert i d)
  have he : p d ≤ p (insert i d) := hmin ⟨insert i d, rfl⟩ hle
  have hd : v ∈ p d := by simpa only [p, Submodule.mem_iInf, LinearMap.mem_ker] using hv
  have hi' : p (insert i d) ≤ (l i).ker :=
    iInf_le_of_le i (iInf_le_of_le (Finset.mem_insert_self i d) le_rfl)
  exact hi' (he hd)

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)
  (P : Polarization S.heisenberg)
  (J : CompactOpenLevel (ActualCover F ζ hζ q))
  (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (π : (LocalField F q)ˣ)
  (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
  (ε : Sign)

theorem actualCoefficientOperator_finite_support :
    {n : ℤ | actualCoefficientOperator F ζ hζ q S P J hJ μ hμ π hπ ε n ≠ 0}.Finite := by
  classical
  let V : Type := compactLevel S.borel P S.iwasawa (sourceSign ε) J
  let W : Type := compactLevel S.borel P S.iwasawa (targetSign ε) J
  letI : Module.Finite ℂ V := compact_level_finite S.borel P S.iwasawa _ J hJ
  letI : Module.Finite ℂ W := compact_level_finite S.borel P S.iwasawa _ J hJ
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  letI : Module ℂ V := inferInstanceAs (Module ℂ (compactLevel S.borel P S.iwasawa (sourceSign ε) J))
  letI : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  letI : Module ℂ W := inferInstanceAs (Module ℂ (compactLevel S.borel P S.iwasawa (targetSign ε) J))
  let b := Module.finBasis ℂ V
  let l : (S.iwasawa.compact.toOpenSubgroup × actualTorus F ζ hζ q) → W →ₗ[ℂ] ℂ :=
    fun z => { toFun := fun w => (w.val.val z.1).val z.2
               map_add' := by intros; rfl
               map_smul' := by intros; rfl }
  obtain ⟨d, hd⟩ := finite_detection l (by
    intro w hw
    apply Subtype.ext
    apply Subtype.ext
    funext k
    apply Subtype.ext
    funext h
    exact hw (k, h))
  let N : Finset ℤ := Finset.univ.biUnion (fun i => d.biUnion (fun z =>
    (actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε (b i) z.1 z.2).support))
  apply N.finite_toSet.subset
  intro n hn
  by_contra hnot
  apply hn
  apply b.ext
  intro i
  apply hd
  intro z hz
  have hns : n ∉ (actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε (b i) z.1 z.2).support := by
    intro hmem
    apply hnot
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨z, hz, hmem⟩⟩
  change ((actualCoefficientOperator F ζ hζ q S P J hJ μ hμ π hπ ε n (b i)).val.val z.1).val z.2 = 0
  rw [actualCoefficientOperator_coordinate]
  exact Finsupp.notMem_support_iff.mp hns

end DedekindZetaZeroFree.KPRankOneShellRepair

end
