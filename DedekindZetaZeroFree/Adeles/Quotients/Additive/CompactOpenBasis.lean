module

public import DedekindZetaZeroFree.Adeles.Characters.FractionalIdealOpenKernels

@[expose] public section

namespace DedekindZetaZeroFree.AdelicSeparation

open scoped NumberField
open NumberField IsDedekindDomain

theorem finiteAdeles_compactOpen_basis_zero
    (F : Type) [Field F] [NumberField F]
    (U : Set (FiniteAdeleRing (𝓞 F) F)) (hU : U ∈ nhds (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ K : AddSubgroup (FiniteAdeleRing (𝓞 F) F),
      IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      (K : Set (FiniteAdeleRing (𝓞 F) F)) ⊆ U := by
  classical
  obtain ⟨T, k, hTU⟩ := KPAdelicCharacter.finiteIdealNeighborhood_basis_nat F hU
  let K : AddSubgroup (FiniteAdeleRing (𝓞 F) F) :=
    { carrier := KPAdelicCharacter.finiteIdealNeighborhood F T (fun w => k w)
      zero_mem' := by
        intro v
        change Valued.v (0 : v.adicCompletion F) ≤ _
        simp
      add_mem' := by
        intro a b ha hb v
        change Valued.v (a v + b v) ≤ _
        exact (Valued.v.map_add _ _).trans (max_le (ha v) (hb v))
      neg_mem' := by
        intro a ha v
        change Valued.v (-a v) ≤ _
        simpa only [Valuation.map_neg] using ha v }
  have hKo : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)) :=
    KPAdelicCharacter.finiteIdealNeighborhood_open_nat F T k
  have hKi : (K : Set (FiniteAdeleRing (𝓞 F) F)) ⊆
      (KPAdelicTopology.integralAdeles F : Set _) := by
    intro a ha v
    apply (ha v).trans
    change WithZero.exp (-KPAdelicCharacter.idealExponent F T (fun w => k w) v) ≤ 1
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    apply neg_nonpos.mpr
    unfold KPAdelicCharacter.idealExponent
    split <;> positivity
  refine ⟨K, ?_, hKo, hTU⟩
  exact (KPAdelicTopology.integralAdeles_isCompact F).of_isClosed_subset
    (K.isClosed_of_isOpen hKo) hKi

end DedekindZetaZeroFree.AdelicSeparation
