module

public import DedekindZetaZeroFree.Adeles.Lattices.ArchimedeanIntegerLattice

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

def sIntegerDiagonalSubgroup (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : AddSubgroup (SLocalProduct F S) :=
  (sIntegerDiagonal F S).toAddMonoidHom.range

theorem sIntegerDiagonalSubgroup_exists_open_zero (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ W : Set (SLocalProduct F S), IsOpen W ∧ (0 : SLocalProduct F S) ∈ W ∧
      W ∩ (sIntegerDiagonalSubgroup F S : Set (SLocalProduct F S)) = {0} := by
  classical
  obtain ⟨B, U, _, hU, h0, _, hsep⟩ := sArchDomain_exists F
  let W : Set (SLocalProduct F S) := Prod.fst ⁻¹' U ∩
    ⋂ v : S, (fun x : SLocalProduct F S => x.2 v) ⁻¹' (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))
  have hW : IsOpen W := hU.preimage continuous_fst |>.inter
    (isOpen_iInter_of_finite fun v => (Valued.isOpen_valuationSubring (v.1.adicCompletion F)).preimage
      ((continuous_apply v).comp continuous_snd))
  have hW0 : (0 : SLocalProduct F S) ∈ W := by
    refine ⟨h0, Set.mem_iInter.mpr fun v => ?_⟩
    change (0 : v.1.adicCompletion F) ∈ v.1.adicCompletionIntegers F
    exact zero_mem _
  refine ⟨W, hW, hW0, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxW, hxL⟩
    obtain ⟨m, rfl⟩ := hxL
    have hm : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (m : F) ≤ 1 := by
      intro v
      have hvint : algebraMap F (v.adicCompletion F) (m : F) ∈
          v.adicCompletionIntegers F := by
        by_cases hv : v ∈ S
        · have hvW := Set.mem_iInter.mp hxW.2 ⟨v, hv⟩
          exact hvW
        · exact (mem_sIntegerRing_iff F S (m : F)).mp m.property v hv
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hvint
      change Valued.v ((m : F) : v.adicCompletion F) ≤ 1 at hvint
      rwa [HeightOneSpectrum.adicCompletion.valued_coe] at hvint
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (m : F) hm
    change (a : F) = (m : F) at ha
    have harch : algebraMap F (InfiniteAdeleRing F) (a : F) ∈ U := by
      rw [ha]
      exact hxW.1
    have ha0 := (hsep a).mp harch
    have hm0 : (m : F) = 0 := by
      rw [← ha, ha0]
      exact map_zero _
    have : m = 0 := Subtype.ext hm0
    simp [this]
  · intro x hx
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨hW0, (sIntegerDiagonalSubgroup F S).zero_mem⟩

theorem sIntegerDiagonalSubgroup_discreteTopology (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    DiscreteTopology (sIntegerDiagonalSubgroup F S) := by
  obtain ⟨W, hW, _, hsep⟩ := sIntegerDiagonalSubgroup_exists_open_zero F S
  apply discreteTopology_of_isOpen_singleton_zero
  have heq : (Subtype.val : sIntegerDiagonalSubgroup F S → SLocalProduct F S) ⁻¹' W = {0} := by
    ext x
    have hx : (x : SLocalProduct F S) ∈ sIntegerDiagonalSubgroup F S := x.property
    have he : (x : SLocalProduct F S) ∈ W ↔ (x : SLocalProduct F S) = 0 := by
      have := Set.ext_iff.mp hsep (x : SLocalProduct F S)
      simpa [hx] using this
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff, ZeroMemClass.coe_zero] using he
  rw [← heq]
  exact hW.preimage continuous_subtype_val

theorem sIntegerDiagonalSubgroup_isClosed (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsClosed (sIntegerDiagonalSubgroup F S : Set (SLocalProduct F S)) := by
  letI := sIntegerDiagonalSubgroup_discreteTopology F S
  exact AddSubgroup.isClosed_of_discreteTopology

end DedekindZetaZeroFree

end
