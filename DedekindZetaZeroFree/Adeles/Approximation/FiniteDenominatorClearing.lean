module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

@[expose] public section

namespace DedekindZetaZeroFree
open IsDedekindDomain

set_option backward.isDefEq.respectTransparency false in

theorem finiteAdele_exists_integral_denominator
    (F : Type*) [Field F] [NumberField F]
    (z : FiniteAdeleRing (NumberField.RingOfIntegers F) F) :
    ∃ d : NumberField.RingOfIntegers F, d ≠ 0 ∧
      ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers F),
        (algebraMap (NumberField.RingOfIntegers F)
          (FiniteAdeleRing (NumberField.RingOfIntegers F) F) d * z) v ∈
          v.adicCompletionIntegers F := by
  classical
  let R := NumberField.RingOfIntegers F
  have hfinite : {v : HeightOneSpectrum R | z v ∉ v.adicCompletionIntegers F}.Finite :=
    z.cofinite_mem_adicCompletionIntegers
  let T := hfinite.toFinset
  have hclear : ∀ s : Finset (HeightOneSpectrum R),
      ∃ d : R, d ≠ 0 ∧ ∀ v ∈ s,
        algebraMap R (v.adicCompletion F) d * z v ∈ v.adicCompletionIntegers F := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | @insert v s hv ih =>
      obtain ⟨d, hd, hds⟩ := ih
      obtain ⟨b, hb, hzb⟩ :=
        HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (z v)
      refine ⟨b * d, mul_ne_zero (nonZeroDivisors.ne_zero hb) hd, ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · have hi := (w.adicCompletionIntegers F).toSubring.mul_mem
          (w.coe_mem_adicCompletionIntegers (K := F) d) hzb
        simpa only [Algebra.cast, map_mul, mul_comm, mul_left_comm, mul_assoc,
          ValuationSubring.mem_toSubring] using hi
      · have hi := (w.adicCompletionIntegers F).mul_mem _ _
          (w.coe_mem_adicCompletionIntegers (K := F) b) (hds w hw)
        simpa only [Algebra.cast, map_mul, mul_assoc] using hi
  obtain ⟨d, hd, hds⟩ := hclear T
  refine ⟨d, hd, ?_⟩
  intro v
  change algebraMap R (v.adicCompletion F) d * z v ∈ v.adicCompletionIntegers F
  by_cases hv : v ∈ T
  · exact hds v hv
  · have hz : z v ∈ v.adicCompletionIntegers F := by
      by_contra hn
      exact hv (hfinite.mem_toFinset.mpr hn)
    exact (v.adicCompletionIntegers F).mul_mem _ _
      (v.coe_mem_adicCompletionIntegers (K := F) d) hz

theorem finiteAdele_exists_integral_denominator_mem_range
    (F : Type*) [Field F] [NumberField F]
    (z : FiniteAdeleRing (NumberField.RingOfIntegers F) F) :
    ∃ d : NumberField.RingOfIntegers F, d ≠ 0 ∧
      algebraMap (NumberField.RingOfIntegers F)
          (FiniteAdeleRing (NumberField.RingOfIntegers F) F) d * z ∈
        Set.range (RestrictedProduct.structureMap
          (fun v : HeightOneSpectrum (NumberField.RingOfIntegers F) => v.adicCompletion F)
          (fun v : HeightOneSpectrum (NumberField.RingOfIntegers F) => v.adicCompletionIntegers F)
          Filter.cofinite) := by
  obtain ⟨d, hd, hcoords⟩ := finiteAdele_exists_integral_denominator F z
  refine ⟨d, hd, ?_⟩
  rw [RestrictedProduct.range_structureMap]
  exact hcoords
end DedekindZetaZeroFree
