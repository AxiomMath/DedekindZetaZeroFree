module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.IntegralIdealClasses
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealFactorization

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.AbelianQuotient

theorem rayClassFinitePrimeFactorization
    (K : Type) [Field K] [NumberField K]
    (μ : ClassFieldTheory.RayClassModulus K)
    (c : ClassFieldTheory.RayClassGroup μ) :
    let V := {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) //
      v ∉ μ.finitePart.support}
    ∃ (s : Finset V) (e : V → ℤ),
      c = ∏ v ∈ s,
        (ClassFieldTheory.rayClassOfFinitePrime μ v.val v.property) ^ e v := by
  classical
  let V := {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) //
    v ∉ μ.finitePart.support}
  obtain ⟨J, rfl⟩ := QuotientGroup.mk'_surjective
    (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo μ) c
  let f := ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector J.val
  have hf : ∀ v ∈ f.support, v ∉ μ.finitePart.support := by
    intro v hv hμ
    have hz := J.property v hμ
    exact (Finsupp.mem_support_iff.mp hv) hz
  let s : Finset V := f.support.subtype (fun v => v ∉ μ.finitePart.support)
  let P : V → ClassFieldTheory.rayClassPrimeToIdeals μ := fun v =>
    ⟨ClassFieldTheory.finitePrimeFractionalIdeal v.val, by
      intro w hw
      exact FractionalIdeal.count_maximal_coprime K w
        (fun h => (h ▸ v.property) hw)⟩
  have hfac : J.val = ∏ v ∈ f.support,
      ClassFieldTheory.finitePrimeFractionalIdeal v ^ f v := by
    have h := ClassFieldTheory.NumberFieldFractionalIdealGroup.ext_count
      (I := ClassFieldTheory.NumberFieldFractionalIdealGroup.factorization
        (Multiplicative.ofAdd f)) (J := J.val) (fun v => by
          rw [ClassFieldTheory.NumberFieldFractionalIdealGroup.count_factorization]
          exact ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector_apply J.val v)
    exact h.symm
  have hJ : J = ∏ v ∈ s, P v ^ f v.val := by
    apply Subtype.ext
    change J.val = (ClassFieldTheory.rayClassPrimeToIdeals μ).subtype
      (∏ v ∈ s, P v ^ f v.val)
    rw [map_prod]
    simp only [map_zpow]
    exact hfac.trans (Finset.prod_subtype_of_mem
      (fun v => ClassFieldTheory.finitePrimeFractionalIdeal v ^ f v) hf).symm
  refine ⟨s, (fun v => f v.val), ?_⟩
  rw [hJ, map_prod]
  simp only [map_zpow]
  rfl

end DedekindZetaZeroFree.AbelianQuotient
