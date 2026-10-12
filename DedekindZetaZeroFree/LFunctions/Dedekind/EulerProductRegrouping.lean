module

public import DedekindZetaZeroFree.LFunctions.Dedekind.WeightedIdealEulerProducts

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField BigOperators

theorem primeEulerRegroup
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (s : ℂ) (hs : 1 < s.re) :
    HasProd
      (fun p : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
        ∏ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L),
          (1 - (Ideal.absNorm Q : ℂ) ^ (-s))⁻¹)
      (NumberField.dedekindZeta L s) := by
  classical
  let u : IsDedekindDomain.HeightOneSpectrum (𝓞 L) →
      IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    IsDedekindDomain.HeightOneSpectrum.under (𝓞 K)
  have hprod := (Equiv.sigmaFiberEquiv u).hasProd_iff.mpr
    (dedekindZeta_idealEulerProduct_hasProd L s hs)
  refine hprod.sigma fun p => ?_
  let e : {Q : IsDedekindDomain.HeightOneSpectrum (𝓞 L) // u Q = p} ≃
      {Q : Ideal (𝓞 L) // Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L)} :=
    { toFun := fun Q => ⟨Q.1.asIdeal, by
        apply (IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot (𝓞 L)).mpr
        refine ⟨Q.1.isPrime, ?_⟩
        exact ⟨(congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal Q.2).symm⟩⟩
      invFun := fun Q => by
        have hQ := (IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot (𝓞 L)).mp Q.2
        refine ⟨⟨Q.1, hQ.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot hQ⟩, ?_⟩
        apply IsDedekindDomain.HeightOneSpectrum.ext
        exact hQ.2.over.symm
      left_inv := fun Q => by
        apply Subtype.ext
        apply IsDedekindDomain.HeightOneSpectrum.ext
        rfl
      right_inv := fun Q => by
        apply Subtype.ext
        rfl }
  letI := Fintype.ofEquiv _ e.symm
  change HasProd
    (fun Q : {Q : IsDedekindDomain.HeightOneSpectrum (𝓞 L) // u Q = p} =>
      (1 - (Ideal.absNorm Q.1.asIdeal : ℂ) ^ (-s))⁻¹)
    (∏ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L),
      (1 - (Ideal.absNorm Q : ℂ) ^ (-s))⁻¹)
  rw [← Finset.prod_coe_sort,
    ← Fintype.prod_equiv e
      (fun Q => (1 - (Ideal.absNorm Q.1.asIdeal : ℂ) ^ (-s))⁻¹)
      (fun Q => (1 - (Ideal.absNorm Q.1 : ℂ) ^ (-s))⁻¹) (fun Q => rfl)]
  exact hasProd_fintype _

end DedekindZetaZeroFree.AbelianQuotient
