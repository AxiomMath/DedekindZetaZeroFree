module

public import DedekindZetaZeroFree.LFunctions.Hecke.EulerProductGroupingByBasePrimes

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem idealHeckeL_absolute_euler_product
    {F : Type} [Field F] [NumberField F] {f : Ideal (𝓞 F)}
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (s : ℂ)
    (hf : f ≠ ⊥) (hη : ∀ I, ‖η I‖ ≤ 1) (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 F) => η I * (Ideal.absNorm I : ℂ) ^ (-s)) ∧
      HasProd (fun p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
        (1 - η p.asIdeal * (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))⁻¹)
        (idealHeckeL η s) := by
  exact ⟨idealHeckeL_summable η s hf hη hs, idealHeckeL_euler_hasProd η s hf hη hs⟩

theorem principal_idealHeckeL_absolute_euler_product
    (F : Type) [Field F] [NumberField F] (s : ℂ) (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 F) =>
      principalUnitRayCharacter F I * (Ideal.absNorm I : ℂ) ^ (-s)) ∧
      HasProd (fun p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
        (1 - (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))⁻¹)
        (idealHeckeL (principalUnitRayCharacter F) s) ∧
      idealHeckeL (principalUnitRayCharacter F) s =
        ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, (Ideal.absNorm I.val : ℂ) ^ (-s) := by
  exact ⟨principal_idealHeckeL_summable F s hs,
    principal_idealHeckeL_euler_hasProd F s hs,
    principal_idealHeckeL_eq_tsum_nonzero F s⟩

theorem principal_idealHeckeL_euler_finite_fibers_grouped
    (F E : Type) [Field F] [Field E] [NumberField F] [NumberField E]
    [Algebra F E] (s : ℂ) (hs : 1 < s.re) :
    (∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      Finite {Q : IsDedekindDomain.HeightOneSpectrum (𝓞 E) //
        Q.asIdeal.LiesOver p.asIdeal}) ∧
      HasProd (fun p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
        ∏' Q : {Q : IsDedekindDomain.HeightOneSpectrum (𝓞 E) //
          Q.asIdeal.LiesOver p.asIdeal},
          (1 - (Ideal.absNorm Q.val.asIdeal : ℂ) ^ (-s))⁻¹)
        (idealHeckeL (principalUnitRayCharacter E) s) := by
  exact ⟨fun p => IdealEuler.finite_prime_liesOver (F := F) (E := E) p,
    principal_idealHeckeL_euler_grouped_hasProd F E s hs⟩

end DedekindZetaZeroFree.LargeSieve
