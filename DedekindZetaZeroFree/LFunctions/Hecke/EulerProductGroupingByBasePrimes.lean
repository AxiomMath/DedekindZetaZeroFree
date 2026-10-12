module

public import DedekindZetaZeroFree.LFunctions.Hecke.IdealSeriesEulerProducts
public import DedekindZetaZeroFree.Arithmetic.Ideals.FinitePrimeContractionFibers

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

universe u v

theorem hasProd_tprod_finite_fibers
    {P : Type u} {Q : Type v} (c : Q → P)
    (hfinite : ∀ p, Finite {q : Q // c q = p}) (A : Q → ℂ) (z : ℂ)
    (hA : HasProd A z) :
    HasProd (fun p : P => ∏' q : {q : Q // c q = p}, A q.val) z := by
  classical
  have hfib : ∀ p : P, HasProd (fun q : {q : Q // c q = p} => A q.val)
      (∏' q : {q : Q // c q = p}, A q.val) := by
    intro p
    letI : Fintype {q : Q // c q = p} := Fintype.ofFinite _
    simpa using hasProd_fintype (fun q : {q : Q // c q = p} => A q.val)
  have hsigma : HasProd (fun x : Σ p : P, {q : Q // c q = p} => A x.2.val) z :=
    ((Equiv.sigmaFiberEquiv c).hasProd_iff).mpr hA
  exact HasProd.sigma hsigma hfib

theorem principal_idealHeckeL_euler_grouped_hasProd
    (F E : Type) [Field F] [Field E] [NumberField F] [NumberField E]
    [Algebra F E] (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      ∏' Q : {Q : IsDedekindDomain.HeightOneSpectrum (𝓞 E) //
        Q.asIdeal.LiesOver p.asIdeal},
        (1 - (Ideal.absNorm Q.val.asIdeal : ℂ) ^ (-s))⁻¹)
      (idealHeckeL (principalUnitRayCharacter E) s) := by
  classical
  have h := hasProd_tprod_finite_fibers
    (fun Q : IsDedekindDomain.HeightOneSpectrum (𝓞 E) => Q.under (𝓞 F))
    (fun p => IdealEuler.finite_prime_under_fiber p)
    (fun Q => (1 - (Ideal.absNorm Q.asIdeal : ℂ) ^ (-s))⁻¹)
    (idealHeckeL (principalUnitRayCharacter E) s)
    (principal_idealHeckeL_euler_hasProd E s hs)
  refine h.congr_fun fun p => ?_
  exact Equiv.tprod_eq
    (Equiv.subtypeEquivRight fun Q =>
      (IdealEuler.under_eq_iff_liesOver Q p).symm)
    (fun Q : {Q : IsDedekindDomain.HeightOneSpectrum (𝓞 E) //
        Q.under (𝓞 F) = p} =>
      (1 - (Ideal.absNorm Q.val.asIdeal : ℂ) ^ (-s))⁻¹)

end DedekindZetaZeroFree.LargeSieve
