module

public import DedekindZetaZeroFree.Arithmetic.Ideals.PrimeFreeFactorization
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.PrimeFreeGenerators

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.CorrectionFactors.ValuationGenerator
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem exists_unitPart (C : A.GeneralArithmeticContext σ η hS)
    (I : A.Exterior) (u : A.R) (hu : A.Generates I u) (p : ExteriorPrime A) :
    ∃ v : A.R, u = generator C p ^ idealPrimeExponent p.val.asIdeal I.val * v ∧
      IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) v) := by
  obtain ⟨J, hJ, hnot⟩ := Exponent.exists_primeFree I p
  obtain ⟨r, a, hr, har, ha⟩ := C.allowed_integral J
  have hspan : Ideal.span {generator C p ^ idealPrimeExponent p.val.asIdeal I.val * r} =
      Ideal.span {u} := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow,
      (generator_generates C p).2, hr.2, hu.2]
    change Ideal.map (algebraMap (𝓞 F) A.R) p.val.asIdeal ^ _ *
      Ideal.map (algebraMap (𝓞 F) A.R) J.val =
      Ideal.map (algebraMap (𝓞 F) A.R) I.val
    conv_rhs => rw [hJ, Ideal.map_mul, Ideal.map_pow]
  obtain ⟨eps, heps⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨(eps : A.R) * r, ?_, ?_⟩
  · rw [← heps]
    ring
  · rw [map_mul]
    exact (eps.isUnit.map _).mul (LocalAlgebra.generator_residue_unit J r hr p hnot)

theorem chi_eq_zero_of_decomposition (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (u v : A.R) (n : ℕ) (hn : n ≠ 0)
    (hu : u = generator C p ^ n * v) :
    chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u) = 0 := by
  have hgen : Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (generator C p) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← (generator_generates C p).2]
    exact Ideal.mem_span_singleton_self _
  rw [hu, map_mul, map_pow, hgen, zero_pow hn, zero_mul, MulChar.map_zero]

end DedekindZetaZeroFree.CorrectionFactors.ValuationGenerator

end
