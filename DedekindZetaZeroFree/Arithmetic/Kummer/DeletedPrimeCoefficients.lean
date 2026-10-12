module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.MaskedPrimitiveInducers

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic
noncomputable section
open scoped Classical NumberField
open IsDedekindDomain LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]

 def rawValuationIdeal (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ A.Sf) : Ideal A.R where
  carrier := {r | v.valuation F (r : F) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change v.valuation F ((x : F) + (y : F)) < 1
    exact (ValuationClass.map_add_le_max _ _ _).trans_lt (max_lt hx hy)
  smul_mem' := by
    intro x y hy
    change v.valuation F ((x : F) * (y : F)) < 1
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (x.property v hv) zero_le).trans_lt (by simpa using hy)

theorem source_kummer_raw_prime_values
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (χ : Detector.PrimitiveFrequencyCharacter F)
    (hχ : Detector.IsKummerFrequencyCharacter F A.zeta12 σ
      (A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
      (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1)) χ) :
    Detector.conductorSupportedOn F (RawHeckeRows.rawDeletionSet U) χ ∧
    ∀ p : LocalFiniteSums.ExteriorPrime A,
      AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U
        (LocalFiniteSums.primeIdeal p) =
      if U.ideal.val ≤ p.val.asIdeal then 0 else χ.character p.val.asIdeal := by
  classical
  constructor
  ·
    intro v hvle
    by_contra hvD
    simp only [RawHeckeRows.rawDeletionSet, Set.mem_union, Set.mem_setOf_eq, not_or] at hvD
    obtain ⟨hvSf, hnot⟩ := hvD
    have huval : v.valuation F (U.u : F) = 1 :=
      ArithmeticContext.actual_generator_valuation_unit A U.ideal U.u
        (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1)) U.generates rfl v hvSf hnot
    obtain ⟨hcop, _⟩ := hχ v hvSf huval
    have htop : (⊤ : Ideal (𝓞 F)) ≤ v.asIdeal := by rw [← hcop]; exact sup_le le_rfl hvle
    exact v.isPrime.ne_top (top_unique htop)
  ·
    intro p
    have hvSf : p.val ∉ A.Sf :=
      ArithmeticContext.actual_exterior_prime_outside A (primeIdeal p) p.val rfl
    by_cases hle : U.ideal.val ≤ p.val.asIdeal
    ·
      rw [if_pos hle]
      change AllRowEuler.UnitCovariance.residueCoefficient σ (primeIdeal p) U.u = 0
      have hu : Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u = 0 := by
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        have h1 : U.u ∈ Ideal.span {U.u} := Ideal.mem_span_singleton_self U.u
        rw [U.generates.2] at h1
        exact Ideal.map_mono hle h1
      have hres : A.sexticResidue (primeIdeal p) U.u = 0 := by
        unfold SArithmeticData.sexticResidue SArithmeticData.residueValue
        rw [hu, MulChar.map_zero]
      rw [AllRowEuler.UnitCovariance.residueCoefficient_eq, hres, map_zero]
    ·
      rw [if_neg hle]
      have huval : p.val.valuation F (U.u : F) = 1 :=
        ArithmeticContext.actual_generator_valuation_unit A U.ideal U.u
          (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1)) U.generates rfl p.val hvSf hle
      obtain ⟨hpc, j, hjval, hjchar⟩ := hχ p.val hvSf huval
      let z : A.R := algebraMap (𝓞 F) A.R A.primitive_zeta12.toInteger
      have hz : (z : F) = A.zeta12 := A.primitive_zeta12.coe_toInteger
      have hlt : p.val.valuation F
          ((U.u ^ ((Ideal.absNorm p.val.asIdeal - 1) / 6) - z ^ (2 * j.val) : A.R) : F) < 1 := by
        simpa only [Units.val_mk0, Subalgebra.coe_sub, Subalgebra.coe_pow, hz, pow_mul] using hjval
      let q := Ideal.Quotient.mk (A.extendIdeal (primeIdeal p))
      have hzero : q (U.u ^ ((Ideal.absNorm p.val.asIdeal - 1) / 6) - z ^ (2 * j.val)) = 0 := by
        apply (A.exteriorLocalResidueEquiv (primeIdeal p) p.val rfl).injective
        rw [map_zero]
        change (A.exteriorLocalResidueEquiv (primeIdeal p) p.val rfl)
          (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) _) = 0
        rw [A.exteriorLocalResidueEquiv_apply (primeIdeal p) p.val rfl]
        apply (IsLocalRing.residue_eq_zero_iff _).mpr
        apply (Valuation.mem_maximalIdeal_iff (p.val.adicCompletion F) Valued.v).mpr
        change Valued.v ((WithVal.toVal (p.val.valuation F)
          ((U.u ^ ((Ideal.absNorm p.val.asIdeal - 1) / 6) - z ^ (2 * j.val) : A.R) : F) :
          WithVal (p.val.valuation F)) : p.val.adicCompletion F) < 1
        rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      have hred : q (z ^ (2 * j.val)) = q U.u ^ ((Ideal.absNorm p.val.asIdeal - 1) / 6) := by
        rw [map_sub, map_pow] at hzero
        exact (sub_eq_zero.mp hzero).symm

      have hmap_extend_le : A.extendIdeal (primeIdeal p) ≤ rawValuationIdeal A p.val hvSf := by
        apply Ideal.map_le_iff_le_comap.mpr
        intro a ha
        change p.val.valuation F (((algebraMap (𝓞 F) A.R) a : A.R) : F) < 1
        have hcoe : (((algebraMap (𝓞 F) A.R) a : A.R) : F) = algebraMap (𝓞 F) F a := rfl
        rw [hcoe]
        exact (p.val.valuation_lt_one_iff_mem (K := F) a).mpr ha
      have hunit : IsUnit (q U.u) := by
        have hmax : (A.extendIdeal (primeIdeal p)).IsMaximal := by
          apply Ideal.Quotient.maximal_of_isField
          exact (A.exteriorLocalResidueEquiv (primeIdeal p) p.val rfl).toMulEquiv.isField
            (Field.toIsField (SArithmeticData.exteriorLocalResidue p.val))
        haveI := hmax
        rw [isUnit_iff_ne_zero]
        intro hz0
        have hmem : U.u ∈ A.extendIdeal (primeIdeal p) := Ideal.Quotient.eq_zero_iff_mem.mp hz0
        have hlt' : p.val.valuation F (U.u : F) < 1 := hmap_extend_le hmem
        rw [huval] at hlt'
        exact lt_irrefl 1 hlt'
      obtain ⟨u, hu⟩ := hunit
      obtain ⟨k, hk, hkchar, hkred⟩ :=
        A.sexticResidueFamily_normalized.2.1 (primeIdeal p) p.val rfl u
      rw [A.exteriorResidue_card (primeIdeal p), hu] at hkred
      have hkj : k = j.val :=
        (A.exterior_sextic_primitive (primeIdeal p) p.val.isPrime.ne_top).pow_inj hk j.isLt (by
          have hh := hkred.trans hred.symm
          simpa only [z, ← map_pow, pow_mul] using hh)
      have hres : A.sexticResidue (primeIdeal p) U.u = (A.zeta12 ^ 2) ^ j.val := by
        have h1 : A.sexticResidue (primeIdeal p) U.u =
            ((A.sexticResidueFamily (primeIdeal p)) u : F) := by
          unfold SArithmeticData.sexticResidue SArithmeticData.residueValue
          rw [← hu, MulChar.ofUnitHom_coe]
        rw [h1, hkchar, hkj, pow_mul]
      change AllRowEuler.UnitCovariance.residueCoefficient σ (primeIdeal p) U.u =
        χ.character p.val.asIdeal
      rw [AllRowEuler.UnitCovariance.residueCoefficient_eq, hres, ← hjchar]

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic
