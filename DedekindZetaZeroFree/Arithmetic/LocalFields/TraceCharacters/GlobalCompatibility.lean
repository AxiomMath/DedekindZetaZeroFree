module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.Residues.GlobalQuotientEquivalence

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSumCompatibility
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem cast_character_mk {R : Type} [CommRing R]
    (I J : Ideal R) (h : I = J) (f : AddChar (R ⧸ I) Circle) (x : R) :
    (cast (congrArg (fun L : Ideal R => AddChar (R ⧸ L) Circle) h) f)
      (Ideal.Quotient.mk J x) = f (Ideal.Quotient.mk I x) := by
  cases h
  rfl

private theorem power_generates (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    A.Generates (powerIdeal p n) (generator C p ^ n) := by
  refine ⟨pow_ne_zero _ (generator_generates C p).1, ?_⟩
  rw [← Ideal.span_singleton_pow, (generator_generates C p).2]
  exact (Ideal.map_pow _ _ _).symm

theorem fieldTrace_eq_negative_localTrace
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (n : ℕ) (x : A.R) :
    A.fieldTraceCharacter ((x : F) / (generator C p : F) ^ n) =
      negativeTrace p (algebraMap F (LocalField p) (x : F) / uniformizer C p ^ n) := by
  have hv : p.val ∉ A.Sf := by
    intro hv
    have h := (A.exterior_iff ⟨p.val.asIdeal, p.val.ne_bot⟩).mp p.property p.val hv
    rw [sup_idem] at h
    exact p.val.isPrime.ne_top h
  have hout (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ A.Sf) (hwp : w ≠ p.val) :
      ResidueTrace.localTraceCharacter w
        (algebraMap F (w.adicCompletion F) ((x : F) / (generator C p : F) ^ n)) = 1 := by
    have hnle : ¬ p.val.asIdeal ≤ w.asIdeal := by
      intro h
      have heq := (p.val.isPrime.isMaximal p.val.ne_bot).eq_of_le (w.isPrime.ne_top) h
      exact hwp (HeightOneSpectrum.ext heq.symm)
    obtain ⟨t, ht, htw⟩ := SetLike.not_le_iff_exists.mp hnle
    have htR : algebraMap (𝓞 F) A.R t ∈ Ideal.span {generator C p} := by
      rw [(generator_generates C p).2]
      exact Ideal.mem_map_of_mem _ ht
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp htR
    have hmul : (t : F) = (y : F) * (generator C p : F) := by
      exact (congrArg (fun z : A.R => (z : F)) hy).symm
    have htval := (w.valuation_eq_one_iff_notMem (K := F)).2 htw
    have hyp := Set.integer_valuation_le_one _ F y hw
    have hpp := Set.integer_valuation_le_one _ F (generator C p) hw
    have hle : 1 ≤ w.valuation F (generator C p : F) := by
      rw [← htval]
      change w.valuation F (t : F) ≤ _
      rw [hmul, map_mul]
      exact mul_le_of_le_one_left' hyp
    have hpval := le_antisymm hpp hle
    have hr : algebraMap F (w.adicCompletion F) ((x : F) / (generator C p : F) ^ n) ∈
        w.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.algebraMap_adicCompletion]
      simp only [Function.comp_apply, Algebra.algebraMap_self]
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      change w.valuation F ((x : F) / (generator C p : F) ^ n) ≤ 1
      rw [map_div₀, map_pow, hpval, one_pow, div_one]
      exact Set.integer_valuation_le_one _ _ x hw
    have h := (hS w hw _).2 hr
    simpa using h (1 : w.adicCompletionIntegers F)
  let f := fun w : HeightOneSpectrum (𝓞 F) => ResidueTrace.localTraceCharacter w
    (algebraMap F (w.adicCompletion F) ((x : F) / (generator C p : F) ^ n))
  have hprod : (∏ᶠ w, f w) = f p.val * ∏ w ∈ A.Sf, f w := by
    rw [finprod_eq_prod_of_mulSupport_subset f (s := insert p.val A.Sf)]
    · exact Finset.prod_insert hv
    · intro w hw
      by_contra hn
      have hw' : w ∉ A.Sf := fun h => hn (Finset.mem_insert_of_mem h)
      have hwp : w ≠ p.val := by
        intro h
        subst w
        exact hn (Finset.mem_insert_self p.val A.Sf)
      exact hw (hout w hw' hwp)
  have hglobal := ResidueTrace.diagonal_product_formula ((x : F) / (generator C p : F) ^ n)
  rw [hprod] at hglobal
  simp only [negativeTrace, AddChar.neg_apply', uniformizer, ← map_pow, ← map_div₀]
  have heq := Finset.prod_coe_sort A.Sf f
  change (∏ w : InfinitePlace F, archTraceCharacter w
    (algebraMap F w.Completion ((x : F) / (generator C p : F) ^ n))) * (∏ w : A.Sf, f w.1) = (f p.val)⁻¹
  rw [heq]
  apply (eq_inv_iff_mul_eq_one).2
  convert hglobal using 1 <;> ac_rfl

theorem quotientTrace_mk (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (x : A.R) :
    quotientTrace C p n (residueMap C p n x) =
      negativeTrace p (algebraMap F (LocalField p) (x : F) / uniformizer C p ^ n) := by
  rw [← fieldTrace_eq_negative_localTrace C p n x]
  unfold quotientTrace
  dsimp
  change (cast (congrArg (fun L : Ideal A.R => AddChar (A.R ⧸ L) Circle)
    (power_generates C p n).2.symm)
    (A.residueTraceCharacter hS (powerIdeal p n) (generator C p ^ n)
      (power_generates C p n))) (Ideal.Quotient.mk _ x) = _
  rw [cast_character_mk]
  · rw [A.residueTraceCharacter_apply]
    rfl
  · exact (power_generates C p n).2.symm

theorem quotientTrace_primitive (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (x : Residue C p n) (hx : x ≠ 0) :
    ∃ y : Residue C p n, quotientTrace C p n (x * y) ≠ 1 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hxI : x ∉ A.extendIdeal (powerIdeal p n) := by
    rw [← (power_generates C p n).2]
    intro hxmem
    exact hx (Ideal.Quotient.eq_zero_iff_mem.mpr hxmem)
  obtain ⟨y, hy⟩ := ResidueTraceFactorProductFormula.principalResidue_separation
    ResidueTrace.baseEmbedding
    (fun v => (ResidueTrace.baseEmbedding_spec v).1)
    (fun v => (ResidueTrace.baseEmbedding_spec v).2)
    A hS (powerIdeal p n) (generator C p ^ n) (power_generates C p n) x hxI
  refine ⟨residueMap C p n y, ?_⟩
  change quotientTrace C p n (residueMap C p n x * residueMap C p n y) ≠ 1
  rw [← map_mul, quotientTrace_mk, ← fieldTrace_eq_negative_localTrace]
  exact hy

end DedekindZetaZeroFree.LocalFiniteSumCompatibility

end
