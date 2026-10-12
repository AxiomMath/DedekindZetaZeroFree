module

public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData
public import DedekindZetaZeroFree.Adeles.Characters.TraceProductFormula
public import DedekindZetaZeroFree.Adeles.Approximation.IntegralProductCRTDensity

@[expose] public section

section

open scoped NumberField Classical Valued
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.ResidueTraceFactorProductFormula
variable {F : Type} [Field F] [NumberField F]

def residuePrime (v : HeightOneSpectrum (𝓞 F)) : Nat.Primes :=
  ⟨ringChar (𝓞 F ⧸ v.asIdeal), by
    letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
    exact CharP.prime_ringChar _⟩

instance (v : HeightOneSpectrum (𝓞 F)) : Fact (residuePrime v).1.Prime :=
  ⟨(residuePrime v).2⟩

private lemma liesOver (v : HeightOneSpectrum (𝓞 F)) :
    v.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm (residuePrime v)).asIdeal := by
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  rw [Ideal.liesOver_iff]
  apply Ideal.ext
  intro x
  change x ∈ _ ↔ (algebraMap ℤ (𝓞 F) x) ∈ v.asIdeal
  have hspan : ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm (residuePrime v)).asIdeal =
       Ideal.span {((residuePrime v).1 : ℤ)} := by
    change (Ideal.span {((residuePrime v).1 : ℤ)}).map (Rat.IsIntegralClosure.intEquiv ℤ).symm = _
    have he : (Rat.IsIntegralClosure.intEquiv ℤ).symm = RingEquiv.refl ℤ := by ext; simp
    rw [he]
    exact Ideal.map_id _
  rw [hspan, Ideal.mem_span_singleton]
  constructor
  · intro hx
    have hh : ((residuePrime v).1 : 𝓞 F) ∈ v.asIdeal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact (ringChar.spec (𝓞 F ⧸ v.asIdeal) _).mpr (dvd_refl _)
    obtain ⟨y, rfl⟩ := hx
    simpa using v.asIdeal.mul_mem_right (y : 𝓞 F) hh
  · intro hx
    have hh : (x : 𝓞 F ⧸ v.asIdeal) = 0 := by
      simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hx
    exact (CharP.intCast_eq_zero_iff (𝓞 F ⧸ v.asIdeal) (ringChar (𝓞 F ⧸ v.asIdeal)) x).mp hh
private lemma extension (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ι : ℚ_[residuePrime v] →+* v.adicCompletion F, Continuous ι := by
  let w : HeightOneSpectrum ℤ := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm (residuePrime v)
  letI : v.asIdeal.LiesOver w.asIdeal := liesOver v
  let f := algebraMap (WithVal (w.valuation ℚ)) (WithVal (v.valuation F))
  have hf : Continuous f := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver ℚ F w v).continuous
  let c := UniformSpace.Completion.mapRingHom f hf
  let e := Padic.adicCompletionEquiv ℤ (residuePrime v)
  let ι : ℚ_[residuePrime v] →+* v.adicCompletion F :=
    ((HeightOneSpectrum.adicCompletion.equiv F v).symm.toRingHom.comp c).comp
      ((HeightOneSpectrum.adicCompletion.equiv ℚ w).toRingHom.comp e.toAlgEquiv.toRingHom)
  refine ⟨ι, ?_⟩
  exact (HeightOneSpectrum.adicCompletion.uniformEquiv F v).symm.continuous.comp
    (UniformSpace.Completion.continuous_map.comp
      ((HeightOneSpectrum.adicCompletion.uniformEquiv ℚ w).continuous.comp e.continuous))

theorem existsUnique_rationalExtension (v : HeightOneSpectrum (𝓞 F)) :
    ∃! ι : ℚ_[residuePrime v] →+* v.adicCompletion F,
      Continuous ι ∧ ∀ q : ℚ, ι (q : ℚ_[residuePrime v]) =
        algebraMap F (v.adicCompletion F) (algebraMap ℚ F q) := by
  obtain ⟨ι, hι⟩ := extension v
  have heq : ∀ q : ℚ, ι (q : ℚ_[residuePrime v]) =
      algebraMap F (v.adicCompletion F) (algebraMap ℚ F q) := by
    intro q
    exact DFunLike.congr_fun (RingHom.ext_rat
      (ι.comp (algebraMap ℚ ℚ_[residuePrime v]))
      ((algebraMap F (v.adicCompletion F)).comp (algebraMap ℚ F))) q
  refine ⟨ι, ⟨hι, heq⟩, ?_⟩
  intro j hj
  apply DFunLike.coe_injective
  exact (Padic.denseRange_ratCast (residuePrime v)).equalizer hj.1 hι (funext fun q => (hj.2 q).trans (heq q).symm)

end DedekindZetaZeroFree.ResidueTraceFactorProductFormula

end

end

section

open scoped NumberField Classical Valued
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.ResidueTraceFactorProductFormula
variable {F : Type} [Field F] [NumberField F]

theorem finite_rationalExtension (v : HeightOneSpectrum (𝓞 F))
    (ι : ℚ_[residuePrime v] →+* v.adicCompletion F)
    (hι : Continuous ι)
    (hℚ : ∀ q : ℚ, ι (q : ℚ_[residuePrime v]) =
      algebraMap F (v.adicCompletion F) (algebraMap ℚ F q)) :
    letI := ι.toAlgebra
    Module.Finite ℚ_[residuePrime v] (v.adicCompletion F) := by
  letI := ι.toAlgebra

  haveI : ContinuousSMul ℚ_[residuePrime v] (v.adicCompletion F) := ⟨by
    show Continuous fun p : ℚ_[residuePrime v] × v.adicCompletion F => p.1 • p.2
    change Continuous fun p : ℚ_[residuePrime v] × v.adicCompletion F => ι p.1 * p.2
    exact (hι.comp continuous_fst).mul continuous_snd⟩

  set b := Module.finBasis ℚ F
  let S : Submodule ℚ_[residuePrime v] (v.adicCompletion F) :=
    Submodule.span ℚ_[residuePrime v]
      (Set.range fun i => algebraMap F (v.adicCompletion F) (b i))
  haveI : Module.Finite ℚ_[residuePrime v] S :=
    Module.Finite.span_of_finite ℚ_[residuePrime v] (Set.finite_range _)

  have hmem : ∀ x : F, algebraMap F (v.adicCompletion F) x ∈ S := by
    intro x
    have hx : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
    rw [hx, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hthis : algebraMap F (v.adicCompletion F) (b.repr x i • b i) =
        (b.repr x i : ℚ_[residuePrime v]) •
          algebraMap F (v.adicCompletion F) (b i) := by
      simp only [Algebra.smul_def, map_mul, ← hℚ (b.repr x i)]
      rfl
    rw [hthis]
    exact S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hrange : Set.range (algebraMap F (v.adicCompletion F)) ⊆ (S : Set _) := by
    rintro _ ⟨x, rfl⟩
    exact hmem x

  have hclosed : IsClosed (S : Set (v.adicCompletion F)) :=
    Submodule.closed_of_finiteDimensional S
  have hdense : DenseRange (algebraMap F (v.adicCompletion F)) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact (hclosed.closure_subset_iff.mpr hrange)
      (by rw [hdense.closure_range]; exact Set.mem_univ x)
  refine Module.Finite.of_surjective S.subtype fun y => ⟨⟨y, ?_⟩, rfl⟩
  rw [htop]; exact Submodule.mem_top

end DedekindZetaZeroFree.ResidueTraceFactorProductFormula

end

end

section

open scoped NumberField Classical Valued
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.ResidueTraceFactorProductFormula
variable {F : Type} [Field F] [NumberField F]

def traceFactor (v : HeightOneSpectrum (𝓞 F))
    (ι : ℚ_[residuePrime v] →+* v.adicCompletion F) :
    AddChar (v.adicCompletion F) Circle := by
  letI := ι.toAlgebra
  exact (rationalPadicCharacter (residuePrime v)).compAddMonoidHom
    (Algebra.trace ℚ_[residuePrime v] (v.adicCompletion F)).toAddMonoidHom

theorem traceFactors_finiteSupport
    (ι : (v : HeightOneSpectrum (𝓞 F)) →
      ℚ_[residuePrime v] →+* v.adicCompletion F)
    (hι : ∀ v, Continuous (ι v))
    (hℚ : ∀ v (q : ℚ), ι v (q : ℚ_[residuePrime v]) =
      algebraMap F (v.adicCompletion F) (algebraMap ℚ F q))
    (x : F) :
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 F) =>
      traceFactor v (ι v) (algebraMap F (v.adicCompletion F) x)) := by

  obtain ⟨n, hn, hint⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset F)
  have hx : IsIntegral ℤ (n • x) := hint x (Finset.mem_singleton_self x)
  have hfin : {v : HeightOneSpectrum (𝓞 F) | (n : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h := Ideal.finite_factors (R := 𝓞 F)
      (I := Ideal.span {(n : 𝓞 F)}) (by simpa using hn)
    simpa only [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] using h
  apply hfin.subset
  intro v hv
  by_contra hnv
  have hndvd : ¬ ((residuePrime v : ℕ) : ℤ) ∣ n := by
    intro h
    apply hnv
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa using (CharP.intCast_eq_zero_iff (𝓞 F ⧸ v.asIdeal)
      (ringChar (𝓞 F ⧸ v.asIdeal)) n).mpr h
  have hnlocal : ‖(n : ℚ_[residuePrime v])‖ = 1 :=
    le_antisymm (Padic.norm_int_le_one n)
      (le_of_not_gt (mt Padic.norm_intCast_lt_one_iff.mp hndvd))
  letI := (ι v).toAlgebra
  letI := finite_rationalExtension v (ι v) (hι v) (hℚ v)

  have ht : IsIntegral ℤ (Algebra.trace ℚ_[residuePrime v] (v.adicCompletion F)
      (algebraMap F (v.adicCompletion F) (n • x))) :=
    Algebra.isIntegral_trace hx.algebraMap
  have ht' : IsIntegral ℤ_[residuePrime v] (Algebra.trace ℚ_[residuePrime v]
      (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (n • x))) :=
    ht.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp ht'
  have hnorm : ‖Algebra.trace ℚ_[residuePrime v] (v.adicCompletion F)
      (algebraMap F (v.adicCompletion F) (n • x))‖ ≤ 1 := by
    rw [← hz, PadicInt.algebraMap_apply]
    exact z.property
  have htrace : (Algebra.trace ℚ_[residuePrime v] (v.adicCompletion F))
      (algebraMap F (v.adicCompletion F) (n • x)) =
      (n : ℚ_[residuePrime v]) * (Algebra.trace ℚ_[residuePrime v]
        (v.adicCompletion F) (algebraMap F (v.adicCompletion F) x)) := by
    rw [map_zsmul, map_zsmul, zsmul_eq_mul]
  rw [htrace, norm_mul, hnlocal, one_mul] at hnorm
  apply hv
  change rationalPadicCharacter (residuePrime v) _ = 1
  exact (rationalPadicCharacter_eq_one_iff _ _).mpr ⟨⟨_, hnorm⟩, rfl⟩

end DedekindZetaZeroFree.ResidueTraceFactorProductFormula

end

end

section

open scoped NumberField Classical Valued
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.ResidueTraceFactorProductFormula
variable {F : Type} [Field F] [NumberField F]

theorem archTraceCharacter_product_eq_trace (x : F) :
    (∏ w : InfinitePlace F,
      archTraceCharacter w (algebraMap F w.Completion x)) =
      Circle.exp (2 * Real.pi * ((Algebra.trace ℚ F x : ℚ) : ℝ)) := by
  classical
  rw [trace_eq_sum_archTrace]
  have h (s : Finset (InfinitePlace F)) :
      (∏ w ∈ s, archTraceCharacter w (algebraMap F w.Completion x)) =
        Circle.exp (2 * Real.pi * ∑ w ∈ s,
          archTrace w (algebraMap F w.Completion x)) := by
    induction s using Finset.induction_on with
    | empty => simp [Circle.exp_zero]
    | @insert w s hw ih =>
      simp only [Finset.prod_insert hw, Finset.sum_insert hw]
      rw [ih]
      change Circle.exp (2 * Real.pi * archTrace w (algebraMap F w.Completion x)) *
        Circle.exp (2 * Real.pi * ∑ w ∈ s,
          archTrace w (algebraMap F w.Completion x)) = _
      rw [← Circle.exp_add]
      congr 1
      ring
  exact h Finset.univ

private theorem residuePrime_eq_adapter (v : HeightOneSpectrum (𝓞 F)) :
    residuePrime v = PlaceTraceAdapter.prime F v := by
  apply Subtype.ext
  change ringChar (𝓞 F ⧸ v.asIdeal) = _
  apply CharP.ringChar_of_prime_eq_zero (PlaceTraceAdapter.prime F v).2
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have h : ((PlaceTraceAdapter.prime F v).1 : 𝓞 ℚ) ∈
      (PlaceTraceAdapter.rationalPlace F v).asIdeal := by
    have hgen := Rat.HeightOneSpectrum.natGenerator_dvd_iff
      (PlaceTraceAdapter.rationalPlace F v) (n := (PlaceTraceAdapter.prime F v).1)
    have hh := hgen.mp (dvd_refl _)
    rw [Ideal.mem_map_iff_of_surjective _
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).surjective] at hh
    obtain ⟨x, hx, he⟩ := hh
    have he' : x = ((PlaceTraceAdapter.prime F v).1 : 𝓞 ℚ) :=
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).injective (by simpa using he)
    exact he' ▸ hx
  have h' : (algebraMap (𝓞 ℚ) (𝓞 F)
      ((PlaceTraceAdapter.prime F v).1 : 𝓞 ℚ)) ∈ v.asIdeal := h
  simpa using h'

private theorem traceFactor_eq_localFiniteCharacter
    (ι : (v : HeightOneSpectrum (𝓞 F)) →
      ℚ_[residuePrime v] →+* v.adicCompletion F)
    (hι : ∀ v, Continuous (ι v))
    (hℚ : ∀ v (q : ℚ), ι v (q : ℚ_[residuePrime v]) =
      algebraMap F (v.adicCompletion F) (algebraMap ℚ F q))
    (v : HeightOneSpectrum (𝓞 F)) :
    traceFactor v (ι v) = localFiniteCharacter F v := by
  letI (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩
  have hpv := residuePrime_eq_adapter v
  have hgeneral (p : Nat.Primes) (m : ℚ_[p] →+* v.adicCompletion F)
      (hmc : Continuous m)
      (hmq : ∀ q : ℚ, m (q : ℚ_[p]) =
        algebraMap F (v.adicCompletion F) (algebraMap ℚ F q))
      (hp : p = PlaceTraceAdapter.prime F v) :
      (letI := m.toAlgebra
       (rationalPadicCharacter p).compAddMonoidHom
        (Algebra.trace ℚ_[p] (v.adicCompletion F)).toAddMonoidHom) =
        localFiniteCharacter F v := by
    subst p
    have hmap : m = PlaceTraceAdapter.padicMap F v := by
      apply DFunLike.coe_injective
      apply (Padic.denseRange_ratCast (PlaceTraceAdapter.prime F v)).equalizer hmc
      · letI : Algebra ℚ ((PlaceTraceAdapter.rationalPlace F v).adicCompletion ℚ) :=
          HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ _
        exact (finitePlaceAdicCompletionMap_continuous ℚ F _ _).comp
          (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
            (PlaceTraceAdapter.rationalPlace F v)).symm.continuous
      · funext q
        exact (hmq q).trans (by simp [PlaceTraceAdapter.padicMap, map_ratCast])
    subst m
    rfl
  exact hgeneral (residuePrime v) (ι v) (hι v) (hℚ v) hpv

private theorem character_sum {A ι : Type*} [AddCommMonoid A]
    (χ : AddChar A Circle) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, χ.map_add_eq_mul, ih]

private theorem character_cast (p q : Nat.Primes) (h : p = q) (x : ℚ_[p]) :
    rationalPadicCharacter p x = rationalPadicCharacter q
      (cast (congrArg (fun r : Nat.Primes => ℚ_[r]) h) x) := by
  subst q
  rfl

private theorem traceFactor_fiber_product
    (ι : (v : HeightOneSpectrum (𝓞 F)) →
      ℚ_[residuePrime v] →+* v.adicCompletion F)
    (hι : ∀ v, Continuous (ι v))
    (hℚ : ∀ v (q : ℚ), ι v (q : ℚ_[residuePrime v]) =
      algebraMap F (v.adicCompletion F) (algebraMap ℚ F q))
    (x : F) (p : Nat.Primes) :
    letI := finitePlacesAboveRationalPrimeFintype F p
    (∏ v : FinitePlacesAbove ℚ F (Rat.HeightOneSpectrum.primesEquiv.symm p),
      traceFactor v.val (ι v.val) (algebraMap F (v.val.adicCompletion F) x)) =
        rationalPadicCharacter p (algebraMap ℚ ℚ_[p] (Algebra.trace ℚ F x)) := by
  letI := finitePlacesAboveRationalPrimeFintype F p
  rw [trace_eq_sum_localTrace_padic F x p, character_sum]
  apply Finset.prod_congr rfl
  intro v _
  rw [traceFactor_eq_localFiniteCharacter ι hι hℚ v.val]
  change rationalPadicCharacter (PlaceTraceAdapter.prime F v.val)
      (PlaceTraceAdapter.trace F v.val (algebraMap F (v.val.adicCompletion F) x)) =
    rationalPadicCharacter p
      (PlaceTraceAdapter.traceAbove F p v (algebraMap F (v.val.adicCompletion F) x))
  exact character_cast _ p (PlaceTraceAdapter.prime_eq_of_above F p v) _

private theorem traceFactor_finprod_eq_rational
    (ι : (v : HeightOneSpectrum (𝓞 F)) →
      ℚ_[residuePrime v] →+* v.adicCompletion F)
    (hι : ∀ v, Continuous (ι v))
    (hℚ : ∀ v (q : ℚ), ι v (q : ℚ_[residuePrime v]) =
      algebraMap F (v.adicCompletion F) (algebraMap ℚ F q))
    (hsupport : ∀ x : F, Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 F) =>
        traceFactor v (ι v) (algebraMap F (v.adicCompletion F) x)))
    (x : F) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 F),
      traceFactor v (ι v) (algebraMap F (v.adicCompletion F) x)) =
    (∏ᶠ p : Nat.Primes,
      rationalPadicCharacter p (algebraMap ℚ ℚ_[p] (Algebra.trace ℚ F x))) := by
  classical
  let g := fun v : HeightOneSpectrum (𝓞 F) =>
    traceFactor v (ι v) (algebraMap F (v.adicCompletion F) x)
  have hg := hsupport x
  rw [finprod_eq_prod _ hg]
  rw [← finprod_prod_filter (PlaceTraceAdapter.prime F) hg.toFinset g]
  apply finprod_congr
  intro p
  letI := finitePlacesAboveRationalPrimeFintype F p
  rw [← traceFactor_fiber_product ι hι hℚ x p]
  rw [← finprod_eq_prod_of_fintype]
  change (∏ y ∈ hg.toFinset with PlaceTraceAdapter.prime F y = p, g y) =
    ∏ᶠ i : {v : HeightOneSpectrum (𝓞 F) //
      finitePlaceBelow (K := ℚ) v = Rat.HeightOneSpectrum.primesEquiv.symm p}, g i.val
  rw [finprod_subtype_eq_finprod_cond]
  symm
  apply finprod_cond_eq_prod_of_cond_iff
  intro v hv
  rw [Finset.mem_filter]
  have hmem : v ∈ hg.toFinset := hg.mem_toFinset.mpr hv
  simp only [hmem, true_and]
  change finitePlaceBelow (K := ℚ) v = Rat.HeightOneSpectrum.primesEquiv.symm p ↔
    PlaceTraceAdapter.prime F v = p
  exact Rat.HeightOneSpectrum.primesEquiv.apply_eq_iff_eq_symm_apply.symm

theorem traceFactors_product_formula
    (ι : (v : HeightOneSpectrum (𝓞 F)) →
      ℚ_[residuePrime v] →+* v.adicCompletion F)
    (hι : ∀ v, Continuous (ι v))
    (hℚ : ∀ v (q : ℚ), ι v (q : ℚ_[residuePrime v]) =
      algebraMap F (v.adicCompletion F) (algebraMap ℚ F q))
    (hsupport : ∀ x : F, Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 F) =>
        traceFactor v (ι v) (algebraMap F (v.adicCompletion F) x)))
    (x : F) :
    (∏ w : InfinitePlace F, archTraceCharacter w (algebraMap F w.Completion x)) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 F),
        traceFactor v (ι v) (algebraMap F (v.adicCompletion F) x)) = 1 := by
  rw [archTraceCharacter_product_eq_trace x,
    traceFactor_finprod_eq_rational ι hι hℚ hsupport x]
  exact rational_diagonal_additive_product (Algebra.trace ℚ F x)

end DedekindZetaZeroFree.ResidueTraceFactorProductFormula

end

end

section

open scoped NumberField Classical Valued
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.ResidueTraceFactorProductFormula
variable {F : Type} [Field F] [NumberField F]

private theorem locally_integral_cofinite (z : F) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ T,
      algebraMap F (v.adicCompletion F) z ∈ v.adicCompletionIntegers F := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 F) z
  let T : Finset (HeightOneSpectrum (𝓞 F)) :=
    (Ideal.finite_factors (I := Ideal.span {b})
      (by simpa [Ideal.span_singleton_eq_bot] using nonZeroDivisors.ne_zero hb)).toFinset
  refine ⟨T, ?_⟩
  intro v hv
  have hvb : b ∉ v.asIdeal := by
    simpa [T, Ideal.dvd_span_singleton] using hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (v.valuation_div_le_one_iff F a (nonZeroDivisors.ne_zero hb) (fun h => (hvb h).elim)).mpr hvb

private theorem continuous_traceFactor (v : HeightOneSpectrum (𝓞 F))
    (ι : ℚ_[residuePrime v] →+* v.adicCompletion F)
    (hι : Continuous ι)
    (hℚ : ∀ q : ℚ, ι (q : ℚ_[residuePrime v]) =
      algebraMap F (v.adicCompletion F) (algebraMap ℚ F q)) :
    Continuous (traceFactor v ι : v.adicCompletion F → Circle) := by
  letI := ι.toAlgebra
  letI := finite_rationalExtension v ι hι hℚ
  letI : ContinuousSMul ℚ_[residuePrime v] (v.adicCompletion F) := by
    constructor
    change Continuous (fun x : ℚ_[residuePrime v] × v.adicCompletion F => ι x.1 * x.2)
    exact (hι.comp continuous_fst).mul continuous_snd
  exact (continuous_rationalPadicCharacter (residuePrime v)).comp
    (Algebra.trace ℚ_[residuePrime v] (v.adicCompletion F)).continuous_of_finiteDimensional

theorem principalResidue_separation
    (ι : (v : HeightOneSpectrum (𝓞 F)) →
      ℚ_[residuePrime v] →+* v.adicCompletion F)
    (hι : ∀ v, Continuous (ι v))
    (hℚ : ∀ v (q : ℚ), ι v (q : ℚ_[residuePrime v]) =
      algebraMap F (v.adicCompletion F) (algebraMap ℚ F q))
    (A : SArithmeticData F)
    (hS : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      ∀ z : v.adicCompletion F,
        (∀ o : v.adicCompletionIntegers F,
          traceFactor v (ι v) (z * (o : v.adicCompletion F)) = 1) ↔
        z ∈ v.adicCompletionIntegers F)
    (I : A.Exterior) (c : A.R) (hc : A.Generates I c)
    (x : A.R) (hx : x ∉ A.extendIdeal I) :
    ∃ y : A.R,
      (∏ w : InfinitePlace F, archTraceCharacter w
        (algebraMap F w.Completion (((x : F) * (y : F)) / (c : F)))) *
      (∏ v : A.Sf, traceFactor v.1 (ι v.1)
        (algebraMap F (v.1.adicCompletion F) (((x : F) * (y : F)) / (c : F)))) ≠ 1 := by
  classical
  by_contra! hall
  let z : F := (x : F) / (c : F)
  obtain ⟨T, hT⟩ := locally_integral_cofinite z
  let P := T \ A.Sf
  have hout (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf ∪ P)
      (o : v.adicCompletionIntegers F) :
      traceFactor v (ι v) (algebraMap F (v.adicCompletion F) z * o) = 1 := by
    have hvS : v ∉ A.Sf := fun h => hv (Finset.mem_union_left P h)
    have hvT : v ∉ T := by
      intro h
      exact hv (Finset.mem_union_right A.Sf (Finset.mem_sdiff.mpr ⟨h, hvS⟩))
    exact (hS v hvS _).mpr (hT v hvT) o
  let g := fun (o : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletionIntegers F) =>
    ∏ v ∈ P, traceFactor v (ι v) (algebraMap F (v.adicCompletion F) z * o v)
  have hg : Continuous g := by
    apply continuous_finset_prod
    intro v hv
    exact (continuous_traceFactor v (ι v) (hι v) (hℚ v)).comp
      (continuous_const.mul (continuous_subtype_val.comp (continuous_apply v)))
  have hmap (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
      (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) A.R a : F) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    change algebraMap (𝓞 F) (v.adicCompletion F) a =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)
    exact IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) a
  have hdiag (a : 𝓞 F) : g (ringOfIntegers_integralDiagonal F a) = 1 := by
    let y : A.R := algebraMap (𝓞 F) A.R a
    let t : F := z * (y : F)
    let f := fun v : HeightOneSpectrum (𝓞 F) =>
      traceFactor v (ι v) (algebraMap F (v.adicCompletion F) t)
    have hf : Function.mulSupport f ⊆ ↑(A.Sf ∪ P) := by
      intro v hv
      by_contra hn
      apply hv
      have hh := hout v hn (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a)
      simpa only [f, t, y, map_mul, hmap] using hh
    have hd : Disjoint A.Sf P := by
      apply Finset.disjoint_left.mpr
      intro v hv hvP
      exact (Finset.mem_sdiff.mp hvP).2 hv
    have hp := traceFactors_product_formula ι hι hℚ
      (fun t => traceFactors_finiteSupport ι hι hℚ t) t
    rw [finprod_eq_prod_of_mulSupport_subset f hf, Finset.prod_union hd] at hp
    have hs := hall y
    have ht : t = ((x : F) * (y : F)) / (c : F) := by dsimp [t, z]; ring
    rw [← ht] at hs
    change (∏ w : InfinitePlace F, archTraceCharacter w (algebraMap F w.Completion t)) *
      (∏ v : A.Sf, f v) = 1 at hs
    rw [Finset.prod_coe_sort] at hs
    have hp' :
        ((∏ w : InfinitePlace F, archTraceCharacter w (algebraMap F w.Completion t)) *
          ∏ v ∈ A.Sf, f v) * (∏ v ∈ P, f v) = 1 := by
      simpa only [f, mul_assoc] using hp
    rw [show (∏ w : InfinitePlace F, archTraceCharacter w (algebraMap F w.Completion t)) *
      (∏ v ∈ A.Sf, f v) = 1 from hs, one_mul] at hp'
    simpa only [g, ringOfIntegers_integralDiagonal, f, t, y, map_mul, hmap] using hp'
  have heq : g = fun _ => (1 : Circle) :=
    (denseRange_ringOfIntegers_integralDiagonal F).equalizer hg continuous_const
      (funext hdiag)
  have hz : z ∈ A.R := by
    intro v hv
    change v ∉ A.Sf at hv
    have hvint : algebraMap F (v.adicCompletion F) z ∈ v.adicCompletionIntegers F := by
      apply (hS v hv _).mp
      intro o
      by_cases hvP : v ∈ P
      · let u : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletionIntegers F :=
          Function.update 0 v o
        have hu := congrFun heq u
        have hsingle : g u = traceFactor v (ι v) (algebraMap F (v.adicCompletion F) z * o) := by
          dsimp [g]
          rw [Finset.prod_eq_single v]
          · simp [u]
          · intro w hw hwv
            simp [u, Function.update_of_ne hwv]
          · exact fun h => (h hvP).elim
        exact hsingle.symm.trans hu
      · exact hout v (by simpa only [Finset.mem_union, not_or] using And.intro hv hvP) o
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.algebraMap_adicCompletion] at hvint
    simp only [Function.comp_apply, Algebra.algebraMap_self] at hvint
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hvint
  apply hx
  rw [← hc.2]
  apply Ideal.mem_span_singleton.mpr
  refine ⟨⟨z, hz⟩, ?_⟩
  apply Subtype.ext
  change (x : F) = (c : F) * ((x : F) / (c : F))
  exact (mul_div_cancel₀ _ (by exact_mod_cast hc.1)).symm

end DedekindZetaZeroFree.ResidueTraceFactorProductFormula

end

end
