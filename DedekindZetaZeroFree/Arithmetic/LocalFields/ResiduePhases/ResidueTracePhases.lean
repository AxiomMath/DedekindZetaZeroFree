module

public import DedekindZetaZeroFree.Adeles.Characters.GlobalTraceProductFormula
public import DedekindZetaZeroFree.Adeles.Lattices.SIntegerLocalProduct
public import DedekindZetaZeroFree.Arithmetic.Ideals.AllowedGenerators

@[expose] public section

open scoped NumberField Classical Valued
open NumberField IsDedekindDomain WithZero Multiplicative
noncomputable section
namespace DedekindZetaZeroFree.ResidueTrace
variable {F : Type} [Field F] [NumberField F]

def rationalPrimeBelow (v : HeightOneSpectrum (𝓞 F)) : Nat.Primes :=
  ⟨ringChar (𝓞 F ⧸ v.asIdeal), by
    letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
    exact CharP.prime_ringChar _⟩
 instance instFactPrimeResidueTraceRationalPrimeBelow (v : HeightOneSpectrum (𝓞 F)) : Fact (rationalPrimeBelow v).1.Prime :=
  ⟨(rationalPrimeBelow v).2⟩

theorem existsUnique_baseEmbedding (v : HeightOneSpectrum (𝓞 F)) :
    ∃! ι : ℚ_[rationalPrimeBelow v] →+* v.adicCompletion F,
      Continuous ι ∧ ∀ q : ℚ, ι (q : ℚ_[rationalPrimeBelow v]) =
        algebraMap F (v.adicCompletion F) (algebraMap ℚ F q) := by
  exact ResidueTraceFactorProductFormula.existsUnique_rationalExtension v

def baseEmbedding (v : HeightOneSpectrum (𝓞 F)) :
    ℚ_[rationalPrimeBelow v] →+* v.adicCompletion F :=
  Classical.choose (existsUnique_baseEmbedding v)

theorem baseEmbedding_spec (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (baseEmbedding v) ∧ ∀ q : ℚ,
      baseEmbedding v (q : ℚ_[rationalPrimeBelow v]) =
        algebraMap F (v.adicCompletion F) (algebraMap ℚ F q) :=
  (Classical.choose_spec (existsUnique_baseEmbedding v)).1

def localTraceCharacter (v : HeightOneSpectrum (𝓞 F)) :
    AddChar (v.adicCompletion F) Circle := by
  letI := (baseEmbedding v).toAlgebra
  exact (rationalPadicCharacter (rationalPrimeBelow v)).compAddMonoidHom
    (Algebra.trace ℚ_[rationalPrimeBelow v] (v.adicCompletion F)).toAddMonoidHom

def IsSelfDual (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ z : v.adicCompletion F,
    (∀ o : v.adicCompletionIntegers F, localTraceCharacter v (z * (o : v.adicCompletion F)) = 1) ↔
      z ∈ v.adicCompletionIntegers F

theorem localTrace_finite (v : HeightOneSpectrum (𝓞 F)) :
    letI := (baseEmbedding v).toAlgebra
    Module.Finite ℚ_[rationalPrimeBelow v] (v.adicCompletion F) := by
  exact ResidueTraceFactorProductFormula.finite_rationalExtension v (baseEmbedding v)
    (baseEmbedding_spec v).1 (baseEmbedding_spec v).2

theorem continuous_localTraceCharacter (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (localTraceCharacter v : v.adicCompletion F → Circle) := by
  letI := (baseEmbedding v).toAlgebra
  letI := localTrace_finite v
  letI : ContinuousSMul ℚ_[rationalPrimeBelow v] (v.adicCompletion F) := by
    constructor
    change Continuous (fun x : ℚ_[rationalPrimeBelow v] × v.adicCompletion F =>
      baseEmbedding v x.1 * x.2)
    exact ((baseEmbedding_spec v).1.comp continuous_fst).mul continuous_snd
  exact (continuous_rationalPadicCharacter (rationalPrimeBelow v)).comp
    (Algebra.trace ℚ_[rationalPrimeBelow v] (v.adicCompletion F)).continuous_of_finiteDimensional

theorem diagonal_hasFiniteMulSupport (x : F) :
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 F) =>
      localTraceCharacter v (algebraMap F (v.adicCompletion F) x)) := by
  exact ResidueTraceFactorProductFormula.traceFactors_finiteSupport baseEmbedding
    (fun v => (baseEmbedding_spec v).1) (fun v => (baseEmbedding_spec v).2) x

theorem diagonal_product_formula (x : F) :
    (∏ w : InfinitePlace F, archTraceCharacter w (algebraMap F w.Completion x)) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 F),
        localTraceCharacter v (algebraMap F (v.adicCompletion F) x)) = 1 := by
  exact ResidueTraceFactorProductFormula.traceFactors_product_formula baseEmbedding
    (fun v => (baseEmbedding_spec v).1) (fun v => (baseEmbedding_spec v).2)
    diagonal_hasFiniteMulSupport x
end DedekindZetaZeroFree.ResidueTrace
namespace DedekindZetaZeroFree.SArithmeticData
variable {F : Type} [Field F] [NumberField F]

def eS (A : SArithmeticData F) : AddChar (SLocalProduct F A.Sf) Circle where
  toFun x := (∏ w, archTraceCharacter w (x.1 w)) *
    ∏ v : A.Sf, ResidueTrace.localTraceCharacter v.1 (x.2 v)
  map_zero_eq_one' := by
    change (∏ w, archTraceCharacter w 0) * (∏ v : A.Sf, ResidueTrace.localTraceCharacter v.1 0) = 1
    simp
  map_add_eq_mul' := by
    intro x y
    change (∏ w, archTraceCharacter w (x.1 w + y.1 w)) *
      (∏ v : A.Sf, ResidueTrace.localTraceCharacter v.1 (x.2 v + y.2 v)) = _
    simp only [AddChar.map_add_eq_mul, Finset.prod_mul_distrib]
    ac_rfl

def fieldTraceCharacter (A : SArithmeticData F) : AddChar F Circle :=
  A.eS.compAddMonoidHom (sLocalDiagonal F A.Sf).toAddMonoidHom

def ContainsTraceBadPlaces (A : SArithmeticData F) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf → ResidueTrace.IsSelfDual v

theorem eS_integer (A : SArithmeticData F) (hS : A.ContainsTraceBadPlaces)
    (r : A.R) : A.fieldTraceCharacter (r : F) = 1 := by
  have hout (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
      ResidueTrace.localTraceCharacter v (algebraMap F (v.adicCompletion F) (r : F)) = 1 := by
    have hr : algebraMap F (v.adicCompletion F) (r : F) ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.algebraMap_adicCompletion]
      simp only [Function.comp_apply, Algebra.algebraMap_self]
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact Set.integer_valuation_le_one _ _ r hv
    have h := (hS v hv _).2 hr
    simpa using h (1 : v.adicCompletionIntegers F)
  have hprod := finprod_eq_prod_of_mulSupport_subset
    (fun v : HeightOneSpectrum (𝓞 F) =>
      ResidueTrace.localTraceCharacter v (algebraMap F (v.adicCompletion F) (r : F)))
    (s := A.Sf) (by
      intro v hv
      by_contra hn
      exact hv (hout v hn))
  have hglobal := ResidueTrace.diagonal_product_formula (r : F)
  rw [hprod] at hglobal
  change (∏ w : InfinitePlace F, archTraceCharacter w (algebraMap F w.Completion (r : F))) *
    (∏ v : A.Sf, ResidueTrace.localTraceCharacter v.1
      (algebraMap F (v.1.adicCompletion F) (r : F))) = 1
  have heq := Finset.prod_coe_sort A.Sf (fun v : HeightOneSpectrum (𝓞 F) =>
    ResidueTrace.localTraceCharacter v (algebraMap F (v.adicCompletion F) (r : F)))
  exact (congrArg (fun t : Circle =>
    (∏ w : InfinitePlace F, archTraceCharacter w (algebraMap F w.Completion (r : F))) * t)
    heq).trans hglobal

def dividedTraceCharacter (A : SArithmeticData F) (c : A.R) : AddChar A.R Circle :=
  A.fieldTraceCharacter.compAddMonoidHom
    ((LinearMap.mulRight F (c : F)⁻¹).toAddMonoidHom.comp A.R.val.toAddMonoidHom)

theorem dividedTraceCharacter_kernel (A : SArithmeticData F)
    (hS : A.ContainsTraceBadPlaces) (I : A.Exterior) (c : A.R)
    (hc : A.Generates I c) (x : A.R) (hx : x ∈ A.extendIdeal I) :
    A.dividedTraceCharacter c x = 1 := by
  rw [← hc.2] at hx
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  have hcF : (c : F) ≠ 0 := by
    exact_mod_cast hc.1
  change A.fieldTraceCharacter (((y : F) * (c : F)) * (c : F)⁻¹) = 1
  rw [mul_assoc, mul_inv_cancel₀ hcF, mul_one]
  exact A.eS_integer hS y

def residueTraceCharacter (A : SArithmeticData F) (hS : A.ContainsTraceBadPlaces)
    (I : A.Exterior) (c : A.R) (hc : A.Generates I c) :
    AddChar (A.R ⧸ A.extendIdeal I) Circle :=
  AddChar.toAddMonoidHomEquiv.symm <|
    QuotientAddGroup.lift (A.extendIdeal I).toAddSubgroup
      (A.dividedTraceCharacter c).toAddMonoidHom (by
        intro x hx
        change Additive.ofMul (A.dividedTraceCharacter c x) = 0
        rw [A.dividedTraceCharacter_kernel hS I c hc x hx]
        rfl)

theorem residueTraceCharacter_apply (A : SArithmeticData F)
    (hS : A.ContainsTraceBadPlaces) (I : A.Exterior) (c : A.R)
    (hc : A.Generates I c) (x : A.R) :
    A.residueTraceCharacter hS I c hc (Ideal.Quotient.mk (A.extendIdeal I) x) =
      A.fieldTraceCharacter ((x : F) / (c : F)) := by
  change A.fieldTraceCharacter ((x : F) * (c : F)⁻¹) = _
  rw [div_eq_mul_inv]

theorem residueTraceCharacter_prime_local (A : SArithmeticData F)
    (hS : A.ContainsTraceBadPlaces) (B : Subgroup A.V)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (p : A.R) (hp : A.Generates I p) (a : Fˣ)
    (hap : (a : F) = (p : F)) (ha : A.IsAllowed B a) (x : A.R) :
    A.residueTraceCharacter hS I p hp (Ideal.Quotient.mk (A.extendIdeal I) x) =
      ResidueTrace.localTraceCharacter v
        (algebraMap F (v.adicCompletion F) (-((x : F) / (p : F)))) := by
  have hv : v ∉ A.Sf := by
    intro hv
    have h := (A.exterior_iff ⟨I.val, I.property.1⟩).mp I.property.2 v hv
    rw [hIv, sup_idem] at h
    exact v.isPrime.ne_top h
  have hout (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ A.Sf) (hwv : w ≠ v) :
      ResidueTrace.localTraceCharacter w
        (algebraMap F (w.adicCompletion F) ((x : F) / (p : F))) = 1 := by
    have hnle : ¬ v.asIdeal ≤ w.asIdeal := by
      intro h
      have heq := (v.isPrime.isMaximal v.ne_bot).eq_of_le (w.isPrime.ne_top) h
      exact hwv (HeightOneSpectrum.ext heq.symm)
    obtain ⟨t, ht, htw⟩ := SetLike.not_le_iff_exists.mp hnle
    have htR : algebraMap (𝓞 F) A.R t ∈ Ideal.span {p} := by
      rw [hp.2]
      exact Ideal.mem_map_of_mem _ (hIv ▸ ht)
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp htR
    have hmul : (t : F) = (y : F) * (p : F) := by
      exact (congrArg (fun z : A.R => (z : F)) hy).symm
    have htval := (w.valuation_eq_one_iff_notMem (K := F)).2 htw
    have hyp := Set.integer_valuation_le_one _ F y hw
    have hpp := Set.integer_valuation_le_one _ F p hw
    have hle : 1 ≤ w.valuation F (p : F) := by
      rw [← htval]
      change w.valuation F (t : F) ≤ _
      rw [hmul, map_mul]
      exact mul_le_of_le_one_left' hyp
    have hpval := le_antisymm hpp hle
    have hr : algebraMap F (w.adicCompletion F) ((x : F) / (p : F)) ∈
        w.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.algebraMap_adicCompletion]
      simp only [Function.comp_apply, Algebra.algebraMap_self]
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      change w.valuation F ((x : F) / (p : F)) ≤ 1
      rw [map_div₀, hpval, div_one]
      exact Set.integer_valuation_le_one _ _ x hw
    have h := (hS w hw _).2 hr
    simpa using h (1 : w.adicCompletionIntegers F)
  let f := fun w : HeightOneSpectrum (𝓞 F) => ResidueTrace.localTraceCharacter w
    (algebraMap F (w.adicCompletion F) ((x : F) / (p : F)))
  have hprod : (∏ᶠ w, f w) = f v * ∏ w ∈ A.Sf, f w := by
    rw [finprod_eq_prod_of_mulSupport_subset f (s := insert v A.Sf)]
    · exact Finset.prod_insert hv
    · intro w hw
      by_contra hn
      have hw' : w ∉ A.Sf := fun h => hn (Finset.mem_insert_of_mem h)
      have hwv : w ≠ v := by
        intro h
        subst w
        exact hn (Finset.mem_insert_self v A.Sf)
      exact hw (hout w hw' hwv)
  have hglobal := ResidueTrace.diagonal_product_formula ((x : F) / (p : F))
  rw [hprod] at hglobal
  rw [A.residueTraceCharacter_apply, map_neg, AddChar.map_neg_eq_inv]
  have heq := Finset.prod_coe_sort A.Sf f
  change (∏ w : InfinitePlace F, archTraceCharacter w
    (algebraMap F w.Completion ((x : F) / (p : F)))) * (∏ w : A.Sf, f w.1) = (f v)⁻¹
  rw [heq]
  apply (eq_inv_iff_mul_eq_one).2
  convert hglobal using 1 <;> ac_rfl

private theorem approximateLocalInteger (v : HeightOneSpectrum (𝓞 F)) (o : v.adicCompletionIntegers F)
    (ε : ℝ) (hε : 0 < ε) : ∃ r : 𝓞 F,
    dist (algebraMap (𝓞 F) (v.adicCompletion F) r) (o : v.adicCompletion F) < ε := by
  obtain ⟨y, hy⟩ := (v.denseRange_algebraMap F).exists_dist_lt
    (o : v.adicCompletion F) (lt_min hε zero_lt_one)
  have hxy : Valued.v ((o : v.adicCompletion F) - algebraMap F (v.adicCompletion F) y) < 1 := by
    rw [← Valued.toNormedField.norm_lt_one_iff]
    simpa only [dist_eq_norm] using (lt_of_lt_of_le hy (min_le_right _ _))
  have hyint : v.valuation F y ≤ 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    change Valued.v (algebraMap F (v.adicCompletion F) y) ≤ 1
    rw [show algebraMap F (v.adicCompletion F) y =
      (o : v.adicCompletion F) - ((o : v.adicCompletion F) - algebraMap F (v.adicCompletion F) y) by ring]
    exact Valued.v.map_sub_le o.property hxy.le
  obtain ⟨z, hz0, hzε⟩ := NormedField.exists_norm_lt (v.adicCompletion F) hε
  have hz : z ≠ 0 := norm_pos_iff.mp hz0
  let γ : (ℤᵐ⁰)ˣ := Units.mk0 (Valued.v z) ((Valuation.ne_zero_iff (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).2 hz)
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer hyint γ
  have hr' : ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r - y)‖ < ‖z‖ := by
    rw [Valued.toNormedField.norm_lt_iff]
    change Valued.v (↑(algebraMap (𝓞 F) F r - y) : v.adicCompletion F) < _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hr
  refine ⟨r, ?_⟩
  have hr'' : dist (algebraMap (𝓞 F) (v.adicCompletion F) r)
      (algebraMap F (v.adicCompletion F) y) < ε := by
    rw [dist_eq_norm]
    rw [map_sub] at hr'
    exact hr'.trans hzε
  exact lt_of_le_of_lt (IsUltrametricDist.dist_triangle_max _ _ _) (max_lt hr''
    (by simpa [dist_comm] using (lt_of_lt_of_le hy (min_le_left _ _))))

theorem residueTraceCharacter_prime_ne_one (A : SArithmeticData F)
    (hS : A.ContainsTraceBadPlaces) (B : Subgroup A.V)
    (I : A.Exterior) (hI : I.val.IsPrime) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (hap : (a : F) = (p : F)) (ha : A.IsAllowed B a) :
    A.residueTraceCharacter hS I p hp ≠ 1 := by
  let v : HeightOneSpectrum (𝓞 F) := ⟨I.val, hI, I.property.1⟩
  have hv : v ∉ A.Sf := by
    intro hv
    have h := (A.exterior_iff ⟨I.val, I.property.1⟩).mp I.property.2 v hv
    change I.val ⊔ I.val = ⊤ at h
    rw [sup_idem] at h
    exact hI.ne_top h
  let ι : A.R →+* v.adicCompletionIntegers F :=
    (algebraMap F (v.adicCompletion F)).comp A.R.val |>.codRestrict
      (v.adicCompletionIntegers F) (by
        intro r
        rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        change Valued.v (algebraMap F (v.adicCompletion F) (r : F)) ≤ 1
        rw [HeightOneSpectrum.algebraMap_adicCompletion]
        simp only [Function.comp_apply, Algebra.algebraMap_self]
        change Valued.v (↑(r : F) : v.adicCompletion F) ≤ 1
        rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        exact Set.integer_valuation_le_one _ _ r hv)
  have hpval : v.valuation F (p : F) < 1 := by
    have hle : A.extendIdeal I ≤ Ideal.comap ι (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro t ht
      change ι (algebraMap (𝓞 F) A.R t) ∈ IsLocalRing.maximalIdeal _
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) t) ≠ 1
      change Valued.v (algebraMap F (v.adicCompletion F) (t : F)) ≠ 1
      rw [HeightOneSpectrum.algebraMap_adicCompletion]
      simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact ne_of_lt ((v.valuation_lt_one_iff_mem (K := F) t).2 ht)
    have hp' := hle (hp.2 ▸ Ideal.subset_span (Set.mem_singleton p))
    change ι p ∈ IsLocalRing.maximalIdeal _ at hp'
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hp'
    have hpne : v.valuation F (p : F) ≠ 1 := by
      change Valued.v (algebraMap F (v.adicCompletion F) (p : F)) ≠ 1 at hp'
      simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        Algebra.algebraMap_self, RingHom.id_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hp'
    exact lt_of_le_of_ne (Set.integer_valuation_le_one _ _ p hv) hpne
  intro heq
  have hchar (r : 𝓞 F) : ResidueTrace.localTraceCharacter v
      (algebraMap F (v.adicCompletion F) (-((r : F) / (p : F)))) = 1 := by
    change ResidueTrace.localTraceCharacter v
      (algebraMap F (v.adicCompletion F) (-((algebraMap (𝓞 F) A.R r : F) / (p : F)))) = 1
    rw [← A.residueTraceCharacter_prime_local hS B I v rfl p hp a hap ha
      (algebraMap (𝓞 F) A.R r), heq]
    rfl
  let z := algebraMap F (v.adicCompletion F) (-(p : F)⁻¹)
  have hzchar (o : v.adicCompletionIntegers F) : ResidueTrace.localTraceCharacter v
      (z * (o : v.adicCompletion F)) = 1 := by
    let f : v.adicCompletion F → Circle := fun x => ResidueTrace.localTraceCharacter v (z * x)
    have hf : Continuous f := (ResidueTrace.continuous_localTraceCharacter v).comp
      (continuous_const.mul continuous_id)
    have ho : (o : v.adicCompletion F) ∈ closure (Set.range (algebraMap (𝓞 F) (v.adicCompletion F))) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨r, hr⟩ := approximateLocalInteger v o ε hε
      exact ⟨_, ⟨r, rfl⟩, by simpa [dist_comm] using hr⟩
    have hr (r : 𝓞 F) : f (algebraMap (𝓞 F) (v.adicCompletion F) r) = 1 := by
      change ResidueTrace.localTraceCharacter v
        (algebraMap F (v.adicCompletion F) (-(p : F)⁻¹) *
          algebraMap (𝓞 F) (v.adicCompletion F) r) = 1
      convert hchar r using 1
      simp only [map_neg, map_inv₀, map_div₀, div_eq_mul_inv, map_mul]
      change ResidueTrace.localTraceCharacter v
        (-(algebraMap F (v.adicCompletion F) (p : F))⁻¹ *
          algebraMap F (v.adicCompletion F) (r : F)) = _
      rw [neg_mul, mul_comm]
    exact closure_minimal (by rintro _ ⟨r, rfl⟩; exact hr r)
      (isClosed_eq hf continuous_const) ho
  have hzint := (hS v hv z).1 hzchar
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hzint
  change Valued.v (algebraMap F (v.adicCompletion F) (-(p : F)⁻¹)) ≤ 1 at hzint
  rw [HeightOneSpectrum.algebraMap_adicCompletion] at hzint
  simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_neg, map_inv₀] at hzint
  rw [Valuation.map_neg, map_inv₀] at hzint
  have hpF : (p : F) ≠ 0 := by exact_mod_cast hp.1
  have hp0 : 0 < v.valuation F (p : F) := (Valuation.pos_iff (v.valuation F)).2 hpF
  exact (not_le_of_gt (one_lt_inv₀ hp0 |>.2 hpval)) hzint

theorem traceCharacter_isPrimitive_of_equiv {R R' : Type*} [CommRing R] [CommRing R']
    (e : R ≃+* R') (χ : AddChar R Circle) (ψ : AddChar R' Circle)
    (hψ : ψ.IsPrimitive) (hχ : ∀ x, χ x = ψ (e x)) : χ.IsPrimitive := by
  intro x hx htrivial
  have he : e x ≠ 0 := by simpa using hx
  apply hψ he
  apply AddChar.eq_one_iff.mpr
  intro y
  obtain ⟨y, rfl⟩ := e.surjective y
  have hh := congrArg (fun f : AddChar R Circle => f y) htrivial
  simp only [AddChar.mulShift_apply, AddChar.one_apply] at hh
  simpa [AddChar.mulShift_apply, hχ, map_mul] using hh

theorem residueTraceCharacter_squarefree_primitive (A : SArithmeticData F)
    (hS : A.ContainsTraceBadPlaces) (B : Subgroup A.V)
    (I : A.Exterior) (hI : Squarefree I.val) (c : A.R) (hc : A.Generates I c)
    (a : Fˣ) (hac : (a : F) = (c : F)) (ha : A.IsAllowed B a) :
    (A.residueTraceCharacter hS I c hc).IsPrimitive := by
  intro x hx heq
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hxI : x ∉ A.extendIdeal I := by
    intro hxmem
    exact hx (Ideal.Quotient.eq_zero_iff_mem.mpr hxmem)
  obtain ⟨y, hy⟩ := ResidueTraceFactorProductFormula.principalResidue_separation
    ResidueTrace.baseEmbedding
    (fun v => (ResidueTrace.baseEmbedding_spec v).1)
    (fun v => (ResidueTrace.baseEmbedding_spec v).2) A hS I c hc x hxI
  have h := congrArg (fun χ : AddChar (A.R ⧸ A.extendIdeal I) Circle =>
    χ (Ideal.Quotient.mk (A.extendIdeal I) y)) heq
  rw [AddChar.mulShift_apply, ← map_mul, A.residueTraceCharacter_apply] at h
  exact hy h

end DedekindZetaZeroFree.SArithmeticData

end
