module

public import DedekindZetaZeroFree.CharacterSums.Gauss.FiniteSupportReciprocityCancellation

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.WeightedFiniteCoefficient
noncomputable section
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]

abbrev ExteriorPrime (A : SArithmeticData F) :=
  {p : HeightOneSpectrum (𝓞 F) // p.asIdeal ⊔ A.cS = ⊤}

def primeIdeal (A : SArithmeticData F) (p : ExteriorPrime A) : A.Exterior :=
  ⟨p.val.asIdeal, p.val.ne_bot, p.property⟩

def fieldUnit (A : SArithmeticData F) (a : A.R) (ha : a ≠ 0) : Fˣ :=
  Units.mk0 (a : F) (by exact_mod_cast ha)

structure ArithmeticCompatibility (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (G : A.GaussCorrectionOutput σ η hS) : Prop where
  generator_allowed : ∀ I : A.Exterior,
    A.IsAllowed G.B (fieldUnit A (D.generator I) (D.generates I).1)
  additive_recipe : ∀ x : F,
    D.additiveCharacter x = (A.fieldTraceCharacter x : ℂ)
  character_recipe : ∀ (I : A.Exterior) (a : A.R) (ha : A.Generates I a),
    D.character a = GeneratorInvariance.transportCharacter _ _ ha.2.symm
      (A.sexticResiduePowerChar σ I 1)
  gammaTwo_recipe : ∀ c : ExteriorSquarefreeIdeal A.cS,
    D.gammaTwo c = A.idealGauss σ hS c.val (D.generator c.val) (D.generates c.val) 2
  theta_recipe : ∀ (a : A.R) (ha : a ≠ 0),
    D.theta a =
      (A.correctionLS G.Λ G.G G.η_id (A.diagonal (fieldUnit A a ha)) : ℂ)

namespace Proof
open UniqueFactorizationMonoid

theorem support_factor (A : SArithmeticData F) (I : A.Exterior)
    (P : Finset (ExteriorPrime A))
    (hP : ∀ p : ExteriorPrime A, p ∉ P → idealPrimeExponent p.val.asIdeal I.val = 0) :
    I.val = ∏ p ∈ P, p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal I.val := by
  let Q := P.image (fun p => p.val.asIdeal)
  have hsub : idealPrimeSupport I.val ⊆ Q := by
    intro p hp
    have hp' : p ∈ normalizedFactors I.val := Multiset.mem_toFinset.mp hp
    have hprime := prime_of_normalized_factor p hp'
    let v : HeightOneSpectrum (𝓞 F) := ⟨p, Ideal.isPrime_of_prime hprime, hprime.ne_zero⟩
    have hv : p ⊔ A.cS = ⊤ := by
      apply top_unique
      rw [← I.property.2]
      exact sup_le_sup_right (Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hp')) _
    let ep : ExteriorPrime A := ⟨v, hv⟩
    have hep : ep ∈ P := by
      by_contra hn
      have hz := hP ep hn
      exact Multiset.count_ne_zero.mpr hp' hz
    exact Finset.mem_image.mpr ⟨ep, hep, rfl⟩
  have hq : I.val = ∏ p ∈ Q, p ^ idealPrimeExponent p I.val := by
    calc
      I.val = ∏ p ∈ idealPrimeSupport I.val, p ^ idealPrimeExponent p I.val :=
        ((Finset.prod_multiset_count (normalizedFactors I.val)).symm.trans
          (Ideal.prod_normalizedFactors_eq_self I.property.1)).symm
      _ = ∏ p ∈ Q, p ^ idealPrimeExponent p I.val := by
        apply Finset.prod_subset hsub
        intro p hp hpn
        rw [show idealPrimeExponent p I.val = 0 from Multiset.count_eq_zero.mpr
          (by simpa only [idealPrimeSupport, Multiset.mem_toFinset] using hpn), pow_zero]
  refine hq.trans ?_
  exact Finset.prod_image (f := fun p => p ^ idealPrimeExponent p I.val)
    (g := fun p : ExteriorPrime A => p.val.asIdeal) (fun a ha b hb hab => by
      apply Subtype.ext
      exact HeightOneSpectrum.asIdeal_injective hab)

theorem ls_mul (A : SArithmeticData F)
    (Φ : A.ArithmeticIdeleClasses →* Circle) (x y : A.G) :
    A.ideleSInverseProduct Φ (x * y) =
      A.ideleSInverseProduct Φ x * A.ideleSInverseProduct Φ y := by
  simp only [SArithmeticData.ideleSInverseProduct, Prod.fst_mul, Prod.snd_mul,
    Pi.mul_apply, map_mul, mul_inv, Finset.prod_mul_distrib]
  ac_rfl

def thetaHom (A : SArithmeticData F) (Φ : A.ArithmeticIdeleClasses →* Circle) : Fˣ →* ℂ :=
  Circle.coeHom.comp (({
    toFun := A.ideleSInverseProduct Φ
    map_one' := by simp [SArithmeticData.ideleSInverseProduct]
    map_mul' := ls_mul A Φ } : A.G →* Circle).comp A.diagonal)

theorem thetaHom_unit (A : SArithmeticData F)
    (Φ : A.ArithmeticIdeleClasses →* Circle)
    (hu : ∀ ε : A.U, A.ideleSInverseProduct Φ (A.diagonal ε.val) = 1)
    (v : A.Rˣ) : thetaHom A Φ (fieldUnit A (v : A.R) v.ne_zero) = 1 := by
  have he : fieldUnit A (v : A.R) v.ne_zero = (A.unitEquiv.symm v).val := by
    apply Units.ext
    rfl
  change (A.ideleSInverseProduct Φ (A.diagonal _) : ℂ) = 1
  rw [he, hu, Circle.coe_one]

theorem theta_associated (A : SArithmeticData F)
    (Φ : A.ArithmeticIdeleClasses →* Circle)
    (hu : ∀ ε : A.U, A.ideleSInverseProduct Φ (A.diagonal ε.val) = 1)
    (a b : A.R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : Ideal.span {a} = Ideal.span {b}) :
    thetaHom A Φ (fieldUnit A a ha) = thetaHom A Φ (fieldUnit A b hb) := by
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hab
  have he : fieldUnit A b hb = fieldUnit A a ha * fieldUnit A (v : A.R) v.ne_zero := by
    apply Units.ext
    change (b : F) = (a : F) * (v : A.R)
    exact congrArg (fun t : A.R => (t : F)) hv.symm
  rw [he, map_mul, thetaHom_unit A Φ hu, mul_one]

theorem span_prod (A : SArithmeticData F) {ι : Type*} (P : Finset ι) (f : ι → A.R) :
    Ideal.span {∏ p ∈ P, f p} = ∏ p ∈ P, Ideal.span {f p} := by
  induction P using Finset.induction_on with
  | empty => simp [Ideal.span_singleton_one, Ideal.one_eq_top]
  | @insert p P hp ih =>
    rw [Finset.prod_insert hp, Finset.prod_insert hp,
      ← Ideal.span_singleton_mul_span_singleton, ih]

theorem generator_prod_span (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (I : A.Exterior) (P : Finset (ExteriorPrime A))
    (hf : I.val = ∏ p ∈ P, p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal I.val) :
    Ideal.span {D.generator I} = Ideal.span
      {∏ p ∈ P, D.generator (primeIdeal A p) ^ idealPrimeExponent p.val.asIdeal I.val} := by
  rw [(D.generates I).2, span_prod A]
  change Ideal.map (algebraMap (𝓞 F) A.R) I.val = _
  conv_lhs => rw [hf]
  rw [show Ideal.map (algebraMap (𝓞 F) A.R) = Ideal.mapHom (algebraMap (𝓞 F) A.R) from rfl,
    map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  change Ideal.map (algebraMap (𝓞 F) A.R) (p.val.asIdeal ^ _) = _
  rw [Ideal.map_pow, ← Ideal.span_singleton_pow, (D.generates (primeIdeal A p)).2]
  rfl

theorem fieldUnit_mul (A : SArithmeticData F) (a b : A.R) (ha : a ≠ 0) (hb : b ≠ 0) :
    fieldUnit A (a * b) (mul_ne_zero ha hb) = fieldUnit A a ha * fieldUnit A b hb := by
  apply Units.ext
  rfl

theorem fieldUnit_prod {ι : Type*} (A : SArithmeticData F) (P : Finset ι)
    (f : ι → A.R) (hf : ∀ p, f p ≠ 0) :
    fieldUnit A (∏ p ∈ P, f p) (Finset.prod_ne_zero_iff.mpr (fun p _ => hf p)) =
    ∏ p ∈ P, fieldUnit A (f p) (hf p) := by
  apply Units.ext
  change ((∏ p ∈ P, f p : A.R) : F) = _
  change ((∏ p ∈ P, f p : A.R) : F) =
    (Units.coeHom F) (∏ p ∈ P, fieldUnit A (f p) (hf p))
  rw [map_prod]
  simp [fieldUnit]

theorem theta_factor (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (G : A.GaussCorrectionOutput σ η hS) (hD : ArithmeticCompatibility A D σ η hS G)
    (I : A.Exterior) (P : Finset (ExteriorPrime A))
    (hf : I.val = ∏ p ∈ P, p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal I.val) :
    D.theta (D.generator I) = ∏ p ∈ P,
      D.theta (D.generator (primeIdeal A p)) ^ idealPrimeExponent p.val.asIdeal I.val := by
  let Φ := A.correctionTheta G.Λ G.G G.η_id
  let π := fun p => D.generator (primeIdeal A p)
  let v := fun p : ExteriorPrime A => idealPrimeExponent p.val.asIdeal I.val
  have hn : ∀ p, π p ^ v p ≠ 0 := fun p => pow_ne_zero _ (D.generates _).1
  rw [hD.theta_recipe _ (D.generates I).1]
  change thetaHom A Φ (fieldUnit A (D.generator I) _) = _
  rw [theta_associated A Φ G.theta_unit _ _ (D.generates I).1
    (Finset.prod_ne_zero_iff.mpr (fun p _ => hn p)) (generator_prod_span A D I P hf),
    fieldUnit_prod A P _ hn, map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have he : fieldUnit A (π p ^ v p) (hn p) = fieldUnit A (π p) (D.generates _).1 ^ v p := by
    apply Units.ext
    simp [fieldUnit]
  rw [he, map_pow, hD.theta_recipe _ (D.generates _).1]
  rfl

theorem norm_factor (A : SArithmeticData F) (I : A.Exterior) (P : Finset (ExteriorPrime A))
    (hf : I.val = ∏ p ∈ P, p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal I.val) :
    A.exteriorNorm I = ∏ p ∈ P,
      A.exteriorNorm (primeIdeal A p) ^ idealPrimeExponent p.val.asIdeal I.val := by
  unfold SArithmeticData.exteriorNorm idealNorm
  conv_lhs => rw [hf]
  rw [map_prod]
  push_cast
  simp only [map_pow, Nat.cast_pow]
  rfl

theorem power_factor (A : SArithmeticData F) (I : A.Exterior) (P : Finset (ExteriorPrime A))
    (hf : I.val = ∏ p ∈ P, p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal I.val) (a : ℂ) :
    comparisonRealPower (A.exteriorNorm I) a = ∏ p ∈ P,
      comparisonRealPower (A.exteriorNorm (primeIdeal A p))
        ((idealPrimeExponent p.val.asIdeal I.val : ℂ) * a) := by
  rw [norm_factor A I P hf]
  unfold comparisonRealPower
  rw [Real.log_prod (fun p hp => pow_ne_zero _ (ne_of_gt
    (lt_of_lt_of_le zero_lt_one (idealNorm_ge_one _ p.val.ne_bot))))]
  simp only [Real.log_pow, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast,
    Finset.mul_sum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro p hp
  congr 1
  ring

end Proof

end
end DedekindZetaZeroFree.WeightedFiniteCoefficient
