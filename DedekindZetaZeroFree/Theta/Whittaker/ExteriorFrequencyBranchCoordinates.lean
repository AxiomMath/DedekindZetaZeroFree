module

public import DedekindZetaZeroFree.Theta.Profiles.ReflectionGaussianAndSixthUnitInvariance
public import DedekindZetaZeroFree.CharacterSums.DavenportHasse.PrimaryAngularNormPhases
public import DedekindZetaZeroFree.Arithmetic.Ideals.ExteriorEulerProducts.PrimeExponentCoordinates

@[expose] public section

namespace DedekindZetaZeroFree.ThetaBranch
noncomputable section
open scoped NumberField BigOperators Classical
open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

def order (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ℤ :=
  -WithZero.log (p.valuation F (x : F))

def support (I : Ideal (𝓞 F)) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (idealPrimeSupport I).preimage HeightOneSpectrum.asIdeal
    HeightOneSpectrum.asIdeal_injective.injOn

abbrev ExteriorPrime (A : SArithmeticData F) :=
  {p : HeightOneSpectrum (𝓞 F) // p ∉ A.Sf}

def primeIdeal (A : SArithmeticData F) (p : ExteriorPrime A) : A.Exterior := by
  refine ⟨p.val.asIdeal, p.val.ne_bot, ?_⟩
  apply (A.exterior_iff ⟨p.val.asIdeal, p.val.ne_bot⟩).mpr
  intro v hv
  apply p.val.isMaximal.coprime_of_ne v.isMaximal
  intro h
  exact p.property (HeightOneSpectrum.asIdeal_injective h ▸ hv)

structure AllowedRecipe (A : SArithmeticData F) where
  B : Subgroup A.V
  complement : IsCompl A.E B
  unit_kernel : A.U ⊓ (ThetaReflectionData.rationalClass A).ker =
    ThetaReflectionData.rationalGamma A
  generator : A.Exterior → Fˣ
  generates : ∀ I : A.Exterior, ∃ r : A.R,
    A.Generates I r ∧ (generator I : F) = (r : F)
  allowed : ∀ I : A.Exterior, ThetaReflectionData.rationalClass A (generator I) ∈ B

structure UnitRepresentatives (A : SArithmeticData F) where
  representative : A.UnitQuotient → A.U
  represents : ∀ ε : A.UnitQuotient,
    QuotientGroup.mk (representative ε) = ε

def IsUnitResidue (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ)
    (t : DHCubic.Residue F p) : Prop :=
  ∃ a b : 𝓞 F, a ∉ p.asIdeal ∧ b ∉ p.asIdeal ∧
    (x : F) = (a : F) / ((b : 𝓞 F) : F) ∧
    t = Ideal.Quotient.mk p.asIdeal a / Ideal.Quotient.mk p.asIdeal b

theorem existsUnique_unitResidue (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ)
    (hx : order p x = 0) : ∃! t, IsUnitResidue p x t := by
  have hval : p.valuation F (x : F) = 1 := by
    have hlog : WithZero.log (p.valuation F (x : F)) = 0 := by
      simpa only [order, neg_eq_zero] using hx
    have hn : p.valuation F (x : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
    rw [← WithZero.exp_log hn, hlog, WithZero.exp_zero]
  obtain ⟨a, b, hab⟩ := p.exists_primeCompl_mul_eq_of_integer (x : F) hval.le
  have hb : (b : 𝓞 F) ∉ p.asIdeal := b.property
  have hbF : ((b : 𝓞 F) : F) ≠ 0 := by
    exact_mod_cast (fun h => hb (h ▸ p.asIdeal.zero_mem) : (b : 𝓞 F) ≠ 0)
  have ha : a ∉ p.asIdeal := by
    apply p.valuation_eq_one_iff_notMem (K := F).mp
    rw [← hab, map_mul, hval, p.valuation_eq_one_iff_notMem (K := F).mpr hb, one_mul]
  have hxdiv : (x : F) = (a : F) / ((b : 𝓞 F) : F) := (eq_div_iff hbF).mpr hab
  refine ⟨Ideal.Quotient.mk p.asIdeal a / Ideal.Quotient.mk p.asIdeal b,
    ⟨a, b, ha, hb, hxdiv, rfl⟩, ?_⟩
  intro t ht
  obtain ⟨c, d, hc, hd, hxcd, ht⟩ := ht
  rw [ht]
  have hdF : (d : F) ≠ 0 := by
    exact_mod_cast (fun h => hd (h ▸ p.asIdeal.zero_mem) : d ≠ 0)
  have hac : a * d = c * b := by
    apply NumberField.RingOfIntegers.ext
    exact (div_eq_div_iff hbF hdF).mp (hxdiv.symm.trans hxcd)
  apply (div_eq_div_iff
    (fun h => hd (Ideal.Quotient.eq_zero_iff_mem.mp h))
    (fun h => hb (Ideal.Quotient.eq_zero_iff_mem.mp h))).mpr
  simpa only [map_mul] using congrArg (Ideal.Quotient.mk p.asIdeal) hac.symm

def unitResidue (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : DHCubic.Residue F p :=
  if hx : order p x = 0 then (existsUnique_unitResidue p x hx).exists.choose else 0

theorem unitResidue_ne_zero (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ)
    (hx : order p x = 0) : unitResidue p x ≠ 0 := by
  have ht : IsUnitResidue p x (unitResidue p x) := by
    simpa only [unitResidue, dif_pos hx] using (existsUnique_unitResidue p x hx).exists.choose_spec
  obtain ⟨a, b, ha, hb, _, ht⟩ := ht
  rw [ht]
  apply div_ne_zero
  · exact fun h => ha ((Ideal.Quotient.eq_zero_iff_mem).mp h)
  · exact fun h => hb ((Ideal.Quotient.eq_zero_iff_mem).mp h)

def residueCharacter (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ExteriorPrime A) : MulChar (DHCubic.Residue F p.val) ℂ :=
  ((DHCubic.existsUnique_normalizedSextic F A p.val p.property).exists.choose).ringHomComp
    (σ.comp (algebraMap (𝓞 F) F))

def symbol (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ExteriorPrime A) (x : Fˣ) : ℂ :=
  residueCharacter A σ p (unitResidue p.val x)

structure RowFactorization (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) where
  rowIdeal : A.Exterior
  h : A.Exterior
  d : A.Exterior
  powerful : Powerful h.val
  squarefree : Squarefree d.val
  coprime : h.val ⊔ d.val = ⊤
  factorization : rowIdeal.val = h.val * d.val
  row_generates : A.Generates rowIdeal m.val
  epsilon : A.U
  row_eq : ThetaReflectionData.rowUnit A m = epsilon.val * G.generator rowIdeal

def rowIndex (A : SArithmeticData F) (m : ThetaReflectionData.Row A)
    (p : HeightOneSpectrum (𝓞 F)) : Fin 6 :=
  ⟨(order p (ThetaReflectionData.rowUnit A m) % 6).toNat, by omega⟩

structure Branch (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m) where
  f : A.Exterior
  squarefree : Squarefree f.val
  divides_radical : f.val ∣ idealRadical D.h.val
  mandatory : ∀ p ∈ support D.h.val, rowIndex A m p ≠ 0 → p ∈ support f.val

structure Coordinates (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) where
  epsilon : A.UnitQuotient
  a : A.Exterior
  c : A.Exterior
  n : A.Exterior
  a_supported : IdealSupportedOn a.val b.f.val
  a_exponents : ∀ p ∈ support b.f.val,
    idealPrimeExponent p.asIdeal a.val % 3 = 0 ∨
      idealPrimeExponent p.asIdeal a.val % 3 = 1
  c_squarefree : Squarefree c.val
  coprime : (c.val * n.val) ⊔ (D.d.val * b.f.val) = ⊤

def coordinateRepresentative (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D)
    (v : Coordinates A G m D b) : Fˣ :=
  (U.representative v.epsilon).val * G.generator v.a * G.generator v.c *
    G.generator v.n ^ 3 / (G.generator D.d * G.generator b.f) ^ 2

def coordinateFrequency (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D)
    (v : Coordinates A G m D b) : ThetaReflectionData.Frequency A :=
  QuotientGroup.mk (coordinateRepresentative A G U m D b v)

def Supported (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (ν : ThetaReflectionData.Frequency A) : Prop :=
  ∃ x : Fˣ, QuotientGroup.mk x = ν ∧
    (∀ p ∈ support D.d.val, order p x = -2) ∧
    (∀ p ∈ support b.f.val, 0 ≤ order p x + 2 ∧
      ((order p x + 2) % 3 = 0 ∨ (order p x + 2) % 3 = 1)) ∧
    (∀ p : ExteriorPrime A, p.val ∉ support D.d.val → p.val ∉ support b.f.val →
      0 ≤ order p.val x ∧ (order p.val x % 3 = 0 ∨ order p.val x % 3 = 1))

theorem support_outside (A : SArithmeticData F) (I : A.Exterior)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p ∈ support I.val) : p ∉ A.Sf := by
  have hfac : p.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I.val := by
    simpa only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using hp
  have hIp : I.val ≤ p.asIdeal := (Ideal.mem_normalizedFactors_iff I.property.1).mp hfac |>.2
  intro hSf
  have hcS : A.cS ≤ p.asIdeal := by
    exact Ideal.IsPrime.prod_le p.isPrime |>.mpr ⟨p, hSf, le_rfl⟩
  have htop : (⊤ : Ideal (𝓞 F)) ≤ p.asIdeal := by
    rw [← I.property.2]
    exact sup_le hIp hcS
  exact p.isPrime.ne_top (top_le_iff.mp htop)

private theorem order_mul (p : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    order p (x * y) = order p x + order p y := by
  simp only [order, Units.val_mul, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
    ((Valuation.ne_zero_iff _).mpr y.ne_zero), neg_add]

private theorem order_zpow (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ) (n : ℤ) :
    order p (x ^ n) = n * order p x := by
  simp only [order, Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow,
    smul_eq_mul]
  ring

private theorem order_unit (A : SArithmeticData F) (p : ExteriorPrime A) (u : A.U) :
    order p.val u.val = 0 := by
  have hv : p.val.valuation F (u.val : F) = 1 := by
    exact u.property p.val p.property
  simp [order, hv]

 def boundIdeal (A : SArithmeticData F)
    (p : ExteriorPrime A) (n : ℕ) : Ideal A.R where
  carrier := {a | p.val.valuation F (a : F) ≤ WithZero.exp (-(n : ℤ))}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change p.val.valuation F ((a : F) + (b : F)) ≤ _
    exact (ValuationClass.map_add_le_max _ _ _).trans (max_le ha hb)
  smul_mem' := by
    intro a b hb
    change p.val.valuation F ((a : F) * (b : F)) ≤ _
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (a.property p.val p.property) zero_le).trans (by simpa using hb)

theorem generator_order (A : SArithmeticData F) (G : AllowedRecipe A)
    (I : A.Exterior) (p : ExteriorPrime A) :
    order p.val (G.generator I) = idealPrimeExponent p.val.asIdeal I.val := by
  classical
  let n := idealPrimeExponent p.val.asIdeal I.val
  have hdvd (k : ℕ) : p.val.asIdeal ^ k ∣ I.val ↔ k ≤ n := by
    rw [pow_dvd_iff_le_emultiplicity,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors p.val.irreducible I.property.1]
    simp [n, idealPrimeExponent]
  have hIn : I.val ≤ p.val.asIdeal ^ n := Ideal.dvd_iff_le.mp ((hdvd n).mpr le_rfl)
  have hnot : ¬ I.val ≤ p.val.asIdeal ^ (n + 1) := by
    rw [← Ideal.dvd_iff_le, hdvd]; omega
  obtain ⟨r, hr, he⟩ := G.generates I
  have hmap : A.extendIdeal I ≤ boundIdeal A p n := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change p.val.valuation F (a : F) ≤ WithZero.exp (-(n : ℤ))
    rw [p.val.valuation_of_algebraMap]
    exact (p.val.intValuation_le_pow_iff_mem a n).mpr (hIn ha)
  have hrv : p.val.valuation F (r : F) ≤ WithZero.exp (-(n : ℤ)) := by
    apply hmap
    rw [← hr.2]
    exact Ideal.subset_span (Set.mem_singleton r)
  obtain ⟨a, ha, han⟩ : ∃ a : 𝓞 F, a ∈ I.val ∧ a ∉ p.val.asIdeal ^ (n + 1) := by
    contrapose! hnot
    exact hnot
  have ham : algebraMap (𝓞 F) A.R a ∈ Ideal.span ({r} : Set A.R) := by
    rw [hr.2]
    exact Ideal.mem_map_of_mem _ ha
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp ham
  have hav : p.val.valuation F (a : F) ≤ p.val.valuation F (r : F) := by
    have hh := congrArg (fun t : A.R => (t : F)) hy
    change (a : F) = (r : F) * (y : F) at hh
    rw [hh, map_mul]
    exact (mul_le_mul_of_nonneg_left (y.property p.val p.property) zero_le).trans (by simp)
  have hrv' : ¬ p.val.valuation F (r : F) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    intro h
    apply han
    apply (p.val.intValuation_le_pow_iff_mem a (n + 1)).mp
    rw [← p.val.valuation_of_algebraMap (K := F)]
    exact hav.trans h
  have hnz : p.val.valuation F (r : F) ≠ 0 := by rw [← he]; exact (Valuation.ne_zero_iff _).mpr (G.generator I).ne_zero
  rw [← WithZero.exp_log hnz, WithZero.exp_le_exp] at hrv hrv'
  change -WithZero.log (p.val.valuation F (G.generator I : F)) = (n : ℤ)
  rw [he]
  push_cast at hrv'
  omega

def supportPrime (A : SArithmeticData F) (I : A.Exterior)
    (p : {p // p ∈ support I.val}) : ExteriorPrime A :=
  ⟨p.val, support_outside A I p.val p.property⟩

def localUnit (A : SArithmeticData F) (G : AllowedRecipe A)
    (p : ExteriorPrime A) (x : Fˣ) : Fˣ :=
  x / G.generator (primeIdeal A p) ^ order p.val x

theorem localUnit_order (A : SArithmeticData F) (G : AllowedRecipe A)
    (p : ExteriorPrime A) (x : Fˣ) : order p.val (localUnit A G p x) = 0 := by
  have hg : order p.val (G.generator (primeIdeal A p)) = 1 := by
    rw [generator_order]
    simp [primeIdeal, idealPrimeExponent,
      UniqueFactorizationMonoid.normalizedFactors_irreducible p.val.irreducible]
  rw [localUnit, div_eq_mul_inv, order_mul]
  rw [← zpow_neg_one, order_zpow, order_zpow, hg]
  ring

def gaussTwo (A : SArithmeticData F) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (p : ExteriorPrime A) : ℂ :=
  (Real.sqrt (Fintype.card (DHCubic.Residue F p.val) : ℝ) : ℂ)⁻¹ *
    gaussSum (residueCharacter A σ p ^ 2) (ψ p)

def scalar (A : SArithmeticData F) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (p : ExteriorPrime A) (j : Fin 6) (e : ℕ) : ℂ :=
  sexticReflectedNonzeroDigits (residueCharacter A σ p) (ψ p) j (e : ℤ) 1

def phaseExponent (j : Fin 6) (e : ℕ) : ℕ :=
  (if e = 0 then 8 - j.val else 4 + 2 * e) % 6

def omegaScalar (A : SArithmeticData F) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (p : ExteriorPrime A) : ℂ := scalar A σ ψ p 1 0

def dArgument (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D)
    (v : Coordinates A G m D b) (p : ExteriorPrime A) : Fˣ :=
  (U.representative v.epsilon).val * G.generator v.a * G.generator v.c *
    G.generator v.n ^ 3 *
    (G.generator D.d / G.generator (primeIdeal A p)) ^ (-2 : ℤ) *
    G.generator b.f ^ (-2 : ℤ)

def fArgument (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D)
    (v : Coordinates A G m D b) (p : ExteriorPrime A) : Fˣ :=
  (U.representative v.epsilon).val *
    (G.generator v.a / G.generator (primeIdeal A p) ^
      idealPrimeExponent p.val.asIdeal v.a.val) *
    G.generator v.c * G.generator v.n ^ 3 * G.generator D.d ^ (-2 : ℤ) *
    (G.generator b.f / G.generator (primeIdeal A p)) ^ (-2 : ℤ)

def cArgument (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D)
    (v : Coordinates A G m D b) (p : ExteriorPrime A) : Fˣ :=
  (U.representative v.epsilon).val * G.generator v.a *
    (G.generator v.c / G.generator (primeIdeal A p)) *
    (G.generator D.d * G.generator b.f) ^ (-2 : ℤ)

private lemma mem_support_iff (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (p : HeightOneSpectrum (𝓞 F)) : p ∈ support I ↔ I ≤ p.asIdeal := by
  simp only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset]
  exact Ideal.mem_normalizedFactors_iff hI |>.trans (and_iff_right p.isPrime)
private lemma exponent_zero (I : Ideal (𝓞 F)) (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∉ support I) : idealPrimeExponent p.asIdeal I = 0 := by
  apply Multiset.count_eq_zero.mpr
  simpa only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using hp
private lemma exponent_one (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hs : Squarefree I)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p ∈ support I) : idealPrimeExponent p.asIdeal I = 1 := by
  apply Multiset.count_eq_one_of_mem (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI |>.mp hs)
  simpa only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using hp
private lemma support_divides (I J : Ideal (𝓞 F)) (hJ : J ≠ ⊥) (h : I ∣ J)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p ∈ support I) : p ∈ support J := by
  have hI : I ≠ ⊥ := by
    intro hi
    obtain ⟨K, hK⟩ := h
    exact hJ (by simpa [hi] using hK)
  exact (mem_support_iff J hJ p).mpr ((Ideal.dvd_iff_le.mp h).trans ((mem_support_iff I hI p).mp hp))
private lemma support_radical (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (p : HeightOneSpectrum (𝓞 F)) : p ∈ support (idealRadical I) ↔ p ∈ support I := by
  simp only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset]
  rw [← Multiset.count_ne_zero, ← Multiset.count_ne_zero]
  change idealPrimeExponent p.asIdeal (idealRadical I) ≠ 0 ↔
    idealPrimeExponent p.asIdeal I ≠ 0
  rw [idealPrimeExponent_radical I hI _ p.prime]
  by_cases hp : p.asIdeal ∈ idealPrimeSupport I
  · simp only [if_pos hp]
    constructor
    · intro _
      exact Multiset.count_ne_zero.mpr (by simpa only [idealPrimeSupport, Multiset.mem_toFinset] using hp)
    · intro _; norm_num
  · simp only [if_neg hp, ne_eq, not_true_eq_false, false_iff, not_not]
    exact Multiset.count_eq_zero.mpr (by simpa only [idealPrimeSupport, Multiset.mem_toFinset] using hp)
private lemma disjoint_support (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hcop : I ⊔ J = ⊤) (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∈ support I) : p ∉ support J := by
  intro hq
  have ht : (⊤ : Ideal (𝓞 F)) ≤ p.asIdeal := by
    rw [← hcop]
    exact sup_le ((mem_support_iff I hI p).mp hp) ((mem_support_iff J hJ p).mp hq)
  exact p.isPrime.ne_top (top_le_iff.mp ht)
private lemma coprime_parts (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b) (p : HeightOneSpectrum (𝓞 F)) :
    (p ∈ support D.d.val ∨ p ∈ support b.f.val) →
      p ∉ support v.c.val ∧ p ∉ support v.n.val := by
  intro hp
  have hd : D.d.val * b.f.val ≤ p.asIdeal := by
    rcases hp with hp | hp
    · exact Ideal.mul_le_left.trans ((mem_support_iff _ D.d.property.1 p).mp hp)
    · exact Ideal.mul_le_right.trans ((mem_support_iff _ b.f.property.1 p).mp hp)
  have hcn : v.c.val * v.n.val ⊔ D.d.val * b.f.val = ⊤ := v.coprime
  constructor <;> intro h
  · have ht : (⊤ : Ideal (𝓞 F)) ≤ p.asIdeal := by
      rw [← hcn]; exact sup_le (Ideal.mul_le_left.trans ((mem_support_iff _ v.c.property.1 p).mp h)) hd
    exact p.isPrime.ne_top (top_le_iff.mp ht)
  · have ht : (⊤ : Ideal (𝓞 F)) ≤ p.asIdeal := by
      rw [← hcn]; exact sup_le (Ideal.mul_le_right.trans ((mem_support_iff _ v.n.property.1 p).mp h)) hd
    exact p.isPrime.ne_top (top_le_iff.mp ht)
private lemma supported_a (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p ∉ support b.f.val) : p ∉ support v.a.val := by
  intro ha
  apply hp
  simpa only [support, Finset.mem_preimage] using v.a_supported
    (show p.asIdeal ∈ idealPrimeSupport v.a.val by
      simpa only [support, Finset.mem_preimage] using ha)
private lemma f_in_h (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∈ support b.f.val) : p ∈ support D.h.val := by
  exact (support_radical _ D.h.property.1 p).mp
    (support_divides _ _ (idealRadical_squarefree_nonzero _ D.h.property.1).2 b.divides_radical p hp)
private lemma mul_order (p : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    order p (x * y) = order p x + order p y := by
  simp only [order, Units.val_mul, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
    ((Valuation.ne_zero_iff _).mpr y.ne_zero), neg_add]
private lemma zpow_order (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ) (n : ℤ) :
    order p (x ^ n) = n * order p x := by
  simp only [order, Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring
private lemma unit_order (A : SArithmeticData F) (p : ExteriorPrime A) (u : A.U) :
    order p.val u.val = 0 := by
  simp [order, u.property p.val p.property]
private lemma div_order (p : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    order p (x / y) = order p x - order p y := by
  rw [div_eq_mul_inv, mul_order, ← zpow_neg_one, zpow_order]; ring
private lemma pow_order (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ) (n : ℕ) :
    order p (x ^ n) = (n : ℤ) * order p x := by
  rw [← zpow_natCast, zpow_order]
private lemma prime_exp (A : SArithmeticData F) (p : ExteriorPrime A) :
    idealPrimeExponent p.val.asIdeal (primeIdeal A p).val = 1 := by
  simp [primeIdeal, idealPrimeExponent, UniqueFactorizationMonoid.normalizedFactors_irreducible p.val.irreducible]

theorem coefficient_arguments_units (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D)
    (v : Coordinates A G m D b) :
    (∀ p : ExteriorPrime A, p.val ∈ support D.d.val →
      order p.val (dArgument A G U m D b v p) = 0) ∧
    (∀ p : ExteriorPrime A, p.val ∈ support b.f.val →
      order p.val (fArgument A G U m D b v p) = 0) ∧
    (∀ p : ExteriorPrime A, p.val ∈ support v.c.val →
      order p.val (cArgument A G U m D b v p) = 0) := by
  have hdf (p : HeightOneSpectrum (𝓞 F)) (hp : p ∈ support D.d.val) : p ∉ support b.f.val := by
    intro hf
    exact disjoint_support _ _ D.h.property.1 D.d.property.1 D.coprime p (f_in_h A G m D b p hf) hp
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have hf := hdf p.val hp
    have ha := exponent_zero _ _ (supported_a A G m D b v p.val hf)
    have hc := exponent_zero _ _ (coprime_parts A G m D b v p.val (Or.inl hp)).1
    have hn := exponent_zero _ _ (coprime_parts A G m D b v p.val (Or.inl hp)).2
    have hd := exponent_one _ D.d.property.1 D.squarefree p.val hp
    have hf' := exponent_zero _ _ hf
    simp only [dArgument, mul_order, div_order, zpow_order, pow_order, unit_order,
      generator_order, prime_exp, ha, hc, hn, hd, hf']
    ring
  · intro p hp
    have hd := disjoint_support _ _ D.h.property.1 D.d.property.1 D.coprime p.val (f_in_h A G m D b p.val hp)
    have hc := exponent_zero _ _ (coprime_parts A G m D b v p.val (Or.inr hp)).1
    have hn := exponent_zero _ _ (coprime_parts A G m D b v p.val (Or.inr hp)).2
    have hd' := exponent_zero _ _ hd
    have hf := exponent_one _ b.f.property.1 b.squarefree p.val hp
    simp only [fArgument, mul_order, div_order, zpow_order, pow_order, unit_order,
      generator_order, prime_exp, hc, hn, hd', hf]
    ring
  · intro p hp
    have hnot : p.val ∉ support D.d.val ∧ p.val ∉ support b.f.val := by
      constructor <;> intro h
      · exact (coprime_parts A G m D b v p.val (Or.inl h)).1 hp
      · exact (coprime_parts A G m D b v p.val (Or.inr h)).1 hp
    have ha := exponent_zero _ _ (supported_a A G m D b v p.val hnot.2)
    have hd := exponent_zero _ _ hnot.1
    have hf := exponent_zero _ _ hnot.2
    have hc := exponent_one _ v.c.property.1 v.c_squarefree p.val hp
    simp only [cArgument, mul_order, div_order, zpow_order, pow_order, unit_order,
      generator_order, prime_exp, ha, hd, hf, hc]
    ring

def exactCoefficient (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b) : ℂ :=
  ((∏ p ∈ support D.h.val \ support b.f.val,
      (1 - (idealNorm p.asIdeal : ℂ)⁻¹)) /
    ((Real.sqrt (A.exteriorNorm v.c) : ℂ) * (A.exteriorNorm v.n : ℂ))) *
  (∏ p : {p // p ∈ support D.d.val},
    omegaScalar A σ ψ (supportPrime A D.d p) *
      symbol A σ (supportPrime A D.d p)
        (dArgument A G U m D b v (supportPrime A D.d p))) *
  (∏ p : {p // p ∈ support b.f.val},
    scalar A σ ψ (supportPrime A b.f p) (rowIndex A m p.val)
        (idealPrimeExponent p.val.asIdeal v.a.val) *
      symbol A σ (supportPrime A b.f p)
        (fArgument A G U m D b v (supportPrime A b.f p)) ^
          phaseExponent (rowIndex A m p.val) (idealPrimeExponent p.val.asIdeal v.a.val)) *
  (∏ p : {p // p ∈ support v.c.val},
    gaussTwo A σ ψ (supportPrime A v.c p) *
      symbol A σ (supportPrime A v.c p)
        (cArgument A G U m D b v (supportPrime A v.c p)) ^ 2)

def sphericalFactor (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (p : ExteriorPrime A) (x : Fˣ) : ℂ :=
  sexticSphericalCoefficient (residueCharacter A σ p) (ψ p) (order p.val x) *
    symbol A σ p (localUnit A G p x) ^ (2 * order p.val x)

def branchLocalFactor (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (p : ExteriorPrime A) (x : Fˣ) : ℂ :=
  if p.val ∈ support D.d.val ∪ support b.f.val then
    sexticReflectedNonzeroDigits (residueCharacter A σ p) (ψ p)
      (rowIndex A m p.val) (order p.val x + 2)
      (unitResidue p.val (localUnit A G p x))
  else if p.val ∈ support D.h.val then
    (1 - (idealNorm p.val.asIdeal : ℂ)⁻¹) * sphericalFactor A G σ ψ p x
  else sphericalFactor A G σ ψ p x

def branchCoefficient (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (x : Fˣ) : ℂ :=
  ∏ᶠ p : ExteriorPrime A, branchLocalFactor A G σ ψ m D b p x

namespace CanonicalCoefficientProof

private lemma ord_mul (p : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    order p (x * y) = order p x + order p y := by
  simp only [order, Units.val_mul, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
    ((Valuation.ne_zero_iff _).mpr y.ne_zero), neg_add]

private lemma ord_zpow (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ) (n : ℤ) :
    order p (x ^ n) = n * order p x := by
  simp only [order, Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow,
    smul_eq_mul]
  ring

private lemma ord_div (p : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    order p (x / y) = order p x - order p y := by
  rw [div_eq_mul_inv, ord_mul, ← zpow_neg_one, ord_zpow]; ring

private lemma ord_pow (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ) (n : ℕ) :
    order p (x ^ n) = (n : ℤ) * order p x := by
  rw [← zpow_natCast, ord_zpow]

private lemma exponent_zero_aux (I : Ideal (𝓞 F)) (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∉ support I) : idealPrimeExponent p.asIdeal I = 0 := by
  apply Multiset.count_eq_zero.mpr
  simpa only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using hp

private lemma exponent_one_aux (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hs : Squarefree I)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p ∈ support I) : idealPrimeExponent p.asIdeal I = 1 := by
  apply Multiset.count_eq_one_of_mem
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI |>.mp hs)
  simpa only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using hp

private lemma mem_support_iff_aux (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (p : HeightOneSpectrum (𝓞 F)) : p ∈ support I ↔ I ≤ p.asIdeal := by
  simp only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset]
  exact Ideal.mem_normalizedFactors_iff hI |>.trans (and_iff_right p.isPrime)

private lemma support_divides_aux (I J : Ideal (𝓞 F)) (hJ : J ≠ ⊥) (h : I ∣ J)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p ∈ support I) : p ∈ support J := by
  have hI : I ≠ ⊥ := by
    intro hi
    obtain ⟨K, hK⟩ := h
    exact hJ (by simpa [hi] using hK)
  exact (mem_support_iff_aux J hJ p).mpr
    ((Ideal.dvd_iff_le.mp h).trans ((mem_support_iff_aux I hI p).mp hp))

private lemma support_radical_aux (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (p : HeightOneSpectrum (𝓞 F)) : p ∈ support (idealRadical I) ↔ p ∈ support I := by
  simp only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset]
  rw [← Multiset.count_ne_zero, ← Multiset.count_ne_zero]
  change idealPrimeExponent p.asIdeal (idealRadical I) ≠ 0 ↔
    idealPrimeExponent p.asIdeal I ≠ 0
  rw [idealPrimeExponent_radical I hI _ p.prime]
  by_cases hp : p.asIdeal ∈ idealPrimeSupport I
  · simp only [if_pos hp]
    constructor
    · intro _
      exact Multiset.count_ne_zero.mpr
        (by simpa only [idealPrimeSupport, Multiset.mem_toFinset] using hp)
    · intro _; norm_num
  · simp only [if_neg hp, ne_eq, not_true_eq_false, false_iff, not_not]
    exact Multiset.count_eq_zero.mpr
      (by simpa only [idealPrimeSupport, Multiset.mem_toFinset] using hp)

private lemma disjoint_support_aux (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hcop : I ⊔ J = ⊤) (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∈ support I) : p ∉ support J := by
  intro hq
  have ht : (⊤ : Ideal (𝓞 F)) ≤ p.asIdeal := by
    rw [← hcop]
    exact sup_le ((mem_support_iff_aux I hI p).mp hp) ((mem_support_iff_aux J hJ p).mp hq)
  exact p.isPrime.ne_top (top_le_iff.mp ht)

private lemma unit_ord_aux (A : SArithmeticData F) (p : ExteriorPrime A) (u : A.U) :
    order p.val u.val = 0 := by
  simp [order, u.property p.val p.property]

private lemma f_in_h_aux (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∈ support b.f.val) : p ∈ support D.h.val :=
  (support_radical_aux _ D.h.property.1 p).mp
    (support_divides_aux _ _ (idealRadical_squarefree_nonzero _ D.h.property.1).2
      b.divides_radical p hp)

private lemma supported_a_aux (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p ∉ support b.f.val) : p ∉ support v.a.val := by
  intro ha
  exact hp (by
    simpa only [support, Finset.mem_preimage] using
      v.a_supported (show p.asIdeal ∈ idealPrimeSupport v.a.val by
        simpa only [support, Finset.mem_preimage] using ha))

private lemma coprime_parts_aux (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b) (p : HeightOneSpectrum (𝓞 F)) :
    (p ∈ support D.d.val ∨ p ∈ support b.f.val) →
      p ∉ support v.c.val ∧ p ∉ support v.n.val := by
  intro hp
  have hd : D.d.val * b.f.val ≤ p.asIdeal := by
    rcases hp with hp | hp
    · exact Ideal.mul_le_left.trans ((mem_support_iff_aux _ D.d.property.1 p).mp hp)
    · exact Ideal.mul_le_right.trans ((mem_support_iff_aux _ b.f.property.1 p).mp hp)
  have hcn : v.c.val * v.n.val ⊔ D.d.val * b.f.val = ⊤ := v.coprime
  constructor <;> intro h
  · have ht : (⊤ : Ideal (𝓞 F)) ≤ p.asIdeal := by
      rw [← hcn]
      exact sup_le (Ideal.mul_le_left.trans
        ((mem_support_iff_aux _ v.c.property.1 p).mp h)) hd
    exact p.isPrime.ne_top (top_le_iff.mp ht)
  · have ht : (⊤ : Ideal (𝓞 F)) ≤ p.asIdeal := by
      rw [← hcn]
      exact sup_le (Ideal.mul_le_right.trans
        ((mem_support_iff_aux _ v.n.property.1 p).mp h)) hd
    exact p.isPrime.ne_top (top_le_iff.mp ht)

private lemma not_mem_d_of_mem_f (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∈ support b.f.val) : p ∉ support D.d.val :=
  disjoint_support_aux _ _ D.h.property.1 D.d.property.1 D.coprime
    p (f_in_h_aux A G m D b p hp)

private lemma not_mem_f_of_mem_d (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∈ support D.d.val) : p ∉ support b.f.val := fun hf =>
  disjoint_support_aux _ _ D.h.property.1 D.d.property.1 D.coprime p
    (f_in_h_aux A G m D b p hf) hp

private theorem order_coordinateRepresentative_of_mem_d (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : ExteriorPrime A) (hp : p.val ∈ support D.d.val) :
    order p.val (coordinateRepresentative A G U m D b v) = -2 := by
  have hf : p.val ∉ support b.f.val := not_mem_f_of_mem_d A G m D b p.val hp
  have ha : p.val ∉ support v.a.val := supported_a_aux A G m D b v p.val hf
  have hc : p.val ∉ support v.c.val :=
    (coprime_parts_aux A G m D b v p.val (Or.inl hp)).1
  have hn : p.val ∉ support v.n.val :=
    (coprime_parts_aux A G m D b v p.val (Or.inl hp)).2
  simp only [coordinateRepresentative, ord_div, ord_mul, ord_zpow, ord_pow,
    unit_ord_aux, generator_order, exponent_zero_aux _ _ ha, exponent_zero_aux _ _ hc,
    exponent_zero_aux _ _ hn, exponent_one_aux _ D.d.property.1 D.squarefree p.val hp,
    exponent_zero_aux _ _ hf]
  ring

private theorem order_coordinateRepresentative_of_mem_f (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : ExteriorPrime A) (hp : p.val ∈ support b.f.val) :
    order p.val (coordinateRepresentative A G U m D b v) + 2 =
      idealPrimeExponent p.val.asIdeal v.a.val := by
  have hd : p.val ∉ support D.d.val := not_mem_d_of_mem_f A G m D b p.val hp
  have hc : p.val ∉ support v.c.val :=
    (coprime_parts_aux A G m D b v p.val (Or.inr hp)).1
  have hn : p.val ∉ support v.n.val :=
    (coprime_parts_aux A G m D b v p.val (Or.inr hp)).2
  simp only [coordinateRepresentative, ord_div, ord_mul, ord_zpow, ord_pow,
    unit_ord_aux, generator_order, exponent_zero_aux _ _ hd, exponent_zero_aux _ _ hc,
    exponent_zero_aux _ _ hn, exponent_one_aux _ b.f.property.1 b.squarefree p.val hp]
  ring

private theorem order_coordinateRepresentative_of_not_mem (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : ExteriorPrime A) (hd : p.val ∉ support D.d.val) (hf : p.val ∉ support b.f.val) :
    order p.val (coordinateRepresentative A G U m D b v) =
      idealPrimeExponent p.val.asIdeal v.c.val +
        3 * idealPrimeExponent p.val.asIdeal v.n.val := by
  have ha : p.val ∉ support v.a.val := supported_a_aux A G m D b v p.val hf
  simp only [coordinateRepresentative, ord_div, ord_mul, ord_zpow, ord_pow,
    unit_ord_aux, generator_order, exponent_zero_aux _ _ ha, exponent_zero_aux _ _ hd,
    exponent_zero_aux _ _ hf]
  ring

private theorem localUnit_coordinateRepresentative_of_mem_d (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : ExteriorPrime A) (hp : p.val ∈ support D.d.val) :
    localUnit A G p (coordinateRepresentative A G U m D b v) =
      dArgument A G U m D b v p := by
  rw [localUnit, order_coordinateRepresentative_of_mem_d A G U m D b v p hp]
  simp only [coordinateRepresentative, dArgument]
  simp only [zpow_sub, zpow_add, zpow_neg, zpow_ofNat, zpow_natCast,
    div_pow, mul_pow, div_eq_mul_inv, mul_inv_rev, inv_inv, inv_pow]
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    Units.val_zpow_eq_zpow_val, zpow_natCast, pow_one, ← Nat.cast_mul, ← pow_mul]
  field_simp
  <;> ring

private theorem localUnit_coordinateRepresentative_of_mem_f (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : ExteriorPrime A) (hp : p.val ∈ support b.f.val) :
    localUnit A G p (coordinateRepresentative A G U m D b v) =
      fArgument A G U m D b v p := by
  have ho := order_coordinateRepresentative_of_mem_f A G U m D b v p hp
  have ho' : order p.val (coordinateRepresentative A G U m D b v) =
      (idealPrimeExponent p.val.asIdeal v.a.val : ℤ) - 2 := by omega
  rw [localUnit, ho']
  simp only [coordinateRepresentative, fArgument]
  simp only [zpow_sub, zpow_add, zpow_neg, zpow_ofNat, zpow_natCast,
    div_pow, mul_pow, div_eq_mul_inv, mul_inv_rev, inv_inv, inv_pow]
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    Units.val_zpow_eq_zpow_val, zpow_natCast, pow_one, ← Nat.cast_mul, ← pow_mul]
  field_simp
  <;> ring

private theorem localUnit_coordinateRepresentative_of_mem_c (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : ExteriorPrime A) (hp : p.val ∈ support v.c.val) :
    localUnit A G p (coordinateRepresentative A G U m D b v) =
      cArgument A G U m D b v p * localUnit A G p (G.generator v.n) ^ 3 := by
  have hd : p.val ∉ support D.d.val := fun h =>
    (coprime_parts_aux A G m D b v p.val (Or.inl h)).1 hp
  have hf : p.val ∉ support b.f.val := fun h =>
    (coprime_parts_aux A G m D b v p.val (Or.inr h)).1 hp
  rw [localUnit, order_coordinateRepresentative_of_not_mem A G U m D b v p hd hf,
    exponent_one_aux _ v.c.property.1 v.c_squarefree p.val hp]
  simp only [coordinateRepresentative, cArgument, localUnit, generator_order, Nat.cast_one]
  simp only [zpow_sub, zpow_add, zpow_neg, zpow_ofNat, zpow_natCast,
    div_pow, mul_pow, div_eq_mul_inv, mul_inv_rev, inv_inv, inv_pow]
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    Units.val_zpow_eq_zpow_val, zpow_natCast, pow_one, ← Nat.cast_mul, ← pow_mul]
  field_simp
  ring_nf
  change (_ : F) ^ (idealPrimeExponent p.val.asIdeal v.n.val * 3) =
    (_ : F) ^ ((idealPrimeExponent p.val.asIdeal v.n.val : ℤ) * 3)
  have he : (idealPrimeExponent p.val.asIdeal v.n.val : ℤ) * 3 =
      ((idealPrimeExponent p.val.asIdeal v.n.val * 3 : ℕ) : ℤ) := by push_cast; rfl
  rw [he, zpow_natCast]

private lemma residue_character_order (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ExteriorPrime A) : orderOf (residueCharacter A σ p) = 6 := by
  apply DHCubic.orderOf_normalizedSextic_complex F A p.val p.property σ
  exact (DHCubic.existsUnique_normalizedSextic F A p.val p.property).exists.choose_spec

private lemma character_six {k : Type*} [Field k] (χ : MulChar k ℂ)
    (hχ : orderOf χ = 6) (u : k) (hu : u ≠ 0) : χ u ^ 6 = 1 := by
  have h := congrArg (fun c : MulChar k ℂ => c u) (pow_orderOf_eq_one χ)
  simpa [hχ, MulChar.pow_apply' χ (by norm_num : (6 : ℕ) ≠ 0),
    MulChar.one_apply (isUnit_iff_ne_zero.mpr hu)] using h

private lemma reduction_spec_aux (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ)
    (hx : order p x = 0) : IsUnitResidue p x (unitResidue p x) := by
  simpa only [unitResidue, dif_pos hx] using (existsUnique_unitResidue p x hx).exists.choose_spec

private lemma reduction_mul_aux (p : HeightOneSpectrum (𝓞 F)) (x y : Fˣ)
    (hx : order p x = 0) (hy : order p y = 0) :
    unitResidue p (x * y) = unitResidue p x * unitResidue p y := by
  have hxy : order p (x * y) = 0 := by rw [ord_mul, hx, hy, add_zero]
  apply (existsUnique_unitResidue p (x * y) hxy).unique (reduction_spec_aux p (x * y) hxy)
  obtain ⟨a, b, ha, hb, hx', hrx⟩ := reduction_spec_aux p x hx
  obtain ⟨c, d, hc, hd, hy', hry⟩ := reduction_spec_aux p y hy
  refine ⟨a * c, b * d, ?_, ?_, ?_, ?_⟩
  · exact fun h => (p.isPrime.mem_or_mem h).elim ha hc
  · exact fun h => (p.isPrime.mem_or_mem h).elim hb hd
  · simp only [Units.val_mul, hx', hy', map_mul, mul_div_mul_comm]
  · rw [hrx, hry, map_mul, map_mul, mul_div_mul_comm]

private lemma reduction_one_aux (p : HeightOneSpectrum (𝓞 F)) :
    unitResidue p (1 : Fˣ) = 1 := by
  have h1 : order p (1 : Fˣ) = 0 := by simp [order]
  apply (existsUnique_unitResidue p 1 h1).unique (reduction_spec_aux p 1 h1)
  refine ⟨1, 1, p.isPrime.one_notMem, p.isPrime.one_notMem, ?_, ?_⟩ <;> simp

private lemma reduction_pow_aux (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ)
    (hx : order p x = 0) (n : ℕ) : unitResidue p (x ^ n) = unitResidue p x ^ n := by
  have hp (n : ℕ) : order p (x ^ n) = 0 := by rw [ord_pow, hx, mul_zero]
  induction n with
  | zero => simp [reduction_one_aux]
  | succ n ih => rw [pow_succ, reduction_mul_aux p _ _ (hp n) hx, ih, pow_succ]

private theorem symbol_mul_cube_sq (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ExteriorPrime A) (x y : Fˣ) (hx : order p.val x = 0)
    (hy : order p.val y = 0) :
    symbol A σ p (x * y ^ 3) ^ 2 = symbol A σ p x ^ 2 := by
  have hy3 : order p.val (y ^ 3) = 0 := by rw [ord_pow, hy, mul_zero]
  simp only [symbol, reduction_mul_aux _ _ _ hx hy3, reduction_pow_aux _ _ hy,
    map_mul, map_pow, mul_pow, ← pow_mul]
  rw [show 3 * 2 = 6 by norm_num,
    character_six _ (residue_character_order A σ p) _ (unitResidue_ne_zero _ _ hy), mul_one]

private theorem symbol_localUnit_coordinateRepresentative_of_mem_c (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : ExteriorPrime A) (hp : p.val ∈ support v.c.val) :
    symbol A σ p (localUnit A G p (coordinateRepresentative A G U m D b v)) ^ 2 =
      symbol A σ p (cArgument A G U m D b v p) ^ 2 := by
  rw [localUnit_coordinateRepresentative_of_mem_c A G U m D b v p hp]
  exact symbol_mul_cube_sq A σ p _ _
    ((coefficient_arguments_units A G U m D b v).2.2 p hp) (localUnit_order A G p _)

private lemma residue_card_coprime (A : SArithmeticData F) (p : ExteriorPrime A) :
    Nat.Coprime (Fintype.card (DHCubic.Residue F p.val)) 6 := by
  have hm := A.exterior_norm_mod_twelve p.val p.property
  have hc : Fintype.card (DHCubic.Residue F p.val) = Ideal.absNorm p.val.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [← hc] at hm
  have hm6 : Fintype.card (DHCubic.Residue F p.val) % 6 = 1 := by omega
  rw [← ZMod.coprime_mod_iff_coprime, hm6]
  exact Nat.coprime_one_left 6

private theorem nonzeroDigits_eq_scalar_phase (A : SArithmeticData F) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (p : ExteriorPrime A) (hψ : (ψ p).IsPrimitive) (j : Fin 6) (e : ℕ)
    (t : DHCubic.Residue F p.val) (ht : t ≠ 0) :
    sexticReflectedNonzeroDigits (residueCharacter A σ p) (ψ p) j (e : ℤ) t =
      scalar A σ ψ p j e * residueCharacter A σ p t ^ phaseExponent j e := by
  have hχ := residue_character_order A σ p
  have hQ := residue_card_coprime A p
  have h6 := character_six _ hχ t ht
  by_cases he : e = 0
  · subst e
    simp only [Nat.cast_zero]
    rw [sexticReflectedNonzeroDigits_depth_zero _ _ hχ hψ hQ j t ht]
    have hs : scalar A σ ψ p j 0 =
        sexticReflectedDepthZeroScalar (residueCharacter A σ p) (ψ p) j := by
      simp only [scalar, Nat.cast_zero]
      rw [sexticReflectedNonzeroDigits_depth_zero _ _ hχ hψ hQ j 1 one_ne_zero]
      simp
    rw [hs]
    simp only [phaseExponent, ite_true]
    rw [← pow_eq_pow_mod _ h6]
  · have hepos : (0 : ℤ) < e := by exact_mod_cast Nat.pos_of_ne_zero he
    by_cases hj : j = 4
    · subst j
      rw [sexticReflectedNonzeroDigits_positive _ _ hχ hψ hQ _ hepos t ht]
      have hs : scalar A σ ψ p 4 e =
          sexticSphericalCoefficient (residueCharacter A σ p) (ψ p) e *
            ((Fintype.card (DHCubic.Residue F p.val) : ℂ) - 1) /
              sexticMaskGaussSum (residueCharacter A σ p) (ψ p) 4 := by
        simp only [scalar]
        rw [sexticReflectedNonzeroDigits_positive _ _ hχ hψ hQ _ hepos 1 one_ne_zero]
        simp
      rw [hs]
      have hc : (4 : ℤ) + 2 * (e : ℤ) = ((4 + 2 * e : ℕ) : ℤ) := by push_cast; rfl
      rw [hc, zpow_natCast]
      simp only [phaseExponent, if_neg he]
      rw [← pow_eq_pow_mod _ h6]
      ring
    · have hj' : j.val ≠ 4 := by intro h; apply hj; exact Fin.ext h
      rw [sexticReflectedNonzeroDigits_eq_zero _ _ hχ hψ hQ j _ t ht
        (Or.inr (Or.inr ⟨hepos, hj'⟩))]
      have hs : scalar A σ ψ p j e = 0 := by
        exact sexticReflectedNonzeroDigits_eq_zero _ _ hχ hψ hQ j _ 1 one_ne_zero
          (Or.inr (Or.inr ⟨hepos, hj'⟩))
      rw [hs, zero_mul]

private theorem branchLocalFactor_coordinateRepresentative_of_mem_f (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : ExteriorPrime A) (hp : p.val ∈ support b.f.val) (hψ : (ψ p).IsPrimitive) :
    branchLocalFactor A G σ ψ m D b p (coordinateRepresentative A G U m D b v) =
      scalar A σ ψ p (rowIndex A m p.val) (idealPrimeExponent p.val.asIdeal v.a.val) *
        symbol A σ p (fArgument A G U m D b v p) ^
          phaseExponent (rowIndex A m p.val) (idealPrimeExponent p.val.asIdeal v.a.val) := by
  simp only [branchLocalFactor, Finset.mem_union, hp, or_true, if_true]
  rw [order_coordinateRepresentative_of_mem_f A G U m D b v p hp,
    localUnit_coordinateRepresentative_of_mem_f A G U m D b v p hp]
  exact nonzeroDigits_eq_scalar_phase A σ ψ p hψ _ _ _
    (unitResidue_ne_zero _ _ ((coefficient_arguments_units A G U m D b v).2.1 p hp))

private lemma rowIndex_d_aux (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (p : ExteriorPrime A) (hp : p.val ∈ support D.d.val) : rowIndex A m p.val = 1 := by
  have hh := exponent_zero_aux _ _ (disjoint_support_aux _ _ D.d.property.1 D.h.property.1
    (by rw [sup_comm]; exact D.coprime) p.val hp)
  have hd := exponent_one_aux _ D.d.property.1 D.squarefree p.val hp
  have hr : order p.val (ThetaReflectionData.rowUnit A m) = 1 := by
    rw [D.row_eq, ord_mul, unit_ord_aux, generator_order, D.factorization]
    simp only [idealPrimeExponent,
      UniqueFactorizationMonoid.normalizedFactors_mul D.h.property.1 D.d.property.1,
      Multiset.count_add] at *
    rw [hh, hd]; norm_num
  apply Fin.ext
  simp [rowIndex, hr]

private theorem branchLocalFactor_coordinateRepresentative_of_mem_d (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : ExteriorPrime A) (hp : p.val ∈ support D.d.val) (hψ : (ψ p).IsPrimitive) :
    branchLocalFactor A G σ ψ m D b p (coordinateRepresentative A G U m D b v) =
      omegaScalar A σ ψ p * symbol A σ p (dArgument A G U m D b v p) := by
  simp only [branchLocalFactor, Finset.mem_union, hp, true_or, if_true]
  rw [order_coordinateRepresentative_of_mem_d A G U m D b v p hp,
    localUnit_coordinateRepresentative_of_mem_d A G U m D b v p hp,
    rowIndex_d_aux A G m D p hp]
  norm_num only
  have he := nonzeroDigits_eq_scalar_phase A σ ψ p hψ 1 0 _
    (unitResidue_ne_zero _ _ ((coefficient_arguments_units A G U m D b v).1 p hp))
  simpa [omegaScalar, phaseExponent, symbol] using he

private theorem symbol_localUnit_pow_three (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (p : ExteriorPrime A) (x : Fˣ) (k : ℕ) :
    symbol A σ p (localUnit A G p x) ^ (2 * (3 * (k : ℤ))) = 1 := by
  have h6 := character_six _ (residue_character_order A σ p) _
    (unitResidue_ne_zero _ _ (localUnit_order A G p x))
  have he : 2 * (3 * (k : ℤ)) = ((6 * k : ℕ) : ℤ) := by push_cast; ring
  rw [he, zpow_natCast, pow_mul, symbol, h6, one_pow]

private theorem sphericalFactor_coordinateRepresentative_of_not_mem_c (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : ExteriorPrime A) (hd : p.val ∉ support D.d.val) (hf : p.val ∉ support b.f.val)
    (hc : p.val ∉ support v.c.val) :
    sphericalFactor A G σ ψ p (coordinateRepresentative A G U m D b v) =
      (idealNorm p.val.asIdeal : ℂ) ^ (-(idealPrimeExponent p.val.asIdeal v.n.val : ℤ)) := by
  have ho := order_coordinateRepresentative_of_not_mem A G U m D b v p hd hf
  rw [exponent_zero_aux _ _ hc, Nat.cast_zero, zero_add] at ho
  have hcard : Fintype.card (DHCubic.Residue F p.val) = idealNorm p.val.asIdeal := by
    simp only [idealNorm, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hcardC : (Fintype.card (DHCubic.Residue F p.val) : ℂ) =
      (idealNorm p.val.asIdeal : ℂ) := by exact_mod_cast hcard
  rw [sphericalFactor, ho, symbol_localUnit_pow_three]
  simp only [sexticSphericalCoefficient, hcardC, mul_one]
  have hn : (0 : ℤ) ≤ idealPrimeExponent p.val.asIdeal v.n.val := by positivity
  rw [if_neg (by omega), show (3 * (idealPrimeExponent p.val.asIdeal v.n.val : ℤ)) % 3 = 0 by omega,
    if_pos rfl]
  congr 1
  rw [Int.mul_ediv_cancel_left _ (by norm_num : (3 : ℤ) ≠ 0)]

private theorem coordinateFrequency_supported (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D) (v : Coordinates A G m D b) :
    Supported A G m D b (coordinateFrequency A G U m D b v) := by
  refine ⟨coordinateRepresentative A G U m D b v, rfl, ?_, ?_, ?_⟩
  · intro p hp
    exact order_coordinateRepresentative_of_mem_d A G U m D b v
      ⟨p, support_outside A D.d p hp⟩ hp
  · intro p hp
    rw [order_coordinateRepresentative_of_mem_f A G U m D b v
      ⟨p, support_outside A b.f p hp⟩ hp]
    constructor
    · positivity
    · rcases v.a_exponents p hp with he | he
      · left; exact_mod_cast he
      · right; exact_mod_cast he
  · intro p hd hf
    rw [order_coordinateRepresentative_of_not_mem A G U m D b v p hd hf]
    have hc : idealPrimeExponent p.val.asIdeal v.c.val = 0 ∨
        idealPrimeExponent p.val.asIdeal v.c.val = 1 := by
      by_cases h : p.val ∈ support v.c.val
      · exact Or.inr (exponent_one_aux _ v.c.property.1 v.c_squarefree p.val h)
      · exact Or.inl (exponent_zero_aux _ _ h)
    constructor
    · positivity
    · rcases hc with hc | hc <;> rw [hc] <;> omega

private theorem symbol_localUnit_pow_three_add_one (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (p : ExteriorPrime A) (x : Fˣ) (k : ℕ) :
    symbol A σ p (localUnit A G p x) ^ (2 * (1 + 3 * (k : ℤ))) =
      symbol A σ p (localUnit A G p x) ^ 2 := by
  have h6 := character_six _ (residue_character_order A σ p) _
    (unitResidue_ne_zero _ _ (localUnit_order A G p x))
  have he : 2 * (1 + 3 * (k : ℤ)) = ((2 + 6 * k : ℕ) : ℤ) := by push_cast; ring
  rw [he, zpow_natCast, pow_add, pow_mul, symbol, h6, one_pow, mul_one]

private theorem sphericalFactor_coordinateRepresentative_of_mem_c (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : ExteriorPrime A) (hp : p.val ∈ support v.c.val) :
    sphericalFactor A G σ ψ p (coordinateRepresentative A G U m D b v) =
      (idealNorm p.val.asIdeal : ℂ) ^ (-(idealPrimeExponent p.val.asIdeal v.n.val : ℤ)) *
        (Real.sqrt (idealNorm p.val.asIdeal) : ℂ)⁻¹ * gaussTwo A σ ψ p *
          symbol A σ p (cArgument A G U m D b v p) ^ 2 := by
  have hd : p.val ∉ support D.d.val := fun h =>
    (coprime_parts_aux A G m D b v p.val (Or.inl h)).1 hp
  have hf : p.val ∉ support b.f.val := fun h =>
    (coprime_parts_aux A G m D b v p.val (Or.inr h)).1 hp
  have ho := order_coordinateRepresentative_of_not_mem A G U m D b v p hd hf
  rw [exponent_one_aux _ v.c.property.1 v.c_squarefree p.val hp, Nat.cast_one] at ho
  rw [sphericalFactor, ho, symbol_localUnit_pow_three_add_one,
    symbol_localUnit_coordinateRepresentative_of_mem_c A G U σ m D b v p hp]
  have hn : (0 : ℤ) ≤ idealPrimeExponent p.val.asIdeal v.n.val := by positivity
  have he : (1 + 3 * (idealPrimeExponent p.val.asIdeal v.n.val : ℤ)) / 3 =
      idealPrimeExponent p.val.asIdeal v.n.val := by omega
  simp only [sexticSphericalCoefficient, gaussTwo]
  rw [if_neg (by omega),
    show (1 + 3 * (idealPrimeExponent p.val.asIdeal v.n.val : ℤ)) % 3 = 1 by omega,
    if_neg (by norm_num : (1 : ℤ) ≠ 0), if_pos rfl, he]
  have hcard : (Fintype.card (DHCubic.Residue F p.val) : ℝ) = idealNorm p.val.asIdeal := by
    simp only [idealNorm, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hcardC : (Fintype.card (DHCubic.Residue F p.val) : ℂ) =
      (idealNorm p.val.asIdeal : ℂ) := by exact_mod_cast hcard
  rw [hcard, hcardC]

private theorem branchLocalFactor_coordinateRepresentative_of_not_mem (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : ExteriorPrime A) (hd : p.val ∉ support D.d.val) (hf : p.val ∉ support b.f.val) :
    branchLocalFactor A G σ ψ m D b p (coordinateRepresentative A G U m D b v) =
      (if p.val ∈ support D.h.val then (1 - (idealNorm p.val.asIdeal : ℂ)⁻¹) else 1) *
        sphericalFactor A G σ ψ p (coordinateRepresentative A G U m D b v) := by
  simp only [branchLocalFactor, Finset.mem_union, hd, hf, or_self, if_false]
  split_ifs <;> simp

private theorem branchLocalFactor_coordinateRepresentative_exact (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : ExteriorPrime A) (hψ : (ψ p).IsPrimitive) :
    branchLocalFactor A G σ ψ m D b p (coordinateRepresentative A G U m D b v) =
      if p.val ∈ support D.d.val then
        omegaScalar A σ ψ p * symbol A σ p (dArgument A G U m D b v p)
      else if p.val ∈ support b.f.val then
        scalar A σ ψ p (rowIndex A m p.val) (idealPrimeExponent p.val.asIdeal v.a.val) *
          symbol A σ p (fArgument A G U m D b v p) ^
            phaseExponent (rowIndex A m p.val) (idealPrimeExponent p.val.asIdeal v.a.val)
      else
        (if p.val ∈ support D.h.val then 1 - (idealNorm p.val.asIdeal : ℂ)⁻¹ else 1) *
          (idealNorm p.val.asIdeal : ℂ) ^ (-(idealPrimeExponent p.val.asIdeal v.n.val : ℤ)) *
            (if p.val ∈ support v.c.val then
              (Real.sqrt (idealNorm p.val.asIdeal) : ℂ)⁻¹ * gaussTwo A σ ψ p *
                symbol A σ p (cArgument A G U m D b v p) ^ 2 else 1) := by
  by_cases hd : p.val ∈ support D.d.val
  · rw [if_pos hd]
    exact branchLocalFactor_coordinateRepresentative_of_mem_d A G U σ ψ m D b v p hd hψ
  · rw [if_neg hd]
    by_cases hf : p.val ∈ support b.f.val
    · rw [if_pos hf]
      exact branchLocalFactor_coordinateRepresentative_of_mem_f A G U σ ψ m D b v p hf hψ
    · rw [if_neg hf, branchLocalFactor_coordinateRepresentative_of_not_mem A G U σ ψ m D b v p hd hf]
      by_cases hc : p.val ∈ support v.c.val
      · rw [if_pos hc, sphericalFactor_coordinateRepresentative_of_mem_c A G U σ ψ m D b v p hc]
        ring
      · rw [if_neg hc, sphericalFactor_coordinateRepresentative_of_not_mem_c A G U σ ψ m D b v p hd hf hc,
          mul_one]

private theorem branchCoefficient_coordinateRepresentative_eq_prod (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b) (s : Finset (ExteriorPrime A))
    (hs : ∀ p : ExteriorPrime A,
      p.val ∈ support D.d.val ∪ support b.f.val ∪ support D.h.val ∪
        support v.c.val ∪ support v.n.val → p ∈ s) :
    branchCoefficient A G σ ψ m D b (coordinateRepresentative A G U m D b v) =
      ∏ p ∈ s, branchLocalFactor A G σ ψ m D b p (coordinateRepresentative A G U m D b v) := by
  apply finprod_eq_prod_of_mulSupport_subset
  intro p hp
  by_contra hnots
  have h : p.val ∉ support D.d.val ∪ support b.f.val ∪ support D.h.val ∪
      support v.c.val ∪ support v.n.val := fun h => hnots (hs p h)
  simp only [Finset.mem_union, not_or] at h
  have hsph := sphericalFactor_coordinateRepresentative_of_not_mem_c A G U σ ψ m D b v p
    h.1.1.1.1 h.1.1.1.2 h.1.2
  rw [exponent_zero_aux _ _ h.2, Nat.cast_zero, neg_zero, zpow_zero] at hsph
  apply hp
  change branchLocalFactor A G σ ψ m D b p (coordinateRepresentative A G U m D b v) = 1
  rw [branchLocalFactor_coordinateRepresentative_of_not_mem A G U σ ψ m D b v p h.1.1.1.1 h.1.1.1.2,
    if_neg h.1.1.2, hsph, mul_one]

lemma ideal_factorization (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    I = ∏ p ∈ idealPrimeSupport I, p ^ idealPrimeExponent p I := by
  unfold idealPrimeSupport idealPrimeExponent
  rw [← Finset.prod_multiset_count]
  exact associated_iff_eq.mp (UniqueFactorizationMonoid.prod_normalizedFactors hI).symm

lemma support_prod (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    {M : Type*} [CommMonoid M] (f : Ideal (𝓞 F) → M) :
    (∏ p ∈ support I, f p.asIdeal) = ∏ p ∈ idealPrimeSupport I, f p := by
  apply Finset.prod_bij (fun p _ => p.asIdeal)
  · intro p hp; simpa only [support, Finset.mem_preimage] using hp
  · intro p hp q hq he; exact HeightOneSpectrum.asIdeal_injective he
  · intro p hp
    have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor p
      (Multiset.mem_toFinset.mp hp)
    refine ⟨⟨p, Ideal.isPrime_of_prime hprime, hprime.ne_zero⟩, ?_, rfl⟩
    simpa only [support, Finset.mem_preimage] using hp
  · intro p hp; rfl

private lemma norm_prod (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    (idealNorm I : ℂ) = ∏ p ∈ support I, (idealNorm p.asIdeal : ℂ) ^ idealPrimeExponent p.asIdeal I := by
  rw [support_prod I hI (fun p => (idealNorm p : ℂ) ^ idealPrimeExponent p I)]
  conv_lhs => rw [ideal_factorization I hI]
  simp only [idealNorm, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow, Complex.ofReal_prod,
    Complex.ofReal_pow, Complex.ofReal_natCast]

private lemma sqrt_norm_prod (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hs : Squarefree I) :
    (Real.sqrt (idealNorm I) : ℂ) = ∏ p ∈ support I, (Real.sqrt (idealNorm p.asIdeal) : ℂ) := by
  have hn : idealNorm I = ∏ p ∈ support I, idealNorm p.asIdeal := by
    apply Complex.ofReal_injective
    rw [norm_prod I hI, Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro p hp
    have he : idealPrimeExponent p.asIdeal I = 1 := by
      apply Multiset.count_eq_one_of_mem
        (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI |>.mp hs)
      simpa only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using hp
    simp [he]
  rw [hn, Real.sqrt_prod (support I) (fun p hp => (idealNorm_ge_one p.asIdeal p.ne_bot).trans' (by norm_num)),
    Complex.ofReal_prod]

def extSupport (A : SArithmeticData F) (I : A.Exterior) : Finset (ExteriorPrime A) :=
  (support I.val).attach.map ⟨supportPrime A I, by
    intro p q h; exact Subtype.ext (congrArg (fun z : ExteriorPrime A => z.val) h)⟩

lemma mem_extSupport (A : SArithmeticData F) (I : A.Exterior) (p : ExteriorPrime A) :
    p ∈ extSupport A I ↔ p.val ∈ support I.val := by
  simp only [extSupport, Finset.mem_map, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨q, rfl⟩; exact q.property
  · intro h; exact ⟨⟨p.val, h⟩, Subtype.ext rfl⟩

private lemma ext_prod (A : SArithmeticData F) (I : A.Exterior)
    {M : Type*} [CommMonoid M] (f : ExteriorPrime A → M) :
    (∏ p ∈ extSupport A I, f p) = ∏ p : {p // p ∈ support I.val}, f (supportPrime A I p) := by
  simp only [extSupport, Finset.prod_map, ← Finset.prod_attach (support I.val)]
  rfl

lemma ext_prod_val (A : SArithmeticData F) (I : A.Exterior)
    {M : Type*} [CommMonoid M] (f : HeightOneSpectrum (𝓞 F) → M) :
    (∏ p ∈ extSupport A I, f p.val) = ∏ p ∈ support I.val, f p := by
  rw [ext_prod]
  exact (Finset.prod_attach _ _)

private lemma extend_prod {α M : Type*} [DecidableEq α] [CommMonoid M]
    (s t : Finset α) (h : t ⊆ s) (f : α → M) :
    (∏ p ∈ s, if p ∈ t then f p else 1) = ∏ p ∈ t, f p := by
  rw [← Finset.prod_filter]
  congr 1
  exact Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr h)

private lemma mem_support_le (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (p : HeightOneSpectrum (𝓞 F)) : p ∈ support I ↔ I ≤ p.asIdeal := by
  simp only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset]
  exact Ideal.mem_normalizedFactors_iff hI |>.trans (and_iff_right p.isPrime)

private lemma df_disjoint (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m) (b : Branch A G m D)
    (p : ExteriorPrime A) (hd : p.val ∈ support D.d.val) :
    p.val ∉ support D.h.val ∧ p.val ∉ support b.f.val := by
  have hh : p.val ∉ support D.h.val := by
    intro hp
    apply p.val.isPrime.ne_top
    apply top_le_iff.mp
    rw [← D.coprime]
    exact sup_le ((mem_support_le _ D.h.property.1 _).mp hp)
      ((mem_support_le _ D.d.property.1 _).mp hd)
  refine ⟨hh, ?_⟩
  intro hf
  have hrad : idealRadical D.h.val ≤ p.val.asIdeal :=
    (Ideal.dvd_iff_le.mp b.divides_radical).trans
      ((mem_support_le _ b.f.property.1 _).mp hf)
  apply hh
  apply (mem_support_le _ D.h.property.1 _).mpr
  have hdvd : idealRadical D.h.val ∣ D.h.val := by
    have hd := Multiset.toFinset_prod_dvd_prod (UniqueFactorizationMonoid.normalizedFactors D.h.val)
    have he := associated_iff_eq.mp (UniqueFactorizationMonoid.prod_normalizedFactors D.h.property.1)
    rw [he] at hd
    simpa only [idealRadical, idealPrimeSupport, id_eq] using hd
  exact (Ideal.dvd_iff_le.mp hdvd).trans hrad

private lemma cn_disjoint (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m) (b : Branch A G m D)
    (v : Coordinates A G m D b) (p : ExteriorPrime A)
    (hdf : p.val ∈ support D.d.val ∨ p.val ∈ support b.f.val) :
    p.val ∉ support v.c.val ∧ p.val ∉ support v.n.val := by
  have hdfle : D.d.val * b.f.val ≤ p.val.asIdeal := by
    rcases hdf with hd | hf
    · exact Ideal.mul_le_left.trans ((mem_support_le _ D.d.property.1 _).mp hd)
    · exact Ideal.mul_le_right.trans ((mem_support_le _ b.f.property.1 _).mp hf)
  constructor <;> intro hp
  · apply p.val.isPrime.ne_top
    apply top_le_iff.mp
    rw [← v.coprime]
    exact sup_le (Ideal.mul_le_left.trans ((mem_support_le _ v.c.property.1 _).mp hp)) hdfle
  · apply p.val.isPrime.ne_top
    apply top_le_iff.mp
    rw [← v.coprime]
    exact sup_le (Ideal.mul_le_right.trans ((mem_support_le _ v.n.property.1 _).mp hp)) hdfle

lemma exp_zero (I : Ideal (𝓞 F)) (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∉ support I) : idealPrimeExponent p.asIdeal I = 0 := by
  apply Multiset.count_eq_zero.mpr
  simpa only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using hp

private theorem branchLocalFactor_coordinateRepresentative_product (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : ExteriorPrime A) (hψ : (ψ p).IsPrimitive) :
    branchLocalFactor A G σ ψ m D b p (coordinateRepresentative A G U m D b v) =
      (if p ∈ extSupport A D.h \ extSupport A b.f then 1 - (idealNorm p.val.asIdeal : ℂ)⁻¹ else 1) *
      (idealNorm p.val.asIdeal : ℂ) ^ (-(idealPrimeExponent p.val.asIdeal v.n.val : ℤ)) *
      (if p ∈ extSupport A v.c then (Real.sqrt (idealNorm p.val.asIdeal) : ℂ)⁻¹ else 1) *
      (if p ∈ extSupport A D.d then omegaScalar A σ ψ p * symbol A σ p (dArgument A G U m D b v p) else 1) *
      (if p ∈ extSupport A b.f then scalar A σ ψ p (rowIndex A m p.val) (idealPrimeExponent p.val.asIdeal v.a.val) *
        symbol A σ p (fArgument A G U m D b v p) ^ phaseExponent (rowIndex A m p.val) (idealPrimeExponent p.val.asIdeal v.a.val) else 1) *
      (if p ∈ extSupport A v.c then gaussTwo A σ ψ p * symbol A σ p (cArgument A G U m D b v p) ^ 2 else 1) := by
  rw [branchLocalFactor_coordinateRepresentative_exact A G U σ ψ m D b v p hψ]
  simp only [Finset.mem_sdiff, mem_extSupport]
  by_cases hd : p.val ∈ support D.d.val
  · obtain ⟨hh, hf⟩ := df_disjoint A G m D b p hd
    obtain ⟨hc, hn⟩ := cn_disjoint A G m D b v p (Or.inl hd)
    simp [hd, hh, hf, hc, exp_zero _ _ hn]
  · by_cases hf : p.val ∈ support b.f.val
    · obtain ⟨hc, hn⟩ := cn_disjoint A G m D b v p (Or.inr hf)
      simp [hd, hf, hc, exp_zero _ _ hn]
    · simp only [hd, hf, if_false, not_false_eq_true, and_true, mul_one]
      split_ifs <;> ring

private lemma ext_sdiff_prod (A : SArithmeticData F) (I J : A.Exterior)
    {M : Type*} [CommMonoid M] (f : HeightOneSpectrum (𝓞 F) → M) :
    (∏ p ∈ extSupport A I \ extSupport A J, f p.val) =
      ∏ p ∈ support I.val \ support J.val, f p := by
  apply Finset.prod_bij (fun p _ => p.val)
  · intro p hp; simpa only [Finset.mem_sdiff, mem_extSupport] using hp
  · intro p hp q hq he; exact Subtype.ext he
  · intro p hp
    refine ⟨⟨p, support_outside A I p (Finset.mem_sdiff.mp hp).1⟩, ?_, rfl⟩
    simpa only [Finset.mem_sdiff, mem_extSupport] using hp
  · intro p hp; rfl

private theorem branch_coefficient_exact_from_local (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b) :
    branchCoefficient A G σ ψ m D b (coordinateRepresentative A G U m D b v) =
      exactCoefficient A G U σ ψ m D b v := by
  let s := extSupport A D.d ∪ extSupport A b.f ∪ extSupport A D.h ∪ extSupport A v.c ∪ extSupport A v.n
  have hs (I : A.Exterior) (hI : I = D.d ∨ I = b.f ∨ I = D.h ∨ I = v.c ∨ I = v.n) :
      extSupport A I ⊆ s := by
    rcases hI with rfl | rfl | rfl | rfl | rfl <;> intro p hp <;> simp only [s, Finset.mem_union] <;> tauto
  rw [branchCoefficient_coordinateRepresentative_eq_prod A G U σ ψ m D b v s (by
    intro p hp; simpa only [s, Finset.mem_union, mem_extSupport] using hp)]
  simp_rw [branchLocalFactor_coordinateRepresentative_product A G U σ ψ m D b v _ (hψ _)]
  simp only [Finset.prod_mul_distrib]
  have hn : (∏ p ∈ s, (idealNorm p.val.asIdeal : ℂ) ^ (-(idealPrimeExponent p.val.asIdeal v.n.val : ℤ))) =
      (A.exteriorNorm v.n : ℂ)⁻¹ := by
    have he : (∏ p ∈ s, (idealNorm p.val.asIdeal : ℂ) ^ idealPrimeExponent p.val.asIdeal v.n.val) =
        (A.exteriorNorm v.n : ℂ) := by
      change (∏ p ∈ s, (idealNorm p.val.asIdeal : ℂ) ^ idealPrimeExponent p.val.asIdeal v.n.val) = (idealNorm v.n.val : ℂ)
      rw [norm_prod v.n.val v.n.property.1, ← ext_prod_val A v.n (fun p => (idealNorm p.asIdeal : ℂ) ^ idealPrimeExponent p.asIdeal v.n.val)]
      symm
      apply Finset.prod_subset (hs v.n (by tauto))
      intro p hp hn
      simp [exp_zero _ _ (fun h => hn ((mem_extSupport A v.n p).mpr h))]
    simp_rw [zpow_neg, zpow_natCast]
    rw [Finset.prod_inv_distrib, he]
  have hc : (∏ p ∈ s, if p ∈ extSupport A v.c then (Real.sqrt (idealNorm p.val.asIdeal) : ℂ)⁻¹ else 1) =
      (Real.sqrt (A.exteriorNorm v.c) : ℂ)⁻¹ := by
    rw [extend_prod s _ (hs v.c (by tauto)), Finset.prod_inv_distrib, ext_prod_val A v.c (fun p => (Real.sqrt (idealNorm p.asIdeal) : ℂ)),
      ← sqrt_norm_prod v.c.val v.c.property.1 v.c_squarefree]
  rw [hn, hc,
    extend_prod s _ (Finset.sdiff_subset.trans (hs D.h (by tauto))),
    extend_prod s _ (hs D.d (by tauto)), extend_prod s _ (hs b.f (by tauto)),
    extend_prod s _ (hs v.c (by tauto)), ext_sdiff_prod A D.h b.f (fun p => 1 - (idealNorm p.asIdeal : ℂ)⁻¹), ext_prod, ext_prod, ext_prod]
  unfold exactCoefficient
  simp only [div_eq_mul_inv, mul_inv_rev, supportPrime]
  ring

end CanonicalCoefficientProof

theorem branch_coefficient_exact (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b) :
    branchCoefficient A G σ ψ m D b (coordinateRepresentative A G U m D b v) =
      exactCoefficient A G U σ ψ m D b v := by
  exact CanonicalCoefficientProof.branch_coefficient_exact_from_local A G U σ ψ hψ m D b v

theorem branches_finite (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m) :
    Finite (Branch A G m D) := by
  letI := UniqueFactorizationMonoid.fintypeSubtypeDvd (idealRadical D.h.val)
    (idealRadical_squarefree_nonzero D.h.val D.h.property.1).2
  apply Finite.of_injective
    (fun b : Branch A G m D => (⟨b.f.val, b.divides_radical⟩ :
      {I : Ideal (𝓞 F) // I ∣ idealRadical D.h.val}))
  intro b₁ b₂ h
  have hv : b₁.f.val = b₂.f.val := congrArg
    (fun z : {I : Ideal (𝓞 F) // I ∣ idealRadical D.h.val} => z.val) h
  have hf : b₁.f = b₂.f := Subtype.ext hv
  cases b₁
  cases b₂
  cases hf
  rfl

def exteriorLocalFactor (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (p : ExteriorPrime A) (x : Fˣ) : ℂ :=
  if p.val ∈ support D.rowIdeal.val then
    sexticReflectedDigitModel (residueCharacter A σ p) (ψ p)
      (rowIndex A m p.val) (order p.val x + 2)
      (unitResidue p.val (localUnit A G p x))
  else sphericalFactor A G σ ψ p x

def exteriorCoefficient (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m) (x : Fˣ) : ℂ :=
  ∏ᶠ p : ExteriorPrime A, exteriorLocalFactor A G σ ψ m D p x

theorem order_finite_support (x : Fˣ) :
    {p : HeightOneSpectrum (𝓞 F) | order p x ≠ 0}.Finite := by
  apply ((HeightOneSpectrum.Support.finite (𝓞 F) (x : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((x : F)⁻¹))).subset
  intro p hp
  have hn : p.valuation F (x : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
  have hv : p.valuation F (x : F) ≠ 1 := by
    intro h
    exact hp (by simp [order, h])
  rcases lt_or_gt_of_ne hv with h | h
  · right
    change 1 < p.valuation F ((x : F)⁻¹)
    rw [map_inv₀]
    exact (one_lt_inv₀ (pos_iff_ne_zero.mpr hn)).mpr h
  · exact Or.inl h

theorem branchLocalFactor_finite_support (A : SArithmeticData F)
    (G : AllowedRecipe A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (x : Fˣ) :
    {p : ExteriorPrime A | branchLocalFactor A G σ ψ m D b p x ≠ 1}.Finite := by
  have hs := ((support D.h.val ∪ support D.d.val ∪ support b.f.val).finite_toSet.union
    (order_finite_support x)).preimage
      (f := fun p : ExteriorPrime A => p.val) Subtype.val_injective.injOn
  apply hs.subset
  intro p hp
  by_contra h
  have hp' : p.val ∉ support D.h.val ∧ p.val ∉ support D.d.val ∧
      p.val ∉ support b.f.val ∧ order p.val x = 0 := by
    simpa only [Set.mem_preimage, Set.mem_union, Finset.mem_coe, Finset.mem_union,
      Set.mem_setOf_eq, not_or, not_not, and_assoc] using h
  apply hp
  simp [branchLocalFactor, hp'.1, hp'.2.1, hp'.2.2.1, sphericalFactor,
    hp'.2.2.2, sexticSphericalCoefficient]

lemma char_pow_six {k : Type*} [Field k] (χ : MulChar k ℂ)
    (hχ : orderOf χ = 6) (u : k) (hu : u ≠ 0) : χ u ^ 6 = 1 := by
  have h := congrArg (fun c : MulChar k ℂ => c u) (pow_orderOf_eq_one χ)
  simpa [hχ, MulChar.pow_apply' χ (by norm_num : (6 : ℕ) ≠ 0),
    MulChar.one_apply (isUnit_iff_ne_zero.mpr hu)] using h
private lemma digits_sixth {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (hχ : orderOf χ = 6)
    (j : Fin 6) (e : ℤ) (t u : k) (hu : u ≠ 0) :
    sexticReflectedNonzeroDigits χ ψ j e (u ^ 6 * t) =
      sexticReflectedNonzeroDigits χ ψ j e t := by
  have hu6 : u ^ 6 ≠ 0 := pow_ne_zero _ hu
  have hc : χ (u ^ 6) = 1 := by rw [map_pow, char_pow_six χ hχ u hu]
  have hi : χ⁻¹ (u ^ 6) = 1 := by rw [MulChar.inv_apply_eq_inv', hc, inv_one]
  have hh : (χ u ^ j.val) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm j.val 6, pow_mul, char_pow_six χ hχ u hu, one_pow]
  have hm (v : k) : sexticFourierMask χ ψ j (u ^ 6 * v) = sexticFourierMask χ ψ j v := by
    have hz : u ^ 6 * v = 0 ↔ v = 0 := mul_eq_zero.trans (by simp [hu6])
    simp only [sexticFourierMask, hz]
    split_ifs <;> simp_all [map_mul, MulChar.pow_apply', MulChar.inv_apply_eq_inv', map_pow]
  simp only [sexticReflectedNonzeroDigits, map_mul, hc, one_mul]
  congr 1
  symm
  apply Finset.sum_bij (fun v _ => u ^ 6 * v)
  · intro v hv
    simpa [Finset.mem_erase, hu6] using hv
  · intro v hv w hw h
    exact mul_left_cancel₀ hu6 h
  · intro w hw
    refine ⟨w / u ^ 6, ?_, ?_⟩
    · simpa [Finset.mem_erase, hu6] using hw
    · exact mul_div_cancel₀ _ hu6
  · intro v hv
    have hv0 : v ≠ 0 := (Finset.mem_erase.mp hv).1
    simp only [hm, map_mul, hc, one_mul]
    congr 1
    split_ifs
    · congr 1
      field_simp
    · rfl
lemma ord_mul (p : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    order p (x * y) = order p x + order p y := by
  simp only [order, Units.val_mul, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
    ((Valuation.ne_zero_iff _).mpr y.ne_zero), neg_add]
lemma ord_zpow (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ) (n : ℤ) :
    order p (x ^ n) = n * order p x := by
  simp only [order, Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow,
    smul_eq_mul]
  ring
lemma reduction_spec (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ)
    (hx : order p x = 0) : IsUnitResidue p x (unitResidue p x) := by
  simpa only [unitResidue, dif_pos hx] using (existsUnique_unitResidue p x hx).exists.choose_spec
lemma reduction_mul (p : HeightOneSpectrum (𝓞 F)) (x y : Fˣ)
    (hx : order p x = 0) (hy : order p y = 0) :
    unitResidue p (x * y) = unitResidue p x * unitResidue p y := by
  have hxy : order p (x * y) = 0 := by rw [ord_mul, hx, hy, add_zero]
  apply (existsUnique_unitResidue p (x * y) hxy).unique (reduction_spec p (x * y) hxy)
  obtain ⟨a, b, ha, hb, hx', hrx⟩ := reduction_spec p x hx
  obtain ⟨c, d, hc, hd, hy', hry⟩ := reduction_spec p y hy
  refine ⟨a * c, b * d, ?_, ?_, ?_, ?_⟩
  · exact fun h => (p.isPrime.mem_or_mem h).elim ha hc
  · exact fun h => (p.isPrime.mem_or_mem h).elim hb hd
  · simp only [Units.val_mul, hx', hy', map_mul, mul_div_mul_comm]
  · rw [hrx, hry, map_mul, map_mul, mul_div_mul_comm]
private lemma reduction_mul_unit (p : HeightOneSpectrum (𝓞 F)) (x y : Fˣ)
    (hx : order p x = 0) : unitResidue p (x * y) = unitResidue p x * unitResidue p y := by
  by_cases hy : order p y = 0
  · exact reduction_mul p x y hx hy
  · have hxy : order p (x * y) ≠ 0 := by simpa only [ord_mul, hx, zero_add] using hy
    simp only [unitResidue, dif_neg hxy, dif_neg hy, mul_zero]
lemma reduction_one (p : HeightOneSpectrum (𝓞 F)) : unitResidue p (1 : Fˣ) = 1 := by
  have h1 : order p (1 : Fˣ) = 0 := by simp [order]
  apply (existsUnique_unitResidue p 1 h1).unique (reduction_spec p 1 h1)
  refine ⟨1, 1, p.isPrime.one_notMem, p.isPrime.one_notMem, ?_, ?_⟩ <;> simp
lemma reduction_pow (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ)
    (hx : order p x = 0) (n : ℕ) : unitResidue p (x ^ n) = unitResidue p x ^ n := by
  have hp (n : ℕ) : order p (x ^ n) = 0 := by
    rw [← zpow_natCast, ord_zpow, hx, mul_zero]
  induction n with
  | zero => simp [reduction_one]
  | succ n ih => rw [pow_succ, reduction_mul p _ _ (hp n) hx, ih, pow_succ]
lemma char_order (A : SArithmeticData F) (σ : F →+* ℂ) (p : ExteriorPrime A) :
    orderOf (residueCharacter A σ p) = 6 := by
  apply DHCubic.orderOf_normalizedSextic_complex F A p.val p.property σ
  exact (DHCubic.existsUnique_normalizedSextic F A p.val p.property).exists.choose_spec
lemma unit_ord (A : SArithmeticData F) (p : ExteriorPrime A) (u : A.U) :
    order p.val u.val = 0 := by
  have hv : p.val.valuation F (u.val : F) = 1 := u.property p.val p.property
  simp [order, hv]
private lemma local_factor_sixth (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (p : ExteriorPrime A) (x : Fˣ) (u : A.U) :
    branchLocalFactor A G σ ψ m D b p (x * u.val ^ 6) =
      branchLocalFactor A G σ ψ m D b p x := by
  have ho : order p.val (x * u.val ^ 6) = order p.val x := by
    rw [ord_mul, ← zpow_natCast, ord_zpow, unit_ord, mul_zero, add_zero]
  have hl : localUnit A G p (x * u.val ^ 6) = u.val ^ 6 * localUnit A G p x := by
    simp only [localUnit, ho, div_eq_mul_inv]; ac_rfl
  have hr : unitResidue p.val (localUnit A G p (x * u.val ^ 6)) =
      unitResidue p.val u.val ^ 6 * unitResidue p.val (localUnit A G p x) := by
    rw [hl, reduction_mul_unit]
    · rw [reduction_pow p.val u.val (unit_ord A p u)]
    · rw [← zpow_natCast, ord_zpow, unit_ord, mul_zero]
  have hc : symbol A σ p (localUnit A G p (x * u.val ^ 6)) =
      symbol A σ p (localUnit A G p x) := by
    simp only [symbol, hr, map_mul, map_pow]
    rw [char_pow_six _ (char_order A σ p) _ (unitResidue_ne_zero _ _ (unit_ord A p u)), one_mul]
  simp only [branchLocalFactor, ho, hr]
  split_ifs
  · exact digits_sixth _ _ (char_order A σ p) _ _ _ _
      (unitResidue_ne_zero _ _ (unit_ord A p u))
  · simp only [sphericalFactor, ho, hc]
  · simp only [sphericalFactor, ho, hc]

private lemma exterior_local_factor_sixth (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (p : ExteriorPrime A) (x : Fˣ) (u : A.U) :
    exteriorLocalFactor A G σ ψ m D p (x * u.val ^ 6) =
      exteriorLocalFactor A G σ ψ m D p x := by
  have ho : order p.val (x * u.val ^ 6) = order p.val x := by
    rw [ord_mul, ← zpow_natCast, ord_zpow, unit_ord, mul_zero, add_zero]
  have hl : localUnit A G p (x * u.val ^ 6) = u.val ^ 6 * localUnit A G p x := by
    simp only [localUnit, ho, div_eq_mul_inv]; ac_rfl
  have hr : unitResidue p.val (localUnit A G p (x * u.val ^ 6)) =
      unitResidue p.val u.val ^ 6 * unitResidue p.val (localUnit A G p x) := by
    rw [hl, reduction_mul_unit]
    · rw [reduction_pow p.val u.val (unit_ord A p u)]
    · rw [← zpow_natCast, ord_zpow, unit_ord, mul_zero]
  have hc : symbol A σ p (localUnit A G p (x * u.val ^ 6)) =
      symbol A σ p (localUnit A G p x) := by
    simp only [symbol, hr, map_mul, map_pow]
    rw [char_pow_six _ (char_order A σ p) _ (unitResidue_ne_zero _ _ (unit_ord A p u)), one_mul]
  simp only [exteriorLocalFactor, ho, hr]
  split_ifs
  · simp only [sexticReflectedDigitModel]
    rw [digits_sixth _ _ (char_order A σ p) _ _ _ _
      (unitResidue_ne_zero _ _ (unit_ord A p u))]
    simp only [map_mul, map_pow]
    rw [char_pow_six _ (char_order A σ p) _
      (unitResidue_ne_zero _ _ (unit_ord A p u)), one_mul]
  · simp only [sphericalFactor, ho, hc]

theorem branchCoefficient_eq_of_rel (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (x y : Fˣ)
    (h : QuotientGroup.leftRel (ThetaReflectionData.rationalGamma A) x y) :
    branchCoefficient A G σ ψ m D b x = branchCoefficient A G σ ψ m D b y := by
  have hh : x⁻¹ * y ∈ A.U.map (powMonoidHom 6) := by
    simpa only [QuotientGroup.leftRel_apply, ThetaReflectionData.rationalGamma] using h
  obtain ⟨u, hu, he⟩ := hh
  have hy : y = x * u ^ 6 := by
    change u ^ 6 = x⁻¹ * y at he
    rw [he]; group
  rw [hy]
  unfold branchCoefficient
  apply finprod_congr
  intro p
  exact (local_factor_sixth A G σ ψ m D b p x ⟨u, hu⟩).symm

def branchFrequencyCoefficient (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) : ThetaReflectionData.Frequency A → ℂ :=
  Quotient.lift (branchCoefficient A G σ ψ m D b)
    (branchCoefficient_eq_of_rel A G σ ψ m D b)

theorem exteriorCoefficient_eq_of_rel (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m) (x y : Fˣ)
    (h : QuotientGroup.leftRel (ThetaReflectionData.rationalGamma A) x y) :
    exteriorCoefficient A G σ ψ m D x = exteriorCoefficient A G σ ψ m D y := by
  have hh : x⁻¹ * y ∈ A.U.map (powMonoidHom 6) := by
    simpa only [QuotientGroup.leftRel_apply, ThetaReflectionData.rationalGamma] using h
  obtain ⟨u, hu, he⟩ := hh
  have hy : y = x * u ^ 6 := by
    change u ^ 6 = x⁻¹ * y at he
    rw [he]; group
  rw [hy]
  unfold exteriorCoefficient
  apply finprod_congr
  intro p
  exact (exterior_local_factor_sixth A G σ ψ m D p x ⟨u, hu⟩).symm

def exteriorFrequencyCoefficient (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m) :
    ThetaReflectionData.Frequency A → ℂ :=
  Quotient.lift (exteriorCoefficient A G σ ψ m D)
    (exteriorCoefficient_eq_of_rel A G σ ψ m D)

private lemma rowIndex_d (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (p : ExteriorPrime A) (hp : p.val ∈ support D.d.val) : rowIndex A m p.val = 1 := by
  have hh := exponent_zero _ _ (disjoint_support _ _ D.d.property.1 D.h.property.1
    (by rw [sup_comm]; exact D.coprime) p.val hp)
  have hd := exponent_one _ D.d.property.1 D.squarefree p.val hp
  have hr : order p.val (ThetaReflectionData.rowUnit A m) = 1 := by
    rw [D.row_eq, order_mul, order_unit, generator_order, D.factorization]
    simp only [idealPrimeExponent,
      UniqueFactorizationMonoid.normalizedFactors_mul D.h.property.1 D.d.property.1,
      Multiset.count_add] at *
    rw [hh, hd]; norm_num
  apply Fin.ext
  simp [rowIndex, hr]

 def exteriorSupport (A : SArithmeticData F) (I : A.Exterior) :
    Finset (ExteriorPrime A) :=
  (support I.val).attach.map ⟨supportPrime A I, by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun z : ExteriorPrime A => z.val) h⟩

 lemma mem_exteriorSupport (A : SArithmeticData F) (I : A.Exterior)
    (p : ExteriorPrime A) : p ∈ exteriorSupport A I ↔ p.val ∈ support I.val := by
  simp only [exteriorSupport, Finset.mem_map, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨q, rfl⟩; exact q.property
  · intro h
    exact ⟨⟨p.val,h⟩, Subtype.ext rfl⟩

 def primeProduct (A : SArithmeticData F) (s : Finset (ExteriorPrime A)) :
    A.Exterior := ⟨∏ p ∈ s, p.val.asIdeal, by
  constructor
  · exact Finset.prod_ne_zero_iff.mpr (fun p _ => p.val.ne_bot)
  · apply Ideal.isCoprime_iff_sup_eq.mp
    apply IsCoprime.prod_left
    intro p hp
    exact Ideal.isCoprime_iff_sup_eq.mpr (primeIdeal A p).property.2⟩

private lemma primeProduct_factors (A : SArithmeticData F) (s : Finset (ExteriorPrime A)) :
    UniqueFactorizationMonoid.normalizedFactors (primeProduct A s).val =
      s.val.map (fun p => p.val.asIdeal) := by
  apply UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  exact q.val.prime

 lemma primeProduct_support (A : SArithmeticData F) (s : Finset (ExteriorPrime A)) :
    exteriorSupport A (primeProduct A s) = s := by
  ext p
  rw [mem_exteriorSupport]
  simp only [support, Finset.mem_preimage, idealPrimeSupport, primeProduct_factors,
    Multiset.mem_toFinset, Multiset.mem_map]
  constructor
  · rintro ⟨q, hq, he⟩
    have h : q = p := Subtype.ext (HeightOneSpectrum.asIdeal_injective he)
    simpa [h] using hq
  · intro hp; exact ⟨p,hp,rfl⟩

private lemma exteriorSupport_injective (A : SArithmeticData F) (I J : A.Exterior)
    (hI : Squarefree I.val) (hJ : Squarefree J.val)
    (h : exteriorSupport A I = exteriorSupport A J) : I = J := by
  have hs : support I.val = support J.val := by
    ext p
    by_cases hp : p ∈ A.Sf
    · have hi : p ∉ support I.val := fun hi => support_outside A I p hi hp
      have hj : p ∉ support J.val := fun hj => support_outside A J p hj hp
      simp [hi,hj]
    · rw [← mem_exteriorSupport A I ⟨p,hp⟩, h, mem_exteriorSupport A J ⟨p,hp⟩]
  have hps : idealPrimeSupport I.val = idealPrimeSupport J.val := by
    ext p
    by_cases hp : ∃ q : HeightOneSpectrum (𝓞 F), q.asIdeal = p
    · obtain ⟨q,rfl⟩ := hp
      simpa only [support, Finset.mem_preimage] using (Finset.ext_iff.mp hs q)
    · have hn (K : Ideal (𝓞 F)) : p ∉ idealPrimeSupport K := by
        intro h
        have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor p
          (Multiset.mem_toFinset.mp h)
        exact hp ⟨⟨p, Ideal.isPrime_of_prime hprime, hprime.ne_zero⟩, rfl⟩
      simp [hn]
  apply Subtype.ext
  have ni := UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors I.property.1 |>.mp hI
  have nj := UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors J.property.1 |>.mp hJ
  have hfac : UniqueFactorizationMonoid.normalizedFactors I.val =
      UniqueFactorizationMonoid.normalizedFactors J.val := by
    have hh := congrArg Finset.val hps
    simpa only [idealPrimeSupport, Multiset.toFinset_val, ni.dedup, nj.dedup] using hh
  exact associated_iff_eq.mp ((UniqueFactorizationMonoid.prod_normalizedFactors I.property.1).symm.trans
    (hfac ▸ UniqueFactorizationMonoid.prod_normalizedFactors J.property.1))

 lemma primeProduct_squarefree (A : SArithmeticData F) (s : Finset (ExteriorPrime A)) :
    Squarefree (primeProduct A s).val := by
  apply (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
    (primeProduct A s).property.1).mpr
  rw [primeProduct_factors]
  exact s.nodup.map (by
    intro p q h
    exact Subtype.ext (HeightOneSpectrum.asIdeal_injective h))

private lemma radical_product_eq (A : SArithmeticData F) (I : A.Exterior) :
    (primeProduct A (exteriorSupport A I)).val = idealRadical I.val := by
  change (∏ p ∈ exteriorSupport A I, p.val.asIdeal) = ∏ p ∈ idealPrimeSupport I.val, p
  unfold exteriorSupport
  rw [Finset.prod_map]
  change (∏ p ∈ (support I.val).attach, p.val.asIdeal) = _
  rw [Finset.prod_attach]
  apply Finset.prod_bij (fun p _ => p.asIdeal)
  · intro p hp
    simpa only [support, Finset.mem_preimage] using hp
  · intro p hp q hq he
    exact HeightOneSpectrum.asIdeal_injective he
  · intro p hp
    have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor p
      (Multiset.mem_toFinset.mp hp)
    refine ⟨⟨p, Ideal.isPrime_of_prime hprime, hprime.ne_zero⟩, ?_, rfl⟩
    simpa only [support, Finset.mem_preimage] using hp
  · intro p hp; rfl

 lemma primeProduct_dvd_radical (A : SArithmeticData F) (I : A.Exterior)
    (s : Finset (ExteriorPrime A)) (hs : s ⊆ exteriorSupport A I) :
    (primeProduct A s).val ∣ idealRadical I.val := by
  rw [← radical_product_eq A I]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hs

private lemma support_row (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (p : ExteriorPrime A) :
    p.val ∈ support D.rowIdeal.val ↔ p.val ∈ support D.h.val ∨ p.val ∈ support D.d.val := by
  simp only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset,
    D.factorization, UniqueFactorizationMonoid.normalizedFactors_mul
      D.h.property.1 D.d.property.1, Multiset.mem_add]

 def nonzeroFactor (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (p : ExteriorPrime A) (x : Fˣ) : ℂ :=
  sexticReflectedNonzeroDigits (residueCharacter A σ p) (ψ p)
    (rowIndex A m p.val) (order p.val x + 2) (unitResidue p.val (localUnit A G p x))

 def zeroFactor (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (p : ExteriorPrime A) (x : Fˣ) : ℂ :=
  sexticFourierMask (residueCharacter A σ p) (ψ p) (rowIndex A m p.val) 0 *
    sphericalFactor A G σ ψ p x

private lemma zeroFactor_zero (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (p : ExteriorPrime A) (x : Fˣ)
    (h : rowIndex A m p.val ≠ 0) : zeroFactor A G σ ψ m p x = 0 := by
  have hj : (rowIndex A m p.val).val ≠ 0 := by
    intro hh; exact h (Fin.ext hh)
  simp [zeroFactor, sexticFourierMask, hj]

private lemma local_expansion (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (p : ExteriorPrime A) (x : Fˣ) (hp : p.val ∈ support D.rowIdeal.val) :
    exteriorLocalFactor A G σ ψ m D p x =
      nonzeroFactor A G σ ψ m p x + zeroFactor A G σ ψ m p x := by
  simp [exteriorLocalFactor, hp, nonzeroFactor, zeroFactor, sexticReflectedDigitModel,
    sphericalFactor, symbol]

private lemma branchLocalFactor_cases (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (p : ExteriorPrime A) (x : Fˣ) :
    branchLocalFactor A G σ ψ m D b p x =
      if p ∈ exteriorSupport A D.h then
        if p ∈ exteriorSupport A b.f then nonzeroFactor A G σ ψ m p x
        else zeroFactor A G σ ψ m p x
      else exteriorLocalFactor A G σ ψ m D p x := by
  by_cases hh : p.val ∈ support D.h.val
  · by_cases hf : p.val ∈ support b.f.val
    · simp [branchLocalFactor, mem_exteriorSupport, hh, hf, nonzeroFactor]
    · have hd := disjoint_support _ _ D.h.property.1 D.d.property.1 D.coprime p.val hh
      have hj : rowIndex A m p.val = 0 := by
        by_contra hj
        exact hf (b.mandatory p.val hh hj)
      have hcard : Fintype.card (DHCubic.Residue F p.val) = Ideal.absNorm p.val.asIdeal := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
      simp [branchLocalFactor, mem_exteriorSupport, hh, hf, hd, zeroFactor, hj,
        sexticFourierMask, idealNorm, hcard]
  · have hf : p.val ∉ support b.f.val := fun hf => hh (f_in_h A G m D b p.val hf)
    by_cases hd : p.val ∈ support D.d.val
    · have hj := rowIndex_d A G m D p hd
      have hr := (support_row A G m D p).mpr (Or.inr hd)
      simp [branchLocalFactor, mem_exteriorSupport, hh, hf, hd,
        exteriorLocalFactor, hr, sexticReflectedDigitModel_nonzero_mask, hj]
    · have hr : p.val ∉ support D.rowIdeal.val := by
        simpa [support_row, hh, hd]
      simp [branchLocalFactor, mem_exteriorSupport, hh, hf, hd, exteriorLocalFactor, hr]

lemma finite_split {P : Type*} [DecidableEq P] (s : Finset P) (f : P → ℂ)
    (hf : Function.HasFiniteMulSupport f) :
    (∏ᶠ p, f p) = (∏ p ∈ s, f p) * ∏ᶠ p, if p ∈ s then 1 else f p := by
  let g := fun p => if p ∈ s then f p else 1
  let h := fun p => if p ∈ s then 1 else f p
  have hg : Function.mulSupport g ⊆ s := by
    intro p hp
    by_contra hn
    exact hp (by simp [g, show p ∉ s from hn])
  have hh : Function.HasFiniteMulSupport h := by
    apply hf.subset
    intro p hp
    by_contra hn
    exact hp (by simp only [Function.mem_mulSupport, not_not] at hn; simp [h, hn])
  have he : f = fun p => g p * h p := by
    funext p; simp [g, h]; split_ifs <;> simp
  calc
    (∏ᶠ p, f p) = ∏ᶠ p, g p * h p := by congr 1
    _ = (∏ᶠ p, g p) * ∏ᶠ p, h p := finprod_mul_distrib (s.finite_toSet.subset hg) hh
    _ = (∏ p ∈ s, f p) * ∏ᶠ p, h p := by
      rw [finprod_eq_prod_of_mulSupport_subset g hg]
      congr 1
      exact Finset.prod_congr rfl (fun p hp => by simp [g, hp])

lemma exteriorLocalFactor_finite (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m) (x : Fˣ) :
    Function.HasFiniteMulSupport (fun p => exteriorLocalFactor A G σ ψ m D p x) := by
  have hs := ((support D.rowIdeal.val).finite_toSet.union (order_finite_support x)).preimage
    (f := fun p : ExteriorPrime A => p.val) Subtype.val_injective.injOn
  apply hs.subset
  intro p hp
  by_contra hn
  have hh : p.val ∉ support D.rowIdeal.val ∧ order p.val x = 0 := by
    simpa only [Set.mem_preimage, Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq,
      not_or, not_not] using hn
  exact hp (by simp [exteriorLocalFactor, hh.1, sphericalFactor, hh.2, sexticSphericalCoefficient])

private lemma branchProduct_eq (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (x : Fˣ) :
    branchCoefficient A G σ ψ m D b x =
      (∏ p ∈ exteriorSupport A D.h,
        if p ∈ exteriorSupport A b.f then nonzeroFactor A G σ ψ m p x
        else zeroFactor A G σ ψ m p x) *
      ∏ᶠ p : ExteriorPrime A, if p ∈ exteriorSupport A D.h then 1
        else exteriorLocalFactor A G σ ψ m D p x := by
  rw [branchCoefficient, finite_split (exteriorSupport A D.h) _
    (branchLocalFactor_finite_support A G σ ψ m D b x)]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    rw [branchLocalFactor_cases, if_pos hp]
  · apply finprod_congr
    intro p
    by_cases hp : p ∈ exteriorSupport A D.h
    · simp [hp]
    · simp [hp, branchLocalFactor_cases]

 def subsetBranch (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (s : Finset (ExteriorPrime A)) (hs : s ⊆ exteriorSupport A D.h)
    (hm : ∀ p ∈ exteriorSupport A D.h, rowIndex A m p.val ≠ 0 → p ∈ s) :
    Branch A G m D where
  f := primeProduct A s
  squarefree := primeProduct_squarefree A s
  divides_radical := primeProduct_dvd_radical A D.h s hs
  mandatory := by
    intro p hp hj
    let q : ExteriorPrime A := ⟨p, support_outside A D.h p hp⟩
    have hq := hm q ((mem_exteriorSupport A D.h q).mpr hp) hj
    exact (mem_exteriorSupport A (primeProduct A s) q).mp (by rw [primeProduct_support]; exact hq)

private lemma branchSupport_sub (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) : exteriorSupport A b.f ⊆ exteriorSupport A D.h := by
  intro p hp
  exact (mem_exteriorSupport A D.h p).mpr (f_in_h A G m D b p.val
    ((mem_exteriorSupport A b.f p).mp hp))

private lemma branchSupport_injective (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b c : Branch A G m D) (h : exteriorSupport A b.f = exteriorSupport A c.f) : b = c := by
  have hf := exteriorSupport_injective A b.f c.f b.squarefree c.squarefree h
  cases b; cases c; cases hf; rfl

private lemma branchChoice_sum (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m) (x : Fˣ) :
    letI := branches_finite A G m D
    letI : Fintype (Branch A G m D) := Fintype.ofFinite _
    (∑ b : Branch A G m D, ∏ p ∈ exteriorSupport A D.h,
      if p ∈ exteriorSupport A b.f then nonzeroFactor A G σ ψ m p x
      else zeroFactor A G σ ψ m p x) =
    ∏ p ∈ exteriorSupport A D.h,
      (nonzeroFactor A G σ ψ m p x + zeroFactor A G σ ψ m p x) := by
  letI := branches_finite A G m D
  letI : Fintype (Branch A G m D) := Fintype.ofFinite _
  let H := exteriorSupport A D.h
  let a := fun p => nonzeroFactor A G σ ψ m p x
  let z := fun p => zeroFactor A G σ ψ m p x
  have hp (s : Finset (ExteriorPrime A)) (hs : s ⊆ H) :
      (∏ p ∈ s, a p) * (∏ p ∈ H \ s, z p) =
      ∏ p ∈ H, if p ∈ s then a p else z p := by
    rw [Finset.prod_ite]
    congr 1
    · congr 1; ext p; simp only [Finset.mem_filter]; exact (and_iff_right_of_imp (fun h => hs h)).symm
    · congr 1; ext p; simp
  have hm (s : Finset (ExteriorPrime A)) (hs : s ⊆ H)
      (hn : (∏ p ∈ s, a p) * (∏ p ∈ H \ s, z p) ≠ 0) :
      ∀ p ∈ H, rowIndex A m p.val ≠ 0 → p ∈ s := by
    intro p hp hj
    by_contra hh
    apply hn
    have hz : ∏ p ∈ H \ s, z p = 0 := Finset.prod_eq_zero_iff.mpr
      ⟨p, Finset.mem_sdiff.mpr ⟨hp,hh⟩, zeroFactor_zero A G σ ψ m p x hj⟩
    rw [hz, mul_zero]
  symm
  rw [Finset.prod_add]
  apply Finset.sum_bij_ne_zero (fun s hs hn =>
    subsetBranch A G m D s (Finset.mem_powerset.mp hs) (hm s (Finset.mem_powerset.mp hs) hn))
  · intro s hs hn; exact Finset.mem_univ _
  · intro s hs hn t ht hnt he
    have he' := congrArg (fun b : Branch A G m D => exteriorSupport A b.f) he
    simpa only [subsetBranch, primeProduct_support] using he'
  · intro b hb hn
    refine ⟨exteriorSupport A b.f, Finset.mem_powerset.mpr (branchSupport_sub A G m D b), ?_, ?_⟩
    · rw [hp _ (branchSupport_sub A G m D b)]; exact hn
    · apply branchSupport_injective A G m D
      exact primeProduct_support A _
  · intro s hs hn
    change (∏ p ∈ s, a p) * (∏ p ∈ H \ s, z p) = _
    rw [hp s (Finset.mem_powerset.mp hs)]
    simp only [subsetBranch, primeProduct_support]
    rfl

theorem sum_branches (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m) (x : Fˣ) :
    letI := branches_finite A G m D
    letI : Fintype (Branch A G m D) := Fintype.ofFinite _
    (∑ b : Branch A G m D, branchCoefficient A G σ ψ m D b x) =
      exteriorCoefficient A G σ ψ m D x := by
  letI := branches_finite A G m D
  letI : Fintype (Branch A G m D) := Fintype.ofFinite _
  simp_rw [branchProduct_eq]
  rw [← Finset.sum_mul, branchChoice_sum, exteriorCoefficient,
    finite_split (exteriorSupport A D.h) _ (exteriorLocalFactor_finite A G σ ψ m D x)]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  apply (local_expansion A G σ ψ m D p x _).symm
  exact (support_row A G m D p).mpr
    (Or.inl ((mem_exteriorSupport A D.h p).mp hp))

private lemma residue_coprime_branch (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ExteriorPrime A) : Nat.Coprime (Fintype.card (DHCubic.Residue F p.val)) 6 := by
  have hd := MulChar.orderOf_dvd_card_sub_one (DHCubic.Residue F p.val) (residueCharacter A σ p)
  rw [char_order] at hd
  obtain ⟨n, hn⟩ := hd
  have hc := Fintype.one_lt_card (α := DHCubic.Residue F p.val)
  have he : Fintype.card (DHCubic.Residue F p.val) = 6 * n + 1 := by omega
  rw [he, Nat.coprime_comm]
  simp

private lemma spherical_nonzero_support {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (e : ℤ)
    (he : sexticSphericalCoefficient χ ψ e ≠ 0) :
    0 ≤ e ∧ (e % 3 = 0 ∨ e % 3 = 1) := by
  by_contra h
  have hb : e < 0 ∨ (e % 3 ≠ 0 ∧ e % 3 ≠ 1) := by omega
  rcases hb with hb | ⟨hb, hc⟩
  · exact he (by simp [sexticSphericalCoefficient, hb])
  · exact he (by simp [sexticSphericalCoefficient, hb, hc])

theorem branchCoefficient_zero_outside (A : SArithmeticData F)
    (G : AllowedRecipe A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (ν : ThetaReflectionData.Frequency A)
    (hν : ¬ Supported A G m D b ν) :
    branchFrequencyCoefficient A G σ ψ m D b ν = 0 := by
  induction ν using Quotient.inductionOn with
  | h x =>
    change branchCoefficient A G σ ψ m D b x = 0
    by_contra hn
    have hl (p : ExteriorPrime A) : branchLocalFactor A G σ ψ m D b p x ≠ 0 := by
      intro hz
      exact hn (finprod_eq_zero _ p hz (branchLocalFactor_finite_support A G σ ψ m D b x))
    have hdigit (p : ExteriorPrime A)
        (hp : p.val ∈ support D.d.val ∪ support b.f.val) :
        0 ≤ order p.val x + 2 ∧
          ((order p.val x + 2) % 3 = 0 ∨ (order p.val x + 2) % 3 = 1) := by
      have hh := hl p
      simp only [branchLocalFactor, if_pos hp] at hh
      apply spherical_nonzero_support (residueCharacter A σ p) (ψ p) _
      intro hz
      apply hh
      simp only [sexticReflectedNonzeroDigits, hz, zero_mul]
    apply hν
    refine ⟨x, rfl, ?_, ?_, ?_⟩
    · intro p hp
      let q : ExteriorPrime A := ⟨p, support_outside A D.d p hp⟩
      have hj : rowIndex A m p = 1 := rowIndex_d A G m D q hp
      have hpq : q.val ∈ support D.d.val ∪ support b.f.val := Finset.mem_union_left _ hp
      have he := hdigit q hpq
      change 0 ≤ order p x + 2 ∧
        ((order p x + 2) % 3 = 0 ∨ (order p x + 2) % 3 = 1) at he
      have heq : order p x + 2 = 0 := by
        by_contra h
        have hpos : 0 < order p x + 2 := by omega
        have hz := sexticReflectedNonzeroDigits_eq_zero (residueCharacter A σ q) (ψ q)
          (char_order A σ q) (hψ q) (residue_coprime_branch A σ q)
          (rowIndex A m p) (order p x + 2)
          (unitResidue p (localUnit A G q x))
          (unitResidue_ne_zero p _ (localUnit_order A G q x))
          (Or.inr (Or.inr ⟨hpos, by rw [hj]; decide⟩))
        apply hl q
        simp only [branchLocalFactor, if_pos hpq]
        exact hz
      omega
    · intro p hp
      exact hdigit ⟨p, support_outside A b.f p hp⟩ (Finset.mem_union_right _ hp)
    · intro p hd hf
      have hh := hl p
      have ha : p.val ∉ support D.d.val ∪ support b.f.val := by simpa using And.intro hd hf
      have hs : sphericalFactor A G σ ψ p x ≠ 0 := by
        intro hz
        apply hh
        simp [branchLocalFactor, ha, hz]
      apply spherical_nonzero_support (residueCharacter A σ p) (ψ p) _
      intro hz
      apply hs
      simp only [sphericalFactor, hz, zero_mul]

theorem branch_frequency_coefficient_exact (A : SArithmeticData F)
    (G : AllowedRecipe A) (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b) :
    branchFrequencyCoefficient A G σ ψ m D b (coordinateFrequency A G U m D b v) =
      exactCoefficient A G U σ ψ m D b v := by
  exact branch_coefficient_exact A G U σ ψ hψ m D b v

theorem sum_branches_frequency (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (ν : ThetaReflectionData.Frequency A) :
    letI := branches_finite A G m D
    letI : Fintype (Branch A G m D) := Fintype.ofFinite _
    (∑ b : Branch A G m D, branchFrequencyCoefficient A G σ ψ m D b ν) =
      exteriorFrequencyCoefficient A G σ ψ m D ν := by
  induction ν using Quotient.inductionOn with
  | h x => exact sum_branches A G σ ψ m D x

namespace CanonicalCoordinateProof
private lemma ord_mul (p : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    order p (x * y) = order p x + order p y := by
  simp only [order, Units.val_mul, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
    ((Valuation.ne_zero_iff _).mpr y.ne_zero), neg_add]
private lemma ord_pow (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ) (n : ℕ) :
    order p (x ^ n) = (n : ℤ) * order p x := by
  simp only [order, Units.val_pow_eq_pow_val, map_pow, WithZero.log_pow, smul_eq_mul]
  ring
private lemma ord_div (p : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    order p (x / y) = order p x - order p y := by
  rw [div_eq_mul_inv, ord_mul]
  simp only [order, Units.val_inv_eq_inv_val, map_inv₀, WithZero.log_inv]
  ring
private lemma ord_unit (A : SArithmeticData F) (p : ExteriorPrime A) (u : A.U) :
    order p.val u.val = 0 := by simp [order, u.property p.val p.property]

 def primeEquiv (A : SArithmeticData F) :
    ExteriorPrime A ≃ ExteriorEulerPrimeIndex.exteriorPrimeRawIndex A.cS where
  toFun p := ⟨primeIdeal A p, p.val.prime⟩
  invFun p := ⟨⟨p.val.val, Ideal.isPrime_of_prime p.property, p.property.ne_zero⟩, by
    intro h
    have hc : A.cS ≤ p.val.val := Ideal.IsPrime.prod_le
      (Ideal.isPrime_of_prime p.property) |>.mpr ⟨_, h, le_rfl⟩
    exact (Ideal.isPrime_of_prime p.property).ne_top
      (top_le_iff.mp (p.val.property.2.symm.le.trans (sup_le le_rfl hc)))⟩
  left_inv p := rfl
  right_inv p := rfl
def idealEquiv (A : SArithmeticData F) : A.Exterior ≃ (ExteriorPrime A →₀ ℕ) :=
  (ExteriorEulerPrimeIndex.exponentEquiv A.cS).trans
    (Finsupp.domCongr (primeEquiv A).symm).toEquiv

private theorem finite_order_support (A : SArithmeticData F) (x : Fˣ) :
    {p : ExteriorPrime A | order p.val x ≠ 0}.Finite := by
  have h := (HeightOneSpectrum.Support.finite (𝓞 F) (x : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((x⁻¹ : Fˣ) : F))
  apply (h.preimage (f := fun p : ExteriorPrime A => p.val) Subtype.val_injective.injOn).subset
  intro p hp
  change p.val ∈ HeightOneSpectrum.Support (𝓞 F) (x : F) ∪
    HeightOneSpectrum.Support (𝓞 F) ((x⁻¹ : Fˣ) : F)
  by_contra hn
  have hle : p.val.valuation F (x : F) ≤ 1 := le_of_not_gt (fun h => hn (Or.inl h))
  have hinv : p.val.valuation F ((x⁻¹ : Fˣ) : F) ≤ 1 :=
    le_of_not_gt (fun h => hn (Or.inr h))
  have hv : p.val.valuation F (x : F) = 1 := by
    apply le_antisymm hle
    rw [Units.val_inv_eq_inv_val, map_inv₀] at hinv
    exact (inv_le_one₀ (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr x.ne_zero))).mp hinv
  exact hp (by simp [order, hv])

theorem order_eq_of_frequency_eq (A : SArithmeticData F) (x y : Fˣ)
    (h : (QuotientGroup.mk x : ThetaReflectionData.Frequency A) = QuotientGroup.mk y)
    (p : ExteriorPrime A) : order p.val x = order p.val y := by
  have hr := Quotient.exact h
  change QuotientGroup.leftRel (ThetaReflectionData.rationalGamma A) x y at hr
  rw [QuotientGroup.leftRel_apply] at hr
  obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp hr
  have ho := congrArg (order p.val) he
  have hi : order p.val (x⁻¹ * y) = -order p.val x + order p.val y := by
    rw [ord_mul]
    simp only [order, Units.val_inv_eq_inv_val, map_inv₀, WithZero.log_inv]
  rw [powMonoidHom_apply, ord_pow, ord_unit A p ⟨u, hu⟩, mul_zero, hi] at ho
  omega
private lemma exp_zero (I : Ideal (𝓞 F)) (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∉ support I) : idealPrimeExponent p.asIdeal I = 0 := by
  apply Multiset.count_eq_zero.mpr
  simpa only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using hp
private lemma exp_le_one {A : SArithmeticData F} (I : A.Exterior) (hs : Squarefree I.val)
    (p : HeightOneSpectrum (𝓞 F)) : idealPrimeExponent p.asIdeal I.val ≤ 1 := by
  exact Multiset.nodup_iff_count_le_one.mp
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors I.property.1 |>.mp hs) _
private lemma supported_a (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p ∉ support b.f.val) : p ∉ support v.a.val := by
  intro ha
  exact hp (by simpa only [support, Finset.mem_preimage] using
    v.a_supported (show p.asIdeal ∈ idealPrimeSupport v.a.val by
      simpa only [support, Finset.mem_preimage] using ha))
private lemma mem_support_iff (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (p : HeightOneSpectrum (𝓞 F)) : p ∈ support I ↔ I ≤ p.asIdeal := by
  simp only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset]
  exact Ideal.mem_normalizedFactors_iff hI |>.trans (and_iff_right p.isPrime)
private lemma coprime_parts (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b) (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∈ support D.d.val ∨ p ∈ support b.f.val) :
    p ∉ support v.c.val ∧ p ∉ support v.n.val := by
  have hd : D.d.val * b.f.val ≤ p.asIdeal := by
    rcases hp with hp | hp
    · exact Ideal.mul_le_left.trans ((mem_support_iff _ D.d.property.1 p).mp hp)
    · exact Ideal.mul_le_right.trans ((mem_support_iff _ b.f.property.1 p).mp hp)
  constructor <;> intro h
  · exact p.isPrime.ne_top (top_le_iff.mp (v.coprime.symm.le.trans
      (sup_le (Ideal.mul_le_left.trans ((mem_support_iff _ v.c.property.1 p).mp h)) hd)))
  · exact p.isPrime.ne_top (top_le_iff.mp (v.coprime.symm.le.trans
      (sup_le (Ideal.mul_le_right.trans ((mem_support_iff _ v.n.property.1 p).mp h)) hd)))
private lemma ideal_ext (A : SArithmeticData F) (I J : A.Exterior)
    (h : ∀ p : ExteriorPrime A, idealPrimeExponent p.val.asIdeal I.val =
      idealPrimeExponent p.val.asIdeal J.val) : I = J := by
  apply (idealEquiv A).injective
  ext p
  exact h p

private theorem coordinate_ideals_eq (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D)
    (v w : Coordinates A G m D b)
    (h : ∀ p : ExteriorPrime A,
      order p.val (coordinateRepresentative A G U m D b v) =
      order p.val (coordinateRepresentative A G U m D b w)) :
    v.a = w.a ∧ v.c = w.c ∧ v.n = w.n := by
  have ha : v.a = w.a := by
    apply ideal_ext A
    intro p
    by_cases hf : p.val ∈ support b.f.val
    · have hv := CanonicalCoefficientProof.order_coordinateRepresentative_of_mem_f A G U m D b v p hf
      have hw := CanonicalCoefficientProof.order_coordinateRepresentative_of_mem_f A G U m D b w p hf
      have hh := h p
      omega
    · rw [exp_zero _ _ (supported_a A G m D b v _ hf),
        exp_zero _ _ (supported_a A G m D b w _ hf)]
  have hcn (p : ExteriorPrime A) :
      idealPrimeExponent p.val.asIdeal v.c.val = idealPrimeExponent p.val.asIdeal w.c.val ∧
      idealPrimeExponent p.val.asIdeal v.n.val = idealPrimeExponent p.val.asIdeal w.n.val := by
    by_cases hr : p.val ∈ support D.d.val ∨ p.val ∈ support b.f.val
    · obtain ⟨hvc, hvn⟩ := coprime_parts A G m D b v p.val hr
      obtain ⟨hwc, hwn⟩ := coprime_parts A G m D b w p.val hr
      simp [exp_zero _ _ hvc, exp_zero _ _ hvn, exp_zero _ _ hwc, exp_zero _ _ hwn]
    · push Not at hr
      have hv := CanonicalCoefficientProof.order_coordinateRepresentative_of_not_mem A G U m D b v p hr.1 hr.2
      have hw := CanonicalCoefficientProof.order_coordinateRepresentative_of_not_mem A G U m D b w p hr.1 hr.2
      have hvc := exp_le_one v.c v.c_squarefree p.val
      have hwc := exp_le_one w.c w.c_squarefree p.val
      have hh := h p
      constructor <;> omega
  exact ⟨ha, ideal_ext A _ _ (fun p => (hcn p).1),
    ideal_ext A _ _ (fun p => (hcn p).2)⟩

private theorem coordinateFrequency_injective (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D) :
    Function.Injective (coordinateFrequency A G U m D b) := by
  intro v w h
  have hi := coordinate_ideals_eq A G U m D b v w
    (order_eq_of_frequency_eq A _ _ h)
  obtain ⟨ha, hc, hn⟩ := hi
  have he : v.epsilon = w.epsilon := by
    have hr := Quotient.exact h
    change QuotientGroup.leftRel (ThetaReflectionData.rationalGamma A)
      (coordinateRepresentative A G U m D b v)
      (coordinateRepresentative A G U m D b w) at hr
    rw [QuotientGroup.leftRel_apply] at hr
    have hr' : (U.representative v.epsilon).val⁻¹ * (U.representative w.epsilon).val ∈
        ThetaReflectionData.rationalGamma A := by
      have eqr : (coordinateRepresentative A G U m D b v)⁻¹ *
          coordinateRepresentative A G U m D b w =
          (U.representative v.epsilon).val⁻¹ * (U.representative w.epsilon).val := by
        simp only [coordinateRepresentative, ha, hc, hn]
        simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
      rwa [eqr] at hr
    obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp hr'
    have hh : (U.representative v.epsilon)⁻¹ * U.representative w.epsilon ∈
        A.unitSixthPowers := by
      refine ⟨⟨u, hu⟩, ?_⟩
      apply Subtype.ext
      exact he
    have hq : (QuotientGroup.mk (U.representative v.epsilon) : A.UnitQuotient) =
        QuotientGroup.mk (U.representative w.epsilon) := by
      apply Quotient.sound
      change QuotientGroup.leftRel A.unitSixthPowers _ _
      rwa [QuotientGroup.leftRel_apply]
    simpa only [U.represents] using hq
  cases v
  cases w
  cases he
  cases ha
  cases hc
  cases hn
  rfl

theorem exterior_ideal_of_exponents (A : SArithmeticData F) (f : ExteriorPrime A → ℕ)
    (hf : {p | f p ≠ 0}.Finite) :
    ∃ I : A.Exterior, ∀ p : ExteriorPrime A, idealPrimeExponent p.val.asIdeal I.val = f p := by
  let e := Finsupp.ofSupportFinite f hf
  refine ⟨(idealEquiv A).symm e, ?_⟩
  intro p
  exact congrArg (fun g : ExteriorPrime A →₀ ℕ => g p) ((idealEquiv A).apply_symm_apply e)

theorem squarefree_of_exponents_le_one (A : SArithmeticData F) (I : A.Exterior)
    (h : ∀ p : ExteriorPrime A, idealPrimeExponent p.val.asIdeal I.val ≤ 1) : Squarefree I.val := by
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors I.property.1,
    Multiset.nodup_iff_count_le_one]
  intro q
  by_cases hq : q ∈ UniqueFactorizationMonoid.normalizedFactors I.val
  · have hp := UniqueFactorizationMonoid.prime_of_normalized_factor q hq
    let p : HeightOneSpectrum (𝓞 F) := ⟨q, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    exact h ⟨p, support_outside A I p (by
      simpa only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using hq)⟩
  · simp [Multiset.count_eq_zero_of_notMem hq]

private theorem supportedOn_of_exponents (A : SArithmeticData F) (I J : A.Exterior)
    (h : ∀ p : ExteriorPrime A, p.val ∉ support J.val → idealPrimeExponent p.val.asIdeal I.val = 0) :
    IdealSupportedOn I.val J.val := by
  intro q hq
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor q (Multiset.mem_toFinset.mp hq)
  let p : HeightOneSpectrum (𝓞 F) := ⟨q, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
  have hpm : p ∈ support I.val := by simpa only [support, Finset.mem_preimage] using hq
  have he : 0 < idealPrimeExponent p.asIdeal I.val := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hq)
  have hpm' : p ∈ support J.val := by
    by_contra hn
    have hz : idealPrimeExponent p.asIdeal I.val = 0 := h ⟨p, support_outside A I p hpm⟩ hn
    omega
  simpa only [support, Finset.mem_preimage] using hpm'

private theorem coprime_of_exponents (A : SArithmeticData F) (I J : A.Exterior)
    (h : ∀ p : ExteriorPrime A, p.val ∈ support J.val → idealPrimeExponent p.val.asIdeal I.val = 0) :
    I.val ⊔ J.val = ⊤ := by
  by_contra hn
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (I.val ⊔ J.val) hn
  have hMn : M ≠ ⊥ := by
    intro hh
    exact I.property.1 (bot_unique ((le_sup_left.trans hle).trans hh.le))
  let p : HeightOneSpectrum (𝓞 F) := ⟨M, hM.isPrime, hMn⟩
  have hi : p ∈ support I.val := (mem_support_iff _ I.property.1 p).mpr (le_sup_left.trans hle)
  have hj : p ∈ support J.val := (mem_support_iff _ J.property.1 p).mpr (le_sup_right.trans hle)
  have hz : idealPrimeExponent p.asIdeal I.val = 0 := h ⟨p, support_outside A I p hi⟩ hj
  have he : 0 < idealPrimeExponent p.asIdeal I.val := by
    apply Multiset.count_pos.mpr
    simpa only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using hi
  omega

theorem ratio_mem_sunit (A : SArithmeticData F) (x y : Fˣ)
    (h : ∀ p : ExteriorPrime A, order p.val x = order p.val y) : x / y ∈ A.U := by
  intro p hp
  have ho : order p (x / y) = 0 := by rw [ord_div, h ⟨p, hp⟩, sub_self]
  have hv : p.valuation F ((x / y : Fˣ) : F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (x / y).ne_zero
  have hl : WithZero.log (p.valuation F ((x / y : Fˣ) : F)) = 0 := by
    simpa only [order, neg_eq_zero] using ho
  rw [← WithZero.exp_log hv, hl, WithZero.exp_zero]

private theorem exists_coordinate_of_matching_orders (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D)
    (x : Fˣ) (v : Coordinates A G m D b)
    (h : ∀ p : ExteriorPrime A, order p.val x =
      order p.val (coordinateRepresentative A G U m D b v)) :
    ∃ w : Coordinates A G m D b, coordinateFrequency A G U m D b w = QuotientGroup.mk x := by
  let y := coordinateRepresentative A G U m D b v
  let u : A.U := ⟨x / y, ratio_mem_sunit A x y h⟩
  let e : A.UnitQuotient := QuotientGroup.mk (u * U.representative v.epsilon)
  let w : Coordinates A G m D b := {v with epsilon := e}
  refine ⟨w, ?_⟩
  have he : (QuotientGroup.mk (U.representative e) : A.UnitQuotient) =
      QuotientGroup.mk (u * U.representative v.epsilon) := U.represents e
  have hr := Quotient.exact he
  change QuotientGroup.leftRel A.unitSixthPowers _ _ at hr
  rw [QuotientGroup.leftRel_apply] at hr
  obtain ⟨t, ht⟩ := hr
  have ht' : (U.representative e).val⁻¹ * (u.val * (U.representative v.epsilon).val) ∈
      ThetaReflectionData.rationalGamma A := by
    apply Subgroup.mem_map.mpr
    exact ⟨t.val, t.property, congrArg Subtype.val ht⟩
  apply Quotient.sound
  change QuotientGroup.leftRel (ThetaReflectionData.rationalGamma A)
    (coordinateRepresentative A G U m D b w) x
  rw [QuotientGroup.leftRel_apply]
  have hy : x = u.val * y := by simp [u]
  rw [hy]
  convert ht' using 1
  dsimp [w, y]
  simp [coordinateRepresentative, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

private theorem exists_coordinate_of_supported (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D)
    (ν : ThetaReflectionData.Frequency A) (hν : Supported A G m D b ν) :
    ∃ v : Coordinates A G m D b, coordinateFrequency A G U m D b v = ν := by
  obtain ⟨x, hx, hd, hf, ho⟩ := hν
  let ae : ExteriorPrime A → ℕ := fun p =>
    if p.val ∈ support b.f.val then (order p.val x + 2).toNat else 0
  let ce : ExteriorPrime A → ℕ := fun p =>
    if p.val ∈ support D.d.val ∨ p.val ∈ support b.f.val then 0 else (order p.val x % 3).toNat
  let ne : ExteriorPrime A → ℕ := fun p =>
    if p.val ∈ support D.d.val ∨ p.val ∈ support b.f.val then 0 else (order p.val x / 3).toNat
  have haF : {p | ae p ≠ 0}.Finite := by
    apply ((support b.f.val).finite_toSet.preimage (f := fun p : ExteriorPrime A => p.val)
      Subtype.val_injective.injOn).subset
    intro p hp
    by_contra hn
    have hn' : p.val ∉ support b.f.val := hn
    exact hp (by simp [ae, hn'])
  have hcF : {p | ce p ≠ 0}.Finite := by
    apply (finite_order_support A x).subset
    intro p hp hz
    exact hp (by simp [ce, hz])
  have hnF : {p | ne p ≠ 0}.Finite := by
    apply (finite_order_support A x).subset
    intro p hp hz
    exact hp (by simp [ne, hz])
  obtain ⟨a, ha⟩ := exterior_ideal_of_exponents A ae haF
  obtain ⟨c, hc⟩ := exterior_ideal_of_exponents A ce hcF
  obtain ⟨n, hn⟩ := exterior_ideal_of_exponents A ne hnF
  have has : IdealSupportedOn a.val b.f.val := by
    apply supportedOn_of_exponents A
    intro p hp
    rw [ha]
    simp [ae, hp]
  have hae : ∀ p ∈ support b.f.val,
      idealPrimeExponent p.asIdeal a.val % 3 = 0 ∨ idealPrimeExponent p.asIdeal a.val % 3 = 1 := by
    intro p hp
    let q : ExteriorPrime A := ⟨p, support_outside A b.f p hp⟩
    have he : idealPrimeExponent p.asIdeal a.val = (order p x + 2).toNat := by
      simpa [ae, q, hp] using ha q
    have hh := hf p hp
    rw [he]
    omega
  have hcs : Squarefree c.val := by
    apply squarefree_of_exponents_le_one A
    intro p
    rw [hc]
    dsimp [ce]
    split_ifs with hh
    · omega
    · push Not at hh
      have ht := ho p hh.1 hh.2
      omega
  have hcpd : c.val ⊔ D.d.val = ⊤ := by
    apply coprime_of_exponents A
    intro p hp; rw [hc]; simp [ce, hp]
  have hcpf : c.val ⊔ b.f.val = ⊤ := by
    apply coprime_of_exponents A
    intro p hp; rw [hc]; simp [ce, hp]
  have hnpd : n.val ⊔ D.d.val = ⊤ := by
    apply coprime_of_exponents A
    intro p hp; rw [hn]; simp [ne, hp]
  have hnpf : n.val ⊔ b.f.val = ⊤ := by
    apply coprime_of_exponents A
    intro p hp; rw [hn]; simp [ne, hp]
  have hcp : (c.val * n.val) ⊔ (D.d.val * b.f.val) = ⊤ := by
    have hcd : c.val ⊔ (D.d.val * b.f.val) = ⊤ := by
      rw [Ideal.sup_mul_eq_of_coprime_left hcpd, hcpf]
    have hnd : n.val ⊔ (D.d.val * b.f.val) = ⊤ := by
      rw [Ideal.sup_mul_eq_of_coprime_left hnpd, hnpf]
    rw [Ideal.mul_sup_eq_of_coprime_left hcd, hnd]
  let v : Coordinates A G m D b := ⟨1, a, c, n, has, hae, hcs, hcp⟩
  have hm : ∀ p : ExteriorPrime A, order p.val x =
      order p.val (coordinateRepresentative A G U m D b v) := by
    intro p
    by_cases hpd : p.val ∈ support D.d.val
    · rw [CanonicalCoefficientProof.order_coordinateRepresentative_of_mem_d A G U m D b v p hpd, hd p.val hpd]
    · by_cases hpf : p.val ∈ support b.f.val
      · have hv := CanonicalCoefficientProof.order_coordinateRepresentative_of_mem_f A G U m D b v p hpf
        change order p.val (coordinateRepresentative A G U m D b v) + 2 =
          (idealPrimeExponent p.val.asIdeal a.val : ℤ) at hv
        rw [ha] at hv
        have he : ae p = (order p.val x + 2).toNat := by simp [ae, hpf]
        rw [he] at hv
        have hh := hf p.val hpf
        omega
      · rw [CanonicalCoefficientProof.order_coordinateRepresentative_of_not_mem A G U m D b v p hpd hpf]
        change order p.val x = (idealPrimeExponent p.val.asIdeal c.val : ℤ) +
          3 * (idealPrimeExponent p.val.asIdeal n.val : ℤ)
        rw [hc, hn]
        have hec : ce p = (order p.val x % 3).toNat := by simp [ce, hpd, hpf]
        have hen : ne p = (order p.val x / 3).toNat := by simp [ne, hpd, hpf]
        rw [hec, hen]
        have hh := ho p hpd hpf
        omega
  obtain ⟨w, hw⟩ := exists_coordinate_of_matching_orders A G U m D b x v hm
  exact ⟨w, hw.trans hx⟩

private theorem supported_iff_existsUnique_of_exists (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D)
    (hex : ∀ ν, Supported A G m D b ν →
      ∃ v : Coordinates A G m D b, coordinateFrequency A G U m D b v = ν)
    (ν : ThetaReflectionData.Frequency A) :
    Supported A G m D b ν ↔
      ∃! v : Coordinates A G m D b, coordinateFrequency A G U m D b v = ν := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := hex ν h
    exact ⟨v, hv, fun w hw => coordinateFrequency_injective A G U m D b (hw.trans hv.symm)⟩
  · rintro ⟨v, hv, _⟩
    rw [← hv]
    exact CanonicalCoefficientProof.coordinateFrequency_supported A G U m D b v

end CanonicalCoordinateProof

theorem coordinates_unique (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D)
    (ν : ThetaReflectionData.Frequency A) :
    Supported A G m D b ν ↔
      ∃! v : Coordinates A G m D b, coordinateFrequency A G U m D b v = ν := by
  exact CanonicalCoordinateProof.supported_iff_existsUnique_of_exists A G U m D b
    (CanonicalCoordinateProof.exists_coordinate_of_supported A G U m D b) ν

end
end DedekindZetaZeroFree.ThetaBranch
