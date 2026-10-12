module

public import DedekindZetaZeroFree.Theta.Whittaker.ExteriorFrequencyBranchCoordinates

@[expose] public section

namespace DedekindZetaZeroFree.ThetaPhaseSeparation
noncomputable section
open scoped NumberField BigOperators Classical
open IsDedekindDomain UniqueFactorizationMonoid ThetaBranch

variable {F : Type} [Field F] [NumberField F]

structure Frozen (A : SArithmeticData F) where
  h : A.Exterior
  powerful : Powerful h.val
  f : A.Exterior
  f_squarefree : Squarefree f.val
  f_divides_radical : f.val ∣ idealRadical h.val
  mandatory : ∀ p ∈ support h.val,
    idealPrimeExponent p.asIdeal h.val % 6 ≠ 0 → p ∈ support f.val
  a : A.Exterior
  a_supported : IdealSupportedOn a.val f.val
  a_exponents : ∀ p ∈ support f.val,
    idealPrimeExponent p.asIdeal a.val % 3 = 0 ∨
      idealPrimeExponent p.asIdeal a.val % 3 = 1
  n : A.Exterior
  n_f_coprime : n.val ⊔ f.val = ⊤
  epsilon : A.UnitQuotient

def powerfulIndex (A : SArithmeticData F) (T : Frozen A)
    (p : HeightOneSpectrum (𝓞 F)) : Fin 6 :=
  ⟨idealPrimeExponent p.asIdeal T.h.val % 6, Nat.mod_lt _ (by decide)⟩

 theorem order_mul (p : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
  order p (x*y) = order p x + order p y := by
  have hx : p.valuation F (x : F) ≠ 0 := (map_ne_zero (p.valuation F)).mpr x.ne_zero
  have hy : p.valuation F (y : F) ≠ 0 := (map_ne_zero (p.valuation F)).mpr y.ne_zero
  simp only [order, Units.val_mul, map_mul, WithZero.log_mul hx hy]
  omega
 theorem order_U (A : SArithmeticData F) (u : A.U)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p ∉ A.Sf) : order p u.val = 0 := by
  have hv : p.valuation F (u.val : F) = 1 := u.property p hp
  simp only [order, hv, WithZero.log_one, neg_zero]
 theorem exp_zero (p : HeightOneSpectrum (𝓞 F)) (I J : Ideal (𝓞 F))
    (hp : p ∈ support I) (hIJ : I ⊔ J = ⊤) : idealPrimeExponent p.asIdeal J = 0 := by
  apply Multiset.count_eq_zero.mpr
  intro hj
  have hi : p.asIdeal ∈ normalizedFactors I := by
    have hh : p.asIdeal ∈ (normalizedFactors I).toFinset := by
      change p.asIdeal ∈ idealPrimeSupport I
      exact Finset.mem_preimage.mp hp
    exact Multiset.mem_toFinset.mp hh
  have hI : I ≤ p.asIdeal := Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hi)
  have hJ : J ≤ p.asIdeal := Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hj)
  have : (⊤ : Ideal (𝓞 F)) ≤ p.asIdeal := by rw [← hIJ]; exact sup_le hI hJ
  exact p.isPrime.ne_top (top_le_iff.mp this)

def freeze (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b) : Frozen A := by
  refine {
    h := D.h
    powerful := D.powerful
    f := b.f
    f_squarefree := b.squarefree
    f_divides_radical := b.divides_radical
    mandatory := ?_
    a := v.a
    a_supported := v.a_supported
    a_exponents := v.a_exponents
    n := v.n
    n_f_coprime := ?_
    epsilon := v.epsilon }
  · intro p hp hn
    apply b.mandatory p hp
    have he : order p (ThetaReflectionData.rowUnit A m) =
        (idealPrimeExponent p.asIdeal D.h.val : ℤ) := by
      rw [D.row_eq, order_mul, order_U A D.epsilon p (support_outside A D.h p hp), zero_add]
      rw [generator_order A G D.rowIdeal ⟨p, support_outside A D.h p hp⟩]
      rw [D.factorization]
      simp only [idealPrimeExponent, normalizedFactors_mul D.h.property.1 D.d.property.1,
        Multiset.count_add]
      rw [show (normalizedFactors D.d.val).count p.asIdeal = 0 from exp_zero p D.h.val D.d.val hp D.coprime]
      simp
    intro hz
    have hz' := congrArg Fin.val hz
    simp only [rowIndex, Fin.val_zero, he, Int.natCast_mod, Int.toNat_natCast] at hz'
    exact hn hz'
  · have hle : v.c.val * v.n.val ⊔ D.d.val * b.f.val ≤ v.n.val ⊔ b.f.val :=
      sup_le_sup Ideal.mul_le_right Ideal.mul_le_right
    exact top_le_iff.mp (v.coprime.ge.trans hle)

def idealSymbol (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (x : Fˣ) : ℂ :=
  ∏ p : {p // p ∈ support I.val}, symbol A σ (supportPrime A I p) x

def SquarefreeGeneratorReciprocity (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) : Prop :=
  ∀ d c : A.Exterior, Squarefree d.val → Squarefree c.val → d.val ⊔ c.val = ⊤ →
    idealSymbol A σ d (G.generator c) = idealSymbol A σ c (G.generator d)

def quadraticPairing (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (d c : A.Exterior) : ℂ :=
  if d.val ⊔ c.val = ⊤ then idealSymbol A σ d (G.generator c) ^ 3 else 0

def mixedPhase (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (d c : A.Exterior) : ℂ :=
  idealSymbol A σ d (G.generator c) *
    idealSymbol A σ c (G.generator d) ^ (-4 : ℤ)

def primePairPhase (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (d c : A.Exterior) : ℂ :=
  ∏ p : {p // p ∈ support d.val},
    ∏ q : {q // q ∈ support c.val},
      symbol A σ (supportPrime A d p) (G.generator (primeIdeal A (supportPrime A c q))) *
      symbol A σ (supportPrime A c q) (G.generator (primeIdeal A (supportPrime A d p))) ^
        (-4 : ℤ)

private theorem symbol_six (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ExteriorPrime A) (x : Fˣ) (hx : order p.val x = 0) :
    symbol A σ p x ^ 6 = 1 := by
  have ht : unitResidue p.val x ≠ 0 := unitResidue_ne_zero p.val x hx
  let t := (isUnit_iff_ne_zero.mpr ht).unit
  have hχ : (residueCharacter A σ p) ^ 6 = 1 := by
    have ho := DHCubic.orderOf_normalizedSextic_complex F A p.val p.property σ _
      (DHCubic.existsUnique_normalizedSextic F A p.val p.property).exists.choose_spec
    have hh := pow_orderOf_eq_one (residueCharacter A σ p)
    rw [show orderOf (residueCharacter A σ p) = 6 from ho] at hh
    exact hh
  have hh := congrArg (fun χ : MulChar (DHCubic.Residue F p.val) ℂ => χ t.val) hχ
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe] at hh
  simpa [symbol, t] using hh
theorem idealSymbol_pow_six_of_coprime (A : SArithmeticData F) (G : AllowedRecipe A) (σ : F →+* ℂ)
    (d c : A.Exterior) (hdc : d.val ⊔ c.val = ⊤) :
    idealSymbol A σ d (G.generator c) ^ 6 = 1 := by
  unfold idealSymbol
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro p _
  apply symbol_six A σ _ _
  rw [generator_order A G c (supportPrime A d p)]
  change (idealPrimeExponent p.val.asIdeal c.val : ℤ) = 0
  apply Int.natCast_eq_zero.mpr
  apply Multiset.count_eq_zero.mpr
  intro hj
  have hi : p.val.asIdeal ∈ normalizedFactors d.val := by
    have hh : p.val.asIdeal ∈ (normalizedFactors d.val).toFinset := by
      change p.val.asIdeal ∈ idealPrimeSupport d.val
      exact Finset.mem_preimage.mp p.property
    exact Multiset.mem_toFinset.mp hh
  have hI : d.val ≤ p.val.asIdeal := Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hi)
  have hJ : c.val ≤ p.val.asIdeal := Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hj)
  have : (⊤ : Ideal (𝓞 F)) ≤ p.val.asIdeal := by
    calc ⊤ = d.val ⊔ c.val := hdc.symm
         _ ≤ p.val.asIdeal := sup_le hI hJ
  exact p.val.isPrime.ne_top (top_le_iff.mp this)

theorem mixedPhase_eq_quadraticPairing_squarefree (A : SArithmeticData F) (G : AllowedRecipe A) (σ : F →+* ℂ)
    (hrec : SquarefreeGeneratorReciprocity A G σ) (d c : A.Exterior)
    (hd : Squarefree d.val) (hc : Squarefree c.val) (hdc : d.val ⊔ c.val = ⊤) :
    mixedPhase A G σ d c = quadraticPairing A G σ d c := by
  have h6 := idealSymbol_pow_six_of_coprime A G σ d c hdc
  have hrec' := hrec d c hd hc hdc
  simp only [mixedPhase, quadraticPairing, if_pos hdc, ← hrec']
  have hx : idealSymbol A σ d (G.generator c) ≠ 0 := by
    intro h
    simpa only [h, zero_pow (by decide : 6 ≠ 0), zero_ne_one] using h6
  simp only [zpow_neg, zpow_ofNat]
  apply (mul_inv_eq_iff_eq_mul₀ (pow_ne_zero 4 hx)).mpr
  have hh : idealSymbol A σ d (G.generator c) ^ 3 * idealSymbol A σ d (G.generator c) ^ 4 =
      idealSymbol A σ d (G.generator c) := by
    calc _ = idealSymbol A σ d (G.generator c) * idealSymbol A σ d (G.generator c) ^ 6 := by ring
         _ = _ := by rw [h6, mul_one]
  exact hh.symm

private theorem order_inv (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : order p x⁻¹ = - order p x := by
  simp only [order, Units.val_inv_eq_inv_val, map_inv₀, WithZero.log_inv]
private theorem separation_order_mul (p : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) : order p (x*y) = order p x + order p y := by
  simp only [order, Units.val_mul, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero) ((Valuation.ne_zero_iff _).mpr y.ne_zero), neg_add]
theorem allowed_class_cocycle (A : SArithmeticData F) (G : AllowedRecipe A) (x y : Fˣ)
    (hx : ThetaReflectionData.rationalClass A x ∈ G.B)
    (hy : ThetaReflectionData.rationalClass A y ∈ G.B)
    (hord : ∀ p : ExteriorPrime A, order p.val x = order p.val y) :
    x / y ∈ ThetaReflectionData.rationalGamma A := by
  have hu : x / y ∈ A.U := by
    intro p hp
    have ho : order p (x/y) = 0 := by
      rw [div_eq_mul_inv, separation_order_mul, order_inv, hord ⟨p, hp⟩, add_neg_cancel]
    have hl : WithZero.log (p.valuation F ((x/y : Fˣ) : F)) = 0 := by
      change -(WithZero.log (p.valuation F ((x/y : Fˣ) : F))) = 0 at ho
      exact neg_eq_zero.mp ho
    have hn : p.valuation F ((x/y : Fˣ) : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr (x/y).ne_zero
    calc p.valuation F ((x/y : Fˣ) : F) = WithZero.exp (WithZero.log (p.valuation F ((x/y : Fˣ) : F))) := (WithZero.exp_log hn).symm
         _ = 1 := by rw [hl, WithZero.exp_zero]
  have hB : ThetaReflectionData.rationalClass A (x/y) ∈ G.B := by
    rw [map_div]
    exact G.B.div_mem hx hy
  have hE : ThetaReflectionData.rationalClass A (x/y) ∈ A.E := by
    exact ⟨A.diagonal (x/y), ⟨x/y, hu, rfl⟩, rfl⟩
  have hk : x/y ∈ (ThetaReflectionData.rationalClass A).ker := by
    change ThetaReflectionData.rationalClass A (x/y) = 1
    apply Subgroup.mem_bot.mp
    rw [← G.complement.disjoint.eq_bot]
    exact ⟨hE, hB⟩
  rw [← G.unit_kernel]
  exact ⟨hu, hk⟩
private theorem order_prod {ι : Type*} (s : Finset ι) (f : ι → Fˣ) (p : HeightOneSpectrum (𝓞 F)) : order p (∏ i ∈ s, f i) = ∑ i ∈ s, order p (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [order]
  | @insert a s ha ih => simp only [Finset.prod_insert ha, Finset.sum_insert ha, separation_order_mul, ih]
private theorem sf_exponent (A : SArithmeticData F) (c : A.Exterior) (hc : Squarefree c.val) (p : HeightOneSpectrum (𝓞 F)) :
    idealPrimeExponent p.asIdeal c.val = if p ∈ support c.val then 1 else 0 := by
  have hn := (squarefree_iff_nodup_normalizedFactors c.property.1).mp hc
  unfold idealPrimeExponent
  by_cases hp : p ∈ support c.val
  · rw [if_pos hp]
    apply Multiset.count_eq_one_of_mem hn
    have h : p.asIdeal ∈ (normalizedFactors c.val).toFinset := Finset.mem_preimage.mp hp
    exact Multiset.mem_toFinset.mp h
  · rw [if_neg hp]
    apply Multiset.count_eq_zero.mpr
    intro h
    apply hp
    exact Finset.mem_preimage.mpr (Multiset.mem_toFinset.mpr h)
private theorem prime_generators_order (A : SArithmeticData F) (G : AllowedRecipe A) (c : A.Exterior) (hc : Squarefree c.val) (p : ExteriorPrime A) :
    order p.val (∏ q : {q // q ∈ support c.val}, G.generator (primeIdeal A (supportPrime A c q))) = order p.val (G.generator c) := by
  rw [order_prod, generator_order A G c p]
  simp_rw [generator_order A G]
  change (∑ q : {q // q ∈ support c.val},
    (idealPrimeExponent p.val.asIdeal q.val.asIdeal : ℤ)) =
    (idealPrimeExponent p.val.asIdeal c.val : ℤ)
  rw [sf_exponent A c hc p.val]
  have hexp (q : HeightOneSpectrum (𝓞 F)) : idealPrimeExponent p.val.asIdeal q.asIdeal = if p.val = q then 1 else 0 := by
    simp only [idealPrimeExponent, normalizedFactors_irreducible q.irreducible, Multiset.count_singleton,
      normalize_eq]
    have hh : (p.val.asIdeal = q.asIdeal) ↔ p.val = q := ⟨fun h => HeightOneSpectrum.asIdeal_injective h, fun h => congrArg HeightOneSpectrum.asIdeal h⟩
    simp only [hh]
  simp_rw [hexp]
  simp only [apply_ite (fun n : ℕ => (n : ℤ)), Int.natCast_one, Int.natCast_zero]
  by_cases hp : p.val ∈ support c.val
  · rw [if_pos hp]
    have heq : (fun q : {q // q ∈ support c.val} => if p.val = q.val then (1 : ℤ) else 0) =
        (fun q => if (⟨p.val, hp⟩ : {q // q ∈ support c.val}) = q then (1 : ℤ) else 0) := by
      funext q
      simp only [Subtype.ext_iff]
    rw [heq]
    simp
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg (by intro he; exact hp (he ▸ q.property))]
theorem prime_generators_cocycle (A : SArithmeticData F) (G : AllowedRecipe A) (c : A.Exterior) (hc : Squarefree c.val) :
    (∏ q : {q // q ∈ support c.val}, G.generator (primeIdeal A (supportPrime A c q))) / G.generator c ∈ ThetaReflectionData.rationalGamma A := by
  apply allowed_class_cocycle A G
  · rw [map_prod]
    exact @Subgroup.prod_mem A.V _ G.B {q // q ∈ support c.val} Finset.univ
      (fun q => ThetaReflectionData.rationalClass A (G.generator (primeIdeal A (supportPrime A c q))))
      (fun q _ => G.allowed (primeIdeal A (supportPrime A c q)))
  · exact G.allowed c
  · exact prime_generators_order A G c hc

private theorem residue_spec (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ)
    (hx : order p x = 0) : IsUnitResidue p x (unitResidue p x) := by
  simpa only [unitResidue, dif_pos hx] using
    (existsUnique_unitResidue p x hx).exists.choose_spec

private theorem residue_mul (p : HeightOneSpectrum (𝓞 F)) (x y : Fˣ)
    (hx : order p x = 0) (hy : order p y = 0) :
    unitResidue p (x*y) = unitResidue p x * unitResidue p y := by
  have hxy : order p (x*y) = 0 := by rw [order_mul, hx, hy, add_zero]
  apply ((existsUnique_unitResidue p (x*y) hxy).unique (residue_spec p (x*y) hxy) ?_)
  obtain ⟨a,b,ha,hb,he,ht⟩ := residue_spec p x hx
  obtain ⟨c,d,hc,hd,hf,hu⟩ := residue_spec p y hy
  refine ⟨a*c,b*d, p.isPrime.mul_notMem ha hc, p.isPrime.mul_notMem hb hd, ?_, ?_⟩
  · simp only [Units.val_mul, he, hf, map_mul]
    ring
  · simp only [ht, hu, map_mul]
    ring

private theorem symbol_mul_units (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ExteriorPrime A) (x y : Fˣ) (hx : order p.val x = 0) (hy : order p.val y = 0) :
    symbol A σ p (x*y) = symbol A σ p x * symbol A σ p y := by
  simp only [symbol, residue_mul p.val x y hx hy, map_mul]

private theorem symbol_one (A : SArithmeticData F) (σ : F →+* ℂ) (p : ExteriorPrime A) :
    symbol A σ p 1 = 1 := by
  have h : unitResidue p.val 1 = 1 := by
    apply (existsUnique_unitResidue p.val 1 (by simp [order])).unique
      (residue_spec p.val 1 (by simp [order]))
    exact ⟨1,1, p.val.isPrime.one_notMem, p.val.isPrime.one_notMem, by simp, by simp⟩
  simp only [symbol, h, map_one]

private theorem order_pow (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ) (n : ℕ) :
    order p (x^n) = n * order p x := by
  induction n with
  | zero => simp [order]
  | succ n ih => rw [pow_succ, order_mul, ih]; push_cast; ring

private theorem symbol_pow_units (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ExteriorPrime A) (x : Fˣ) (hx : order p.val x = 0) (n : ℕ) :
    symbol A σ p (x^n) = symbol A σ p x ^ n := by
  induction n with
  | zero => simp [symbol_one]
  | succ n ih => rw [pow_succ, symbol_mul_units A σ p _ _ (by rw [order_pow, hx, mul_zero]) hx, ih, pow_succ]

private theorem symbol_eq_of_gamma (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ExteriorPrime A) (x y : Fˣ) (hy : order p.val y = 0)
    (h : x/y ∈ ThetaReflectionData.rationalGamma A) : symbol A σ p x = symbol A σ p y := by
  obtain ⟨u,hu,he⟩ := h
  change u^6 = x/y at he
  have ho := order_U A ⟨u,hu⟩ p.val p.property
  have hx : x = u^6*y := by rw [he, div_mul_cancel]
  rw [hx, symbol_mul_units A σ p _ _ (by rw [order_pow, ho, mul_zero]) hy,
    symbol_pow_units A σ p u ho, symbol_six A σ p u ho, one_mul]

private theorem symbol_prod_units (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ExteriorPrime A) {ι : Type*} (s : Finset ι) (f : ι → Fˣ)
    (hf : ∀ i ∈ s, order p.val (f i) = 0) :
    symbol A σ p (∏ i ∈ s, f i) = ∏ i ∈ s, symbol A σ p (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [symbol_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      symbol_mul_units A σ p _ _ (hf a (Finset.mem_insert_self _ _))
        (by rw [order_prod]; exact Finset.sum_eq_zero (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

private theorem symbol_prime_product (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (d c : A.Exterior) (hc : Squarefree c.val)
    (hdc : d.val ⊔ c.val = ⊤) (p : {p // p ∈ support d.val}) :
    (∏ q : {q // q ∈ support c.val},
      symbol A σ (supportPrime A d p) (G.generator (primeIdeal A (supportPrime A c q)))) =
    symbol A σ (supportPrime A d p) (G.generator c) := by
  have ho : order (supportPrime A d p).val (G.generator c) = 0 := by
    rw [generator_order A G c (supportPrime A d p)]
    exact_mod_cast exp_zero p.val d.val c.val p.property hdc
  rw [← symbol_prod_units A σ (supportPrime A d p) Finset.univ _ (by
    intro q _
    rw [generator_order A G]
    change (idealPrimeExponent p.val.asIdeal q.val.asIdeal : ℤ) = 0
    have hq : q.val.asIdeal ∣ c.val := dvd_of_mem_normalizedFactors
      (Multiset.mem_toFinset.mp (Finset.mem_preimage.mp q.property))
    have hcop : d.val ⊔ q.val.asIdeal = ⊤ := top_le_iff.mp
      (hdc.ge.trans (sup_le_sup_left (Ideal.dvd_iff_le.mp hq) _))
    exact_mod_cast exp_zero p.val d.val q.val.asIdeal p.property hcop)]
  exact symbol_eq_of_gamma A σ _ _ _ ho (prime_generators_cocycle A G c hc)

theorem mixed_phase_exact_squarefree (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (hrec : SquarefreeGeneratorReciprocity A G σ)
    (d c : A.Exterior) (hd : Squarefree d.val) (hc : Squarefree c.val)
    (hdc : d.val ⊔ c.val = ⊤) :
    primePairPhase A G σ d c = mixedPhase A G σ d c ∧
    mixedPhase A G σ d c = quadraticPairing A G σ d c := by
  refine ⟨?_, mixedPhase_eq_quadraticPairing_squarefree A G σ hrec d c hd hc hdc⟩
  unfold primePairPhase mixedPhase idealSymbol
  simp_rw [Finset.prod_mul_distrib]
  congr 1
  · apply Finset.prod_congr rfl
    intro p _
    exact symbol_prime_product A G σ d c hc hdc p
  · rw [Finset.prod_comm]
    simp_rw [Finset.prod_zpow]
    congr 1
    apply Finset.prod_congr rfl
    intro q _
    exact symbol_prime_product A G σ c d hd (by simpa [sup_comm] using hdc) q

def frozenArgument (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (T : Frozen A) (p : ExteriorPrime A) : Fˣ :=
  (U.representative T.epsilon).val *
    (G.generator T.a / G.generator (primeIdeal A p) ^
      idealPrimeExponent p.val.asIdeal T.a.val) *
    G.generator T.n ^ 3 * (G.generator T.f / G.generator (primeIdeal A p)) ^ (-2 : ℤ)

def omega (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (T : Frozen A) : ℂ :=
  (∏ p ∈ support T.h.val \ support T.f.val, (1 - (idealNorm p.asIdeal : ℂ)⁻¹)) *
    (L ((U.representative T.epsilon).val * G.generator T.a * G.generator T.n ^ 3 *
      G.generator T.f ^ (-2 : ℤ)))⁻¹ *
    (∏ p : {p // p ∈ support T.f.val},
      scalar A σ ψ (supportPrime A T.f p) (powerfulIndex A T p.val)
        (idealPrimeExponent p.val.asIdeal T.a.val) *
      symbol A σ (supportPrime A T.f p) (frozenArgument A G U T (supportPrime A T.f p)) ^
        phaseExponent (powerfulIndex A T p.val) (idealPrimeExponent p.val.asIdeal T.a.val))

def rho (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (T : Frozen A) (d : A.Exterior) : ℂ :=
  L (G.generator d) ^ 2 *
    (∏ p : {p // p ∈ support d.val},
      omegaScalar A σ ψ (supportPrime A d p) *
      symbol A σ (supportPrime A d p)
        ((U.representative T.epsilon).val * G.generator T.a * G.generator T.n ^ 3 *
          (G.generator d / G.generator (primeIdeal A (supportPrime A d p))) ^ (-2 : ℤ) *
          G.generator T.f ^ (-2 : ℤ))) *
    (∏ p : {p // p ∈ support T.f.val},
      symbol A σ (supportPrime A T.f p) (G.generator d) ^
        (-2 * (phaseExponent (powerfulIndex A T p.val)
          (idealPrimeExponent p.val.asIdeal T.a.val) : ℤ)))

def lambda (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (T : Frozen A) (c : A.Exterior) : ℂ :=
  (L (G.generator c))⁻¹ *
    (∏ p : {p // p ∈ support T.f.val},
      symbol A σ (supportPrime A T.f p) (G.generator c) ^
        phaseExponent (powerfulIndex A T p.val) (idealPrimeExponent p.val.asIdeal T.a.val)) *
    (∏ q : {q // q ∈ support c.val},
      gaussTwo A σ ψ (supportPrime A c q) *
      symbol A σ (supportPrime A c q)
        ((U.representative T.epsilon).val * G.generator T.a *
          (G.generator c / G.generator (primeIdeal A (supportPrime A c q))) *
          G.generator T.f ^ (-2 : ℤ)) ^ 2)

def rowMask (A : SArithmeticData F) (T : Frozen A) (d : A.Exterior) : ℂ :=
  if d.val ⊔ (T.h.val * T.n.val) = ⊤ then 1 else 0

def columnMask (A : SArithmeticData F) (T : Frozen A) (c : A.Exterior) : ℂ :=
  if c.val ⊔ T.f.val = ⊤ then 1 else 0

def separatedCoefficient (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (T : Frozen A) (d c : A.Exterior) : ℂ :=
  rowMask A T d * columnMask A T c * omega A G U σ ψ L T *
    rho A G U σ ψ L T d * lambda A G U σ ψ L T c * quadraticPairing A G σ d c /
      ((Real.sqrt (A.exteriorNorm c) : ℂ) * (A.exteriorNorm T.n : ℂ))

def omegaMajorant (A : SArithmeticData F) (T : Frozen A) : ℝ :=
  ∏ p ∈ support T.f.val, betaLocal (idealNorm p.asIdeal)
    (idealPrimeExponent p.asIdeal T.a.val)

private theorem red_sextic_primitive (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal (A.primitive_zeta12.toInteger ^ 2)) 6 := by
  let r := Ideal.Quotient.mk v.asIdeal
  let z := A.primitive_zeta12.toInteger ^ 2
  have hp : IsPrimitiveRoot z 6 := A.primitive_zeta12.toInteger_isPrimitiveRoot.pow
    (by decide) (by decide : 12 = 2 * 6)
  have h6 : (6 : DHCubic.Residue F v) ≠ 0 := by
    intro h
    apply hv
    apply A.above_six v
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using h)
  have h2 : (2 : DHCubic.Residue F v) ≠ 0 := by
    intro h
    apply h6
    linear_combination 3 * h
  have h3 : (3 : DHCubic.Residue F v) ≠ 0 := by
    intro h
    apply h6
    linear_combination 2 * h
  have hc : z ^ 3 = -1 := (hp.pow (by decide) (by decide : 6 = 3 * 2)).eq_neg_one_of_two_right
  have hr3 : IsPrimitiveRoot ((r z) ^ 3) 2 := by
    rw [← map_pow, hc, map_neg, map_one]
    apply (IsPrimitiveRoot.iff (by decide : 0 < 2)).mpr
    refine ⟨by simp, ?_⟩
    intro l hl hlt
    have : l = 1 := by omega
    subst l
    intro h
    apply h2
    simp only [pow_one] at h
    linear_combination -h
  have hr2 : IsPrimitiveRoot ((r z) ^ 2) 3 := by
    have hp2 := hp.pow (by decide) (by decide : 6 = 2 * 3)
    have hpow : ((r z) ^ 2) ^ 3 = 1 := by rw [← map_pow, ← map_pow, hp2.pow_eq_one, map_one]
    have hne : (r z) ^ 2 ≠ 1 := by
      intro h
      have hg := congrArg r (hp2.geom_sum_eq_zero (by decide : 1 < 3))
      simp [Finset.sum_range_succ, map_add, map_pow, h] at hg
      exact h3 (by linear_combination hg)
    exact isPrimitiveRoot_of_mem_nthRootsFinset (by decide : Nat.Prime 3)
      ((Polynomial.mem_nthRootsFinset (by decide : 0 < 3) 1).mpr hpow) hne
  apply (IsPrimitiveRoot.iff_def _ _).mpr
  refine ⟨by rw [← map_pow, hp.pow_eq_one, map_one], ?_⟩
  intro l hl
  have hd2 : 2 ∣ l := hr3.dvd_of_pow_eq_one l (by rw [pow_right_comm, hl, one_pow])
  have hd3 : 3 ∣ l := hr2.dvd_of_pow_eq_one l (by rw [pow_right_comm, hl, one_pow])
  exact Nat.lcm_dvd hd2 hd3

private theorem residue_six_dvd (A : SArithmeticData F) (p : ExteriorPrime A) :
    6 ∣ Fintype.card (DHCubic.Residue F p.val) - 1 := by
  have hp := red_sextic_primitive F A p.val p.property
  exact hp.dvd_of_pow_eq_one _ (FiniteField.pow_card_sub_one_eq_one _ (hp.ne_zero (by decide)))

private theorem residue_coprime (A : SArithmeticData F) (p : ExteriorPrime A) :
    Nat.Coprime (Fintype.card (DHCubic.Residue F p.val)) 6 := by
  obtain ⟨n, hn⟩ := residue_six_dvd A p
  have hc := Fintype.one_lt_card (α := DHCubic.Residue F p.val)
  have he : Fintype.card (DHCubic.Residue F p.val) = 6*n + 1 := by omega
  rw [he, Nat.coprime_comm]
  simp

set_option maxHeartbeats 800000 in
private theorem residue_order (A : SArithmeticData F) (σ : F →+* ℂ) (p : ExteriorPrime A) :
    orderOf (residueCharacter A σ p) = 6 := by
  let χ := (DHCubic.existsUnique_normalizedSextic F A p.val p.property).exists.choose
  have hn : DHCubic.IsNormalizedSextic F A p.val χ :=
    (DHCubic.existsUnique_normalizedSextic F A p.val p.property).exists.choose_spec
  have h6 : χ ^ 6 = 1 := by
    apply MulChar.ext
    intro x
    obtain ⟨⟨j, hj, he⟩, _⟩ := hn x x.ne_zero
    rw [χ.pow_apply_coe, he, ← pow_mul]
    have he' : 2*j*6 = 12*j := by ring
    rw [he', pow_mul, A.primitive_zeta12.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    simp
  have hleft : orderOf χ ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr h6
  have hright : 6 ∣ orderOf χ := by
    let n := (Fintype.card (DHCubic.Residue F p.val) - 1) / 6
    have hn6 : n * 6 = Fintype.card (DHCubic.Residue F p.val) - 1 :=
      Nat.div_mul_cancel (residue_six_dvd A p)
    have hn0 : 0 < n := by
      have hc := Fintype.one_lt_card (α := DHCubic.Residue F p.val)
      omega
    have hpow : ∀ x : (DHCubic.Residue F p.val)ˣ, x ^ (n * orderOf χ) = 1 := by
      intro x
      apply Units.ext
      have hc : χ x ^ orderOf χ = 1 := by
        simpa only [χ.pow_apply_coe, MulChar.one_apply_coe] using
          congrArg (fun f : MulChar (DHCubic.Residue F p.val) (𝓞 F) => f x) (pow_orderOf_eq_one χ)
      have hr := congrArg (Ideal.Quotient.mk p.val.asIdeal) hc
      rw [map_pow, map_one, (hn x x.ne_zero).2, ← pow_mul] at hr
      exact hr
    have hd := (FiniteField.forall_pow_eq_one_iff (DHCubic.Residue F p.val) _).mp hpow
    rw [← hn6] at hd
    exact Nat.dvd_of_mul_dvd_mul_left hn0 hd
  have hc : orderOf χ = 6 := Nat.dvd_antisymm hleft hright
  have hi : Function.Injective (σ.comp (algebraMap (𝓞 F) F)) :=
    σ.injective.comp NumberField.RingOfIntegers.coe_injective
  exact (orderOf_injective (MulChar.ringHomCompHom (σ.comp (algebraMap (𝓞 F) F)))
    (MulChar.injective_ringHomComp hi) χ).trans hc

private theorem symbol_norm_le (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ExteriorPrime A) (x : Fˣ) : ‖symbol A σ p x‖ ≤ 1 := by
  unfold symbol
  by_cases hx : unitResidue p.val x = 0
  · simpa [hx, MulChar.map_zero] using (show (0 : ℝ) ≤ 1 by norm_num)
  · let u := (isUnit_iff_ne_zero.mpr hx).unit
    have h := Complex.norm_eq_one_of_mem_rootsOfUnity
      ((residueCharacter A σ p).apply_mem_rootsOfUnity u)
    exact le_of_eq (by simpa [MulChar.coe_equivToUnitHom, u] using h)

private theorem symbol_zpow_norm_le (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ExteriorPrime A) (x : Fˣ) (z : ℤ) : ‖symbol A σ p x ^ z‖ ≤ 1 := by
  by_cases hx : symbol A σ p x = 0
  · rw [hx]
    by_cases hz : z = 0
    · simp [hz]
    · simp only [zero_zpow _ hz, norm_zero]; norm_num
  · have hr : unitResidue p.val x ≠ 0 := by
      intro h; apply hx; simp [symbol, h, MulChar.map_zero]
    let u := (isUnit_iff_ne_zero.mpr hr).unit
    have h := Complex.norm_eq_one_of_mem_rootsOfUnity
      ((residueCharacter A σ p).apply_mem_rootsOfUnity u)
    have hn : ‖symbol A σ p x‖ = 1 := by
      simpa [symbol, MulChar.coe_equivToUnitHom, u] using h
    simp [norm_zpow, hn]

private theorem gauss_norm {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card k : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hn := congrArg norm h
  rw [norm_mul, norm_star, Complex.norm_natCast] at hn
  nlinarith [Real.sq_sqrt (show 0 ≤ (Fintype.card k : ℝ) by positivity),
    norm_nonneg (gaussSum χ ψ), Real.sqrt_nonneg (Fintype.card k : ℝ)]

theorem norm_gaussTwo (A : SArithmeticData F) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p, (ψ p).IsPrimitive) (p : ExteriorPrime A) :
    ‖gaussTwo A σ ψ p‖ = 1 := by
  have hn : (residueCharacter A σ p) ^ 2 ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by norm_num) (by rw [residue_order]; norm_num)
  have hpos : 0 < Real.sqrt (Fintype.card (DHCubic.Residue F p.val) : ℝ) :=
    Real.sqrt_pos.mpr (by positivity)
  simp only [gaussTwo, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), gauss_norm _ _ hn (hψ p)]
  exact inv_mul_cancel₀ hpos.ne'

private theorem digit_scalar_norm_le {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (hχ : orderOf χ = 6)
    (hψ : ψ.IsPrimitive) (hQ : Nat.Coprime (Fintype.card k) 6)
    (j : Fin 6) (e : ℕ) :
    ‖sexticReflectedNonzeroDigits χ ψ j (e : ℤ) 1‖ ≤ betaLocal (Fintype.card k) e := by
  by_cases he : e = 0
  · subst e
    norm_num only [Nat.cast_zero, Int.cast_zero]
    rw [sexticReflectedNonzeroDigits_depth_zero χ ψ hχ hψ hQ _ _ one_ne_zero]
    simpa [betaLocal_zero] using sexticReflectedDepthZeroScalar_norm_le χ ψ hχ hψ hQ j
  have he0 : (0 : ℤ) < e := by omega
  have hQ2 : (2 : ℝ) ≤ Fintype.card k := by exact_mod_cast Fintype.one_lt_card
  have hQ0 : (0 : ℝ) < Fintype.card k := by positivity
  by_cases hj : j.val = 4
  · have hj' : j = 4 := Fin.ext hj
    subst j
    rw [sexticReflectedNonzeroDigits_positive χ ψ hχ hψ hQ _ he0 _ one_ne_zero]
    simp only [map_one, one_zpow, mul_one, norm_div, norm_mul,
      sexticMaskGaussSum_norm χ ψ hχ hψ hQ 4 (by norm_num)]
    have hsub : ‖(Fintype.card k : ℂ) - 1‖ = (Fintype.card k : ℝ) - 1 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [hsub]
    have hg : ‖gaussSum (χ ^ 2) ψ‖ = Real.sqrt (Fintype.card k : ℝ) :=
      gauss_norm _ _ (pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hχ]; norm_num)) hψ
    have hp : ‖(Fintype.card k : ℂ) ^ (-((e : ℤ) / 3))‖ =
        (Fintype.card k : ℝ).rpow (-(e / 3 : ℕ) : ℝ) := by
      rw [norm_zpow, Complex.norm_natCast, ← Real.rpow_intCast]
      congr 1
      have hm : ((e : ℤ) / 3) = ((e / 3 : ℕ) : ℤ) := (Int.natCast_ediv e 3).symm
      rw [hm]
      push_cast
      rfl
    have hs : ‖(Real.sqrt (Fintype.card k : ℝ) : ℂ)⁻¹‖ =
        (Real.sqrt (Fintype.card k : ℝ))⁻¹ := by
      simp [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hspos : 0 < Real.sqrt (Fintype.card k : ℝ) := Real.sqrt_pos.mpr hQ0
    have hsq := Real.sq_sqrt hQ0.le
    have hrnon : 0 ≤ (Fintype.card k : ℝ).rpow (-(e / 3 : ℕ) : ℝ) :=
      Real.rpow_nonneg hQ0.le _
    simp only [sexticSphericalCoefficient, if_neg (by omega : ¬(e : ℤ) < 0)]
    by_cases hm0 : e % 3 = 0
    · rw [if_pos (by omega), hp, betaLocal, if_neg he, if_neg (by omega), if_pos hm0]
      have hr : (Fintype.card k : ℝ).rpow ((1/2 : ℝ) - (e / 3 : ℕ)) =
          (Fintype.card k : ℝ).rpow (-(e / 3 : ℕ) : ℝ) * Real.sqrt (Fintype.card k : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        change _ = (Fintype.card k : ℝ).rpow (-(e / 3 : ℕ) : ℝ) *
          (Fintype.card k : ℝ).rpow (1 / 2 : ℝ)
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_add hQ0]
        congr 1; ring
      rw [hr, div_le_iff₀ hspos]
      nlinarith
    · rw [if_neg (by omega)]
      by_cases hm1 : e % 3 = 1
      · rw [if_pos (by omega), norm_mul, norm_mul, norm_mul, hp, hs, hg,
          inv_mul_cancel₀ hspos.ne', mul_one, betaLocal, if_neg he, if_pos hm1]
        rw [div_le_iff₀ hspos]
        have hinv : (Real.sqrt (Fintype.card k : ℝ))⁻¹ * ((Fintype.card k : ℝ) - 1) ≤
            Real.sqrt (Fintype.card k : ℝ) := by
          rw [← div_eq_inv_mul, div_le_iff₀ hspos]
          nlinarith
        nlinarith
      · rw [if_neg (by omega)]
        simp [betaLocal, he, hm0, hm1]
  · rw [sexticReflectedNonzeroDigits_eq_zero χ ψ hχ hψ hQ _ _ _ one_ne_zero
      (Or.inr (Or.inr ⟨he0, hj⟩)), norm_zero]
    exact betaLocal_nonneg _ hQ2 e

private theorem scalar_norm_le (A : SArithmeticData F) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p, (ψ p).IsPrimitive) (p : ExteriorPrime A) (j : Fin 6) (e : ℕ) :
    ‖scalar A σ ψ p j e‖ ≤ betaLocal (idealNorm p.val.asIdeal) e := by
  have hn : idealNorm p.val.asIdeal = (Fintype.card (DHCubic.Residue F p.val) : ℝ) := by
    simp [idealNorm, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [hn]
  exact digit_scalar_norm_le _ _ (residue_order A σ p) (hψ p) (residue_coprime A p) j e

private theorem omegaScalar_norm_le (A : SArithmeticData F) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p, (ψ p).IsPrimitive) (p : ExteriorPrime A) :
    ‖omegaScalar A σ ψ p‖ ≤ 1 := by
  simpa [omegaScalar, betaLocal_zero] using scalar_norm_le A σ ψ hψ p 1 0

private theorem prod_norm_le_one {ι : Type*} [Fintype ι] (f : ι → ℂ)
    (hf : ∀ i, ‖f i‖ ≤ 1) : ‖∏ i, f i‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hf i)

private theorem mul_norm_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a*b‖ ≤ 1 := by
  rw [norm_mul]
  nlinarith [norm_nonneg a, norm_nonneg b]

private theorem pow_norm_le_one {a : ℂ} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a^n‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg a) ha

private theorem rho_bound (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p, (ψ p).IsPrimitive) (L : Fˣ →* ℂ) (hL : ∀ x, ‖L x‖ = 1)
    (T : Frozen A) (d : A.Exterior) : ‖rho A G U σ ψ L T d‖ ≤ 1 := by
  unfold rho
  apply mul_norm_le_one
  · apply mul_norm_le_one
    · simp [norm_pow, hL]
    · apply prod_norm_le_one
      intro p
      apply mul_norm_le_one
      · exact omegaScalar_norm_le A σ ψ hψ _
      · exact symbol_norm_le A σ _ _
  · apply prod_norm_le_one
    intro p
    exact symbol_zpow_norm_le A σ _ _ _

private theorem lambda_bound (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p, (ψ p).IsPrimitive) (L : Fˣ →* ℂ) (hL : ∀ x, ‖L x‖ = 1)
    (T : Frozen A) (c : A.Exterior) : ‖lambda A G U σ ψ L T c‖ ≤ 1 := by
  unfold lambda
  apply mul_norm_le_one
  · apply mul_norm_le_one
    · simp [norm_inv, hL]
    · apply prod_norm_le_one
      intro p
      exact pow_norm_le_one (symbol_norm_le A σ _ _) _
  · apply prod_norm_le_one
    intro p
    apply mul_norm_le_one
    · exact (norm_gaussTwo A σ ψ hψ _).le
    · exact pow_norm_le_one (symbol_norm_le A σ _ _) _

private theorem omega_bound (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p, (ψ p).IsPrimitive) (L : Fˣ →* ℂ) (hL : ∀ x, ‖L x‖ = 1)
    (T : Frozen A) : ‖omega A G U σ ψ L T‖ ≤ omegaMajorant A T := by
  have hinactive : ‖∏ p ∈ support T.h.val \ support T.f.val,
      (1 - (idealNorm p.asIdeal : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    intro p hp
    have hQ := idealNorm_prime_ge_two p.asIdeal p.prime
    have hqi : (idealNorm p.asIdeal)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr (by linarith)
    have hnon : 0 ≤ (idealNorm p.asIdeal)⁻¹ := inv_nonneg.mpr (by linarith)
    rw [← Complex.ofReal_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    linarith
  unfold omega
  rw [norm_mul, norm_mul, norm_inv, hL, inv_one, mul_one]
  have hprod : ‖∏ p : {p // p ∈ support T.f.val},
      scalar A σ ψ (supportPrime A T.f p) (powerfulIndex A T p.val)
        (idealPrimeExponent p.val.asIdeal T.a.val) *
      symbol A σ (supportPrime A T.f p) (frozenArgument A G U T (supportPrime A T.f p)) ^
        phaseExponent (powerfulIndex A T p.val) (idealPrimeExponent p.val.asIdeal T.a.val)‖ ≤
      omegaMajorant A T := by
    rw [norm_prod]
    unfold omegaMajorant
    rw [Finset.prod_subtype (support T.f.val) (fun _ => Iff.rfl)]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro p _
    rw [norm_mul]
    have hs := scalar_norm_le A σ ψ hψ (supportPrime A T.f p)
      (powerfulIndex A T p.val) (idealPrimeExponent p.val.asIdeal T.a.val)
    have hsy := pow_norm_le_one (symbol_norm_le A σ (supportPrime A T.f p)
      (frozenArgument A G U T (supportPrime A T.f p)))
      (phaseExponent (powerfulIndex A T p.val) (idealPrimeExponent p.val.asIdeal T.a.val))
    rw [norm_pow] at hsy ⊢
    change ‖scalar A σ ψ (supportPrime A T.f p) _ _‖ ≤
      betaLocal (idealNorm p.val.asIdeal) _ at hs
    nlinarith [norm_nonneg (scalar A σ ψ (supportPrime A T.f p)
      (powerfulIndex A T p.val) (idealPrimeExponent p.val.asIdeal T.a.val)),
      pow_nonneg (norm_nonneg (symbol A σ (supportPrime A T.f p)
        (frozenArgument A G U T (supportPrime A T.f p))))
        (phaseExponent (powerfulIndex A T p.val) (idealPrimeExponent p.val.asIdeal T.a.val))]
  nlinarith [norm_nonneg (∏ p : {p // p ∈ support T.f.val},
      scalar A σ ψ (supportPrime A T.f p) (powerfulIndex A T p.val)
        (idealPrimeExponent p.val.asIdeal T.a.val) *
      symbol A σ (supportPrime A T.f p) (frozenArgument A G U T (supportPrime A T.f p)) ^
        phaseExponent (powerfulIndex A T p.val) (idealPrimeExponent p.val.asIdeal T.a.val))]

theorem factors_norm_le (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : Fˣ →* ℂ) (hL : ∀ x : Fˣ, ‖L x‖ = 1)
    (T : Frozen A) (d c : A.Exterior) :
    ‖omega A G U σ ψ L T‖ ≤ omegaMajorant A T ∧
    ‖rho A G U σ ψ L T d‖ ≤ 1 ∧ ‖lambda A G U σ ψ L T c‖ ≤ 1 := by
  exact ⟨omega_bound A G U σ ψ hψ L hL T, rho_bound A G U σ ψ hψ L hL T d,
    lambda_bound A G U σ ψ hψ L hL T c⟩

private theorem unitResidue_mul (p : HeightOneSpectrum (𝓞 F)) (x y : Fˣ)
    (hx : order p x = 0) (hy : order p y = 0) :
    unitResidue p (x*y) = unitResidue p x * unitResidue p y := by
  have hxy : order p (x*y) = 0 := by rw [order_mul]; omega
  have htx : IsUnitResidue p x (unitResidue p x) := by
    simpa [unitResidue, hx] using (existsUnique_unitResidue p x hx).exists.choose_spec
  have hty : IsUnitResidue p y (unitResidue p y) := by
    simpa [unitResidue, hy] using (existsUnique_unitResidue p y hy).exists.choose_spec
  obtain ⟨a, b, ha, hb, hxeq, hta⟩ := htx
  obtain ⟨c, d, hc, hd, hyeq, htc⟩ := hty
  have hxyres : IsUnitResidue p (x * y)
      (unitResidue p x * unitResidue p y) := by
    refine ⟨a*c, b*d, ?_, ?_, ?_, ?_⟩
    · exact fun h => (p.isPrime.mem_or_mem h).elim ha hc
    · exact fun h => (p.isPrime.mem_or_mem h).elim hb hd
    · simp only [Units.val_mul, hxeq, hyeq, map_mul]
      ring
    · rw [hta, htc, map_mul, map_mul]
      ring
  exact ((existsUnique_unitResidue p (x * y) hxy).unique
    (by simpa [unitResidue, hxy] using
      (existsUnique_unitResidue p (x*y) hxy).exists.choose_spec) hxyres)

private theorem symbol_mul (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ExteriorPrime A) (x y : Fˣ) (hx : order p.val x = 0)
    (hy : order p.val y = 0) :
    symbol A σ p (x*y) = symbol A σ p x * symbol A σ p y := by
  simp only [symbol, unitResidue_mul p.val x y hx hy, map_mul]

private theorem order_one (p : HeightOneSpectrum (𝓞 F)) : order p (1 : Fˣ) = 0 := by
  simp [ThetaBranch.order]
private theorem order_inv_exact (p : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    order p x⁻¹ = -order p x := by
  have h := order_mul p x x⁻¹
  rw [mul_inv_cancel, order_one] at h
  omega
private theorem symbol_inv (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ExteriorPrime A) (x : Fˣ) (hx : order p.val x = 0) :
    symbol A σ p x⁻¹ = (symbol A σ p x)⁻¹ := by
  have hn : symbol A σ p x ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr (unitResidue_ne_zero p.val x hx))
  have h := symbol_mul A σ p x x⁻¹ hx (by rw [order_inv_exact, hx, neg_zero])
  rw [mul_inv_cancel, symbol_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm
private theorem symbol_pow (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ExteriorPrime A) (x : Fˣ) (n : ℕ) (hx : order p.val x = 0) :
    symbol A σ p (x^n) = symbol A σ p x ^ n := by
  induction n with
  | zero => simp [symbol_one]
  | succ n ih => rw [pow_succ, symbol_mul _ _ _ _ _ (by rw [order_pow,hx,mul_zero]) hx, ih, pow_succ]
private theorem symbol_zpow (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ExteriorPrime A) (x : Fˣ) (z : ℤ) (hx : order p.val x = 0) :
    symbol A σ p (x^z) = symbol A σ p x ^ z := by
  cases z with
  | ofNat n => exact symbol_pow A σ p x n hx
  | negSucc n =>
    rw [zpow_negSucc, symbol_inv _ _ _ _ (by rw [order_pow,hx,mul_zero]), symbol_pow _ _ _ _ _ hx,
      zpow_negSucc]
private theorem coordinate_coprime_d (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b) :
    D.d.val ⊔ v.c.val = ⊤ := by
  have hle : v.c.val*v.n.val ⊔ D.d.val*b.f.val ≤ v.c.val ⊔ D.d.val :=
    sup_le_sup Ideal.mul_le_left Ideal.mul_le_left
  rw [sup_comm]; exact top_le_iff.mp (v.coprime.ge.trans hle)
private theorem coordinate_coprime_f (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b) :
    v.c.val ⊔ b.f.val = ⊤ := by
  have hle : v.c.val*v.n.val ⊔ D.d.val*b.f.val ≤ v.c.val ⊔ b.f.val :=
    sup_le_sup Ideal.mul_le_left Ideal.mul_le_right
  exact top_le_iff.mp (v.coprime.ge.trans hle)
private theorem symbol_generator_unit (A : SArithmeticData F) (G : AllowedRecipe A)
    (I J : A.Exterior) (p : ExteriorPrime A) (hp : p.val ∈ support I.val)
    (hc : I.val ⊔ J.val = ⊤) : order p.val (G.generator J) = 0 := by
  rw [generator_order]
  exact_mod_cast exp_zero p.val I.val J.val hp hc
private theorem d_argument_split (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : {p // p ∈ support D.d.val}) :
    symbol A σ (supportPrime A D.d p) (dArgument A G U m D b v (supportPrime A D.d p)) =
    symbol A σ (supportPrime A D.d p)
      ((U.representative v.epsilon).val * G.generator v.a * G.generator v.n ^ 3 *
        (G.generator D.d / G.generator (primeIdeal A (supportPrime A D.d p))) ^ (-2 : ℤ) *
        G.generator b.f ^ (-2 : ℤ)) *
      symbol A σ (supportPrime A D.d p) (G.generator v.c) := by
  have hc := symbol_generator_unit A G D.d v.c (supportPrime A D.d p) p.property
    (coordinate_coprime_d A G m D b v)
  have he : dArgument A G U m D b v (supportPrime A D.d p) =
      ((U.representative v.epsilon).val * G.generator v.a * G.generator v.n ^ 3 *
        (G.generator D.d / G.generator (primeIdeal A (supportPrime A D.d p))) ^ (-2 : ℤ) *
        G.generator b.f ^ (-2 : ℤ)) * G.generator v.c := by
    unfold dArgument
    ac_rfl
  have hunit := (coefficient_arguments_units A G U m D b v).1 (supportPrime A D.d p) p.property
  rw [he, order_mul, hc, add_zero] at hunit
  rw [he, symbol_mul A σ _ _ _ hunit hc]
private theorem c_argument_split (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : {p // p ∈ support v.c.val}) :
    symbol A σ (supportPrime A v.c p) (cArgument A G U m D b v (supportPrime A v.c p)) ^ 2 =
    symbol A σ (supportPrime A v.c p)
      ((U.representative v.epsilon).val * G.generator v.a *
        (G.generator v.c / G.generator (primeIdeal A (supportPrime A v.c p))) *
        G.generator b.f ^ (-2 : ℤ)) ^ 2 *
      symbol A σ (supportPrime A v.c p) (G.generator D.d) ^ (-4 : ℤ) := by
  have hdc := coordinate_coprime_d A G m D b v
  have hd := symbol_generator_unit A G v.c D.d (supportPrime A v.c p) p.property
    (by rw [sup_comm]; exact hdc)
  have he : cArgument A G U m D b v (supportPrime A v.c p) =
      ((U.representative v.epsilon).val * G.generator v.a *
        (G.generator v.c / G.generator (primeIdeal A (supportPrime A v.c p))) *
        G.generator b.f ^ (-2 : ℤ)) * G.generator D.d ^ (-2 : ℤ) := by
    simp only [cArgument, mul_zpow]
    ac_rfl
  have hd2 : order (supportPrime A v.c p).val (G.generator D.d ^ (-2 : ℤ)) = 0 := by
    simp only [zpow_neg, zpow_ofNat, order_inv, order_pow, hd, mul_zero, neg_zero]
  have hunit := (coefficient_arguments_units A G U m D b v).2.2 (supportPrime A v.c p) p.property
  rw [he, order_mul, hd2, add_zero] at hunit
  rw [he, symbol_mul A σ _ _ _ hunit hd2, symbol_zpow A σ _ _ _ hd, mul_pow]
  congr 1
  rw [← zpow_natCast, ← zpow_mul]
  norm_num

private theorem radical_dvd (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) : idealRadical I ∣ I := by
  have hd := Multiset.toFinset_prod_dvd_prod (normalizedFactors I)
  have he : (normalizedFactors I).prod = I := (associated_iff_eq.mp (prod_normalizedFactors hI))
  rw [he] at hd
  simpa only [idealRadical, idealPrimeSupport, id_eq] using hd
private theorem f_argument_split (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : {p // p ∈ support b.f.val}) (j : Fin 6) :
    symbol A σ (supportPrime A b.f p) (fArgument A G U m D b v (supportPrime A b.f p)) ^
      phaseExponent j (idealPrimeExponent p.val.asIdeal v.a.val) =
    symbol A σ (supportPrime A b.f p)
      (frozenArgument A G U (freeze A G m D b v) (supportPrime A b.f p)) ^
      phaseExponent j (idealPrimeExponent p.val.asIdeal v.a.val) *
    symbol A σ (supportPrime A b.f p) (G.generator D.d) ^
      (-2 * (phaseExponent j (idealPrimeExponent p.val.asIdeal v.a.val) : ℤ)) *
    symbol A σ (supportPrime A b.f p) (G.generator v.c) ^
      phaseExponent j (idealPrimeExponent p.val.asIdeal v.a.val) := by
  have hc := symbol_generator_unit A G b.f v.c (supportPrime A b.f p) p.property
    (by rw [sup_comm]; exact coordinate_coprime_f A G m D b v)
  have hfd : b.f.val ⊔ D.d.val = ⊤ := by
    have hfh : D.h.val ≤ b.f.val := by
      have hrad : idealRadical D.h.val ∣ D.h.val := radical_dvd D.h.val D.h.property.1
      exact Ideal.dvd_iff_le.mp (dvd_trans b.divides_radical hrad)
    exact top_le_iff.mp (D.coprime.ge.trans (sup_le_sup hfh le_rfl))
  have hd := symbol_generator_unit A G b.f D.d (supportPrime A b.f p) p.property hfd
  have hd2 : order (supportPrime A b.f p).val (G.generator D.d ^ (-2 : ℤ)) = 0 := by
    simp only [zpow_neg, zpow_ofNat, order_inv, order_pow, hd, mul_zero, neg_zero]
  have he : fArgument A G U m D b v (supportPrime A b.f p) =
      (frozenArgument A G U (freeze A G m D b v) (supportPrime A b.f p) *
        G.generator D.d ^ (-2 : ℤ)) * G.generator v.c := by
    simp only [fArgument, frozenArgument, freeze]
    ac_rfl
  have hunit := (coefficient_arguments_units A G U m D b v).2.1 (supportPrime A b.f p) p.property
  rw [he, order_mul, order_mul, hd2, hc, add_zero, add_zero] at hunit
  rw [he, symbol_mul A σ _ _ _ (by rw [order_mul,hunit,hd2,zero_add]) hc,
    symbol_mul A σ _ _ _ hunit hd2, symbol_zpow A σ _ _ _ hd, mul_pow, mul_pow]
  congr 2
  rw [← zpow_natCast, ← zpow_mul]
private theorem active_row_index (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b)
    (p : {p // p ∈ support b.f.val}) :
    rowIndex A m p.val = powerfulIndex A (freeze A G m D b v) p.val := by
  have hf : D.h.val ≤ b.f.val := Ideal.dvd_iff_le.mp
    (dvd_trans b.divides_radical (radical_dvd D.h.val D.h.property.1))
  have hfac : p.val.asIdeal ∈ normalizedFactors b.f.val := by
    simpa only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using p.property
  have hp : p.val ∈ support D.h.val := by
    have hdiv : p.val.asIdeal ∣ D.h.val := Ideal.dvd_iff_le.mpr
      (hf.trans (Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hfac)))
    simpa only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using
      (mem_normalizedFactors_iff D.h.property.1).mpr ⟨p.val.prime, hdiv⟩
  have hv : order p.val (ThetaReflectionData.rowUnit A m) =
      (idealPrimeExponent p.val.asIdeal D.h.val : ℤ) := by
    rw [D.row_eq, order_mul, order_U A D.epsilon p.val (support_outside A D.h p.val hp), zero_add,
      generator_order A G D.rowIdeal ⟨p.val,support_outside A D.h p.val hp⟩, D.factorization]
    simp only [idealPrimeExponent, normalizedFactors_mul D.h.property.1 D.d.property.1, Multiset.count_add]
    rw [show (normalizedFactors D.d.val).count p.val.asIdeal = 0 from
      exp_zero p.val D.h.val D.d.val hp D.coprime]
    simp
  apply Fin.ext
  simp only [rowIndex, powerfulIndex, freeze, hv]
  omega
private theorem masks_one (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b) :
    rowMask A (freeze A G m D b v) D.d = 1 ∧
      columnMask A (freeze A G m D b v) v.c = 1 := by
  have hn : D.d.val ⊔ v.n.val = ⊤ := by
    have hle : v.c.val*v.n.val ⊔ D.d.val*b.f.val ≤ v.n.val ⊔ D.d.val :=
      sup_le_sup Ideal.mul_le_right Ideal.mul_le_left
    rw [sup_comm]
    exact top_le_iff.mp (v.coprime.ge.trans hle)
  constructor
  · unfold rowMask freeze
    rw [if_pos]
    exact ((Ideal.isCoprime_iff_sup_eq.mpr (by rw [sup_comm]; exact D.coprime)).mul_right
      (Ideal.isCoprime_iff_sup_eq.mpr hn)).sup_eq
  · change (if v.c.val ⊔ b.f.val = ⊤ then (1:ℂ) else 0) = 1
    rw [if_pos (coordinate_coprime_f A G m D b v)]
set_option maxHeartbeats 3000000 in
private theorem coefficient_split_squarefree (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (hrec : SquarefreeGeneratorReciprocity A G σ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b) :
    exactCoefficient A G U σ ψ m D b v *
      (L (coordinateRepresentative A G U m D b v))⁻¹ =
    separatedCoefficient A G U σ ψ L (freeze A G m D b v) D.d v.c := by
  have hdc := coordinate_coprime_d A G m D b v
  have hm := masks_one A G m D b v
  have hmix := (mixed_phase_exact_squarefree A G σ hrec D.d v.c D.squarefree v.c_squarefree hdc).2
  have hLsplit : (L (coordinateRepresentative A G U m D b v))⁻¹ =
      (L ((U.representative v.epsilon).val * G.generator v.a * G.generator v.n ^ 3 *
        G.generator b.f ^ (-2:ℤ)))⁻¹ * L (G.generator D.d)^2 * (L (G.generator v.c))⁻¹ := by
    simp only [coordinateRepresentative, map_div, map_mul, map_pow, map_zpow, zpow_neg,
      zpow_ofNat, mul_inv, inv_div, inv_pow, inv_inv]
    simp only [map_inv, map_pow, inv_inv]
    ring
  unfold exactCoefficient separatedCoefficient
  rw [hm.1, hm.2]
  simp only [one_mul]
  simp_rw [d_argument_split A G U σ m D b v,
    f_argument_split A G U σ m D b v, c_argument_split A G U σ m D b v,
    active_row_index A G m D b v]
  simp only [omega, rho, lambda, freeze, powerfulIndex]
  rw [hLsplit, ← hmix]
  unfold mixedPhase idealSymbol
  simp only [Finset.prod_mul_distrib, ← Finset.prod_zpow]
  simp only [div_eq_mul_inv, mul_inv, frozenArgument, powerfulIndex, freeze]
  let H := ∏ p ∈ support D.h.val \ support b.f.val, (1 - (idealNorm p.asIdeal : ℂ)⁻¹)
  let O := ∏ p : {p // p ∈ support D.d.val}, omegaScalar A σ ψ (supportPrime A D.d p)
  let R := ∏ p : {p // p ∈ support D.d.val}, symbol A σ (supportPrime A D.d p)
    ((U.representative v.epsilon).val * G.generator v.a * G.generator v.n ^ 3 *
      (G.generator D.d / G.generator (primeIdeal A (supportPrime A D.d p))) ^ (-2:ℤ) *
      G.generator b.f ^ (-2:ℤ))
  let M := ∏ p : {p // p ∈ support D.d.val}, symbol A σ (supportPrime A D.d p) (G.generator v.c)
  let S := ∏ p : {p // p ∈ support b.f.val}, scalar A σ ψ (supportPrime A b.f p)
    (powerfulIndex A (freeze A G m D b v) p.val) (idealPrimeExponent p.val.asIdeal v.a.val)
  let W := ∏ p : {p // p ∈ support b.f.val}, symbol A σ (supportPrime A b.f p)
    (frozenArgument A G U (freeze A G m D b v) (supportPrime A b.f p)) ^
    phaseExponent (powerfulIndex A (freeze A G m D b v) p.val) (idealPrimeExponent p.val.asIdeal v.a.val)
  let P := ∏ p : {p // p ∈ support b.f.val}, symbol A σ (supportPrime A b.f p) (G.generator D.d) ^
    (-2 * (phaseExponent (powerfulIndex A (freeze A G m D b v) p.val)
      (idealPrimeExponent p.val.asIdeal v.a.val) : ℤ))
  let Q := ∏ p : {p // p ∈ support b.f.val}, symbol A σ (supportPrime A b.f p) (G.generator v.c) ^
    phaseExponent (powerfulIndex A (freeze A G m D b v) p.val) (idealPrimeExponent p.val.asIdeal v.a.val)
  let G2 := ∏ p : {p // p ∈ support v.c.val}, gaussTwo A σ ψ (supportPrime A v.c p)
  let C2 := ∏ p : {p // p ∈ support v.c.val}, symbol A σ (supportPrime A v.c p)
    ((U.representative v.epsilon).val * G.generator v.a *
      (G.generator v.c / G.generator (primeIdeal A (supportPrime A v.c p))) *
      G.generator b.f ^ (-2:ℤ)) ^ 2
  let N := ∏ p : {p // p ∈ support v.c.val}, symbol A σ (supportPrime A v.c p) (G.generator D.d) ^ (-4:ℤ)
  let Ll := (L ((U.representative v.epsilon).val * G.generator v.a * G.generator v.n ^ 3 *
      G.generator b.f ^ (-2:ℤ)))⁻¹
  let Ld := L (G.generator D.d)^2
  let Lc := (L (G.generator v.c))⁻¹
  let den := (Real.sqrt (A.exteriorNorm v.c) : ℂ)⁻¹ * (A.exteriorNorm v.n : ℂ)⁻¹
  change H * den * (O * (R * M)) * (S * ((W * P) * Q)) * (G2 * (C2 * N)) *
    (Ll * Ld * Lc) = H * Ll * (S * W) * (Ld * (O * R) * P) *
      ((Lc * Q) * (G2 * C2)) * (M * N) * den
  ring

theorem exact_coefficient_separated_squarefree (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : Fˣ →* ℂ) (hL : ∀ x : Fˣ, ‖L x‖ = 1)
    (hrec : SquarefreeGeneratorReciprocity A G σ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b) :
    exactCoefficient A G U σ ψ m D b v *
      (L (coordinateRepresentative A G U m D b v))⁻¹ =
    separatedCoefficient A G U σ ψ L (freeze A G m D b v) D.d v.c := by
  exact coefficient_split_squarefree A G U σ ψ L hrec m D b v

def profileIndex (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (T : Frozen A) (sd sc : G.B) : A.V :=
  ThetaReflectionData.rationalClass A (U.representative T.epsilon).val *
    ThetaReflectionData.rationalClass A (G.generator T.a) * (sc : A.V) *
    ThetaReflectionData.rationalClass A (G.generator T.n) ^ 3 *
    (sd : A.V) ^ (-2 : ℤ) *
    ThetaReflectionData.rationalClass A (G.generator T.f) ^ (-2 : ℤ)

def profileArgument (A : SArithmeticData F) (T : Frozen A)
    (d c : A.Exterior) (Z : ℝ) : ℝ :=
  Z * A.exteriorNorm T.a * A.exteriorNorm c * A.exteriorNorm T.n ^ 3 /
    (A.exteriorNorm d ^ 2 * A.exteriorNorm T.f ^ 2)

 def normHom (A : SArithmeticData F) : A.G →* ℝ where
  toFun := A.norm
  map_one' := by simp [SArithmeticData.norm]
  map_mul' := by
    intro x y
    simp only [SArithmeticData.norm, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, Units.val_mul,
      norm_mul, mul_pow, Finset.prod_mul_distrib]
    ring
private theorem norm_div (A : SArithmeticData F) (x y : A.G) : A.norm (x / y) = A.norm x / A.norm y := by
  simp [SArithmeticData.norm, div_eq_mul_inv, norm_mul, norm_inv, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_inv_distrib, inv_pow]
  ring
private theorem gen_norm (A : SArithmeticData F) (G : AllowedRecipe A) (I : A.Exterior) :
  A.norm (A.diagonal (G.generator I)) = A.exteriorNorm I := by
  obtain ⟨r, hr, he⟩ := G.generates I
  exact A.generator_norm I r hr (G.generator I) he
private theorem U_norm (A : SArithmeticData F) (u : A.U) :
    A.norm (A.diagonal u.val) = 1 := by
  have h : A.diagonal (u.val ^ 6) ∈ A.Gamma := by
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem (powMonoidHom 6) u.property)
  have h6 : A.norm (A.diagonal u.val) ^ 6 = 1 := by
    have hh : A.norm (A.diagonal (u.val ^ 6)) = 1 := A.Gamma_le_G1 h
    change normHom A (A.diagonal (u.val ^ 6)) = 1 at hh
    have hh' := (show normHom A (A.diagonal u.val) ^ 6 = 1 by
      simpa only [map_pow] using hh)
    exact hh'
  apply (pow_eq_one_iff_of_nonneg _ (by decide : 6 ≠ 0)).mp h6
  dsimp [SArithmeticData.norm]
  positivity

theorem coordinate_class_norm (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (b : Branch A G m D)
    (v : Coordinates A G m D b) (sd sc : G.B)
    (hd : ThetaReflectionData.rationalClass A (G.generator D.d) = (sd : A.V))
    (hc : ThetaReflectionData.rationalClass A (G.generator v.c) = (sc : A.V)) (Z : ℝ) :
    ThetaReflectionData.frequencyClass A (coordinateFrequency A G U m D b v) =
      profileIndex A G U (freeze A G m D b v) sd sc ∧
    Z * ThetaReflectionData.frequencyNorm A (coordinateFrequency A G U m D b v) =
      profileArgument A (freeze A G m D b v) D.d v.c Z := by
  constructor
  · have he : coordinateRepresentative A G U m D b v =
        (U.representative v.epsilon).val * G.generator v.a * G.generator v.c *
          G.generator v.n ^ 3 * G.generator D.d ^ (-2 : ℤ) *
          G.generator b.f ^ (-2 : ℤ) := by
      dsimp [coordinateRepresentative]
      simp only [zpow_neg, zpow_ofNat, div_eq_mul_inv, mul_pow, mul_inv]
      group
    simp only [coordinateFrequency, ThetaReflectionData.frequencyClass_mk, he,
      map_mul, map_pow, map_zpow, hd, hc, profileIndex, freeze]
  · simp only [coordinateFrequency, ThetaReflectionData.frequencyNorm_mk,
      coordinateRepresentative, map_div, map_mul, map_pow, norm_div]
    change Z * ((normHom A (A.diagonal (U.representative v.epsilon).val *
      A.diagonal (G.generator v.a) * A.diagonal (G.generator v.c) *
      A.diagonal (G.generator v.n) ^ 3)) /
      normHom A ((A.diagonal (G.generator D.d) * A.diagonal (G.generator b.f)) ^ 2)) = _
    simp only [map_pow, map_mul]
    change Z * (A.norm (A.diagonal (U.representative v.epsilon).val) *
      A.norm (A.diagonal (G.generator v.a)) * A.norm (A.diagonal (G.generator v.c)) *
      A.norm (A.diagonal (G.generator v.n)) ^ 3 /
      (A.norm (A.diagonal (G.generator D.d)) * A.norm (A.diagonal (G.generator b.f))) ^ 2) = _
    simp only [gen_norm, U_norm, one_mul, profileArgument, freeze, mul_pow]
    ring

end
end DedekindZetaZeroFree.ThetaPhaseSeparation
