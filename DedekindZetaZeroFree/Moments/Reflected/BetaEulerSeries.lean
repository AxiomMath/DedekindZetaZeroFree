module

public import DedekindZetaZeroFree.Arithmetic.Ideals.ExteriorIdeals.EulerWeights

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical

def betaLocalTerm (Q σ : ℝ) (e : ℕ) : ℝ :=
  betaLocal Q e * Real.rpow Q (-σ * (e : ℝ))

theorem betaLocalTerm_nonneg (Q σ : ℝ) (hQ : 2 ≤ Q) (hσ : 0 ≤ σ) (e : ℕ) :
    0 ≤ betaLocalTerm Q σ e := by
  unfold betaLocalTerm
  exact mul_nonneg (betaLocal_nonneg Q hQ e) (Real.rpow_nonneg (by linarith) _)

private theorem betaLocalTerm_one (Q σ : ℝ) (hQ : 2 ≤ Q) (k : ℕ) :
    betaLocalTerm Q σ (1 + 3 * k) =
      Real.rpow Q (-σ) * Real.rpow Q (-1 - 3 * σ) ^ k := by
  have hQ0 : 0 < Q := by linarith
  simp only [betaLocalTerm, betaLocal_one_add_three_mul Q hQ, Real.rpow_eq_pow]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le, ← Real.rpow_add hQ0,
    ← Real.rpow_add hQ0]
  congr 1
  push_cast
  ring

private theorem betaLocalTerm_three (Q σ : ℝ) (hQ : 2 ≤ Q) (k : ℕ) :
    betaLocalTerm Q σ (3 * (k + 1)) =
      Real.rpow Q (-(1 / 2 : ℝ) - 3 * σ) * Real.rpow Q (-1 - 3 * σ) ^ k := by
  have hQ0 : 0 < Q := by linarith
  simp only [betaLocalTerm, betaLocal_three_mul Q hQ (k + 1) (by omega), Real.rpow_eq_pow]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le, ← Real.rpow_add hQ0,
    ← Real.rpow_add hQ0]
  congr 1
  push_cast
  ring

private theorem betaLocalTerm_two (Q σ : ℝ) (hQ : 2 ≤ Q) (k : ℕ) :
    betaLocalTerm Q σ (2 + 3 * k) = 0 := by
  simp [betaLocalTerm, betaLocal_two_add_three_mul Q hQ]

private theorem betaLocalTerm_residue_hasSum (Q σ : ℝ) (hQ : 2 ≤ Q) (hσ : 0 ≤ σ) :
    HasSum (fun k => betaLocalTerm Q σ (3 * k))
      (1 + Real.rpow Q (-(1 / 2 : ℝ) - 3 * σ) / (1 - Real.rpow Q (-1 - 3 * σ))) ∧
    HasSum (fun k => betaLocalTerm Q σ (1 + 3 * k))
      (Real.rpow Q (-σ) / (1 - Real.rpow Q (-1 - 3 * σ))) ∧
    HasSum (fun k => betaLocalTerm Q σ (2 + 3 * k)) 0 := by
  have hQ0 : 0 ≤ Q := by linarith
  have hr := hasSum_geometric_of_lt_one (Real.rpow_nonneg hQ0 (-1 - 3 * σ))
    (Real.rpow_lt_one_of_one_lt_of_neg (by linarith : 1 < Q)
      (by linarith : -1 - 3 * σ < 0))
  constructor
  · have h : HasSum (fun k => betaLocalTerm Q σ (3 * (k + 1)))
        (Real.rpow Q (-(1 / 2 : ℝ) - 3 * σ) / (1 - Real.rpow Q (-1 - 3 * σ))) := by
      convert hr.mul_left (Real.rpow Q (-(1 / 2 : ℝ) - 3 * σ)) using 1
      · ext k
        exact betaLocalTerm_three Q σ hQ k
      · exact div_eq_mul_inv _ _
    have h' := (hasSum_nat_add_iff (f := fun k => betaLocalTerm Q σ (3 * k)) 1).mp h
    simpa [betaLocalTerm, betaLocal_zero, add_comm] using h'
  constructor
  · convert hr.mul_left (Real.rpow Q (-σ)) using 1
    · ext k
      exact betaLocalTerm_one Q σ hQ k
    · exact div_eq_mul_inv _ _
  · simp only [betaLocalTerm_two Q σ hQ]
    exact hasSum_zero

theorem betaLocalTerm_summable (Q σ : ℝ) (hQ : 2 ≤ Q) (hσ : 0 ≤ σ) :
    Summable (betaLocalTerm Q σ) := by
  obtain ⟨h0, h1, h2⟩ := betaLocalTerm_residue_hasSum Q σ hQ hσ
  let g : Fin 3 × ℕ → ℝ := fun p => betaLocalTerm Q σ (p.2 * 3 + p.1)
  have hg : Summable g := by
    apply (summable_prod_of_nonneg (fun p => betaLocalTerm_nonneg Q σ hQ hσ _)).2
    constructor
    · intro j
      fin_cases j
      · simpa [g, mul_comm] using h0.summable
      · simpa [g, mul_comm, add_comm] using h1.summable
      · simpa [g, mul_comm, add_comm] using h2.summable
    · exact (hasSum_fintype _).summable
  exact ((Nat.divModEquiv 3).symm.summable_iff).mp
    (by simpa [g, Function.comp_def] using hg.prod_symm)

theorem betaLocalTerm_tsum (Q σ : ℝ) (hQ : 2 ≤ Q) (hσ : 0 ≤ σ) :
    ∑' e : ℕ, betaLocalTerm Q σ e = eulerLocal Q σ := by
  obtain ⟨h0, h1, h2⟩ := betaLocalTerm_residue_hasSum Q σ hQ hσ
  have hs := (betaLocalTerm_summable Q σ hQ hσ).comp_injective
    (Nat.divModEquiv 3).symm.injective
  rw [← (Nat.divModEquiv 3).symm.tsum_eq (betaLocalTerm Q σ)]
  rw [← (Equiv.prodComm (Fin 3) ℕ).tsum_eq
    (fun p : ℕ × Fin 3 => betaLocalTerm Q σ ((Nat.divModEquiv 3).symm p))]
  change (∑' c : Fin 3 × ℕ, (betaLocalTerm Q σ ∘ (Nat.divModEquiv 3).symm) c.swap) = _
  rw [Summable.tsum_prod hs.prod_symm, tsum_fintype, Fin.sum_univ_three]
  simp only [Function.comp_def, Nat.divModEquiv_symm_apply, Prod.swap, Fin.val_zero,
    Fin.val_one, Fin.val_two, add_zero]
  have h0' : ∑' k, betaLocalTerm Q σ (k * 3) =
      1 + Real.rpow Q (-(1 / 2 : ℝ) - 3 * σ) / (1 - Real.rpow Q (-1 - 3 * σ)) := by
    simpa only [mul_comm] using h0.tsum_eq
  have h1' : ∑' k, betaLocalTerm Q σ (k * 3 + 1) =
      Real.rpow Q (-σ) / (1 - Real.rpow Q (-1 - 3 * σ)) := by
    simpa only [mul_comm, add_comm] using h1.tsum_eq
  have h2' : ∑' k, betaLocalTerm Q σ (k * 3 + 2) = 0 := by
    simpa only [mul_comm, add_comm] using h2.tsum_eq
  rw [h0', h1', h2']
  unfold eulerLocal
  ring

theorem eulerLocal_bounds (Q σ : ℝ) (hQ : 2 ≤ Q) (hσ : 0 ≤ σ) :
    1 ≤ eulerLocal Q σ ∧ eulerLocal Q σ ≤ 3 + Real.sqrt 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hr0 : 0 ≤ Real.rpow Q (-1 - 3 * σ) := Real.rpow_nonneg hQ0.le _
  have hr : Real.rpow Q (-1 - 3 * σ) ≤ (1 / 2 : ℝ) := by
    calc
      Real.rpow Q (-1 - 3 * σ) ≤ Real.rpow Q (-1) :=
        Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
      _ ≤ Real.rpow 2 (-1) := Real.rpow_le_rpow_of_nonpos (by norm_num) hQ (by norm_num)
      _ = 1 / 2 := by norm_num [Real.rpow_neg_one]
  have ha0 : 0 ≤ Real.rpow Q (-σ) := Real.rpow_nonneg hQ0.le _
  have ha : Real.rpow Q (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  have hb0 : 0 ≤ Real.rpow Q (-(1 / 2 : ℝ) - 3 * σ) := Real.rpow_nonneg hQ0.le _
  have hb : Real.rpow Q (-(1 / 2 : ℝ) - 3 * σ) ≤ Real.sqrt 2 / 2 := by
    calc
      Real.rpow Q (-(1 / 2 : ℝ) - 3 * σ) ≤ Real.rpow Q (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
      _ ≤ Real.rpow 2 (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hQ (by norm_num)
      _ = Real.sqrt 2 / 2 := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
        have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        have hp := Real.sqrt_pos.2 (show (0 : ℝ) < 2 by norm_num)
        field_simp
        nlinarith
  unfold eulerLocal
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (add_nonneg ha0 hb0) (by linarith))
  · have hfrac : (Real.rpow Q (-σ) + Real.rpow Q (-(1 / 2 : ℝ) - 3 * σ)) /
        (1 - Real.rpow Q (-1 - 3 * σ)) ≤ 2 + Real.sqrt 2 := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - Real.rpow Q (-1 - 3 * σ))).2
      have hs0 := Real.sqrt_nonneg (2 : ℝ)
      nlinarith
    linarith

variable {F : Type} [Field F] [NumberField F] {cS : Ideal (𝓞 F)}

def supportedExteriorIdeals (f : ExteriorSquarefreeIdeal cS) : Set (ExteriorIdeal cS) :=
  { a | IdealSupportedOn a.val f.val.val }

def betaIdealTerm (f : ExteriorSquarefreeIdeal cS) (σ : ℝ)
    (a : ↥(supportedExteriorIdeals f)) : ℝ :=
  betaIdeal f a.val.val * Real.rpow (idealNorm a.val.val) (-σ)

theorem betaIdealTerm_nonneg (f : ExteriorSquarefreeIdeal cS) (σ : ℝ) (hσ : 0 ≤ σ)
    (a : ↥(supportedExteriorIdeals f)) : 0 ≤ betaIdealTerm f σ a := by
  unfold betaIdealTerm
  apply mul_nonneg _ (Real.rpow_nonneg (by unfold idealNorm; positivity) _)
  unfold betaIdeal
  split_ifs
  · apply Finset.prod_nonneg
    intro p hp
    have hp' : Prime p := UniqueFactorizationMonoid.prime_of_normalized_factor p
      (Multiset.mem_toFinset.mp hp)
    exact betaLocal_nonneg _ (idealNorm_prime_ge_two p hp') _
  · exact le_rfl

private theorem supportedIdeal_factorization_raw (f a : Ideal (𝓞 F)) (ha : a ≠ ⊥)
    (hs : IdealSupportedOn a f) :
    (∏ p ∈ idealPrimeSupport f, p ^ idealPrimeExponent p a) = a := by
  calc
    (∏ p ∈ idealPrimeSupport f, p ^ idealPrimeExponent p a) =
        ∏ p ∈ idealPrimeSupport a, p ^ idealPrimeExponent p a := by
      symm
      apply Finset.prod_subset hs
      intro p hp hpa
      have hcount : idealPrimeExponent p a = 0 :=
        Multiset.count_eq_zero.mpr (by simpa only [idealPrimeSupport, Multiset.mem_toFinset] using hpa)
      simp [hcount]
    _ = a := by
      change (∏ p ∈ (UniqueFactorizationMonoid.normalizedFactors a).toFinset,
        p ^ (UniqueFactorizationMonoid.normalizedFactors a).count p) = _
      have h := Finset.prod_multiset_map_count (UniqueFactorizationMonoid.normalizedFactors a) id
      simp only [id_eq, Multiset.map_id'] at h
      exact h.symm.trans (associated_iff_eq.mp (UniqueFactorizationMonoid.prod_normalizedFactors ha))

private theorem supportedIdeal_factorization (f : ExteriorSquarefreeIdeal cS)
    (a : ↥(supportedExteriorIdeals f)) :
    (∏ p : ↥(idealPrimeSupport f.val.val), p.val ^ idealPrimeExponent p.val a.val.val) = a.val.val := by
  exact ((idealPrimeSupport f.val.val).prod_coe_sort
    (fun p => p ^ idealPrimeExponent p a.val.val)).trans
      (supportedIdeal_factorization_raw f.val.val a.val.val a.val.property.1 a.property)

private theorem betaIdealTerm_eq_prod (f : ExteriorSquarefreeIdeal cS) (σ : ℝ)
    (a : ↥(supportedExteriorIdeals f)) :
    betaIdealTerm f σ a = ∏ p : ↥(idealPrimeSupport f.val.val),
      betaLocalTerm (idealNorm p.val) σ (idealPrimeExponent p.val a.val.val) := by
  have hnorm : idealNorm a.val.val = ∏ p : ↥(idealPrimeSupport f.val.val),
      idealNorm p.val ^ idealPrimeExponent p.val a.val.val := by
    conv_lhs => rw [← supportedIdeal_factorization f a]
    simp [idealNorm, map_prod, map_pow]
  unfold betaIdealTerm betaIdeal
  rw [if_pos ⟨a.val.property.1, a.val.property.2, a.property⟩, hnorm]
  have hpow := Real.finset_prod_rpow Finset.univ
    (fun p : ↥(idealPrimeSupport f.val.val) => idealNorm p.val ^ idealPrimeExponent p.val a.val.val)
    (fun p _ => by unfold idealNorm; positivity) (-σ)
  simp only [← Real.rpow_eq_pow] at hpow
  rw [← hpow]
  have hb := (idealPrimeSupport f.val.val).prod_coe_sort
    (fun p => betaLocal (idealNorm p) (idealPrimeExponent p a.val.val))
  rw [← hb, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  unfold betaLocalTerm
  congr 1
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by unfold idealNorm; positivity)]
  congr 1
  ring

private theorem supportedExponent_injective (f : ExteriorSquarefreeIdeal cS) :
    Function.Injective (fun a : ↥(supportedExteriorIdeals f) =>
      fun p : ↥(idealPrimeSupport f.val.val) => idealPrimeExponent p.val a.val.val) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply associated_iff_eq.mp
  apply (UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors
    a.val.property.1 b.val.property.1).2
  apply Multiset.ext.mpr
  intro p
  by_cases hp : p ∈ idealPrimeSupport f.val.val
  · exact congrFun hab ⟨p, hp⟩
  · have ha : p ∉ idealPrimeSupport a.val.val := fun h => hp (a.property h)
    have hb : p ∉ idealPrimeSupport b.val.val := fun h => hp (b.property h)
    simp only [idealPrimeSupport, Multiset.mem_toFinset] at ha hb
    simp [Multiset.count_eq_zero.mpr ha, Multiset.count_eq_zero.mpr hb]

private theorem summable_finite_products {ι : Type*} [Fintype ι]
    (g : ι → ℕ → ℝ) (hg : ∀ i n, 0 ≤ g i n) (hs : ∀ i, Summable (g i)) :
    Summable (fun x : ι → ℕ => ∏ i, g i (x i)) := by
  classical
  apply summable_of_sum_le (fun x => Finset.prod_nonneg (fun i _ => hg i _))
  intro s
  let t : Finset (ι → ℕ) := Fintype.piFinset (fun i => s.image (fun x => x i))
  have hst : s ⊆ t := by
    intro x hx
    exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_image_of_mem _ hx)
  calc
    (∑ x ∈ s, ∏ i, g i (x i)) ≤ ∑ x ∈ t, ∏ i, g i (x i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hst (fun x _ _ => Finset.prod_nonneg (fun i _ => hg i _))
    _ = ∏ i, ∑ n ∈ s.image (fun x => x i), g i n := by
      exact (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' n, g i n := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Finset.sum_nonneg (fun n _ => hg i n)
      · intro i hi
        exact (hs i).sum_le_tsum _ (fun n _ => hg i n)

theorem betaIdealTerm_summable (f : ExteriorSquarefreeIdeal cS) (σ : ℝ) (hσ : 0 ≤ σ) :
    Summable (betaIdealTerm f σ) := by
  let g : ↥(idealPrimeSupport f.val.val) → ℕ → ℝ :=
    fun p => betaLocalTerm (idealNorm p.val) σ
  have hQ : ∀ p : ↥(idealPrimeSupport f.val.val), 2 ≤ idealNorm p.val := by
    intro p
    exact idealNorm_prime_ge_two _
      (UniqueFactorizationMonoid.prime_of_normalized_factor _ (Multiset.mem_toFinset.mp p.property))
  have hs := summable_finite_products g
    (fun p n => betaLocalTerm_nonneg _ σ (hQ p) hσ n)
    (fun p => betaLocalTerm_summable _ σ (hQ p) hσ)
  have hc := hs.comp_injective (supportedExponent_injective f)
  simpa only [Function.comp_def, g, ← betaIdealTerm_eq_prod] using hc

private theorem finite_products_hasSum {ι : Type*} [Fintype ι]
    (g : ι → ℕ → ℝ) (hg : ∀ i n, 0 ≤ g i n) (hs : ∀ i, Summable (g i)) :
    HasSum (fun x : ι → ℕ => ∏ i, g i (x i)) (∏ i, ∑' n, g i n) := by
  classical
  let t : Finset ℕ → Finset (ι → ℕ) := fun s => Fintype.piFinset (fun _ => s)
  have ht : Filter.Tendsto t Filter.atTop Filter.atTop := by
    apply Monotone.tendsto_atTop_atTop
    · intro s u hsu x hx
      exact Fintype.mem_piFinset.mpr (fun i => hsu (Fintype.mem_piFinset.mp hx i))
    · intro s
      refine ⟨s.biUnion (fun x => Finset.univ.image x), ?_⟩
      intro x hx
      apply Fintype.mem_piFinset.mpr
      intro i
      exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image_of_mem x (Finset.mem_univ i)⟩
  refine hasSum_of_subseq_of_summable ?_ ht ?_
  · simpa only [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun i _ => hg i _))]
      using summable_finite_products g hg hs
  · simp only [t, Finset.sum_prod_piFinset]
    exact tendsto_finsetProd _ (fun i _ => (hs i).hasSum)

private theorem primeExponent_prod (s : Finset (Ideal (𝓞 F)))
    (e : Ideal (𝓞 F) → ℕ) (hprime : ∀ q ∈ s, Prime q) (p : Ideal (𝓞 F)) :
    idealPrimeExponent p (∏ q ∈ s, q ^ e q) = ∑ q ∈ s, if q = p then e q else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change idealPrimeExponent p (1 : Ideal (𝓞 F)) = _
    simp only [idealPrimeExponent, UniqueFactorizationMonoid.normalizedFactors_one,
      Multiset.count_zero, Finset.sum_empty]
  | @insert q s hq ih =>
    have hpq := hprime q (Finset.mem_insert_self q s)
    have hps : ∀ r ∈ s, Prime r := fun r hr => hprime r (Finset.mem_insert_of_mem hr)
    have hne : (∏ r ∈ s, r ^ e r) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun r hr => pow_ne_zero _ (hps r hr).ne_zero)
    rw [Finset.prod_insert hq, Finset.sum_insert hq]
    unfold idealPrimeExponent
    rw [UniqueFactorizationMonoid.normalizedFactors_mul (pow_ne_zero _ hpq.ne_zero) hne,
      Multiset.count_add, hpq.irreducible.normalizedFactors_pow]
    simp only [normalize_eq, Multiset.count_replicate]
    exact congrArg (fun n => (if q = p then e q else 0) + n) (ih hps)

private theorem supportedExponent_surjective (f : ExteriorSquarefreeIdeal cS) :
    Function.Surjective (fun a : ↥(supportedExteriorIdeals f) =>
      fun p : ↥(idealPrimeSupport f.val.val) => idealPrimeExponent p.val a.val.val) := by
  classical
  intro x
  let s := idealPrimeSupport f.val.val
  let e : Ideal (𝓞 F) → ℕ := fun p => if hp : p ∈ s then x ⟨p, hp⟩ else 0
  let a : Ideal (𝓞 F) := ∏ p ∈ s, p ^ e p
  have hp : ∀ p ∈ s, Prime p := fun p h =>
    UniqueFactorizationMonoid.prime_of_normalized_factor p (Multiset.mem_toFinset.mp h)
  have ha : a ≠ ⊥ := Finset.prod_ne_zero_iff.mpr (fun p h => pow_ne_zero _ (hp p h).ne_zero)
  have hex : a ⊔ cS = ⊤ := by
    apply Ideal.prod_sup_eq_top
    intro p h
    apply Ideal.pow_sup_eq_top
    apply top_unique
    calc
      ⊤ = f.val.val ⊔ cS := f.val.property.2.symm
      _ ≤ p ⊔ cS := sup_le_sup_right
        (Ideal.dvd_iff_le.mp (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
          (Multiset.mem_toFinset.mp h))) _
  have hv : ∀ p, idealPrimeExponent p a = if p ∈ s then e p else 0 := by
    intro p
    rw [primeExponent_prod s e hp p]
    simp
  have hsup : IdealSupportedOn a f.val.val := by
    intro p h
    by_contra hn
    have hz : idealPrimeExponent p a = 0 := by rw [hv]; simp [s, hn]
    exact (Multiset.count_ne_zero.mpr (Multiset.mem_toFinset.mp h)) hz
  refine ⟨⟨⟨a, ha, hex⟩, hsup⟩, ?_⟩
  funext p
  change idealPrimeExponent p.val a = x p
  rw [hv]
  simp [e, p.property]

theorem betaIdealTerm_tsum (f : ExteriorSquarefreeIdeal cS) (σ : ℝ) (hσ : 0 ≤ σ) :
    ∑' a : ↥(supportedExteriorIdeals f), betaIdealTerm f σ a = eulerIdeal f σ := by
  classical
  let g : ↥(idealPrimeSupport f.val.val) → ℕ → ℝ :=
    fun p => betaLocalTerm (idealNorm p.val) σ
  have hQ : ∀ p : ↥(idealPrimeSupport f.val.val), 2 ≤ idealNorm p.val := by
    intro p
    exact idealNorm_prime_ge_two _
      (UniqueFactorizationMonoid.prime_of_normalized_factor _ (Multiset.mem_toFinset.mp p.property))
  let e : ↥(supportedExteriorIdeals f) ≃ (↥(idealPrimeSupport f.val.val) → ℕ) :=
    Equiv.ofBijective (fun a p => idealPrimeExponent p.val a.val.val)
      ⟨supportedExponent_injective f, supportedExponent_surjective f⟩
  have hs := finite_products_hasSum g
    (fun p n => betaLocalTerm_nonneg _ σ (hQ p) hσ n)
    (fun p => betaLocalTerm_summable _ σ (hQ p) hσ)
  have ht := e.hasSum_iff.mpr hs
  have hb : HasSum (betaIdealTerm f σ) (∏ p : ↥(idealPrimeSupport f.val.val),
      ∑' n, betaLocalTerm (idealNorm p.val) σ n) := by
    convert ht using 1
    funext a
    exact betaIdealTerm_eq_prod f σ a
  rw [hb.tsum_eq]
  unfold eulerIdeal
  rw [← (idealPrimeSupport f.val.val).prod_coe_sort (fun p => eulerLocal (idealNorm p) σ)]
  apply Finset.prod_congr rfl
  intro p hp
  exact betaLocalTerm_tsum _ σ (hQ p) hσ

end
end DedekindZetaZeroFree
