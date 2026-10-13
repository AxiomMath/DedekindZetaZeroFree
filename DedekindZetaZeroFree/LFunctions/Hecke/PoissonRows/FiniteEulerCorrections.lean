module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.FixedData.Row

open DedekindZetaZeroFree NumberField in

noncomputable def ideal {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus} {D : FixedData S η}
    (u : D.Row) : D.recipe.A.Exterior :=
  PrincipalProbeConstruction.Inputs.rowIdeal D.recipe.A u.u u.u_ne_zero

end DedekindZetaZeroFree.Quantitative.FixedData.Row

namespace DedekindZetaZeroFree.Quantitative.EulerDeletion

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def rowPrimes (u : D.Row) : Finset (Ideal (NumberField.RingOfIntegers F)) :=
  (UniqueFactorizationMonoid.normalizedFactors
    (Subtype.val (DedekindZetaZeroFree.Quantitative.FixedData.Row.ideal u) : Ideal (NumberField.RingOfIntegers F))).toFinset

def rowPrimesWithS (u : D.Row) : Finset (Ideal (NumberField.RingOfIntegers F)) :=
  rowPrimes D u ∪ D.recipe.A.Sf.image (fun v => v.asIdeal)

private theorem rowPrimes_eq (u : D.Row) :
    rowPrimes D u = idealPrimeSupport (DedekindZetaZeroFree.Quantitative.FixedData.Row.ideal u).val := by
  unfold rowPrimes idealPrimeSupport
  congr

private theorem two_le_absNorm_of_ne (p : Ideal (NumberField.RingOfIntegers F))
    (h0 : p ≠ ⊥) (h1 : p ≠ ⊤) : 2 ≤ Ideal.absNorm p := by
  have ha : Ideal.absNorm p ≠ 0 := fun h => h0 (Ideal.absNorm_eq_zero_iff.mp h)
  have hb : Ideal.absNorm p ≠ 1 := fun h => h1 (Ideal.absNorm_eq_one_iff.mp h)
  omega

private theorem idealNorm_nonneg' (p : Ideal (NumberField.RingOfIntegers F)) :
    0 ≤ idealNorm p := by
  unfold idealNorm
  positivity

private theorem inv_facts (σ : ℝ) (hσ : 0 < σ) (n : ℝ) (hn : 2 ≤ n) :
    0 < 1 - n ^ (-σ) ∧ 0 ≤ n ^ (-σ) ∧ 1 ≤ (1 - n ^ (-σ))⁻¹ ∧
      (1 - n ^ (-σ))⁻¹ ≤ 1 + (1 / (1 - (2:ℝ) ^ (-σ))) * n ^ (-σ) := by
  have hr1 : (2:ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hx0 : 0 ≤ n ^ (-σ) := Real.rpow_nonneg (by linarith) _
  have hxr : n ^ (-σ) ≤ (2:ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hn (by linarith)
  have hd : 0 < 1 - (2:ℝ) ^ (-σ) := by linarith
  have hCpos : 0 < 1 / (1 - (2:ℝ) ^ (-σ)) := div_pos one_pos hd
  have hC : 1 / (1 - (2:ℝ) ^ (-σ)) * (1 - (2:ℝ) ^ (-σ)) = 1 := one_div_mul_cancel hd.ne'
  have hpos : 0 < 1 - n ^ (-σ) := by linarith
  have h1 : 1 ≤ 1 / (1 - (2:ℝ) ^ (-σ)) * (1 - n ^ (-σ)) := by
    nlinarith [mul_nonneg hCpos.le (sub_nonneg.mpr hxr)]
  have hi := inv_pos.mpr hpos
  have hinv : (1 - n ^ (-σ)) * (1 - n ^ (-σ))⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  refine ⟨hpos, hx0, ?_, ?_⟩
  · nlinarith [mul_nonneg hi.le hx0]
  · rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr h1)]

private theorem sset_two (p : Ideal (NumberField.RingOfIntegers F))
    (hp : p ∈ D.recipe.A.Sf.image (fun v => v.asIdeal)) : 2 ≤ idealNorm p := by
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hp
  have h := two_le_absNorm_of_ne v.asIdeal v.ne_bot v.isPrime.ne_top
  unfold idealNorm
  exact_mod_cast h

private theorem prime_norm_two (I : Ideal (NumberField.RingOfIntegers F))
    (p : Ideal (NumberField.RingOfIntegers F)) (hp : p ∈ idealPrimeSupport I) :
    2 ≤ idealNorm p :=
  idealNorm_prime_ge_two p (UniqueFactorizationMonoid.prime_of_normalized_factor p
    (by simpa only [idealPrimeSupport, Multiset.mem_toFinset] using hp))

private theorem q_eq_idealNorm (u : D.Row) :
    D.q u = idealNorm (DedekindZetaZeroFree.Quantitative.FixedData.Row.ideal u).val := by
  unfold DedekindZetaZeroFree.Quantitative.FixedData.q
  show ((Nat.card (D.recipe.A.R ⧸ Ideal.span {u.u}) : ℕ) : ℝ) = _
  rw [(PrincipalProbeConstruction.Inputs.rowIdeal_generates D.recipe.A u.u u.u_ne_zero).2,
    D.recipe.A.exteriorResidue_card]
  rfl

private theorem prod_union_le_aux {ι : Type} [DecidableEq ι] (A B : Finset ι) (g : ι → ℝ)
    (hA : ∀ p ∈ A, 0 ≤ g p) (hB : ∀ p ∈ B, 1 ≤ g p) :
    ∏ p ∈ A ∪ B, g p ≤ (∏ p ∈ A, g p) * ∏ p ∈ B, g p := by
  have hU : 0 ≤ ∏ p ∈ A ∪ B, g p := Finset.prod_nonneg (fun p hp => by
    rcases Finset.mem_union.mp hp with h | h
    · exact hA p h
    · linarith [hB p h])
  have hI : 1 ≤ ∏ p ∈ A ∩ B, g p :=
    Finset.one_le_prod₀ (fun p hp => hB p (Finset.mem_inter.mp hp).2)
  have key := Finset.prod_union_inter (s₁ := A) (s₂ := B) (f := g)
  nlinarith [mul_le_mul_of_nonneg_left hI hU]

private theorem row_bounds (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ K1 K2 : ℝ, 0 < K1 ∧ 0 < K2 ∧ ∀ u : D.Row,
      (∏ p ∈ idealPrimeSupport (DedekindZetaZeroFree.Quantitative.FixedData.Row.ideal u).val,
          (1 + idealNorm p ^ (-σ))) ≤ K1 * (D.q u) ^ ε ∧
      (∏ p ∈ idealPrimeSupport (DedekindZetaZeroFree.Quantitative.FixedData.Row.ideal u).val,
          (1 - idealNorm p ^ (-σ))⁻¹) ≤ K2 * (D.q u) ^ ε := by
  have hr1 : (2:ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨K1, hK1, h1⟩ :=
    fixed_small_prime_subpower F D.recipe.A.cS 1 σ ε zero_le_one hσ hε
  obtain ⟨K2, hK2, h2⟩ :=
    fixed_small_prime_subpower F D.recipe.A.cS (1 / (1 - (2:ℝ) ^ (-σ))) σ ε
      (div_nonneg zero_le_one (sub_nonneg.mpr hr1.le)) hσ hε
  refine ⟨K1, K2, hK1, hK2, fun u => ?_⟩
  have hq := q_eq_idealNorm D u
  rw [hq]
  have hI1 := h1 (DedekindZetaZeroFree.Quantitative.FixedData.Row.ideal u)
  have hI2 := h2 (DedekindZetaZeroFree.Quantitative.FixedData.Row.ideal u)
  simp only [one_mul] at hI1
  constructor
  · exact hI1
  · refine le_trans ?_ hI2
    apply Finset.prod_le_prod₀
    · intro p hp
      exact le_trans zero_le_one (inv_facts σ hσ (idealNorm p)
        (prime_norm_two _ p hp)).2.2.1
    · intro p hp
      exact (inv_facts σ hσ (idealNorm p) (prime_norm_two _ p hp)).2.2.2

theorem euler_product_bound (σs : ℝ) (hσs : 0 < σs) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : D.Row, 1 ≤ D.q u →
      (∏ p ∈ rowPrimes D u, (1 + (Ideal.absNorm p : ℝ) ^ (-σs)) ≤ C * D.q u ^ ε) ∧
      (∏ p ∈ rowPrimes D u, (1 - (Ideal.absNorm p : ℝ) ^ (-σs))⁻¹ ≤ C * D.q u ^ ε) := by
  obtain ⟨K1, K2, hK1, hK2, h⟩ := row_bounds D σs ε hσs hε
  refine ⟨K1 + K2, by linarith, fun u hu => ?_⟩
  have hq0 : 0 ≤ D.q u ^ ε := Real.rpow_nonneg (le_trans zero_le_one hu) ε
  obtain ⟨h1, h2⟩ := h u
  rw [rowPrimes_eq]
  exact ⟨le_trans h1 (mul_le_mul_of_nonneg_right (by linarith) hq0),
    le_trans h2 (mul_le_mul_of_nonneg_right (by linarith) hq0)⟩

theorem euler_product_bound_with_S (σs : ℝ) (hσs : 0 < σs) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : D.Row, 1 ≤ D.q u →
      (∏ p ∈ rowPrimesWithS D u, (1 + (Ideal.absNorm p : ℝ) ^ (-σs)) ≤ C * D.q u ^ ε) ∧
      (∏ p ∈ rowPrimesWithS D u, (1 - (Ideal.absNorm p : ℝ) ^ (-σs))⁻¹ ≤ C * D.q u ^ ε) := by
  obtain ⟨K1, K2, hK1, hK2, h⟩ := row_bounds D σs ε hσs hε
  set Sset := D.recipe.A.Sf.image (fun v => v.asIdeal) with hSset
  have hPS1 : 0 < ∏ p ∈ Sset, (1 + idealNorm p ^ (-σs)) :=
    Finset.prod_pos (fun p _ => by
      have := Real.rpow_nonneg (idealNorm_nonneg' p) (-σs)
      linarith)
  have hPS2 : 0 < ∏ p ∈ Sset, (1 - idealNorm p ^ (-σs))⁻¹ :=
    Finset.prod_pos (fun p hp => lt_of_lt_of_le zero_lt_one
      (inv_facts σs hσs (idealNorm p) (sset_two D p hp)).2.2.1)
  refine ⟨(K1 + K2) * ((∏ p ∈ Sset, (1 + idealNorm p ^ (-σs))) +
      ∏ p ∈ Sset, (1 - idealNorm p ^ (-σs))⁻¹), mul_pos (by linarith) (by linarith),
    fun u hu => ?_⟩
  have hq0 : 0 ≤ D.q u ^ ε := Real.rpow_nonneg (le_trans zero_le_one hu) ε
  obtain ⟨h1, h2⟩ := h u
  have hU : rowPrimesWithS D u =
      idealPrimeSupport (DedekindZetaZeroFree.Quantitative.FixedData.Row.ideal u).val ∪ Sset := by
    unfold rowPrimesWithS
    rw [rowPrimes_eq]
  rw [hU]
  have hA1 : ∀ p ∈ idealPrimeSupport (DedekindZetaZeroFree.Quantitative.FixedData.Row.ideal u).val,
      0 ≤ 1 + idealNorm p ^ (-σs) := fun p _ => by
    have := Real.rpow_nonneg (idealNorm_nonneg' p) (-σs)
    linarith
  have hA2 : ∀ p ∈ idealPrimeSupport (DedekindZetaZeroFree.Quantitative.FixedData.Row.ideal u).val,
      0 ≤ (1 - idealNorm p ^ (-σs))⁻¹ := fun p hp =>
    le_trans zero_le_one (inv_facts σs hσs (idealNorm p) (prime_norm_two _ p hp)).2.2.1
  have hB1 : ∀ p ∈ Sset, 1 ≤ 1 + idealNorm p ^ (-σs) := fun p _ => by
    have := Real.rpow_nonneg (idealNorm_nonneg' p) (-σs)
    linarith
  have hB2 : ∀ p ∈ Sset, 1 ≤ (1 - idealNorm p ^ (-σs))⁻¹ := fun p hp =>
    (inv_facts σs hσs (idealNorm p) (sset_two D p hp)).2.2.1
  have m1 := prod_union_le_aux _ Sset (fun p => 1 + idealNorm p ^ (-σs)) hA1 hB1
  have m2 := prod_union_le_aux _ Sset (fun p => (1 - idealNorm p ^ (-σs))⁻¹) hA2 hB2
  have e1 := mul_le_mul_of_nonneg_right h1 hPS1.le
  have e2 := mul_le_mul_of_nonneg_right h2 hPS2.le
  have f1 : 0 ≤ (K1 * D.q u ^ ε) * ∏ p ∈ Sset, (1 - idealNorm p ^ (-σs))⁻¹ :=
    mul_nonneg (mul_nonneg hK1.le hq0) hPS2.le
  have f2 : 0 ≤ (K2 * D.q u ^ ε) * ∏ p ∈ Sset, (1 + idealNorm p ^ (-σs)) :=
    mul_nonneg (mul_nonneg hK2.le hq0) hPS1.le
  have g1 := mul_nonneg (mul_nonneg hK1.le hPS2.le) hq0
  have g2 := mul_nonneg (mul_nonneg hK2.le hPS1.le) hq0
  have g3 := mul_nonneg (mul_nonneg hK2.le hPS2.le) hq0
  have g4 := mul_nonneg (mul_nonneg hK1.le hPS1.le) hq0
  constructor
  · change (∏ p ∈ idealPrimeSupport (DedekindZetaZeroFree.Quantitative.FixedData.Row.ideal u).val ∪ Sset,
      (1 + idealNorm p ^ (-σs))) ≤ _
    nlinarith
  · change (∏ p ∈ idealPrimeSupport (DedekindZetaZeroFree.Quantitative.FixedData.Row.ideal u).val ∪ Sset,
      (1 - idealNorm p ^ (-σs))⁻¹) ≤ _
    nlinarith

end

end DedekindZetaZeroFree.Quantitative.EulerDeletion
