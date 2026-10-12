module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveCharacterDescent
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.PrimitiveSmoothIdealSums
public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorEpsilonBounds
public import DedekindZetaZeroFree.Arithmetic.Ideals.MoebiusCoprimality

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

noncomputable section

 def thetaWeight (F : Type*) [Field F] [NumberField F] (X : ℝ)
    (I : Ideal (𝓞 F)) : ℂ :=
  (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight ((Ideal.absNorm I : ℝ) / X) : ℂ)

private lemma thetaWeight_eq_zero_of_gt {F : Type*} [Field F] [NumberField F]
    {X : ℝ} (hX : 0 < X) {I : Ideal (𝓞 F)}
    (hI : 5 / 2 * X < (Ideal.absNorm I : ℝ)) : thetaWeight F X I = 0 := by
  unfold thetaWeight
  rw [DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_eq_zero_of_ge (by rw [le_div_iff₀ hX]; linarith)]
  simp

private lemma thetaWeight_bot {F : Type*} [Field F] [NumberField F] (X : ℝ) :
    thetaWeight F X (⊥ : Ideal (𝓞 F)) = 0 := by
  unfold thetaWeight
  have hb : (Ideal.absNorm (⊥ : Ideal (𝓞 F)) : ℝ) = 0 := by
    simp [Ideal.absNorm_eq_zero_iff]
  rw [hb, zero_div, DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_eq_zero_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
  simp

private lemma support_theta_subset {F : Type*} [Field F] [NumberField F]
    (v : Ideal (𝓞 F) → ℂ) {X : ℝ} (hX : 0 < X) :
    Function.support (fun I : Ideal (𝓞 F) =>
        if I = ⊥ then 0 else thetaWeight F X I * v I) ⊆
      (↑(DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F (5 / 2 * X)) : Set (Ideal (𝓞 F))) := by
  intro I hI
  rw [Finset.mem_coe, DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals]
  by_contra hcon
  push Not at hcon
  have hz : thetaWeight F X I = 0 := thetaWeight_eq_zero_of_gt hX hcon
  simp only [Function.mem_support, ne_eq] at hI
  exact hI (by by_cases h : I = ⊥ <;> simp [h, hz])

private lemma initialTheta_eq_finsum_all {F : Type*} [Field F] [NumberField F]
    (v : Ideal (𝓞 F) → ℂ) {X : ℝ} (hX : 0 < X) :
    initialTheta F v X =
      ∑ᶠ I : Ideal (𝓞 F), if I = ⊥ then 0 else thetaWeight F X I * v I := by
  rw [finsum_eq_finsetSum_of_support_subset _ (support_theta_subset v hX)]
  have : (∑ I ∈ DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F (5 / 2 * X),
        (if I = ⊥ then 0 else thetaWeight F X I * v I)) =
      ∑ I ∈ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F (5 / 2 * X)).filter (fun I => I ≠ ⊥),
        thetaWeight F X I * v I := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases h : I = ⊥ <;> simp [h]
  rw [this]
  rfl

private lemma thetaWeight_mul {F : Type*} [Field F] [NumberField F]
    (X : ℝ) (d J : Ideal (𝓞 F)) :
    thetaWeight F X (d * J) = thetaWeight F (X / (Ideal.absNorm d : ℝ)) J := by
  unfold thetaWeight
  rw [Ideal.absNorm.map_mul]
  push_cast
  congr 1
  rw [div_div_eq_mul_div]
  ring_nf

private lemma multiples_eq_scaled {F : Type*} [Field F] [NumberField F]
    (v : Ideal (𝓞 F) → ℂ) (hv : ∀ I J : Ideal (𝓞 F), v (I * J) = v I * v J)
    {X : ℝ} (hX : 0 < X) (d : Ideal (𝓞 F)) (hd : d ≠ ⊥) :
    (∑ᶠ I : Ideal (𝓞 F), if I ≠ ⊥ ∧ d ∣ I then thetaWeight F X I * v I else 0) =
      v d * (∑ᶠ J : Ideal (𝓞 F), if J = ⊥ then 0 else
        thetaWeight F (X / (Ideal.absNorm d : ℝ)) J * v J) := by
  have hmem : ∀ I : Ideal (𝓞 F),
      (I ∈ Set.range (fun J : Ideal (𝓞 F) => d * J)) ↔ d ∣ I := by
    intro I
    rw [Set.mem_range]
    exact ⟨fun ⟨J, hJ⟩ => ⟨J, hJ.symm⟩, fun ⟨J, hJ⟩ => ⟨J, hJ.symm⟩⟩
  have hcongr : (∑ᶠ I : Ideal (𝓞 F),
        if I ≠ ⊥ ∧ d ∣ I then thetaWeight F X I * v I else 0) =
      ∑ᶠ I ∈ Set.range (fun J : Ideal (𝓞 F) => d * J), thetaWeight F X I * v I := by
    rw [finsum_mem_def]
    refine finsum_congr fun I => ?_
    rw [Set.indicator_apply, hmem I]
    by_cases hI : I = ⊥
    · subst hI
      rw [thetaWeight_bot]
      simp
    · by_cases h : d ∣ I <;> simp [hI, h]
  rw [hcongr, finsum_mem_range (f := fun I => thetaWeight F X I * v I)
    (g := fun J : Ideal (𝓞 F) => d * J) (fun a b hab => mul_left_cancel₀ hd hab)]
  have hstep : (∑ᶠ J : Ideal (𝓞 F), thetaWeight F X (d * J) * v (d * J)) =
      ∑ᶠ J : Ideal (𝓞 F), v d * (if J = ⊥ then 0 else
        thetaWeight F (X / (Ideal.absNorm d : ℝ)) J * v J) := by
    refine finsum_congr fun J => ?_
    rw [thetaWeight_mul, hv]
    by_cases hJ : J = ⊥
    · subst hJ
      rw [thetaWeight_bot]
      simp
    · simp only [hJ, if_false]
      ring
  rw [hstep, mul_finsum]

private lemma one_le_absNorm_of_mem_idealDivisors {F : Type*} [Field F] [NumberField F]
    {m d : Ideal (𝓞 F)} (hd : d ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors m) :
    (1 : ℝ) ≤ (Ideal.absNorm d : ℝ) := by
  have hne := DedekindZetaZeroFree.LargeSieve.ne_bot_of_mem_idealDivisors hd
  have h0 : Ideal.absNorm d ≠ 0 := fun h => hne (Ideal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0

private lemma moebius_norm_le_one {F : Type*} [Field F] [NumberField F]
    (d : Ideal (𝓞 F)) : ‖(UniqueFactorizationMonoid.moebius d : ℂ)‖ ≤ 1 := by
  by_cases h : Squarefree d
  · rw [h.moebius_eq]
    push_cast
    simp
  · rw [UniqueFactorizationMonoid.moebius_of_not_squarefree h]
    simp

theorem initial_imprimitive_smooth_sum
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ m : Ideal (𝓞 F), m ≠ ⊥ →
        ∀ η : DedekindZetaZeroFree.RayClassCharacter F m, ¬ η.IsPrincipal →
          ∀ X : ℝ, 0 < X →
            ‖initialTheta F η X‖ ≤ A * (Ideal.absNorm m : ℝ) ^ (1 / 2 + δ) := by
  obtain ⟨A0, hA0, hprim⟩ :=
    initial_primitive_smooth_sum F hF (δ / 2) (by linarith)
  obtain ⟨C, hC1, hdiv⟩ := DedekindZetaZeroFree.LargeSieve.ideal_divisor_count_le_rpow F (δ / 2) (by linarith)
  refine ⟨A0 * C, mul_nonneg hA0 (le_trans zero_le_one hC1), ?_⟩
  intro m hm η hnp X hX
  obtain ⟨f, hf, hfm, η0, hprim0, hind, hiff⟩ :=
    DedekindZetaZeroFree.LargeSieve.initial_ray_primitive_descent F m hm η
  have hnp0 : ¬ η0.IsPrincipal := fun h => hnp (hiff.mpr h)

  have hid : initialTheta F η X =
      ∑ d ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors m, (UniqueFactorizationMonoid.moebius d : ℂ) *
        (η0 d * initialTheta F η0 (X / (Ideal.absNorm d : ℝ))) := by
    rw [initialTheta_eq_finsum_all (fun I => η I) hX]
    have hcongr : (∑ᶠ I : Ideal (𝓞 F),
          if I = ⊥ then 0 else thetaWeight F X I * η I) =
        ∑ᶠ I : Ideal (𝓞 F),
          if I ≠ ⊥ ∧ I ⊔ m = ⊤ then thetaWeight F X I * η0 I else 0 := by
      refine finsum_congr fun I => ?_
      by_cases hI : I = ⊥
      · simp [hI]
      · rw [hind I]
        by_cases hc : I ⊔ m = ⊤ <;> simp [hI, hc]
    rw [hcongr, DedekindZetaZeroFree.LargeSieve.PoissonCoprimeExact.coprimeFinsum_eq_moebiusMultiples
      (fun I => thetaWeight F X I * η0 I)
      ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F (5 / 2 * X)).finite_toSet.subset
        (support_theta_subset (fun I => η0 I) hX)) m hm]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdpos : 0 < (Ideal.absNorm d : ℝ) := by
      have h1 := one_le_absNorm_of_mem_idealDivisors hd
      linarith
    rw [multiples_eq_scaled (fun I => η0 I) (fun I J => η0.map_mul' I J) hX d
      (DedekindZetaZeroFree.LargeSieve.ne_bot_of_mem_idealDivisors hd),
      ← initialTheta_eq_finsum_all (fun I => η0 I) (div_pos hX hdpos)]

  have hbound : ∀ d ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors m,
      ‖(UniqueFactorizationMonoid.moebius d : ℂ) *
        (η0 d * initialTheta F η0 (X / (Ideal.absNorm d : ℝ)))‖ ≤
      A0 * (Ideal.absNorm f : ℝ) ^ ((1 : ℝ) / 2 + δ / 2) := by
    intro d hd
    have hdpos : 0 < (Ideal.absNorm d : ℝ) := by
      have h1 := one_le_absNorm_of_mem_idealDivisors hd
      linarith
    have hXd : 0 < X / (Ideal.absNorm d : ℝ) := div_pos hX hdpos
    have hth := hprim f hf η0 hprim0 hnp0 (X / (Ideal.absNorm d : ℝ)) hXd
    rw [norm_mul, norm_mul]
    calc ‖(UniqueFactorizationMonoid.moebius d : ℂ)‖ *
            (‖η0 d‖ * ‖initialTheta F η0 (X / (Ideal.absNorm d : ℝ))‖)
        ≤ 1 * (1 * (A0 * (Ideal.absNorm f : ℝ) ^ ((1 : ℝ) / 2 + δ / 2))) := by
          refine mul_le_mul (moebius_norm_le_one d)
            (mul_le_mul (DedekindZetaZeroFree.LargeSieve.RayOperations.norm_le_one η0 d) hth (norm_nonneg _) zero_le_one)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
      _ = A0 * (Ideal.absNorm f : ℝ) ^ ((1 : ℝ) / 2 + δ / 2) := by ring
  have hNfm : (Ideal.absNorm f : ℝ) ≤ (Ideal.absNorm m : ℝ) := by
    have hm0 : Ideal.absNorm m ≠ 0 := fun h => hm (Ideal.absNorm_eq_zero_iff.mp h)
    have hdvd : Ideal.absNorm f ∣ Ideal.absNorm m :=
      Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hfm)
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
  have hm1 : (1 : ℝ) ≤ (Ideal.absNorm m : ℝ) := by
    have hm0 : Ideal.absNorm m ≠ 0 := fun h => hm (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
  have hm0' : (0 : ℝ) < (Ideal.absNorm m : ℝ) := lt_of_lt_of_le zero_lt_one hm1
  calc ‖initialTheta F η X‖
      = ‖∑ d ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors m, (UniqueFactorizationMonoid.moebius d : ℂ) *
          (η0 d * initialTheta F η0 (X / (Ideal.absNorm d : ℝ)))‖ := by rw [hid]
    _ ≤ ∑ d ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors m,
          ‖(UniqueFactorizationMonoid.moebius d : ℂ) *
            (η0 d * initialTheta F η0 (X / (Ideal.absNorm d : ℝ)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _d ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors m,
          A0 * (Ideal.absNorm f : ℝ) ^ ((1 : ℝ) / 2 + δ / 2) :=
        Finset.sum_le_sum hbound
    _ = (DedekindZetaZeroFree.LargeSieve.idealDivisorCount m : ℝ) *
          (A0 * (Ideal.absNorm f : ℝ) ^ ((1 : ℝ) / 2 + δ / 2)) := by
        rw [Finset.sum_const, DedekindZetaZeroFree.LargeSieve.idealDivisorCount, nsmul_eq_mul]
    _ ≤ (C * (Ideal.absNorm m : ℝ) ^ (δ / 2)) *
          (A0 * (Ideal.absNorm f : ℝ) ^ ((1 : ℝ) / 2 + δ / 2)) := by
        refine mul_le_mul_of_nonneg_right (hdiv m) ?_
        exact mul_nonneg hA0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ (C * (Ideal.absNorm m : ℝ) ^ (δ / 2)) *
          (A0 * (Ideal.absNorm m : ℝ) ^ ((1 : ℝ) / 2 + δ / 2)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hA0)
          (mul_nonneg (le_trans zero_le_one hC1) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) hNfm (by linarith)
    _ = A0 * C * (Ideal.absNorm m : ℝ) ^ (1 / 2 + δ) := by
        have h1 : (Ideal.absNorm m : ℝ) ^ (δ / 2) *
              (Ideal.absNorm m : ℝ) ^ (1 / 2 + δ / 2) =
            (Ideal.absNorm m : ℝ) ^ (1 / 2 + δ) := by
          rw [← Real.rpow_add hm0']
          rw [show δ / 2 + (1 / 2 + δ / 2) = 1 / 2 + δ by ring]
        calc C * (Ideal.absNorm m : ℝ) ^ (δ / 2) *
              (A0 * (Ideal.absNorm m : ℝ) ^ (1 / 2 + δ / 2))
            = A0 * C * ((Ideal.absNorm m : ℝ) ^ (δ / 2) *
                (Ideal.absNorm m : ℝ) ^ (1 / 2 + δ / 2)) := by ring
          _ = A0 * C * (Ideal.absNorm m : ℝ) ^ (1 / 2 + δ) := by rw [h1]

end

end DedekindZetaZeroFree.LargeSieve.Sieve
