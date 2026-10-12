module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.LargeDivisors.DirectExpansionAndRectangleBounds
public import DedekindZetaZeroFree.LargeSieve.Bilinear.DivisibleColumnOperator

@[expose] public section

section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirect

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private theorem fixed_mass_le (C : Context Q) : fixedDivisorMass C ≤ (idealDivisorCount (c * C.d) : ℝ) := by
  have hc : c ≠ ⊥ := by simpa only [C.core] using C.D.bad_ne_bot
  have hcd : c * C.d ≠ ⊥ := mul_ne_zero hc C.hd0
  have hsub : C.mobiusDivisors ⊆ idealDivisors (c * C.d) := by
    intro f hf
    apply (mem_idealDivisors hcd).mpr
    have hr : (c * C.d).radical ≠ ⊥ := by
      intro h
      have := Ideal.le_radical (I := c * C.d)
      rw [h] at this
      exact hcd (le_bot_iff.mp this)
    exact ((mem_idealDivisors hr).mp hf).trans (Ideal.dvd_iff_le.mpr Ideal.le_radical)
  calc
    fixedDivisorMass C ≤ ∑ f ∈ C.mobiusDivisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro f hf
      have hf0 := ne_bot_of_mem_idealDivisors hf
      have hn : 1 ≤ norm f := by
        have hp : 0 < Ideal.absNorm f := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hf0)
        change 1 ≤ (Ideal.absNorm f : ℝ)
        exact_mod_cast (Nat.succ_le_of_lt hp : 1 ≤ Ideal.absNorm f)
      exact (div_le_one (by linarith : 0 < norm f)).mpr hn
    _ = (C.mobiusDivisors.card : ℝ) := by simp
    _ ≤ (idealDivisorCount (c * C.d) : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
private theorem rectangle_card_le (C : Context Q) (B : ℝ) :
    ((ErrorRectangles.directRectangles C B).card : ℝ) ≤
      (Vendor.dyadicLength (2 * max 1 (C.N / norm C.d)) + 1 : ℝ) ^ 2 := by
  have h12 : (ErrorRectangles.directRectangles C B).card ≤
      ((ErrorRectangles.scales (C.N / norm C.d)) ×ˢ
        (ErrorRectangles.scales (C.N / norm C.d))).card := by
    apply Finset.card_le_card
    intro P hP
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).1
  have hs : (ErrorRectangles.scales (C.N / norm C.d)).card ≤
      Vendor.dyadicLength (2 * max 1 (C.N / norm C.d)) + 1 := by
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
      ((Finset.card_image_le).trans (by rw [Finset.card_range])) 1)
  have hd : (ErrorRectangles.directRectangles C B).card ≤
      (Vendor.dyadicLength (2 * max 1 (C.N / norm C.d)) + 1) ^ 2 := by
    exact h12.trans (by
      rw [Finset.card_product, pow_two]
      exact Nat.mul_le_mul hs hs)
  exact_mod_cast hd

theorem fixed_cost_epsilon
    (D : Sieve.AllIndexNormalizedFamilyData Q) (W : ℝ → ℝ)
    (η : ℝ) (hη : 0 < η) :
    ∃ J : ℝ, 0 < J ∧ ∀ C : Context Q, C.D = D → C.W = W →
      1 ≤ C.M → 1 ≤ C.N → 1 ≤ norm C.d → ∀ B : ℝ,
        residueMagnitude C * fixedDivisorMass C *
            ((ErrorRectangles.directRectangles C B).card : ℝ) ≤
          J * Real.rpow (C.M * C.N * norm C.d) η := by
  classical
  by_cases hex : ∃ C₀ : Context Q, C₀.D = D ∧ C₀.W = W
  · obtain ⟨C₀, hD₀, hW₀⟩ := hex
    let e := η / 3
    have he : 0 < e := by dsimp [e]; linarith
    obtain ⟨A, hA, hdiv⟩ := ideal_divisor_count_le_rpow F e he
    let R := residueMagnitude C₀ + 1
    let T := max 1 (norm c)
    let L := 2 + 1 / (e * Real.log 2)
    let H := L * (2 : ℝ) ^ e
    have hR : 0 < R := by dsimp [R, residueMagnitude]; positivity
    have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hL : 0 < L := Vendor.dyadicLength_small_power_constant_pos he
    have hH : 0 < H := mul_pos hL (Real.rpow_pos_of_pos (by norm_num) _)
    refine ⟨R * (A * T ^ e) * H ^ 2, by positivity, ?_⟩
    intro C hD hW hM hN hn B
    let Z := C.M * C.N * norm C.d
    have hMN : 1 ≤ C.M * C.N := one_le_mul_of_one_le_of_one_le hM hN
    have hZ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le hMN hn
    have hnZ : norm C.d ≤ Z := le_mul_of_one_le_left (by linarith) hMN
    have hNZ : C.N ≤ Z := by
      dsimp [Z]
      calc C.N ≤ C.M * C.N := le_mul_of_one_le_left (by linarith) hM
        _ ≤ C.M * C.N * norm C.d := le_mul_of_one_le_right (by linarith) hn
    have hr : residueMagnitude C ≤ R := by
      have hk : C.kappa = C₀.kappa := rfl
      have hm : C.mass = C₀.mass := by
        simp only [Context.mass, Context.source, hW, hW₀]
      dsimp [R, residueMagnitude]
      rw [hk, hm]
      linarith
    have hf : fixedDivisorMass C ≤ (A * T ^ e) * Z ^ e := by
      have hnorm : norm (c * C.d) = norm c * norm C.d := by
        simp [norm, map_mul]
      have hb : norm (c * C.d) ≤ T * Z := by
        rw [hnorm]
        exact mul_le_mul (le_max_right _ _) hnZ (by dsimp [norm]; positivity) hT.le
      calc fixedDivisorMass C ≤ (idealDivisorCount (c * C.d) : ℝ) := fixed_mass_le C
        _ ≤ A * (norm (c * C.d)) ^ e := hdiv _
        _ ≤ A * (T * Z) ^ e := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by dsimp [norm]; positivity) hb he.le) (by linarith)
        _ = (A * T ^ e) * Z ^ e := by rw [Real.mul_rpow hT.le (by linarith)]; ring
    have hx : 2 * max 1 (C.N / norm C.d) ≤ 2 * Z := by
      have hd : C.N / norm C.d ≤ C.N := (div_le_self (by linarith) hn)
      exact mul_le_mul_of_nonneg_left (max_le hZ (hd.trans hNZ)) (by norm_num)
    have hl : (Vendor.dyadicLength (2 * max 1 (C.N / norm C.d)) + 1 : ℝ) ≤ H * Z ^ e := by
      calc _ ≤ L * (2 * max 1 (C.N / norm C.d)) ^ e :=
          Vendor.dyadicLength_small_power he (by
            have := le_max_left (1 : ℝ) (C.N / norm C.d); linarith)
        _ ≤ L * (2 * Z) ^ e := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hx he.le) hL.le
        _ = H * Z ^ e := by dsimp [H]; rw [Real.mul_rpow (by norm_num) (by linarith)]; ring
    have hc : ((ErrorRectangles.directRectangles C B).card : ℝ) ≤ (H * Z ^ e) ^ 2 :=
      (rectangle_card_le C B).trans (pow_le_pow_left₀ (by positivity) hl 2)
    have hf0 : 0 ≤ fixedDivisorMass C := by
      unfold fixedDivisorMass
      exact Finset.sum_nonneg (fun f _ => by dsimp [norm]; positivity)
    calc residueMagnitude C * fixedDivisorMass C * ((ErrorRectangles.directRectangles C B).card : ℝ)
        ≤ (R * ((A * T ^ e) * Z ^ e)) * (H * Z ^ e) ^ 2 :=
          mul_le_mul (mul_le_mul hr hf hf0 hR.le) hc (by positivity) (by positivity)
      _ = (R * (A * T ^ e) * H ^ 2) * Z ^ η := by
        have hp : Z ^ e * Z ^ e * Z ^ e = Z ^ η := by
          rw [← Real.rpow_add (by linarith : 0 < Z), ← Real.rpow_add (by linarith : 0 < Z)]
          congr 1
          dsimp [e]
          ring
        calc _ = (R * (A * T ^ e) * H ^ 2) * (Z ^ e * Z ^ e * Z ^ e) := by ring
          _ = _ := by rw [hp]
  · refine ⟨1, zero_lt_one, ?_⟩
    intro C hD hW
    exact False.elim (hex ⟨C, hD, hW⟩)

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirect

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirect

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def incidenceEnergy (C : Context Q) (P : ℝ) : ℝ :=
  ∑ u ∈ C.columns,
    (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card *
      (((divisorBin (F := F) P).filter (fun f => f ∣ u)).card : ℝ) *
        ‖C.lam (C.d * u)‖ ^ 2

private lemma col_data (C : Context Q) {u : Ideal (𝓞 F)} (hu : u ∈ C.columns) :
    u ≠ ⊥ ∧ Squarefree u ∧ u ⊔ c = ⊤ ∧ Squarefree (C.d * u) ∧
      (C.d * u) ⊔ c = ⊤ ∧ Q.cls (C.d * u) = C.g := by
  obtain ⟨ha, hb, hg⟩ := Finset.mem_filter.mp hu
  obtain ⟨hs, hc, -⟩ := (Sieve.mem_idealAdmissibleFinset F c _ _).mp ha
  obtain ⟨hds, hdc, -, -⟩ := (Sieve.mem_paperShell F c _ _).mp hb
  exact ⟨hs.ne_zero, hs, hc, hds, hdc, hg⟩

private lemma valid_iff (C : Context Q) {u v : Ideal (𝓞 F)}
    (hu : u ∈ C.columns) (hv : v ∈ C.columns) :
    C.ValidPair (u,v) ↔ u ⊔ v = ⊤ ∧ (u ≠ ⊤ ∨ v ≠ ⊤) := by
  obtain ⟨hu0, hus, huc, hdus, hduc, hgu⟩ := col_data C hu
  obtain ⟨hv0, hvs, hvc, hdvs, hdvc, hgv⟩ := col_data C hv
  constructor
  · intro h
    refine ⟨h.huv, ?_⟩
    by_contra hn
    push Not at hn
    exact h.offDiagonal (by simp [hn.1, hn.2])
  · rintro ⟨huv, hoff⟩
    have hdu := IsRelPrime.of_squarefree_mul hdus
    have hdv := IsRelPrime.of_squarefree_mul hdvs
    have hduv : C.d ⊔ u * v = ⊤ :=
      Ideal.isUnit_iff.mp ((hdu.mul_right hdv)
        (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))
    have hclass : Q.cls (C.d * u) = Q.cls (C.d * v) := hgu.trans hgv.symm
    have hquot : Q.cls u = Q.cls v := by
      letI := Q.instGroup
      apply mul_left_cancel (a := Q.cls C.d)
      rw [← Q.cls_mul C.d u C.hdc huc, ← Q.cls_mul C.d v C.hdc hvc]
      exact hclass
    refine ⟨hu0, hv0, hus, hvs, huc, hvc, hdus, hdvs, hduc, hdvc,
      huv, hduv, hclass, hquot, ?_⟩
    intro htop
    have hut : u = ⊤ := top_unique (htop.symm.trans_le Ideal.mul_le_left)
    have hvt : v = ⊤ := top_unique (htop.symm.trans_le Ideal.mul_le_right)
    rcases hoff with h | h <;> contradiction

private lemma row_data (C : Context Q) (B : ℝ) (unit : Bool)
    (hunit : unit = true → B = 1) (hB : 1 ≤ B) {a : Ideal (𝓞 F)}
    (ha : a ∈ C.originalRows B unit) :
    a ∈ Sieve.idealAdmissibleFinset F c (2 * B) ∧ a ⊔ (c * C.d) = ⊤ := by
  cases unit
  · obtain ⟨ha, -⟩ := Finset.mem_filter.mp ha
    obtain ⟨hs, hc, -, hn⟩ := (Sieve.mem_paperShell F (c * C.d) B _).mp ha
    refine ⟨(Sieve.mem_idealAdmissibleFinset F c _ _).mpr ⟨hs, ?_, hn⟩, hc⟩
    exact top_unique (hc.symm.trans_le (sup_le_sup_left Ideal.mul_le_left a))
  · have hBeq := hunit rfl
    have hat : a = ⊤ := Finset.mem_singleton.mp (Finset.mem_filter.mp ha).1
    subst a
    constructor
    · apply (Sieve.mem_idealAdmissibleFinset F c _ _).mpr
      refine ⟨by simpa only [← Ideal.one_eq_top] using squarefree_one, by simp, ?_⟩
      simp [hBeq]
    · simp

private lemma pair_sum_as_product (C : Context Q) (B : ℝ) (unit : Bool)
    (hunit : unit = true → B = 1) (hB : 1 ≤ B)
    (a : Ideal (𝓞 F)) (ha : a ∈ C.originalRows B unit) (f₁ f₂ : Ideal (𝓞 F)) :
    C.pairSum (fun p hp => if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then
      C.coefficient p * C.primitive p hp a else 0) =
    ∑ u ∈ C.columns, ∑ v ∈ C.columns,
      if u ⊔ v = ⊤ ∧ (u ≠ ⊤ ∨ v ≠ ⊤) ∧ f₁ ∣ u ∧ f₂ ∣ v then
        C.lam (C.d * u) * starRingEnd ℂ (C.lam (C.d * v)) *
          (Q.χ u) a * starRingEnd ℂ ((Q.χ v) a) else 0 := by
  unfold Context.pairSum Context.pairs
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have hiff := valid_iff C hu hv
  by_cases hp : C.ValidPair (u,v)
  · have hprim := (C.primitive_spec (u,v) hp).2.2 a (row_data C B unit hunit hB ha).2
    simp only [if_pos hp, dif_pos hp, hiff.mp hp, true_and, and_true]
    rw [hprim.2]
    by_cases hf : f₁ ∣ u ∧ f₂ ∣ v
    · simp only [if_pos hf, Context.coefficient]
      change C.lam (C.d * u) * starRingEnd ℂ (C.lam (C.d * v)) *
        ((Q.χ u) a * starRingEnd ℂ ((Q.χ v) a)) = _
      ring
    · simp [hf]
  · have hn : ¬(u ⊔ v = ⊤ ∧ (u ≠ ⊤ ∨ v ≠ ⊤)) := mt hiff.mpr hp
    simp only [if_neg hp]
    rw [if_neg (by tauto)]

 def coprimeMass (C : Context Q) (B : ℝ) (unit : Bool) (P : ℝ × ℝ)
    (U V : Finset (Ideal (𝓞 F))) : ℝ :=
  Sieve.DivisorSeparation.idealDivisorRectangle F c Q
    (divisorBin P.1) (divisorBin P.2) (C.originalRows B unit) U V
    (fun u => C.lam (C.d * u)) (fun u => C.lam (C.d * u))

private lemma rectangleMass_le (C : Context Q) (B : ℝ) (unit : Bool)
    (hunit : unit = true → B = 1) (hB : 1 ≤ B) (P : ℝ × ℝ) :
    rectangleMass C B unit P ≤
      coprimeMass C B unit P (C.columns.filter (fun u => u ≠ ⊤)) C.columns +
      coprimeMass C B unit P (C.columns.filter (fun u => u = ⊤))
        (C.columns.filter (fun v => v ≠ ⊤)) := by
  unfold rectangleMass coprimeMass Sieve.DivisorSeparation.idealDivisorRectangle
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro f₁ hf₁
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro f₂ hf₂
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  rw [pair_sum_as_product C B unit hunit hB a ha]
  rw [Finset.sum_filter, Finset.sum_filter]
  simp only [Finset.sum_filter]
  apply le_trans (b := ‖(∑ u ∈ C.columns, ∑ v ∈ C.columns,
      if u ⊔ v = ⊤ ∧ (u ≠ ⊤ ∨ v ≠ ⊤) ∧ f₁ ∣ u ∧ f₂ ∣ v then
        C.lam (C.d * u) * starRingEnd ℂ (C.lam (C.d * v)) *
          (Q.χ u) a * starRingEnd ℂ ((Q.χ v) a) else 0)‖) (le_refl _)
  have he : (∑ u ∈ C.columns, ∑ v ∈ C.columns,
      if u ⊔ v = ⊤ ∧ (u ≠ ⊤ ∨ v ≠ ⊤) ∧ f₁ ∣ u ∧ f₂ ∣ v then
        C.lam (C.d * u) * starRingEnd ℂ (C.lam (C.d * v)) *
          (Q.χ u) a * starRingEnd ℂ ((Q.χ v) a) else 0) =
      (∑ u ∈ C.columns, if u ≠ ⊤ then ∑ v ∈ C.columns,
        if u ⊔ v = ⊤ ∧ f₁ ∣ u ∧ f₂ ∣ v then
          C.lam (C.d * u) * starRingEnd ℂ (C.lam (C.d * v)) *
            (Q.χ u) a * starRingEnd ℂ ((Q.χ v) a) else 0 else 0) +
      (∑ u ∈ C.columns, if u = ⊤ then ∑ v ∈ C.columns,
        if v ≠ ⊤ then if u ⊔ v = ⊤ ∧ f₁ ∣ u ∧ f₂ ∣ v then
          C.lam (C.d * u) * starRingEnd ℂ (C.lam (C.d * v)) *
            (Q.χ u) a * starRingEnd ℂ ((Q.χ v) a) else 0 else 0 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hut : u = ⊤
    · simp only [hut, ne_eq, not_true_eq_false, if_false, if_true, zero_add]
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hvt : v = ⊤ <;> simp [hvt]
    · simp only [hut, ne_eq, not_false_eq_true, if_false, if_true, add_zero, true_or, true_and]
  rw [he]
  exact norm_add_le _ _

private lemma U_nonneg (B X : ℝ) : 0 ≤ ErrorRectangles.U Q B X := by
  exact Real.sSup_nonneg' ⟨0, Or.inl rfl, le_rfl⟩

private lemma incidence_nonneg (C : Context Q) (P : ℝ) : 0 ≤ incidenceEnergy C P := by
  unfold incidenceEnergy
  positivity

private lemma coprimeMass_bound (C : Context Q) (B : ℝ) (unit : Bool) (P : ℝ × ℝ)
    (hP₁ : 1 ≤ P.1) (hP₂ : 1 ≤ P.2)
    (H K : ℝ) (hH : 1 ≤ H) (hK : 1 ≤ K)
    (hcard : ∀ X : ℝ, 1 ≤ X → ((divisorBin (F := F) X).card : ℝ) ≤ 2 * H * X)
    (hOp : ∀ P₀ ∈ ({P.1, P.2} : Finset ℝ), ∀ f ∈ divisorBin (F := F) P₀,
      ∀ V : Finset (Ideal (𝓞 F)), V ⊆ C.columns → ∀ z : Ideal (𝓞 F) → ℂ,
        (∑ a ∈ C.originalRows B unit, ‖∑ u ∈ V,
          if f ∣ u then z u * (Q.χ u) a else 0‖ ^ 2) ≤
          (K * ErrorRectangles.U Q B (C.N / (norm C.d * P₀))) * ∑ u ∈ V, ‖z u‖ ^ 2)
    (V₁ V₂ : Finset (Ideal (𝓞 F))) (hV₁ : V₁ ⊆ C.columns) (hV₂ : V₂ ⊆ C.columns) :
    coprimeMass C B unit P V₁ V₂ ≤
      2 * H * K * Real.sqrt (P.1 * P.2) *
        Real.sqrt (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
          ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) *
        Real.sqrt (incidenceEnergy C P.1 * incidenceEnergy C P.2) := by
  have hH0 : 0 ≤ H := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hp₁0 : 0 ≤ P.1 := by linarith
  have hp₂0 : 0 ≤ P.2 := by linarith
  have hi₁ := incidence_nonneg C P.1
  have hi₂ := incidence_nonneg C P.2
  have hu₁ := U_nonneg (Q := Q) B (C.N / (norm C.d * P.1))
  have hu₂ := U_nonneg (Q := Q) B (C.N / (norm C.d * P.2))
  let E (X : ℝ) (V : Finset (Ideal (𝓞 F))) : ℝ := ∑ u ∈ V,
    (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card *
      (((divisorBin (F := F) X).filter (fun f => f ∣ u)).card : ℝ) *
        ‖C.lam (C.d * u)‖ ^ 2
  have hE0 : ∀ X V, 0 ≤ E X V := by intros; unfold E; positivity
  have hE : ∀ X V, V ⊆ C.columns → E X V ≤ incidenceEnergy C X := by
    intros X V hv
    exact Finset.sum_le_sum_of_subset_of_nonneg hv (by intros; positivity)
  have hh := Sieve.DivisorSeparation.rectangle_operator_bound Q
    (divisorBin P.1) (divisorBin P.2) (C.originalRows B unit) V₁ V₂
    (fun u hu => (col_data C (hV₁ hu)).1) (fun u hu => (col_data C (hV₂ hu)).1)
    (K * ErrorRectangles.U Q B (C.N / (norm C.d * P.1)))
    (K * ErrorRectangles.U Q B (C.N / (norm C.d * P.2)))
    (mul_nonneg hK0 (U_nonneg _ _)) (mul_nonneg hK0 (U_nonneg _ _))
    (fun f hf z => hOp P.1 (by simp) f hf V₁ hV₁ z)
    (fun f hf z => hOp P.2 (by simp) f hf V₂ hV₂ z)
    (fun u => C.lam (C.d * u)) (fun u => C.lam (C.d * u))
  change coprimeMass C B unit P V₁ V₂ ^ 2 ≤ _ at hh
  have hsq : coprimeMass C B unit P V₁ V₂ ^ 2 ≤
      (2 * H * P.1) * (2 * H * P.2) *
        (K * ErrorRectangles.U Q B (C.N / (norm C.d * P.1))) *
        (K * ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) *
        incidenceEnergy C P.1 * incidenceEnergy C P.2 := by
    apply hh.trans
    change _ * E P.1 V₁ * E P.2 V₂ ≤ _
    have hu₁ := U_nonneg (Q := Q) B (C.N / (norm C.d * P.1))
    have hu₂ := U_nonneg (Q := Q) B (C.N / (norm C.d * P.2))
    exact mul_le_mul
      (mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul (hcard _ hP₁) (hcard _ hP₂) (Nat.cast_nonneg _) (by positivity))
            (mul_nonneg hK0 hu₁)) (mul_nonneg hK0 hu₂))
        (hE _ _ hV₁) (hE0 _ _) (by positivity))
      (hE _ _ hV₂) (hE0 _ _) (by positivity)
  apply Real.le_sqrt_of_sq_le at hsq
  calc
    _ ≤ _ := hsq
    _ = _ := by
      rw [show (2 * H * P.1) * (2 * H * P.2) *
        (K * ErrorRectangles.U Q B (C.N / (norm C.d * P.1))) *
        (K * ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) *
        incidenceEnergy C P.1 * incidenceEnergy C P.2 =
        (2 * H * K)^2 * (P.1 * P.2) *
        (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
          ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) *
        (incidenceEnergy C P.1 * incidenceEnergy C P.2) by ring]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

private lemma rectangle_bound_from_operators (C : Context Q) (B : ℝ) (unit : Bool)
    (hunit : unit = true → B = 1) (hB : 1 ≤ B) (P : ℝ × ℝ)
    (hP : P ∈ ErrorRectangles.rectangles C)
    (H K : ℝ) (hH : 1 ≤ H) (hK : 1 ≤ K)
    (hcard : ∀ X : ℝ, 1 ≤ X → ((divisorBin (F := F) X).card : ℝ) ≤ 2 * H * X)
    (hOp : ∀ P₀ ∈ ({P.1, P.2} : Finset ℝ), ∀ f ∈ divisorBin (F := F) P₀,
      ∀ V : Finset (Ideal (𝓞 F)), V ⊆ C.columns → ∀ z : Ideal (𝓞 F) → ℂ,
        (∑ a ∈ C.originalRows B unit, ‖∑ u ∈ V,
          if f ∣ u then z u * (Q.χ u) a else 0‖ ^ 2) ≤
          (K * ErrorRectangles.U Q B (C.N / (norm C.d * P₀))) * ∑ u ∈ V, ‖z u‖ ^ 2) :
    rectangleMass C B unit P / (P.1 * P.2) ≤
      4 * H * K * ErrorRectangles.largeScore C B P *
        Real.sqrt (incidenceEnergy C P.1 * incidenceEnergy C P.2) := by
  obtain ⟨hp₁, hp₂, -⟩ := ErrorRectangles.rectangle_endpoints C P hP
  have hb₁ := coprimeMass_bound C B unit P hp₁ hp₂ H K hH hK hcard hOp
    (C.columns.filter (fun u => u ≠ ⊤)) C.columns (Finset.filter_subset _ _) (Finset.Subset.refl _)
  have hb₂ := coprimeMass_bound C B unit P hp₁ hp₂ H K hH hK hcard hOp
    (C.columns.filter (fun u => u = ⊤)) (C.columns.filter (fun u => u ≠ ⊤))
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsum := (rectangleMass_le C B unit hunit hB P).trans (add_le_add hb₁ hb₂)
  have hp0 : 0 < P.1 * P.2 := mul_pos (by linarith) (by linarith)
  have hs0 := Real.sqrt_pos.mpr hp0
  have hs2 := Real.sq_sqrt hp0.le
  apply (div_le_iff₀ hp0).mpr
  have he : 4 * H * K * ErrorRectangles.largeScore C B P *
        Real.sqrt (incidenceEnergy C P.1 * incidenceEnergy C P.2) * (P.1 * P.2) =
      2 * (2 * H * K * Real.sqrt (P.1 * P.2) *
        Real.sqrt (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
          ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) *
        Real.sqrt (incidenceEnergy C P.1 * incidenceEnergy C P.2)) := by
    unfold ErrorRectangles.largeScore
    conv_lhs => rw [← hs2, Real.sqrt_sq (Real.sqrt_nonneg _)]
    field_simp
    <;> ring
  rw [he]
  linarith

theorem actual_prefix_rectangle_estimate_of_operators
    (D : Sieve.AllIndexNormalizedFamilyData Q)
    (hhelper : ∀ core : D.bad = c, ∃ K : ℝ, 1 ≤ K ∧
      ∀ C : Context Q, C.D = D → ∀ B P : ℝ, 1 ≤ C.N → 1 ≤ B → 1 ≤ P →
      ∀ f : Ideal (𝓞 F), f ≠ ⊥ → P ≤ norm f →
      ∀ R V : Finset (Ideal (𝓞 F)), R ⊆ Sieve.idealAdmissibleFinset F c (2 * B) →
        V ⊆ C.columns → ∀ z : Ideal (𝓞 F) → ℂ,
        (∑ a ∈ R, ‖∑ u ∈ V, if f ∣ u then z u * (Q.χ u) a else 0‖ ^ 2) ≤
          K * ErrorRectangles.U Q B (C.N / (norm C.d * P)) * ∑ u ∈ V, ‖z u‖ ^ 2) :
      ∀ η : ℝ, 0 < η → ∃ A : ℝ, 0 < A ∧
        ∀ C : Context Q, C.D = D →
        ∀ (B : ℝ) (unit : Bool), (unit = true → B = 1) →
          1 ≤ C.M → 1 ≤ C.N → 1 ≤ B → B ≤ C.K → C.K ≤ C.M →
          1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
        ∀ P ∈ ErrorRectangles.rectangles C,
          rectangleMass C B unit P / (P.1 * P.2) ≤
            A * Real.rpow (C.M * C.N * norm C.d) η *
              ErrorRectangles.largeScore C B P *
                Real.sqrt (incidenceEnergy C P.1 * incidenceEnergy C P.2) := by
  intro η hη
  by_cases hcore : D.bad = c
  · obtain ⟨K, hK, hOp⟩ := hhelper hcore
    obtain ⟨H, hH, _, hcount⟩ := exists_ideal_count_bound_finset F
    have hcard : ∀ X : ℝ, 1 ≤ X → ((divisorBin (F := F) X).card : ℝ) ≤ 2 * H * X := by
      intro X hX
      have hh := hcount (2 * X) (by linarith) (divisorBin (F := F) X)
        (fun f hf => (mem_boundedNormIdeals.mp (Finset.mem_filter.mp hf).1))
      linarith
    refine ⟨4 * H * K, by positivity, ?_⟩
    intro C hCD B unit hunit hM hN hB hBK hKM hn hnN P hP
    obtain ⟨hp₁, hp₂, -⟩ := ErrorRectangles.rectangle_endpoints C P hP
    have hop : ∀ P₀ ∈ ({P.1, P.2} : Finset ℝ), ∀ f ∈ divisorBin (F := F) P₀,
      ∀ V : Finset (Ideal (𝓞 F)), V ⊆ C.columns → ∀ z : Ideal (𝓞 F) → ℂ,
        (∑ a ∈ C.originalRows B unit, ‖∑ u ∈ V,
          if f ∣ u then z u * (Q.χ u) a else 0‖ ^ 2) ≤
          (K * ErrorRectangles.U Q B (C.N / (norm C.d * P₀))) * ∑ u ∈ V, ‖z u‖ ^ 2 := by
      intro P₀ hP₀ f hf V hV z
      have hp₀ : 1 ≤ P₀ := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hP₀
        rcases hP₀ with rfl | rfl <;> assumption
      obtain ⟨hf0, hlow, -⟩ := (Finset.mem_filter.mp hf).2
      have hlow' : P₀ ≤ norm f := by
        split_ifs at hlow with h
        · simpa [h] using hlow
        · exact hlow.le
      exact hOp C hCD B P₀ hN hB hp₀ f hf0 hlow' (C.originalRows B unit) V
        (fun a ha => (row_data C B unit hunit hB ha).1) hV z
    have hb := rectangle_bound_from_operators C B unit hunit hB P hP H K hH hK hcard hop
    have hpow : 1 ≤ Real.rpow (C.M * C.N * norm C.d) η :=
      Real.one_le_rpow (by nlinarith [mul_le_mul hM hN zero_le_one (by linarith : 0 ≤ C.M)]) hη.le
    apply hb.trans
    have hscore : 0 ≤ ErrorRectangles.largeScore C B P := by
      unfold ErrorRectangles.largeScore; positivity
    have hge := Real.sqrt_nonneg (incidenceEnergy C P.1 * incidenceEnergy C P.2)
    have hHK : 0 ≤ 4 * H * K := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hpow
      (mul_nonneg (mul_nonneg hHK hscore) hge)]
  · refine ⟨1, zero_lt_one, ?_⟩
    intro C hCD
    exact False.elim (hcore (hCD ▸ C.core))

theorem actual_prefix_rectangle_estimate
    (D : Sieve.AllIndexNormalizedFamilyData Q) :
    ∀ η : ℝ, 0 < η → ∃ A : ℝ, 0 < A ∧
      ∀ C : Context Q, C.D = D →
      ∀ (B : ℝ) (unit : Bool), (unit = true → B = 1) →
        1 ≤ C.M → 1 ≤ C.N → 1 ≤ B → B ≤ C.K → C.K ≤ C.M →
        1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
      ∀ P ∈ ErrorRectangles.rectangles C,
        rectangleMass C B unit P / (P.1 * P.2) ≤
          A * Real.rpow (C.M * C.N * norm C.d) η *
            ErrorRectangles.largeScore C B P *
              Real.sqrt (incidenceEnergy C P.1 * incidenceEnergy C P.2) := by
  apply actual_prefix_rectangle_estimate_of_operators D
  intro core
  obtain ⟨K, hK, hop⟩ := DivisiblePrefix.realized_divisible_column_U D core
  refine ⟨K, hK, ?_⟩
  intro C hCD B P hN hB hP f hf0 hPf R V hR hV z
  by_cases hfV : ∃ u ∈ V, f ∣ u
  · obtain ⟨u, hu, hfu⟩ := hfV
    obtain ⟨_, hus, huc, _⟩ := col_data C (hV hu)
    have hfsf := hus.squarefree_of_dvd hfu
    have hfc : f ⊔ c = ⊤ := top_unique
      (huc.symm.trans_le (sup_le_sup_right (Ideal.dvd_iff_le.mp hfu) c))
    have hb := hop C hCD hN B P hB hP f hf0 hfsf hfc hPf R V hR hV
      (fun _ => 1) (fun _ => 1) z (by simp) (by simp)
    simp only [one_mul, mul_one] at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith) (U_nonneg _ _))
    apply Finset.sum_le_sum
    intro u hu
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  · have hz : (∑ a ∈ R, ‖∑ u ∈ V,
        if f ∣ u then z u * (Q.χ u) a else 0‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have hs : (∑ u ∈ V, if f ∣ u then z u * (Q.χ u) a else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro u hu
        exact if_neg (fun hd => hfV ⟨u, hu, hd⟩)
      simp [hs]
    rw [hz]
    exact mul_nonneg (mul_nonneg (by linarith) (U_nonneg _ _)) (by positivity)

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirect

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirect

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private lemma primeSupportCost_le_divisorCount {F : Type} [Field F] [NumberField F]
    (u : Ideal (𝓞 F)) (hu : u ≠ ⊥) :
    (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card ≤ (DedekindZetaZeroFree.LargeSieve.idealDivisorCount u : ℝ) := by
  classical
  set m := UniqueFactorizationMonoid.normalizedFactors u with hm
  set S := m.toFinset with hS
  have hmem : ∀ p : Ideal (𝓞 F), p ∈ S ↔ p ∈ m := fun p => Multiset.mem_toFinset
  have hprime : ∀ p ∈ S, Irreducible p := fun p hp =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor p ((hmem p).mp hp)
  have hnorm : ∀ p ∈ S, normalize p = p := fun p hp =>
    UniqueFactorizationMonoid.normalize_normalized_factor p ((hmem p).mp hp)
  have key : ∀ s : Finset (Ideal (𝓞 F)), s ⊆ S →
      UniqueFactorizationMonoid.normalizedFactors (∏ p ∈ s, p) = s.val := by
    intro s hs
    have hirr : ∀ p ∈ s.val, Irreducible p := by
      intro p hp
      exact hprime p (hs (by simpa using hp))
    have h1 := UniqueFactorizationMonoid.normalizedFactors_prod_eq s.val hirr
    have hprod : (∏ p ∈ s, p) = s.val.prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    rw [hprod, h1]
    rw [Multiset.map_congr rfl (fun p hp => hnorm p (hs (by simpa using hp))),
      Multiset.map_id']
  have hinj : Set.InjOn (fun s : Finset (Ideal (𝓞 F)) => ∏ p ∈ s, p)
      (↑S.powerset : Set (Finset (Ideal (𝓞 F)))) := by
    intro s hs t ht hst
    have hssub : s ⊆ S := Finset.mem_powerset.mp hs
    have htsub : t ⊆ S := Finset.mem_powerset.mp ht
    have hsval : UniqueFactorizationMonoid.normalizedFactors (∏ p ∈ s, p) = s.val :=
      key s hssub
    have htval : UniqueFactorizationMonoid.normalizedFactors (∏ p ∈ t, p) = t.val :=
      key t htsub
    have hst' : (∏ p ∈ s, p) = (∏ p ∈ t, p) := hst
    rw [hst'] at hsval
    exact Finset.val_inj.mp (hsval.symm.trans htval)
  have hmaps : Set.MapsTo (fun s : Finset (Ideal (𝓞 F)) => ∏ p ∈ s, p)
      (↑S.powerset : Set (Finset (Ideal (𝓞 F))))
      (↑(DedekindZetaZeroFree.LargeSieve.idealDivisors u) : Set (Ideal (𝓞 F))) := by
    intro s hs
    change (∏ p ∈ s, p) ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors u
    rw [DedekindZetaZeroFree.LargeSieve.mem_idealDivisors hu]
    have hssub : s ⊆ S := Finset.mem_powerset.mp hs
    have hle : s.val ≤ m := by
      rw [Multiset.le_iff_subset s.nodup]
      intro p hp
      exact (hmem p).mp (hssub (by simpa using hp))
    have hprod : (∏ p ∈ s, p) = s.val.prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    rw [hprod, ← Ideal.prod_normalizedFactors_eq_self hu]
    exact Multiset.prod_dvd_prod_of_le hle
  have hcard : S.powerset.card ≤ (DedekindZetaZeroFree.LargeSieve.idealDivisors u).card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  have hcost : (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card = (2 : ℝ) ^ S.card := by
    rw [hS, ← hm]
  rw [hcost]
  have hpc : ((S.powerset.card : ℕ) : ℝ) = (2 : ℝ) ^ S.card := by
    rw [Finset.card_powerset]
    push_cast
    ring
  rw [← hpc]
  exact_mod_cast hcard

private lemma column_energy_le (C : Context Q) :
    (∑ u ∈ C.columns, ‖C.lam (C.d * u)‖ ^ 2) ≤ Sieve.energy F c C.N C.lam := by
  apply Finset.sum_le_sum_of_injOn (fun u => C.d * u)
  · intro u _ v _ huv
    exact mul_left_cancel₀ C.hd0 huv
  · intro b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
    exact (Finset.mem_filter.mp hu).2.1
  · intro u hu
    exact le_rfl
  · intro b _ _
    exact sq_nonneg _

private lemma incidence_energy_le (η A : ℝ) (hη : 0 < η) (hA : 1 ≤ A)
    (hcount : ∀ u : Ideal (𝓞 F), (idealDivisorCount u : ℝ) ≤ A * norm u ^ η)
    (C : Context Q) (hN : 1 ≤ C.N) (hn : 1 ≤ norm C.d) (P : ℝ) :
    incidenceEnergy C P ≤ (A * (2 * C.N) ^ η) ^ 2 * Sieve.energy F c C.N C.lam := by
  let L := A * (2 * C.N) ^ η
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hu0 : ∀ u ∈ C.columns, u ≠ ⊥ := by
    intro u hu
    exact ((Sieve.mem_idealAdmissibleFinset _ _ _ _).mp (Finset.mem_filter.mp hu).1).1.ne_zero
  have hcnt : ∀ u ∈ C.columns, (idealDivisorCount u : ℝ) ≤ L := by
    intro u hu
    have huN := ((Sieve.mem_idealAdmissibleFinset _ _ _ _).mp (Finset.mem_filter.mp hu).1).2.2
    have hn0 : 0 < norm C.d := by linarith
    have hnorm : norm u ≤ 2 * C.N := by
      have hh := (le_div_iff₀ hn0).mp huN
      change norm u * norm C.d ≤ 2 * C.N at hh
      have hu_non : 0 ≤ norm u := Nat.cast_nonneg _
      nlinarith
    exact (hcount u).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hη.le) (by linarith))
  have hcard : ∀ u ∈ C.columns,
      (((divisorBin (F := F) P).filter (fun f => f ∣ u)).card : ℝ) ≤ L := by
    intro u hu
    have hc : ((divisorBin (F := F) P).filter (fun f => f ∣ u)).card ≤ (idealDivisors u).card := by
      apply Finset.card_le_card
      intro f hf
      exact (mem_idealDivisors (hu0 u hu)).mpr (Finset.mem_filter.mp hf).2
    exact (by exact_mod_cast hc : _ ≤ (idealDivisorCount u : ℝ)).trans (hcnt u hu)
  unfold incidenceEnergy
  calc
    _ ≤ ∑ u ∈ C.columns, L ^ 2 * ‖C.lam (C.d * u)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      have hs := (primeSupportCost_le_divisorCount u (hu0 u hu)).trans (hcnt u hu)
      have hc := hcard u hu
      nlinarith [mul_le_mul hc hs (by positivity : 0 ≤ (2 : ℝ) ^
        (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card) hL,
        sq_nonneg ‖C.lam (C.d * u)‖]
    _ = L ^ 2 * ∑ u ∈ C.columns, ‖C.lam (C.d * u)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (column_energy_le C) (sq_nonneg _)

theorem incidence_energy_epsilon (η : ℝ) (hη : 0 < η) :
    ∃ I : ℝ, 1 ≤ I ∧ ∀ C : Context Q,
      1 ≤ C.M → 1 ≤ C.N → 1 ≤ norm C.d →
      ∀ P₁ P₂ : ℝ,
        Real.sqrt (incidenceEnergy C P₁ * incidenceEnergy C P₂) ≤
          I * Real.rpow (C.M * C.N * norm C.d) η *
            Sieve.energy F c C.N C.lam := by
  obtain ⟨A, hA, hcount⟩ := ideal_divisor_count_le_rpow F (η / 2) (by linarith)
  let I := (A * (2 : ℝ) ^ (η / 2)) ^ 2
  have hI : 1 ≤ I := by
    apply one_le_pow₀
    exact one_le_mul_of_one_le_of_one_le hA
      (Real.one_le_rpow (by norm_num) (by linarith))
  refine ⟨I, hI, ?_⟩
  intro C hM hN hn P₁ P₂
  let T := C.M * C.N * norm C.d
  let E := Sieve.energy F c C.N C.lam
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hNle : C.N ≤ T := by
    dsimp [T]
    exact (le_mul_of_one_le_left (by linarith) hM).trans
      (le_mul_of_one_le_right (by positivity) hn)
  have hbound : ∀ P : ℝ, incidenceEnergy C P ≤ I * T ^ η * E := by
    intro P
    have hh := incidence_energy_le (η / 2) A (by linarith) hA hcount C hN hn P
    have hp : (2 * C.N) ^ (η / 2) ≤ (2 : ℝ) ^ (η / 2) * T ^ (η / 2) := by
      rw [Real.mul_rpow (by norm_num) (by linarith)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by linarith) hNle (by linarith)) (by positivity)
    calc
      _ ≤ _ := hh
      _ ≤ (A * ((2 : ℝ) ^ (η / 2) * T ^ (η / 2))) ^ 2 * E := by
        apply mul_le_mul_of_nonneg_right _ hE
        exact pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left hp (by linarith)) 2
      _ = I * (T ^ (η / 2)) ^ 2 * E := by dsimp [I]; ring
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hT0]; congr 2; ring
  have hnonneg : ∀ P : ℝ, 0 ≤ incidenceEnergy C P := by
    intro P
    unfold incidenceEnergy
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  change Real.sqrt (incidenceEnergy C P₁ * incidenceEnergy C P₂) ≤ I * T ^ η * E
  have hB : 0 ≤ I * T ^ η * E :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hT0 η)) hE
  apply Real.sqrt_le_iff.mpr
  refine ⟨hB, ?_⟩
  rw [pow_two]
  exact mul_le_mul (hbound P₁) (hbound P₂) (hnonneg P₂) hB

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirect

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

theorem bilinear_error_large_direct
    (D : Sieve.AllIndexNormalizedFamilyData Q) (W : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
      ∀ C : Context Q, C.D = D → C.W = W → C.δ = δ →
      ∀ (B : ℝ) (unit : Bool), (unit = true → B = 1) →
        1 ≤ C.M → 1 ≤ C.N → 1 ≤ B → B ≤ C.K → C.K ≤ C.M →
        1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
        ‖E4 C B unit‖ ≤ A * Real.rpow (C.M * C.N * norm C.d) ε *
          Real.sqrt (C.M / B) * ErrorRectangles.directEnvelope C B *
          Sieve.energy F c C.N C.lam := by
  intro ε hε
  let η := ε / 3
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨A₀, hA₀, hrect⟩ :=
    LargeDirect.actual_prefix_rectangle_estimate D η hη
  obtain ⟨I, hI, hinc⟩ :=
    LargeDirect.incidence_energy_epsilon (Q := Q) η hη
  obtain ⟨J, hJ, hfixed⟩ := LargeDirect.fixed_cost_epsilon D W η hη
  refine ⟨A₀ * I * J, by positivity, ?_⟩
  intro C hCD hCW hCδ B unit hunit hM hN hB hBK hKM hn hnN
  have hδC : 0 < C.δ := by simpa [hCδ] using hδ
  have hX : 0 < C.M * C.N * norm C.d := by
    have hM0 : 0 < C.M := by linarith
    have hN0 : 0 < C.N := by linarith
    have hn0 : 0 < norm C.d := by linarith
    positivity
  let X := C.M * C.N * norm C.d
  change 0 < X at hX
  have hp : 0 ≤ Real.rpow X η := Real.rpow_nonneg hX.le _
  have hI0 : 0 ≤ I := le_trans zero_le_one hI
  let T := ErrorRectangles.directRectangles C B
  let E := Sieve.energy F c C.N C.lam
  let V := ErrorRectangles.directEnvelope C B
  have hE : 0 ≤ E := by
    dsimp [E, Sieve.energy]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsupbdd : BddAbove ({0} ∪ {x : ℝ | ∃ P ∈ T,
      x = ErrorRectangles.largeScore C B P}) := by
    have hf : ({x : ℝ | ∃ P ∈ T,
        x = ErrorRectangles.largeScore C B P} : Set ℝ) =
        ErrorRectangles.largeScore C B '' (T : Set (ℝ × ℝ)) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨P, hP, rfl⟩
        exact ⟨P, hP, rfl⟩
      · rintro ⟨P, hP, rfl⟩
        exact ⟨P, hP, rfl⟩
    rw [hf]
    exact ((Set.finite_singleton 0).union (T.finite_toSet.image _)).bddAbove
  have hV : 0 ≤ V := by
    exact le_csSup hsupbdd (Or.inl rfl)
  have hscore : ∀ P ∈ T, ErrorRectangles.largeScore C B P ≤ V := by
    intro P hP
    exact le_csSup hsupbdd (Or.inr ⟨P, hP, rfl⟩)
  have hterm : ∀ P ∈ T,
      LargeDirect.rectangleMass C B unit P / (P.1 * P.2) ≤
        A₀ * Real.rpow X η * V * (I * Real.rpow X η * E) := by
    intro P hP
    have hh := hrect C hCD B unit hunit hM hN hB hBK hKM hn hnN P
      (Finset.mem_filter.mp hP).1
    have hi := hinc C hM hN hn P.1 P.2
    have hs : 0 ≤ ErrorRectangles.largeScore C B P := by
      unfold ErrorRectangles.largeScore
      positivity
    calc
      _ ≤ A₀ * Real.rpow X η * ErrorRectangles.largeScore C B P *
            Real.sqrt (LargeDirect.incidenceEnergy C P.1 *
              LargeDirect.incidenceEnergy C P.2) := hh
      _ ≤ A₀ * Real.rpow X η * V * (I * Real.rpow X η * E) := by
        gcongr
        exact hscore P hP
  have hsum : (∑ P ∈ T,
      LargeDirect.rectangleMass C B unit P / (P.1 * P.2)) ≤
        (T.card : ℝ) * (A₀ * Real.rpow X η * V * (I * Real.rpow X η * E)) := by
    calc
      _ ≤ ∑ _P ∈ T, A₀ * Real.rpow X η * V * (I * Real.rpow X η * E) :=
        Finset.sum_le_sum hterm
      _ = _ := by simp
  have hr : 0 ≤ LargeDirect.residueMagnitude C := norm_nonneg _
  have hf : 0 ≤ LargeDirect.fixedDivisorMass C := by
    unfold LargeDirect.fixedDivisorMass
    apply Finset.sum_nonneg
    intro f _
    unfold norm
    positivity
  have hcost := hfixed C hCD hCW hM hN hn B
  have hpows : Real.rpow X η * Real.rpow X η * Real.rpow X η =
      Real.rpow X ε := by
    change X ^ η * X ^ η * X ^ η = X ^ ε
    rw [← Real.rpow_add hX, ← Real.rpow_add hX]
    congr 1
    dsimp [η]
    ring
  calc
    ‖E4 C B unit‖ ≤ Real.sqrt (C.M / B) *
        (LargeDirect.residueMagnitude C * LargeDirect.fixedDivisorMass C *
          ∑ P ∈ T, LargeDirect.rectangleMass C B unit P / (P.1 * P.2)) :=
      LargeDirect.large_divisor_expansion C B unit hunit hM hN hδC hB hBK hKM hn hnN
    _ ≤ Real.sqrt (C.M / B) *
        (LargeDirect.residueMagnitude C * LargeDirect.fixedDivisorMass C *
          ((T.card : ℝ) * (A₀ * Real.rpow X η * V * (I * Real.rpow X η * E)))) := by
      gcongr
    _ = (LargeDirect.residueMagnitude C * LargeDirect.fixedDivisorMass C *
          (T.card : ℝ)) *
        (Real.sqrt (C.M / B) * A₀ * Real.rpow X η * V * (I * Real.rpow X η * E)) := by ring
    _ ≤ (J * Real.rpow X η) *
        (Real.sqrt (C.M / B) * A₀ * Real.rpow X η * V * (I * Real.rpow X η * E)) := by
      apply mul_le_mul_of_nonneg_right hcost
      positivity
    _ = (A₀ * I * J) * Real.rpow (C.M * C.N * norm C.d) ε *
        Real.sqrt (C.M / B) * ErrorRectangles.directEnvelope C B *
          Sieve.energy F c C.N C.lam := by
      change _ = (A₀ * I * J) * Real.rpow X ε * Real.sqrt (C.M / B) * V * E
      rw [← hpows]
      ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

end

end
