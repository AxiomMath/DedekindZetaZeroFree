module

public import DedekindZetaZeroFree.Arithmetic.Ideals.SquarefreeGcdDecomposition
public import DedekindZetaZeroFree.LargeSieve.Bilinear.OperatorNormBounds
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleRangeBoundaryCases
public import DedekindZetaZeroFree.LargeSieve.Bilinear.CoprimeForms.WeightedGramBound
public import DedekindZetaZeroFree.LargeSieve.Bilinear.CoprimeForms.PrimeSupportEpsilonEnergyBound

@[expose] public section

section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.Sieve.GcdTail

open scoped NumberField Classical

private theorem quotient_mem {F : Type} [Field F] [NumberField F]
    {c d u : Ideal (𝓞 F)} {N : ℝ} (hd : d ≠ ⊥)
    (h : d * u ∈ paperShell F c N) :
    u ∈ paperShell F c (N / (Ideal.absNorm d : ℝ)) := by
  obtain ⟨hs, hc, hl, hr⟩ := (mem_paperShell F c N _).mp h
  have hpos : 0 < (Ideal.absNorm d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hd)
  have hnorm : (Ideal.absNorm (d * u) : ℝ) =
      (Ideal.absNorm d : ℝ) * (Ideal.absNorm u : ℝ) := by
    rw [map_mul, Nat.cast_mul]
  refine (mem_paperShell F c _ _).mpr ⟨hs.squarefree_of_dvd (dvd_mul_left u d), ?_, ?_, ?_⟩
  · exact top_unique (hc.symm.trans_le (sup_le_sup_right Ideal.mul_le_right c))
  · exact (div_lt_iff₀' hpos).mpr (hnorm ▸ hl)
  · rw [← mul_div_assoc]
    exact (le_div_iff₀ hpos).mpr (by rw [mul_comm]; exact hnorm ▸ hr)

private theorem divisor_sum {F : Type} [Field F] [NumberField F]
    {Z : Type*} [AddCommMonoid Z] (c d : Ideal (𝓞 F)) (N : ℝ) (hd : d ≠ ⊥)
    (f : Ideal (𝓞 F) → Z) :
    (∑ b ∈ paperShell F c N, if d ∣ b then f b else 0) =
      ∑ u ∈ paperShell F c (N / (Ideal.absNorm d : ℝ)),
        if d * u ∈ paperShell F c N then f (d * u) else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply (Finset.sum_bij (i := fun u _ => d * u) ?_ ?_ ?_ ?_).symm
  · intro u hu
    obtain ⟨hu, hp⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨hp, dvd_mul_right d u⟩
  · intro u hu v hv he
    exact mul_left_cancel₀ hd he
  · intro b hb
    obtain ⟨hb, u, rfl⟩ := Finset.mem_filter.mp hb
    exact ⟨u, Finset.mem_filter.mpr ⟨quotient_mem hd hb, hb⟩, rfl⟩
  · intros; rfl

private theorem divisor_sum_of_support {F : Type} [Field F] [NumberField F]
    {Z : Type*} [AddCommMonoid Z] (c d : Ideal (𝓞 F)) (N : ℝ) (hd : d ≠ ⊥)
    (f : Ideal (𝓞 F) → Z) (hf : ∀ b, ¬ d ∣ b → f b = 0) :
    (∑ b ∈ paperShell F c N, f b) =
      ∑ u ∈ paperShell F c (N / (Ideal.absNorm d : ℝ)),
        if d * u ∈ paperShell F c N then f (d * u) else 0 := by
  convert divisor_sum c d N hd f using 1
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : d ∣ b
  · simp [h]
  · simp [h, hf b h]

private theorem divisor_pair_sum {F : Type} [Field F] [NumberField F]
    {Z : Type*} [AddCommMonoid Z] (c d : Ideal (𝓞 F)) (N : ℝ) (hd : d ≠ ⊥)
    (f : Ideal (𝓞 F) → Ideal (𝓞 F) → Z)
    (hf : ∀ b1 b2, ¬ d ∣ b1 ∨ ¬ d ∣ b2 → f b1 b2 = 0) :
    (∑ b1 ∈ paperShell F c N, ∑ b2 ∈ paperShell F c N, f b1 b2) =
      ∑ u ∈ paperShell F c (N / (Ideal.absNorm d : ℝ)),
        ∑ v ∈ paperShell F c (N / (Ideal.absNorm d : ℝ)),
          if d * u ∈ paperShell F c N ∧ d * v ∈ paperShell F c N
          then f (d * u) (d * v) else 0 := by
  rw [divisor_sum_of_support c d N hd
    (fun b1 => ∑ b2 ∈ paperShell F c N, f b1 b2)
    (fun b1 hb1 => Finset.sum_eq_zero (fun b2 _ => hf b1 b2 (Or.inl hb1)))]
  apply Finset.sum_congr rfl
  intro u hu
  rw [divisor_sum_of_support c d N hd (f (d * u))
    (fun b2 hb2 => hf (d * u) b2 (Or.inr hb2))]
  by_cases h : d * u ∈ paperShell F c N
  · simp only [h, ite_true, true_and]
  · simp [h]

private theorem gcd_mul_iff {F : Type} [Field F] [NumberField F]
    {d u v : Ideal (𝓞 F)} (hd : d ≠ ⊥) :
    d * u ⊔ d * v = d ↔ u ⊔ v = ⊤ := by
  rw [← Ideal.mul_sup]
  constructor
  · intro h
    exact mul_left_cancel₀ hd (h.trans (Ideal.mul_top d).symm)
  · intro h
    rw [h, Ideal.mul_top]

theorem quotient_reindex
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (q : Ideal (𝓞 F))
    (htransport : ∀ d u v : Ideal (𝓞 F),
      d ≠ ⊥ → u ≠ ⊥ → v ≠ ⊥ →
      Squarefree d → Squarefree u → Squarefree v →
      Squarefree (d * u) → Squarefree (d * v) →
      (d * u) ⊔ c = ⊤ → (d * v) ⊔ c = ⊤ →
      u ⊔ v = ⊤ → d ⊔ (u * v) = ⊤ →
      Q.cls (d * u) = Q.cls (d * v) →
      ∀ a : Ideal (𝓞 F), a ≠ ⊥ → a ⊔ (q * d) = ⊤ →
        (Q.χ (d * u)) a * (starRingEnd ℂ) ((Q.χ (d * v)) a) =
          (Q.χ u) a * (starRingEnd ℂ) ((Q.χ v) a))
    (M N K : ℝ) (hN : 0 < N)
    (d : Ideal (𝓞 F)) (hd : d ≠ ⊥)
    (g : Q.G) (lam : Ideal (𝓞 F) → ℂ)
    (rowMask : Ideal (𝓞 F) → ℝ) (columnMask : Ideal (𝓞 F) → ℂ)
    (hcol : ∀ b : Ideal (𝓞 F), ‖columnMask b‖ ≤ 1) :
    ∃ alpha : Ideal (𝓞 F) → ℂ,
      energy F c (N / (Ideal.absNorm d : ℝ)) alpha ≤
        (∑ b ∈ paperShell F c N, if d ∣ b then ‖lam b‖ ^ 2 else 0) ∧
      (∑ b1 ∈ paperShell F c N, ∑ b2 ∈ paperShell F c N,
        if b1 ⊔ b2 = d ∧ Q.cls b1 = g ∧ Q.cls b2 = g then
          (columnMask b1 * lam b1) * (starRingEnd ℂ) (columnMask b2 * lam b2) *
            (∑ a ∈ kernelRows F c M K,
              if a ⊔ (q * d) = ⊤ then
                (W ((Ideal.absNorm a : ℝ) / M) * rowMask a : ℂ) *
                  (Q.χ b1) a * (starRingEnd ℂ) ((Q.χ b2) a)
              else 0)
        else 0) =
        coprimeForm (kernelRows F c M K)
          (paperShell F c (N / (Ideal.absNorm d : ℝ)))
          (maskedRowWeight W q d M rowMask) (fun a u => (Q.χ u) a) alpha := by
  classical
  let S := paperShell F c N
  let U := paperShell F c (N / (Ideal.absNorm d : ℝ))
  let good := fun u : Ideal (𝓞 F) => d * u ∈ S ∧ Q.cls (d * u) = g
  let alpha := fun u : Ideal (𝓞 F) =>
    if good u then columnMask (d * u) * lam (d * u) else 0
  refine ⟨alpha, ?_, ?_⟩
  · rw [divisor_sum c d N hd]
    apply Finset.sum_le_sum
    intro u hu
    change ‖alpha u‖ ^ 2 ≤ if d * u ∈ S then ‖lam (d * u)‖ ^ 2 else 0
    by_cases h : good u
    · simp only [alpha, if_pos h, if_pos h.1, norm_mul]
      have hn : ‖columnMask (d * u)‖ * ‖lam (d * u)‖ ≤ ‖lam (d * u)‖ := by
        exact mul_le_of_le_one_left (norm_nonneg _) (hcol _)
      exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hn 2
    · simp only [alpha, if_neg h, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      split_ifs <;> positivity
  · let f := fun b1 b2 : Ideal (𝓞 F) =>
      if b1 ⊔ b2 = d ∧ Q.cls b1 = g ∧ Q.cls b2 = g then
        (columnMask b1 * lam b1) * (starRingEnd ℂ) (columnMask b2 * lam b2) *
          (∑ a ∈ kernelRows F c M K,
            if a ⊔ (q * d) = ⊤ then
              (W ((Ideal.absNorm a : ℝ) / M) * rowMask a : ℂ) *
                (Q.χ b1) a * (starRingEnd ℂ) ((Q.χ b2) a)
            else 0)
      else 0
    have hf : ∀ b1 b2, ¬ d ∣ b1 ∨ ¬ d ∣ b2 → f b1 b2 = 0 := by
      intro b1 b2 hh
      dsimp only [f]
      apply if_neg
      intro ht
      rcases hh with hh | hh
      · exact (hh (Ideal.dvd_iff_le.mpr (ht.1 ▸ le_sup_left))).elim
      · exact (hh (Ideal.dvd_iff_le.mpr (ht.1 ▸ le_sup_right))).elim
    change (∑ b1 ∈ S, ∑ b2 ∈ S, f b1 b2) = _
    rw [divisor_pair_sum c d N hd f hf]
    unfold coprimeForm
    simp_rw [Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    change (if d * u ∈ S ∧ d * v ∈ S then f (d * u) (d * v) else 0) = _
    by_cases hgu : good u
    · by_cases hgv : good v
      · by_cases huv : u ⊔ v = ⊤
        · have hpair : d * u ⊔ d * v = d ∧ Q.cls (d * u) = g ∧ Q.cls (d * v) = g :=
            ⟨(gcd_mul_iff hd).mpr huv, hgu.2, hgv.2⟩
          simp only [ite_eq_left (And.intro hgu.1 hgv.1), f, ite_eq_left hpair,
            alpha, ite_eq_left hgu, ite_eq_left hgv, ite_eq_left huv]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          by_cases haqd : a ⊔ (q * d) = ⊤
          · have hsu := (mem_paperShell F c N (d * u)).mp hgu.1
            have hsv := (mem_paperShell F c N (d * v)).mp hgv.1
            have hs := SquarefreeGcd.strip_squarefree_and_coprime hsu.1 hsv.1
              (show d * u = (d * u ⊔ d * v) * u by rw [hpair.1])
              (show d * v = (d * u ⊔ d * v) * v by rw [hpair.1])
            rw [hpair.1] at hs
            have hduv : d ⊔ (u * v) = ⊤ := by
              rw [Ideal.sup_mul_eq_of_coprime_left hs.2.2.2.2.1, hs.2.2.2.2.2]
            have hane : a ≠ ⊥ := (Finset.mem_filter.mp ha).2.1
            have htr := htransport d u v hd
              (SquarefreeGcd.ne_bot_of_squarefree hs.2.1)
              (SquarefreeGcd.ne_bot_of_squarefree hs.2.2.1)
              hs.1 hs.2.1 hs.2.2.1 hsu.1 hsv.1 hsu.2.1 hsv.2.1 huv hduv
              (hgu.2.trans hgv.2.symm) a hane haqd
            simp only [haqd, ite_true, maskedRowWeight, map_mul, Complex.ofReal_mul]
            calc
              _ = (columnMask (d * u) * lam (d * u)) *
                  (starRingEnd ℂ) (columnMask (d * v) * lam (d * v)) *
                  (W ((Ideal.absNorm a : ℝ) / M) * rowMask a : ℂ) *
                  ((Q.χ (d * u)) a * (starRingEnd ℂ) ((Q.χ (d * v)) a)) := by simp only [map_mul, Complex.ofReal_mul]; ring
              _ = _ := by
                rw [htr]
                simp only [map_mul, star_mul, Complex.ofReal_mul]
                change (columnMask (d * u) * lam (d * u)) *
                    (star (columnMask (d * v)) * star (lam (d * v))) *
                    (W ((Ideal.absNorm a : ℝ) / M) * rowMask a : ℂ) *
                    ((Q.χ u) a * star ((Q.χ v) a)) = _
                ring
          · simp [haqd, maskedRowWeight]
        · have hp : ¬ (d * u ⊔ d * v = d ∧ Q.cls (d * u) = g ∧ Q.cls (d * v) = g) :=
            fun h => huv ((gcd_mul_iff hd).mp h.1)
          simp [hgu.1, hgv.1, f, hp, huv]
      · have halpha : alpha v = 0 := by simp [alpha, hgv]
        have hp : ¬ (d * u ∈ S ∧ d * v ∈ S ∧ Q.cls (d * v) = g) :=
          fun h => hgv ⟨h.2.1, h.2.2⟩
        by_cases hvS : d * v ∈ S
        · have hvc : Q.cls (d * v) ≠ g := fun h => hgv ⟨hvS, h⟩
          simp [hgu.1, hvS, f, hvc, halpha]
        · simp [hvS, halpha]
    · have halpha : alpha u = 0 := by simp [alpha, hgu]
      by_cases huS : d * u ∈ S
      · have huc : Q.cls (d * u) ≠ g := fun h => hgu ⟨huS, h⟩
        simp [huS, f, huc, halpha]
      · simp [huS, halpha]

end DedekindZetaZeroFree.LargeSieve.Sieve.GcdTail

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.Sieve.GcdTail

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

private lemma exists_sieveWeight_bound (W : ℝ → ℝ) (hW : SieveWeight W) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, W t ≤ B := by
  obtain ⟨x, _hx, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (by norm_num : (1 / 2 : ℝ) ≤ 5 / 2))
      hW.smooth.continuous.continuousOn
  refine ⟨W x, hW.nonneg x, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (1 / 2 : ℝ) (5 / 2)
  · exact hmax ht
  · rw [hW.zero_outside t ht]
    exact hW.nonneg x

private lemma maskedRowWeight_nonneg (W : ℝ → ℝ) (hW : SieveWeight W)
    (q d : Ideal (𝓞 F)) (M : ℝ) (rowMask : Ideal (𝓞 F) → ℝ)
    (hrow : ∀ a : Ideal (𝓞 F), 0 ≤ rowMask a ∧ rowMask a ≤ 1) (a : Ideal (𝓞 F)) :
    0 ≤ maskedRowWeight W q d M rowMask a := by
  rw [maskedRowWeight]
  split
  · exact mul_nonneg (hW.nonneg _) (hrow a).1
  · exact le_refl 0

private lemma maskedRowWeight_le (W : ℝ → ℝ) (hW : SieveWeight W)
    (q d : Ideal (𝓞 F)) (M : ℝ) (rowMask : Ideal (𝓞 F) → ℝ)
    (hrow : ∀ a : Ideal (𝓞 F), 0 ≤ rowMask a ∧ rowMask a ≤ 1) (a : Ideal (𝓞 F)) :
    maskedRowWeight W q d M rowMask a ≤ W ((Ideal.absNorm a : ℝ) / M) := by
  rw [maskedRowWeight]
  split
  · exact mul_le_of_le_one_right (hW.nonneg _) (hrow a).2
  · exact hW.nonneg _

private lemma rowSum_sq_le {c : Ideal (𝓞 F)}
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) (T : ℝ)
    (lam : Ideal (𝓞 F) → ℂ) (a : Ideal (𝓞 F)) :
    ‖rowSum Q T lam a‖ ^ 2 ≤ ((paperShell F c T).card : ℝ) * energy F c T lam := by
  have h2 : (∑ b ∈ paperShell F c T, ‖lam b * (Q.χ b) a‖) ^ 2 ≤
      ((paperShell F c T).card : ℝ) * ∑ b ∈ paperShell F c T, ‖lam b * (Q.χ b) a‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : ∑ b ∈ paperShell F c T, ‖lam b * (Q.χ b) a‖ ^ 2 ≤
      ∑ b ∈ paperShell F c T, ‖lam b‖ ^ 2 := by
    refine Finset.sum_le_sum fun b hb => ?_
    have hb' := (mem_paperShell F c T b).mp hb
    have hchi : ‖(Q.χ b) a‖ ≤ 1 := quadraticFamily_norm_le_one Q hb'.1 hb'.2.1 a
    have hchi2 : ‖(Q.χ b) a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ((Q.χ b) a), hchi]
    rw [norm_mul, mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) hchi2
  have h1 : ‖rowSum Q T lam a‖ ^ 2 ≤
      (∑ b ∈ paperShell F c T, ‖lam b * (Q.χ b) a‖) ^ 2 := by
    rw [rowSum]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
  have h4 : ∑ b ∈ paperShell F c T, ‖lam b‖ ^ 2 = energy F c T lam := rfl
  calc ‖rowSum Q T lam a‖ ^ 2
      ≤ ((paperShell F c T).card : ℝ) * ∑ b ∈ paperShell F c T, ‖lam b * (Q.χ b) a‖ ^ 2 :=
        h1.trans h2
    _ ≤ ((paperShell F c T).card : ℝ) * ∑ b ∈ paperShell F c T, ‖lam b‖ ^ 2 :=
        mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
    _ = ((paperShell F c T).card : ℝ) * energy F c T lam := by rw [h4]

private lemma paperShell_eq_empty_or_singleton_of_lt_one {c : Ideal (𝓞 F)} {X : ℝ}
    (hX : X < 1) : paperShell F c X = ∅ ∨ paperShell F c X = {⊤} := by
  rcases lt_or_ge (2 * X) 1 with h | h
  · left
    rw [paperShell, idealAdmissibleFinset_eq_empty_of_lt_one F c (2 * X) h]
    simp
  · right
    rw [paperShell,
      idealAdmissibleFinset_eq_singleton_of_one_le_of_lt_two F c (2 * X) h (by linarith),
      Finset.filter_singleton, if_pos]
    rw [Ideal.absNorm_top, Nat.cast_one]
    exact hX

theorem masked_shell_operator_bound
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (hW : SieveWeight W)
    (q d : Ideal (𝓞 F)) (M X K : ℝ) (hX : 0 < X)
    (rowMask : Ideal (𝓞 F) → ℝ)
    (hrow : ∀ a : Ideal (𝓞 F), 0 ≤ rowMask a ∧ rowMask a ≤ 1) :
    let U : ℝ := sSup ({0} ∪
      {x : ℝ | ∃ T : ℝ, 1 ≤ T ∧ T ≤ X ∧ x = B2 F c Q W M T K} ∪
      {x : ℝ | X < 1 ∧ 1 ≤ 2 * X ∧ x =
        ∑ a ∈ kernelRows F c M K,
          W ((Ideal.absNorm a : ℝ) / M) * ‖(Q.χ ⊤) a‖ ^ 2})
    0 ≤ U ∧
      (∀ a ∈ kernelRows F c M K, 0 ≤ maskedRowWeight W q d M rowMask a) ∧
      ∀ alpha : Ideal (𝓞 F) → ℂ,
        weightedEnergy (kernelRows F c M K) (paperShell F c X)
          (maskedRowWeight W q d M rowMask) (fun a u => (Q.χ u) a) alpha ≤
          U * energy F c X alpha := by
  intro U
  set S : Set ℝ := {0} ∪
    {x : ℝ | ∃ T : ℝ, 1 ≤ T ∧ T ≤ X ∧ x = B2 F c Q W M T K} ∪
    {x : ℝ | X < 1 ∧ 1 ≤ 2 * X ∧ x =
      ∑ a ∈ kernelRows F c M K,
        W ((Ideal.absNorm a : ℝ) / M) * ‖(Q.χ ⊤) a‖ ^ 2} with hSdef
  have hUdef : U = sSup S := rfl
  obtain ⟨Wb, hWb0, hWb⟩ := exists_sieveWeight_bound W hW
  set Cb : ℝ := Wb * ((boundedNormIdeals F ((5 / 2) * M)).card : ℝ) *
    ((boundedNormIdeals F (2 * X)).card : ℝ) with hCbdef
  have hCb0 : 0 ≤ Cb := by
    rw [hCbdef]
    exact mul_nonneg (mul_nonneg hWb0 (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hcard_kernel : (kernelRows F c M K).card ≤ (boundedNormIdeals F ((5 / 2) * M)).card := by
    unfold kernelRows
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hcardX : 1 ≤ ((boundedNormIdeals F (2 * X)).card : ℝ) := by
    have hne : (⊥ : Ideal (𝓞 F)) ∈ boundedNormIdeals F (2 * X) := by
      rw [mem_boundedNormIdeals]
      have hbot : (Ideal.absNorm (⊥ : Ideal (𝓞 F)) : ℝ) = 0 := by
        rw [Ideal.absNorm_bot]; norm_num
      rw [hbot]
      linarith
    have hpos := Finset.card_pos.mpr ⟨⊥, hne⟩
    exact_mod_cast hpos
  have hunit : (∑ a ∈ kernelRows F c M K,
      W ((Ideal.absNorm a : ℝ) / M) * ‖(Q.χ ⊤) a‖ ^ 2) ≤ Cb := by
    have h1 : ∑ a ∈ kernelRows F c M K,
        W ((Ideal.absNorm a : ℝ) / M) * ‖(Q.χ ⊤) a‖ ^ 2 ≤
        ∑ a ∈ kernelRows F c M K, Wb := by
      refine Finset.sum_le_sum fun a _ha => ?_
      have hchi : ‖(Q.χ ⊤) a‖ ≤ 1 :=
        quadraticFamily_norm_le_one Q (by rw [← Ideal.one_eq_top]; exact squarefree_one)
          (by simp) a
      have hsq : ‖(Q.χ ⊤) a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ((Q.χ ⊤) a), hchi]
      calc W ((Ideal.absNorm a : ℝ) / M) * ‖(Q.χ ⊤) a‖ ^ 2
          ≤ Wb * 1 := mul_le_mul (hWb _) hsq (sq_nonneg _) hWb0
        _ = Wb := mul_one Wb
    have hnn : (0 : ℝ) ≤ ((boundedNormIdeals F ((5 / 2) * M)).card : ℝ) * Wb :=
      mul_nonneg (Nat.cast_nonneg _) hWb0
    calc ∑ a ∈ kernelRows F c M K, W ((Ideal.absNorm a : ℝ) / M) * ‖(Q.χ ⊤) a‖ ^ 2
        ≤ ∑ a ∈ kernelRows F c M K, Wb := h1
      _ = ((kernelRows F c M K).card : ℝ) * Wb := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((boundedNormIdeals F ((5 / 2) * M)).card : ℝ) * Wb :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_kernel) hWb0
      _ ≤ ((boundedNormIdeals F ((5 / 2) * M)).card : ℝ) * Wb *
            ((boundedNormIdeals F (2 * X)).card : ℝ) :=
          (mul_one _).symm.le.trans (mul_le_mul_of_nonneg_left hcardX hnn)
      _ = Cb := by rw [hCbdef]; ring
  have hB2le : ∀ T : ℝ, T ≤ X → B2 F c Q W M T K ≤ Cb := by
    intro T hTX
    rw [B2]
    refine csSup_le ⟨0, Or.inl rfl⟩ ?_
    intro x hx
    rcases hx with hx | hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hCb0
    · obtain ⟨lam, hlam, rfl⟩ := hx
      have hshell_card : ((paperShell F c T).card : ℝ) ≤
          ((boundedNormIdeals F (2 * X)).card : ℝ) := by
        have hsub : paperShell F c T ⊆ boundedNormIdeals F (2 * X) := by
          intro I hI
          rw [mem_boundedNormIdeals]
          have hI' := (mem_paperShell F c T I).mp hI
          linarith [hI'.2.2.2]
        exact_mod_cast Finset.card_le_card hsub
      rw [Q2]
      calc ∑ a ∈ kernelRows F c M K,
            W ((Ideal.absNorm a : ℝ) / M) * ‖rowSum Q T lam a‖ ^ 2
          ≤ ∑ a ∈ kernelRows F c M K,
              Wb * ((boundedNormIdeals F (2 * X)).card : ℝ) := by
            refine Finset.sum_le_sum fun a _ha => ?_
            have hcardnn : (0 : ℝ) ≤ ((paperShell F c T).card : ℝ) := Nat.cast_nonneg _
            have h1 : ‖rowSum Q T lam a‖ ^ 2 ≤
                ((boundedNormIdeals F (2 * X)).card : ℝ) := by
              calc ‖rowSum Q T lam a‖ ^ 2
                  ≤ ((paperShell F c T).card : ℝ) * energy F c T lam := rowSum_sq_le Q T lam a
                _ ≤ ((paperShell F c T).card : ℝ) * 1 :=
                    mul_le_mul_of_nonneg_left hlam hcardnn
                _ = ((paperShell F c T).card : ℝ) := mul_one _
                _ ≤ ((boundedNormIdeals F (2 * X)).card : ℝ) := hshell_card
            exact mul_le_mul (hWb _) h1 (sq_nonneg _) hWb0
        _ = ((kernelRows F c M K).card : ℝ) *
              (Wb * ((boundedNormIdeals F (2 * X)).card : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((boundedNormIdeals F ((5 / 2) * M)).card : ℝ) *
              (Wb * ((boundedNormIdeals F (2 * X)).card : ℝ)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_kernel)
              (mul_nonneg hWb0 (Nat.cast_nonneg _))
        _ = Cb := by rw [hCbdef]; ring
  have hBdd : BddAbove S := by
    refine ⟨Cb, ?_⟩
    intro x hx
    rw [hSdef] at hx
    rcases hx with hx | hx
    · rcases hx with hx | hx
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hCb0
      · obtain ⟨T, _hT1, hTX, rfl⟩ := hx
        exact hB2le T hTX
    · obtain ⟨_hX1, _h2X, rfl⟩ := hx
      exact hunit
  refine ⟨?_, ?_, ?_⟩
  · rw [hUdef]
    refine le_csSup hBdd ?_
    exact Or.inl (Or.inl (Set.mem_singleton_iff.mpr rfl))
  · intro a _ha
    exact maskedRowWeight_nonneg W hW q d M rowMask hrow a
  · intro alpha
    by_cases hX1 : 1 ≤ X
    · have hmem : B2 F c Q W M X K ∈ S := by
        rw [hSdef]
        exact Or.inl (Or.inr ⟨X, hX1, le_refl X, rfl⟩)
      have hUX : B2 F c Q W M X K ≤ U := by
        rw [hUdef]
        exact le_csSup hBdd hmem
      have hwe : weightedEnergy (kernelRows F c M K) (paperShell F c X)
          (maskedRowWeight W q d M rowMask) (fun a u => (Q.χ u) a) alpha ≤
          Q2 F c Q W M X K alpha := by
        simp only [weightedEnergy, Q2, rowSum]
        refine Finset.sum_le_sum fun a _ha => ?_
        have hle : maskedRowWeight W q d M rowMask a ≤
            W ((Ideal.absNorm a : ℝ) / M) := maskedRowWeight_le W hW q d M rowMask hrow a
        have hinner : (∑ u ∈ paperShell F c X, (Q.χ u) a * alpha u) =
            (∑ u ∈ paperShell F c X, alpha u * (Q.χ u) a) :=
          Finset.sum_congr rfl fun u _hu => mul_comm _ _
        rw [hinner]
        exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      have hQ2 : Q2 F c Q W M X K alpha ≤ B2 F c Q W M X K * energy F c X alpha :=
        Q2_le_B2_mul_energy Q W M X K alpha
      have henergy_nn : 0 ≤ energy F c X alpha := by
        simp only [energy]
        exact Finset.sum_nonneg fun b _hb => sq_nonneg _
      calc weightedEnergy (kernelRows F c M K) (paperShell F c X)
            (maskedRowWeight W q d M rowMask) (fun a u => (Q.χ u) a) alpha
          ≤ Q2 F c Q W M X K alpha := hwe
        _ ≤ B2 F c Q W M X K * energy F c X alpha := hQ2
        _ ≤ U * energy F c X alpha := mul_le_mul_of_nonneg_right hUX henergy_nn
    · have hX1' : X < 1 := lt_of_not_ge hX1
      rcases paperShell_eq_empty_or_singleton_of_lt_one (c := c) hX1' with hshell | hshell
      · simp [weightedEnergy, energy, hshell]
      · have htop : ⊤ ∈ paperShell F c X := by rw [hshell]; simp
        have h2X : 1 ≤ 2 * X := by
          have := (mem_paperShell F c X ⊤).mp htop
          simpa using this.2.2.2
        have henergy : energy F c X alpha = ‖alpha ⊤‖ ^ 2 := by
          rw [energy, hshell]; simp
        have hwe : weightedEnergy (kernelRows F c M K) (paperShell F c X)
            (maskedRowWeight W q d M rowMask) (fun a u => (Q.χ u) a) alpha =
            (∑ a ∈ kernelRows F c M K, maskedRowWeight W q d M rowMask a *
              ‖(Q.χ ⊤) a‖ ^ 2) * ‖alpha ⊤‖ ^ 2 := by
          have hinner : ∀ a : Ideal (𝓞 F),
              (∑ u ∈ paperShell F c X, (Q.χ u) a * alpha u) = (Q.χ ⊤) a * alpha ⊤ := by
            intro a
            rw [hshell]
            simp
          simp only [weightedEnergy]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ha => ?_
          rw [hinner a, norm_mul, mul_pow]
          ring
        have hsum : (∑ a ∈ kernelRows F c M K, maskedRowWeight W q d M rowMask a *
            ‖(Q.χ ⊤) a‖ ^ 2) ≤ U := by
          have hle : ∑ a ∈ kernelRows F c M K, maskedRowWeight W q d M rowMask a *
              ‖(Q.χ ⊤) a‖ ^ 2 ≤ ∑ a ∈ kernelRows F c M K,
              W ((Ideal.absNorm a : ℝ) / M) * ‖(Q.χ ⊤) a‖ ^ 2 := by
            refine Finset.sum_le_sum fun a _ha => ?_
            exact mul_le_mul_of_nonneg_right
              (maskedRowWeight_le W hW q d M rowMask hrow a) (sq_nonneg _)
          refine hle.trans ?_
          refine le_csSup hBdd ?_
          exact Or.inr ⟨hX1', h2X, rfl⟩
        calc weightedEnergy (kernelRows F c M K) (paperShell F c X)
              (maskedRowWeight W q d M rowMask) (fun a u => (Q.χ u) a) alpha
            = (∑ a ∈ kernelRows F c M K, maskedRowWeight W q d M rowMask a *
                ‖(Q.χ ⊤) a‖ ^ 2) * ‖alpha ⊤‖ ^ 2 := hwe
          _ ≤ U * ‖alpha ⊤‖ ^ 2 := mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
          _ = U * energy F c X alpha := by rw [henergy]

end DedekindZetaZeroFree.LargeSieve.Sieve.GcdTail

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {c : Ideal (𝓞 F)}

def GcdPairTransport (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) : Prop :=
  ∀ d u v : Ideal (𝓞 F),
    d ≠ ⊥ → u ≠ ⊥ → v ≠ ⊥ →
    Squarefree d → Squarefree u → Squarefree v →
    Squarefree (d * u) → Squarefree (d * v) →
    (d * u) ⊔ c = ⊤ → (d * v) ⊔ c = ⊤ →
    u ⊔ v = ⊤ → d ⊔ (u * v) = ⊤ →
    Q.cls (d * u) = Q.cls (d * v) →
    ∀ a : Ideal (𝓞 F), a ≠ ⊥ → a ⊔ (q * d) = ⊤ →
      (Q.χ (d * u)) a * (starRingEnd ℂ) ((Q.χ (d * v)) a) =
        (Q.χ u) a * (starRingEnd ℂ) ((Q.χ v) a)

def B2unitColumn (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (M K : ℝ) : ℝ :=
  ∑ a ∈ kernelRows F c M K,
    W ((Ideal.absNorm a : ℝ) / M) * ‖(Q.χ ⊤) a‖ ^ 2

def B2env (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (M X K : ℝ) : ℝ :=
  sSup ({0} ∪
    {x : ℝ | ∃ T : ℝ, 1 ≤ T ∧ T ≤ X ∧ x = B2 F c Q W M T K} ∪
    {x : ℝ | X < 1 ∧ 1 ≤ 2 * X ∧ x = B2unitColumn F c Q W M K})

def gcdTailEnergy (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (N : ℝ) (d : Ideal (𝓞 F))
    (lam : Ideal (𝓞 F) → ℂ) : ℝ :=
  ∑ b ∈ paperShell F c N, if d ∣ b then ‖lam b‖ ^ 2 else 0

def maskedGcdBlock (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (q : Ideal (𝓞 F)) (M N K : ℝ)
    (d : Ideal (𝓞 F)) (g : Q.G) (lam : Ideal (𝓞 F) → ℂ)
    (rowMask : Ideal (𝓞 F) → ℝ) (columnMask : Ideal (𝓞 F) → ℂ) : ℂ :=
  ∑ b1 ∈ paperShell F c N, ∑ b2 ∈ paperShell F c N,
    if b1 ⊔ b2 = d ∧ Q.cls b1 = g ∧ Q.cls b2 = g then
      (columnMask b1 * lam b1) * (starRingEnd ℂ) (columnMask b2 * lam b2) *
        (∑ a ∈ kernelRows F c M K,
          if a ⊔ (q * d) = ⊤ then
            (W ((Ideal.absNorm a : ℝ) / M) * rowMask a : ℂ) *
              (Q.χ b1) a * (starRingEnd ℂ) ((Q.χ b2) a)
          else 0)
    else 0

end DedekindZetaZeroFree.LargeSieve.Sieve

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem bilinear_gcd_tail
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (hW : Sieve.SieveWeight W)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (htransport : Sieve.GcdPairTransport Q q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ M N K : ℝ, 1 ≤ M → 1 ≤ N → 0 < K →
      ∀ d : Ideal (𝓞 F), d ≠ ⊥ → (Ideal.absNorm d : ℝ) ≤ 2 * N →
      ∀ (lam : Ideal (𝓞 F) → ℂ),
        (∀ b : Ideal (𝓞 F), b ∉ Sieve.paperShell F c N → lam b = 0) →
      ∀ (g : Q.G) (rowMask : Ideal (𝓞 F) → ℝ)
        (columnMask : Ideal (𝓞 F) → ℂ),
        (∀ a : Ideal (𝓞 F), 0 ≤ rowMask a ∧ rowMask a ≤ 1) →
        (∀ b : Ideal (𝓞 F), ‖columnMask b‖ ≤ 1) →
        ‖Sieve.maskedGcdBlock F c Q W q M N K d g lam rowMask columnMask‖ ≤
          C * Real.rpow N ε *
            Sieve.B2env F c Q W M (N / (Ideal.absNorm d : ℝ)) K *
              Sieve.gcdTailEnergy F c N d lam := by
  obtain ⟨C, hC, hcost⟩ := Sieve.GcdTail.support_cost_energy_bound F ε hε
  refine ⟨C, hC, ?_⟩
  intro M N K hM hN hK d hd hdN lam hlam g rowMask columnMask hrow hcol
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hdpos : 0 < Ideal.absNorm d :=
    Nat.pos_of_ne_zero (fun h => hd (Ideal.absNorm_eq_zero_iff.mp h))
  have hdreal : 0 < (Ideal.absNorm d : ℝ) := by exact_mod_cast hdpos
  have hdge : 1 ≤ (Ideal.absNorm d : ℝ) := by exact_mod_cast hdpos
  let X : ℝ := N / (Ideal.absNorm d : ℝ)
  have hX : 0 < X := div_pos hNpos hdreal
  have hXN : X ≤ N := (div_le_iff₀ hdreal).2 (by nlinarith)
  obtain ⟨alpha, halpha, hreindex⟩ := Sieve.GcdTail.quotient_reindex
    F c Q W q htransport M N K hNpos d hd g lam rowMask columnMask hcol
  change Sieve.energy F c X alpha ≤ Sieve.gcdTailEnergy F c N d lam at halpha
  change Sieve.maskedGcdBlock F c Q W q M N K d g lam rowMask columnMask =
    Sieve.GcdTail.coprimeForm (Sieve.kernelRows F c M K)
      (Sieve.paperShell F c X) (Sieve.GcdTail.maskedRowWeight W q d M rowMask)
      (fun a u => (Q.χ u) a) alpha at hreindex
  have hop := Sieve.GcdTail.masked_shell_operator_bound
    F c Q W hW q d M X K hX rowMask hrow
  change 0 ≤ Sieve.B2env F c Q W M X K ∧
    (∀ a ∈ Sieve.kernelRows F c M K,
      0 ≤ Sieve.GcdTail.maskedRowWeight W q d M rowMask a) ∧
    (∀ beta : Ideal (𝓞 F) → ℂ,
      Sieve.GcdTail.weightedEnergy (Sieve.kernelRows F c M K)
        (Sieve.paperShell F c X) (Sieve.GcdTail.maskedRowWeight W q d M rowMask)
        (fun a u => (Q.χ u) a) beta ≤
        Sieve.B2env F c Q W M X K * Sieve.energy F c X beta) at hop
  have hcols : ∀ u ∈ Sieve.paperShell F c X, u ≠ ⊥ := by
    intro u hu
    have hsf := (Sieve.mem_paperShell F c X u).mp hu
    simpa [Ideal.zero_eq_bot] using hsf.1.ne_zero
  have hcop := Sieve.GcdTail.coprime_form_bound
    (Sieve.kernelRows F c M K) (Sieve.paperShell F c X) hcols
    (Sieve.GcdTail.maskedRowWeight W q d M rowMask) hop.2.1
    (fun a u => (Q.χ u) a) (Sieve.B2env F c Q W M X K) hop.1 hop.2.2 alpha
  have hloss := hcost c N X hN hX hXN alpha
  have hCN : 0 ≤ C * Real.rpow N ε := mul_nonneg hC (Real.rpow_nonneg hNpos.le ε)
  rw [hreindex]
  calc
    _ ≤ Sieve.B2env F c Q W M X K *
        ∑ u ∈ Sieve.paperShell F c X,
          Sieve.GcdTail.primeSupportCost u * ‖alpha u‖ ^ 2 := hcop
    _ ≤ Sieve.B2env F c Q W M X K *
        (C * Real.rpow N ε * Sieve.energy F c X alpha) :=
      mul_le_mul_of_nonneg_left hloss hop.1
    _ = (C * Real.rpow N ε * Sieve.B2env F c Q W M X K) *
        Sieve.energy F c X alpha := by ring
    _ ≤ (C * Real.rpow N ε * Sieve.B2env F c Q W M X K) *
        Sieve.gcdTailEnergy F c N d lam :=
      mul_le_mul_of_nonneg_left halpha (mul_nonneg hCN hop.1)

end DedekindZetaZeroFree.LargeSieve

end

end
