module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.FourierRectangles.InclusiveDivisorBucketEnergy
public import DedekindZetaZeroFree.LargeSieve.Bilinear.LargeDivisors.RadicalCoprimeColumnExpansion
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Remainders.DivisorNormAndCardinalityBounds

@[expose] public section

section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteFourierRectangles.FourierExpansion
open ExplicitTerms
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private lemma bucket_partition_sum (C : Context Q)
    (hN : 1 ≤ C.N) (hK : 1 ≤ C.K) (hnN : norm C.d ≤ 2 * C.N)
    (u : Ideal (𝓞 F)) (hu : u ∈ C.columns) (H : Ideal (𝓞 F) → ℂ) :
    (∑ f ∈ idealDivisors u, H f) =
      ∑ j ∈ Finset.range (Vendor.dyadicLength (2 * C.N / norm C.d) + 1),
        ∑ f ∈ divisorBucket F (2 * C.N / norm C.d) j,
          if f ∣ u then H f else 0 := by
  let J := Finset.range (Vendor.dyadicLength (2 * C.N / norm C.d) + 1)
  let blk := fun j => (divisorBucket F (2 * C.N / norm C.d) j).filter (fun f => f ∣ u)
  have hu0 : u ≠ ⊥ := ((Sieve.mem_idealAdmissibleFinset _ _ _ _).mp
    (Finset.mem_filter.mp hu).1).1.ne_zero
  have hex := (inclusive_divisor_endpoint_energy C hN hK hnN).2.1 u hu
  have heq : J.biUnion blk = idealDivisors u := by
    ext f
    constructor
    · intro hf
      obtain ⟨j, hj, hf⟩ := Finset.mem_biUnion.mp hf
      exact (mem_idealDivisors hu0).mpr (Finset.mem_filter.mp hf).2
    · intro hf
      obtain ⟨j, ⟨hj, hfj⟩, _⟩ := hex f hf
      exact Finset.mem_biUnion.mpr ⟨j, hj,
        Finset.mem_filter.mpr ⟨hfj, (mem_idealDivisors hu0).mp hf⟩⟩
  have hdis : (↑J : Set ℕ).PairwiseDisjoint blk := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro f hfi hfj
    have hf : f ∈ idealDivisors u := (mem_idealDivisors hu0).mpr (Finset.mem_filter.mp hfi).2
    obtain ⟨k, hk, huniq⟩ := hex f hf
    exact hij ((huniq i ⟨hi, (Finset.mem_filter.mp hfi).1⟩).trans
      (huniq j ⟨hj, (Finset.mem_filter.mp hfj).1⟩).symm)
  rw [← heq, Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro j hj
  exact Finset.sum_filter _ _

theorem sum_divisors_rectangles (C : Context Q)
    (hN : 1 ≤ C.N) (hK : 1 ≤ C.K) (hnN : norm C.d ≤ 2 * C.N)
    (B Cq : ℝ) (hThreshold : Threshold C B Cq)
    (e : Ideal (𝓞 F)) (he : e ∈ C.mobiusDivisors)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : p ∈ C.pairs)
    (H : Ideal (𝓞 F) → ℂ)
    (hH : ∀ f, ¬(C.Y1 B e < ExplicitTerms.norm f ∧ ExplicitTerms.norm f ≤ C.Z1 B e) → H f = 0) :
    (∑ f ∈ idealDivisors (p.1 * p.2), H f) =
      ∑ ij ∈ rectangles F B C.M C.N (norm C.d) (Real.rpow (C.M * C.N) C.δ) Cq,
        ∑ f₁ ∈ divisorBucket F (2 * C.N / norm C.d) ij.1,
          ∑ f₂ ∈ divisorBucket F (2 * C.N / norm C.d) ij.2,
            if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then H (f₁ * f₂) else 0 := by
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  have hvalid := (Finset.mem_filter.mp hp).2
  let J := Finset.range (Vendor.dyadicLength (2 * C.N / norm C.d) + 1)
  let cell := fun ij : ℕ × ℕ =>
    ∑ f₁ ∈ divisorBucket F (2 * C.N / norm C.d) ij.1,
      ∑ f₂ ∈ divisorBucket F (2 * C.N / norm C.d) ij.2,
        if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then H (f₁ * f₂) else 0
  have hall : (∑ f ∈ idealDivisors (p.1 * p.2), H f) = ∑ ij ∈ J ×ˢ J, cell ij := by
    rw [LargeDirectDictionary.sum_divisors_mul p.1 p.2 hvalid.hu0 hvalid.hv0 hvalid.huv]
    rw [bucket_partition_sum C hN hK hnN p.1 hu]
    simp_rw [bucket_partition_sum C hN hK hnN p.2 hv]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    have hmove (x : Ideal (𝓞 F)) :
        (if x ∣ p.1 then ∑ j ∈ J, ∑ f ∈ divisorBucket F (2 * C.N / norm C.d) j,
          if f ∣ p.2 then H (x*f) else 0 else 0) =
        ∑ j ∈ J, ∑ f ∈ divisorBucket F (2 * C.N / norm C.d) j,
          if x ∣ p.1 ∧ f ∣ p.2 then H (x*f) else 0 := by
      by_cases hx : x ∣ p.1 <;> simp [hx]
    change (∑ x ∈ divisorBucket F (2 * C.N / norm C.d) i,
      if x ∣ p.1 then ∑ j ∈ J, ∑ f ∈ divisorBucket F (2 * C.N / norm C.d) j,
        if f ∣ p.2 then H (x*f) else 0 else 0) = _
    simp_rw [hmove]
    rw [Finset.sum_comm]
  rw [hall]
  change _ = ∑ ij ∈ (J ×ˢ J).filter _, cell ij
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro ij hij hnot
  dsimp [cell]
  apply Finset.sum_eq_zero
  intro f₁ hf₁
  apply Finset.sum_eq_zero
  intro f₂ hf₂
  split_ifs with hd
  · by_contra hn
    have hwindow : C.Y1 B e < ExplicitTerms.norm (f₁*f₂) ∧
        ExplicitTerms.norm (f₁*f₂) ≤ C.Z1 B e := by
      by_contra hw
      exact hn (hH _ hw)
    obtain ⟨hb1, hf10, hl1, hh1⟩ := Finset.mem_filter.mp hf₁
    obtain ⟨hb2, hf20, hl2, hh2⟩ := Finset.mem_filter.mp hf₂
    have hu1 : ExplicitTerms.norm f₁ ≤ 2 * C.N / norm C.d :=
      mem_boundedNormIdeals.mp hb1
    have hu2 : ExplicitTerms.norm f₂ ≤ 2 * C.N / norm C.d :=
      mem_boundedNormIdeals.mp hb2
    have hp1 : 0 ≤ divisorScale ij.1 := by unfold divisorScale; positivity
    have hp2 : 0 ≤ divisorScale ij.2 := by unfold divisorScale; positivity
    have hn1 : 0 ≤ ExplicitTerms.norm f₁ := Nat.cast_nonneg _
    have hprod : divisorScale ij.1 * divisorScale ij.2 ≤ ExplicitTerms.norm (f₁*f₂) := by
      rw [ExplicitTerms.norm, map_mul, Nat.cast_mul]
      exact mul_le_mul hl1 hl2 hp2 hn1
    apply hnot
    apply Finset.mem_filter.mpr
    refine ⟨hij, le_trans hl1 hu1, le_trans hl2 hu2, ?_, ⟨f₁, hf₁⟩, ⟨f₂, hf₂⟩⟩
    exact hprod.trans (hwindow.2.trans (hThreshold e he))
  · rfl

end DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteFourierRectangles.FourierExpansion

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteFourierRectangles.FourierExpansion
open ExplicitTerms
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def rowScale (C : Context Q) (e a f₁ f₂ : Ideal (𝓞 F)) : ℝ :=
  (C.N / norm C.d) * Real.sqrt (norm e) /
    (norm (f₁ * f₂) * Real.sqrt (C.M * norm a))

def rowCoefficient (C : Context Q) (χ : ℝ → ℝ)
    (e a f₁ f₂ b : Ideal (𝓞 F)) (t s : ℝ) : ℂ :=
  MiddleLogKernel.fourierCoefficient C.reflectedKernel χ (rowScale C e a f₁ f₂) (norm b) t s

def FourierInversion (C : Context Q) (χ : ℝ → ℝ) : Prop :=
  ∀ h b : ℝ, 0 < h → 1 ≤ b →
    Integrable (fun p : ℝ × ℝ => MiddleLogKernel.fourierCoefficient C.reflectedKernel χ h b p.1 p.2) ∧
    ∀ x y : ℝ, MiddleLogKernel.normalizedKernel C.reflectedKernel χ h b x y =
      ∫ p : ℝ × ℝ, MiddleLogKernel.fourierCoefficient C.reflectedKernel χ h b p.1 p.2 *
        Complex.exp (((2 * Real.pi * (p.1 * x + p.2 * y) : ℝ) : ℂ) * Complex.I)

private lemma reflectedRowIdealNorm_pos_of_ne_bot {a : Ideal (𝓞 F)} (ha : a ≠ ⊥) : 0 < norm a := by
  unfold ExplicitTerms.norm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ha)
private lemma norm_mul (a b : Ideal (𝓞 F)) : norm (a * b) = norm a * norm b := by
  simp [ExplicitTerms.norm, map_mul]

theorem normalizedKernel_eq (K : ℝ → ℂ) (χ : ℝ → ℝ)
    (hχ : ∀ x ∈ Set.Icc 0 (Real.log 2), χ x = 1)
    (M X E A f b u v : ℝ) (hM : 0 < M) (hX : 0 < X)
    (hE : 0 < E) (hA : 0 < A) (hf : 0 < f)
    (hu : X < u) (hu2 : u ≤ 2 * X) (hv : X < v) (hv2 : v ≤ 2 * X) :
    MiddleLogKernel.normalizedKernel K χ (X * Real.sqrt E / (f * Real.sqrt (M * A))) b
      (Real.log (u / X)) (Real.log (v / X)) =
      (Real.sqrt (E * (u * v) / M / A) / f : ℂ) *
        K (b * Real.sqrt (E * (u * v) / M / A) / f) := by
  have hu0 := hX.trans hu
  have hv0 := hX.trans hv
  have huq := div_pos hu0 hX
  have hvq := div_pos hv0 hX
  have hx : Real.log (u / X) ∈ Set.Icc 0 (Real.log 2) :=
    ⟨Real.log_nonneg ((le_div_iff₀ hX).mpr (by simpa using hu.le)),
      Real.log_le_log huq ((div_le_iff₀ hX).mpr hu2)⟩
  have hy : Real.log (v / X) ∈ Set.Icc 0 (Real.log 2) :=
    ⟨Real.log_nonneg ((le_div_iff₀ hX).mpr (by simpa using hv.le)),
      Real.log_le_log hvq ((div_le_iff₀ hX).mpr hv2)⟩
  have he : Real.exp ((Real.log (u / X) + Real.log (v / X)) / 2) = Real.sqrt (u * v) / X := by
    rw [← Real.log_mul huq.ne' hvq.ne', Real.exp_half, Real.exp_log (mul_pos huq hvq)]
    rw [show u / X * (v / X) = (u * v) / X ^ 2 by ring,
      Real.sqrt_div (mul_pos hu0 hv0).le, Real.sqrt_sq hX.le]
  have ht : Real.sqrt (E * (u * v) / M / A) =
      Real.sqrt E * Real.sqrt (u * v) / Real.sqrt (M * A) := by
    rw [show E * (u * v) / M / A = (E * (u * v)) / (M * A) by ring,
      Real.sqrt_div (by positivity), Real.sqrt_mul hE.le]
  have hs : Real.sqrt (M * A) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hM hA)).ne'
  have hscale : (X * Real.sqrt E / (f * Real.sqrt (M * A))) * (Real.sqrt (u * v) / X) =
      Real.sqrt (E * (u * v) / M / A) / f := by
    rw [ht]
    field_simp
  simp only [MiddleLogKernel.normalizedKernel, hχ _ hx, hχ _ hy, one_mul, he]
  rw [hscale]
  push_cast
  congr 1
  congr 1
  rw [mul_assoc, hscale]
  ring

theorem coefficient_prefactor (C : Context Q) (e : Ideal (𝓞 F))
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p) :
    C.coefficient p * C.prefactor e p hp =
      (UniqueFactorizationMonoid.moebius e : ℂ) * (C.M / norm e : ℂ) *
        (weightedColumn C p.1 * star (weightedColumn C p.2)) * C.primitive p hp e := by
  have hu := reflectedRowIdealNorm_pos_of_ne_bot hp.hu0
  have hv := reflectedRowIdealNorm_pos_of_ne_bot hp.hv0
  have hs : Real.sqrt (norm (p.1 * p.2)) = Real.sqrt (norm p.1) * Real.sqrt (norm p.2) := by
    rw [norm_mul, Real.sqrt_mul hu.le]
  simp only [Context.coefficient, Context.prefactor, weightedColumn, star_div₀,
    star_mul, star_inv₀, RCLike.star_def, Complex.conj_ofReal, hs, Complex.ofReal_mul, Complex.ofReal_div]
  ring

theorem row_fourier_identity (C : Context Q) (χ : ℝ → ℝ)
    (hχ : ∀ x ∈ Set.Icc 0 (Real.log 2), χ x = 1) (hFourier : FourierInversion C χ)
    (hM : 0 < C.M) (hN : 0 < C.N)
    (e a f₁ f₂ b : Ideal (𝓞 F)) (he : e ≠ ⊥) (ha : a ≠ ⊥)
    (hf₁ : f₁ ≠ ⊥) (hf₂ : f₂ ≠ ⊥) (hb : b ≠ ⊥)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p)
    (hu : C.N / norm C.d < norm p.1) (hu2 : norm p.1 ≤ 2 * (C.N / norm C.d))
    (hv : C.N / norm C.d < norm p.2) (hv2 : norm p.2 ≤ 2 * (C.N / norm C.d)) :
    C.coefficient p * C.prefactor e p hp * C.primitive p hp a *
      (Real.sqrt (C.dualScale e p / norm a) / norm (f₁ * f₂) : ℂ) *
      C.reflectedKernel (norm b * Real.sqrt (C.dualScale e p / norm a) / norm (f₁ * f₂)) =
    (UniqueFactorizationMonoid.moebius e : ℂ) * (C.M / norm e : ℂ) *
      (weightedColumn C p.1 * star (weightedColumn C p.2) *
        C.primitive p hp e * C.primitive p hp a) *
      ∫ q : ℝ × ℝ, frequencyPhase C p q.1 q.2 * rowCoefficient C χ e a f₁ f₂ b q.1 q.2 := by
  have hX : 0 < C.N / norm C.d := div_pos hN (reflectedRowIdealNorm_pos_of_ne_bot C.hd0)
  have hE := reflectedRowIdealNorm_pos_of_ne_bot he
  have hA := reflectedRowIdealNorm_pos_of_ne_bot ha
  have hf : 0 < norm (f₁ * f₂) := by rw [norm_mul]; exact mul_pos (reflectedRowIdealNorm_pos_of_ne_bot hf₁) (reflectedRowIdealNorm_pos_of_ne_bot hf₂)
  have hscale : 0 < rowScale C e a f₁ f₂ := by unfold rowScale; positivity
  have hb1 : 1 ≤ norm b := by
    unfold ExplicitTerms.norm
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hb)
  have hnorm := normalizedKernel_eq C.reflectedKernel χ hχ C.M (C.N / norm C.d)
    (norm e) (norm a) (norm (f₁ * f₂)) (norm b) (norm p.1) (norm p.2)
    hM hX hE hA hf hu hu2 hv hv2
  rw [← norm_mul] at hnorm
  change MiddleLogKernel.normalizedKernel C.reflectedKernel χ (rowScale C e a f₁ f₂) (norm b)
    (Real.log (norm p.1 / (C.N / norm C.d))) (Real.log (norm p.2 / (C.N / norm C.d))) =
    (Real.sqrt (C.dualScale e p / norm a) / norm (f₁ * f₂) : ℂ) *
      C.reflectedKernel (norm b * Real.sqrt (C.dualScale e p / norm a) / norm (f₁ * f₂)) at hnorm
  have hInv := (hFourier _ _ hscale hb1).2
    (Real.log (norm p.1 / (C.N / norm C.d))) (Real.log (norm p.2 / (C.N / norm C.d)))
  have heq : (Real.sqrt (C.dualScale e p / norm a) / norm (f₁ * f₂) : ℂ) *
      C.reflectedKernel (norm b * Real.sqrt (C.dualScale e p / norm a) / norm (f₁ * f₂)) =
      ∫ q : ℝ × ℝ, frequencyPhase C p q.1 q.2 * rowCoefficient C χ e a f₁ f₂ b q.1 q.2 := by
    rw [← hnorm, hInv]
    unfold frequencyPhase rowCoefficient
    apply integral_congr_ae
    filter_upwards with q
    exact mul_comm _ _
  rw [coefficient_prefactor]
  calc
    _ = (UniqueFactorizationMonoid.moebius e : ℂ) * (C.M / norm e : ℂ) *
      (weightedColumn C p.1 * star (weightedColumn C p.2) * C.primitive p hp e * C.primitive p hp a) *
      ((Real.sqrt (C.dualScale e p / norm a) / norm (f₁ * f₂) : ℂ) *
      C.reflectedKernel (norm b * Real.sqrt (C.dualScale e p / norm a) / norm (f₁ * f₂))) := by ring
    _ = _ := by rw [heq]

end DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteFourierRectangles.FourierExpansion

end

end

section
noncomputable section
open scoped NumberField Classical BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteFourierRectangles.FourierExpansion
open ExplicitTerms
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
private lemma fourier_rectangles_nonzero_ideal_norm_pos {a : Ideal (𝓞 F)} (ha : a ≠ ⊥) : 0 < norm a := by
  unfold ExplicitTerms.norm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ha)
private lemma row_nonzero (C : Context Q) (B : ℝ) (unit : Bool)
    (a : Ideal (𝓞 F)) (ha : a ∈ C.reflectedRows B unit) : a ≠ ⊥ := by
  obtain ⟨tr, ht, rfl⟩ := Finset.mem_image.mp ha
  exact (Finset.mem_filter.mp ht).2.2.2
private lemma column_range (C : Context Q) (hN : 1 ≤ C.N) (u : Ideal (𝓞 F)) (hu : u ∈ C.columns) :
    C.N / norm C.d < norm u ∧ norm u ≤ 2 * (C.N / norm C.d) := by
  have hs := (Finset.mem_filter.mp hu).2.1
  have h := (Sieve.mem_paperShell F c C.N (C.d*u)).mp hs
  have he : norm (C.d*u) = norm C.d * norm u := by simp [ExplicitTerms.norm, map_mul]
  have hn : C.N < norm (C.d*u) ∧ norm (C.d*u) ≤ 2*C.N := h.2.2
  rw [he] at hn
  constructor
  · exact (div_lt_iff₀ (fourier_rectangles_nonzero_ideal_norm_pos C.hd0)).mpr (by simpa [mul_comm] using hn.1)
  · rw [show 2 * (C.N / norm C.d) = 2*C.N / norm C.d by ring]
    exact (le_div_iff₀ (fourier_rectangles_nonzero_ideal_norm_pos C.hd0)).mpr (by simpa [mul_comm] using hn.2)

private lemma pairSum_sum {α : Type*} (C : Context Q) (s : Finset α)
    (f : α → (p : Ideal (𝓞 F) × Ideal (𝓞 F)) → C.ValidPair p → ℂ) :
    C.pairSum (fun p hp => ∑ i ∈ s, f i p hp) = ∑ i ∈ s, C.pairSum (f i) := by
  unfold Context.pairSum
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp
private lemma pairSum_mul (C : Context Q) (z : ℂ)
    (f : (p : Ideal (𝓞 F) × Ideal (𝓞 F)) → C.ValidPair p → ℂ) :
    C.pairSum (fun p hp => z * f p hp) = z * C.pairSum f := by
  unfold Context.pairSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp
private lemma pairSum_congr (C : Context Q)
    (f g : (p : Ideal (𝓞 F) × Ideal (𝓞 F)) → C.ValidPair p → ℂ)
    (h : ∀ p ∈ C.pairs, ∀ hp, f p hp = g p hp) : C.pairSum f = C.pairSum g := by
  unfold Context.pairSum
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs with hv
  · exact h p hp hv
  · rfl

private lemma phase_norm (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (t s : ℝ) :
    ‖frequencyPhase C p t s‖ = 1 := by
  simp [frequencyPhase, Complex.norm_exp]
private lemma phase_integrable (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F))
    (A : ℝ × ℝ → ℂ) (hA : Integrable A) (z : ℂ) :
    Integrable (fun q : ℝ × ℝ => z * (frequencyPhase C p q.1 q.2 * A q)) := by
  apply Integrable.const_mul
  apply Integrable.mono' hA.norm
  · exact ((show Continuous (fun q : ℝ × ℝ => frequencyPhase C p q.1 q.2) by
      unfold frequencyPhase; fun_prop).aestronglyMeasurable.mul hA.aestronglyMeasurable)
  · filter_upwards with q
    simp only [_root_.norm_mul, phase_norm, one_mul]
    exact le_refl _

private lemma pair_integral (C : Context Q) (e a f₁ f₂ : Ideal (𝓞 F))
    (A : ℝ × ℝ → ℂ) (hA : Integrable A) :
    C.pairSum (fun p hp => if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then
      (weightedColumn C p.1 * star (weightedColumn C p.2) * C.primitive p hp e * C.primitive p hp a) *
        ∫ q : ℝ × ℝ, frequencyPhase C p q.1 q.2 * A q else 0) =
      ∫ q : ℝ × ℝ, frequencyCell C e a f₁ f₂ q.1 q.2 * A q := by
  unfold frequencyCell Context.pairSum
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum _ (fun p hp => ?_)]
  · apply Finset.sum_congr rfl
    intro p hp
    split_ifs with hv hd <;> simp [integral_const_mul, mul_assoc]
  · by_cases hv : C.ValidPair p
    · by_cases hd : f₁ ∣ p.1 ∧ f₂ ∣ p.2
      · simpa only [dif_pos hv, if_pos hd, mul_assoc] using
          phase_integrable C p A hA (weightedColumn C p.1 * star (weightedColumn C p.2) *
            C.primitive p hv e * C.primitive p hv a)
      · simp [hv, hd]
    · simp [hv]

private lemma middle_rectangles (C : Context Q) (hN : 1 ≤ C.N) (hK : 1 ≤ C.K)
    (hnN : norm C.d ≤ 2*C.N) (B Cq : ℝ) (ht : Threshold C B Cq)
    (e : Ideal (𝓞 F)) (he : e ∈ C.mobiusDivisors)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : p ∈ C.pairs) (T : ℝ) :
    Context.middle C.reflectedKernel (p.1*p.2) T (C.Y1 B e) (C.Z1 B e) C.L1 =
    ∑ ij ∈ rectangles F B C.M C.N (norm C.d) (Real.rpow (C.M*C.N) C.δ) Cq,
      ∑ f₁ ∈ divisorBucket F (2*C.N/norm C.d) ij.1,
        ∑ f₂ ∈ divisorBucket F (2*C.N/norm C.d) ij.2,
          if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then
            if C.Y1 B e < norm (f₁*f₂) ∧ norm (f₁*f₂) ≤ C.Z1 B e then
              (UniqueFactorizationMonoid.moebius (f₁*f₂) : ℂ) * (T / norm (f₁*f₂) : ℂ) *
                ∑ b ∈ (boundedNormIdeals F C.L1).filter (fun b => b ≠ ⊥),
                  C.reflectedKernel (norm b * T / norm (f₁*f₂))
            else 0
          else 0 := by
  unfold Context.middle
  rw [Finset.sum_filter]
  exact sum_divisors_rectangles C hN hK hnN B Cq ht e he p hp _ (by intro f hf; simp [hf])

private lemma cell_identity (C : Context Q) (χ : ℝ → ℝ)
    (hχ : ∀ x ∈ Set.Icc 0 (Real.log 2), χ x = 1) (hFourier : FourierInversion C χ)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N)
    (e a f₁ f₂ : Ideal (𝓞 F)) (he : e ≠ ⊥) (ha : a ≠ ⊥)
    (hf₁ : f₁ ≠ ⊥) (hf₂ : f₂ ≠ ⊥) (B : ℝ) :
    C.pairSum (fun p hp => C.coefficient p * C.prefactor e p hp * C.primitive p hp a *
      (if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then
        if C.Y1 B e < norm (f₁*f₂) ∧ norm (f₁*f₂) ≤ C.Z1 B e then
          (UniqueFactorizationMonoid.moebius (f₁*f₂) : ℂ) *
            (Real.sqrt (C.dualScale e p / norm a) / norm (f₁*f₂) : ℂ) *
            ∑ b ∈ (boundedNormIdeals F C.L1).filter (fun b => b ≠ ⊥),
              C.reflectedKernel (norm b * Real.sqrt (C.dualScale e p / norm a) / norm (f₁*f₂))
        else 0
      else 0)) =
    (UniqueFactorizationMonoid.moebius e : ℂ) * (C.M / norm e : ℂ) *
      (if C.Y1 B e < norm (f₁*f₂) ∧ norm (f₁*f₂) ≤ C.Z1 B e then
        (UniqueFactorizationMonoid.moebius (f₁*f₂) : ℂ) *
          ∑ b ∈ (boundedNormIdeals F C.L1).filter (fun b => b ≠ ⊥),
            ∫ q : ℝ × ℝ, frequencyCell C e a f₁ f₂ q.1 q.2 * rowCoefficient C χ e a f₁ f₂ b q.1 q.2
      else 0) := by
  by_cases hw : C.Y1 B e < norm (f₁*f₂) ∧ norm (f₁*f₂) ≤ C.Z1 B e
  · simp only [if_pos hw]
    have hrewrite := pairSum_congr C
      (fun p hp => C.coefficient p * C.prefactor e p hp * C.primitive p hp a *
        (if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then
          (UniqueFactorizationMonoid.moebius (f₁*f₂) : ℂ) *
          (Real.sqrt (C.dualScale e p / norm a) / norm (f₁*f₂) : ℂ) *
          ∑ b ∈ (boundedNormIdeals F C.L1).filter (fun b => b ≠ ⊥),
            C.reflectedKernel (norm b * Real.sqrt (C.dualScale e p / norm a) / norm (f₁*f₂)) else 0))
      (fun p hp => (UniqueFactorizationMonoid.moebius e : ℂ) * (C.M / norm e : ℂ) *
        ((UniqueFactorizationMonoid.moebius (f₁*f₂) : ℂ) *
          ∑ b ∈ (boundedNormIdeals F C.L1).filter (fun b => b ≠ ⊥),
            if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then
              (weightedColumn C p.1 * star (weightedColumn C p.2) * C.primitive p hp e * C.primitive p hp a) *
                ∫ q : ℝ × ℝ, frequencyPhase C p q.1 q.2 * rowCoefficient C χ e a f₁ f₂ b q.1 q.2
            else 0)) (by
        intro p hpv hp
        by_cases hd : f₁ ∣ p.1 ∧ f₂ ∣ p.2
        · simp only [if_pos hd, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          obtain ⟨hu,hv⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpv).1
          obtain ⟨hu1,hu2⟩ := column_range C hN _ hu
          obtain ⟨hv1,hv2⟩ := column_range C hN _ hv
          have h := row_fourier_identity C χ hχ hFourier (by linarith) (by linarith)
            e a f₁ f₂ b he ha hf₁ hf₂ (Finset.mem_filter.mp hb).2 p hp hu1 hu2 hv1 hv2
          linear_combination (UniqueFactorizationMonoid.moebius (f₁*f₂) : ℂ) * h
        · simp [hd])
    rw [hrewrite, pairSum_mul, pairSum_mul, pairSum_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro b hb
    apply pair_integral
    have hscale : 0 < rowScale C e a f₁ f₂ := by
      unfold rowScale
      have : 0 < C.N / norm C.d := div_pos (by linarith) (fourier_rectangles_nonzero_ideal_norm_pos C.hd0)
      have : 0 < norm (f₁*f₂) := by simp [ExplicitTerms.norm, map_mul]; exact mul_pos (fourier_rectangles_nonzero_ideal_norm_pos hf₁) (fourier_rectangles_nonzero_ideal_norm_pos hf₂)
      have := fourier_rectangles_nonzero_ideal_norm_pos he
      have := fourier_rectangles_nonzero_ideal_norm_pos ha
      positivity
    have hb1 : 1 ≤ norm b := by
      unfold ExplicitTerms.norm
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.mem_filter.mp hb).2)
    exact (hFourier _ _ hscale hb1).1
  · simp only [if_neg hw]
    simp [Context.pairSum]

theorem maskedE3_eq_fourier_rectangles (C : Context Q) (χ : ℝ → ℝ)
    (hχ : ∀ x ∈ Set.Icc 0 (Real.log 2), χ x = 1) (hFourier : FourierInversion C χ)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hK : 1 ≤ C.K)
    (hnN : norm C.d ≤ 2 * C.N) (B Cq : ℝ) (unit : Bool)
    (hThreshold : Threshold C B Cq) (ρ : Ideal (𝓞 F) → ℂ) :
    maskedE3 C B unit ρ =
      ∑ e ∈ C.mobiusDivisors, (UniqueFactorizationMonoid.moebius e : ℂ) * (C.M / norm e : ℂ) *
        ∑ ij ∈ rectangles F B C.M C.N (norm C.d) (Real.rpow (C.M * C.N) C.δ) Cq,
          ∑ f₁ ∈ divisorBucket F (2 * C.N / norm C.d) ij.1,
            ∑ f₂ ∈ divisorBucket F (2 * C.N / norm C.d) ij.2,
              if C.Y1 B e < norm (f₁ * f₂) ∧ norm (f₁ * f₂) ≤ C.Z1 B e then
                (UniqueFactorizationMonoid.moebius (f₁ * f₂) : ℂ) *
                  ∑ a ∈ C.reflectedRows B unit, ρ a *
                    ∑ b ∈ (boundedNormIdeals F C.L1).filter (fun b => b ≠ ⊥),
                      ∫ q : ℝ × ℝ, frequencyCell C e a f₁ f₂ q.1 q.2 *
                        rowCoefficient C χ e a f₁ f₂ b q.1 q.2
              else 0 := by
  have hrewrite : maskedE3 C B unit ρ =
      C.pairSum (fun p hp => ∑ e ∈ C.mobiusDivisors,
        ∑ ij ∈ rectangles F B C.M C.N (norm C.d) (Real.rpow (C.M*C.N) C.δ) Cq,
          ∑ f₁ ∈ divisorBucket F (2*C.N/norm C.d) ij.1,
            ∑ f₂ ∈ divisorBucket F (2*C.N/norm C.d) ij.2,
              ∑ a ∈ C.reflectedRows B unit,
                ρ a * (C.coefficient p * C.prefactor e p hp * C.primitive p hp a *
                  (if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then
                    if C.Y1 B e < norm (f₁*f₂) ∧ norm (f₁*f₂) ≤ C.Z1 B e then
                      (UniqueFactorizationMonoid.moebius (f₁*f₂) : ℂ) *
                        (Real.sqrt (C.dualScale e p / norm a) / norm (f₁*f₂) : ℂ) *
                          ∑ b ∈ (boundedNormIdeals F C.L1).filter (fun b => b ≠ ⊥),
                            C.reflectedKernel (norm b * Real.sqrt (C.dualScale e p / norm a) / norm (f₁*f₂))
                    else 0
                  else 0))) := by
    unfold maskedE3
    apply pairSum_congr
    intro p hpv hp
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    simp_rw [middle_rectangles C hN hK hnN B Cq hThreshold e he p hpv, Finset.mul_sum]
    simp_rw [Finset.sum_comm (s := C.reflectedRows B unit)]
    apply Finset.sum_congr rfl
    intro ij hij
    apply Finset.sum_congr rfl
    intro f₁ hf₁
    apply Finset.sum_congr rfl
    intro f₂ hf₂
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [hrewrite]
  simp_rw [pairSum_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f₁ hf₁
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f₂ hf₂
  simp_rw [pairSum_mul]
  have he0 := ne_bot_of_mem_idealDivisors he
  have hf₁0 := (Finset.mem_filter.mp hf₁).2.1
  have hf₂0 := (Finset.mem_filter.mp hf₂).2.1
  calc
    _ = ∑ a ∈ C.reflectedRows B unit, ρ a *
      ((UniqueFactorizationMonoid.moebius e : ℂ) * (C.M / norm e : ℂ) *
        (if C.Y1 B e < norm (f₁*f₂) ∧ norm (f₁*f₂) ≤ C.Z1 B e then
          (UniqueFactorizationMonoid.moebius (f₁*f₂) : ℂ) *
            ∑ b ∈ (boundedNormIdeals F C.L1).filter (fun b => b ≠ ⊥),
              ∫ q : ℝ × ℝ, frequencyCell C e a f₁ f₂ q.1 q.2 * rowCoefficient C χ e a f₁ f₂ b q.1 q.2
        else 0)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [cell_identity C χ hχ hFourier hM hN e a f₁ f₂ he0
        (row_nonzero C B unit a ha) hf₁0 hf₂0 B]
    _ = _ := by
      by_cases hw : C.Y1 B e < norm (f₁*f₂) ∧ norm (f₁*f₂) ≤ C.Z1 B e
      · simp only [if_pos hw, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
      · simp [hw]

end DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteFourierRectangles.FourierExpansion

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators ContDiff
open MeasureTheory
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteFourierRectangles
open ExplicitTerms
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private lemma row_scale_bounds (Q M B e f a θ q : ℝ) (hQ : 0 < Q) (hM : 0 < M) (hB : 0 < B)
    (he : 0 < e) (hf : 0 < f) (hθ : 1 ≤ θ) (hq : 1 ≤ q)
    (ha : B ≤ a) (haq : a ≤ q*(2*B))
    (hY : Q*Real.sqrt e/(Real.sqrt (2*B*M)*θ) < f)
    (hZ : f ≤ Q*Real.sqrt e*θ/Real.sqrt (B*M)) :
    1/(Real.sqrt 2*(q*θ)) ≤ Q*Real.sqrt e/(f*Real.sqrt (M*a)) ∧
    Q*Real.sqrt e/(f*Real.sqrt (M*a)) ≤ Real.sqrt 2*(q*θ) := by
  have hθ0 : 0 < θ := by linarith
  have hq0 : 0 < q := by linarith
  have ha0 : 0 < a := lt_of_lt_of_le hB ha
  have hse : 0 < Real.sqrt e := Real.sqrt_pos.2 he
  have hsMa : 0 < Real.sqrt (M*a) := by positivity
  have hsBM : 0 < Real.sqrt (B*M) := by positivity
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs2BM : Real.sqrt (2*B*M) = Real.sqrt 2 * Real.sqrt (B*M) := by
    rw [show 2*B*M=2*(B*M) by ring, Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  have hsMa_le : Real.sqrt (M*a) ≤ Real.sqrt 2*q*Real.sqrt (B*M) := by
    have hh : M*a ≤ (Real.sqrt 2*q*Real.sqrt (B*M))^2 := by
      have hsq : (Real.sqrt 2*q*Real.sqrt (B*M))^2 = 2*q^2*(B*M) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (show 0≤B*M by positivity),
          Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
      rw [hsq]
      nlinarith [mul_nonneg (show 0≤q*(q-1) by positivity) (show 0≤B*M by positivity)]
    exact (Real.sqrt_le_left (by positivity)).2 hh
  have hsBM_le : Real.sqrt (B*M) ≤ Real.sqrt (M*a) := by
    apply Real.sqrt_le_sqrt; nlinarith
  have hfl := (le_div_iff₀ hsBM).mp hZ
  have hfu := (div_lt_iff₀ (mul_pos (by positivity) hθ0)).mp hY
  constructor
  · apply (le_div_iff₀ (mul_pos hf hsMa)).2
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_le_iff₀ (by positivity : 0<Real.sqrt 2*(q*θ))).2
    have h1 := mul_le_mul_of_nonneg_left hsMa_le hf.le
    have h2 := mul_le_mul_of_nonneg_left hfl (mul_pos hs2 hq0).le
    nlinarith
  · apply (div_le_iff₀ (mul_pos hf hsMa)).2
    rw [hs2BM] at hfu
    have h1 := mul_le_mul_of_nonneg_left hsBM_le (mul_pos (mul_pos hf hs2) hθ0).le
    have h2 : Real.sqrt 2*θ ≤ Real.sqrt 2*(q*θ) := by
      have := mul_le_mul_of_nonneg_left hq (mul_pos hs2 hθ0).le
      nlinarith
    have h3 := mul_le_mul_of_nonneg_right h2 (mul_pos hf hsMa).le
    nlinarith

 def logBump : ContDiffBump (Real.log 2 / 2) where
  rIn := Real.log 2 / 2
  rOut := 1 + Real.log 2 / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith
 def logCutoff (x : ℝ) : ℝ := logBump x
private lemma logCutoff_smooth : ContDiff ℝ ∞ logCutoff := logBump.contDiff
private lemma logCutoff_one : ∀ x ∈ Set.Icc 0 (Real.log 2), logCutoff x = 1 := by
  intro x hx
  apply logBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_sub_le_iff]
  change x - Real.log 2 / 2 ≤ Real.log 2 / 2 ∧ Real.log 2 / 2 - x ≤ Real.log 2 / 2
  constructor <;> linarith [hx.1, hx.2]
private lemma logCutoff_support : Function.support logCutoff ⊆ Set.Icc (-1) (1+Real.log 2) := by
  intro x hx
  have hn : |x - Real.log 2 / 2| < 1 + Real.log 2 / 2 := by
    by_contra hh
    have hz : logCutoff x = 0 := logBump.zero_of_le_dist (by simpa only [Real.dist_eq, logBump] using le_of_not_gt hh)
    exact hx hz
  have hh := abs_lt.mp hn
  constructor <;> linarith [hh.1, hh.2]

private lemma all_positive_rows_inversion {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (C : Context Q) (h b : ℝ) (hh : 0 < h) (hb : 1 ≤ b) :
    Integrable (fun p : ℝ × ℝ => MiddleLogKernel.fourierCoefficient C.reflectedKernel logCutoff h b p.1 p.2) ∧
      ∀ x y, MiddleLogKernel.normalizedKernel C.reflectedKernel logCutoff h b x y =
        ∫ p : ℝ × ℝ, MiddleLogKernel.fourierCoefficient C.reflectedKernel logCutoff h b p.1 p.2 *
          Complex.exp (((2*Real.pi*(p.1*x+p.2*y):ℝ):ℂ)*Complex.I) := by
  obtain ⟨A,hA,henv⟩ := bilinear_middle_log_kernel_envelope
    (principalDiscriminant F) (principalComplexPlaces F) C.source (1/2) (5/2)
    (principalDiscriminant_pos F) (principalComplexPlaces_pos F C.hF)
    (Complex.ofRealCLM.contDiff.comp C.hW.smooth)
    (by intro x hx; by_contra hn; exact hx (by simp [Context.source, C.hW.zero_outside x hn]))
    (by norm_num) (by norm_num) logCutoff logCutoff_smooth logCutoff_one logCutoff_support
  let θ := max 1 (max h h⁻¹)
  have hθ : 1 ≤ θ := le_max_left _ _
  have hθ0 : 0 < θ := by linarith
  have hs : 1 ≤ Real.sqrt 2 := by simpa using Real.sqrt_le_sqrt (show (1:ℝ)≤2 by norm_num)
  have hlow : 1/(Real.sqrt 2*θ) ≤ h := by
    apply (div_le_iff₀ (by positivity : 0<Real.sqrt 2*θ)).2
    have hhθ : h⁻¹ ≤ θ := (le_max_right h h⁻¹).trans (le_max_right 1 _)
    have hhprod : 1 ≤ θ*h := by
      have := mul_le_mul_of_nonneg_right hhθ hh.le
      simpa only [inv_mul_cancel₀ hh.ne'] using this
    have ht : θ ≤ Real.sqrt 2*θ := le_mul_of_one_le_left hθ0.le hs
    nlinarith [mul_le_mul_of_nonneg_right ht hh.le]
  have hhigh : h ≤ Real.sqrt 2*θ :=
    ((le_max_left h h⁻¹).trans (le_max_right 1 _)).trans (le_mul_of_one_le_left hθ0.le hs)
  exact ⟨(henv θ b h hθ hb hlow hhigh).2.2.1, (henv θ b h hθ hb hlow hhigh).2.2.2.1⟩

private lemma reflected_row_bounds {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (C : Context Q) (B : ℝ) (unit : Bool) (hB : 1 ≤ B) (hunit : unit=true→B=1)
    {a : Ideal (𝓞 F)} (ha : a ∈ C.reflectedRows B unit) :
    B ≤ norm a ∧ norm a ≤ ExplicitAssembly.LocalTailGeometry.supportedNormBound c*(2*B) := by
  have hupp := (ExplicitAssembly.LocalTailGeometry.reflected_row_norm C B unit hB ha).2
  refine ⟨?_, hupp⟩
  obtain ⟨⟨t,r⟩,htr,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨htr,hmask⟩ := Finset.mem_filter.mp htr
  obtain ⟨ht,hr⟩ := Finset.mem_product.mp htr
  have ht0 : t ≠ ⊥ := fun hz => hmask.2.2 (by simp [hz])
  have ht1 := ExplicitAssembly.LocalTailGeometry.norm_one_le ht0
  have hrB : B ≤ norm r := by
    cases unit
    · exact ((Sieve.mem_paperShell F c B r).mp (Finset.mem_filter.mp hr).1).2.2.1.le
    · have he := ExplicitAssembly.LocalTailGeometry.unit_row_eq_top hr
      change r = ⊤ at he
      simp [he, hunit rfl, ExplicitTerms.norm]
  rw [ExplicitAssembly.LocalTailGeometry.norm_mul]
  exact hrB.trans (le_mul_of_one_le_left (by unfold ExplicitTerms.norm; positivity) ht1)

private lemma frequencyWeight_integrable : Integrable frequencyWeight := by
  have hh := integrable_inv_one_add_sq.mul_prod integrable_inv_one_add_sq
  rw [Measure.volume_eq_prod]
  exact hh.congr (Filter.Eventually.of_forall (fun p => by simp [frequencyWeight, mul_inv_rev, mul_comm]))
private lemma frequencyCell_continuous (C : Context Q) (e a f₁ f₂ : Ideal (𝓞 F)) :
    Continuous (fun p : ℝ × ℝ => frequencyCell C e a f₁ f₂ p.1 p.2) := by
  unfold frequencyCell Context.pairSum
  apply continuous_finsetSum
  intro p hp
  split_ifs <;> try fun_prop
  dsimp only
  split_ifs
  · simp only [frequencyPhase]
    fun_prop
  · exact continuous_const
private lemma frequencyCell_bound (C : Context Q) (e a f₁ f₂ : Ideal (𝓞 F)) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ p : ℝ × ℝ, ‖frequencyCell C e a f₁ f₂ p.1 p.2‖ ≤ J := by
  let J := ∑ p ∈ C.pairs, if hp : C.ValidPair p then
    ‖weightedColumn C p.1 * star (weightedColumn C p.2) * C.primitive p hp e * C.primitive p hp a‖ else 0
  refine ⟨J, Finset.sum_nonneg (by intros; split_ifs <;> positivity), ?_⟩
  intro x
  unfold frequencyCell Context.pairSum
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  split_ifs <;> try simp
  split_ifs
  · rw [norm_mul]
    have hphase : ‖frequencyPhase C p x.1 x.2‖ = 1 := by
      simp [frequencyPhase, Complex.norm_exp]
    simp only [hphase, mul_one, norm_mul, starRingEnd_apply, norm_star]
    rfl
  · simp; positivity
private lemma weightedCell_integrable (C : Context Q) (e a f₁ f₂ : Ideal (𝓞 F)) :
    Integrable (fun p : ℝ × ℝ => frequencyWeight p * ‖frequencyCell C e a f₁ f₂ p.1 p.2‖) := by
  obtain ⟨J,hJ,hb⟩ := frequencyCell_bound C e a f₁ f₂
  apply Integrable.mono' (frequencyWeight_integrable.mul_const J)
  · have hw : Continuous frequencyWeight := by
      unfold frequencyWeight
      exact (by fun_prop : Continuous (fun p : ℝ × ℝ => (1+p.1^2)*(1+p.2^2))).inv₀
        (fun p => ne_of_gt (by positivity))
    exact hw.aestronglyMeasurable.mul (frequencyCell_continuous C e a f₁ f₂).norm.aestronglyMeasurable
  · filter_upwards with p
    have hw : 0 ≤ frequencyWeight p := by unfold frequencyWeight; positivity
    rw [Real.norm_of_nonneg (mul_nonneg hw (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hb p) hw

private lemma uniform_row_envelope {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (hF : NumberField.IsTotallyComplex F) (W : ℝ → ℝ) (hW : Sieve.SieveWeight W) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : Context Q, C.W = W →
      ∀ (B : ℝ) (unit : Bool), 1 ≤ C.M → 1 ≤ C.N → 0 < C.δ → 1 ≤ B →
        (unit=true→B=1) → ∀ e a f : Ideal (𝓞 F), e ≠ ⊥ → f ≠ ⊥ →
        a ∈ C.reflectedRows B unit → C.Y1 B e < norm f → norm f ≤ C.Z1 B e →
        ∀ b : ℝ, 1 ≤ b → ∀ t s : ℝ,
          ‖MiddleLogKernel.fourierCoefficient C.reflectedKernel logCutoff
            ((C.N/norm C.d)*Real.sqrt (norm e)/(norm f*Real.sqrt (C.M*norm a))) b t s‖ ≤
              A * Real.rpow (C.M*C.N) C.δ * b⁻¹ ^ 2 / ((1+t^2)*(1+s^2)) := by
  obtain ⟨A,hA,henv⟩ := bilinear_middle_log_kernel_envelope
    (principalDiscriminant F) (principalComplexPlaces F) (fun x => (W x:ℂ)) (1/2) (5/2)
    (principalDiscriminant_pos F) (principalComplexPlaces_pos F hF)
    (Complex.ofRealCLM.contDiff.comp hW.smooth)
    (by intro x hx; by_contra hn; exact hx (by simp [hW.zero_outside x hn]))
    (by norm_num) (by norm_num) logCutoff logCutoff_smooth logCutoff_one logCutoff_support
  let q := ExplicitAssembly.LocalTailGeometry.supportedNormBound c
  have hq : 1 ≤ q := ExplicitAssembly.LocalTailGeometry.supportedNormBound_one_le c
  refine ⟨A*q, by positivity, ?_⟩
  intro C hCW B unit hM hN hδ hB hunit e a f he hf ha hY hZ b hb t s
  have hn : 0 < norm C.d := lt_of_lt_of_le zero_lt_one
    (ExplicitAssembly.LocalTailGeometry.norm_one_le C.hd0)
  have he0 : 0 < norm e := lt_of_lt_of_le zero_lt_one
    (ExplicitAssembly.LocalTailGeometry.norm_one_le he)
  have hf0 : 0 < norm f := lt_of_lt_of_le zero_lt_one
    (ExplicitAssembly.LocalTailGeometry.norm_one_le hf)
  let θ := Real.rpow (C.M*C.N) C.δ
  have hθ : 1 ≤ θ := Real.one_le_rpow (by nlinarith : 1 ≤ C.M*C.N) hδ.le
  have hθ0 : 0 < θ := by linarith
  have hrpow : Real.rpow (C.M*C.N) (-C.δ) = θ⁻¹ := Real.rpow_neg (by nlinarith : 0 ≤ C.M*C.N) C.δ
  have hY' : (C.N/norm C.d)*Real.sqrt (norm e)/(Real.sqrt (2*B*C.M)*θ)<norm f := by
    convert hY using 1
    unfold Context.Y1
    rw [hrpow]
    ring
  have hZ' : norm f ≤ (C.N/norm C.d)*Real.sqrt (norm e)*θ/Real.sqrt (B*C.M) := by
    convert hZ using 1
    unfold Context.Z1 θ
    ring
  have hra := reflected_row_bounds C B unit hB hunit ha
  have hs := row_scale_bounds (C.N/norm C.d) C.M B (norm e) (norm f) (norm a) θ q
    (div_pos (by linarith) hn) (by linarith) (by linarith) he0 hf0 hθ hq hra.1 hra.2 hY' hZ'
  have hqθ : 1 ≤ q*θ := by nlinarith
  have hcoeff := (henv (q*θ) b ((C.N/norm C.d)*Real.sqrt (norm e)/(norm f*Real.sqrt (C.M*norm a)))
    hqθ hb hs.1 hs.2).1 t s
  have hk : C.reflectedKernel = SquareSecondPass.reflectedTransform (principalDiscriminant F)
      (principalComplexPlaces F) (fun x => (W x:ℂ)) := by
    have hs : C.source = fun x => (W x:ℂ) := by ext x; simp [Context.source, hCW]
    simp only [Context.reflectedKernel, hs]
  rw [hk]
  convert hcoeff using 1 <;> ring

private lemma moebius_le_one {F : Type} [Field F] [NumberField F] (a : Ideal (𝓞 F)) :
    ‖(UniqueFactorizationMonoid.moebius a : ℂ)‖ ≤ 1 := by
  rw [UniqueFactorizationMonoid.moebius]
  split_ifs
  · rw [Int.cast_pow, Int.cast_neg, Int.cast_one, norm_pow, norm_neg, norm_one, one_pow]
  · simp
private lemma integral_product_bound (f g : ℝ × ℝ → ℂ) (J : ℝ) (hJ : 0 ≤ J)
    (hint : Integrable (fun p => frequencyWeight p * ‖f p‖))
    (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g)
    (hbound : ∀ p, ‖g p‖ ≤ J * frequencyWeight p) :
    ‖∫ p, f p * g p‖ ≤ J * ∫ p, frequencyWeight p * ‖f p‖ := by
  have hw : ∀ p, 0 ≤ frequencyWeight p := fun p => by unfold frequencyWeight; positivity
  have hmul : Integrable (fun p => f p * g p) := by
    apply Integrable.mono' (hint.const_mul J)
    · exact hf.mul hg
    · filter_upwards with p
      rw [norm_mul]
      have hh := mul_le_mul_of_nonneg_left (hbound p) (norm_nonneg (f p))
      nlinarith
  calc
    ‖∫ p, f p*g p‖ ≤ ∫ p, ‖f p*g p‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p, J*(frequencyWeight p*‖f p‖) := by
      apply integral_mono hmul.norm (hint.const_mul J)
      intro p
      dsimp only
      rw [norm_mul]
      have hh := mul_le_mul_of_nonneg_left (hbound p) (norm_nonneg (f p))
      nlinarith
    _ = _ := integral_const_mul _ _

set_option maxHeartbeats 1000000

theorem fourier_rows_bound
    (D : Sieve.AllIndexNormalizedFamilyData Q) (core : D.bad = c)
    (hF : NumberField.IsTotallyComplex F) (W : ℝ → ℝ) (hW : Sieve.SieveWeight W) :
    ∃ A : ℝ, 0 < A ∧
      ∀ C : Context Q, C.D = D → C.W = W →
      1 ≤ C.M → 1 ≤ C.N → 0 < C.δ → 1 ≤ C.K → C.K ≤ C.M →
      norm C.d ≤ 2 * C.N →
      Function.support C.lam ⊆ (Sieve.paperShell F c C.N : Set (Ideal (𝓞 F))) →
      ∀ (B Cq : ℝ) (unit : Bool), 1 ≤ B → B ≤ C.K →
      (unit = true → B = 1) → 1 ≤ Cq → Threshold C B Cq →
      ∀ ρ : Ideal (𝓞 F) → ℂ,
        (∀ a ∈ C.reflectedRows B unit, ‖ρ a‖ ≤ 1) →
        ‖maskedE3 C B unit ρ‖ ≤ A * C.M * Real.rpow (C.M * C.N) C.δ *
          dualNormCost C * integratedCost C B Cq unit := by
  obtain ⟨A,hA,henv⟩ := uniform_row_envelope (Q := Q) hF W hW
  refine ⟨A,hA,?_⟩
  intro C hCD hCW hM hN hδ hK hKM hnN hlam B Cq unit hB hBK hunit hCq hT ρ hρ
  let θ := Real.rpow (C.M*C.N) C.δ
  let I := fun e a f₁ f₂ : Ideal (𝓞 F) =>
    ∫ p : ℝ × ℝ, frequencyWeight p * ‖frequencyCell C e a f₁ f₂ p.1 p.2‖
  have hI : ∀ e a f₁ f₂, 0 ≤ I e a f₁ f₂ := by
    intros
    apply integral_nonneg
    intro p
    exact mul_nonneg (by unfold frequencyWeight; positivity) (norm_nonneg _)
  have hθ : 0 ≤ θ := Real.rpow_nonneg (by nlinarith) _
  have hdual : 0 ≤ dualNormCost C := Finset.sum_nonneg (fun b hb => sq_nonneg _)
  have hfac : 0 ≤ A*θ*dualNormCost C := mul_nonneg (mul_nonneg hA.le hθ) hdual
  have hcell : ∀ e ∈ C.mobiusDivisors, ∀ a ∈ C.reflectedRows B unit,
      ∀ f₁ f₂ : Ideal (𝓞 F), f₁ ≠ ⊥ → f₂ ≠ ⊥ →
      C.Y1 B e < norm (f₁*f₂) → norm (f₁*f₂) ≤ C.Z1 B e →
      ∀ b ∈ (boundedNormIdeals F C.L1).filter (fun b => b ≠ ⊥),
      ‖∫ p : ℝ × ℝ, frequencyCell C e a f₁ f₂ p.1 p.2 *
        FourierExpansion.rowCoefficient C logCutoff e a f₁ f₂ b p.1 p.2‖ ≤
          (A*θ*(norm b)⁻¹ ^ 2) * I e a f₁ f₂ := by
    intro e he a ha f₁ f₂ hf₁ hf₂ hY hZ b hb
    have he0 := ne_bot_of_mem_idealDivisors he
    have hb0 := (Finset.mem_filter.mp hb).2
    have hb1 := ExplicitAssembly.LocalTailGeometry.norm_one_le hb0
    have ha0 : a ≠ ⊥ := by
      have han := (ExplicitAssembly.LocalTailGeometry.reflected_row_norm C B unit hB ha).1
      intro hz; simp [hz, ExplicitTerms.norm] at han; linarith
    have hscale : 0 < FourierExpansion.rowScale C e a f₁ f₂ := by
      unfold FourierExpansion.rowScale
      have hd := ExplicitAssembly.LocalTailGeometry.norm_one_le C.hd0
      have he' := ExplicitAssembly.LocalTailGeometry.norm_one_le he0
      have hf' := ExplicitAssembly.LocalTailGeometry.norm_one_le (mul_ne_zero hf₁ hf₂)
      have ha' := ExplicitAssembly.LocalTailGeometry.norm_one_le ha0
      positivity
    have hcf := (all_positive_rows_inversion C (FourierExpansion.rowScale C e a f₁ f₂) (norm b) hscale hb1).1
    apply integral_product_bound _ _ (A*θ*(norm b)⁻¹ ^ 2) (by positivity)
      (weightedCell_integrable C e a f₁ f₂)
      (frequencyCell_continuous C e a f₁ f₂).aestronglyMeasurable hcf.aestronglyMeasurable
    intro p
    have hh := henv C hCW B unit hM hN hδ hB hunit e a (f₁*f₂) he0
      (mul_ne_zero hf₁ hf₂) ha hY hZ (norm b) hb1 p.1 p.2
    simpa only [FourierExpansion.rowCoefficient, FourierExpansion.rowScale, frequencyWeight, div_eq_mul_inv] using hh
  have hsum_b : ∀ e ∈ C.mobiusDivisors, ∀ a ∈ C.reflectedRows B unit,
      ∀ f₁ f₂ : Ideal (𝓞 F), f₁ ≠ ⊥ → f₂ ≠ ⊥ →
      C.Y1 B e < norm (f₁*f₂) → norm (f₁*f₂) ≤ C.Z1 B e →
      ‖ρ a * ∑ b ∈ (boundedNormIdeals F C.L1).filter (fun b => b ≠ ⊥),
        ∫ p : ℝ × ℝ, frequencyCell C e a f₁ f₂ p.1 p.2 *
          FourierExpansion.rowCoefficient C logCutoff e a f₁ f₂ b p.1 p.2‖ ≤
            A*θ*dualNormCost C*I e a f₁ f₂ := by
    intro e he a ha f₁ f₂ hf₁ hf₂ hY hZ
    rw [norm_mul]
    calc
      _ ≤ 1 * ∑ b ∈ (boundedNormIdeals F C.L1).filter (fun b => b ≠ ⊥),
        ‖∫ p : ℝ × ℝ, frequencyCell C e a f₁ f₂ p.1 p.2 *
          FourierExpansion.rowCoefficient C logCutoff e a f₁ f₂ b p.1 p.2‖ :=
        mul_le_mul (hρ a ha) (norm_sum_le _ _) (norm_nonneg _) zero_le_one
      _ ≤ ∑ b ∈ (boundedNormIdeals F C.L1).filter (fun b => b ≠ ⊥),
        A*θ*(norm b)⁻¹ ^ 2*I e a f₁ f₂ := by
        rw [one_mul]
        exact Finset.sum_le_sum (fun b hb => hcell e he a ha f₁ f₂ hf₁ hf₂ hY hZ b hb)
      _ = _ := by simp only [dualNormCost, Finset.mul_sum, Finset.sum_mul]
  let rect := rectangles F B C.M C.N (norm C.d) θ Cq
  let bucket := divisorBucket F (2*C.N/norm C.d)
  let cost := ∑ e ∈ C.mobiusDivisors, (norm e)⁻¹ *
    ∑ ij ∈ rect, ∑ f₁ ∈ bucket ij.1, ∑ f₂ ∈ bucket ij.2,
      ∑ a ∈ C.reflectedRows B unit, I e a f₁ f₂
  have hcost : integratedCost C B Cq unit = cost := by
    unfold integratedCost frequencyCost rectangleCost
    simp only [Finset.mul_sum]
    have rearr (p : ℝ × ℝ) (e : Ideal (𝓞 F)) (v : ℝ) :
        frequencyWeight p * ((norm e)⁻¹ * v) = (norm e)⁻¹ * (frequencyWeight p * v) := by ring
    simp_rw [rearr]
    simp only [← Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro e he
      rw [integral_const_mul]
      congr 1
      simp only [Finset.mul_sum]
      rw [integral_finsetSum]
      ·
        apply Finset.sum_congr rfl
        intro ij hij
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro f₁ hf₁
          rw [integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro f₂ hf₂
            rw [integral_finsetSum _ (fun a ha => weightedCell_integrable C e a f₁ f₂)]
          · intro f₂ hf₂
            exact integrable_finsetSum _ (fun a ha => weightedCell_integrable C e a f₁ f₂)
        · intro f₁ hf₁
          exact integrable_finsetSum _ (fun f₂ hf₂ => integrable_finsetSum _ (fun a ha => weightedCell_integrable C e a f₁ f₂))
      · intro ij hij
        exact integrable_finsetSum _ (fun f₁ hf₁ => integrable_finsetSum _ (fun f₂ hf₂ => integrable_finsetSum _ (fun a ha => weightedCell_integrable C e a f₁ f₂)))
    · intro e he
      have hh : Integrable (fun p : ℝ × ℝ =>
          ∑ ij ∈ rect, ∑ f₁ ∈ bucket ij.1, ∑ f₂ ∈ bucket ij.2,
            ∑ a ∈ C.reflectedRows B unit, frequencyWeight p * ‖frequencyCell C e a f₁ f₂ p.1 p.2‖) :=
        integrable_finsetSum _ (fun ij hij => integrable_finsetSum _ (fun f₁ hf₁ => integrable_finsetSum _ (fun f₂ hf₂ => integrable_finsetSum _ (fun a ha => weightedCell_integrable C e a f₁ f₂))))
      have hh' := hh.const_mul (norm e)⁻¹
      simpa only [rect, bucket, θ, ← Finset.mul_sum] using hh'
  rw [FourierExpansion.maskedE3_eq_fourier_rectangles C logCutoff logCutoff_one
    (all_positive_rows_inversion C) hM hN hK hnN B Cq unit hT ρ]
  rw [hcost]
  calc
    _ ≤ ∑ e ∈ C.mobiusDivisors, (C.M*(norm e)⁻¹) *
        ∑ ij ∈ rect, ∑ f₁ ∈ bucket ij.1, ∑ f₂ ∈ bucket ij.2,
          ∑ a ∈ C.reflectedRows B unit, A*θ*dualNormCost C*I e a f₁ f₂ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e he
      rw [norm_mul, norm_mul]
      have he0 := ne_bot_of_mem_idealDivisors he
      have hen := ExplicitAssembly.LocalTailGeometry.norm_one_le he0
      have hpref : ‖(C.M/norm e : ℂ)‖ = C.M*(norm e)⁻¹ := by
        rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_eq_mul_inv]
      rw [hpref]
      have hnon : 0 ≤ C.M*(norm e)⁻¹ := by positivity
      apply mul_le_mul (mul_le_of_le_one_left hnon (moebius_le_one e)) ?_ (norm_nonneg _) hnon
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro ij hij
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro f₁ hf₁
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro f₂ hf₂
      have hf₁0 := (Finset.mem_filter.mp hf₁).2.1
      have hf₂0 := (Finset.mem_filter.mp hf₂).2.1
      split_ifs with hw
      · rw [norm_mul]
        apply (mul_le_of_le_one_left (norm_nonneg _) (moebius_le_one (f₁*f₂))).trans
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun a ha => hsum_b e he a ha f₁ f₂ hf₁0 hf₂0 hw.1 hw.2)
      · simp only [norm_zero]
        exact Finset.sum_nonneg (fun a ha => mul_nonneg hfac (hI e a f₁ f₂))
    _ = A*C.M*θ*dualNormCost C*cost := by
      dsimp only [cost]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro ij hij
      apply Finset.sum_congr rfl
      intro f₁ hf₁
      apply Finset.sum_congr rfl
      intro f₂ hf₂
      apply Finset.sum_congr rfl
      intro a ha
      ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteFourierRectangles

end

end
