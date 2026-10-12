module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.LargeDivisors.SupportedRowsAndReflectedProductBounds

@[expose] public section

section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDual

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def divisorBin (P : ℝ) : Finset (Ideal (𝓞 F)) :=
  (boundedNormIdeals F (2 * P)).filter (ErrorRectangles.InBin P)

def binEnergy (C : Context Q) (P : ℝ) : ℝ :=
  ∑ f ∈ divisorBin (F := F) P, divisorEnergy C f

private lemma scalar_identity (M B E J A : ℝ) (hM : 0 < M) (hB : 0 < B)
    (hE : 0 < E) (hJ : 0 < J) (hA : 0 < A) :
    M / (E * Real.sqrt J) * Real.sqrt (E * J / M / A) =
      (1 / Real.sqrt E) * Real.sqrt (M / B) * Real.sqrt (B / A) := by
  rw [Real.sqrt_div (by positivity), Real.sqrt_div (by positivity),
    Real.sqrt_mul hE.le, Real.sqrt_div hM.le, Real.sqrt_div hB.le]
  have se := Real.sq_sqrt hE.le
  have sm := Real.sq_sqrt hM.le
  have sb := Real.sq_sqrt hB.le
  have hse := (Real.sqrt_pos.mpr hE).ne'
  have hsm := (Real.sqrt_pos.mpr hM).ne'
  have hsb := (Real.sqrt_pos.mpr hB).ne'
  have hsj := (Real.sqrt_pos.mpr hJ).ne'
  have hsa := (Real.sqrt_pos.mpr hA).ne'
  field_simp
  nlinarith
private lemma energy_nonneg (C : Context Q) (f : Ideal (𝓞 F)) : 0 ≤ divisorEnergy C f := by
  unfold divisorEnergy
  apply Finset.sum_nonneg
  intro u hu
  split <;> positivity
private lemma bin_cauchy (C : Context Q) (P : ℝ) :
    (∑ f ∈ divisorBin (F := F) P, Real.sqrt (divisorEnergy C f)) ≤
      Real.sqrt ((divisorBin (F := F) P).card : ℝ) * Real.sqrt (binEnergy C P) := by
  simpa [binEnergy] using Real.sum_sqrt_mul_sqrt_le (divisorBin (F := F) P)
    (f := fun _ => 1) (g := divisorEnergy C) (fun _ => by norm_num) (energy_nonneg C)
private lemma bin_count (A : ℝ) (hcount : ∀ X : ℝ, 1 ≤ X →
    ((boundedNormIdeals F X).card : ℝ) ≤ A * X) (P : ℝ) (hP : 1 ≤ P) :
    ((divisorBin (F := F) P).card : ℝ) ≤ 2 * A * P := by
  calc
    _ ≤ ((boundedNormIdeals F (2 * P)).card : ℝ) := by
      exact_mod_cast Finset.card_filter_le _ _
    _ ≤ A * (2 * P) := hcount _ (by linarith)
    _ = _ := by ring
private lemma bin_double_cauchy (C : Context Q) (A : ℝ) (hA : 1 ≤ A)
    (hcount : ∀ X : ℝ, 1 ≤ X → ((boundedNormIdeals F X).card : ℝ) ≤ A * X)
    (P : ℝ × ℝ) (hP1 : 1 ≤ P.1) (hP2 : 1 ≤ P.2) :
    (∑ f₁ ∈ divisorBin (F := F) P.1, ∑ f₂ ∈ divisorBin (F := F) P.2,
      Real.sqrt (divisorEnergy C f₁ * divisorEnergy C f₂)) ≤
      (2 * A) * Real.sqrt (P.1 * P.2) *
        Real.sqrt (binEnergy C P.1 * binEnergy C P.2) := by
  have hn (P : ℝ) : 0 ≤ binEnergy C P := Finset.sum_nonneg (fun _ _ => energy_nonneg C _)
  have hc (P : ℝ) (hP : 1 ≤ P) :
      (∑ f ∈ divisorBin (F := F) P, Real.sqrt (divisorEnergy C f)) ≤
        Real.sqrt (2 * A * P) * Real.sqrt (binEnergy C P) :=
    (bin_cauchy C P).trans (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (bin_count A hcount P hP)) (Real.sqrt_nonneg _))
  calc
    _ = (∑ f ∈ divisorBin (F := F) P.1, Real.sqrt (divisorEnergy C f)) *
        (∑ f ∈ divisorBin (F := F) P.2, Real.sqrt (divisorEnergy C f)) := by
      simp_rw [Real.sqrt_mul (energy_nonneg C _), Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm
    _ ≤ (Real.sqrt (2 * A * P.1) * Real.sqrt (binEnergy C P.1)) *
        (Real.sqrt (2 * A * P.2) * Real.sqrt (binEnergy C P.2)) :=
      mul_le_mul (hc _ hP1) (hc _ hP2) (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))
        (by positivity)
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * A),
        Real.sqrt_mul (by positivity : 0 ≤ 2 * A),
        Real.sqrt_mul (by linarith : 0 ≤ P.1), Real.sqrt_mul (hn P.1)]
      have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * A)
      calc
        _ = (Real.sqrt (2 * A)) ^ 2 * (Real.sqrt P.1 * Real.sqrt P.2) *
          (Real.sqrt (binEnergy C P.1) * Real.sqrt (binEnergy C P.2)) := by ring
        _ = _ := by rw [hs]

private lemma bin_divisors_eq (P : ℝ) (u : Ideal (𝓞 F)) (hu : u ≠ ⊥) :
    binDivisors P u = (divisorBin (F := F) P).filter (fun f => f ∣ u) := by
  ext f
  simp only [binDivisors, divisorBin, Finset.mem_filter, mem_idealDivisors hu,
    mem_boundedNormIdeals]
  constructor
  · rintro ⟨hd, hb⟩
    exact ⟨⟨hb.2.2, hb⟩, hd⟩
  · rintro ⟨⟨_, hb⟩, hd⟩
    exact ⟨hd, hb⟩
private lemma row_nonzero (C : Context Q) (B : ℝ) (unit : Bool)
    (a : Ideal (𝓞 F)) (ha : a ∈ C.reflectedRows B unit) : a ≠ ⊥ := by
  obtain ⟨tr, ht, rfl⟩ := Finset.mem_image.mp ha
  exact (Finset.mem_filter.mp ht).2.2.2
private lemma norm_pos (a : Ideal (𝓞 F)) (ha : a ≠ ⊥) : 0 < norm a := by
  unfold norm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ha)
private lemma scalar_complex (C : Context Q) (M B E J A : ℝ) (hM : 0 < M) (hB : 0 < B)
    (hE : 0 < E) (hJ : 0 < J) (hA : 0 < A) :
    (M : ℂ) / ((E : ℂ) * (Real.sqrt J : ℂ)) * (Real.sqrt (E * J / M / A) : ℂ) =
      (1 / Real.sqrt E : ℝ) * (Real.sqrt (M / B) : ℂ) * (Real.sqrt (B / A) : ℂ) := by
  exact_mod_cast scalar_identity M B E J A hM hB hE hJ hA
private lemma prefactor_row (C : Context Q) (B : ℝ) (e a : Ideal (𝓞 F))
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p)
    (hM : 0 < C.M) (hB : 0 < B) (he : e ≠ ⊥) (ha : a ≠ ⊥) :
    C.prefactor e p hp * (Real.sqrt (C.dualScale e p / norm a) : ℂ) =
      (UniqueFactorizationMonoid.moebius e : ℂ) *
      (1 / Real.sqrt (norm e) : ℝ) * (Real.sqrt (C.M / B) : ℂ) *
      (Real.sqrt (B / norm a) : ℂ) * C.primitive p hp e := by
  have hj : p.1 * p.2 ≠ ⊥ := by
    simpa only [← Ideal.zero_eq_bot] using mul_ne_zero (by simpa using hp.hu0) (by simpa using hp.hv0)
  unfold Context.prefactor Context.dualScale
  have hs := scalar_complex C C.M B (norm e) (norm (p.1*p.2)) (norm a)
    hM hB (norm_pos e he) (norm_pos _ hj) (norm_pos a ha)
  calc
    _ = (UniqueFactorizationMonoid.moebius e : ℂ) * C.primitive p hp e *
      ((C.M : ℂ) / ((norm e : ℂ) * (Real.sqrt (norm (p.1*p.2)) : ℂ)) *
      (Real.sqrt (norm e * norm (p.1*p.2) / C.M / norm a) : ℂ)) := by ring
    _ = _ := by rw [hs]; ring
 def weight (C : Context Q) (B : ℝ) (e f₁ f₂ : Ideal (𝓞 F)) : ℂ :=
  if C.Z1 B e < norm (f₁ * f₂) then
    (UniqueFactorizationMonoid.moebius (f₁ * f₂) : ℂ) / (norm (f₁ * f₂) : ℂ)
  else 0
private lemma bucket_eq (C : Context Q) (B : ℝ) (unit : Bool) (e : Ideal (𝓞 F))
    (P : ℝ × ℝ) (hM : 0 < C.M) (hB : 0 < B) (he : e ≠ ⊥) :
    bucket C B unit e P =
    ((UniqueFactorizationMonoid.moebius e : ℂ) *
      (1 / Real.sqrt (norm e) : ℝ) * (Real.sqrt (C.M / B) : ℂ) * (C.kappa * C.mass)) *
      ∑ f₁ ∈ divisorBin (F := F) P.1, ∑ f₂ ∈ divisorBin (F := F) P.2,
        weight C B e f₁ f₂ * ∑ a ∈ C.reflectedRows B unit,
          (Real.sqrt (B / norm a) : ℂ) * rowDivisorBlock C e f₁ f₂ a := by
  unfold bucket Context.pairSum
  simp_rw [Finset.mul_sum]
  simp_rw [rowDivisorBlock, Context.pairSum, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := C.reflectedRows B unit) (t := C.pairs),
    Finset.sum_comm (s := divisorBin (F := F) P.2) (t := C.pairs),
    Finset.sum_comm (s := divisorBin (F := F) P.1) (t := C.pairs)]
  apply Finset.sum_congr rfl
  intro p hp
  simp_rw [Finset.sum_comm (s := divisorBin (F := F) P.2) (t := C.reflectedRows B unit),
    Finset.sum_comm (s := divisorBin (F := F) P.1) (t := C.reflectedRows B unit)]
  by_cases hpv : C.ValidPair p
  · simp only [dif_pos hpv]
    unfold bucketDensity
    rw [bin_divisors_eq _ _ hpv.hu0, bin_divisors_eq _ _ hpv.hv0]
    simp_rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro f₁ hf₁
    by_cases hd₁ : f₁ ∣ p.1
    · simp only [if_pos hd₁, Finset.mul_sum, true_and]
      apply Finset.sum_congr rfl
      intro f₂ hf₂
      by_cases hd₂ : f₂ ∣ p.2
      · simp only [if_pos hd₂, if_pos (And.intro hd₁ hd₂)]
        have hs := prefactor_row C B e a p hpv hM hB he (row_nonzero C B unit a ha)
        unfold weight
        calc
          _ = C.coefficient p * (C.prefactor e p hpv *
            (Real.sqrt (C.dualScale e p / norm a) : ℂ)) * C.primitive p hpv a *
            (C.kappa * C.mass) *
              (if C.Z1 B e < norm (f₁ * f₂) then
                (UniqueFactorizationMonoid.moebius (f₁ * f₂) : ℂ) / (norm (f₁ * f₂) : ℂ)
               else 0) := by ring
          _ = _ := by rw [hs]; ring
      · simp [hd₂]
    · simp [hd₁]
  · simp [hpv]

private lemma weight_bound (C : Context Q) (B : ℝ) (e f₁ f₂ : Ideal (𝓞 F))
    (P : ℝ × ℝ) (hP1 : 1 ≤ P.1) (hP2 : 1 ≤ P.2)
    (hf₁ : ErrorRectangles.InBin P.1 f₁) (hf₂ : ErrorRectangles.InBin P.2 f₂) :
    ‖weight C B e f₁ f₂‖ ≤ 1 / (P.1 * P.2) := by
  have low (P : ℝ) (f : Ideal (𝓞 F)) (hf : ErrorRectangles.InBin P f) : P ≤ norm f := by
    by_cases h : P = 1
    · simpa [h] using hf.2.1
    · exact le_of_lt (by simpa [h] using hf.2.1)
  have hn : 0 < norm (f₁*f₂) := norm_pos _ (by
    simpa only [← Ideal.zero_eq_bot] using mul_ne_zero (by simpa using hf₁.1) (by simpa using hf₂.1))
  have hl : P.1 * P.2 ≤ norm (f₁ * f₂) := by
    have hh := mul_le_mul (low _ _ hf₁) (low _ _ hf₂) (by linarith : 0 ≤ P.2)
      (norm_pos _ hf₁.1).le
    simpa [norm, map_mul] using hh
  have hm : ‖(UniqueFactorizationMonoid.moebius (f₁*f₂) : ℂ)‖ ≤ 1 := by
    rw [UniqueFactorizationMonoid.moebius]; split <;> simp
  unfold weight
  split
  · rw [norm_div]
    have hn' : ‖(norm (f₁*f₂) : ℂ)‖ = norm (f₁*f₂) := by simp [Complex.norm_real, abs_of_pos hn]
    rw [hn']
    exact (div_le_div_of_nonneg_right hm hn.le).trans (one_div_le_one_div_of_le (by positivity) hl)
  · simp only [norm_zero]
    positivity
private lemma norm_row_sum (C : Context Q) (B : ℝ) (unit : Bool) (e f₁ f₂ : Ideal (𝓞 F)) :
    ‖∑ a ∈ C.reflectedRows B unit, (Real.sqrt (B / norm a) : ℂ) *
      rowDivisorBlock C e f₁ f₂ a‖ ≤
      ∑ a ∈ C.reflectedRows B unit, Real.sqrt (B / norm a) * ‖rowDivisorBlock C e f₁ f₂ a‖ := by
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro a ha
  simp [norm_mul, Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem rectangle_bucket_bound :
    ∃ J : ℝ, 0 < J ∧
      ∀ H : ℝ, 0 < H →
      ∀ (C : Context Q),
      ∀ (B : ℝ) (unit : Bool), (unit = true → B = 1) →
        1 ≤ C.M → 1 ≤ C.N → 1 ≤ B → B ≤ C.K → C.K ≤ C.M →
        1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
      ∀ e ∈ C.mobiusDivisors,
      ∀ P ∈ admissibleRectangles C B,
        (∀ f₁ f₂ : Ideal (𝓞 F),
          ErrorRectangles.InBin P.1 f₁ → ErrorRectangles.InBin P.2 f₂ →
          (∑ a ∈ C.reflectedRows B unit,
              Real.sqrt (B / norm a) * ‖rowDivisorBlock C e f₁ f₂ a‖) ≤
            H * Real.sqrt
              (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
               ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) *
              Real.sqrt (divisorEnergy C f₁ * divisorEnergy C f₂)) →
        ‖bucket C B unit e P‖ ≤
          J * H * ‖C.kappa * C.mass‖ * Real.sqrt (C.M / B) *
            ErrorRectangles.largeScore C B P *
              Real.sqrt (binEnergy C P.1 * binEnergy C P.2) := by
  obtain ⟨A, hA, hcount⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound F
  refine ⟨2 * A, by linarith, ?_⟩
  intro H hH C B unit hunit hM hN hB hBK hKM hn hnN e he P hP hbound
  have hp := ErrorRectangles.rectangle_endpoints C P (Finset.mem_filter.mp hP).1
  have hp1 : 0 < P.1 := by linarith [hp.1]
  have hp2 : 0 < P.2 := by linarith [hp.2.1]
  have he0 : e ≠ ⊥ := ne_bot_of_mem_idealDivisors he
  have he1 : 1 ≤ norm e := by
    unfold norm
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr he0)
  have hcoef : ‖(UniqueFactorizationMonoid.moebius e : ℂ) *
    (1 / Real.sqrt (norm e) : ℝ) * (Real.sqrt (C.M / B) : ℂ) * (C.kappa * C.mass)‖ ≤
    Real.sqrt (C.M / B) * ‖C.kappa * C.mass‖ := by
    have hm : ‖(UniqueFactorizationMonoid.moebius e : ℂ)‖ ≤ 1 := by
      rw [UniqueFactorizationMonoid.moebius]; split <;> simp
    have hs : 1 ≤ Real.sqrt (norm e) := by
      simpa using Real.sqrt_le_sqrt he1
    have hh : ‖(UniqueFactorizationMonoid.moebius e : ℂ)‖ * (1 / Real.sqrt (norm e)) ≤ 1 :=
      (mul_le_mul_of_nonneg_right hm (by positivity)).trans (by simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hs)
    rw [norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (norm e)),
      abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ 1 * Real.sqrt (C.M / B) * ‖C.kappa * C.mass‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  let U := Real.sqrt (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
               ErrorRectangles.U Q B (C.N / (norm C.d * P.2)))
  have hterm (f₁) (hf₁ : f₁ ∈ divisorBin (F := F) P.1)
      (f₂) (hf₂ : f₂ ∈ divisorBin (F := F) P.2) :
      ‖weight C B e f₁ f₂ * ∑ a ∈ C.reflectedRows B unit,
        (Real.sqrt (B / norm a) : ℂ) * rowDivisorBlock C e f₁ f₂ a‖ ≤
        (1 / (P.1 * P.2)) * (H * U) * Real.sqrt (divisorEnergy C f₁ * divisorEnergy C f₂) := by
    rw [norm_mul]
    have hw := weight_bound C B e f₁ f₂ P hp.1 hp.2.1 (Finset.mem_filter.mp hf₁).2 (Finset.mem_filter.mp hf₂).2
    have hr := (norm_row_sum C B unit e f₁ f₂).trans (hbound f₁ f₂
      (Finset.mem_filter.mp hf₁).2 (Finset.mem_filter.mp hf₂).2)
    exact (mul_le_mul hw hr (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hsum : ‖∑ f₁ ∈ divisorBin (F := F) P.1, ∑ f₂ ∈ divisorBin (F := F) P.2,
      weight C B e f₁ f₂ * ∑ a ∈ C.reflectedRows B unit,
        (Real.sqrt (B / norm a) : ℂ) * rowDivisorBlock C e f₁ f₂ a‖ ≤
      (1 / (P.1 * P.2)) * (H * U) *
        ((2 * A) * Real.sqrt (P.1 * P.2) * Real.sqrt (binEnergy C P.1 * binEnergy C P.2)) := by
    calc
      _ ≤ ∑ f₁ ∈ divisorBin (F := F) P.1, ∑ f₂ ∈ divisorBin (F := F) P.2,
        ‖weight C B e f₁ f₂ * ∑ a ∈ C.reflectedRows B unit,
          (Real.sqrt (B / norm a) : ℂ) * rowDivisorBlock C e f₁ f₂ a‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
      _ ≤ _ := by
        calc
          _ ≤ ∑ f₁ ∈ divisorBin (F := F) P.1, ∑ f₂ ∈ divisorBin (F := F) P.2,
              (1 / (P.1 * P.2)) * (H * U) * Real.sqrt (divisorEnergy C f₁ * divisorEnergy C f₂) :=
            Finset.sum_le_sum (fun f₁ hf₁ => Finset.sum_le_sum (hterm f₁ hf₁))
          _ = (1 / (P.1 * P.2)) * (H * U) *
              (∑ f₁ ∈ divisorBin (F := F) P.1, ∑ f₂ ∈ divisorBin (F := F) P.2,
                Real.sqrt (divisorEnergy C f₁ * divisorEnergy C f₂)) := by simp_rw [Finset.mul_sum]
          _ ≤ _ := mul_le_mul_of_nonneg_left (bin_double_cauchy C A hA hcount P hp.1 hp.2.1) (by positivity)
  rw [bucket_eq C B unit e P (by linarith) (by linarith) he0, norm_mul]
  apply (mul_le_mul hcoef hsum (norm_nonneg _) (by positivity)).trans_eq
  unfold ErrorRectangles.largeScore
  change _ = 2 * A * H * ‖C.kappa * C.mass‖ * Real.sqrt (C.M / B) *
    (U / Real.sqrt (P.1 * P.2)) * Real.sqrt (binEnergy C P.1 * binEnergy C P.2)
  have hs := Real.sq_sqrt (mul_pos hp1 hp2).le
  have hs0 := (Real.sqrt_pos.mpr (mul_pos hp1 hp2)).ne'
  field_simp
  rw [hs]
  ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDual

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDual

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def envelope (C : Context Q) (B : ℝ) : ℝ :=
  ErrorRectangles.finiteSup (admissibleRectangles C B) (ErrorRectangles.largeScore C B)

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

private theorem finiteSup_nonneg (S : Finset (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) :
    0 ≤ ErrorRectangles.finiteSup S f :=
  Real.sSup_nonneg' ⟨0, Or.inl rfl, le_rfl⟩

private theorem finite_values_bddAbove (S : Finset (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) :
    BddAbove ({0} ∪ {x : ℝ | ∃ P ∈ S, x = f P}) := by
  have hh : {x : ℝ | ∃ P ∈ S, x = f P} = f '' (↑S : Set (ℝ × ℝ)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨P, hP, rfl⟩
      exact ⟨P, hP, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨P, hP, rfl⟩
  rw [hh]
  exact (Set.finite_singleton 0 |>.union (S.finite_toSet.image f)).bddAbove

private theorem scales_card_le (X : ℝ) :
    ((ErrorRectangles.scales X).card : ℝ) ≤ (Vendor.dyadicLength (2 * max 1 X) : ℝ) + 1 := by
  have h := (Finset.card_insert_le (1 : ℝ)
    ((Finset.range (Vendor.dyadicLength (2 * max 1 X))).image
      (fun i : ℕ => (2 : ℝ) ^ i))).trans
    (Nat.add_le_add_right (Finset.card_image_le.trans_eq (Finset.card_range _)) 1)
  have h' : (ErrorRectangles.scales X).card ≤ Vendor.dyadicLength (2 * max 1 X) + 1 := h
  exact_mod_cast h'

private theorem scales_card_small_power (η : ℝ) (hη : 0 < η) (X : ℝ) :
    ((ErrorRectangles.scales X).card : ℝ) ≤
      (2 + 1 / (η * Real.log 2)) * Real.rpow (2 * max 1 X) η := by
  exact (scales_card_le X).trans
    (Vendor.dyadicLength_small_power hη (by have := le_max_left (1 : ℝ) X; linarith))

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

private lemma bin_energy_le (η A : ℝ) (hη : 0 < η) (hA : 1 ≤ A)
    (hcount : ∀ u : Ideal (𝓞 F), (idealDivisorCount u : ℝ) ≤ A * norm u ^ η)
    (C : Context Q) (hN : 1 ≤ C.N) (hn : 1 ≤ norm C.d) (P : ℝ) :
    binEnergy C P ≤ (A * (2 * C.N) ^ η) ^ 2 * Sieve.energy F c C.N C.lam := by
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
  unfold binEnergy divisorEnergy
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ u ∈ C.columns, L ^ 2 * ‖C.lam (C.d * u)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hs := (primeSupportCost_le_divisorCount u (hu0 u hu)).trans (hcnt u hu)
      have hc := hcard u hu
      nlinarith [mul_le_mul hc hs (by positivity : 0 ≤ (2 : ℝ) ^
        (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card) hL,
        sq_nonneg ‖C.lam (C.d * u)‖]
    _ = L ^ 2 * ∑ u ∈ C.columns, ‖C.lam (C.d * u)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (column_energy_le C) (sq_nonneg _)

private lemma mobius_card_le (η A : ℝ) (hη : 0 < η)
    (hcount : ∀ u : Ideal (𝓞 F), (idealDivisorCount u : ℝ) ≤ A * norm u ^ η)
    (C : Context Q) :
    (C.mobiusDivisors.card : ℝ) ≤ A * (norm c * norm C.d) ^ η := by
  have hc0 : c * C.d ≠ ⊥ := mul_ne_zero C.D.original_ne_bot C.hd0
  have hr0 : (c * C.d).radical ≠ ⊥ := by
    intro h
    apply hc0
    exact bot_unique (by simpa [h] using (Ideal.le_radical : c * C.d ≤ (c * C.d).radical))
  have hc : C.mobiusDivisors.card ≤ (idealDivisors (c * C.d)).card := by
    apply Finset.card_le_card
    intro e he
    apply (mem_idealDivisors hc0).mpr
    exact dvd_trans ((mem_idealDivisors hr0).mp he) (Ideal.dvd_iff_le.mpr Ideal.le_radical)
  have h := (show (C.mobiusDivisors.card : ℝ) ≤ (idealDivisorCount (c * C.d) : ℝ) by exact_mod_cast hc).trans (hcount _)
  simpa [norm, map_mul] using h

private lemma score_le_envelope (C : Context Q) (B : ℝ) (P : ℝ × ℝ)
    (hP : P ∈ admissibleRectangles C B) :
    ErrorRectangles.largeScore C B P ≤ envelope C B := by
  exact le_csSup (finite_values_bddAbove _ _) (Or.inr ⟨P, hP, rfl⟩)

private lemma rectangle_card_le (C : Context Q) (B : ℝ) :
    ((admissibleRectangles C B).card : ℝ) ≤
      ((ErrorRectangles.scales (C.N / norm C.d)).card : ℝ) ^ 2 := by
  have hh : (admissibleRectangles C B).card ≤
      ((ErrorRectangles.scales (C.N / norm C.d)) ×ˢ
        (ErrorRectangles.scales (C.N / norm C.d))).card :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans
      (Finset.card_le_card (Finset.filter_subset _ _))
  rw [Finset.card_product] at hh
  have h : (admissibleRectangles C B).card ≤
      (ErrorRectangles.scales (C.N / norm C.d)).card *
        (ErrorRectangles.scales (C.N / norm C.d)).card := hh
  simpa [pow_two] using (Nat.cast_le.mpr h : (_ : ℝ) ≤ _)

private lemma scale_card_bound (η : ℝ) (hη : 0 < η) (C : Context Q)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hn : 1 ≤ norm C.d) :
    ((ErrorRectangles.scales (C.N / norm C.d)).card : ℝ) ≤
      ((2 + 1 / (η * Real.log 2)) * (2 : ℝ) ^ η) *
        (C.M * C.N * norm C.d) ^ η := by
  have hn0 : 0 < norm C.d := by linarith
  have hT : C.N ≤ C.M * C.N * norm C.d := by
    have hh : C.N ≤ C.M * C.N := le_mul_of_one_le_left (by linarith) hM
    exact hh.trans (le_mul_of_one_le_right (by positivity) hn)
  have hX : max 1 (C.N / norm C.d) ≤ C.M * C.N * norm C.d := by
    apply max_le
    · exact hN.trans hT
    · exact (div_le_self (by linarith) hn).trans hT
  have hh := scales_card_small_power η hη (C.N / norm C.d)
  have hL : 0 ≤ 2 + 1 / (η * Real.log 2) := by
    exact (Vendor.dyadicLength_small_power_constant_pos hη).le
  calc
    _ ≤ _ := hh
    _ ≤ (2 + 1 / (η * Real.log 2)) * (2 * (C.M * C.N * norm C.d)) ^ η := by
      apply mul_le_mul_of_nonneg_left _ hL
      exact Real.rpow_le_rpow (by positivity) (by linarith) hη.le
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring

theorem incidence_envelope_bound
    (D : Sieve.AllIndexNormalizedFamilyData Q) (W : ℝ → ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
      ∀ (C : Context Q), C.D = D → C.W = W →
      ∀ B : ℝ,
        1 ≤ C.M → 1 ≤ C.N → 1 ≤ B → B ≤ C.K → C.K ≤ C.M →
        1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
        (∑ e ∈ C.mobiusDivisors,
          ∑ P ∈ admissibleRectangles C B,
            ‖C.kappa * C.mass‖ * ErrorRectangles.largeScore C B P *
              Real.sqrt (binEnergy C P.1 * binEnergy C P.2)) ≤
          A * Real.rpow (C.M * C.N * norm C.d) ε * envelope C B *
            Sieve.energy F c C.N C.lam := by
  intro ε hε
  by_cases hex : ∃ C : Context Q, C.D = D ∧ C.W = W
  · obtain ⟨C₀, hD₀, hW₀⟩ := hex
    let η := ε / 8
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨A₀, hA₀, hcount₀⟩ := ideal_divisor_count_le_rpow F η hη
    have hcount : ∀ u : Ideal (𝓞 F), (idealDivisorCount u : ℝ) ≤ A₀ * norm u ^ η := hcount₀
    let I := (A₀ * (2 : ℝ) ^ η) ^ 2
    let H := (2 + 1 / (η * Real.log 2)) * (2 : ℝ) ^ η
    let J := A₀ * norm c ^ η
    let R := ‖C₀.kappa * C₀.mass‖
    let A := J * H ^ 2 * R * I + 1
    have hI : 0 ≤ I := sq_nonneg _
    have hH : 0 ≤ H := mul_nonneg
      (Vendor.dyadicLength_small_power_constant_pos hη).le (by positivity)
    have hJ : 0 ≤ J := mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hR : 0 ≤ R := norm_nonneg _
    refine ⟨A, by dsimp [A]; positivity, ?_⟩
    intro C hCD hCW B hM hN hB hBK hKM hn hnN
    let T := C.M * C.N * norm C.d
    let t := T ^ η
    let E := Sieve.energy F c C.N C.lam
    let V := envelope C B
    have hT : 1 ≤ T := by
      dsimp [T]
      have hh : 1 ≤ C.M * C.N := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hh (by linarith : 0 ≤ norm C.d)]
    have hT0 : 0 < T := by linarith
    have ht : 1 ≤ t := Real.one_le_rpow hT hη.le
    have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hV : 0 ≤ V := finiteSup_nonneg _ _
    have hNle : C.N ≤ T := by
      dsimp [T]
      exact (le_mul_of_one_le_left (by linarith) hM).trans
        (le_mul_of_one_le_right (by positivity) hn)
    have hnle : norm C.d ≤ T := by
      dsimp [T]
      exact le_mul_of_one_le_left (by linarith) (by nlinarith : 1 ≤ C.M * C.N)
    have hres : ‖C.kappa * C.mass‖ = R := by
      have hk : C.kappa = C₀.kappa := rfl
      have hm : C.mass = C₀.mass := by
        unfold Context.mass Context.source
        rw [hCW, hW₀]
      rw [hk, hm]
    have hbin : ∀ P : ℝ, binEnergy C P ≤ I * t ^ 2 * E := by
      intro P
      have hh := bin_energy_le η A₀ hη hA₀ hcount C hN hn P
      have hp : (2 * C.N) ^ η ≤ (2 : ℝ) ^ η * t := by
        rw [Real.mul_rpow (by norm_num) (by linarith)]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith) hNle hη.le) (by positivity)
      calc
        _ ≤ _ := hh
        _ ≤ (A₀ * ((2 : ℝ) ^ η * t)) ^ 2 * E := by
          apply mul_le_mul_of_nonneg_right _ hE
          exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hp (by linarith)) 2
        _ = _ := by dsimp [I, E]; ring
    have hbin0 : ∀ P : ℝ, 0 ≤ binEnergy C P := by
      intro P
      unfold binEnergy divisorEnergy
      apply Finset.sum_nonneg
      intro f hf
      apply Finset.sum_nonneg
      intro u hu
      split_ifs <;> positivity
    have hsqrt : ∀ P : ℝ × ℝ,
        Real.sqrt (binEnergy C P.1 * binEnergy C P.2) ≤ I * t ^ 2 * E := by
      intro P
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      rw [pow_two]
      exact mul_le_mul (hbin P.1) (hbin P.2) (hbin0 _)
        (mul_nonneg (mul_nonneg hI (sq_nonneg _)) hE)
    have hcardP : ((admissibleRectangles C B).card : ℝ) ≤ H ^ 2 * t ^ 2 := by
      have hh := scale_card_bound η hη C hM hN hn
      exact (rectangle_card_le C B).trans (by
        calc
          _ ≤ (H * t) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hh 2
          _ = _ := by ring)
    have hcarde : (C.mobiusDivisors.card : ℝ) ≤ J * t := by
      calc
        _ ≤ _ := mobius_card_le η A₀ hη hcount C
        _ = J * (norm C.d) ^ η := by
          rw [Real.mul_rpow (show 0 ≤ norm c by exact Nat.cast_nonneg _)
            (show 0 ≤ norm C.d by linarith)]
          dsimp [J]; ring
        _ ≤ J * t := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith) hnle hη.le) hJ
    have ht5 : t ^ 5 ≤ T ^ ε := by
      dsimp [t]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
      apply Real.rpow_le_rpow_of_exponent_le hT
      dsimp [η]
      norm_num
      linarith
    calc
      _ ≤ ∑ e ∈ C.mobiusDivisors, ∑ P ∈ admissibleRectangles C B,
          R * V * (I * t ^ 2 * E) := by
        apply Finset.sum_le_sum
        intro e he
        apply Finset.sum_le_sum
        intro P hP
        rw [hres]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (score_le_envelope C B P hP) hR)
          (hsqrt P) (Real.sqrt_nonneg _) (mul_nonneg hR hV)
      _ = (C.mobiusDivisors.card : ℝ) * ((admissibleRectangles C B).card : ℝ) *
          (R * V * (I * t ^ 2 * E)) := by simp; ring
      _ ≤ (J * t) * (H ^ 2 * t ^ 2) * (R * V * (I * t ^ 2 * E)) := by
        gcongr
      _ = (J * H ^ 2 * R * I) * t ^ 5 * V * E := by ring
      _ ≤ A * T ^ ε * V * E := by
        apply mul_le_mul_of_nonneg_right _ hE
        apply mul_le_mul_of_nonneg_right _ hV
        exact mul_le_mul (by dsimp [A]; linarith) ht5 (by positivity) (by dsimp [A]; positivity)
      _ = _ := rfl
  · refine ⟨1, by norm_num, ?_⟩
    intro C hCD hCW
    exact False.elim (hex ⟨C, hCD, hCW⟩)

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDual

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

namespace ErrorRectangles

def dualRectangles (C : Context Q) (B : ℝ) : Finset (ℝ × ℝ) :=
  (rectangles C).filter (fun P =>
    lowerConstant c * C.N / (norm C.d * Real.sqrt (B * C.M)) *
      Real.rpow (C.M * C.N) C.δ ≤ P.1 * P.2)

def dualEnvelope (C : Context Q) (B : ℝ) : ℝ :=
  finiteSup (dualRectangles C B) (largeScore C B)

end ErrorRectangles

theorem bilinear_error_large_dual
    (D : Sieve.AllIndexNormalizedFamilyData Q) (W : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
      ∀ C : Context Q, C.D = D → C.W = W → C.δ = δ →
      ∀ (B : ℝ) (unit : Bool), (unit = true → B = 1) →
        1 ≤ C.M → 1 ≤ C.N → 1 ≤ B → B ≤ C.K → C.K ≤ C.M →
        1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
        ‖E1 C B unit‖ ≤ A * Real.rpow (C.M * C.N * norm C.d) ε *
          Real.sqrt (C.M / B) * ErrorRectangles.dualEnvelope C B *
          Sieve.energy F c C.N C.lam := by
  obtain ⟨H, hH, hrow⟩ := LargeDual.supported_divisible_pair_bound D
  obtain ⟨J, hJ, hrect⟩ := LargeDual.rectangle_bucket_bound (F := F) (c := c) (Q := Q)
  intro ε hε
  obtain ⟨A, hA, hagg⟩ := LargeDual.incidence_envelope_bound D W ε hε
  refine ⟨J * H * A, by positivity, ?_⟩
  intro C hD hW hδC B unit hunit hM hN hB hBK hKM hn hnN
  have hδ' : 0 < C.δ := by rw [hδC]; exact hδ
  have hrow' := hrow C hD B unit hunit hM hN hB hBK hKM hn hnN
  have hrect' := hrect H hH C B unit hunit hM hN hB hBK hKM hn hnN
  have hagg' := hagg C hD hW B hM hN hB hBK hKM hn hnN
  have hpoint : ∀ e ∈ C.mobiusDivisors,
      ∀ P ∈ LargeDual.admissibleRectangles C B,
        ‖LargeDual.bucket C B unit e P‖ ≤
          (J * H * Real.sqrt (C.M / B)) *
            (‖C.kappa * C.mass‖ * ErrorRectangles.largeScore C B P *
              Real.sqrt (LargeDual.binEnergy C P.1 * LargeDual.binEnergy C P.2)) := by
    intro e he P hP
    convert hrect' e he P hP (hrow' e he P hP) using 1 <;> ring
  have hsum : ‖E1 C B unit‖ ≤
      (J * H * Real.sqrt (C.M / B)) *
        (∑ e ∈ C.mobiusDivisors,
          ∑ P ∈ LargeDual.admissibleRectangles C B,
            ‖C.kappa * C.mass‖ * ErrorRectangles.largeScore C B P *
              Real.sqrt (LargeDual.binEnergy C P.1 * LargeDual.binEnergy C P.2)) := by
    rw [LargeDual.finite_rectangle_expansion C B unit hM hN hδ' hB hBK hKM hn hnN]
    calc
      ‖∑ e ∈ C.mobiusDivisors,
          ∑ P ∈ LargeDual.admissibleRectangles C B,
            LargeDual.bucket C B unit e P‖
        ≤ ∑ e ∈ C.mobiusDivisors,
            ∑ P ∈ LargeDual.admissibleRectangles C B,
              ‖LargeDual.bucket C B unit e P‖ := by
          calc
            _ ≤ ∑ e ∈ C.mobiusDivisors,
                ‖∑ P ∈ LargeDual.admissibleRectangles C B,
                  LargeDual.bucket C B unit e P‖ := norm_sum_le _ _
            _ ≤ _ := Finset.sum_le_sum (fun e _ => norm_sum_le _ _)
      _ ≤ _ := by
          simp only [Finset.mul_sum]
          exact Finset.sum_le_sum (fun e he =>
            Finset.sum_le_sum (fun P hP => hpoint e he P hP))
  have hnonneg : 0 ≤ J * H * Real.sqrt (C.M / B) := by positivity
  have h := le_trans hsum (mul_le_mul_of_nonneg_left hagg' hnonneg)
  change ‖E1 C B unit‖ ≤
    J * H * A * Real.rpow (C.M * C.N * norm C.d) ε *
      Real.sqrt (C.M / B) * LargeDual.envelope C B *
        Sieve.energy F c C.N C.lam
  convert h using 1 <;> ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

end

end
