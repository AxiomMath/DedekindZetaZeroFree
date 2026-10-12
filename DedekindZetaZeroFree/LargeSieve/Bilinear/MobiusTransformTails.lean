module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.PrimitiveQuadraticMoebiusFormula
public import DedekindZetaZeroFree.Arithmetic.Ideals.SquarefreeKernel

@[expose] public section

section

noncomputable section
open scoped NumberField Classical ContDiff BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.TransformTail

variable {F : Type} [Field F] [NumberField F]

def scale (M : ℝ) (e u v : Ideal (𝓞 F)) : ℝ :=
  (Ideal.absNorm e : ℝ) * (Ideal.absNorm u : ℝ) * (Ideal.absNorm v : ℝ) / M

def term (q : Ideal (𝓞 F)) (K : ℝ) (h : ℝ → ℂ) (X : ℝ)
    {f : Ideal (𝓞 F)} (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (a : Ideal (𝓞 F)) : ℂ :=
  if a ≠ ⊥ ∧ K < sc q a then S4allTerm ⊤ h X η a else 0

def mobiusTail (q d : Ideal (𝓞 F)) (W : ℝ → ℝ) (M K : ℝ)
    (u v : Ideal (𝓞 F))
    (η : DedekindZetaZeroFree.RayClassCharacter F (u * v)) : ℂ :=
  let dotW := DedekindZetaZeroFree.LargeSieve.fieldTransform (DedekindZetaZeroFree.LargeSieve.principalDiscriminant F)
    (DedekindZetaZeroFree.LargeSieve.principalComplexPlaces F) (fun x => (W x : ℂ))
  ∑ e ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors (q * d).radical,
    (UniqueFactorizationMonoid.moebius e : ℂ) * η e *
      ((M : ℂ) / ((Ideal.absNorm e : ℂ) *
        (Real.sqrt (Ideal.absNorm (u * v) : ℝ) : ℂ))) *
      ∑' a : Ideal (𝓞 F), term q K dotW (scale M e u v) η a

def blockTail (q d : Ideal (𝓞 F)) (W : ℝ → ℝ) (M K : ℝ)
    (L : Finset (Ideal (𝓞 F))) (lam : Ideal (𝓞 F) → ℂ)
    (θ : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ)
    (η : ∀ u v : Ideal (𝓞 F), DedekindZetaZeroFree.RayClassCharacter F (u * v)) : ℂ :=
  ∑ u ∈ L, ∑ v ∈ L, θ u v * lam u * star (lam v) *
    mobiusTail q d W M K u v (η u v)

def majorant (q d : Ideal (𝓞 F)) (W : ℝ → ℝ) (M K : ℝ)
    (L : Finset (Ideal (𝓞 F))) (lam : Ideal (𝓞 F) → ℂ)
    (θ : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ)
    (η : ∀ u v : Ideal (𝓞 F), DedekindZetaZeroFree.RayClassCharacter F (u * v)) : ℝ :=
  let dotW := DedekindZetaZeroFree.LargeSieve.fieldTransform (DedekindZetaZeroFree.LargeSieve.principalDiscriminant F)
    (DedekindZetaZeroFree.LargeSieve.principalComplexPlaces F) (fun x => (W x : ℂ))
  ∑ u ∈ L, ∑ v ∈ L,
    if θ u v ≠ 0 then
      ‖θ u v * lam u * star (lam v)‖ *
        (∑ e ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors (q * d).radical,
          ‖(UniqueFactorizationMonoid.moebius e : ℂ) * (η u v) e *
            ((M : ℂ) / ((Ideal.absNorm e : ℂ) *
              (Real.sqrt (Ideal.absNorm (u * v) : ℝ) : ℂ)))‖ *
          ∑' a : Ideal (𝓞 F), ‖term q K dotW (scale M e u v) (η u v) a‖)
    else 0

theorem chooseOrder {F : Type} [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (W : ℝ → ℝ) (hW : DedekindZetaZeroFree.LargeSieve.Sieve.SieveWeight W)
    (ε A0 : ℝ) (hε : 0 < ε) (hA0 : 0 < A0) :
    let dotW := DedekindZetaZeroFree.LargeSieve.fieldTransform (DedekindZetaZeroFree.LargeSieve.principalDiscriminant F)
      (DedekindZetaZeroFree.LargeSieve.principalComplexPlaces F) (fun x => (W x : ℂ))
    ∃ (A : ℕ) (δ CW : ℝ), 2 < A ∧ 0 < δ ∧ δ < ε ∧
      δ ≤ (A : ℝ) ∧ A0 + 3 ≤ ε * ((A : ℝ) - 1) ∧ 0 < CW ∧
      (∀ x : ℝ, 0 < x → x ≤ 1 → ‖dotW x‖ ≤ CW * Real.rpow x (-δ)) ∧
      (∀ x : ℝ, 1 ≤ x → ‖dotW x‖ ≤ CW * Real.rpow x (-(A : ℝ))) := by
  dsimp only
  have horder_exists : ∃ A : ℕ, 3 ≤ A ∧ A0 + 3 ≤ ε * ((A : ℝ) - 1) := by
    obtain ⟨A, hA⟩ := exists_nat_gt (max 3 ((A0 + 3) / ε + 2))
    have hA3 : (3 : ℝ) < (A : ℝ) := lt_of_le_of_lt (le_max_left _ _) hA
    have hAlarge : (A0 + 3) / ε + 2 < (A : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hA
    refine ⟨A, by exact_mod_cast le_of_lt hA3, ?_⟩
    have hstep : (A0 + 3) / ε + 1 < (A : ℝ) - 1 := by linarith
    have hmul := mul_lt_mul_of_pos_left hstep hε
    have hcalc : ε * ((A0 + 3) / ε + 1) = (A0 + 3) + ε := by
      rw [mul_add, mul_div_cancel₀ _ hε.ne', mul_one]
    rw [hcalc] at hmul
    linarith
  obtain ⟨A, hA3, horder⟩ := horder_exists
  have hA2 : 2 < A := by omega
  set δ : ℝ := min (ε / 2) 1 with hδdef
  have hδpos : 0 < δ := lt_min (by positivity) one_pos
  have hδlt : δ < ε := by
    have h1 : δ ≤ ε / 2 := min_le_left _ _
    linarith
  have hA3real : (3 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA3
  have hδA : δ ≤ (A : ℝ) := by
    have h1 : δ ≤ 1 := min_le_right _ _
    linarith
  have hD : 0 < DedekindZetaZeroFree.LargeSieve.principalDiscriminant F := DedekindZetaZeroFree.LargeSieve.principalDiscriminant_pos F
  have hr : 1 ≤ DedekindZetaZeroFree.LargeSieve.principalComplexPlaces F :=
    DedekindZetaZeroFree.LargeSieve.principalComplexPlaces_pos F hF
  have hh : ContDiff ℝ ∞ (fun x : ℝ => (W x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hW.smooth
  have hhc : HasCompactSupport (fun x : ℝ => (W x : ℂ)) :=
    HasCompactSupport.intro' (K := Set.Icc (1 / 2 : ℝ) (5 / 2))
      isCompact_Icc isClosed_Icc (fun x hx => by simp [hW.zero_outside x hx])
  obtain ⟨C, hCpos, hsmall, hlarge⟩ :=
    DedekindZetaZeroFree.LargeSieve.fieldTransform_euler_two_ended_bound (DedekindZetaZeroFree.LargeSieve.principalDiscriminant F)
      (DedekindZetaZeroFree.LargeSieve.principalComplexPlaces F) (fun x : ℝ => (W x : ℂ))
      hD hr hh hhc 0 A δ hδpos
  refine ⟨A, δ, C, hA2, hδpos, hδlt, hδA, horder, hCpos, ?_, ?_⟩
  · intro x hx0 hx1
    simpa using hsmall x hx0 hx1
  · intro x hx1
    simpa using hlarge x hx1

end DedekindZetaZeroFree.LargeSieve.Bilinear.TransformTail

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.TransformTail

private lemma sc_le_norm {F : Type} [Field F] [NumberField F]
    (q a : Ideal (𝓞 F)) (ha : a ≠ ⊥) : sc q a ≤ (Ideal.absNorm a : ℝ) := by
  have hk := DedekindZetaZeroFree.LargeSieve.Sieve.UniversalB2.canonical_kernel_extraction a ha
  have hd : primeToSquarefreeKernel q a ∣ DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel a := by
    unfold primeToSquarefreeKernel
    apply dvd_trans (Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _))
    exact (Multiset.toFinset_prod_dvd_prod _).trans
      (dvd_of_eq (Ideal.prod_normalizedFactors_eq_self hk.1))
  have hn := Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp (hd.trans hk.2.2.1))
  have hpos : 0 < Ideal.absNorm a := Nat.pos_of_ne_zero (by
    intro h0
    exact ha (Ideal.absNorm_eq_zero_iff.mp h0))
  unfold sc
  exact_mod_cast Nat.le_of_dvd hpos hn

theorem idealTail {F : Type} [Field F] [NumberField F]
    (A : ℕ) (hA : 2 < A) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (q : Ideal (𝓞 F)), q ≠ ⊥ →
      ∀ (h : ℝ → ℂ) (δ CW : ℝ), 0 < δ → δ ≤ (A : ℝ) → 0 ≤ CW →
        (∀ x : ℝ, 0 < x → x ≤ 1 → ‖h x‖ ≤ CW * Real.rpow x (-δ)) →
        (∀ x : ℝ, 1 ≤ x → ‖h x‖ ≤ CW * Real.rpow x (-(A : ℝ))) →
      ∀ (X K : ℝ), 0 < X → 0 < K →
      ∀ (f : Ideal (𝓞 F)) (η : DedekindZetaZeroFree.RayClassCharacter F f),
        Summable (fun a : Ideal (𝓞 F) => ‖term q K h X η a‖) ∧
        (∑' a : Ideal (𝓞 F), ‖term q K h X η a‖) ≤
          B * CW * Real.rpow X (A : ℝ) * Real.rpow K (1 - (A : ℝ)) := by
  have hp : 1 < (A : ℝ) := by exact_mod_cast (by omega : 1 < A)
  have hs := DedekindZetaZeroFree.LargeSieve.summable_ideal_inverse_power F (A : ℝ) hp
  let w : Ideal (𝓞 F) → ℝ := fun a =>
    if a = ⊥ then 0 else Real.rpow (Ideal.absNorm a : ℝ) (-(A : ℝ))
  have hw : ∀ a, 0 ≤ w a := by
    intro a
    dsimp [w]
    split_ifs <;> positivity
  let S : ℝ := ∑' a, w a
  have hS : 0 ≤ S := tsum_nonneg hw
  obtain ⟨B0, hB0, htail⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_inverse_power_tail_bound F (A : ℝ) hp
  refine ⟨B0 + S, add_nonneg hB0 hS, ?_⟩
  intro q hq h δ CW hδ hδA hCW hsmall hlarge X K hX hK f η
  let t : Ideal (𝓞 F) → ℝ := fun a =>
    if a ≠ ⊥ ∧ K < (Ideal.absNorm a : ℝ)
    then Real.rpow (Ideal.absNorm a : ℝ) (-(A : ℝ)) else 0
  have ht0 : ∀ a, 0 ≤ t a := by
    intro a
    dsimp [t]
    split_ifs <;> positivity
  have htw : ∀ a, t a ≤ w a := by
    intro a
    dsimp [t, w]
    by_cases ha : a = ⊥
    · simp [ha]
    · split_ifs <;> first | exact le_rfl | positivity
  have hts : Summable t := Summable.of_nonneg_of_le ht0 htw hs
  have htbound : (∑' a, t a) ≤ (B0 + S) * Real.rpow K (1 - (A : ℝ)) := by
    by_cases hK1 : 1 ≤ K
    · exact (htail K hK1).trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right hS) (Real.rpow_nonneg hK.le _))
    · have hpow : 1 ≤ Real.rpow K (1 - (A : ℝ)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hK (le_of_not_ge hK1) (by linarith)
      calc
        (∑' a, t a) ≤ S := Summable.tsum_le_tsum htw hts hs
        _ ≤ B0 + S := le_add_of_nonneg_left hB0
        _ ≤ (B0 + S) * Real.rpow K (1 - (A : ℝ)) :=
          le_mul_of_one_le_right (add_nonneg hB0 hS) hpow
  have hglobal : ∀ x : ℝ, 0 < x → ‖h x‖ ≤ CW * Real.rpow x (-(A : ℝ)) := by
    intro x hx
    by_cases hx1 : x ≤ 1
    · exact (hsmall x hx hx1).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le_or_ge (Or.inr ⟨hx, hx1, by linarith⟩)) hCW)
    · exact hlarge x (le_of_not_ge hx1)
  have hpoint : ∀ a : Ideal (𝓞 F), ‖term q K h X η a‖ ≤
      (CW * Real.rpow X (A : ℝ)) * t a := by
    intro a
    by_cases ha : a ≠ ⊥ ∧ K < sc q a
    · have han : 0 < (Ideal.absNorm a : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (by
          intro h0
          exact ha.1 (Ideal.absNorm_eq_zero_iff.mp h0))
      have hat : a ≠ ⊥ ∧ K < (Ideal.absNorm a : ℝ) :=
        ⟨ha.1, lt_of_lt_of_le ha.2 (sc_le_norm q a ha.1)⟩
      simp only [term, if_pos ha, S4allTerm, sup_top_eq, and_true, if_pos ha.1,
        norm_mul, t, if_pos hat]
      calc
        ‖h ((Ideal.absNorm a : ℝ) / X)‖ * ‖η a‖ ≤
            ‖h ((Ideal.absNorm a : ℝ) / X)‖ :=
          mul_le_of_le_one_right (norm_nonneg _) (DedekindZetaZeroFree.LargeSieve.RayOperations.norm_le_one η a)
        _ ≤ CW * Real.rpow ((Ideal.absNorm a : ℝ) / X) (-(A : ℝ)) :=
          hglobal _ (div_pos han hX)
        _ = (CW * Real.rpow X (A : ℝ)) *
            Real.rpow (Ideal.absNorm a : ℝ) (-(A : ℝ)) := by
          change CW * ((Ideal.absNorm a : ℝ) / X) ^ (-(A : ℝ)) =
            (CW * X ^ (A : ℝ)) * (Ideal.absNorm a : ℝ) ^ (-(A : ℝ))
          rw [Real.div_rpow han.le hX.le (-(A : ℝ)), Real.rpow_neg hX.le (A : ℝ)]
          simp only [div_inv_eq_mul]
          ring
    · simp only [term, if_neg ha, norm_zero]
      exact mul_nonneg (mul_nonneg hCW (Real.rpow_nonneg hX.le _)) (ht0 a)
  have hmaj := hts.mul_left (CW * Real.rpow X (A : ℝ))
  have hsum : Summable (fun a : Ideal (𝓞 F) => ‖term q K h X η a‖) :=
    Summable.of_nonneg_of_le (fun a => norm_nonneg _) hpoint hmaj
  refine ⟨hsum, ?_⟩
  calc
    (∑' a, ‖term q K h X η a‖) ≤
        ∑' a, (CW * Real.rpow X (A : ℝ)) * t a :=
      Summable.tsum_le_tsum hpoint hsum hmaj
    _ = (CW * Real.rpow X (A : ℝ)) * ∑' a, t a := tsum_mul_left
    _ ≤ (CW * Real.rpow X (A : ℝ)) *
        ((B0 + S) * Real.rpow K (1 - (A : ℝ))) :=
      mul_le_mul_of_nonneg_left htbound (mul_nonneg hCW (Real.rpow_nonneg hX.le _))
    _ = (B0 + S) * CW * Real.rpow X (A : ℝ) * Real.rpow K (1 - (A : ℝ)) := by ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.TransformTail

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.TransformTail

theorem absorb (Q ε A0 B CW : ℝ) (hQ : 0 < Q) (hε : 0 < ε)
    (hB : 0 ≤ B) (hCW : 0 ≤ CW) (A : ℕ) (hA : 2 < A)
    (horder : A0 + 3 ≤ ε * ((A : ℝ) - 1))
    (M N K D : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) (hD : 1 ≤ D)
    (hK : (N ^ 2 / M) * Real.rpow (M * N) ε ≤ K) :
    B * CW * (M * N) ^ 3 *
      Real.rpow ((4 * Q * N ^ 2 / (M * D)) / K) ((A : ℝ) - 1) ≤
      (B * CW * Real.rpow (4 * Q) ((A : ℝ) - 1)) *
        Real.rpow (M * N) (-A0) := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hP : 1 ≤ M * N := one_le_mul_of_one_le_of_one_le hM hN
  have hP0 : 0 < M * N := mul_pos hM0 hN0
  have hR0 : 0 < Real.rpow (M * N) ε := Real.rpow_pos_of_pos hP0 _
  have hT0 : 0 < N ^ 2 / M := div_pos (pow_pos hN0 _) hM0
  have hK0 : 0 < K := lt_of_lt_of_le (mul_pos hT0 hR0) hK
  have hDK : N ^ 2 / M * Real.rpow (M * N) ε ≤ D * K :=
    hK.trans (by nlinarith)
  have hratio : (4 * Q * N ^ 2 / (M * D)) / K ≤
      (4 * Q) / Real.rpow (M * N) ε := by
    have heq : (4 * Q * N ^ 2 / (M * D)) / K =
        (4 * Q * (N ^ 2 / M)) / (D * K) := by
      field_simp
      <;> ring
    rw [heq, div_le_div_iff₀ (mul_pos hD0 hK0) hR0]
    have hh := mul_le_mul_of_nonneg_left hDK (show 0 ≤ 4 * Q by positivity)
    nlinarith [hh]
  have hs : 0 ≤ (A : ℝ) - 1 := by
    have : (2 : ℝ) < A := by exact_mod_cast hA
    linarith
  have hpow := Real.rpow_le_rpow (show 0 ≤ (4 * Q * N ^ 2 / (M * D)) / K by positivity)
    hratio hs
  have heq : (M * N) ^ 3 * Real.rpow ((4 * Q) / Real.rpow (M * N) ε) ((A : ℝ) - 1) =
      Real.rpow (4 * Q) ((A : ℝ) - 1) *
        Real.rpow (M * N) (3 - ε * ((A : ℝ) - 1)) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.div_rpow (show 0 ≤ 4 * Q by positivity) (show 0 ≤ (M * N) ^ ε by positivity) ((A : ℝ) - 1),
      ← Real.rpow_mul (le_of_lt hP0), Real.rpow_sub hP0, Real.rpow_ofNat]
    ring
  calc
    B * CW * (M * N) ^ 3 * Real.rpow ((4 * Q * N ^ 2 / (M * D)) / K) ((A : ℝ) - 1)
        ≤ B * CW * (M * N) ^ 3 * Real.rpow ((4 * Q) / Real.rpow (M * N) ε) ((A : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (B * CW * Real.rpow (4 * Q) ((A : ℝ) - 1)) *
        Real.rpow (M * N) (3 - ε * ((A : ℝ) - 1)) := by
      rw [mul_assoc (B * CW), heq]
      ring
    _ ≤ (B * CW * Real.rpow (4 * Q) ((A : ℝ) - 1)) * Real.rpow (M * N) (-A0) := by
      simp only [Real.rpow_eq_pow]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hP (by linarith)

end DedekindZetaZeroFree.LargeSieve.Bilinear.TransformTail

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.TransformTail

private lemma power_identity (X K a : ℝ) (hX : 0 < X) (hK : 0 < K) :
    Real.rpow X a * Real.rpow K (1-a) = X * Real.rpow (X/K) (a-1) := by
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow hX.le hK.le]
  rw [show a = 1 + (a-1) by ring, Real.rpow_add hX, Real.rpow_one]
  rw [show 1 - (1+(a-1)) = -(a-1) by ring,
    show 1 + (a-1) - 1 = a-1 by ring, Real.rpow_neg hK.le]
  ring
private lemma prefactor_identity (E U V M : ℝ) (hE : 0 < E) (hU : 0 < U)
    (hV : 0 < V) (hM : 0 < M) :
    (M / (E * Real.sqrt (U*V))) * (E*U*V/M) = Real.sqrt (U*V) := by
  have hs : 0 < Real.sqrt (U*V) := Real.sqrt_pos.2 (mul_pos hU hV)
  have hsq := Real.sq_sqrt (mul_pos hU hV).le
  field_simp
  nlinarith
private lemma absnorm_one {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
private lemma divisor_bound {F : Type} [Field F] [NumberField F]
    (q d : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hd : d ≠ ⊥)
    (e : Ideal (𝓞 F)) (he : e ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors (q*d).radical) :
    (Ideal.absNorm e : ℝ) ≤ (Ideal.absNorm q : ℝ)*(Ideal.absNorm d : ℝ) := by
  have h1 := DedekindZetaZeroFree.LargeSieve.absNorm_le_of_mem_idealDivisors he
  have hqd : q*d ≠ ⊥ := by simpa only [← Ideal.zero_eq_bot] using mul_ne_zero (by simpa using hq) (by simpa using hd)
  have h2 : Ideal.absNorm (q*d).radical ≤ Ideal.absNorm (q*d) :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hqd))
      (Ideal.absNorm_dvd_absNorm_of_le Ideal.le_radical)
  have h := h1.trans h2
  rw [map_mul] at h
  exact_mod_cast h
private lemma coefficient_bound {F : Type} [Field F] [NumberField F]
    (M : ℝ) (hM : 0 < M) (e u v : Ideal (𝓞 F))
    (he : e ≠ ⊥) (hu : u ≠ ⊥) (hv : v ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F (u*v)) :
    ‖(UniqueFactorizationMonoid.moebius e : ℂ) * η e *
      ((M : ℂ) / ((Ideal.absNorm e : ℂ) *
        (Real.sqrt (Ideal.absNorm (u*v) : ℝ) : ℂ)))‖ ≤
    M / ((Ideal.absNorm e : ℝ) * Real.sqrt
      ((Ideal.absNorm u : ℝ)*(Ideal.absNorm v : ℝ))) := by
  have hmo : ‖(UniqueFactorizationMonoid.moebius e : ℂ)‖ ≤ 1 := by
    rw [UniqueFactorizationMonoid.moebius]
    split <;> simp
  have huv : u*v ≠ ⊥ := by
    simpa only [← Ideal.zero_eq_bot] using mul_ne_zero (by simpa using hu) (by simpa using hv)
  have hη := DedekindZetaZeroFree.LargeSieve.RayOperations.norm_le_one η e
  have hb : ‖(UniqueFactorizationMonoid.moebius e : ℂ) * η e‖ ≤ 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (η e), norm_nonneg (UniqueFactorizationMonoid.moebius e : ℂ)]
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq
  simp [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_real,
    abs_of_nonneg hM.le, abs_of_nonneg (Real.sqrt_nonneg _), map_mul]
private lemma pair_scale_bounds {F : Type} [Field F] [NumberField F]
    (q d e u v : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hd : d ≠ ⊥)
    (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (he : e ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors (q*d).radical)
    (hu : u ∈ DedekindZetaZeroFree.LargeSieve.Sieve.paperShell F ⊤ (N / (Ideal.absNorm d : ℝ)))
    (hv : v ∈ DedekindZetaZeroFree.LargeSieve.Sieve.paperShell F ⊤ (N / (Ideal.absNorm d : ℝ))) :
    u ≠ ⊥ ∧ v ≠ ⊥ ∧ 0 < scale M e u v ∧
    scale M e u v ≤ 4 * (Ideal.absNorm q : ℝ) * N^2 / (M * (Ideal.absNorm d : ℝ)) ∧
    Real.sqrt ((Ideal.absNorm u : ℝ)*(Ideal.absNorm v : ℝ)) ≤ 2*N / (Ideal.absNorm d : ℝ) := by
  have hu' := (DedekindZetaZeroFree.LargeSieve.Sieve.mem_paperShell F ⊤ _ u).mp hu
  have hv' := (DedekindZetaZeroFree.LargeSieve.Sieve.mem_paperShell F ⊤ _ v).mp hv
  have hd1 := absnorm_one d hd
  have hd0 : 0 < (Ideal.absNorm d : ℝ) := by linarith
  have hN0 : 0 < N := by linarith
  have hu0 : 0 < (Ideal.absNorm u : ℝ) := (div_pos hN0 hd0).trans hu'.2.2.1
  have hv0 : 0 < (Ideal.absNorm v : ℝ) := (div_pos hN0 hd0).trans hv'.2.2.1
  have hue : u ≠ ⊥ := by intro h; simp [h] at hu0
  have hve : v ≠ ⊥ := by intro h; simp [h] at hv0
  have he0 : 0 < (Ideal.absNorm e : ℝ) := lt_of_lt_of_le zero_lt_one
    (absnorm_one e (DedekindZetaZeroFree.LargeSieve.ne_bot_of_mem_idealDivisors he))
  have hM0 : 0 < M := by linarith
  have heb := divisor_bound q d hq hd e he
  have hprod : (Ideal.absNorm u : ℝ)*(Ideal.absNorm v : ℝ) ≤ (2*N/(Ideal.absNorm d : ℝ))^2 := by
    have h1 : (Ideal.absNorm u : ℝ) ≤ 2*N/(Ideal.absNorm d : ℝ) := by simpa [mul_div_assoc] using hu'.2.2.2
    have h2 : (Ideal.absNorm v : ℝ) ≤ 2*N/(Ideal.absNorm d : ℝ) := by simpa [mul_div_assoc] using hv'.2.2.2
    nlinarith [mul_le_mul h1 h2 hv0.le (by positivity : 0 ≤ 2*N/(Ideal.absNorm d : ℝ))]
  refine ⟨hue, hve, div_pos (mul_pos (mul_pos he0 hu0) hv0) hM0, ?_, ?_⟩
  · unfold scale
    rw [mul_assoc]
    apply (div_le_div_of_nonneg_right (mul_le_mul heb hprod (mul_pos hu0 hv0).le
      (by positivity)) hM0.le).trans_eq
    field_simp
    <;> ring
  · apply (Real.sqrt_le_sqrt hprod).trans_eq
    rw [Real.sqrt_sq (by positivity)]
private lemma one_divisor_bound {F : Type} [Field F] [NumberField F]
    (q d e u v : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hd : d ≠ ⊥)
    (M N K B CW : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) (hK : 0 < K)
    (hB : 0 ≤ B) (hCW : 0 ≤ CW) (a : ℝ) (ha : 1 ≤ a)
    (he : e ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors (q*d).radical)
    (hu : u ∈ DedekindZetaZeroFree.LargeSieve.Sieve.paperShell F ⊤ (N / (Ideal.absNorm d : ℝ)))
    (hv : v ∈ DedekindZetaZeroFree.LargeSieve.Sieve.paperShell F ⊤ (N / (Ideal.absNorm d : ℝ)))
    (η : DedekindZetaZeroFree.RayClassCharacter F (u*v)) (T : ℝ)
    (hT : T ≤ B * CW * Real.rpow (scale M e u v) a * Real.rpow K (1-a)) :
    ‖(UniqueFactorizationMonoid.moebius e : ℂ) * η e *
      ((M : ℂ) / ((Ideal.absNorm e : ℂ) *
        (Real.sqrt (Ideal.absNorm (u*v) : ℝ) : ℂ)))‖ * T ≤
      B * CW * (2*N) * Real.rpow
        ((4 * (Ideal.absNorm q : ℝ) * N^2 / (M * (Ideal.absNorm d : ℝ))) / K) (a-1) := by
  obtain ⟨hu0, hv0, hX, hXb, hsb⟩ := pair_scale_bounds q d e u v hq hd M N hM hN he hu hv
  have hM0 : 0 < M := by linarith
  have hU := absnorm_one u hu0
  have hV := absnorm_one v hv0
  have hE := absnorm_one e (DedekindZetaZeroFree.LargeSieve.ne_bot_of_mem_idealDivisors he)
  have hc := coefficient_bound M hM0 e u v (DedekindZetaZeroFree.LargeSieve.ne_bot_of_mem_idealDivisors he) hu0 hv0 η
  have hp : Real.rpow (scale M e u v / K) (a-1) ≤ Real.rpow
      ((4 * (Ideal.absNorm q : ℝ) * N^2 / (M * (Ideal.absNorm d : ℝ))) / K) (a-1) := by
    simp only [Real.rpow_eq_pow]
    exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hXb hK.le) (by linarith)
  have hs : Real.sqrt ((Ideal.absNorm u : ℝ)*(Ideal.absNorm v : ℝ)) ≤ 2*N := by
    apply hsb.trans
    exact div_le_self (by positivity) (absnorm_one d hd)
  calc
    _ ≤ ‖(UniqueFactorizationMonoid.moebius e : ℂ) * η e *
      ((M : ℂ) / ((Ideal.absNorm e : ℂ) *
        (Real.sqrt (Ideal.absNorm (u*v) : ℝ) : ℂ)))‖ *
      (B * CW * Real.rpow (scale M e u v) a * Real.rpow K (1-a)) :=
      mul_le_mul_of_nonneg_left hT (norm_nonneg _)
    _ ≤ (M / ((Ideal.absNorm e : ℝ) * Real.sqrt
      ((Ideal.absNorm u : ℝ)*(Ideal.absNorm v : ℝ)))) *
      (B * CW * Real.rpow (scale M e u v) a * Real.rpow K (1-a)) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg
        (mul_nonneg (mul_nonneg hB hCW) (Real.rpow_nonneg hX.le _))
        (Real.rpow_nonneg hK.le _))
    _ = B * CW * Real.sqrt ((Ideal.absNorm u : ℝ)*(Ideal.absNorm v : ℝ)) *
      Real.rpow (scale M e u v / K) (a-1) := by
      rw [mul_assoc (B*CW), power_identity _ _ _ hX hK]
      have hid := prefactor_identity (Ideal.absNorm e) (Ideal.absNorm u) (Ideal.absNorm v)
        M (by linarith) (by linarith) (by linarith) hM0
      unfold scale
      calc
        _ = B * CW * ((M / ((Ideal.absNorm e : ℝ) * Real.sqrt
              ((Ideal.absNorm u : ℝ)*(Ideal.absNorm v : ℝ)))) *
            ((Ideal.absNorm e : ℝ)*(Ideal.absNorm u : ℝ)*
            (Ideal.absNorm v : ℝ)/M)) *
            Real.rpow (((Ideal.absNorm e : ℝ)*(Ideal.absNorm u : ℝ)*
            (Ideal.absNorm v : ℝ)/M)/K) (a-1) := by ring
        _ = _ := by rw [hid]
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hs (mul_nonneg hB hCW)) hp
      (Real.rpow_nonneg (div_pos hX hK).le _) (by positivity)
private lemma block_bound {F : Type} [Field F] [NumberField F]
    (q d : Ideal (𝓞 F)) (W : ℝ → ℝ) (M K : ℝ)
    (L : Finset (Ideal (𝓞 F))) (lam : Ideal (𝓞 F) → ℂ)
    (θ : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ)
    (η : ∀ u v : Ideal (𝓞 F), DedekindZetaZeroFree.RayClassCharacter F (u*v))
    (hs : ∀ u ∈ L, ∀ v ∈ L, θ u v ≠ 0 →
      ∀ e ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors (q*d).radical,
      Summable (fun a => ‖term q K
        (DedekindZetaZeroFree.LargeSieve.fieldTransform (DedekindZetaZeroFree.LargeSieve.principalDiscriminant F)
          (DedekindZetaZeroFree.LargeSieve.principalComplexPlaces F) (fun x => (W x : ℂ)))
        (scale M e u v) (η u v) a‖)) :
    ‖blockTail q d W M K L lam θ η‖ ≤ majorant q d W M K L lam θ η := by
  unfold blockTail majorant mobiusTail
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro u hu
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro v hv
  by_cases ht : θ u v = 0
  · simp [ht]
  · rw [if_pos ht, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro e he
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact norm_tsum_le_tsum_norm (hs u hu v hv ht e he)

theorem aggregate {F : Type} [Field F] [NumberField F]
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (A : ℕ) (hA : 2 < A) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (W : ℝ → ℝ) (δ CW : ℝ), 0 < δ → δ ≤ (A : ℝ) → 0 ≤ CW →
      let dotW := DedekindZetaZeroFree.LargeSieve.fieldTransform (DedekindZetaZeroFree.LargeSieve.principalDiscriminant F)
        (DedekindZetaZeroFree.LargeSieve.principalComplexPlaces F) (fun x => (W x : ℂ))
      (∀ x : ℝ, 0 < x → x ≤ 1 → ‖dotW x‖ ≤ CW * Real.rpow x (-δ)) →
      (∀ x : ℝ, 1 ≤ x → ‖dotW x‖ ≤ CW * Real.rpow x (-(A : ℝ))) →
      ∀ M N K : ℝ, 1 ≤ M → 1 ≤ N → 0 < K →
      ∀ d : Ideal (𝓞 F), d ≠ ⊥ →
        1 ≤ (Ideal.absNorm d : ℝ) → (Ideal.absNorm d : ℝ) ≤ 2 * N →
      ∀ L : Finset (Ideal (𝓞 F)),
        L ⊆ DedekindZetaZeroFree.LargeSieve.Sieve.paperShell F ⊤ (N / (Ideal.absNorm d : ℝ)) →
      ∀ (lam : Ideal (𝓞 F) → ℂ)
        (θ : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ),
        (∀ u ∈ L, ∀ v ∈ L, ‖θ u v‖ ≤ 1) →
      ∀ (η : ∀ u v : Ideal (𝓞 F),
        DedekindZetaZeroFree.RayClassCharacter F (u * v)),
        (∀ u ∈ L, ∀ v ∈ L, θ u v ≠ 0 →
          ∀ e ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors (q * d).radical,
            Summable (fun a : Ideal (𝓞 F) =>
              ‖term q K dotW (scale M e u v) (η u v) a‖)) ∧
        majorant q d W M K L lam θ η ≤
          (B * CW * (M * N) ^ 3 *
            Real.rpow ((4 * (Ideal.absNorm q : ℝ) * N ^ 2 /
              (M * (Ideal.absNorm d : ℝ))) / K) ((A : ℝ) - 1)) *
            (∑ u ∈ L, ‖lam u‖ ^ 2) ∧
        ‖blockTail q d W M K L lam θ η‖ ≤ majorant q d W M K L lam θ η := by
  obtain ⟨B0, hB0, htail⟩ := idealTail (F := F) A hA
  obtain ⟨C, hC1, -, hcount⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound_finset F
  have hC : 0 ≤ C := by linarith
  have hq1 := absnorm_one q hq
  refine ⟨8 * B0 * C^2 * (Ideal.absNorm q : ℝ), by positivity, ?_⟩
  intro W δ CW hδ hδA hCW
  dsimp only
  intro hwsmall hwlarge M N K hM hN hK d hd hd1 hdN L hL lam θ hθ η
  let h := DedekindZetaZeroFree.LargeSieve.fieldTransform (DedekindZetaZeroFree.LargeSieve.principalDiscriminant F)
    (DedekindZetaZeroFree.LargeSieve.principalComplexPlaces F) (fun x => (W x : ℂ))
  let R := Real.rpow ((4 * (Ideal.absNorm q : ℝ) * N^2 /
    (M * (Ideal.absNorm d : ℝ))) / K) ((A : ℝ)-1)
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hd0 : 0 < (Ideal.absNorm d : ℝ) := by linarith
  have hR : 0 ≤ R := Real.rpow_nonneg (by positivity) _
  have ht : ∀ u ∈ L, ∀ v ∈ L, ∀ e ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors (q*d).radical,
      Summable (fun a => ‖term q K h (scale M e u v) (η u v) a‖) ∧
      (∑' a, ‖term q K h (scale M e u v) (η u v) a‖) ≤
        B0 * CW * Real.rpow (scale M e u v) (A : ℝ) * Real.rpow K (1-(A : ℝ)) := by
    intro u hu v hv e he
    have hx := (pair_scale_bounds q d e u v hq hd M N hM hN he (hL hu) (hL hv)).2.2.1
    exact htail q hq h δ CW hδ hδA hCW hwsmall hwlarge _ K hx hK _ (η u v)
  have hs : ∀ u ∈ L, ∀ v ∈ L, θ u v ≠ 0 →
      ∀ e ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors (q*d).radical,
      Summable (fun a => ‖term q K h (scale M e u v) (η u v) a‖) := by
    intro u hu v hv _ e he
    exact (ht u hu v hv e he).1
  refine ⟨hs, ?_, block_bound q d W M K L lam θ η hs⟩
  have ha : 1 ≤ (A : ℝ) := by exact_mod_cast (by omega : 1 ≤ A)
  have hdcard : ((DedekindZetaZeroFree.LargeSieve.idealDivisors (q*d).radical).card : ℝ) ≤
      2 * C * (Ideal.absNorm q : ℝ) * N := by
    have hb := hcount ((Ideal.absNorm q : ℝ)*(Ideal.absNorm d : ℝ))
      (by nlinarith) (DedekindZetaZeroFree.LargeSieve.idealDivisors (q*d).radical)
      (fun e he => divisor_bound q d hq hd e he)
    nlinarith [mul_le_mul_of_nonneg_left hdN (mul_nonneg hC (by positivity : 0 ≤ (Ideal.absNorm q : ℝ)))]
  have hLcard : (L.card : ℝ) ≤ 2 * C * N := by
    apply (hcount (2*N) (by linarith) L ?_).trans_eq (by ring)
    intro u hu
    have hub := ((DedekindZetaZeroFree.LargeSieve.Sieve.mem_paperShell F ⊤ _ u).mp (hL hu)).2.2.2
    apply hub.trans
    have : N / (Ideal.absNorm d : ℝ) ≤ N := div_le_self hN0.le hd1
    linarith
  have hdtotal : ∀ u ∈ L, ∀ v ∈ L,
      (∑ e ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors (q*d).radical,
        ‖(UniqueFactorizationMonoid.moebius e : ℂ) * (η u v) e *
          ((M : ℂ) / ((Ideal.absNorm e : ℂ) *
            (Real.sqrt (Ideal.absNorm (u*v) : ℝ) : ℂ)))‖ *
          ∑' a, ‖term q K h (scale M e u v) (η u v) a‖) ≤
      (2*C*(Ideal.absNorm q : ℝ)*N) * (B0*CW*(2*N)*R) := by
    intro u hu v hv
    calc
      _ ≤ ∑ _e ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors (q*d).radical, B0*CW*(2*N)*R := by
        apply Finset.sum_le_sum
        intro e he
        exact one_divisor_bound q d e u v hq hd M N K B0 CW hM hN hK hB0 hCW
          A ha he (hL hu) (hL hv) (η u v) _ (ht u hu v hv e he).2
      _ = ((DedekindZetaZeroFree.LargeSieve.idealDivisors (q*d).radical).card : ℝ) * (B0*CW*(2*N)*R) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hdcard (by positivity)
  have hmask : ∀ u ∈ L, ∀ v ∈ L,
      ‖θ u v * lam u * star (lam v)‖ ≤ ‖lam u‖ * ‖lam v‖ := by
    intro u hu v hv
    simp only [norm_mul, norm_star]
    nlinarith [hθ u hu v hv, norm_nonneg (θ u v), norm_nonneg (lam u), norm_nonneg (lam v),
      mul_nonneg (norm_nonneg (lam u)) (norm_nonneg (lam v))]
  have hcs : (∑ u ∈ L, ‖lam u‖)^2 ≤ (L.card : ℝ) * ∑ u ∈ L, ‖lam u‖^2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq L (fun _ => (1 : ℝ)) (fun u => ‖lam u‖)
  have henergy : 0 ≤ ∑ u ∈ L, ‖lam u‖^2 := by positivity
  have hcoeff : 0 ≤ (2*C*(Ideal.absNorm q : ℝ)*N) * (B0*CW*(2*N)*R) := by positivity
  calc
    majorant q d W M K L lam θ η ≤
        ∑ u ∈ L, ∑ v ∈ L, (‖lam u‖*‖lam v‖) *
          ((2*C*(Ideal.absNorm q : ℝ)*N) * (B0*CW*(2*N)*R)) := by
      unfold majorant
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      split_ifs with htθ
      · exact mul_le_mul (hmask u hu v hv) (hdtotal u hu v hv)
          (by positivity) (by positivity)
      · positivity
    _ = ((2*C*(Ideal.absNorm q : ℝ)*N) * (B0*CW*(2*N)*R)) *
        (∑ u ∈ L, ‖lam u‖)^2 := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      ring
    _ ≤ ((2*C*(Ideal.absNorm q : ℝ)*N) * (B0*CW*(2*N)*R)) *
        ((2*C*N) * ∑ u ∈ L, ‖lam u‖^2) := by
      apply mul_le_mul_of_nonneg_left _ hcoeff
      exact hcs.trans (mul_le_mul_of_nonneg_right hLcard henergy)
    _ ≤ _ := by
      have hnm : N^3 ≤ (M*N)^3 := by
        apply pow_le_pow_left₀ hN0.le
        nlinarith
      have hb : 0 ≤ (8*B0*C^2*(Ideal.absNorm q : ℝ))*CW*R *
          (∑ u ∈ L, ‖lam u‖^2) := by positivity
      dsimp only [R]
      convert mul_le_mul_of_nonneg_left hnm hb using 1 <;> ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.TransformTail

end

end

section

noncomputable section
open scoped NumberField Classical ContDiff BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear

variable {F : Type} [Field F] [NumberField F]

def primitiveDualScale (M : ℝ) (e u v : Ideal (𝓞 F)) : ℝ :=
  (Ideal.absNorm e : ℝ) * (Ideal.absNorm u : ℝ) *
    (Ideal.absNorm v : ℝ) / M

def reflectedKernelTailTerm (q : Ideal (𝓞 F)) (K : ℝ)
    (h : ℝ → ℂ) (X : ℝ) {f : Ideal (𝓞 F)}
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (a : Ideal (𝓞 F)) : ℂ :=
  if a ≠ ⊥ ∧ K < sc q a then S4allTerm ⊤ h X η a else 0

def primitiveMobiusTransformTail (q d : Ideal (𝓞 F)) (W : ℝ → ℝ)
    (M K : ℝ) (u v : Ideal (𝓞 F))
    (η : DedekindZetaZeroFree.RayClassCharacter F (u * v)) : ℂ :=
  let dotW := DedekindZetaZeroFree.LargeSieve.fieldTransform (DedekindZetaZeroFree.LargeSieve.principalDiscriminant F)
    (DedekindZetaZeroFree.LargeSieve.principalComplexPlaces F) (fun x => (W x : ℂ))
  ∑ e ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors (q * d).radical,
    (UniqueFactorizationMonoid.moebius e : ℂ) * η e *
      ((M : ℂ) / ((Ideal.absNorm e : ℂ) *
        (Real.sqrt (Ideal.absNorm (u * v) : ℝ) : ℂ))) *
      ∑' a : Ideal (𝓞 F),
        reflectedKernelTailTerm q K dotW (primitiveDualScale M e u v) η a

end DedekindZetaZeroFree.LargeSieve.Bilinear

end

end
