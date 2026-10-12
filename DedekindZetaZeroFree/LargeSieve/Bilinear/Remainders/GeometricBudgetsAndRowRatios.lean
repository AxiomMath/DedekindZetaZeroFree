module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.Remainders.DivisorNormAndCardinalityBounds

@[expose] public section

section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly.LocalTailRatios
open ExplicitTerms

private lemma ratios_from_squares (T Y Z U H : ℝ)
    (hT : 0 < T) (hY : 0 < Y) (hZ : 0 < Z) (hU : 0 < U) (hH : 1 ≤ H)
    (hzlo : (T*U)^2 ≤ (H*Z)^2)
    (hyhi : (Y*U)^2 ≤ (H*T)^2)
    (hzhi : Z^2 ≤ (H*T*U)^2) :
    U/H ≤ Z/T ∧ U/H ≤ T/Y ∧ U/H ≤ (8*U^2)*T/Z := by
  have hH0 : 0 < H := by linarith
  have hzlo' : T*U ≤ H*Z := (sq_le_sq₀ (by positivity) (by positivity)).mp hzlo
  have hyhi' : Y*U ≤ H*T := (sq_le_sq₀ (by positivity) (by positivity)).mp hyhi
  have hzhi' : Z ≤ H*T*U := (sq_le_sq₀ (by positivity) (by positivity)).mp hzhi
  constructor
  · apply (div_le_div_iff₀ hH0 hT).mpr
    nlinarith
  constructor
  · apply (div_le_div_iff₀ hH0 hY).mpr
    nlinarith
  · apply (div_le_div_iff₀ hH0 hZ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hzhi' hU.le]

private lemma original_squares (M R B U H : ℝ) (hM : 0 < M) (hR : 0 < R)
    (hB : 0 < B) (hU : 0 < U) (hH : 2 ≤ H)
    (hRB : B ≤ R) (hBR : R ≤ 2*B) :
    let T := Real.sqrt (M/R)
    let Y := Real.sqrt (M/(2*B))/U
    let Z := Real.sqrt (M/B)*U
    (T*U)^2 ≤ (H*Z)^2 ∧ (Y*U)^2 ≤ (H*T)^2 ∧ Z^2 ≤ (H*T*U)^2 := by
  dsimp
  have hT := Real.sq_sqrt (div_pos hM hR).le
  have hY := Real.sq_sqrt (div_pos hM (by positivity : 0 < 2*B)).le
  have hZ := Real.sq_sqrt (div_pos hM hB).le
  have hH2 : 2 ≤ H^2 := by nlinarith
  have hMB : 0 < M/B := div_pos hM hB
  have hMR : 0 < M/R := div_pos hM hR
  have hcmp : M/R ≤ M/B := div_le_div_of_nonneg_left hM.le hB hRB
  have hcmp2 : M/B ≤ 2*(M/R) := by
    rw [div_le_iff₀ hB]
    rw [mul_assoc, mul_comm (M/R) B, ← mul_assoc, ← mul_div_assoc,
      le_div_iff₀ hR]
    nlinarith [mul_le_mul_of_nonneg_left hBR hM.le]
  have hcmp3 : M/(2*B) ≤ M/R := div_le_div_of_nonneg_left hM.le hR hBR
  simp only [mul_pow, div_pow, hT, hY, hZ, div_mul_cancel₀ _ (pow_ne_zero 2 hU.ne')]
  constructor
  · calc
      _ ≤ (M/B)*U^2 := mul_le_mul_of_nonneg_right hcmp (sq_nonneg U)
      _ ≤ H^2*((M/B)*U^2) := le_mul_of_one_le_left (by positivity) (by linarith)
  constructor
  · exact hcmp3.trans (le_mul_of_one_le_left hMR.le (by linarith))
  · have hb : M/B ≤ H^2*(M/R) := hcmp2.trans
      (mul_le_mul_of_nonneg_right hH2 hMR.le)
    calc
      _ ≤ (H^2*(M/R))*U^2 := mul_le_mul_of_nonneg_right hb (sq_nonneg U)
      _ = _ := by ring

private lemma reflected_square_ratios (M N d E V R B U q : ℝ)
    (hM : 0 < M) (hN : 0 < N) (hd : 0 < d) (hE : 0 < E) (hV : 0 < V)
    (hR : 0 < R) (hB : 0 < B) (hU : 0 < U) (hq : 1 ≤ q)
    (hVRlo : N^2 ≤ d^2*V) (hVRhi : d^2*V ≤ 4*N^2)
    (hRlo : B ≤ R) (hRhi : R ≤ 2*q*B) :
    let T := Real.sqrt (E*V/M/R)
    let Y := N*Real.sqrt E/(d*Real.sqrt (2*B*M))/U
    let Z := N*Real.sqrt E/(d*Real.sqrt (B*M))*U
    (T*U)^2 ≤ (4*q*Z)^2 ∧ (Y*U)^2 ≤ (4*q*T)^2 ∧ Z^2 ≤ (4*q*T*U)^2 := by
  dsimp
  have hT := Real.sq_sqrt (show 0 ≤ E*V/M/R by positivity)
  have hY := Real.sq_sqrt (show 0 ≤ 2*B*M by positivity)
  have hZ := Real.sq_sqrt (show 0 ≤ B*M by positivity)
  have hEs := Real.sq_sqrt hE.le
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hq2 : 1 ≤ q^2 := by nlinarith
  have hBq : R ≤ 16*q^2*B := hRhi.trans (by nlinarith [mul_nonneg (by linarith : 0 ≤ q-1) hB.le])
  have hcomp : V ≤ 16*q^2*N^2/d^2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hd)]
    nlinarith [mul_le_mul_of_nonneg_right hq2 (sq_nonneg N)]
  have hcomp2 : N^2/d^2 ≤ 16*q^2*V := by
    rw [div_le_iff₀ (sq_pos_of_pos hd)]
    nlinarith [mul_le_mul_of_nonneg_right hq2 (mul_nonneg (sq_nonneg d) hV.le)]
  simp only [mul_pow, div_pow, hT, hY, hZ, hEs, div_mul_cancel₀ _ (pow_ne_zero 2 hU.ne')]
  constructor
  · have hb : E*V/M/R ≤ 16*q^2*(N^2*E/(d^2*(B*M))) := by
      have hi := mul_le_mul_of_nonneg_left hcomp (div_pos hE hM).le
      have hj := div_le_div_of_nonneg_left (by positivity : 0 ≤ (E/M)*(16*q^2*N^2/d^2)) hB hRlo
      calc
        _ ≤ ((E/M)*(16*q^2*N^2/d^2))/R := by
          convert div_le_div_of_nonneg_right hi hR.le using 1 <;> ring
        _ ≤ ((E/M)*(16*q^2*N^2/d^2))/B := hj
        _ = _ := by ring
    convert mul_le_mul_of_nonneg_right hb (sq_nonneg U) using 1 <;> ring
  constructor
  · have hb : N^2*E/(d^2*(2*B*M)) ≤ 16*q^2*(E*V/M/R) := by
      have hh : R ≤ 32*q^2*B := hBq.trans (by nlinarith [mul_nonneg (sq_nonneg q) hB.le])
      have hi := mul_le_mul_of_nonneg_right hVRlo (show 0 ≤ E*R by positivity)
      have hj := mul_le_mul_of_nonneg_left hh (show 0 ≤ d^2*V*E by positivity)
      have he : 16*q^2*(E*V/M/R) = (16*q^2*E*V)/(M*R) := by ring
      rw [he]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hbase : N^2*E*R ≤ d^2*V*E*(32*q^2*B) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hbase hM.le]
    convert hb using 1 <;> ring
  · have hb : N^2*E/(d^2*(B*M)) ≤ 16*q^2*(E*V/M/R) := by
      have hi := mul_le_mul_of_nonneg_right hVRlo (show 0 ≤ E*R by positivity)
      have hj := mul_le_mul_of_nonneg_left hBq (show 0 ≤ d^2*V*E by positivity)
      have he : 16*q^2*(E*V/M/R) = (16*q^2*E*V)/(M*R) := by ring
      rw [he]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hbase : N^2*E*R ≤ d^2*V*E*(16*q^2*B) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hbase hM.le]
    convert mul_le_mul_of_nonneg_right hb (sq_nonneg U) using 1 <;> ring

theorem uniform_row_ratios
    {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (D : Sieve.AllIndexNormalizedFamilyData Q) :
    ∃ H : ℝ, 0 < H ∧ ∀ C : Context Q, C.D = D →
      0 < C.M → 0 < C.N →
      ∀ (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p), p ∈ C.pairs →
      ∀ (B : ℝ) (unit : Bool), 0 < B → (unit = true → B = 1) →
      (∀ r ∈ C.originalRows B unit,
        let T := Real.sqrt (C.M / norm r)
        let v := Real.rpow (C.M * C.N) C.δ / H
        v ≤ C.Z2 B / T ∧ v ≤ T / C.Y2 B ∧ v ≤ C.L2 * T / C.Z2 B) ∧
      (∀ e ∈ C.mobiusDivisors, ∀ r ∈ C.reflectedRows B unit,
        let T := Real.sqrt (C.dualScale e p / norm r)
        let v := Real.rpow (C.M * C.N) C.δ / H
        v ≤ C.Z1 B e / T ∧ v ≤ T / C.Y1 B e ∧ v ≤ C.L1 * T / C.Z1 B e) := by
  let q := LocalTailGeometry.supportedNormBound c
  have hq : 1 ≤ q := LocalTailGeometry.supportedNormBound_one_le c
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  refine ⟨4*q, by positivity, ?_⟩
  intro C hCD hM hN p hp hpair B unit hB hunit
  have hd : 0 < norm C.d := zero_lt_one.trans_le (LocalTailGeometry.norm_one_le C.hd0)
  have hV : 0 < norm (p.1*p.2) := zero_lt_one.trans_le
    (LocalTailGeometry.norm_one_le (mul_ne_zero hp.hu0 hp.hv0))
  let U := Real.rpow (C.M*C.N) C.δ
  have hU : 0 < U := Real.rpow_pos_of_pos (mul_pos hM hN) _
  have hinv : Real.rpow (C.M*C.N) (-C.δ) = 1/U := by
    dsimp [U]
    have he := Real.rpow_neg (mul_pos hM hN).le C.δ
    simpa using he
  have hL : C.L1 = 8*U^2 := by
    unfold Context.L1
    dsimp [U]
    have he := Real.rpow_mul (mul_pos hM hN).le C.δ 2
    have hh : Real.rpow (Real.rpow (C.M*C.N) C.δ) 2 =
      (Real.rpow (C.M*C.N) C.δ)^2 := Real.rpow_two _
    simp only [Real.rpow_eq_pow] at he hh ⊢
    rw [← hh, ← he]
    congr 2
    ring
  have horig {r : Ideal (𝓞 F)} (hr : r ∈ C.originalRows B unit) :
      B ≤ norm r ∧ norm r ≤ 2*B := by
    cases unit
    · have hs := (Sieve.mem_paperShell F (c*C.d) B r).mp (Finset.mem_filter.mp hr).1
      exact ⟨hs.2.2.1.le, hs.2.2.2⟩
    · have he := LocalTailGeometry.unit_row_eq_top hr
      have hb : B=1 := hunit rfl
      simp [he, hb, ExplicitTerms.norm]
  have href {r : Ideal (𝓞 F)} (hr : r ∈ C.reflectedRows B unit) :
      B ≤ norm r ∧ norm r ≤ 2*q*B := by
    obtain ⟨⟨t,r⟩, htr, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨htr, hmask⟩ := Finset.mem_filter.mp htr
    obtain ⟨ht, hr⟩ := Finset.mem_product.mp htr
    have ht1 : 1 ≤ norm t := LocalTailGeometry.norm_one_le
      ((mem_squarefreeBadPool C.D.original_ne_bot).mp ht).1
    have htb : norm t ≤ q := LocalTailGeometry.supported_norm_le ht
    have hrb : B ≤ norm r ∧ norm r ≤ 2*B := by
      cases unit
      · have hs := (Sieve.mem_paperShell F c B r).mp (Finset.mem_filter.mp hr).1
        exact ⟨hs.2.2.1.le, hs.2.2.2⟩
      · have he : r = ⊤ := LocalTailGeometry.unit_row_eq_top hr
        have hb : B=1 := hunit rfl
        simp [he, hb, ExplicitTerms.norm]
    rw [LocalTailGeometry.norm_mul]
    constructor
    · exact hrb.1.trans (le_mul_of_one_le_left (hB.trans_le hrb.1).le ht1)
    · have hb := mul_le_mul htb hrb.2 (LocalTailGeometry.norm_nonneg r) hq0.le
      nlinarith
  have hpairnorm : C.N^2 ≤ (norm C.d)^2*norm (p.1*p.2) ∧
      (norm C.d)^2*norm (p.1*p.2) ≤ 4*C.N^2 := by
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpair).1
    have hus := (Sieve.mem_paperShell F c C.N _).mp (Finset.mem_filter.mp hu).2.1
    have hvs := (Sieve.mem_paperShell F c C.N _).mp (Finset.mem_filter.mp hv).2.1
    have hlo := mul_le_mul hus.2.2.1.le hvs.2.2.1.le hN.le
      (LocalTailGeometry.norm_nonneg _)
    have hhi := mul_le_mul hus.2.2.2 hvs.2.2.2
      (LocalTailGeometry.norm_nonneg _) (by positivity : 0 ≤ 2*C.N)
    simp only [LocalTailGeometry.norm_mul] at ⊢
    simp only [ExplicitTerms.norm, map_mul, Nat.cast_mul] at hlo hhi ⊢
    constructor <;> nlinarith [hlo,hhi]
  constructor
  · intro r hr
    have hn : 0 < norm r := hB.trans_le (horig hr).1
    have hs := original_squares C.M (norm r) B U (4*q) hM hn hB hU
      (by linarith) (horig hr).1 (horig hr).2
    have hy : 0 < Real.sqrt (C.M/(2*B))/U := by positivity
    have hz : 0 < Real.sqrt (C.M/B)*U := by positivity
    have hh := ratios_from_squares _ _ _ U (4*q) (by positivity) hy hz hU
      (by linarith) hs.1 hs.2.1 hs.2.2
    dsimp only
    unfold Context.Y2 Context.Z2 Context.L2
    rw [hL, hinv]
    dsimp [U] at hh
    simpa only [U, Real.rpow_eq_pow, div_eq_mul_inv, one_mul, mul_assoc] using hh
  · intro e he r hr
    have hE : 0 < norm e := zero_lt_one.trans_le
      (LocalTailGeometry.mobius_divisor_norm C he).1
    have hn : 0 < norm r := hB.trans_le (href hr).1
    have hs := reflected_square_ratios C.M C.N (norm C.d) (norm e)
      (norm (p.1*p.2)) (norm r) B U q hM hN hd hE hV hn hB hU hq
      hpairnorm.1 hpairnorm.2 (href hr).1 (href hr).2
    have hh := ratios_from_squares _ _ _ U (4*q) (by positivity) (by positivity)
      (by positivity) hU (by linarith) hs.1 hs.2.1 hs.2.2
    dsimp only
    unfold Context.dualScale Context.Y1 Context.Z1
    rw [hL, hinv]
    dsimp [U] at hh
    simpa only [U, Real.rpow_eq_pow, div_eq_mul_inv, one_mul, mul_assoc] using hh

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly.LocalTailRatios

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly.LocalTailAux
open ExplicitTerms

def tailBudget (p T Y Z L : ℝ) : ℝ :=
  Real.rpow (Z / T) (-p) + Real.rpow (T / Y) (1-p) + Real.rpow (L * T / Z) (1-p)

lemma tailBudget_of_ratio_lower_bounds (a T Y Z L s H : ℝ)
    (ha : 1 < a) (hs : 1 ≤ s) (hH : 0 < H)
    (hT : 0 < T) (hY : 0 < Y) (hZ : 0 < Z) (hL : 0 < L)
    (hZT : s / H ≤ Z / T) (hTY : s / H ≤ T / Y)
    (hLTZ : s / H ≤ L * T / Z) :
    tailBudget a T Y Z L ≤
      (Real.rpow H a + 2 * Real.rpow H (a-1)) * Real.rpow s (1-a) := by
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hr : 0 < s / H := div_pos hs0 hH
  have hpow₁ := Real.rpow_le_rpow_of_nonpos hr hZT (show -a ≤ 0 by linarith)
  have hpow₂ := Real.rpow_le_rpow_of_nonpos hr hTY (show 1-a ≤ 0 by linarith)
  have hpow₃ := Real.rpow_le_rpow_of_nonpos hr hLTZ (show 1-a ≤ 0 by linarith)
  have hneg (b : ℝ) : Real.rpow H (-b) = (Real.rpow H b)⁻¹ := Real.rpow_neg hH.le b
  have he₁ : Real.rpow (s / H) (-a) = Real.rpow H a * Real.rpow s (-a) := by
    have hdiv : Real.rpow (s / H) (-a) = Real.rpow s (-a) / Real.rpow H (-a) :=
      Real.div_rpow hs0.le hH.le (-a)
    rw [hdiv, hneg a, div_inv_eq_mul, mul_comm]
  have he₂ : Real.rpow (s / H) (1-a) = Real.rpow H (a-1) * Real.rpow s (1-a) := by
    have hdiv : Real.rpow (s / H) (1-a) = Real.rpow s (1-a) / Real.rpow H (1-a) :=
      Real.div_rpow hs0.le hH.le (1-a)
    rw [show 1-a = -(a-1) by ring, hneg (a-1), div_inv_eq_mul, mul_comm] at hdiv
    simpa only [show -(a-1) = 1-a by ring] using hdiv
  have hexp := Real.rpow_le_rpow_of_exponent_le hs (show -a ≤ 1-a by linarith)
  have hfirst := hpow₁.trans (he₁.le.trans (mul_le_mul_of_nonneg_left hexp
    (Real.rpow_nonneg hH.le a)))
  unfold tailBudget
  have hsum := add_le_add (add_le_add hfirst (hpow₂.trans_eq he₂)) (hpow₃.trans_eq he₂)
  refine hsum.trans_eq ?_
  simp only [Real.rpow_eq_pow]
  ring

def blockBudget {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (C : Context Q) (a : ℝ) (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p)
    (B : ℝ) (unit : Bool := false) : ℝ :=
  (∑ e ∈ C.mobiusDivisors, ‖C.prefactor e p hp‖ *
    ∑ r ∈ C.reflectedRows B unit,
      ((idealDivisors (p.1 * p.2)).card : ℝ) *
        tailBudget a (Real.sqrt (C.dualScale e p / norm r))
          (C.Y1 B e) (C.Z1 B e) C.L1) +
  (∑ r ∈ C.originalRows B unit,
    ((idealDivisors ((c * C.d) * (p.1 * p.2))).card : ℝ) *
      tailBudget a (Real.sqrt (C.M / norm r)) (C.Y2 B) (C.Z2 B) C.L2)

def pairBudget {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (C : Context Q) (a : ℝ) (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p) : ℝ :=
  blockBudget C a p hp 1 true + ∑ B ∈ dyadicScales C, blockBudget C a p hp B

private lemma blockBudget_bound
    {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (C : Context Q) (a A U B : ℝ) (unit : Bool)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hA : 1 ≤ A) (hU : 0 ≤ U)
    (hecard : (C.mobiusDivisors.card : ℝ) ≤ A * C.N)
    (hjcard : ((idealDivisors (p.1 * p.2)).card : ℝ) ≤ A * C.N ^ 2)
    (hkcard : ((idealDivisors ((c * C.d) * (p.1 * p.2))).card : ℝ) ≤ A * C.N ^ 3)
    (hrcard : (C.reflectedRows B unit).card ≤ A * C.M)
    (hocard : (C.originalRows B unit).card ≤ A * C.M)
    (htr : ∀ e ∈ C.mobiusDivisors, ∀ r ∈ C.reflectedRows B unit,
      tailBudget a (Real.sqrt (C.dualScale e p / norm r))
        (C.Y1 B e) (C.Z1 B e) C.L1 ≤ U)
    (hto : ∀ r ∈ C.originalRows B unit,
      tailBudget a (Real.sqrt (C.M / norm r)) (C.Y2 B) (C.Z2 B) C.L2 ≤ U) :
    blockBudget C a p hp B unit ≤ (A ^ 3 + A ^ 2) * (C.M * C.N) ^ 5 * U := by
  have hM0 : 0 ≤ C.M := by linarith
  have hN0 : 0 ≤ C.N := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hX : 1 ≤ C.M * C.N := by nlinarith
  have hMX : C.M ≤ C.M * C.N := by nlinarith
  have hNX : C.N ≤ C.M * C.N := by nlinarith
  have hinner : ∀ e ∈ C.mobiusDivisors,
      (∑ r ∈ C.reflectedRows B unit, ((idealDivisors (p.1 * p.2)).card : ℝ) *
        tailBudget a (Real.sqrt (C.dualScale e p / norm r))
          (C.Y1 B e) (C.Z1 B e) C.L1) ≤ A * C.M * (A * C.N ^ 2 * U) := by
    intro e he
    calc
      _ ≤ ∑ r ∈ C.reflectedRows B unit, A * C.N ^ 2 * U := by
        apply Finset.sum_le_sum
        intro r hr
        exact (mul_le_mul_of_nonneg_left (htr e he r hr) (Nat.cast_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hjcard hU)
      _ = (C.reflectedRows B unit).card * (A * C.N ^ 2 * U) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hrcard (by positivity)
  have href : (∑ e ∈ C.mobiusDivisors, ‖C.prefactor e p hp‖ *
      ∑ r ∈ C.reflectedRows B unit, ((idealDivisors (p.1 * p.2)).card : ℝ) *
        tailBudget a (Real.sqrt (C.dualScale e p / norm r))
          (C.Y1 B e) (C.Z1 B e) C.L1) ≤
      (A * C.N) * (C.M * (A * C.M * (A * C.N ^ 2 * U))) := by
    calc
      _ ≤ ∑ e ∈ C.mobiusDivisors, C.M * (A * C.M * (A * C.N ^ 2 * U)) := by
        apply Finset.sum_le_sum
        intro e he
        exact (mul_le_mul_of_nonneg_left (hinner e he) (_root_.norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_right (LocalTailGeometry.prefactor_norm_le C hM p hp he)
            (by positivity))
      _ = C.mobiusDivisors.card * (C.M * (A * C.M * (A * C.N ^ 2 * U))) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hecard (by positivity)
  have hori : (∑ r ∈ C.originalRows B unit,
      ((idealDivisors ((c * C.d) * (p.1 * p.2))).card : ℝ) *
        tailBudget a (Real.sqrt (C.M / norm r)) (C.Y2 B) (C.Z2 B) C.L2) ≤
      (A * C.M) * (A * C.N ^ 3 * U) := by
    calc
      _ ≤ ∑ r ∈ C.originalRows B unit, A * C.N ^ 3 * U := by
        apply Finset.sum_le_sum
        intro r hr
        exact (mul_le_mul_of_nonneg_left (hto r hr) (Nat.cast_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hkcard hU)
      _ = (C.originalRows B unit).card * (A * C.N ^ 3 * U) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hocard (by positivity)
  have hpow : C.M ^ 2 * C.N ^ 3 ≤ (C.M * C.N) ^ 5 := by
    calc
      _ ≤ (C.M * C.N) ^ 2 * (C.M * C.N) ^ 3 := by gcongr
      _ = _ := by ring
  have hpow' : C.M * C.N ^ 3 ≤ (C.M * C.N) ^ 5 := by
    have : C.M * C.N ^ 3 ≤ C.M ^ 2 * C.N ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    exact this.trans hpow
  unfold blockBudget
  refine (add_le_add href hori).trans ?_
  have h₁ := mul_le_mul_of_nonneg_left hpow (show 0 ≤ A ^ 3 * U by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hpow' (show 0 ≤ A ^ 2 * U by positivity)
  nlinarith [h₁, h₂]

theorem geometric_pair_budget
    {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (D : Sieve.AllIndexNormalizedFamilyData Q)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) (hδε : δ ≤ ε / 100)
    (a : ℝ) (ha : 1 < a) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ C : Context Q, C.D = D → C.δ = δ →
      1 ≤ C.M → 1 ≤ C.N →
      max 1 (C.N ^ 2 / C.M * Real.rpow (C.M * C.N) ε) ≤ C.K →
      C.K ≤ C.M * Real.rpow (C.M * C.N) (-ε) →
      1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
      ∀ (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p),
        p ∈ C.pairs → pairBudget C a p hp ≤
          G * Real.rpow (C.M * C.N) (10 + 4 * δ - δ * (a-1)) := by
  obtain ⟨H, hH, hrat⟩ := LocalTailRatios.uniform_row_ratios D
  obtain ⟨A, hA, hcards⟩ := LocalTailGeometry.polynomial_card_bounds F c
  let P := Real.rpow H a + 2 * Real.rpow H (a - 1)
  let J := 2 + 1 / Real.log 2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨(A ^ 3 + A ^ 2) * P * J, by positivity, ?_⟩
  intro C hCD hCδ hM hN hKlo hKhi hd hdN p hp hpair
  have hM0 : 0 < C.M := by linarith
  have hN0 : 0 < C.N := by linarith
  have hX : 1 ≤ C.M * C.N := by nlinarith
  have hX0 : 0 < C.M * C.N := by positivity
  have hK : 1 ≤ C.K := (le_max_left _ _).trans hKlo
  have hpowε : Real.rpow (C.M * C.N) (-ε) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos hX (by linarith)
  have hKM : C.K ≤ C.M := hKhi.trans (by nlinarith)
  have hkn : (dyadicScales C).card + (1 : ℝ) ≤ J * (C.M * C.N) := by
    have hcard : ((dyadicScales C).card : ℝ) ≤ Vendor.dyadicLength C.K := by
      exact_mod_cast (Finset.card_image_le.trans_eq (Finset.card_range _))
    have hlen := Vendor.dyadicLength_small_power (η := (1 : ℝ)) (by norm_num) hK
    have hKX : C.K ≤ C.M * C.N := hKM.trans (by nlinarith)
    have : (Vendor.dyadicLength C.K : ℝ) + 1 ≤ J * C.K := by
      simpa [J] using hlen
    exact (by linarith : ((dyadicScales C).card : ℝ) + 1 ≤ J * C.K).trans
      (mul_le_mul_of_nonneg_left hKX hJ)
  have hS : 1 ≤ Real.rpow (C.M * C.N) δ := Real.one_le_rpow hX hδ.le
  let U := P * Real.rpow (C.M * C.N) (δ * (1 - a))
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have heq : Real.rpow (Real.rpow (C.M * C.N) δ) (1 - a) =
      Real.rpow (C.M * C.N) (δ * (1 - a)) := by
    simpa only [Real.rpow_eq_pow] using (Real.rpow_mul hX0.le δ (1-a)).symm
  have hcard := hcards C hM hN hd hdN hpair
  have hblock : ∀ B : ℝ, 1 ≤ B → B ≤ C.M → ∀ unit : Bool,
      (unit = true → B = 1) → blockBudget C a p hp B unit ≤
        (A ^ 3 + A ^ 2) * (C.M * C.N) ^ 5 * U := by
    intro B hB hBM unit hunit
    have hrat' := hrat C hCD hM0 hN0 p hp hpair B unit (by linarith) hunit
    have htOriginal : ∀ r ∈ C.originalRows B unit,
        tailBudget a (Real.sqrt (C.M / norm r)) (C.Y2 B) (C.Z2 B) C.L2 ≤ U := by
      intro r hr
      have hrnorm := LocalTailGeometry.original_row_norm C B unit hB hr
      have hnr : 0 < norm r := by linarith [hrnorm.1]
      have hy : 0 < C.Y2 B := by unfold Context.Y2; rw [Real.rpow_eq_pow]; positivity
      have hz : 0 < C.Z2 B := by unfold Context.Z2; rw [Real.rpow_eq_pow]; positivity
      have hl : 0 < C.L2 := by unfold Context.L2 Context.L1; rw [Real.rpow_eq_pow]; positivity
      have h := hrat'.1 r hr
      simp only [hCδ] at h
      have hb := tailBudget_of_ratio_lower_bounds a (Real.sqrt (C.M / norm r))
        (C.Y2 B) (C.Z2 B) C.L2 (Real.rpow (C.M * C.N) δ) H ha hS hH
        (by positivity) hy hz hl h.1 h.2.1 h.2.2
      simpa only [heq] using hb
    have htReflected : ∀ e ∈ C.mobiusDivisors, ∀ r ∈ C.reflectedRows B unit,
        tailBudget a (Real.sqrt (C.dualScale e p / norm r))
          (C.Y1 B e) (C.Z1 B e) C.L1 ≤ U := by
      intro e he r hr
      have hen := (LocalTailGeometry.mobius_divisor_norm C he).1
      have hpn := LocalTailGeometry.norm_one_le (mul_ne_zero hp.hu0 hp.hv0)
      have hrn := (LocalTailGeometry.reflected_row_norm C B unit hB hr).1
      have he0 : 0 < norm e := by linarith
      have hp0 : 0 < norm (p.1 * p.2) := by linarith
      have hr0 : 0 < norm r := by linarith
      have hd0 : 0 < norm C.d := by linarith
      have ht : 0 < Real.sqrt (C.dualScale e p / norm r) := by
        unfold Context.dualScale; positivity
      have hy : 0 < C.Y1 B e := by unfold Context.Y1; rw [Real.rpow_eq_pow]; positivity
      have hz : 0 < C.Z1 B e := by unfold Context.Z1; rw [Real.rpow_eq_pow]; positivity
      have hl : 0 < C.L1 := by unfold Context.L1; rw [Real.rpow_eq_pow]; positivity
      have h := hrat'.2 e he r hr
      simp only [hCδ] at h
      have hb := tailBudget_of_ratio_lower_bounds a (Real.sqrt (C.dualScale e p / norm r))
        (C.Y1 B e) (C.Z1 B e) C.L1 (Real.rpow (C.M * C.N) δ) H ha hS hH
        ht hy hz hl h.1 h.2.1 h.2.2
      simpa only [heq] using hb
    exact blockBudget_bound C a A U B unit p hp hM hN hA hU hcard.1 hcard.2.1
      hcard.2.2.1 (hcard.2.2.2 B hB hBM unit).2
      (hcard.2.2.2 B hB hBM unit).1 htReflected htOriginal
  have htotal : pairBudget C a p hp ≤
      ((dyadicScales C).card + (1 : ℝ)) * ((A ^ 3 + A ^ 2) * (C.M * C.N) ^ 5 * U) := by
    unfold pairBudget
    have hsum : (∑ B ∈ dyadicScales C, blockBudget C a p hp B) ≤
        (dyadicScales C).card * ((A ^ 3 + A ^ 2) * (C.M * C.N) ^ 5 * U) := by
      calc
        _ ≤ ∑ B ∈ dyadicScales C, (A ^ 3 + A ^ 2) * (C.M * C.N) ^ 5 * U := by
          apply Finset.sum_le_sum
          intro B hB
          have hsc := LocalTailGeometry.active_scale_bounds C hK hB
          exact hblock B hsc.1 (hsc.2.le.trans hKM) false (by simp)
        _ = _ := by simp
    have hu := hblock 1 le_rfl hM true (by simp)
    nlinarith
  have hexp : 6 + δ * (1 - a) ≤ 10 + 4 * δ - δ * (a - 1) := by linarith
  have hpows : Real.rpow (C.M * C.N) (6 + δ * (1 - a)) ≤
      Real.rpow (C.M * C.N) (10 + 4 * δ - δ * (a - 1)) :=
    Real.rpow_le_rpow_of_exponent_le hX hexp
  calc
    _ ≤ (J * (C.M * C.N)) * ((A ^ 3 + A ^ 2) * (C.M * C.N) ^ 5 * U) :=
      htotal.trans (mul_le_mul_of_nonneg_right hkn (by positivity))
    _ = ((A ^ 3 + A ^ 2) * P * J) * Real.rpow (C.M * C.N) (6 + δ * (1 - a)) := by
      dsimp [U]
      rw [Real.rpow_add hX0, Real.rpow_ofNat]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpows (by positivity)
end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly.LocalTailAux

end

end
