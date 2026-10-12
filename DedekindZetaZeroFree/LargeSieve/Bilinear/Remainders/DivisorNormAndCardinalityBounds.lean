module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.SevenTermApproximation
public import DedekindZetaZeroFree.Analysis.DyadicLengthBounds

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly.LocalTailGeometry
open ExplicitTerms
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

lemma norm_mul (u v : Ideal (𝓞 F)) : norm (u * v) = norm u * norm v := by
  simp [ExplicitTerms.norm, map_mul]

lemma norm_nonneg (u : Ideal (𝓞 F)) : 0 ≤ norm u := by
  unfold ExplicitTerms.norm; positivity

lemma norm_one_le {u : Ideal (𝓞 F)} (hu : u ≠ ⊥) : 1 ≤ norm u := by
  unfold ExplicitTerms.norm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hu)

lemma norm_le_of_dvd {u v : Ideal (𝓞 F)} (hv : v ≠ ⊥) (h : u ∣ v) :
    norm u ≤ norm v := by
  unfold ExplicitTerms.norm
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hv))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp h))

lemma unit_row_eq_top {m : Ideal (𝓞 F)} {K : ℝ} {r : Ideal (𝓞 F)}
    (hr : r ∈ ReflectedSigma4.unitRows c m K) : r = ⊤ := by
  exact Finset.mem_singleton.mp (Finset.mem_filter.mp hr).1

lemma core_row_norm (C : Context Q) (B : ℝ) (unit : Bool) (hB : 1 ≤ B)
    {r : Ideal (𝓞 F)} (hr : r ∈ C.reflectedCoreRows B unit) :
    1 ≤ norm r ∧ norm r ≤ 2 * B := by
  cases unit
  · have hr' := Finset.mem_filter.mp hr
    have hs := (Sieve.mem_paperShell F c B r).mp hr'.1
    exact ⟨by simpa [ExplicitTerms.norm] using hB.trans hs.2.2.1.le, hs.2.2.2⟩
  · have he : r = ⊤ := unit_row_eq_top hr
    subst r
    simp only [ExplicitTerms.norm, Ideal.absNorm_top, Nat.cast_one]
    constructor <;> linarith

lemma original_row_norm (C : Context Q) (B : ℝ) (unit : Bool) (hB : 1 ≤ B)
    {r : Ideal (𝓞 F)} (hr : r ∈ C.originalRows B unit) :
    1 ≤ norm r ∧ norm r ≤ 2 * B := by
  cases unit
  · have hr' := Finset.mem_filter.mp hr
    have hs := (Sieve.mem_paperShell F (c * C.d) B r).mp hr'.1
    exact ⟨by simpa [ExplicitTerms.norm] using hB.trans hs.2.2.1.le, hs.2.2.2⟩
  · have he : r = ⊤ := unit_row_eq_top hr
    subst r
    simp only [ExplicitTerms.norm, Ideal.absNorm_top, Nat.cast_one]
    constructor <;> linarith

def supportedNormBound (c : Ideal (𝓞 F)) : ℝ :=
  1 + ∑ t ∈ squarefreeBadPool c, norm t

lemma supportedNormBound_one_le (c : Ideal (𝓞 F)) : 1 ≤ supportedNormBound c := by
  unfold supportedNormBound
  have : 0 ≤ ∑ t ∈ squarefreeBadPool c, norm t := Finset.sum_nonneg (by
    intro t ht; exact norm_nonneg t)
  linarith

lemma supported_norm_le {t : Ideal (𝓞 F)} (ht : t ∈ squarefreeBadPool c) :
    norm t ≤ supportedNormBound c := by
  have h := Finset.single_le_sum (fun t ht => norm_nonneg t) ht
  unfold supportedNormBound
  linarith

lemma reflected_row_norm (C : Context Q) (B : ℝ) (unit : Bool) (hB : 1 ≤ B)
    {r : Ideal (𝓞 F)} (hr : r ∈ C.reflectedRows B unit) :
    1 ≤ norm r ∧ norm r ≤ supportedNormBound c * (2 * B) := by
  obtain ⟨⟨t,s⟩, hts, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨hts, hmask⟩ := Finset.mem_filter.mp hts
  obtain ⟨ht, hs⟩ := Finset.mem_product.mp hts
  have hn := core_row_norm C B unit hB hs
  refine ⟨norm_one_le hmask.2.2, ?_⟩
  rw [norm_mul]
  exact mul_le_mul (supported_norm_le ht) hn.2 (norm_nonneg s)
    (by linarith [supportedNormBound_one_le c])

lemma pair_norm_bounds (C : Context Q) (hN : 1 ≤ C.N) (hd : 1 ≤ norm C.d)
    {p : Ideal (𝓞 F) × Ideal (𝓞 F)} (hp : p ∈ C.pairs) :
    (C.N / norm C.d) ^ 2 < norm (p.1 * p.2) ∧
    norm (p.1 * p.2) ≤ (2 * C.N / norm C.d) ^ 2 := by
  obtain ⟨huv, hpv⟩ := Finset.mem_filter.mp hp
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
  have hu' := (Sieve.mem_paperShell F c C.N (C.d * p.1)).mp
    (Finset.mem_filter.mp hu).2.1
  have hv' := (Sieve.mem_paperShell F c C.N (C.d * p.2)).mp
    (Finset.mem_filter.mp hv).2.1
  have hd0 : 0 < norm C.d := by linarith
  have hN0 : 0 < C.N := by linarith
  have ulo : C.N / norm C.d < norm p.1 := by
    rw [div_lt_iff₀ hd0]; simpa [ExplicitTerms.norm, map_mul, mul_comm] using hu'.2.2.1
  have vlo : C.N / norm C.d < norm p.2 := by
    rw [div_lt_iff₀ hd0]; simpa [ExplicitTerms.norm, map_mul, mul_comm] using hv'.2.2.1
  have uhi : norm p.1 ≤ 2 * C.N / norm C.d := by
    rw [le_div_iff₀ hd0]; simpa [ExplicitTerms.norm, map_mul, mul_comm] using hu'.2.2.2
  have vhi : norm p.2 ≤ 2 * C.N / norm C.d := by
    rw [le_div_iff₀ hd0]; simpa [ExplicitTerms.norm, map_mul, mul_comm] using hv'.2.2.2
  rw [norm_mul, pow_two, pow_two]
  exact ⟨mul_lt_mul ulo vlo.le (div_pos hN0 hd0) (by linarith [norm_nonneg p.1]),
    mul_le_mul uhi vhi (norm_nonneg p.2) (by positivity)⟩

lemma active_scale_bounds (C : Context Q) (hK : 1 ≤ C.K)
    {B : ℝ} (hB : B ∈ dyadicScales C) : 1 ≤ B ∧ B < C.K := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
  exact ⟨one_le_pow₀ (by norm_num),
    Vendor.pow_lt_of_lt_dyadicLength hK (Finset.mem_range.mp hi)⟩

lemma mobius_divisor_norm (C : Context Q) {e : Ideal (𝓞 F)}
    (he : e ∈ C.mobiusDivisors) :
    1 ≤ norm e ∧ norm e ≤ norm c * norm C.d := by
  refine ⟨norm_one_le (ne_bot_of_mem_idealDivisors he), ?_⟩
  have hcd : c * C.d ≠ ⊥ := mul_ne_zero C.D.original_ne_bot C.hd0
  have he' := absNorm_le_of_mem_idealDivisors he
  have hrad : Ideal.absNorm (c * C.d).radical ≤ Ideal.absNorm (c * C.d) :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hcd))
      (Ideal.absNorm_dvd_absNorm_of_le Ideal.le_radical)
  simpa [ExplicitTerms.norm, map_mul] using
    (show (Ideal.absNorm e : ℝ) ≤ (Ideal.absNorm (c * C.d) : ℝ) by exact_mod_cast he'.trans hrad)

lemma primitive_norm_le_one (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F))
    (hp : C.ValidPair p) (e : Ideal (𝓞 F)) : ‖C.primitive p hp e‖ ≤ 1 := by
  exact ((primitiveProductQuadratic Q hp.hu0 hp.hv0 hp.hu hp.hv hp.huc hp.hvc hp.huv
    hp.hquotientClass (C.primitive p hp) (C.primitive_spec p hp).2.1).1 e).2.2.2

lemma prefactor_norm_le (C : Context Q) (hM : 1 ≤ C.M)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p)
    {e : Ideal (𝓞 F)} (he : e ∈ C.mobiusDivisors) :
    ‖C.prefactor e p hp‖ ≤ C.M := by
  have hen := (mobius_divisor_norm C he).1
  have hpn := norm_one_le (mul_ne_zero hp.hu0 hp.hv0)
  have hsq : 1 ≤ Real.sqrt (norm (p.1 * p.2)) := by
    simpa using Real.sqrt_le_sqrt hpn
  have hden : 1 ≤ norm e * Real.sqrt (norm (p.1 * p.2)) := by nlinarith
  have hmo : ‖(UniqueFactorizationMonoid.moebius e : ℂ)‖ ≤ 1 := by
    rw [UniqueFactorizationMonoid.moebius]; split <;> simp
  have hprod : ‖(UniqueFactorizationMonoid.moebius e : ℂ) * C.primitive p hp e‖ ≤ 1 := by
    rw [_root_.norm_mul]
    exact (mul_le_mul hmo (primitive_norm_le_one C p hp e) (_root_.norm_nonneg _)
      zero_le_one).trans_eq (by ring)
  have hM0 : 0 ≤ C.M := by linarith
  have hq : ‖((C.M : ℂ) / ((norm e : ℂ) * (Real.sqrt (norm (p.1 * p.2)) : ℂ)))‖ =
      C.M / (norm e * Real.sqrt (norm (p.1 * p.2))) := by
    rw [_root_.norm_div, _root_.norm_mul, Complex.norm_real, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hM0, abs_of_nonneg (by linarith : 0 ≤ norm e),
      abs_of_nonneg (Real.sqrt_nonneg _)]
  unfold Context.prefactor
  rw [_root_.norm_mul, hq]
  exact (mul_le_mul_of_nonneg_right hprod (div_nonneg hM0 (by linarith))).trans
    (by simpa using div_le_self hM0 hden)

lemma finite_card_bounds (F : Type) [Field F] [NumberField F] :
    ∃ H : ℝ, 1 ≤ H ∧
      (∀ j : Ideal (𝓞 F), (idealDivisors j).card ≤ H * norm j) ∧
      (∀ {c : Ideal (𝓞 F)} {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
        (C : Context Q) (B : ℝ) (unit : Bool), 1 ≤ B →
        (C.originalRows B unit).card ≤ H * (2 * B) ∧
        (C.reflectedRows B unit).card ≤ H * (supportedNormBound c * (2 * B))) := by
  obtain ⟨H, hH, _, hcount⟩ := exists_ideal_count_bound_finset F
  refine ⟨H, hH, ?_, ?_⟩
  · intro j
    by_cases hj : j = ⊥
    · subst j
      simp [idealDivisors, ExplicitTerms.norm]
    · apply hcount (norm j) (norm_one_le hj)
      intro e he
      change (Ideal.absNorm e : ℝ) ≤ (Ideal.absNorm j : ℝ)
      exact_mod_cast absNorm_le_of_mem_idealDivisors he
  · intro c Q C B unit hB
    constructor
    · apply hcount (2 * B) (by linarith)
      intro r hr
      exact (original_row_norm C B unit hB hr).2
    · apply hcount (supportedNormBound c * (2 * B))
        (by nlinarith [supportedNormBound_one_le c])
      intro r hr
      exact (reflected_row_norm C B unit hB hr).2

lemma mobius_card_le (C : Context Q) (H : ℝ)
    (hcount : ∀ j : Ideal (𝓞 F), (idealDivisors j).card ≤ H * norm j)
    (hH : 0 ≤ H) : C.mobiusDivisors.card ≤ H * (norm c * norm C.d) := by
  have hcd : c * C.d ≠ ⊥ := mul_ne_zero C.D.original_ne_bot C.hd0
  have hrad : norm (c * C.d).radical ≤ norm c * norm C.d := by
    simpa [norm_mul] using norm_le_of_dvd hcd (Ideal.dvd_iff_le.mpr Ideal.le_radical)
  exact (hcount _).trans (mul_le_mul_of_nonneg_left hrad hH)

set_option maxHeartbeats 1000000 in

lemma polynomial_card_bounds (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) :
    ∃ H : ℝ, 1 ≤ H ∧
    ∀ {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c} (C : Context Q),
      1 ≤ C.M → 1 ≤ C.N → 1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
      ∀ {p : Ideal (𝓞 F) × Ideal (𝓞 F)}, p ∈ C.pairs →
        (C.mobiusDivisors.card : ℝ) ≤ H * C.N ∧
        ((idealDivisors (p.1 * p.2)).card : ℝ) ≤ H * C.N ^ 2 ∧
        ((idealDivisors ((c * C.d) * (p.1 * p.2))).card : ℝ) ≤ H * C.N ^ 3 ∧
        ∀ B : ℝ, 1 ≤ B → B ≤ C.M → ∀ unit : Bool,
          (C.originalRows B unit).card ≤ H * C.M ∧
          (C.reflectedRows B unit).card ≤ H * C.M := by
  obtain ⟨A, hA, hdiv, hrows⟩ := finite_card_bounds F
  let nc := max 1 (norm c)
  let sc := supportedNormBound c
  have hnc : 1 ≤ nc := le_max_left _ _
  have hsc : 1 ≤ sc := supportedNormBound_one_le c
  have hAnc : 0 ≤ A * nc := mul_nonneg (by linarith) (by linarith)
  have hAncsc : 0 ≤ A * nc * sc := mul_nonneg hAnc (by linarith)
  refine ⟨8 * A * nc * sc, by nlinarith [mul_le_mul hA hnc zero_le_one (by linarith : 0 ≤ A)], ?_⟩
  intro Q C hM hN hd hdN p hp
  have hpN := (pair_norm_bounds C hN hd hp).2
  have hq : 2 * C.N / norm C.d ≤ 2 * C.N :=
    div_le_self (by linarith) hd
  have hq0 : 0 ≤ 2 * C.N / norm C.d := by positivity
  have hpn : norm (p.1 * p.2) ≤ 4 * C.N ^ 2 := by
    nlinarith [sq_nonneg (2 * C.N - 2 * C.N / norm C.d)]
  have hcn : norm c ≤ nc := le_max_right _ _
  have hA0 : 0 ≤ A := by linarith
  have hnc0 : 0 ≤ nc := by linarith
  have hsc0 : 0 ≤ sc := by linarith
  have hbase : A ≤ A * nc * sc := by nlinarith
  have hbasec : A * norm c ≤ A * nc * sc := by nlinarith
  have hmcard := mobius_card_le C A hdiv hA0
  have hprodcard := hdiv (p.1 * p.2)
  have hcdcard := hdiv ((c * C.d) * (p.1 * p.2))
  have hdprod : norm ((c * C.d) * (p.1 * p.2)) ≤ 8 * nc * C.N ^ 3 := by
    rw [norm_mul, norm_mul]
    have h1 : norm c * norm C.d ≤ nc * (2 * C.N) :=
      mul_le_mul hcn hdN (norm_nonneg _) hnc0
    have h2 := mul_le_mul h1 hpn (norm_nonneg _) (by positivity : 0 ≤ nc * (2 * C.N))
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : A * (norm c * norm C.d) ≤ A * (nc * (2 * C.N)) := by
      gcongr
    have hcoef : 2 * A * nc ≤ 8 * A * nc * sc := by nlinarith
    exact hmcard.trans (h1.trans (by nlinarith))
  · have h1 := mul_le_mul_of_nonneg_left hpn hA0
    have hcoef : 4 * A ≤ 8 * A * nc * sc := by nlinarith
    exact hprodcard.trans (h1.trans (by nlinarith [sq_nonneg C.N]))
  · have h1 := mul_le_mul_of_nonneg_left hdprod hA0
    have hcoef : 8 * A * nc ≤ 8 * A * nc * sc := by nlinarith
    exact hcdcard.trans (h1.trans (by nlinarith [show 0 ≤ C.N ^ 3 by positivity]))
  · intro B hB hBM unit
    have hr := hrows C B unit hB
    have ho := mul_le_mul_of_nonneg_left (show 2 * B ≤ 2 * C.M by linarith) hA0
    have hre := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (show 2 * B ≤ 2 * C.M by linarith) hsc0) hA0
    have hcoef1 : 2 * A ≤ 8 * A * nc * sc := by nlinarith
    have hcoef2 : 2 * A * sc ≤ 8 * A * nc * sc := by nlinarith
    exact ⟨hr.1.trans (ho.trans (by nlinarith)), hr.2.trans (hre.trans (by nlinarith))⟩

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly.LocalTailGeometry

end
