module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Definitions
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Convexity

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.ReciprocalLogDiskAux

open DedekindZetaZeroFree NumberField Metric
open scoped Classical

theorem exists_analytic_log_ball {g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (Metric.ball c R)) (h0 : ∀ s ∈ Metric.ball c R, g s ≠ 0)
    {w : ℂ} (hw : Complex.exp w = g c) (hR : 0 < R) :
    ∃ ℓ : ℂ → ℂ, AnalyticOnNhd ℂ ℓ (Metric.ball c R) ∧
      (∀ s ∈ Metric.ball c R, g s = Complex.exp (ℓ s)) ∧ ℓ c = w := by
  have hq : AnalyticOnNhd ℂ (fun s => deriv g s / g s) (Metric.ball c R) :=
    fun s hs => ((hg.deriv) s hs).div (hg s hs) (h0 s hs)
  obtain ⟨F, hF⟩ := (hq.differentiableOn).isExactOn_ball (c := c) (r := R)
  have hFd : DifferentiableOn ℂ F (Metric.ball c R) := fun s hs => (hF s hs).differentiableAt.differentiableWithinAt
  set ℓ : ℂ → ℂ := fun s => F s - F c + w with hℓ
  have hdiff : DifferentiableOn ℂ ℓ (Metric.ball c R) := by
    intro s hs
    exact ((hFd s hs).sub (differentiableWithinAt_const _)).add (differentiableWithinAt_const _)
  have hcmem : c ∈ Metric.ball c R := mem_ball_self hR
  refine ⟨ℓ, hdiff.analyticOnNhd isOpen_ball, ?_, by simp [hℓ]⟩

  set k : ℂ → ℂ := fun s => g s * Complex.exp (-ℓ s) with hk
  have hdA : ∀ s ∈ Metric.ball c R, DifferentiableAt ℂ ℓ s := fun s hs =>
    (hdiff s hs).differentiableAt (isOpen_ball.mem_nhds hs)
  have hkd : DifferentiableOn ℂ k (Metric.ball c R) := by
    intro s hs
    exact DifferentiableAt.differentiableWithinAt
      (DifferentiableAt.mul ((hg s hs).differentiableAt) ((hdA s hs).neg.cexp))
  have hk0 : (Metric.ball c R).EqOn (deriv k) 0 := by
    intro s hs
    have hgs : HasDerivAt g (deriv g s) s := ((hg s hs).differentiableAt).hasDerivAt
    have hlin : HasDerivAt ℓ (deriv g s / g s) s := by
      have := hF s hs
      simpa [hℓ] using this.sub_const (F c) |>.add_const w
    have hexp : HasDerivAt (fun s => Complex.exp (-ℓ s)) (Complex.exp (-ℓ s) * (-(deriv g s / g s))) s := by
      have := (hlin.neg).cexp
      simpa using this
    have hkd' : HasDerivAt k (deriv g s * Complex.exp (-ℓ s) + g s * (Complex.exp (-ℓ s) * -(deriv g s / g s))) s :=
      hgs.mul hexp
    show deriv k s = 0
    rw [hkd'.deriv]
    have hgne := h0 s hs
    field_simp
    ring
  have hconst : ∀ x ∈ Metric.ball c R, ∀ y ∈ Metric.ball c R, k x = k y := fun x hx y hy =>
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected hkd hk0 hx hy
  intro s hs
  have hkc : k s = k c := hconst s hs c hcmem
  have hkc' : k c = 1 := by
    simp only [hk, hℓ, sub_self, zero_add, Complex.exp_neg, hw]
    exact mul_inv_cancel₀ (h0 c hcmem)
  have hks : k s = 1 := hkc.trans hkc'
  have hone : Complex.exp (ℓ s) * Complex.exp (-ℓ s) = 1 := by
    rw [← Complex.exp_add]; simp
  simp only [hk] at hks
  calc g s = g s * (Complex.exp (ℓ s) * Complex.exp (-ℓ s)) := by rw [hone, mul_one]
    _ = Complex.exp (ℓ s) * (g s * Complex.exp (-ℓ s)) := by ring
    _ = Complex.exp (ℓ s) := by rw [hks, mul_one]

theorem analytic_log_unique_ball {ℓ₁ ℓ₂ : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (h₁ : AnalyticOnNhd ℂ ℓ₁ (Metric.ball c R)) (h₂ : AnalyticOnNhd ℂ ℓ₂ (Metric.ball c R))
    (he : ∀ s ∈ Metric.ball c R, Complex.exp (ℓ₁ s) = Complex.exp (ℓ₂ s)) (hc : ℓ₁ c = ℓ₂ c) :
    ∀ s ∈ Metric.ball c R, ℓ₁ s = ℓ₂ s := by
  set f : ℂ → ℂ := fun s => ℓ₁ s - ℓ₂ s with hf
  have hfd : DifferentiableOn ℂ f (Metric.ball c R) :=
    (h₁.differentiableOn.sub h₂.differentiableOn)
  have hexp : ∀ s ∈ Metric.ball c R, Complex.exp (f s) = 1 := by
    intro s hs
    simp only [hf]
    rw [Complex.exp_sub, he s hs, div_self (Complex.exp_ne_zero _)]
  have hderiv : (Metric.ball c R).EqOn (deriv f) 0 := by
    intro s hs
    have hfs : DifferentiableAt ℂ f s := hfd.differentiableAt (isOpen_ball.mem_nhds hs)
    have hcomp : HasDerivAt (fun z => Complex.exp (f z)) (Complex.exp (f s) * deriv f s) s :=
      (hfs.hasDerivAt).cexp
    have hEq : (fun z => Complex.exp (f z)) =ᶠ[nhds s] fun _ => (1 : ℂ) :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hs) (fun z hz => hexp z hz)
    have h1 : HasDerivAt (fun z => Complex.exp (f z)) 0 s :=
      (hasDerivAt_const s (1 : ℂ)).congr_of_eventuallyEq hEq
    have := hcomp.unique h1
    rw [hexp s hs, one_mul] at this
    simpa using this
  have hconst : ∀ x ∈ Metric.ball c R, ∀ y ∈ Metric.ball c R, f x = f y := fun x hx y hy =>
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected hfd hderiv hx hy
  intro s hs
  have : f s = f c := hconst s hs c (mem_ball_self hR)
  simp only [hf] at this
  rw [hc] at this
  linear_combination this

private theorem bc_aux {ℓ : ℂ → ℂ} {c : ℂ} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hℓ : AnalyticOnNhd ℂ ℓ (Metric.ball c R)) {A : ℝ} (hA : 0 < A)
    (hRe : ∀ s ∈ Metric.ball c R, (ℓ s - ℓ c).re ≤ A) :
    ∀ s ∈ closedBall c r, ‖ℓ s - ℓ c‖ ≤ 2 * A * r / (R - r) := by
  have hR : 0 < R := hr.trans hrR
  set h : ℂ → ℂ := fun s => ℓ s - ℓ c with hh
  have hpos : ∀ s ∈ Metric.ball c R, 0 < (2 * (A : ℂ) - h s).re := by
    intro s hs
    have := hRe s hs
    simp only [hh] at this ⊢
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re,
      Complex.im_ofNat, Complex.ofReal_im] at this ⊢
    linarith
  have hne : ∀ s ∈ Metric.ball c R, 2 * (A : ℂ) - h s ≠ 0 := by
    intro s hs h0
    have := hpos s hs
    rw [h0] at this
    simp at this
  set φ : ℂ → ℂ := fun s => h s / (2 * (A : ℂ) - h s) with hφ
  have hhd : DifferentiableOn ℂ h (Metric.ball c R) :=
    hℓ.differentiableOn.sub (differentiableOn_const _)
  have hφd : DifferentiableOn ℂ φ (Metric.ball c R) :=
    hhd.div (differentiableOn_const _ |>.sub hhd) hne
  have hφ1 : ∀ s ∈ Metric.ball c R, ‖φ s‖ ≤ 1 := by
    intro s hs
    simp only [hφ, norm_div]
    have hn : 0 < ‖2 * (A : ℂ) - h s‖ := norm_pos_iff.mpr (hne s hs)
    rw [div_le_one hn]
    have := hRe s hs
    have h2 : ‖h s‖ ^ 2 ≤ ‖2 * (A : ℂ) - h s‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [hh] at this ⊢
      simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re,
        Complex.im_ofNat, Complex.ofReal_im, Complex.sub_im, Complex.mul_im] at this ⊢
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hφc : φ c = 0 := by simp [hφ, hh]
  have hmaps : Set.MapsTo φ (Metric.ball c R) (closedBall (φ c) 1) := by
    intro s hs
    rw [hφc]
    simpa using hφ1 s hs
  intro s hs
  have hsR : s ∈ Metric.ball c R := by
    refine closedBall_subset_ball hrR hs
  have hS := Complex.dist_le_div_mul_dist_of_mapsTo_ball hφd hmaps hsR
  rw [hφc, dist_zero_right, dist_eq_norm] at hS
  have hsr : ‖s - c‖ ≤ r := by simpa [dist_eq_norm] using hs
  have ht : ‖φ s‖ ≤ r / R := by
    calc ‖φ s‖ ≤ 1 / R * ‖s - c‖ := hS
      _ ≤ 1 / R * r := by gcongr
      _ = r / R := by ring
  have heq : h s * (1 + φ s) = 2 * (A : ℂ) * φ s := by
    have := hne s hsR
    simp only [hφ]
    field_simp
    ring
  have htl : r / R < 1 := (div_lt_one hR).2 hrR
  have h1 : 1 - r / R ≤ ‖1 + φ s‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-φ s)
    simp only [norm_neg, norm_one, sub_neg_eq_add] at this
    linarith
  have h1pos : 0 < 1 - r / R := by linarith
  have hnorm : ‖h s‖ * ‖1 + φ s‖ = 2 * A * ‖φ s‖ := by
    have := congrArg norm heq
    rw [norm_mul, norm_mul, norm_mul] at this
    simpa [abs_of_pos hA] using this
  have hfin : ‖h s‖ * (1 - r / R) ≤ 2 * A * (r / R) := by
    calc ‖h s‖ * (1 - r / R) ≤ ‖h s‖ * ‖1 + φ s‖ := by gcongr
      _ = 2 * A * ‖φ s‖ := hnorm
      _ ≤ 2 * A * (r / R) := by gcongr
  have hRr : 0 < R - r := by linarith
  have : 1 - r / R = (R - r) / R := by field_simp
  rw [this] at hfin
  rw [le_div_iff₀ hRr]
  have hfin' : ‖h s‖ * (R - r) ≤ 2 * A * r := by
    have := hfin
    rw [mul_div_assoc', div_le_iff₀ hR] at this
    have e : 2 * A * (r / R) * R = 2 * A * r := by field_simp
    rw [e] at this
    exact this
  exact hfin'

theorem borel_caratheodory {ℓ : ℂ → ℂ} {c : ℂ} {R r M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hM0 : 0 ≤ M) (hℓ : AnalyticOnNhd ℂ ℓ (Metric.ball c R))
    (hM : ∀ s ∈ Metric.ball c R, (ℓ s).re ≤ M) :
    ∀ s ∈ closedBall c r,
      ‖ℓ s‖ ≤ 2 * r / (R - r) * M + (R + r) / (R - r) * ‖ℓ c‖ := by
  intro s hs
  have hR : 0 < R := hr.trans hrR
  have hRr : 0 < R - r := by linarith
  set A0 : ℝ := M + ‖ℓ c‖ with hA0
  have hA00 : 0 ≤ A0 := by positivity
  have key : ‖ℓ s - ℓ c‖ ≤ 2 * A0 * r / (R - r) := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hA : 0 < A0 + ε * (R - r) / (2 * r) := by positivity
    have := bc_aux hr hrR hℓ hA (fun s hs => by
      have h1 := hM s hs
      have h2 : (ℓ c).re ≥ -‖ℓ c‖ := by
        have := Complex.abs_re_le_norm (ℓ c)
        linarith [neg_abs_le (ℓ c).re]
      have h3 : 0 ≤ ε * (R - r) / (2 * r) := by positivity
      simp only [Complex.sub_re]
      linarith) s hs
    refine this.trans (le_of_eq ?_)
    field_simp
  have hle : ‖ℓ s‖ ≤ ‖ℓ s - ℓ c‖ + ‖ℓ c‖ := by
    have := norm_add_le (ℓ s - ℓ c) (ℓ c)
    simpa using this
  have e : 2 * A0 * r / (R - r) + ‖ℓ c‖ =
      2 * r / (R - r) * M + (R + r) / (R - r) * ‖ℓ c‖ := by
    simp only [hA0]
    field_simp
    ring
  linarith

section EulerLog

open DedekindZetaZeroFree.ExteriorIdealEuler DedekindZetaZeroFree.HeckeLogProof

private def primeEquiv (F : Type) [Field F] [NumberField F] :
    {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥} ≃ PrimeIndex (⊤ : Ideal (𝓞 F)) where
  toFun P := ⟨⟨P.1, P.2.2, by simp⟩, (Ideal.prime_iff_isPrime P.2.2).2 P.2.1⟩
  invFun p := ⟨p.1.1, (Ideal.prime_iff_isPrime p.1.2.1).1 p.2, p.1.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem char_pow {F : Type} [Field F] [NumberField F] (ω : Detector.PrimitiveFrequencyCharacter F)
    (I : Ideal (𝓞 F)) (k : ℕ) : ω.character (I ^ k) = ω.character I ^ k := by
  induction k with
  | zero => simpa using ω.character.map_top'
  | succ k ih => rw [pow_succ, ω.character.map_mul', ih, pow_succ]

private theorem inner_eq {F : Type} [Field F] [NumberField F] (ω : Detector.PrimitiveFrequencyCharacter F)
    (s : ℂ) (hs : 1 < s.re) (P : {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥}) :
    ∑' k : ℕ, ω.character (P.1 ^ (k + 1)) /
            (((k : ℂ) + 1) * (Ideal.absNorm P.1 : ℂ) ^ (((k : ℂ) + 1) * s)) =
      -Complex.log (1 - primeTerm (fun I : ExteriorIdeal (⊤ : Ideal (𝓞 F)) => ω.character I.val) s
        (primeEquiv F P)) := by
  have ha := ray_isCoefficient ω.conductor ω.conductor_ne_zero ω.character
  have hlt := norm_primeTerm_lt_one _ ha s hs (primeEquiv F P)
  have hN : (Ideal.absNorm P.1 : ℂ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.2.2)
  have h := (Complex.hasSum_taylorSeries_neg_log' hlt).tsum_eq
  rw [← h]
  refine tsum_congr fun k => ?_
  have e1 : primeTerm (fun I : ExteriorIdeal (⊤ : Ideal (𝓞 F)) => ω.character I.val) s
        (primeEquiv F P) = ω.character P.1 * (Ideal.absNorm P.1 : ℂ) ^ (-s) := rfl
  rw [e1, char_pow, mul_pow, ← Complex.cpow_nat_mul, Nat.cast_add, Nat.cast_one,
    mul_neg, Complex.cpow_neg]
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hpow : (Ideal.absNorm P.1 : ℂ) ^ (((k : ℂ) + 1) * s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; simp [hN]
  field_simp

private theorem sum_eq_eulerLog {F : Type} [Field F] [NumberField F]
    (ω : Detector.PrimitiveFrequencyCharacter F) (s : ℂ) (hs : 1 < s.re) :
    ∑' P : {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥},
          ∑' k : ℕ, ω.character (P.1 ^ (k + 1)) /
            (((k : ℂ) + 1) * (Ideal.absNorm P.1 : ℂ) ^ (((k : ℂ) + 1) * s)) =
      eulerLog (fun I : ExteriorIdeal (⊤ : Ideal (𝓞 F)) => ω.character I.val) s := by
  unfold eulerLog
  rw [← (primeEquiv F).tsum_eq]
  exact tsum_congr fun P => inner_eq ω s hs P

theorem euler_log_facts (F : Type) [Field F] [NumberField F] :
    ∃ E : ℝ, 0 < E ∧ ∀ ω : Detector.PrimitiveFrequencyCharacter F,
      AnalyticOnNhd ℂ (fun s : ℂ =>
        ∑' P : {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥},
          ∑' k : ℕ, ω.character (P.1 ^ (k + 1)) /
            (((k : ℂ) + 1) * (Ideal.absNorm P.1 : ℂ) ^ (((k : ℂ) + 1) * s)))
        {s : ℂ | 1 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        Complex.exp (∑' P : {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥},
          ∑' k : ℕ, ω.character (P.1 ^ (k + 1)) /
            (((k : ℂ) + 1) * (Ideal.absNorm P.1 : ℂ) ^ (((k : ℂ) + 1) * s))) =
          Detector.idealLSeries F ω.character s) ∧
      (∀ s : ℂ, 1001 / 1000 ≤ s.re →
        ‖∑' P : {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥},
          ∑' k : ℕ, ω.character (P.1 ^ (k + 1)) /
            (((k : ℂ) + 1) * (Ideal.absNorm P.1 : ℂ) ^ (((k : ℂ) + 1) * s))‖ ≤ E) := by
  refine ⟨(3 / 2 : ℝ) * ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-(1001 / 1000 : ℝ)) + 1,
    ?_, fun ω => ?_⟩
  · have : 0 ≤ ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-(1001 / 1000 : ℝ)) :=
      tsum_nonneg fun I => Real.rpow_nonneg (by unfold idealNorm; positivity) _
    linarith
  have ha := ray_isCoefficient ω.conductor ω.conductor_ne_zero ω.character
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine ⟨?_, ?_, ?_⟩
  · refine ((eulerLog_differentiableOn _ ha).analyticOnNhd hopen).congr hopen ?_
    intro s hs
    exact (sum_eq_eulerLog ω s hs).symm
  · intro s hs
    rw [sum_eq_eulerLog ω s hs, exp_eulerLog _ ha s hs]
    unfold Detector.idealLSeries
    set g : Ideal (𝓞 F) → ℂ := fun n => if n ≠ ⊥ then ω.character n * (Ideal.absNorm n : ℂ) ^ (-s)
      else 0 with hg
    have hsupp : Function.support g ⊆ {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ ⊤ = ⊤} := by
      intro I hI
      simp only [Function.mem_support] at hI
      refine ⟨?_, by simp⟩
      intro h
      exact hI (by simp [hg, h])
    rw [← tsum_subtype_eq_of_support_subset (f := g) hsupp]
    refine tsum_congr fun I => ?_
    have := I.2.1
    simp [hg, summand, this]
  · intro s hs
    have hs1 : 1 < s.re := by linarith
    rw [sum_eq_eulerLog ω s hs1]
    have := eulerLog_norm_le _ ha (1001 / 1000) (by norm_num) s hs
    linarith

end EulerLog

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem convexity_upper_bound (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧
      ∀ u : D.Row, u.u ≠ 1 → ∀ U : ℝ, 2 ≤ U → U ≤ D.q u → D.q u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F (D.omega u).character s) →
        ∀ s : ℂ, 4 / 5 ≤ s.re → s.re ≤ 4 → |s.im| ≤ 5 * U ^ ρ →
          ‖g s‖ ≤ C * U ^ K := by
  classical
  have hF : NumberField.IsTotallyComplex F :=
    primitive12_totallyComplex F D.recipe.A.zeta12 D.recipe.A.primitive_zeta12
  obtain ⟨A_F, hA0, hconv⟩ := convex_normalized F hF
  obtain ⟨C1, hC1, hnorm⟩ := hconv (1 / 100) (by norm_num) (by norm_num)
  obtain ⟨Cc, hCc, hcb⟩ := ConvexBridge.conductor_bound' D
  obtain ⟨E, hE, hlog⟩ := euler_log_facts F
  have hCtot : 0 < C1 * (2 * Cc) * 7 ^ A_F + Real.exp E :=
    add_pos (mul_pos (mul_pos hC1 (mul_pos (by norm_num) hCc)) (by positivity)) (Real.exp_pos E)
  refine ⟨C1 * (2 * Cc) * 7 ^ A_F + Real.exp E, 1 + ρ * A_F, hCtot,
    by have := mul_nonneg hρ.le hA0; linarith, ?_⟩
  intro u hu U hU2 hUq hUq2 g hg hgs s hs1 hs2 hsim
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hq1 : 1 ≤ D.q u := (by norm_num : (1:ℝ) ≤ 2).trans (hU2.trans hUq)
  have hKU : 1 ≤ U ^ (1 + ρ * A_F) := Real.one_le_rpow hU1 (by have := mul_nonneg hρ.le hA0; linarith)
  have hKnn : 0 ≤ U ^ (1 + ρ * A_F) := Real.rpow_nonneg hU0.le _
  by_cases hσ : s.re ≤ 1 + 1 / 100
  ·
    have hnpO : ¬ (D.omega u).character.IsPrincipal :=
      (RowNonprincipal.inducers_nonprincipal D u hu).2
    have hpos : 0 < s.re := by linarith
    have hg_eq : g s = nonprincipalHeckeEntireContinuation F (D.omega u).conductor
        (D.omega u).character (RowHeckeBridge.heckeOmega D u hnpO) s :=
      (RowHeckeBridge.entire_eq_heckeOmega D u hnpO hg hgs s hpos).trans
        (nonprincipalHeckeEntireContinuation_eq F hF (D.omega u).conductor
          (D.omega u).conductor_ne_zero (D.omega u).character
          (RowHeckeBridge.heckeOmega D u hnpO) s hpos).symm
    have hNb := hnorm (D.omega u).conductor (D.omega u).conductor_ne_zero
      (D.omega u).character (D.omega u).primitive hnpO
      (RowHeckeBridge.heckeOmega D u hnpO) s (by linarith) hσ
    have hcb2 : 1 + (Ideal.absNorm (D.omega u).conductor : ℝ) ≤ Cc * D.q u := (hcb u hq1).2
    have hQ1 : 1 ≤ 1 + (Ideal.absNorm (D.omega u).conductor : ℝ) := by
      have : (0 : ℝ) ≤ (Ideal.absNorm (D.omega u).conductor : ℝ) := by positivity
      linarith
    have he1 : (1 + 1 / 100 - s.re) / 2 ≤ 1 := by linarith
    have hQpow : (1 + (Ideal.absNorm (D.omega u).conductor : ℝ)) ^ ((1 + 1 / 100 - s.re) / 2)
        ≤ 2 * Cc * U := by
      calc (1 + (Ideal.absNorm (D.omega u).conductor : ℝ)) ^ ((1 + 1 / 100 - s.re) / 2)
          ≤ (1 + (Ideal.absNorm (D.omega u).conductor : ℝ)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hQ1 he1
        _ = 1 + (Ideal.absNorm (D.omega u).conductor : ℝ) := Real.rpow_one _
        _ ≤ Cc * D.q u := hcb2
        _ ≤ Cc * (2 * U) := mul_le_mul_of_nonneg_left hUq2.le hCc.le
        _ = 2 * Cc * U := by ring
    have hYpow : (2 + |s.im|) ^ A_F ≤ 7 ^ A_F * U ^ (ρ * A_F) := by
      have h1 : 2 + |s.im| ≤ 7 * U ^ ρ := by
        have := Real.one_le_rpow hU1 hρ.le
        linarith
      calc (2 + |s.im|) ^ A_F ≤ (7 * U ^ ρ) ^ A_F :=
            Real.rpow_le_rpow (by positivity) h1 hA0
        _ = 7 ^ A_F * U ^ (ρ * A_F) := by
            rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hU0.le _), ← Real.rpow_mul hU0.le]
    have hY : (0 : ℝ) ≤ (2 + |s.im|) ^ A_F := by positivity
    have hfin : ‖g s‖ ≤ (C1 * (2 * Cc) * 7 ^ A_F) * U ^ (1 + ρ * A_F) := by
      rw [hg_eq]
      refine le_trans hNb (le_trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hQpow hC1.le) hYpow hY
          (mul_nonneg hC1.le (mul_nonneg (mul_nonneg (by norm_num) hCc.le) hU0.le))) (le_of_eq ?_))
      rw [Real.rpow_add hU0, Real.rpow_one]
      ring
    have hC0 : 0 ≤ C1 * (2 * Cc) * 7 ^ A_F := by
      have := mul_pos hC1 (mul_pos (by norm_num : (0:ℝ) < 2) hCc)
      positivity
    calc ‖g s‖ ≤ (C1 * (2 * Cc) * 7 ^ A_F) * U ^ (1 + ρ * A_F) := hfin
      _ ≤ (C1 * (2 * Cc) * 7 ^ A_F + Real.exp E) * U ^ (1 + ρ * A_F) :=
          mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos E]) hKnn
  ·
    have hs' : 1 < s.re := by linarith
    have hexp := (hlog (D.omega u)).2.1 s hs'
    have hbd := (hlog (D.omega u)).2.2 s (by linarith)
    have key : ∀ z : ℂ, ‖z‖ ≤ E → ‖Complex.exp z‖ ≤ Real.exp E := fun z hz => by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr ((Complex.re_le_norm z).trans hz)
    have hleE : Real.exp E ≤ C1 * (2 * Cc) * 7 ^ A_F + Real.exp E := by
      have h7 : (0 : ℝ) < 7 ^ A_F := by positivity
      have := mul_pos (mul_pos hC1 (mul_pos (by norm_num : (0:ℝ) < 2) hCc)) h7
      linarith
    have h2 : ‖g s‖ ≤ Real.exp E := by
      rw [hgs s hs', ← hexp]
      exact key _ hbd
    calc ‖g s‖ ≤ Real.exp E := h2
      _ ≤ Real.exp E * U ^ (1 + ρ * A_F) := le_mul_of_one_le_right (Real.exp_pos E).le hKU
      _ ≤ (C1 * (2 * Cc) * 7 ^ A_F + Real.exp E) * U ^ (1 + ρ * A_F) :=
          mul_le_mul_of_nonneg_right hleE hKnn

open DedekindZetaZeroFree.Quantitative.DetectorDef in

theorem mem_exceptionalSet_of_zero (ρ U : ℝ) (u : D.Row) (hu1 : u.u ≠ 1)
    (hUq : U ≤ D.q u) (hUq2 : D.q u < 2 * U) (s : ℂ) (hs : IsLZero (D.omega u) s)
    (h1 : σ₀ ≤ s.re) (h2 : |s.im| ≤ 4 * U ^ ρ) : u ∈ exceptionalSet D ρ U :=
  ⟨hu1, hUq, hUq2, s, hs, h1, h2⟩

end DedekindZetaZeroFree.Quantitative.ReciprocalLogDiskAux
