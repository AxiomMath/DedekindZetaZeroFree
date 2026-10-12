module

public import DedekindZetaZeroFree.LFunctions.Hecke.NonprincipalRayContinuation
public import DedekindZetaZeroFree.LFunctions.Hecke.ExteriorIdealEulerProducts

@[expose] public section

namespace DedekindZetaZeroFree.HeckeLogProof
noncomputable section
open scoped NumberField Classical
open ExteriorIdealEuler
variable {F : Type} [Field F] [NumberField F]

private theorem primeTerm_bound {cS : Ideal (𝓞 F)}
    (a : ExteriorIdeal cS → ℂ) (ha : IsCoefficient a)
    (σ : ℝ) (hσ : 1 < σ) (s : ℂ) (hs : σ ≤ s.re) (p : PrimeIndex cS) :
    ‖primeTerm a s p‖ ≤ (idealNorm p.val.val) ^ (-σ) ∧
      (idealNorm p.val.val) ^ (-σ) ≤ 1 / 2 := by
  have hq : 2 ≤ idealNorm p.val.val := idealNorm_prime_ge_two _ p.property
  have hq0 : 0 < idealNorm p.val.val := by linarith
  have hq1 : 1 ≤ idealNorm p.val.val := by linarith
  constructor
  · unfold primeTerm summand
    rw [norm_mul]
    have hc : (Ideal.absNorm p.val.val : ℂ) = (idealNorm p.val.val : ℂ) := by simp [idealNorm]
    rw [hc, Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re]
    calc
      ‖a p.val‖ * (Ideal.absNorm p.val.val : ℝ) ^ (-s.re) ≤
          1 * (idealNorm p.val.val) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (ha.norm_le_one _) (Real.rpow_nonneg hq0.le _)
      _ ≤ (idealNorm p.val.val) ^ (-σ) := by
        simpa using Real.rpow_le_rpow_of_exponent_le hq1 (neg_le_neg hs)
  · calc
      (idealNorm p.val.val) ^ (-σ) ≤ (idealNorm p.val.val) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      _ = (idealNorm p.val.val)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hq

private theorem primeLog_bound {cS : Ideal (𝓞 F)}
    (a : ExteriorIdeal cS → ℂ) (ha : IsCoefficient a)
    (σ : ℝ) (hσ : 1 < σ) (s : ℂ) (hs : σ ≤ s.re) (p : PrimeIndex cS) :
    ‖-Complex.log (1 - primeTerm a s p)‖ ≤
      (3 / 2 : ℝ) * (idealNorm p.val.val) ^ (-σ) := by
  have h := primeTerm_bound a ha σ hσ s hs p
  rw [norm_neg]
  have hb := Complex.norm_log_one_add_half_le_self (z := -primeTerm a s p) (by simpa using h.1.trans h.2)
  simp only [norm_neg, ← sub_eq_add_neg] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left h.1 (by norm_num))

 def primeToNonzero {cS : Ideal (𝓞 F)} (p : PrimeIndex cS) : NonzeroIdeal F :=
  ⟨p.val.val, p.val.property.1⟩

private theorem primeToNonzero_injective {cS : Ideal (𝓞 F)} :
    Function.Injective (primeToNonzero (F := F) (cS := cS)) := by
  intro p q h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : NonzeroIdeal F => z.val) h

private theorem primeMajorant_summable {cS : Ideal (𝓞 F)} (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun p : PrimeIndex cS => (3 / 2 : ℝ) * (idealNorm p.val.val) ^ (-σ)) := by
  exact ((ideal_norm_rpow_summable F σ hσ).comp_injective primeToNonzero_injective).mul_left _

private theorem primeLog_summable_norm {cS : Ideal (𝓞 F)}
    (a : ExteriorIdeal cS → ℂ) (ha : IsCoefficient a)
    (σ : ℝ) (hσ : 1 < σ) (s : ℂ) (hs : σ ≤ s.re) :
    Summable (fun p : PrimeIndex cS => ‖-Complex.log (1 - primeTerm a s p)‖) := by
  exact (primeMajorant_summable σ hσ).of_nonneg_of_le (fun _ => norm_nonneg _) (primeLog_bound a ha σ hσ s hs)

private theorem primeTerm_differentiable {cS : Ideal (𝓞 F)}
    (a : ExteriorIdeal cS → ℂ) (p : PrimeIndex cS) :
    Differentiable ℂ (fun s => primeTerm a s p) := by
  have hn : (Ideal.absNorm p.val.val : ℂ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr p.val.property.1)
  exact ((differentiable_id (𝕜 := ℂ)).neg.const_cpow (Or.inl hn)).const_mul (a p.val)

private theorem primeLog_differentiable {cS : Ideal (𝓞 F)}
    (a : ExteriorIdeal cS → ℂ) (ha : IsCoefficient a) (σ : ℝ) (hσ : 1 < σ)
    (p : PrimeIndex cS) :
    DifferentiableOn ℂ (fun s => -Complex.log (1 - primeTerm a s p)) {s : ℂ | σ < s.re} := by
  apply DifferentiableOn.neg
  apply ((primeTerm_differentiable a p).differentiableOn.const_sub 1).clog
  intro s hs
  have h := primeTerm_bound a ha σ hσ s hs.le p
  have hb : ‖-primeTerm a s p‖ < 1 := by rw [norm_neg]; linarith [h.1.trans h.2]
  simpa only [← sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hb

def eulerLog {cS : Ideal (𝓞 F)} (a : ExteriorIdeal cS → ℂ) (s : ℂ) : ℂ :=
  ∑' p : PrimeIndex cS, -Complex.log (1 - primeTerm a s p)

theorem eulerLog_differentiableOn {cS : Ideal (𝓞 F)}
    (a : ExteriorIdeal cS → ℂ) (ha : IsCoefficient a) :
    DifferentiableOn ℂ (eulerLog a) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  let σ := (1 + s.re) / 2
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hsσ : σ < s.re := by dsimp [σ]; linarith
  have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (eulerLog a) {s : ℂ | σ < s.re} :=
    Complex.differentiableOn_tsum_of_summable_norm (primeMajorant_summable σ hσ)
      (primeLog_differentiable a ha σ hσ) hopen
      (fun p z hz => primeLog_bound a ha σ hσ z hz.le p)
  exact (hd.differentiableAt (hopen.mem_nhds hsσ)).differentiableWithinAt

theorem eulerLog_norm_le {cS : Ideal (𝓞 F)}
    (a : ExteriorIdeal cS → ℂ) (ha : IsCoefficient a)
    (σ : ℝ) (hσ : 1 < σ) (s : ℂ) (hs : σ ≤ s.re) :
    ‖eulerLog a s‖ ≤ (3 / 2 : ℝ) * ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-σ) := by
  have hmaj := primeMajorant_summable (cS := cS) σ hσ
  have hn := primeLog_summable_norm a ha σ hσ s hs
  apply (norm_tsum_le_tsum_norm hn).trans
  apply (hn.tsum_le_tsum (primeLog_bound a ha σ hσ s hs) hmaj).trans
  rw [← tsum_mul_left]
  exact hmaj.tsum_le_tsum_of_inj primeToNonzero primeToNonzero_injective
    (fun I _ => mul_nonneg (by norm_num) (Real.rpow_nonneg (by dsimp [idealNorm]; positivity) _)) (fun _ => le_rfl)
    ((ideal_norm_rpow_summable F σ hσ).mul_left _)

theorem exp_eulerLog {cS : Ideal (𝓞 F)}
    (a : ExteriorIdeal cS → ℂ) (ha : IsCoefficient a) (s : ℂ) (hs : 1 < s.re) :
    Complex.exp (eulerLog a s) = ∑' I : ExteriorIdeal cS, summand a s I := by
  have hn := primeLog_summable_norm a ha s.re hs s le_rfl
  have hp := hn.of_norm.hasSum.cexp
  have hlocal : ∀ p : PrimeIndex cS,
      Complex.exp (-Complex.log (1 - primeTerm a s p)) = factor a s p := by
    intro p
    have h := primeTerm_bound a ha s.re hs s le_rfl p
    have hne : 1 - primeTerm a s p ≠ 0 := by
      intro hz
      have : primeTerm a s p = 1 := (sub_eq_zero.mp hz).symm
      rw [this, norm_one] at h
      linarith [h.1.trans h.2]
    rw [Complex.exp_neg, Complex.exp_log hne]
    rfl
  have hp' : HasProd (factor a s) (Complex.exp (eulerLog a s)) := by
    convert hp using 1
    · ext p
      exact (hlocal p).symm
    · rfl
  exact hp'.unique (exterior_ideal_euler a ha s hs).2.1

theorem ray_isCoefficient (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (ω : RayClassCharacter F 𝔪) :
    IsCoefficient (fun I : ExteriorIdeal (⊤ : Ideal (𝓞 F)) => ω I.val) := by
  constructor
  · exact ω.map_top'
  · intro I J _
    exact ω.map_mul' I.val J.val
  · intro I
    exact RayUnitary.ray_character_norm_le_one F 𝔪 h𝔪 ω I.val
  · intro p k
    change ω (p.val.val ^ k) = ω p.val.val ^ k
    induction k with
    | zero => simpa using ω.map_top'
    | succ k ih => rw [pow_succ, ω.map_mul', ih, pow_succ]

theorem ray_exp_eulerLog (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (ω : RayClassCharacter F 𝔪)
    (D : NonprincipalRayHeckeData F 𝔪 ω) (s : ℂ) (hs : 1 < s.re) :
    Complex.exp (eulerLog (fun I : ExteriorIdeal (⊤ : Ideal (𝓞 F)) => ω I.val) s) = D.L s := by
  rw [exp_eulerLog _ (ray_isCoefficient 𝔪 h𝔪 ω) s hs]
  have hsupport : Function.support (fun I : Ideal (𝓞 F) => ω I * (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
      {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ ⊤ = ⊤} := by
    intro I hI
    simp only [Function.mem_support] at hI
    refine ⟨?_, by simp⟩
    intro hzero
    have hω : ω I = 0 := (ω.eq_zero_iff' I).mpr (Or.inl hzero)
    exact hI (by rw [hω, zero_mul])
  have hsum := (hasSum_subtype_iff_of_support_subset hsupport).mpr (D.series s hs)
  exact hsum.tsum_eq

end
end DedekindZetaZeroFree.HeckeLogProof
