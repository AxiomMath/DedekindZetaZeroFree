module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.Divisors.IdealDivisorBins
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Errors.LargeDirectRectangles

@[expose] public section

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/
noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirect.Geometry
open ErrorRectangles
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def admissibleRectangles (C : Context Q) (B : ℝ) : Finset (ℝ × ℝ) :=
  (ErrorRectangles.rectangles C).filter (fun P =>
    (ErrorRectangles.lowerConstant c / 2) * Real.sqrt (C.M / B) *
      Real.rpow (C.M * C.N) (-C.δ) / norm C.d ≤ P.1 * P.2)

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirect.Geometry

end

end

section
noncomputable section
open scoped NumberField Classical ContDiff
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirectKernelUniformity
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
private lemma square_source_smooth (W : ℝ → ℝ) (hW : Sieve.SieveWeight W) :
    ContDiff ℝ ∞ (fun x : ℝ => (W (x ^ 2) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hW.smooth.comp (contDiff_id.pow 2))
private lemma square_source_support (W : ℝ → ℝ) (hW : Sieve.SieveWeight W) :
    Function.support (fun x : ℝ => (W (x ^ 2) : ℂ)) ⊆ Set.Icc (-2 : ℝ) 2 := by
  intro x hx
  have hs : x ^ 2 ∈ Set.Icc (1 / 2 : ℝ) (5 / 2) := by
    by_contra hs
    exact hx (by simp [hW.zero_outside _ hs])
  constructor <;> nlinarith [hs.2]
theorem originalKernelUniform
    (hF : NumberField.IsTotallyComplex F) (W : ℝ → ℝ) (hW : Sieve.SieveWeight W) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : Context Q, C.W = W →
      ∀ R x : ℝ, 1 ≤ R → 0 < x → R⁻¹ ≤ x →
        ‖C.originalKernel x‖ ≤ A * R := by
  let h : ℝ → ℂ := fun x => (W (x ^ 2) : ℂ)
  have hh : ContDiff ℝ ∞ h := square_source_smooth W hW
  have hs := square_source_support W hW
  have hc : HasCompactSupport h :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs
  have hb : Vendor.PositiveSideSupport 2 h := by
    intro x hx
    by_contra hn
    have hxmem := hs hn
    exact (not_le_of_gt hx) hxmem.2
  obtain ⟨N, A₀, hA₀, hbound⟩ := fieldTransform_uniform_euler_two_ended_bound
    (principalDiscriminant F) (principalComplexPlaces F) 2 0 0 1
    (principalDiscriminant_pos F) (principalComplexPlaces_pos F hF)
    (by norm_num) (by norm_num)
  have hS : 0 ≤ Vendor.S 2 N h := Vendor.S_nonneg 2 (by norm_num) N h hh
  let A := A₀ * Vendor.S 2 N h + 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro C hCW R x hR hx hxR
  have hk : C.originalKernel = fieldTransform (principalDiscriminant F)
      (principalComplexPlaces F) h := by
    funext y
    simp [Context.originalKernel, Context.source, h, hCW]
  rw [hk]
  have hR0 : 0 < R := by linarith
  have hcoeff : A₀ * Vendor.S 2 N h ≤ A := by dsimp [A]; linarith
  have hbounds := hbound h hh hc hb
  by_cases hx1 : x ≤ 1
  · have hinv : x⁻¹ ≤ R := by
      simpa only [inv_inv] using (inv_le_inv₀ hx (inv_pos.mpr hR0)).mpr hxR
    have hh := hbounds.1 x hx hx1
    norm_num [Vendor.EulerIter_zero, Real.rpow_neg_one] at hh
    calc
      _ ≤ A₀ * Vendor.S 2 N h * x⁻¹ := hh
      _ ≤ A * R := mul_le_mul hcoeff hinv (inv_nonneg.mpr hx.le) hA.le
  · have hh := hbounds.2 x (le_of_not_ge hx1)
    norm_num [Vendor.EulerIter_zero, Real.rpow_zero] at hh
    exact hh.trans (hcoeff.trans (le_mul_of_one_le_right hA.le hR))
theorem originalKernel_middle_uniform
    (hF : NumberField.IsTotallyComplex F) (W : ℝ → ℝ) (hW : Sieve.SieveWeight W) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : Context Q, C.W = W →
      ∀ B : ℝ, 1 ≤ C.M → 1 ≤ C.N → 0 < C.δ → 1 ≤ B →
      ∀ a f b : Ideal (𝓞 F), 0 < norm a → norm a ≤ 2 * B →
        0 < norm f → norm f ≤ C.Z2 B → 1 ≤ norm b →
        ‖C.originalKernel (norm b * Real.sqrt (C.M / norm a) / norm f)‖ ≤
          A * Real.rpow (C.M * C.N) C.δ := by
  obtain ⟨A, hA, hbound⟩ := originalKernelUniform (Q := Q) hF W hW
  refine ⟨2 * A, by positivity, ?_⟩
  intro C hCW B hM hN hδ hB a f b ha0 ha hf0 hf hb
  have hM0 : 0 < C.M := by linarith
  have hB0 : 0 < B := by linarith
  have hb0 : 0 < norm b := by linarith
  have hMN : 1 ≤ C.M * C.N := by nlinarith
  let p := Real.rpow (C.M * C.N) C.δ
  have hp : 1 ≤ p := Real.one_le_rpow hMN hδ.le
  have hp0 : 0 < p := by linarith
  let T := Real.sqrt (C.M / norm a)
  have hT0 : 0 < T := Real.sqrt_pos.mpr (div_pos hM0 ha0)
  have hrad : C.M / B ≤ 4 * (C.M / norm a) := by
    rw [div_le_iff₀ hB0]
    have heq : 4 * (C.M / norm a) * B = (4 * C.M * B) / norm a := by ring
    rw [heq, le_div_iff₀ ha0]
    nlinarith
  have hT : Real.sqrt (C.M / B) ≤ 2 * T := by
    have hh := Real.sqrt_le_sqrt hrad
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hh
    norm_num [T] at hh ⊢
    exact hh
  have hfT : norm f ≤ 2 * T * p := by
    change norm f ≤ Real.sqrt (C.M / B) * p at hf
    exact hf.trans (mul_le_mul_of_nonneg_right hT hp0.le)
  have hx : 0 < norm b * T / norm f := div_pos (mul_pos hb0 hT0) hf0
  have hxR : (2 * p)⁻¹ ≤ norm b * T / norm f := by
    rw [← one_div]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * p) hf0).mpr
    have hbT : T ≤ norm b * T := le_mul_of_one_le_left hT0.le hb
    nlinarith
  have hh := hbound C hCW (2 * p) (norm b * T / norm f) (by linarith) hx hxR
  calc
    _ ≤ A * (2 * p) := hh
    _ = (2 * A) * Real.rpow (C.M * C.N) C.δ := by dsimp [p]; ring
end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirectKernelUniformity

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirectKernelUniformity

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

theorem finiteDualKernel_uniform
    (hF : NumberField.IsTotallyComplex F) (W : ℝ → ℝ) (hW : Sieve.SieveWeight W) :
    ∃ J : ℝ, 0 < J ∧ ∀ C : Context Q, C.W = W →
      ∀ B : ℝ, 1 ≤ C.M → 1 ≤ C.N → 0 < C.δ → 1 ≤ B →
      ∀ a f : Ideal (𝓞 F), 0 < norm a → norm a ≤ 2 * B →
        0 < norm f → norm f ≤ C.Z2 B →
        ‖∑ b ∈ (boundedNormIdeals F C.L2).filter (fun b => b ≠ ⊥),
          C.originalKernel (norm b * Real.sqrt (C.M / norm a) / norm f)‖ ≤
            J * Real.rpow (C.M * C.N) (3 * C.δ) := by
  obtain ⟨A, hA, hk⟩ := originalKernel_middle_uniform (Q := Q) hF W hW
  obtain ⟨I, hI, hc⟩ := exists_ideal_count_bound F
  refine ⟨8 * I * A, by positivity, ?_⟩
  intro C hCW B hM hN hδ hB a f ha0 ha hf0 hf
  have hMN : 1 ≤ C.M * C.N := one_le_mul_of_one_le_of_one_le hM hN
  have hMN0 : 0 < C.M * C.N := by linarith
  have hp2 : 1 ≤ Real.rpow (C.M * C.N) (2 * C.δ) :=
    Real.one_le_rpow hMN (by positivity)
  have hL : 1 ≤ C.L2 := by
    change 1 ≤ 8 * Real.rpow (C.M * C.N) (2 * C.δ)
    linarith
  let S := (boundedNormIdeals F C.L2).filter (fun b => b ≠ ⊥)
  have hcard : (S.card : ℝ) ≤ I * C.L2 := by
    exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (hc C.L2 hL)
  have hterm : ∀ b ∈ S,
      ‖C.originalKernel (norm b * Real.sqrt (C.M / norm a) / norm f)‖ ≤
        A * Real.rpow (C.M * C.N) C.δ := by
    intro b hb
    have hb0 : b ≠ ⊥ := (Finset.mem_filter.mp hb).2
    have hbn : 1 ≤ norm b := by
      unfold norm
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hb0)
    exact hk C hCW B hM hN hδ hB a f b ha0 ha hf0 hf hbn
  calc
    _ ≤ ∑ b ∈ S, ‖C.originalKernel (norm b * Real.sqrt (C.M / norm a) / norm f)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ b ∈ S, A * Real.rpow (C.M * C.N) C.δ := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (A * Real.rpow (C.M * C.N) C.δ) := by simp
    _ ≤ (I * C.L2) * (A * Real.rpow (C.M * C.N) C.δ) :=
      mul_le_mul_of_nonneg_right hcard
        (mul_nonneg hA.le (Real.rpow_nonneg hMN0.le _))
    _ = (8 * I * A) * Real.rpow (C.M * C.N) (3 * C.δ) := by
      change (I * (8 * (C.M * C.N) ^ (2 * C.δ))) *
        (A * (C.M * C.N) ^ C.δ) = (8 * I * A) * (C.M * C.N) ^ (3 * C.δ)
      rw [show (3 * C.δ) = 2 * C.δ + C.δ by ring, Real.rpow_add hMN0]
      ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirectKernelUniformity

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirectKernelUniformity

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

theorem prefactored_finiteDualKernel_uniform
    (hF : NumberField.IsTotallyComplex F) (W : ℝ → ℝ) (hW : Sieve.SieveWeight W) :
    ∃ J : ℝ, 0 < J ∧ ∀ C : Context Q, C.W = W →
      ∀ B : ℝ, 1 ≤ C.M → 1 ≤ C.N → 0 < C.δ → 1 ≤ B →
      ∀ a f : Ideal (𝓞 F), B ≤ norm a → norm a ≤ 2 * B →
        0 < norm f → norm f ≤ C.Z2 B →
        Real.sqrt (C.M / norm a) / norm f *
          ‖∑ b ∈ (boundedNormIdeals F C.L2).filter (fun b => b ≠ ⊥),
            C.originalKernel (norm b * Real.sqrt (C.M / norm a) / norm f)‖ ≤
          J * Real.rpow (C.M * C.N) (3 * C.δ) * Real.sqrt (C.M / B) / norm f := by
  obtain ⟨J, hJ, hbound⟩ := finiteDualKernel_uniform (Q := Q) hF W hW
  refine ⟨J, hJ, ?_⟩
  intro C hCW B hM hN hδ hB a f hBa ha hf0 hf
  have hB0 : 0 < B := by linarith
  have ha0 : 0 < norm a := lt_of_lt_of_le hB0 hBa
  have hM0 : 0 ≤ C.M := by linarith
  have hsqrt : Real.sqrt (C.M / norm a) ≤ Real.sqrt (C.M / B) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left hM0 hB0 hBa
  have hkernel := hbound C hCW B hM hN hδ hB a f ha0 ha hf0 hf
  have hscale : 0 ≤ J * Real.rpow (C.M * C.N) (3 * C.δ) := by
    exact mul_nonneg hJ.le (Real.rpow_nonneg (by positivity) _)
  have hleft : 0 ≤ Real.sqrt (C.M / norm a) / norm f := by positivity
  calc
    _ ≤ (Real.sqrt (C.M / norm a) / norm f) *
          (J * Real.rpow (C.M * C.N) (3 * C.δ)) :=
      mul_le_mul_of_nonneg_left hkernel hleft
    _ ≤ (Real.sqrt (C.M / B) / norm f) *
          (J * Real.rpow (C.M * C.N) (3 * C.δ)) := by
      apply mul_le_mul_of_nonneg_right _ hscale
      exact div_le_div_of_nonneg_right hsqrt hf0.le
    _ = J * Real.rpow (C.M * C.N) (3 * C.δ) * Real.sqrt (C.M / B) /
        norm f := by ring

def rowKernel (C : Context Q) (a f : Ideal (𝓞 F)) : ℂ :=
  (UniqueFactorizationMonoid.moebius f : ℂ) *
    (Real.sqrt (C.M / norm a) / norm f : ℂ) *
      ∑ b ∈ (boundedNormIdeals F C.L2).filter (fun b => b ≠ ⊥),
        C.originalKernel (norm b * Real.sqrt (C.M / norm a) / norm f)

theorem rowKernel_uniform
    (hF : NumberField.IsTotallyComplex F) (W : ℝ → ℝ) (hW : Sieve.SieveWeight W) :
    ∃ J : ℝ, 0 < J ∧ ∀ C : Context Q, C.W = W →
      ∀ (B : ℝ) (unit : Bool), (unit = true → B = 1) →
        1 ≤ C.M → 1 ≤ C.N → 0 < C.δ → 1 ≤ B →
      ∀ a ∈ C.originalRows B unit, ∀ f : Ideal (𝓞 F),
        0 < norm f → norm f ≤ C.Z2 B →
        ‖rowKernel C a f‖ ≤
          J * Real.rpow (C.M * C.N) (3 * C.δ) * Real.sqrt (C.M / B) / norm f := by
  obtain ⟨J, hJ, hbound⟩ := prefactored_finiteDualKernel_uniform (Q := Q) hF W hW
  refine ⟨J, hJ, ?_⟩
  intro C hCW B unit hunit hM hN hδ hB a ha f hf0 hf
  have hBa : B ≤ norm a ∧ norm a ≤ 2 * B := by
    cases unit
    · have hn := (Sieve.mem_paperShell F (c * C.d) B a).mp
        (Finset.mem_filter.mp ha).1
      exact ⟨hn.2.2.1.le, hn.2.2.2⟩
    · have ha' : a = ⊤ := Finset.mem_singleton.mp (Finset.mem_filter.mp ha).1
      subst a
      simp [norm, hunit rfl]
  have hmoebius : ‖(UniqueFactorizationMonoid.moebius f : ℂ)‖ ≤ 1 := by
    rw [UniqueFactorizationMonoid.moebius]
    split_ifs
    · rw [Int.cast_pow, Int.cast_neg, Int.cast_one, norm_pow, norm_neg, norm_one, one_pow]
    · simp
  have hfrac : 0 ≤ Real.sqrt (C.M / norm a) / norm f := by positivity
  have hnorm : ‖(Real.sqrt (C.M / norm a) / norm f : ℂ)‖ =
      Real.sqrt (C.M / norm a) / norm f := by
    rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_of_nonneg hfrac]
  unfold rowKernel
  rw [norm_mul, norm_mul, hnorm]
  calc
    _ ≤ 1 * (Real.sqrt (C.M / norm a) / norm f) *
          ‖∑ b ∈ (boundedNormIdeals F C.L2).filter (fun b => b ≠ ⊥),
            C.originalKernel (norm b * Real.sqrt (C.M / norm a) / norm f)‖ := by
      gcongr
    _ ≤ _ := by
      rw [one_mul]
      exact hbound C hCW B hM hN hδ hB a f hBa.1 hBa.2 hf0 hf

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirectKernelUniformity

end

end

section
noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirectWindow
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private lemma rel {a b : Ideal (𝓞 F)} (h : a ⊔ b = ⊤) : IsRelPrime a b := by
  intro z hza hzb
  rw [Ideal.isUnit_iff]
  exact le_antisymm le_top (h ▸ sup_le (Ideal.dvd_iff_le.mp hza) (Ideal.dvd_iff_le.mp hzb))

theorem moebius_triple (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F))
    (hp : C.ValidPair p) (K : Ideal (𝓞 F) → ℂ) :
    (∑ f ∈ idealDivisors ((c * C.d) * (p.1 * p.2)),
      (UniqueFactorizationMonoid.moebius f : ℂ) * K f) =
      ∑ e ∈ C.mobiusDivisors, ∑ f₁ ∈ idealDivisors p.1, ∑ f₂ ∈ idealDivisors p.2,
        (UniqueFactorizationMonoid.moebius (e * (f₁ * f₂)) : ℂ) * K (e * (f₁ * f₂)) := by
  open UniqueFactorizationMonoid in
  have hcd0 : c * C.d ≠ ⊥ := mul_ne_zero C.D.original_ne_bot C.hd0
  have huv0 : p.1 * p.2 ≠ ⊥ := mul_ne_zero hp.hu0 hp.hv0
  have hcuv : c ⊔ (p.1 * p.2) = ⊤ := by
    rw [Ideal.sup_mul_eq_of_coprime_left (by simpa [sup_comm] using hp.huc)]
    simpa [sup_comm] using hp.hvc
  have hfixed : (c * C.d) ⊔ (p.1 * p.2) = ⊤ := by
    rw [sup_comm, Ideal.sup_mul_eq_of_coprime_left (by simpa [sup_comm] using hcuv)]
    simpa [sup_comm] using hp.hduv
  rw [LargeDirectDictionary.sum_divisors_mul _ _ hcd0 huv0 hfixed]
  simp_rw [LargeDirectDictionary.sum_divisors_mul _ _ hp.hu0 hp.hv0 hp.huv]
  have hfrel : ∀ e ∈ idealDivisors (c * C.d), ∀ f₁ ∈ idealDivisors p.1,
      ∀ f₂ ∈ idealDivisors p.2,
      UniqueFactorizationMonoid.moebius (e * (f₁ * f₂)) =
        UniqueFactorizationMonoid.moebius e * UniqueFactorizationMonoid.moebius (f₁ * f₂) := by
    intro e he f₁ hf₁ f₂ hf₂
    exact ((rel hfixed).of_dvd_left ((mem_idealDivisors hcd0).mp he) |>.of_dvd_right
      (mul_dvd_mul ((mem_idealDivisors hp.hu0).mp hf₁)
        ((mem_idealDivisors hp.hv0).mp hf₂))).moebius_mul
  have hterm : ∀ e ∈ idealDivisors (c * C.d),
      (∑ f₁ ∈ idealDivisors p.1, ∑ f₂ ∈ idealDivisors p.2,
        (UniqueFactorizationMonoid.moebius (e * (f₁ * f₂)) : ℂ) * K (e * (f₁ * f₂))) =
      (UniqueFactorizationMonoid.moebius e : ℂ) *
        (∑ f₁ ∈ idealDivisors p.1, ∑ f₂ ∈ idealDivisors p.2,
          (UniqueFactorizationMonoid.moebius (f₁ * f₂) : ℂ) * K (e * (f₁ * f₂))) := by
    intro e he
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f₁ hf₁
    apply Finset.sum_congr rfl
    intro f₂ hf₂
    rw [hfrel e he f₁ hf₁ f₂ hf₂, Int.cast_mul, mul_assoc]
  rw [Finset.sum_congr rfl hterm, LargeDirectDictionary.sum_moebius_radical _ hcd0]
  apply Finset.sum_congr rfl
  intro e he
  have he0 : (c * C.d).radical ≠ ⊥ := by
    intro h
    have := Ideal.le_radical (I := c * C.d)
    rw [h] at this
    exact hcd0 (le_bot_iff.mp this)
  have hedvd : e ∣ c * C.d := ((mem_idealDivisors he0).mp he).trans
    (Ideal.dvd_iff_le.mpr Ideal.le_radical)
  exact (hterm e ((mem_idealDivisors hcd0).mpr hedvd)).symm

theorem middle_triple (C : Context Q) (B : ℝ) (a : Ideal (𝓞 F))
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p) :
    Context.middle C.originalKernel ((c * C.d) * (p.1 * p.2))
      (Real.sqrt (C.M / norm a)) (C.Y2 B) (C.Z2 B) C.L2 =
      ∑ e ∈ C.mobiusDivisors, ∑ f₁ ∈ idealDivisors p.1, ∑ f₂ ∈ idealDivisors p.2,
        if C.Y2 B < norm (e * (f₁ * f₂)) ∧ norm (e * (f₁ * f₂)) ≤ C.Z2 B then
          MiddleDirectKernelUniformity.rowKernel C a (e * (f₁ * f₂)) else 0 := by
  unfold Context.middle MiddleDirectKernelUniformity.rowKernel
  rw [Finset.sum_filter]
  have h := moebius_triple C p hp (fun f =>
    if C.Y2 B < norm f ∧ norm f ≤ C.Z2 B then
      (Real.sqrt (C.M / norm a) / norm f : ℂ) *
        ∑ b ∈ (boundedNormIdeals F C.L2).filter (fun b => b ≠ ⊥),
          C.originalKernel (norm b * Real.sqrt (C.M / norm a) / norm f)
    else 0)
  simp only [mul_ite, mul_zero, mul_assoc] at h ⊢
  exact h

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirectWindow

end

end

section
noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirectWindow
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private lemma norm_mul (a b : Ideal (𝓞 F)) : norm (a*b) = norm a * norm b := by
  simp [norm, map_mul]
private lemma norm_le_of_dvd {a b : Ideal (𝓞 F)} (hb : b ≠ ⊥) (h : a ∣ b) :
    norm a ≤ norm b := by
  unfold norm
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hb))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp h))

private lemma norm_nonneg (a : Ideal (𝓞 F)) : 0 ≤ norm a := by
  unfold norm; positivity

private lemma bin_admissible (C : Context Q) (B : ℝ)
    (hn : 1 ≤ norm C.d) {e : Ideal (𝓞 F)} (he : e ∈ C.mobiusDivisors)
    {P : ℝ × ℝ} (hrect : P ∈ ErrorRectangles.rectangles C)
    {a b : Ideal (𝓞 F)} (ha : ErrorRectangles.InBin P.1 a)
    (hb : ErrorRectangles.InBin P.2 b) (hl : C.Y2 B < norm (e * (a*b))) :
    P ∈ MiddleDirect.Geometry.admissibleRectangles C B := by
  have hcd0 : c * C.d ≠ ⊥ := mul_ne_zero C.D.original_ne_bot C.hd0
  have hed : e ∣ c * C.d := by
    have hr0 : (c * C.d).radical ≠ ⊥ := by
      intro h
      apply hcd0
      apply bot_unique
      simpa [h] using (Ideal.le_radical : c * C.d ≤ (c * C.d).radical)
    have hd := (mem_idealDivisors hr0).mp he
    exact hd.trans (Ideal.dvd_iff_le.mpr Ideal.le_radical)
  have hen : norm e ≤ norm c * norm C.d := by
    simpa [norm_mul] using norm_le_of_dvd hcd0 hed
  have hP := ErrorRectangles.rectangle_endpoints C P hrect
  have hh : norm (e * (a*b)) ≤ (max 1 (norm c) * norm C.d) * (4 * (P.1*P.2)) := by
    rw [norm_mul, norm_mul]
    have hab : norm a * norm b ≤ (2*P.1)*(2*P.2) :=
      mul_le_mul ha.2.2 hb.2.2 (norm_nonneg b) (by linarith [hP.1])
    calc
      _ ≤ (norm c * norm C.d) * ((2*P.1)*(2*P.2)) :=
        mul_le_mul hen hab (mul_nonneg (norm_nonneg a) (norm_nonneg b))
          (mul_nonneg (norm_nonneg c) (norm_nonneg C.d))
      _ ≤ (max 1 (norm c) * norm C.d) * ((2*P.1)*(2*P.2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right 1 (norm c)) (norm_nonneg C.d))
          (by nlinarith [hP.1, hP.2.1])
      _ = _ := by ring
  apply Finset.mem_filter.mpr
  refine ⟨hrect, ?_⟩
  change (ErrorRectangles.lowerConstant c / 2) * Real.sqrt (C.M / B) *
    Real.rpow (C.M*C.N) (-C.δ) / norm C.d ≤ P.1*P.2
  have hsqrt : Real.sqrt (C.M / B) ≤ 2 * Real.sqrt (C.M / (2 * B)) := by
    have heq : C.M / B = 2 * (C.M / (2 * B)) := by ring
    rw [heq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_right (by norm_num : Real.sqrt 2 ≤ 2) (Real.sqrt_nonneg _)
  have hp0 : 0 ≤ P.1 * P.2 := by nlinarith [hP.1, hP.2.1]
  by_cases hr : 0 ≤ Real.rpow (C.M * C.N) (-C.δ)
  · have hroot : Real.sqrt (C.M / B) * Real.rpow (C.M * C.N) (-C.δ) ≤
        2 * C.Y2 B := by
      unfold Context.Y2
      nlinarith [mul_le_mul_of_nonneg_right hsqrt hr]
    rw [ErrorRectangles.lowerConstant, div_le_iff₀ (by linarith : 0 < norm C.d)]
    have hc4 : 0 < 4 * max 1 (norm c) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hroot
      (show 0 ≤ 1 / (4 * max 1 (norm c)) / 2 by positivity)
    have hdiv : (1 / (4 * max 1 (norm c))) * C.Y2 B ≤ norm C.d * (P.1 * P.2) := by
      rw [one_div_mul_eq_div]
      apply (div_le_iff₀ hc4).mpr
      nlinarith
    nlinarith
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by unfold ErrorRectangles.lowerConstant; positivity)
        (Real.sqrt_nonneg _)) (le_of_not_ge hr)) (by linarith)) hp0

private lemma bucket_bins (C : Context Q) (B : ℝ)
    (hn : 1 ≤ norm C.d) (hnN : norm C.d ≤ 2 * C.N)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : p ∈ C.pairs)
    (e : Ideal (𝓞 F)) (he : e ∈ C.mobiusDivisors)
    (k : Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ)
    (hk : ∀ e a b, ¬(C.Y2 B < norm (e*(a*b)) ∧ norm (e*(a*b)) ≤ C.Z2 B) → k e a b = 0) :
    (∑ a ∈ idealDivisors p.1, ∑ b ∈ idealDivisors p.2, k e a b) =
      ∑ P ∈ MiddleDirect.Geometry.admissibleRectangles C B,
        ∑ a ∈ idealDivisors p.1, ∑ b ∈ idealDivisors p.2,
          if ErrorRectangles.InBin P.1 a ∧ ErrorRectangles.InBin P.2 b then k e a b else 0 := by
  have hpv := (Finset.mem_filter.mp hp).2
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  have had := (mem_idealDivisors hpv.hu0).mp ha
  have hbd := (mem_idealDivisors hpv.hv0).mp hb
  by_cases hl : C.Y2 B < norm (e*(a*b)) ∧ norm (e*(a*b)) ≤ C.Z2 B
  · have hpp := (Finset.mem_filter.mp hp).1
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp hpp
    have huN : norm p.1 ≤ 2*C.N / norm C.d :=
      ((Sieve.mem_idealAdmissibleFinset F c _ _).mp (Finset.mem_filter.mp hu).1).2.2
    have hvN : norm p.2 ≤ 2*C.N / norm C.d :=
      ((Sieve.mem_idealAdmissibleFinset F c _ _).mp (Finset.mem_filter.mp hv).1).2.2
    have hX : 1 ≤ 2*(C.N / norm C.d) := by
      rw [← mul_div_assoc, le_div_iff₀ (by linarith : 0 < norm C.d)]
      simpa using hnN
    obtain ⟨P₁,hP₁s,hP₁,hP₁N,hP₁a⟩ := DivisorBins.bin_exists _ hX a (ne_bot_of_mem_idealDivisors ha)
      ((norm_le_of_dvd hpv.hu0 had).trans (by simpa [mul_div_assoc] using huN))
    obtain ⟨P₂,hP₂s,hP₂,hP₂N,hP₂b⟩ := DivisorBins.bin_exists _ hX b (ne_bot_of_mem_idealDivisors hb)
      ((norm_le_of_dvd hpv.hv0 hbd).trans (by simpa [mul_div_assoc] using hvN))
    have hrect : (P₁,P₂) ∈ ErrorRectangles.rectangles C := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hP₁s,hP₂s⟩,hP₁,hP₂,?_,?_,p,hp,a,b,had,hbd,hP₁a,hP₂b⟩ <;>
        simpa [mul_div_assoc] using (by assumption : _)
    have hAdm := bin_admissible C B hn he hrect hP₁a hP₂b hl.1
    symm
    rw [Finset.sum_eq_single (P₁,P₂)]
    · simp [hP₁a, hP₂b]
    · intro R hR hne
      have hRs := (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
      by_cases hRa : ErrorRectangles.InBin R.1 a
      · by_cases hRb : ErrorRectangles.InBin R.2 b
        · have h1 := DivisorBins.bin_unique hRs.1 hP₁s hRa hP₁a
          have h2 := DivisorBins.bin_unique hRs.2 hP₂s hRb hP₂b
          exact (hne (Prod.ext h1 h2)).elim
        · simp [hRb]
      · simp [hRa]
    · intro hnmem
      exact (hnmem hAdm).elim
  · simp [hk e a b hl]

theorem window_bucket_partition (C : Context Q) (B : ℝ)
    (hN : 1 ≤ C.N) (hn : 1 ≤ norm C.d) (hnN : norm C.d ≤ 2 * C.N)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : p ∈ C.pairs)
    (k : Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ)
    (hk : ∀ e f₁ f₂ : Ideal (𝓞 F),
      ¬(C.Y2 B < norm (e * (f₁ * f₂)) ∧ norm (e * (f₁ * f₂)) ≤ C.Z2 B) →
      k e f₁ f₂ = 0) :
    (∑ e ∈ C.mobiusDivisors, ∑ f₁ ∈ idealDivisors p.1,
      ∑ f₂ ∈ idealDivisors p.2, k e f₁ f₂) =
    ∑ e ∈ C.mobiusDivisors, ∑ P ∈ MiddleDirect.Geometry.admissibleRectangles C B,
      ∑ f₁ ∈ LargeDirect.divisorBin (F := F) P.1,
      ∑ f₂ ∈ LargeDirect.divisorBin (F := F) P.2,
        k e f₁ f₂ * (if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then 1 else 0) := by
  have hpv := (Finset.mem_filter.mp hp).2
  apply Finset.sum_congr rfl
  intro e he
  rw [bucket_bins C B hn hnN p hp e he k hk]
  apply Finset.sum_congr rfl
  intro P hP
  have heq : (∑ a ∈ idealDivisors p.1, ∑ b ∈ idealDivisors p.2,
      if ErrorRectangles.InBin P.1 a ∧ ErrorRectangles.InBin P.2 b then k e a b else 0) =
      ∑ a ∈ idealDivisors p.1, if ErrorRectangles.InBin P.1 a then
        ∑ b ∈ idealDivisors p.2, if ErrorRectangles.InBin P.2 b then k e a b else 0
      else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> simp [*]
  rw [heq, DivisorBins.sum_bin p.1 hpv.hu0]
  apply Finset.sum_congr rfl
  intro a ha
  rw [DivisorBins.sum_bin p.2 hpv.hv0]
  by_cases h1 : a ∣ p.1
  · simp only [if_pos h1]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h2 : b ∣ p.2 <;> simp [h1, h2]
  · simp [h1]

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirectWindow

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirectWindow
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private lemma pairSum_mul (C : Context Q) (z : ℂ)
    (f : (p : Ideal (𝓞 F) × Ideal (𝓞 F)) → C.ValidPair p → ℂ) :
    C.pairSum (fun p hp => z * f p hp) = z * C.pairSum f := by
  unfold Context.pairSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

private lemma pairSum_sum {α : Type*} (C : Context Q) (s : Finset α)
    (f : α → (p : Ideal (𝓞 F) × Ideal (𝓞 F)) → C.ValidPair p → ℂ) :
    C.pairSum (fun p hp => ∑ i ∈ s, f i p hp) =
      ∑ i ∈ s, C.pairSum (f i) := by
  unfold Context.pairSum
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

theorem middle_window_assembly (C : Context Q) (B : ℝ) (unit : Bool)
    (H : ℝ) (hH : 0 ≤ H)
    (w : Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ)
    (hrewrite : ∀ p ∈ C.pairs, ∀ a ∈ C.originalRows B unit,
      Context.middle C.originalKernel ((c * C.d) * (p.1 * p.2))
        (Real.sqrt (C.M / norm a)) (C.Y2 B) (C.Z2 B) C.L2 =
      ∑ e ∈ C.mobiusDivisors, ∑ P ∈ MiddleDirect.Geometry.admissibleRectangles C B,
        ∑ f₁ ∈ LargeDirect.divisorBin (F := F) P.1,
          ∑ f₂ ∈ LargeDirect.divisorBin (F := F) P.2,
            w e f₁ f₂ a * (if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then 1 else 0))
    (hw : ∀ e ∈ C.mobiusDivisors,
      ∀ P ∈ MiddleDirect.Geometry.admissibleRectangles C B,
      ∀ f₁ ∈ LargeDirect.divisorBin (F := F) P.1,
      ∀ f₂ ∈ LargeDirect.divisorBin (F := F) P.2,
      ∀ a ∈ C.originalRows B unit,
        ‖w e f₁ f₂ a‖ ≤ (H / norm e) / (P.1 * P.2)) :
    ‖E5 C B unit‖ ≤ H *
      (LargeDirect.fixedDivisorMass C *
        ∑ P ∈ MiddleDirect.Geometry.admissibleRectangles C B,
          LargeDirect.rectangleMass C B unit P / (P.1 * P.2)) := by
  let S := MiddleDirect.Geometry.admissibleRectangles C B
  let R := C.originalRows B unit
  let v := fun f₁ f₂ a => C.pairSum (fun p hp =>
    if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then C.coefficient p * C.primitive p hp a else 0)
  have heq : E5 C B unit =
      ∑ e ∈ C.mobiusDivisors, ∑ P ∈ S,
        ∑ f₁ ∈ LargeDirect.divisorBin (F := F) P.1,
          ∑ f₂ ∈ LargeDirect.divisorBin (F := F) P.2,
            ∑ a ∈ R, w e f₁ f₂ a * v f₁ f₂ a := by
    unfold E5
    have hreplace : C.pairSum (fun p hp => C.coefficient p *
        ∑ a ∈ R, C.primitive p hp a *
          Context.middle C.originalKernel ((c * C.d) * (p.1 * p.2))
            (Real.sqrt (C.M / norm a)) (C.Y2 B) (C.Z2 B) C.L2) =
      C.pairSum (fun p hp => C.coefficient p * ∑ a ∈ R, C.primitive p hp a *
        (∑ e ∈ C.mobiusDivisors, ∑ P ∈ S,
          ∑ f₁ ∈ LargeDirect.divisorBin (F := F) P.1,
            ∑ f₂ ∈ LargeDirect.divisorBin (F := F) P.2,
              w e f₁ f₂ a * (if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then 1 else 0))) := by
      unfold Context.pairSum
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs with hvalid
      · apply congrArg
        apply Finset.sum_congr rfl
        intro a ha
        rw [hrewrite p hp a ha]
      · rfl
    rw [hreplace]
    simp only [Finset.mul_sum, pairSum_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro P hP
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f₁ hf₁
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f₂ hf₂
    apply Finset.sum_congr rfl
    intro a ha
    rw [← pairSum_mul]
    unfold Context.pairSum
    apply Finset.sum_congr rfl
    intro p hp
    split_ifs <;> simp [v, mul_assoc] <;> ring
  rw [heq]
  apply le_trans (norm_sum_le _ _)
  calc
    _ ≤ ∑ e ∈ C.mobiusDivisors, ∑ P ∈ S,
          ∑ f₁ ∈ LargeDirect.divisorBin (F := F) P.1,
            ∑ f₂ ∈ LargeDirect.divisorBin (F := F) P.2,
              ∑ a ∈ R, ((H / norm e) / (P.1 * P.2)) * ‖v f₁ f₂ a‖ := by
      apply Finset.sum_le_sum
      intro e he
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro P hP
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro f₁ hf₁
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro f₂ hf₂
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      rw [_root_.norm_mul]
      exact mul_le_mul_of_nonneg_right (hw e he P hP f₁ hf₁ f₂ hf₂ a ha) (_root_.norm_nonneg _)
    _ = _ := by
      simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul,
        LargeDirect.rectangleMass, LargeDirect.fixedDivisorMass, S, R, v]
      simp_rw [← Finset.sum_comm (s := C.mobiusDivisors)]
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro P hP
      apply Finset.sum_congr rfl
      intro f₁ hf₁
      apply Finset.sum_congr rfl
      intro f₂ hf₂
      apply Finset.sum_congr rfl
      intro a ha
      ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirectWindow

end

end

section
noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirectKernelUniformity
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
def middleDivisorRectangles (C : Context Q) (B : ℝ) : Finset (ℝ × ℝ) :=
  (ErrorRectangles.rectangles C).filter (fun P =>
    ErrorRectangles.lowerConstant c / 2 * Real.sqrt (C.M / B) *
      Real.rpow (C.M * C.N) (-C.δ) / norm C.d ≤ P.1 * P.2)
theorem middle_divisor_expansion (C : Context Q) (B : ℝ) (unit : Bool)
    (hunit : unit = true → B = 1)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hδ : 0 < C.δ)
    (hB : 1 ≤ B) (hBK : B ≤ C.K) (hKM : C.K ≤ C.M)
    (hn : 1 ≤ norm C.d) (hnN : norm C.d ≤ 2 * C.N)
    (H : ℝ) (hH : 0 ≤ H)
    (hkernel : ∀ a ∈ C.originalRows B unit, ∀ f : Ideal (𝓞 F),
      0 < norm f → norm f ≤ C.Z2 B → ‖rowKernel C a f‖ ≤ H / norm f) :
    ‖E5 C B unit‖ ≤ H * (LargeDirect.fixedDivisorMass C *
      ∑ P ∈ middleDivisorRectangles C B,
        LargeDirect.rectangleMass C B unit P / (P.1 * P.2)) := by
  let w := fun e f₁ f₂ a =>
    if C.Y2 B < norm (e * (f₁ * f₂)) ∧ norm (e * (f₁ * f₂)) ≤ C.Z2 B then
      rowKernel C a (e * (f₁ * f₂)) else 0
  apply MiddleDirectWindow.middle_window_assembly C B unit H hH w
  · intro p hp a ha
    rw [MiddleDirectWindow.middle_triple C B a p (Finset.mem_filter.mp hp).2]
    exact MiddleDirectWindow.window_bucket_partition C B hN hn hnN p hp
      (fun e f₁ f₂ => w e f₁ f₂ a) (by
        intro e f₁ f₂ hnot
        simp [w, hnot])
  · intro e he P hP f₁ hf₁ f₂ hf₂ a ha
    dsimp [w]
    split_ifs with hwin
    · have he0 : e ≠ ⊥ := ne_bot_of_mem_idealDivisors he
      have hf₁b := (Finset.mem_filter.mp hf₁).2
      have hf₂b := (Finset.mem_filter.mp hf₂).2
      have hf₁0 : f₁ ≠ ⊥ := hf₁b.1
      have hf₂0 : f₂ ≠ ⊥ := hf₂b.1
      have hepos : 0 < norm e := by
        unfold norm
        exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr he0)
      have hf₁pos : 0 < norm f₁ := by
        unfold norm
        exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hf₁0)
      have hf₂pos : 0 < norm f₂ := by
        unfold norm
        exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hf₂0)
      have hfnorm : norm (e * (f₁ * f₂)) = norm e * (norm f₁ * norm f₂) := by
        simp [norm, map_mul]
      have hfpos : 0 < norm (e * (f₁ * f₂)) := by rw [hfnorm]; positivity
      have hPe := ErrorRectangles.rectangle_endpoints C P (Finset.mem_filter.mp hP).1
      have hPl : P.1 ≤ norm f₁ := by
        by_cases hh : P.1 = 1
        · simpa [hh] using hf₁b.2.1
        · exact (by simpa [hh] using hf₁b.2.1 : P.1 < norm f₁).le
      have hPr : P.2 ≤ norm f₂ := by
        by_cases hh : P.2 = 1
        · simpa [hh] using hf₂b.2.1
        · exact (by simpa [hh] using hf₂b.2.1 : P.2 < norm f₂).le
      have hPpos : 0 < P.1 * P.2 := by
        exact mul_pos (by linarith [hPe.1]) (by linarith [hPe.2.1])
      have hprod : P.1 * P.2 ≤ norm f₁ * norm f₂ :=
        mul_le_mul hPl hPr (by linarith [hPe.2.1]) hf₁pos.le
      calc
        ‖rowKernel C a (e * (f₁ * f₂))‖ ≤ H / norm (e * (f₁ * f₂)) :=
          hkernel a ha _ hfpos hwin.2
        _ = (H / norm e) / (norm f₁ * norm f₂) := by rw [hfnorm]; ring
        _ ≤ (H / norm e) / (P.1 * P.2) :=
          div_le_div_of_nonneg_left (div_nonneg hH hepos.le) hPpos hprod
    · simp only [norm_zero]
      have he' := ErrorRectangles.rectangle_endpoints C P (Finset.mem_filter.mp hP).1
      apply div_nonneg (div_nonneg hH (show 0 ≤ norm e by unfold norm; positivity))
      exact mul_nonneg (by linarith [he'.1]) (by linarith [he'.2.1])
end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirectKernelUniformity

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirectKernelUniformity

open LargeDirect

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
    ((middleDivisorRectangles C B).card : ℝ) ≤
      (Vendor.dyadicLength (2 * max 1 (C.N / norm C.d)) + 1 : ℝ) ^ 2 := by
  have h12 : (middleDivisorRectangles C B).card ≤
      ((ErrorRectangles.scales (C.N / norm C.d)) ×ˢ
        (ErrorRectangles.scales (C.N / norm C.d))).card := by
    apply Finset.card_le_card
    intro P hP
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).1
  have hs : (ErrorRectangles.scales (C.N / norm C.d)).card ≤
      Vendor.dyadicLength (2 * max 1 (C.N / norm C.d)) + 1 := by
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
      ((Finset.card_image_le).trans (by rw [Finset.card_range])) 1)
  have hd : (middleDivisorRectangles C B).card ≤
      (Vendor.dyadicLength (2 * max 1 (C.N / norm C.d)) + 1) ^ 2 := by
    exact h12.trans (by
      rw [Finset.card_product, pow_two]
      exact Nat.mul_le_mul hs hs)
  exact_mod_cast hd

theorem fixed_cost_epsilon
    (η : ℝ) (hη : 0 < η) :
    ∃ J : ℝ, 0 < J ∧ ∀ C : Context Q,
      1 ≤ C.M → 1 ≤ C.N → 1 ≤ norm C.d → ∀ B : ℝ,
        fixedDivisorMass C * ((middleDivisorRectangles C B).card : ℝ) ≤
          J * Real.rpow (C.M * C.N * norm C.d) η := by
  let e := η / 3
  have he : 0 < e := by dsimp [e]; linarith
  obtain ⟨A, hA, hdiv⟩ := ideal_divisor_count_le_rpow F e he
  let T := max 1 (norm c)
  let L := 2 + 1 / (e * Real.log 2)
  let H := L * (2 : ℝ) ^ e
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hL : 0 < L := Vendor.dyadicLength_small_power_constant_pos he
  have hH : 0 < H := mul_pos hL (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨(A * T ^ e) * H ^ 2, by positivity, ?_⟩
  intro C hM hN hn B
  let Z := C.M * C.N * norm C.d
  have hMN : 1 ≤ C.M * C.N := one_le_mul_of_one_le_of_one_le hM hN
  have hZ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le hMN hn
  have hnZ : norm C.d ≤ Z := le_mul_of_one_le_left (by linarith) hMN
  have hNZ : C.N ≤ Z := by
    dsimp [Z]
    calc C.N ≤ C.M * C.N := le_mul_of_one_le_left (by linarith) hM
      _ ≤ C.M * C.N * norm C.d := le_mul_of_one_le_right (by linarith) hn
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
  have hc : ((middleDivisorRectangles C B).card : ℝ) ≤ (H * Z ^ e) ^ 2 :=
    (rectangle_card_le C B).trans (pow_le_pow_left₀ (by positivity) hl 2)
  have hf0 : 0 ≤ fixedDivisorMass C := by
    unfold fixedDivisorMass
    exact Finset.sum_nonneg (fun f _ => by dsimp [norm]; positivity)
  calc fixedDivisorMass C * ((middleDivisorRectangles C B).card : ℝ)
      ≤ ((A * T ^ e) * Z ^ e) * (H * Z ^ e) ^ 2 :=
        mul_le_mul hf hc (by positivity) (by positivity)
    _ = ((A * T ^ e) * H ^ 2) * Z ^ η := by
      have hp : Z ^ e * Z ^ e * Z ^ e = Z ^ η := by
        rw [← Real.rpow_add (by linarith : 0 < Z), ← Real.rpow_add (by linarith : 0 < Z)]
        congr 1
        dsimp [e]
        ring
      calc _ = ((A * T ^ e) * H ^ 2) * (Z ^ e * Z ^ e * Z ^ e) := by ring
           _ = _ := by rw [hp]

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.MiddleDirectKernelUniformity

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

def middleRectangles (C : Context Q) (B : ℝ) : Finset (ℝ × ℝ) :=
  (rectangles C).filter (fun P =>
    (lowerConstant c / 2) * Real.sqrt (C.M / B) * Real.rpow (C.M * C.N) (-C.δ) /
      norm C.d ≤ P.1 * P.2)

def middleEnvelope (C : Context Q) (B : ℝ) : ℝ :=
  finiteSup (middleRectangles C B) (largeScore C B)

end ErrorRectangles

theorem bilinear_error_middle_direct
    (D : Sieve.AllIndexNormalizedFamilyData Q) (core : D.bad = c)
    (hF : NumberField.IsTotallyComplex F)
    (W : ℝ → ℝ) (hW : Sieve.SieveWeight W) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
        ∀ δ : ℝ, 0 < δ →
        ∀ C : Context Q, C.D = D → C.W = W → C.δ = δ →
        ∀ (B : ℝ) (unit : Bool), (unit = true → B = 1) →
          1 ≤ C.M → 1 ≤ C.N → 1 ≤ B → B ≤ C.K → C.K ≤ C.M →
          1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
          ‖E5 C B unit‖ ≤
            A * Real.rpow (C.M * C.N * norm C.d) ε *
              Real.rpow (C.M * C.N) (C0 * δ) *
              Real.sqrt (C.M / B) * ErrorRectangles.middleEnvelope C B *
              Sieve.energy F c C.N C.lam := by
  refine ⟨3, by norm_num, ?_⟩
  intro ε hε
  let η := ε / 3
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨A₀, hA₀, hrect⟩ :=
    LargeDirect.actual_prefix_rectangle_estimate D η hη
  obtain ⟨I, hI, hinc⟩ :=
    LargeDirect.incidence_energy_epsilon (Q := Q) η hη
  obtain ⟨J, hJ, hfixed⟩ := MiddleDirectKernelUniformity.fixed_cost_epsilon (Q := Q) η hη
  obtain ⟨H, hH, hkernel⟩ := MiddleDirectKernelUniformity.rowKernel_uniform (Q := Q) hF W hW
  refine ⟨H * A₀ * I * J, by positivity, ?_⟩
  intro δ hδ
  intro C hCD hCW hCδ B unit hunit hM hN hB hBK hKM hn hnN
  have hδC : 0 < C.δ := by simpa [hCδ] using hδ
  have hMN0 : 0 ≤ C.M * C.N := mul_nonneg (by linarith) (by linarith)
  have hX : 0 < C.M * C.N * norm C.d := by
    have hM0 : 0 < C.M := by linarith
    have hN0 : 0 < C.N := by linarith
    have hn0 : 0 < norm C.d := by linarith
    positivity
  let X := C.M * C.N * norm C.d
  change 0 < X at hX
  have hp : 0 ≤ Real.rpow X η := Real.rpow_nonneg hX.le _
  have hI0 : 0 ≤ I := le_trans zero_le_one hI
  let T := ErrorRectangles.middleRectangles C B
  let E := Sieve.energy F c C.N C.lam
  let V := ErrorRectangles.middleEnvelope C B
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
  have hf : 0 ≤ LargeDirect.fixedDivisorMass C := by
    unfold LargeDirect.fixedDivisorMass
    apply Finset.sum_nonneg
    intro f _
    unfold norm
    positivity
  have hcost := hfixed C hM hN hn B
  have hpows : Real.rpow X η * Real.rpow X η * Real.rpow X η =
      Real.rpow X ε := by
    change X ^ η * X ^ η * X ^ η = X ^ ε
    rw [← Real.rpow_add hX, ← Real.rpow_add hX]
    congr 1
    dsimp [η]
    ring
  have hkernelC : ∀ a ∈ C.originalRows B unit, ∀ f : Ideal (𝓞 F),
      0 < norm f → norm f ≤ C.Z2 B →
      ‖MiddleDirectKernelUniformity.rowKernel C a f‖ ≤
        (H * Real.rpow (C.M * C.N) (3 * C.δ) * Real.sqrt (C.M / B)) / norm f :=
    hkernel C hCW B unit hunit hM hN hδC hB
  have hpMN : 0 ≤ Real.rpow (C.M * C.N) (3 * C.δ) := Real.rpow_nonneg hMN0 _
  have hscale : 0 ≤ H * Real.rpow (C.M * C.N) (3 * C.δ) * Real.sqrt (C.M / B) :=
    mul_nonneg (mul_nonneg hH.le hpMN) (Real.sqrt_nonneg _)
  have hExp := MiddleDirectKernelUniformity.middle_divisor_expansion C B unit
    hunit hM hN hδC hB hBK hKM hn hnN
    (H * Real.rpow (C.M * C.N) (3 * C.δ) * Real.sqrt (C.M / B))
    (by positivity) hkernelC
  calc
    ‖E5 C B unit‖ ≤ (H * Real.rpow (C.M * C.N) (3 * C.δ) * Real.sqrt (C.M / B)) *
        (LargeDirect.fixedDivisorMass C *
          ∑ P ∈ T, LargeDirect.rectangleMass C B unit P / (P.1 * P.2)) := hExp
    _ ≤ (H * Real.rpow (C.M * C.N) (3 * C.δ) * Real.sqrt (C.M / B)) *
        (LargeDirect.fixedDivisorMass C *
          ((T.card : ℝ) * (A₀ * Real.rpow X η * V * (I * Real.rpow X η * E)))) := by
      gcongr
    _ = (LargeDirect.fixedDivisorMass C * (T.card : ℝ)) *
        (H * Real.rpow (C.M * C.N) (3 * C.δ) *
          Real.sqrt (C.M / B) * A₀ * Real.rpow X η * V * (I * Real.rpow X η * E)) := by ring
    _ ≤ (J * Real.rpow X η) *
        (H * Real.rpow (C.M * C.N) (3 * C.δ) *
          Real.sqrt (C.M / B) * A₀ * Real.rpow X η * V * (I * Real.rpow X η * E)) := by
      apply mul_le_mul_of_nonneg_right hcost
      positivity
    _ = (H * A₀ * I * J) * Real.rpow (C.M * C.N * norm C.d) ε *
        Real.rpow (C.M * C.N) (3 * δ) *
        Real.sqrt (C.M / B) * ErrorRectangles.middleEnvelope C B *
          Sieve.energy F c C.N C.lam := by
      change _ = (H * A₀ * I * J) * Real.rpow X ε *
        Real.rpow (C.M * C.N) (3 * δ) * Real.sqrt (C.M / B) * V * E
      rw [← hpows, hCδ]
      ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

end

end
