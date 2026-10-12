module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorShellRestriction

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneReverseRegulatorSpecialization

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShells

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H₀ D : Type} [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H₀ D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

def IsShellExpansion (I : IwasawaData A) (μ : Measure (LocalField F q))
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (p : H₀ → ShellNumerator) : Prop :=
  ∀ (r : ℂˣ), IsRegular F q r → ∀ lam : ℂ, ConvergenceRegion F q r lam →
    ∀ h : H₀,
      H F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r lam h =
        evaluateNumerator (p h) r (Q F q lam) /
          shellDenominator F q r (Q F q lam)

def actualDoubleCoefficient (I : IwasawaData A) (μ : Measure (LocalField F q))
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r : ℂˣ) (h : H₀) : ℂ :=
  ((J.op .minus (additiveParameter F q r)
    (forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r)).val
      (openCoordinate F ζ hζ q 0)).val h

 def Good {K L : Type} [Field K] [Field L] (f : K →+* L) (a : L) (x : RatFunc K) (b : L) : Prop :=
  Polynomial.eval₂ f a x.denom ≠ 0 ∧ RatFunc.eval f a x = b
variable {K L : Type} [Field K] [Field L] {f : K →+* L} {a : L}
private lemma good_C (c : K) : Good f a (RatFunc.C c) (f c) := by
  simp [Good]
private lemma good_X : Good f a (RatFunc.X : RatFunc K) a := by
  simp [Good]
private lemma good_mul {x y : RatFunc K} {b c : L} (hx : Good f a x b) (hy : Good f a y c) :
    Good f a (x*y) (b*c) := by
  refine ⟨?_, by rw [RatFunc.eval_mul f a hx.1 hy.1, hx.2, hy.2]⟩
  intro h
  have h' := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (RatFunc.denom_mul_dvd x y) h
  rw [Polynomial.eval₂_mul] at h'
  exact (mul_ne_zero hx.1 hy.1) h'
private lemma good_add {x y : RatFunc K} {b c : L} (hx : Good f a x b) (hy : Good f a y c) :
    Good f a (x+y) (b+c) := by
  refine ⟨?_, by rw [RatFunc.eval_add f a hx.1 hy.1, hx.2, hy.2]⟩
  intro h
  have h' := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (RatFunc.denom_add_dvd x y) h
  rw [Polynomial.eval₂_mul] at h'
  exact (mul_ne_zero hx.1 hy.1) h'
private lemma good_neg {x : RatFunc K} {b : L} (hx : Good f a x b) : Good f a (-x) (-b) := by
  simpa using good_mul (good_C (f := f) (a := a) (-1)) hx
private lemma good_sub {x y : RatFunc K} {b c : L} (hx : Good f a x b) (hy : Good f a y c) :
    Good f a (x-y) (b-c) := by
  simpa [sub_eq_add_neg] using good_add hx (good_neg hy)
private lemma good_one : Good f a (1 : RatFunc K) 1 := by
  simpa using good_C (f := f) (a := a) 1
private lemma good_zero : Good f a (0 : RatFunc K) 0 := by
  simpa using good_C (f := f) (a := a) 0
private lemma good_inv {x : RatFunc K} {b : L} (hx : Good f a x b) (hb : b ≠ 0) :
    Good f a x⁻¹ b⁻¹ := by
  have hnum : Polynomial.eval₂ f a x.num ≠ 0 := by
    intro h
    have : b = 0 := by rw [← hx.2, RatFunc.eval, h, zero_div]
    exact hb this
  have hxn : x ≠ 0 := by
    intro h; subst x; simpa using hnum
  have hi : Polynomial.eval₂ f a x⁻¹.denom ≠ 0 := by
    intro h
    exact hnum (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (RatFunc.denom_inv_dvd hxn) h)
  refine ⟨hi, ?_⟩
  have hm := good_mul hx (show Good f a x⁻¹ (RatFunc.eval f a x⁻¹) from ⟨hi, rfl⟩)
  have he : b * RatFunc.eval f a x⁻¹ = 1 := by
    rw [← hm.2, mul_inv_cancel₀ hxn, RatFunc.eval_one]
  apply (mul_left_cancel₀ hb)
  rw [he, mul_inv_cancel₀ hb]
private lemma good_div {x y : RatFunc K} {b c : L} (hx : Good f a x b) (hy : Good f a y c) (hc : c ≠ 0) :
    Good f a (x/y) (b/c) := by
  simpa [div_eq_mul_inv] using good_mul hx (good_inv hy hc)
private lemma good_pow {x : RatFunc K} {b : L} (hx : Good f a x b) (n : ℕ) :
    Good f a (x^n) (b^n) := by
  induction n with
  | zero => simpa using (good_one (f := f) (a := a))
  | succ n hn => simpa [pow_succ] using good_mul hn hx
private lemma good_zpow {x : RatFunc K} {b : L} (hx : Good f a x b) (hb : b ≠ 0) (n : ℤ) :
    Good f a (x^n) (b^n) := by
  cases n with
  | ofNat n => simpa using good_pow hx n
  | negSucc n => simpa [zpow_negSucc] using good_inv (good_pow hx (n+1)) (pow_ne_zero _ hb)
private lemma good_sum {ι : Type*} (s : Finset ι) (x : ι → RatFunc K) (b : ι → L)
    (h : ∀ i ∈ s, Good f a (x i) (b i)) : Good f a (∑ i ∈ s, x i) (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (good_zero (f := f) (a := a))
  | @insert i s hi hs =>
    simp only [Finset.sum_insert hi]
    exact good_add (h i (Finset.mem_insert_self _ _)) (hs fun j hj => h j (Finset.mem_insert_of_mem hj))

private theorem good_restriction (p : ShellNumerator) (r : ℂˣ)
    (hd : shellDenominator F q (r : ℂ) 1 ≠ 0) :
    Good (RingHom.id ℂ) (r : ℂ) (restrictionAtOne F q p)
      (evaluateNumerator p r 1 / shellDenominator F q r 1) := by
  have hq : (residueCardinality (LocalField F q) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
      (ValuativeRel.valuation (LocalField F q)).integer)).ne'
  have ht : t F q (r : ℂ) ≠ 0 := mul_ne_zero (inv_ne_zero hq) (pow_ne_zero _ r.ne_zero)
  have hn : Good (RingHom.id ℂ) (r : ℂ)
      (p.sum (fun ij c => RatFunc.C c * (RatFunc.X : Rr)^ij.1))
      (evaluateNumerator p r 1) := by
    classical
    simp only [evaluateNumerator, one_zpow, mul_one, Finsupp.sum]
    apply good_sum
    intro ij hij
    exact good_mul (good_C _) (good_zpow good_X r.ne_zero _)
  have hT : Good (RingHom.id ℂ) (r : ℂ)
      (RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ * (RatFunc.X : Rr)^6)
      (t F q (r : ℂ)) := good_mul (good_C _) (good_pow good_X _)
  have hD := good_mul (good_mul (good_sub good_one hT)
    (good_sub good_one (good_inv hT ht)))
    (good_sub good_one (good_C ((residueCardinality (LocalField F q) : ℂ)^(-3 : ℤ))))
  rw [restrictionAtOne_eq]
  simpa only [shellDenominator, one_pow, one_zpow, mul_one, RingHom.id_apply] using good_div hn hD (by simpa only [shellDenominator, one_pow, one_zpow, mul_one, RingHom.id_apply] using hd)

theorem restriction_regular (p : ShellNumerator) (r : ℂˣ)
    (hr : IsRegular F q r) :
    Polynomial.eval (r : ℂ) (RatFunc.denom (restrictionAtOne F q p)) ≠ 0 := by
  have hq : (1 : ℝ) < residueCardinality (LocalField F q) := by
    exact_mod_cast (Finite.one_lt_card (α := IsLocalRing.ResidueField
      (ValuativeRel.valuation (LocalField F q)).integer))
  have hq3 : (residueCardinality (LocalField F q) : ℂ)^3 ≠ 1 := by
    exact_mod_cast (one_lt_pow₀ hq (by decide : (3 : ℕ) ≠ 0)).ne'
  have ht : t F q (r : ℂ) ≠ 1 := by
    intro he
    exact hr (by rw [he]; exact sub_self 1)
  have hd : shellDenominator F q r 1 ≠ 0 := by
    simp only [shellDenominator, one_pow, one_zpow, mul_one]
    apply mul_ne_zero (mul_ne_zero hr _) _
    · exact sub_ne_zero.mpr (fun he => ht (inv_eq_one.mp he.symm))
    · simp only [zpow_neg, zpow_ofNat]
      exact sub_ne_zero.mpr (fun he => hq3 (inv_eq_one.mp he.symm))
  exact (good_restriction F q p r hd).1

end
end DedekindZetaZeroFree.KPRankOneReverseRegulatorSpecialization
