module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.InfinityValuationBlocks
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseSmallTailSignedCubeBlocks
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseShellLaurentDenominator

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneReverseRegulatorShells

open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseLaurentShellExpansion
open KPRankOneReverseRegulatorShellsRaw (smallRegion annulusRegion infinityRegion valuationIndex)

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]

def additiveParameter (r : ℂˣ) : ℂ :=
  -Complex.log (r : ℂ) / (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ)

theorem root_parameter_additiveParameter (r : ℂˣ) :
    KPRankOneRootParameter.r (LocalField F q) (additiveParameter F q r) = (r : ℂ) := by
  have hq1 : 1 < residueCardinality (LocalField F q) := Finite.one_lt_card
  have hlog : (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ) ≠ 0 := by
    have hl : Real.log (residueCardinality (LocalField F q) : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hq1)).ne'
    exact_mod_cast hl
  unfold KPRankOneRootParameter.r additiveParameter
  rw [show -(-Complex.log (r : ℂ) / (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ)) *
      (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ) = Complex.log (r : ℂ) by
    field_simp]
  exact Complex.exp_log r.ne_zero

def t (r : ℂ) : ℂ := (residueCardinality (LocalField F q) : ℂ)⁻¹ * r ^ 6

def IsRegular (r : ℂˣ) : Prop := 1 - t F q (r : ℂ) ≠ 0

def Q (lam : ℂ) : ℂ :=
  Complex.exp (-lam * (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ))

def ConvergenceRegion (r : ℂˣ) (lam : ℂ) : Prop :=
  lam.re < 1 ∧
    (residueCardinality (LocalField F q) : ℝ).rpow (-3 * lam.re) < ‖t F q (r : ℂ)‖

variable {H₀ D : Type} [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H₀ D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

def actualSection (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r : ℂˣ) : centerSectionSpace F ζ hζ q T A .plus (additiveParameter F q r) :=
  Classical.choose (center_pure_coordinate_section F ζ hζ q T A P B rep hrep d
    (additiveParameter F q r) φ hφ hcφ)

theorem actualSection_spec (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r : ℂˣ) :
    (∀ x, centerCoordinates T rep hrep
      ((actualSection F ζ hζ q T A P B rep hrep d φ hφ hcφ r).val
        (openCoordinate F ζ hζ q x)) = φ x • Pi.single d 1) ∧
    (∀ g : Cover F ζ hζ q,
      (¬ ∃ (b : A.B) (x : LocalField F q),
        g = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q x) →
      (actualSection F ζ hζ q T A P B rep hrep d φ hφ hcφ r).val g = 0) := by
  unfold actualSection
  exact (Classical.choose_spec (center_pure_coordinate_section F ζ hζ q T A P B rep hrep d
    (additiveParameter F q r) φ hφ hcφ)).1

def forwardSection (I : IwasawaData A) (μ : Measure (LocalField F q))
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r : ℂˣ) : centerSectionSpace F ζ hζ q T A .minus (-additiveParameter F q r) :=
  J.op .plus (additiveParameter F q r)
    (actualSection F ζ hζ q T A P B rep hrep d φ hφ hcφ r)

def reverseRoot (B : Binding F ζ hζ q A P) (r : ℂˣ)
    (v : (LocalField F q)ˣ) : CenterModule T →ₗ[ℂ] CenterModule T :=
  normPower (LocalField F q) (v ^ 2) (-additiveParameter F q r) •
    centerTorus F ζ hζ q T A .minus (B.rootTorus v)

theorem center_section_affine_locallyConstant (B : Binding F ζ hζ q A P)
    (ε : Sign) (z : ℂ) (f : centerSectionSpace F ζ hζ q T A ε z) :
    IsLocallyConstant (fun x : LocalField F q => f.val (openCoordinate F ζ hζ q x)) := by
  have hl : IsLocallyConstant f.val := by
    obtain ⟨U, hU⟩ := f.property.2
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have hc : Continuous (fun y : Cover F ζ hζ q => g⁻¹ * y) :=
      continuous_const.mul continuous_id
    have hmem : ∀ᶠ y : Cover F ζ hζ q in nhds g, g⁻¹ * y ∈ U :=
      hc.continuousAt.preimage_mem_nhds (by simpa using U.isOpen.mem_nhds U.one_mem)
    filter_upwards [hmem] with y hy
    have he := congrFun (hU (g⁻¹ * y) hy) g
    simpa [vectorRightTranslation] using he
  apply hl.comp_continuous
  have hn : Continuous (nLift F ζ hζ q) := by
    have he : nLift F ζ hζ q = fun s =>
        (A.upperRoot (Multiplicative.ofAdd s) : Cover F ζ hζ q) := by
      funext s
      exact (B.upper_eq s).symm
    rw [he]
    exact continuous_subtype_val.comp (A.upperRoot_continuous.comp continuous_ofAdd)
  exact continuous_const.mul hn

def reverseIntegrand (I : IwasawaData A) (μ : Measure (LocalField F q))
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r : ℂˣ) (lam : ℂ) (h : H₀) (v : (LocalField F q)ˣ) : ℂ :=
  (B.eta (kappa F ζ hζ q v 0) : ℂ) *
    (reverseRoot F ζ hζ q T A P B r v
      ((forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r).val
        (openCoordinate F ζ hζ q (v : LocalField F q)))).val h *
    normPower (LocalField F q) v lam

def H (I : IwasawaData A) (μ : Measure (LocalField F q))
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r : ℂˣ) (lam : ℂ) (h : H₀) : ℂ :=
  ∫ v : (LocalField F q)ˣ,
    reverseIntegrand F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r lam h v
      ∂multiplicativeMeasure F q μ

theorem actualSection_eq_zero_of_profile_eq_zero (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (hzero : φ = 0) (r : ℂˣ) :
    actualSection F ζ hζ q T A P B rep hrep d φ hφ hcφ r = 0 := by
  apply Eq.symm
  exact (Classical.choose_spec (center_pure_coordinate_section F ζ hζ q T A P B rep hrep d
    (additiveParameter F q r) φ hφ hcφ)).2 0 (by simp [hzero])

theorem reverseIntegrand_eq_zero_of_profile_eq_zero (I : IwasawaData A) (μ : Measure (LocalField F q))
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (hzero : φ = 0) (r : ℂˣ) (lam : ℂ) (h : H₀) :
    reverseIntegrand F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r lam h = 0 := by
  funext v
  have hf : forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r = 0 := by
    unfold forwardSection
    rw [actualSection_eq_zero_of_profile_eq_zero F ζ hζ q T A P B rep hrep d φ hφ hcφ hzero r]
    change (J.op .plus (additiveParameter F q r)) 0 = 0
    exact (J.op .plus (additiveParameter F q r)).map_zero
  simp only [reverseIntegrand, hf]
  change (B.eta (kappa F ζ hζ q v 0) : ℂ) *
    ((reverseRoot F ζ hζ q T A P B r v) 0).val h * normPower (LocalField F q) v lam = 0
  rw [map_zero]
  simp

abbrev ShellNumerator := (ℤ × ℤ) →₀ ℂ

def evaluateNumerator (p : ShellNumerator) (r Q : ℂ) : ℂ :=
  p.sum (fun ij c => c * r ^ ij.1 * Q ^ ij.2)

def shellDenominator (r Q : ℂ) : ℂ :=
  (1 - t F q r) * (1 - (t F q r)⁻¹ * Q ^ 3) *
    (1 - (residueCardinality (LocalField F q) : ℂ) ^ (-3 : ℤ) * Q ^ (-3 : ℤ))

theorem shellDenominator_ne_zero (r : ℂˣ) (hr : IsRegular F q r) (lam : ℂ)
    (hlam : ConvergenceRegion F q r lam) :
    shellDenominator F q r (Q F q lam) ≠ 0 := by
  have hqpos : 0 < (residueCardinality (LocalField F q) : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
      (Valuation.integer (valuation (LocalField F q)))))
  have hlog : 0 < Real.log (residueCardinality (LocalField F q) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (Finite.one_lt_card (α := IsLocalRing.ResidueField
      (Valuation.integer (valuation (LocalField F q)))))
  have htpos : 0 < ‖t F q (r : ℂ)‖ := by
    apply norm_pos_iff.mpr
    unfold t
    exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hqpos.ne'))
      (pow_ne_zero _ (Units.ne_zero r))
  have hnormQ : ‖Q F q lam‖ = Real.exp (-lam.re *
      Real.log (residueCardinality (LocalField F q) : ℝ)) := by
    simp only [Q, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_im, mul_zero, sub_zero]
  have hsmall : ‖(t F q (r : ℂ))⁻¹ * Q F q lam ^ 3‖ < 1 := by
    rw [norm_mul, norm_inv, norm_pow, hnormQ, ← Real.exp_nat_mul,
      inv_mul_lt_iff₀ htpos, mul_one]
    convert hlam.2 using 1
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hqpos]
    congr 1
    norm_num
    ring
  have hlarge : ‖(residueCardinality (LocalField F q) : ℂ) ^ (-3 : ℤ) *
      Q F q lam ^ (-3 : ℤ)‖ < 1 := by
    rw [norm_mul, norm_zpow, Complex.norm_natCast, norm_zpow, hnormQ]
    rw [zpow_neg, zpow_ofNat, zpow_neg, zpow_ofNat, ← Real.exp_nat_mul,
      ← Real.exp_neg]
    rw [show (residueCardinality (LocalField F q) : ℝ) ^ 3 =
      Real.exp (3 * Real.log (residueCardinality (LocalField F q) : ℝ)) by
        simpa [Real.exp_log hqpos] using
          (Real.exp_nat_mul (Real.log (residueCardinality (LocalField F q) : ℝ)) 3).symm, ← Real.exp_neg, ← Real.exp_add]
    apply Real.exp_lt_one_iff.mpr
    norm_num
    have hlt : lam.re < 1 := hlam.1
    nlinarith [mul_pos (sub_pos.mpr hlt) hlog]
  have hn {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
    intro he
    have : z = 1 := (sub_eq_zero.mp he).symm
    simpa [this] using hz
  exact mul_ne_zero (mul_ne_zero hr (hn hsmall)) (hn hlarge)

abbrev Rr := RatFunc ℂ
abbrev RrQ := RatFunc Rr

def rationalNumerator (p : ShellNumerator) : RrQ :=
  p.sum (fun ij c => RatFunc.C (RatFunc.C c) *
    (RatFunc.C (RatFunc.X : Rr)) ^ ij.1 * (RatFunc.X : RrQ) ^ ij.2)

def rationalDenominator : RrQ :=
  let t' : RrQ := RatFunc.C
    (RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ * (RatFunc.X : Rr) ^ 6)
  (1 - t') * (1 - t'⁻¹ * (RatFunc.X : RrQ) ^ 3) *
    (1 - RatFunc.C (RatFunc.C
      ((residueCardinality (LocalField F q) : ℂ) ^ (-3 : ℤ))) *
      (RatFunc.X : RrQ) ^ (-3 : ℤ))

def rationalH (p : ShellNumerator) : RrQ :=
  rationalNumerator p / rationalDenominator F q

def evaluateRational (R : RrQ) (r Q : ℂ) : ℂ :=
  RatFunc.eval (RingHom.id ℂ) r
    (RatFunc.eval (RingHom.id Rr) (RatFunc.C Q) R)

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

private lemma good_geometric {K L : Type} [Field K] [Field L]
    {f : K →+* L} {a : L} {s x c : RatFunc K} {sb xb cb : L}
    (hs : Good f a s sb) (hx : Good f a x xb) (hc : Good f a c cb)
    (hsb : sb ≠ 0) (hxb : xb ≠ 0) :
    Good f a ((1-s) * (1-s⁻¹*x^3) * (1-c*x^(-3 : ℤ)))
      ((1-sb) * (1-sb⁻¹*xb^3) * (1-cb*xb^(-3 : ℤ))) :=
  good_mul (good_mul (good_sub good_one hs)
    (good_sub good_one (good_mul (good_inv hs hsb) (good_pow hx 3))))
    (good_sub good_one (good_mul hc (good_zpow hx hxb (-3))))

private lemma good_numerator_outer (p : ShellNumerator) (Q : ℂ) (hQ : Q ≠ 0) :
    Good (RingHom.id Rr) (RatFunc.C Q) (rationalNumerator p)
      (p.sum (fun ij c => RatFunc.C c * (RatFunc.X : Rr)^ij.1 * (RatFunc.C Q)^ij.2)) := by
  classical
  unfold rationalNumerator Finsupp.sum
  apply good_sum
  intro ij hij
  exact good_mul (good_mul (good_C _) (good_zpow (good_C _) RatFunc.X_ne_zero _))
    (good_zpow good_X (by simpa using hQ) _)

private lemma good_numerator_inner (p : ShellNumerator) (r Q : ℂ) (hr : r ≠ 0) :
    Good (RingHom.id ℂ) r
      (p.sum (fun ij c => RatFunc.C c * (RatFunc.X : Rr)^ij.1 * (RatFunc.C Q)^ij.2))
      (evaluateNumerator p r Q) := by
  classical
  unfold evaluateNumerator Finsupp.sum
  apply good_sum
  intro ij hij
  have hg : Good (RingHom.id ℂ) r ((RatFunc.C Q)^ij.2) (Q^ij.2) := by
    rw [← map_zpow₀]
    exact good_C _
  exact good_mul (good_mul (good_C _) (good_zpow good_X hr _)) hg

private lemma good_t_inner (r : ℂ) :
    Good (RingHom.id ℂ) r
      (RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ * (RatFunc.X : Rr)^6)
      (t F q r) := by
  unfold t
  exact good_mul (good_C _) (good_pow good_X 6)

private lemma t_ne_zero (r : ℂ) (hr : r ≠ 0) : t F q r ≠ 0 := by
  unfold t
  apply mul_ne_zero _ (pow_ne_zero _ hr)
  apply inv_ne_zero
  exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
    (Valuation.integer (valuation (LocalField F q))))).ne'

private lemma good_denominator_inner (r Q : ℂ) (hr : r ≠ 0) (hQ : Q ≠ 0) :
    Good (RingHom.id ℂ) r
      ((1 - RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ * (RatFunc.X : Rr)^6) *
        (1 - (RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ * (RatFunc.X : Rr)^6)⁻¹ * (RatFunc.C Q)^3) *
        (1 - RatFunc.C ((residueCardinality (LocalField F q) : ℂ)^(-3 : ℤ)) * (RatFunc.C Q)^(-3 : ℤ)))
      (shellDenominator F q r Q) := by
  exact good_geometric (good_t_inner F q r) (good_C Q) (good_C _)
    (t_ne_zero F q r hr) hQ

private lemma good_denominator_outer (Q : ℂ) (hQ : Q ≠ 0) :
    Good (RingHom.id Rr) (RatFunc.C Q) (rationalDenominator F q)
      ((1 - RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ * (RatFunc.X : Rr)^6) *
        (1 - (RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ * (RatFunc.X : Rr)^6)⁻¹ * (RatFunc.C Q)^3) *
        (1 - RatFunc.C ((residueCardinality (LocalField F q) : ℂ)^(-3 : ℤ)) * (RatFunc.C Q)^(-3 : ℤ))) := by
  have hs : RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ * (RatFunc.X : Rr)^6 ≠ 0 := by
    apply mul_ne_zero _ (pow_ne_zero _ RatFunc.X_ne_zero)
    simp only [ne_eq, map_eq_zero, inv_eq_zero]
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
      (Valuation.integer (valuation (LocalField F q))))).ne'
  unfold rationalDenominator
  exact good_geometric
    (good_C (RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ * (RatFunc.X : Rr)^6))
    good_X (good_C (RatFunc.C ((residueCardinality (LocalField F q) : ℂ)^(-3 : ℤ))))
    hs (by simpa using hQ)

theorem evaluateRational_rationalH (p : ShellNumerator) (r Q : ℂ)
    (hr : r ≠ 0) (hQ : Q ≠ 0) (hden : shellDenominator F q r Q ≠ 0) :
    evaluateRational (rationalH F q p) r Q =
      evaluateNumerator p r Q / shellDenominator F q r Q := by
  have hi := good_denominator_inner F q r Q hr hQ
  have hd :
      (1 - RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ * (RatFunc.X : Rr)^6) *
        (1 - (RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ * (RatFunc.X : Rr)^6)⁻¹ * (RatFunc.C Q)^3) *
        (1 - RatFunc.C ((residueCardinality (LocalField F q) : ℂ)^(-3 : ℤ)) * (RatFunc.C Q)^(-3 : ℤ)) ≠ 0 := by
    intro hz
    have : shellDenominator F q r Q = 0 := by rw [← hi.2, hz, RatFunc.eval_zero]
    exact hden this
  have ho := good_div (good_numerator_outer p Q hQ) (good_denominator_outer F q Q hQ) hd
  unfold evaluateRational rationalH
  rw [ho.2]
  exact (good_div (good_numerator_inner p r Q hr) hi hden).2

def restrictionAtOne (p : ShellNumerator) : Rr :=
  RatFunc.eval (RingHom.id Rr) 1 (rationalH F q p)

private lemma denominator_one_ne_zero :
    (1 - RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ * (RatFunc.X : Rr)^6) *
      (1 - (RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ * (RatFunc.X : Rr)^6)⁻¹) *
      (1 - RatFunc.C ((residueCardinality (LocalField F q) : ℂ)^(-3 : ℤ))) ≠ 0 := by
  have hq : (1 : ℝ) < residueCardinality (LocalField F q) := by
    exact_mod_cast (Finite.one_lt_card (α := IsLocalRing.ResidueField
      (Valuation.integer (valuation (LocalField F q)))))
  have hqn : (residueCardinality (LocalField F q) : ℂ) ≠ 0 := by
    exact_mod_cast (lt_trans zero_lt_one hq).ne'
  have hq1 : (residueCardinality (LocalField F q) : ℂ) ≠ 1 := by
    exact_mod_cast hq.ne'
  have hq3 : (residueCardinality (LocalField F q) : ℂ)^3 ≠ 1 := by
    exact_mod_cast (one_lt_pow₀ hq (by decide : (3 : ℕ) ≠ 0)).ne'
  have hn : shellDenominator F q 1 1 ≠ 0 := by
    simp only [shellDenominator, t, one_pow, one_zpow, mul_one, inv_inv, zpow_neg,
      zpow_ofNat]
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply sub_ne_zero.mpr
        intro he
        exact hq1 (inv_eq_one.mp he.symm)
      · exact sub_ne_zero.mpr (Ne.symm hq1)
    · apply sub_ne_zero.mpr
      simp only [inv_one, mul_one]
      intro he
      exact hq3 (inv_eq_one.mp he.symm)
  have hg := good_denominator_inner F q 1 1 one_ne_zero one_ne_zero
  simp only [one_pow, one_zpow, map_one, mul_one] at hg
  intro hz
  exact hn (by rw [← hg.2, hz, RatFunc.eval_zero])

private lemma good_H_one (p : ShellNumerator) :
    Good (RingHom.id Rr) (1 : Rr) (rationalH F q p)
      ((p.sum (fun ij c => RatFunc.C c * (RatFunc.X : Rr)^ij.1)) /
        ((1 - RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ * (RatFunc.X : Rr)^6) *
          (1 - (RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ * (RatFunc.X : Rr)^6)⁻¹) *
          (1 - RatFunc.C ((residueCardinality (LocalField F q) : ℂ)^(-3 : ℤ))))) := by
  have hn := good_numerator_outer p 1 one_ne_zero
  have hd := good_denominator_outer F q 1 one_ne_zero
  simp only [map_one, one_zpow, one_pow, mul_one] at hn hd
  exact good_div hn hd (denominator_one_ne_zero F q)

theorem restrictionAtOne_eq (p : ShellNumerator) :
    restrictionAtOne F q p =
      (p.sum (fun ij c => RatFunc.C c * (RatFunc.X : Rr) ^ ij.1)) /
        ((1 - RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ *
            (RatFunc.X : Rr) ^ 6) *
          (1 - (RatFunc.C (residueCardinality (LocalField F q) : ℂ)⁻¹ *
            (RatFunc.X : Rr) ^ 6)⁻¹) *
          (1 - RatFunc.C ((residueCardinality (LocalField F q) : ℂ) ^ (-3 : ℤ)))) := by
  exact (good_H_one F q p).2

end
end DedekindZetaZeroFree.KPRankOneReverseRegulatorShells
