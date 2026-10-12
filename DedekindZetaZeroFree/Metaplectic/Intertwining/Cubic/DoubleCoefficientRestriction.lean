module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.FullCenterReverseChart
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorSpecialization

@[expose] public section

namespace DedekindZetaZeroFree.KPActualResidueSources
open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShells KPRankOneReverseRegulatorSpecialization KPActualScalarBinding
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg) [DecidableEq S.D]
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

private theorem actual_own_chamber_composition
    (I : IwasawaData S.borel) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel I μ)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q) (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (p : KPExceptionalRaw.actualTorus F ζ hζ q → ShellNumerator)
    (hp : IsShellExpansion F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ p)
    (r : ℂˣ) (hr : IsRegular F q r) (ht : 1 < ‖t F q (r : ℂ)‖) (h : KPExceptionalRaw.actualTorus F ζ hζ q) :
    Integrable (fun x : LocalField F q =>
      ((forwardSection F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r).val
        (kernelW (LocalField F q) S.borel .minus * nLift F ζ hζ q x *
          openCoordinate F ζ hζ q 0)).val h) μ ∧
    H F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r 0 h =
      centerIntegralCoordinate F ζ hζ q S.heisenberg S.borel μ .minus (additiveParameter F q r)
        (forwardSection F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r)
        (openCoordinate F ζ hζ q 0) h ∧
    centerIntegralCoordinate F ζ hζ q S.heisenberg S.borel μ .minus (additiveParameter F q r)
        (forwardSection F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r)
        (openCoordinate F ζ hζ q 0) h =
      actualDoubleCoefficient F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r h ∧
    RatFunc.eval (RingHom.id ℂ) (r : ℂ) (restrictionAtOne F q (p h)) =
      actualDoubleCoefficient F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r h := by
  have hc : ConvergenceRegion F q r 0 := by
    constructor
    · norm_num
    · convert ht using 1 <;> norm_num
  have hz : convergenceHalfPlane .minus (additiveParameter F q r) := by
    apply (convergence_iff_geometric (LocalField F q) .minus _).mpr
    simp only [reduceCtorEq, if_false, KPRankOneRootParameter.t,
      root_parameter_additiveParameter, norm_inv]
    change ‖t F q (r : ℂ)‖⁻¹ < 1
    exact (inv_lt_one₀ (lt_trans zero_lt_one ht)).mpr ht
  let f := forwardSection F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r
  obtain ⟨hi, he⟩ := J.integral_eq .minus (additiveParameter F q r) hz f
    (openCoordinate F ζ hζ q 0) h
  have hb : ∀ v : (LocalField F q)ˣ,
      (f.val (kernelW (LocalField F q) S.borel .minus * nLift F ζ hζ q
        (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q)) * openCoordinate F ζ hζ q 0)).val h =
      (KPCubicHaar.abs (LocalField F q) (v : LocalField F q) : ℂ) *
        reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r 0 h v := by
    intro v
    have hb := congrArg (fun V : CenterModule S.heisenberg => V.val h)
      (actual_reverse_chart F ζ hζ q S P r f v)
    have ha : localAbs (LocalField F q) v =
        KPCubicHaar.abs (LocalField F q) (v : LocalField F q) := by
      simp only [localAbs, KPCubicHaar.abs, if_neg v.ne_zero, Real.rpow_intCast]
      rfl
    simpa only [kernelW, (S.openCell P).weyl_eq, reverseIntegrand,
      S.openCell_ordinary P, normPower, zero_mul, Complex.exp_zero, mul_one, ha,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, f,
      KPRankOneReverseRegulatorShellsRaw.reverseRoot, reverseRoot,
      KPRankOneReverseRegulatorShellsRaw.additiveParameter, additiveParameter]
      using hb
  have hint := KPRankOneBruhatKernelTransport.inverse_substitution (LocalField F q) μ
    (fun x => (f.val (kernelW (LocalField F q) S.borel .minus * nLift F ζ hζ q x *
      openCoordinate F ζ hζ q 0)).val h)
    (reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r 0 h) hi hb
  have hH : H F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r 0 h =
      centerIntegralCoordinate F ζ hζ q S.heisenberg S.borel μ .minus (additiveParameter F q r) f
        (openCoordinate F ζ hζ q 0) h := hint.2.symm
  have hval : RatFunc.eval (RingHom.id ℂ) (r : ℂ) (restrictionAtOne F q (p h)) =
      H F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r 0 h := by
    have hd := shellDenominator_ne_zero F q r hr 0 hc
    simp only [Q, neg_zero, zero_mul, Complex.exp_zero] at hd
    have hp' := hp r hr 0 hc h
    simp only [Q, neg_zero, zero_mul, Complex.exp_zero] at hp'
    exact (good_restriction F q (p h) r hd).2.trans hp'.symm
  exact ⟨hi, hH, he.symm, hval.trans (hH.trans he.symm)⟩

private theorem exterior_infinite (a : ℂ) (ha : a ≠ 0) :
    {z : ℂ | 1 < ‖a * z ^ 6‖}.Infinite := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((2 : ℂ) / a) (by decide : 0 < 6)
  have hm : a * z ^ 6 = 2 := by rw [hz]; field_simp
  have ho : IsOpen {z : ℂ | 1 < ‖a * z ^ 6‖} :=
    isOpen_lt continuous_const ((continuous_const.mul (continuous_id.pow 6)).norm)
  apply infinite_of_mem_nhds z
  apply ho.mem_nhds
  change 1 < ‖a * z ^ 6‖
  rw [hm, Complex.norm_ofNat]
  norm_num

private theorem ratfunc_eq_of_infinite (R S : RatFunc ℂ)
    (s : Set ℂ) (hs : s.Infinite)
    (h : ∀ z ∈ s, Polynomial.eval z R.denom ≠ 0 ∧ Polynomial.eval z S.denom ≠ 0 ∧
      RatFunc.eval (RingHom.id ℂ) z R = RatFunc.eval (RingHom.id ℂ) z S) : R = S := by
  have hp : R.num * S.denom = S.num * R.denom := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hs.mono
    intro z hz
    obtain ⟨hr, hs, he⟩ := h z hz
    simp only [RatFunc.eval, Polynomial.eval₂_id] at he
    simpa only [Set.mem_setOf_eq, Polynomial.eval_mul] using (div_eq_div_iff hr hs).mp he
  exact (RatFunc.num_mul_eq_mul_denom_iff (RatFunc.denom_ne_zero S)).mp hp |>.trans
    (RatFunc.num_div_denom S)

private theorem actual_rational_coefficient_restriction
    (I : IwasawaData S.borel) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel I μ)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q) (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (p : KPExceptionalRaw.actualTorus F ζ hζ q → ShellNumerator)
    (hp : IsShellExpansion F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ p)
    (h : KPExceptionalRaw.actualTorus F ζ hζ q) (R : Rr)
    (hR : ∀ (r : ℂˣ), IsRegular F q r → 1 < ‖t F q (r : ℂ)‖ →
      Polynomial.eval (r : ℂ) (RatFunc.denom R) ≠ 0 →
      RatFunc.eval (RingHom.id ℂ) (r : ℂ) R =
        actualDoubleCoefficient F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r h) :
    R = restrictionAtOne F q (p h) := by
  classical
  let Rone := restrictionAtOne F q (p h)
  have hq : (residueCardinality (LocalField F q) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
      (ValuativeRel.valuation (LocalField F q)).integer)).ne'
  have hinf : {z : ℂ | 1 < ‖t F q z‖}.Infinite :=
    exterior_infinite _ (inv_ne_zero hq)
  let poles : Set ℂ := {z | Polynomial.eval z R.denom = 0} ∪
    {z | Polynomial.eval z Rone.denom = 0}
  have hfinite : poles.Finite :=
    (Polynomial.finite_setOf_isRoot (RatFunc.denom_ne_zero R)).union
      (Polynomial.finite_setOf_isRoot (RatFunc.denom_ne_zero Rone))
  apply ratfunc_eq_of_infinite R Rone _ (hinf.diff hfinite)
  intro z hz
  obtain ⟨ht, hpole⟩ := hz
  change 1 < ‖t F q z‖ at ht
  have hRden : Polynomial.eval z R.denom ≠ 0 := fun he => hpole (Or.inl he)
  have hSden : Polynomial.eval z Rone.denom ≠ 0 := fun he => hpole (Or.inr he)
  have hz0 : z ≠ 0 := by
    intro he
    simp [he, t] at ht
    exact (not_lt_of_ge zero_le_one ht)
  let r : ℂˣ := Units.mk0 z hz0
  have hr : IsRegular F q r := by
    intro he
    have he' : t F q z = 1 := by
      change 1 - t F q z = 0 at he
      exact (sub_eq_zero.mp he).symm
    rw [he'] at ht
    norm_num at ht
  refine ⟨hRden, hSden, ?_⟩
  have heR := hR r hr ht hRden
  have heS := (actual_own_chamber_composition F ζ hζ q S P I μ J
    rep hrep d φ hφ hcφ p hp r hr ht h).2.2.2
  exact heR.trans heS.symm

set_option backward.isDefEq.respectTransparency false in
private theorem exists_rational_double
    (I : IwasawaData S.borel) (μ : Measure (LocalField F q))
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel I μ)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q) (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (h : KPExceptionalRaw.actualTorus F ζ hζ q) :
    ∃ R : RatFunc ℂ, ∀ r : ℂˣ, IsRegular F q r →
      Good (RingHom.id ℂ) (r : ℂ) R
        (actualDoubleCoefficient F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r h) := by
  classical
  obtain ⟨L, hL, ψ, hψ⟩ :=
    KPRankOneReverseLaurentShellExpansion.FiniteAnnulusSteps.compact_profile_uniform_laurent
      F ζ hζ q S.heisenberg S.borel P I (S.openCell P) rep hrep d φ hφ hcφ
  obtain ⟨pp, hpp, _⟩ := J.numerators L hL .plus
  obtain ⟨pm, hpm, _⟩ := J.numerators L hL .minus
  let g := openCoordinate F ζ hζ q 0
  let b := I.borelPart g
  let m : ℤ := -KPRankOneReverseRegulatorShellsRaw.valuationIndex F q (S.borel.coordinate (S.borel.retract b))
  let c (j i n : ℤ) : ℂ :=
    (centerTorus F ζ hζ q S.heisenberg S.borel .plus (S.borel.retract b)
      (((pm j) ((pp i) (ψ n))).val.val (I.compactPart g))).val h
  let N : RatFunc ℂ := ∑ j ∈ pm.support, ∑ i ∈ pp.support, ∑ n ∈ ψ.support,
    RatFunc.C (c j i n) * (RatFunc.X : RatFunc ℂ)^(-j) * RatFunc.X^i * RatFunc.X^n
  let U : RatFunc ℂ := RatFunc.C ((residueCardinality (LocalField F q) : ℂ)⁻¹) * RatFunc.X^6
  let R : RatFunc ℂ := (RatFunc.C (deltaHalf S.borel b) * RatFunc.X^m * N) / ((1-U)*(1-U⁻¹))
  refine ⟨R, ?_⟩
  intro r hr
  let a := additiveParameter F q r
  have hdplus : denominator (LocalField F q) .plus a = 1 - t F q (r : ℂ) := by
    simp only [denominator, if_true, KPRankOneRootParameter.t, a, root_parameter_additiveParameter, t]
  have hdminus : denominator (LocalField F q) .minus a = 1 - (t F q (r : ℂ))⁻¹ := by
    simp only [denominator, reduceCtorEq, if_false, a, root_parameter_additiveParameter, t,
      mul_inv_rev, inv_inv, inv_pow]
    ring
  have hq : (residueCardinality (LocalField F q) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
      (ValuativeRel.valuation (LocalField F q)).integer)).ne'
  have ht : t F q (r : ℂ) ≠ 0 := mul_ne_zero (inv_ne_zero hq) (pow_ne_zero _ r.ne_zero)
  have hdm : 1 - (t F q (r : ℂ))⁻¹ ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    apply hr
    exact sub_eq_zero.mpr (inv_eq_one.mp he.symm).symm
  have hactual : actualDoubleCoefficient F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r h =
      deltaHalf S.borel b * (r : ℂ)^m *
        (∑ j ∈ pm.support, ∑ i ∈ pp.support, ∑ n ∈ ψ.support,
          c j i n * (r : ℂ)^(-j) * (r : ℂ)^i * (r : ℂ)^n) /
          ((1 - t F q (r : ℂ)) * (1 - (t F q (r : ℂ))⁻¹)) := by
    have hsplus := J.shell_eq L .plus pp hpp a (hdplus ▸ hr) (ψ.sum (fun n f => (r : ℂ)^n • f))
    have hsminus := J.shell_eq L .minus pm hpm a (hdminus ▸ hdm)
      (centerContinuedLevel F ζ hζ q S.heisenberg S.borel I L .plus pp a (ψ.sum (fun n f => (r : ℂ)^n • f)))
    have hin : actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P) rep hrep d φ hφ hcφ r =
        centerCompactTrivialization F ζ hζ q S.heisenberg S.borel I .plus a (ψ.sum (fun n f => (r : ℂ)^n • f)).val := hψ r
    change J.op .plus a (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel I .plus a
      (ψ.sum (fun n f => (r : ℂ)^n • f)).val) =
      centerCompactTrivialization F ζ hζ q S.heisenberg S.borel I .minus (-a)
        (centerContinuedLevel F ζ hζ q S.heisenberg S.borel I L .plus pp a
          (ψ.sum (fun n f => (r : ℂ)^n • f))).val at hsplus
    rw [← hin] at hsplus
    have hcomp := (congrArg (J.op .minus a) hsplus).trans hsminus
    change J.op .minus a (forwardSection F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r) = _ at hcomp
    have hcval := congrArg (fun f => (f.val g).val h) hcomp
    change actualDoubleCoefficient F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r h = _ at hcval
    rw [hcval]
    with_unfolding_all simp only [targetParameter, sourceParameter, targetSign, sourceSign, id_eq,
      show Sign.minus ≠ Sign.plus from by decide, ite_false, neg_neg]
    have heplus : (evaluationUnit (LocalField F q) .plus a : ℂ) = (r : ℂ) := by
      simp [evaluationUnit, a, KPRankOneRootParameter.rUnit, root_parameter_additiveParameter]
    have heminus : (evaluationUnit (LocalField F q) .minus a : ℂ) = (r : ℂ)⁻¹ := by
      simp [evaluationUnit, a, KPRankOneRootParameter.rUnit, root_parameter_additiveParameter]
    have hnorm : normPower (LocalField F q) (S.borel.coordinate (S.borel.retract b)) a = (r : ℂ)^m := by
      have hn := KPRankOneReverseLaurentShellExpansion.FiniteAnnulusSteps.reverse_compact_normPower_root
        F q (S.borel.coordinate (S.borel.retract b)) r
      have he : normPower (LocalField F q) (S.borel.coordinate (S.borel.retract b)) a =
          (normPower (LocalField F q) (S.borel.coordinate (S.borel.retract b)) (-a))⁻¹ := by
        simp only [normPower, neg_mul, Complex.exp_neg, inv_inv]
      exact he.trans ((congrArg Inv.inv hn).trans (by simp only [m, zpow_neg]))
    change (centerInducingAction F ζ hζ q S.heisenberg S.borel .plus (targetParameter .minus a) b
      (((centerContinuedLevel F ζ hζ q S.heisenberg S.borel I L .minus pm a)
        ((centerContinuedLevel F ζ hζ q S.heisenberg S.borel I L .plus pp a)
          (ψ.sum (fun n f => (r : ℂ)^n • f)))).val.val (I.compactPart g))).val h = _
    change ((deltaHalf S.borel b * normPower (LocalField F q) (S.borel.coordinate (S.borel.retract b))
      (targetParameter .minus a)) • centerTorus F ζ hζ q S.heisenberg S.borel .plus (S.borel.retract b)
      (((centerContinuedLevel F ζ hζ q S.heisenberg S.borel I L .minus pm a)
        ((centerContinuedLevel F ζ hζ q S.heisenberg S.borel I L .plus pp a)
          (ψ.sum (fun n f => (r : ℂ)^n • f)))).val.val (I.compactPart g))).val h = _
    have htpar : targetParameter .minus a = a := by simp [targetParameter, sourceParameter]
    rw [htpar, hnorm]
    simp only [centerContinuedLevel, centerEvaluate, Finsupp.sum, hdplus, hdminus,
      heplus, heminus, LinearMap.smul_apply, LinearMap.sum_apply,
      Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply, Finset.sum_apply,
      map_smul, map_sum, smul_eq_mul, inv_zpow, ← zpow_neg]
    simp only [c, Finset.mul_sum, Finset.sum_mul, div_eq_mul_inv, mul_inv_rev]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hU : Good (RingHom.id ℂ) (r : ℂ) U (t F q (r : ℂ)) :=
    good_mul (good_C _) (good_pow good_X _)
  have hN : Good (RingHom.id ℂ) (r : ℂ) N
      (∑ j ∈ pm.support, ∑ i ∈ pp.support, ∑ n ∈ ψ.support,
        c j i n * (r : ℂ)^(-j) * (r : ℂ)^i * (r : ℂ)^n) := by
    apply good_sum
    intro j hj
    apply good_sum
    intro i hi
    apply good_sum
    intro n hn
    exact good_mul (good_mul (good_mul (good_C _) (good_zpow good_X r.ne_zero _))
      (good_zpow good_X r.ne_zero _)) (good_zpow good_X r.ne_zero _)
  have hR := good_div (good_mul (good_mul (good_C (deltaHalf S.borel b))
    (good_zpow good_X r.ne_zero m)) hN)
    (good_mul (good_sub good_one hU) (good_sub good_one (good_inv hU ht))) (mul_ne_zero hr hdm)
  exact ⟨hR.1, hR.2.trans hactual.symm⟩

theorem actual_restriction_eq_double_coefficient
    (I : IwasawaData S.borel) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel I μ)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q) (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (p : KPExceptionalRaw.actualTorus F ζ hζ q → ShellNumerator)
    (hp : IsShellExpansion F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ p)
    (r : ℂˣ) (hr : IsRegular F q r) (h : KPExceptionalRaw.actualTorus F ζ hζ q) :
    Polynomial.eval (r : ℂ) (RatFunc.denom (restrictionAtOne F q (p h))) ≠ 0 ∧
    RatFunc.eval (RingHom.id ℂ) (r : ℂ) (restrictionAtOne F q (p h)) =
      actualDoubleCoefficient F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r h := by
  obtain ⟨R, hR⟩ := exists_rational_double F ζ hζ q S P I μ J rep hrep d φ hφ hcφ h
  have he : R = restrictionAtOne F q (p h) :=
    actual_rational_coefficient_restriction F ζ hζ q S P I μ J rep hrep d φ hφ hcφ p hp h R
      (fun s hs _ _ => (hR s hs).2)
  exact ⟨restriction_regular F q (p h) r hr, he ▸ (hR r hr).2⟩

end
end DedekindZetaZeroFree.KPActualResidueSources
