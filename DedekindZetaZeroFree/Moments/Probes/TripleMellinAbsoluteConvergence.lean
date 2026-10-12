module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.NormOneFourierSheetEstimates
public import DedekindZetaZeroFree.Theta.Unfolding.UnitOrbitNormSummability
public import DedekindZetaZeroFree.CharacterSums.Gauss.Squarefree.PrincipalNormBound

@[expose] public section

namespace DedekindZetaZeroFree
namespace NormalizedProbe
noncomputable section
open scoped NumberField Classical
open MeasureTheory

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

abbrev MellinSeriesIndex (P : PrincipalData A σ η hS) :=
  {u // u ∈ P.frequencies.reps} ×
    (ExteriorSquarefreeIdeal A.cS × A.Exterior × A.Exterior × A.Exterior)

def weightedSeparatedSummand (P : PrincipalData A σ η hS)
    (i : MellinSeriesIndex P) (ξ w z : ℂ) : ℂ :=
  comparisonRealPower
      (FiniteTransform.exteriorNorm A.R.toSubring i.1.val.val : ℝ) (-z) *
    comparisonEulerPoissonSummand F A P.coefficients i.1.val.val ξ w z
      i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2

def separatedSeriesDomain : Set (ℂ × ℂ × ℂ) :=
  {p | 3 / 2 < p.1.re ∧ 2 < p.2.1.re ∧ 1 < p.2.2.re}

def separatedSeriesMajorant (P : PrincipalData A σ η hS)
    (i : MellinSeriesIndex P) (σξ σw σz : ℝ) : ℝ :=
  (A.exteriorNorm i.2.1.val) ^ (1 / 2 - σξ) *
    (A.exteriorNorm i.2.2.1) ^ (2 - 3 * σξ) *
    (A.exteriorNorm i.2.2.2.1) ^ (1 - σw) *
    (A.exteriorNorm i.2.2.2.2) ^ (-6 * σz) *
    (FiniteTransform.exteriorNorm A.R.toSubring i.1.val.val : ℝ) ^ (-σz)

theorem comparisonRealPower_norm (q : ℝ) (hq : 0 < q) (s : ℂ) :
    ‖comparisonRealPower q s‖ = q ^ s.re := by
  rw [comparisonRealPower, Complex.norm_exp, Real.rpow_def_of_pos hq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [mul_comm]

theorem principal_theta_norm (P : PrincipalData A σ η hS) (m : ThetaReflectionData.Row A) :
    ‖P.coefficients.theta m.val‖ = 1 := by
  rw [P.theta_principal]
  exact Circle.norm_coe _

theorem principal_generator_quotient_norm (P : PrincipalData A σ η hS) (I : A.Exterior) :
    (FiniteTransform.exteriorNorm A.R.toSubring (P.coefficients.generator I) : ℝ) =
      A.exteriorNorm I := by
  change (Nat.card (A.R ⧸ Ideal.span {P.coefficients.generator I}) : ℝ) = _
  rw [(P.coefficients.generates I).2, A.exteriorResidue_card]
  rfl

private theorem principalTheta_norm (P : PrincipalData A σ η hS)
    (m : ThetaReflectionData.Row A) : ‖P.coefficients.theta m.val‖ = 1 :=
  principal_theta_norm P m

private theorem generated_norm_eq (P : PrincipalData A σ η hS) (I : A.Exterior) :
    (FiniteTransform.exteriorNorm A.R.toSubring (P.coefficients.generator I) : ℝ) =
      A.exteriorNorm I := principal_generator_quotient_norm P I

private theorem modulus_norm_eq (P : PrincipalData A σ η hS)
    (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) :
    (FiniteTransform.exteriorNorm A.R.toSubring
      (P.coefficients.generator c.val * P.coefficients.generator n ^ 3) : ℝ) =
      A.exteriorNorm c.val * A.exteriorNorm n ^ (3 : ℕ) := by
  let I : A.Exterior := ⟨c.val.val * n.val ^ 3,
    mul_ne_zero c.val.property.1 (pow_ne_zero _ n.property.1),
    (Ideal.mul_sup_eq_of_coprime_left c.val.property.2).trans
      (Ideal.pow_sup_eq_top n.property.2)⟩
  have hg : Ideal.span {P.coefficients.generator c.val * P.coefficients.generator n ^ 3} =
      A.extendIdeal I := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow,
      (P.coefficients.generates c.val).2, (P.coefficients.generates n).2]
    simp [SArithmeticData.extendIdeal, I, Ideal.map_mul, Ideal.map_pow]
  unfold FiniteTransform.exteriorNorm
  change (Nat.card (A.R ⧸ Ideal.span {_}) : ℝ) = _
  rw (config := { transparency := .all }) [hg, A.exteriorResidue_card]
  simp [I, SArithmeticData.exteriorNorm, idealNorm, map_mul, map_pow]

private theorem finite_coefficient_bound (P : PrincipalData A σ η hS)
    (c : ExteriorSquarefreeIdeal A.cS) (n s : A.Exterior) (u : A.R) :
    ‖comparisonPoissonFiniteCoefficient F A P.coefficients c n s u‖ ≤
      A.exteriorNorm s * (A.exteriorNorm c.val * A.exteriorNorm n ^ (3 : ℕ)) := by
  let D := P.coefficients
  let a := D.generator c.val * D.generator n ^ 3
  letI := D.finiteResidue (D.generator s) (D.generates s).1
  letI := D.finiteResidue a (mul_ne_zero (D.generates c.val).1 (pow_ne_zero _ (D.generates n).1))
  have he (x : F) : ‖D.additiveCharacter x‖ = 1 := by
    rw [P.sameTrace]
    simp [ProbeAdditive.phase, ProbeAdditive.archPhase, norm_mul, norm_prod, Complex.norm_exp]
  have h := FiniteTransform.finiteCoefficient_norm_le A.R.toSubring (D.generator s) a u
    (D.character (D.generator s)) (D.character a) D.additiveCharacter he
  rw [generated_norm_eq P s, modulus_norm_eq P c n] at h
  exact h

theorem weightedSeparatedSummand_norm_le (P : PrincipalData A σ η hS)
    (i : MellinSeriesIndex P) (ξ w z : ℂ) :
    ‖weightedSeparatedSummand P i ξ w z‖ ≤
      separatedSeriesMajorant P i ξ.re w.re z.re := by
  let c := i.2.1
  let n := i.2.2.1
  let s := i.2.2.2.1
  let r := i.2.2.2.2
  have hc := A.exteriorNorm_pos c.val
  have hn := A.exteriorNorm_pos n
  have hs := A.exteriorNorm_pos s
  have hr := A.exteriorNorm_pos r
  letI := P.coefficients.finiteResidue i.1.val.val i.1.val.property
  have hu : 0 < (FiniteTransform.exteriorNorm A.R.toSubring i.1.val.val : ℝ) := by
    exact_mod_cast (show 0 < FiniteTransform.exteriorNorm A.R.toSubring i.1.val.val from by
      simp only [FiniteTransform.exteriorNorm, Nat.card_eq_fintype_card]
      exact Fintype.card_pos)
  have hpow (q : ℝ) (hq : 0 < q) (t : ℂ) : ‖comparisonRealPower q t‖ = q ^ t.re := by
    rw [comparisonRealPower, Complex.norm_exp, Complex.mul_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.ofReal_re, Real.rpow_def_of_pos hq, mul_comm]
  have htheta : ‖P.coefficients.theta (P.coefficients.generator c.val *
      P.coefficients.generator n ^ 3)‖ = 1 := principalTheta_norm P
        ⟨_, mul_ne_zero (P.coefficients.generates c.val).1 (pow_ne_zero _ (P.coefficients.generates n).1)⟩
  have hg := PrincipalData.norm_gammaTwo_le_one A σ η hS P c
  have hf := finite_coefficient_bound P c n s (i.1.val.val * P.coefficients.generator r ^ 6)
  unfold weightedSeparatedSummand comparisonEulerPoissonSummand
  change ‖comparisonRealPower _ (-z) * (P.coefficients.gammaTwo c *
    P.coefficients.theta _ * comparisonPoissonFiniteCoefficient F A P.coefficients c n s _ *
    comparisonRealPower (A.exteriorNorm c.val) (-1 / 2 - ξ) *
    comparisonRealPower (A.exteriorNorm n) (-1 - 3 * ξ) *
    comparisonRealPower (A.exteriorNorm s) (-w) *
    comparisonRealPower (A.exteriorNorm r) (-6 * z))‖ ≤ _
  simp only [norm_mul, htheta, mul_one, hpow _ hu, hpow _ hc, hpow _ hn, hpow _ hs, hpow _ hr]
  have he : (FiniteTransform.exteriorNorm A.R.toSubring i.1.val.val : ℝ) ^ (-z).re *
      (1 * (A.exteriorNorm s * (A.exteriorNorm c.val * A.exteriorNorm n ^ (3 : ℕ))) *
      A.exteriorNorm c.val ^ (-1 / 2 - ξ).re * A.exteriorNorm n ^ (-1 - 3 * ξ).re *
      A.exteriorNorm s ^ (-w).re * A.exteriorNorm r ^ (-6 * z).re) =
      separatedSeriesMajorant P i ξ.re w.re z.re := by
    have hec : A.exteriorNorm c.val * A.exteriorNorm c.val ^ (-1 / 2 - ξ).re =
        A.exteriorNorm c.val ^ (1 / 2 - ξ.re) := by
      nth_rw 1 [← Real.rpow_one (A.exteriorNorm c.val)]
      rw [← Real.rpow_add hc]
      congr 1
      norm_num [Complex.sub_re, Complex.div_re, Complex.mul_re]
      ring
    have hen : A.exteriorNorm n ^ (3 : ℕ) * A.exteriorNorm n ^ (-1 - 3 * ξ).re =
        A.exteriorNorm n ^ (2 - 3 * ξ.re) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hn]
      congr 1
      norm_num [Complex.sub_re, Complex.div_re, Complex.mul_re]
      ring
    have hes : A.exteriorNorm s * A.exteriorNorm s ^ (-w).re =
        A.exteriorNorm s ^ (1 - w.re) := by
      nth_rw 1 [← Real.rpow_one (A.exteriorNorm s)]
      rw [← Real.rpow_add hs]
      congr 1
    calc
      _ = (A.exteriorNorm c.val * A.exteriorNorm c.val ^ (-1 / 2 - ξ).re) *
        (A.exteriorNorm n ^ (3 : ℕ) * A.exteriorNorm n ^ (-1 - 3 * ξ).re) *
        (A.exteriorNorm s * A.exteriorNorm s ^ (-w).re) *
        A.exteriorNorm r ^ (-6 * z).re *
        (FiniteTransform.exteriorNorm A.R.toSubring i.1.val.val : ℝ) ^ (-z).re := by ring
      _ = _ := by
        rw [hec, hen, hes]
        simp [separatedSeriesMajorant, c, n, s, r, Complex.mul_re]
  rw [← he]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hu.le _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr.le _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hs.le _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn.le _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hc.le _)
  have htheta' : ‖P.coefficients.theta (P.coefficients.generator i.2.1.val *
      P.coefficients.generator i.2.2.1 ^ 3)‖ = 1 := htheta
  simpa only [htheta', mul_one] using mul_le_mul hg hf (norm_nonneg _) zero_le_one

private theorem frequency_orbit_injective (P : PrincipalData A σ η hS) : Function.Injective
    (fun u : {u // u ∈ P.frequencies.reps} => ProbeOrbitNormSum.orbitMk A u.val) := by
  intro u v huv
  have h := Quotient.exact huv
  obtain ⟨γ, heq⟩ := MulAction.orbitRel_apply.mp h
  obtain ⟨δ, hδ⟩ := γ.property
  let I : A.Exterior := ⟨⊤, top_ne_bot, by simp⟩
  let r := P.coefficients.generator I
  have hr := (P.coefficients.generates I).1
  let m : ThetaReflectionData.Row A := ⟨u.val.val * r ^ 6, mul_ne_zero u.val.property (pow_ne_zero _ hr)⟩
  obtain ⟨x, hx, hxuniq⟩ := P.frequencies.factorization m
  have hg : P.allowed.generator I = ThetaReflectionData.rowUnit A ⟨r, hr⟩ := by
    apply Units.ext
    exact P.sameGenerator I
  have hu : ∃ γ : A.U, ThetaReflectionData.rowUnit A m =
      ThetaReflectionData.rowUnit A u.val * P.allowed.generator I ^ 6 * γ.val ^ 6 := by
    refine ⟨1, ?_⟩
    rw [hg]
    apply Units.ext
    simp [m, r, ThetaReflectionData.rowUnit]
  have hv : ∃ γ : A.U, ThetaReflectionData.rowUnit A m =
      ThetaReflectionData.rowUnit A v.val * P.allowed.generator I ^ 6 * γ.val ^ 6 := by
    refine ⟨δ, ?_⟩
    rw [hg]
    have huu := congrArg (fun x : ThetaReflectionData.Row A => (x.val : F)) heq
    have hδF := congrArg (fun x : A.U => (x.val : F)) hδ
    apply Units.ext
    simp only [m, ThetaReflectionData.rowUnit, Units.val_mk0, map_mul, map_pow]
    change (u.val.val : F) * (r : F) ^ 6 = (v.val.val : F) * (r : F) ^ 6 * (δ.val : F) ^ 6
    change ((A.unitEquiv γ.val : A.R) : F) * (v.val.val : F) = (u.val.val : F) at huu
    have hcoe : ((A.unitEquiv γ.val : A.R) : F) = (γ.val.val : F) := by
      simp [SArithmeticData.unitEquiv, Set.unitEquivUnitsInteger]
    rw [hcoe, ← hδF] at huu
    change (δ.val : F) ^ 6 * (v.val.val : F) = (u.val.val : F) at huu
    rw [← huu]
    ring
  have he : (u, I) = (v, I) := (hxuniq _ hu).trans (hxuniq _ hv).symm
  exact congrArg Prod.fst he

private theorem frequency_norm_summable (P : PrincipalData A σ η hS)
    (z : ℝ) (hz : 1 < z) : Summable (fun u : {u // u ∈ P.frequencies.reps} =>
      (FiniteTransform.exteriorNorm A.R.toSubring u.val.val : ℝ) ^ (-z)) := by
  have he (u : {u // u ∈ P.frequencies.reps}) :
      (FiniteTransform.exteriorNorm A.R.toSubring u.val.val : ℝ) =
        ProbeOrbitNormSum.orbitNorm A (ProbeOrbitNormSum.orbitMk A u.val) := by
    unfold FiniteTransform.exteriorNorm ProbeOrbitNormSum.orbitNorm
    rw [ProbeOrbitNormSum.orbitIdeal_mk]
    change (Nat.card (A.R ⧸ Ideal.span {u.val.val}) : ℝ) =
      A.exteriorNorm (ProbeOrbitNormSum.principalExterior A u.val)
    rw [(ProbeOrbitNormSum.principalExterior_generates A u.val).2,
      A.exteriorResidue_card]
    rfl
  simp_rw [he]
  exact (ProbeOrbitNormSum.orbit_norm_rpow_summable A z hz).comp_injective
    (frequency_orbit_injective P)

theorem weightedSeparatedSummand_continuous (P : PrincipalData A σ η hS)
    (i : MellinSeriesIndex P) :
    Continuous (fun p : ℂ × ℂ × ℂ => weightedSeparatedSummand P i p.1 p.2.1 p.2.2) := by
  unfold weightedSeparatedSummand comparisonEulerPoissonSummand comparisonRealPower
  fun_prop

theorem separatedSeriesMajorant_summable (P : PrincipalData A σ η hS)
    (σξ σw σz : ℝ) (hξ : 3 / 2 < σξ) (hw : 2 < σw) (hz : 1 < σz) :
    Summable (fun i : MellinSeriesIndex P =>
      separatedSeriesMajorant P i σξ σw σz) := by
  have hc : Summable (fun c : ExteriorSquarefreeIdeal A.cS =>
      A.exteriorNorm c.val ^ (1 / 2 - σξ)) := by
    let f : ExteriorSquarefreeIdeal A.cS → A.Exterior := Subtype.val
    have hf : Function.Injective f := Subtype.val_injective
    have h := (ProbeExteriorIdealCount.ideal_norm_summable F A.cS
      (σξ - 1 / 2) (by linarith)).comp_injective hf
    have hexp : -(σξ - 1 / 2) = 1 / 2 - σξ := by ring
    simpa only [hexp, Function.comp_def] using h
  have hn : Summable (fun n : A.Exterior => A.exteriorNorm n ^ (2 - 3 * σξ)) := by
    have h := ProbeExteriorIdealCount.ideal_norm_summable F A.cS
      (3 * σξ - 2) (by linarith)
    convert h using 1 <;> dsimp <;> try { funext i; congr 1 <;> ring }
  have hs : Summable (fun s : A.Exterior => A.exteriorNorm s ^ (1 - σw)) := by
    have h := ProbeExteriorIdealCount.ideal_norm_summable F A.cS
      (σw - 1) (by linarith)
    convert h using 1 <;> dsimp <;> try { funext i; congr 1 <;> ring }
  have hr : Summable (fun r : A.Exterior => A.exteriorNorm r ^ (-6 * σz)) := by
    have h := ProbeExteriorIdealCount.ideal_norm_summable F A.cS
      (6 * σz) (by linarith)
    convert h using 1 <;> dsimp <;> try { funext i; congr 1 <;> ring }
  have hu := frequency_norm_summable P σz hz
  have h0 (I : A.Exterior) (t : ℝ) : 0 ≤ A.exteriorNorm I ^ t :=
    Real.rpow_nonneg (A.exteriorNorm_pos I).le _
  have hsr := hs.mul_of_nonneg hr (fun _ => h0 _ _) (fun _ => h0 _ _)
  have hnsr := hn.mul_of_nonneg hsr (fun _ => h0 _ _)
    (fun _ => mul_nonneg (h0 _ _) (h0 _ _))
  have hcn := hc.mul_of_nonneg hnsr (fun _ => h0 _ _)
    (fun _ => mul_nonneg (h0 _ _) (mul_nonneg (h0 _ _) (h0 _ _)))
  have hfull := hu.mul_of_nonneg hcn (fun _ => Real.rpow_nonneg (by positivity) _)
    (fun _ => mul_nonneg (h0 _ _) (mul_nonneg (h0 _ _) (mul_nonneg (h0 _ _) (h0 _ _))))
  convert hfull using 1
  funext i
  unfold separatedSeriesMajorant
  dsimp
  ring

private theorem majorant_antitone (P : PrincipalData A σ η hS)
    (i : MellinSeriesIndex P) {a b c a' b' c' : ℝ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    separatedSeriesMajorant P i a' b' c' ≤ separatedSeriesMajorant P i a b c := by
  have hn : ∀ I : A.Exterior, 1 ≤ A.exteriorNorm I := by
    intro I
    have hpos := A.exteriorNorm_pos I
    change 0 < (Ideal.absNorm I.val : ℝ) at hpos
    change (1 : ℝ) ≤ (Ideal.absNorm I.val : ℝ)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (show Ideal.absNorm I.val ≠ 0 by exact_mod_cast ne_of_gt hpos))
  letI := P.coefficients.finiteResidue i.1.val.val i.1.val.property
  have hu : (1 : ℝ) ≤ (FiniteTransform.exteriorNorm A.R.toSubring i.1.val.val : ℝ) := by
    simp only [FiniteTransform.exteriorNorm, Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty
      (FiniteTransform.Residue A.R.toSubring i.1.val.val))
  unfold separatedSeriesMajorant
  apply mul_le_mul
  · apply mul_le_mul
    · apply mul_le_mul
      · apply mul_le_mul
        · exact Real.rpow_le_rpow_of_exponent_le (hn _) (by linarith)
        · exact Real.rpow_le_rpow_of_exponent_le (hn _) (by linarith)
        · exact Real.rpow_nonneg (A.exteriorNorm_pos _).le _
        · exact Real.rpow_nonneg (A.exteriorNorm_pos _).le _
      · exact Real.rpow_le_rpow_of_exponent_le (hn _) (by linarith)
      · exact Real.rpow_nonneg (A.exteriorNorm_pos _).le _
      · exact mul_nonneg (Real.rpow_nonneg (A.exteriorNorm_pos _).le _)
          (Real.rpow_nonneg (A.exteriorNorm_pos _).le _)
    · exact Real.rpow_le_rpow_of_exponent_le (hn _) (by linarith)
    · exact Real.rpow_nonneg (A.exteriorNorm_pos _).le _
    · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (A.exteriorNorm_pos _).le _)
        (Real.rpow_nonneg (A.exteriorNorm_pos _).le _))
        (Real.rpow_nonneg (A.exteriorNorm_pos _).le _)
  · exact Real.rpow_le_rpow_of_exponent_le hu (by linarith)
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (A.exteriorNorm_pos _).le _)
      (Real.rpow_nonneg (A.exteriorNorm_pos _).le _))
      (Real.rpow_nonneg (A.exteriorNorm_pos _).le _))
      (Real.rpow_nonneg (A.exteriorNorm_pos _).le _)

theorem separatedSeries_absolute_locallyUniform (P : PrincipalData A σ η hS) :
    (∀ p ∈ separatedSeriesDomain,
      Summable (fun i : MellinSeriesIndex P =>
        ‖weightedSeparatedSummand P i p.1 p.2.1 p.2.2‖)) ∧
    SummableLocallyUniformlyOn
      (fun (i : MellinSeriesIndex P) (p : ℂ × ℂ × ℂ) =>
        weightedSeparatedSummand P i p.1 p.2.1 p.2.2) separatedSeriesDomain ∧
    SummableLocallyUniformlyOn
      (fun (i : MellinSeriesIndex P) (p : ℂ × ℂ × ℂ) =>
        ‖weightedSeparatedSummand P i p.1 p.2.1 p.2.2‖) separatedSeriesDomain := by
  have habs : ∀ p ∈ separatedSeriesDomain,
      Summable (fun i : MellinSeriesIndex P =>
        ‖weightedSeparatedSummand P i p.1 p.2.1 p.2.2‖) := by
    intro p hp
    exact (separatedSeriesMajorant_summable P _ _ _ hp.1 hp.2.1 hp.2.2).of_nonneg_of_le
      (fun i => norm_nonneg _) (fun i => weightedSeparatedSummand_norm_le P i _ _ _)
  refine ⟨habs, ?_, ?_⟩
  all_goals
    apply summableLocallyUniformlyOn_of_of_forall_exists_nhds
    intro p hp
    let a := ((3 / 2 : ℝ) + p.1.re) / 2
    let b := ((2 : ℝ) + p.2.1.re) / 2
    let c := ((1 : ℝ) + p.2.2.re) / 2
    have ha : 3 / 2 < a ∧ a < p.1.re := by dsimp [a]; constructor <;> linarith [hp.1]
    have hb : 2 < b ∧ b < p.2.1.re := by dsimp [b]; constructor <;> linarith [hp.2.1]
    have hc : 1 < c ∧ c < p.2.2.re := by dsimp [c]; constructor <;> linarith [hp.2.2]
    let U : Set (ℂ × ℂ × ℂ) := {q | a < q.1.re ∧ b < q.2.1.re ∧ c < q.2.2.re}
    have hU : U ∈ nhds p := by
      refine IsOpen.mem_nhds (s := U) ?_ (show p ∈ U from ⟨ha.2, hb.2, hc.2⟩)
      exact (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
        ((isOpen_lt continuous_const (Complex.continuous_re.comp
          (continuous_fst.comp continuous_snd))).inter
        (isOpen_lt continuous_const (Complex.continuous_re.comp
          (continuous_snd.comp continuous_snd))))
    refine ⟨U, nhdsWithin_le_nhds hU, ?_⟩
    apply HasSumUniformlyOn.summableUniformlyOn
    apply HasSumUniformlyOn.of_norm_le_summable
      (separatedSeriesMajorant_summable P a b c ha.1 hb.1 hc.1)
    intro i q hq
    have hh := (weightedSeparatedSummand_norm_le P i q.1 q.2.1 q.2.2).trans
      (majorant_antitone P i hq.1.le hq.2.1.le hq.2.2.le)
    simpa only [Real.norm_eq_abs, abs_norm] using hh

theorem separatedSeries_eq_grouped (P : PrincipalData A σ η hS)
    (ξ w z : ℂ) (hξ : 3 / 2 < ξ.re) (hw : 2 < w.re) (hz : 1 < z.re) :
    (∑' i : MellinSeriesIndex P, weightedSeparatedSummand P i ξ w z) =
      ∑' u : {u // u ∈ P.frequencies.reps},
        comparisonRealPower
            (FiniteTransform.exteriorNorm A.R.toSubring u.val.val : ℝ) (-z) *
          principalSeparatedMellinSeries A σ η hS P u ξ w z := by
  obtain ⟨habs, -, -⟩ := separatedSeries_absolute_locallyUniform P
  have hnorm : Summable (fun i : MellinSeriesIndex P =>
      ‖weightedSeparatedSummand P i ξ w z‖) := habs (ξ, w, z) ⟨hξ, hw, hz⟩
  rw [show (∑' i : MellinSeriesIndex P, weightedSeparatedSummand P i ξ w z) =
      ∑' p : {u // u ∈ P.frequencies.reps} × (ExteriorSquarefreeIdeal A.cS ×
          A.Exterior × A.Exterior × A.Exterior), weightedSeparatedSummand P p ξ w z
        from rfl]
  rw [(Summable.of_norm hnorm).tsum_prod' (fun u =>
    Summable.of_norm (hnorm.comp_injective (fun a b h => congrArg Prod.snd h)))]
  apply tsum_congr
  intro u
  simp only [weightedSeparatedSummand, principalSeparatedMellinSeries, separatedMellinSeries,
    comparisonEulerPoissonSeries]
  rw [tsum_mul_left]

def initialMellinPoint (t : ℝ × ℝ × ℝ) : ℂ × ℂ × ℂ :=
  ((4 : ℂ) + (t.1 : ℂ) * Complex.I,
    (4 : ℂ) + (t.2.1 : ℂ) * Complex.I,
    (2 : ℂ) + (t.2.2 : ℂ) * Complex.I)

def tripleMellinWeight (P : PrincipalData A σ η hS)
    (X Y Z : ℝ) (ξ w z : ℂ) : ℂ := by
  letI : MeasurableSpace (SLocalProduct F A.Sf) := borel _
  exact comparisonRealPower X (1 / 2 - z) *
    comparisonRealPower Z (ξ + z - 1) * comparisonRealPower Y (w - 1) *
    Complex.exp ((ξ + z - 1) ^ 2) *
    ProbeWeight.fourierMellin F A.Sf P.finiteTrace P.additiveMeasure
      P.multiplicativeMeasure P.W0 z * probeRealWeightMellin P.W1 w

def initialTripleMellinSummand (P : PrincipalData A σ η hS)
    (X Y Z : ℝ) (i : MellinSeriesIndex P) (t : ℝ × ℝ × ℝ) : ℂ :=
  let p := initialMellinPoint t
  tripleMellinWeight P X Y Z p.1 p.2.1 p.2.2 *
    weightedSeparatedSummand P i p.1 p.2.1 p.2.2

def initialAbsoluteMellinMajorant (P : PrincipalData A σ η hS)
    (X Y Z : ℝ) (t : ℝ × ℝ × ℝ) : ℝ :=
  let p := initialMellinPoint t
  ‖tripleMellinWeight P X Y Z p.1 p.2.1 p.2.2‖ *
    ∑' i : MellinSeriesIndex P, ‖weightedSeparatedSummand P i p.1 p.2.1 p.2.2‖

theorem tripleMellinWeight_integrable_of_nontrivialTrace (P : PrincipalData A σ η hS) (hne : ∀ v, P.finiteTrace v ≠ 1)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Integrable (fun t : ℝ × ℝ × ℝ => tripleMellinWeight P X Y Z
      (initialMellinPoint t).1 (initialMellinPoint t).2.1 (initialMellinPoint t).2.2) := by
  letI : MeasurableSpace (SLocalProduct F A.Sf) := borel _
  letI : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩
  let w0 : NumberField.InfinitePlace F := Classical.arbitrary _
  obtain ⟨dt, hdt, hdis, hest⟩ := probe_sheet_mellin_estimates F A P.finiteTrace
    P.continuousTrace P.traceCompatible hne P.additiveMeasure P.multiplicativeMeasure
    P.additiveHaar P.multiplicativeHaar w0 P.W0 P.W1 P.annular P.compactSupport P.supportUnits
  rcases hest with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  let M := ProbeWeight.fourierMellin F A.Sf P.finiteTrace P.additiveMeasure P.multiplicativeMeasure P.W0
  let W := probeRealWeightMellin P.W1
  have hM : comparisonRapidStripDecay M 2 2 := by
    intro B hB
    obtain ⟨C,hC,h⟩ := h5 2 2 B (by norm_num) le_rfl hB
    refine ⟨C + 1, by linarith, ?_⟩
    intro s hs
    have hsre : s.re = 2 := le_antisymm hs.2 hs.1
    have hh := h 2 (by simp) s.im
    have he : (2 : ℂ) + (s.im : ℂ) * Complex.I = s := by
      apply Complex.ext <;> simp [hsre]
    norm_num only [Complex.ofReal_ofNat] at hh
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hW : comparisonRapidStripDecay W 4 4 := by
    intro B hB
    obtain ⟨C,hC,h⟩ := h7 4 4 B le_rfl hB
    refine ⟨C + 1, by linarith, ?_⟩
    intro s hs
    have hsre : s.re = 4 := le_antisymm hs.2 hs.1
    have hh := h 4 (by simp) s.im
    have he : (4 : ℂ) + (s.im : ℂ) * Complex.I = s := by
      apply Complex.ext <;> simp [hsre]
    norm_num only [Complex.ofReal_ofNat] at hh
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  obtain ⟨C,hC,hbound⟩ := comparisonGaussianMellinWeight_polynomial_bound M W
    4 4 4 4 2 2 2 0 0 le_rfl le_rfl le_rfl (by norm_num) (by norm_num)
    le_rfl le_rfl hM hW
  have hm : Continuous (fun t : ℝ × ℝ × ℝ => M (initialMellinPoint t).2.2) :=
    h4.continuousOn.comp_continuous (by unfold initialMellinPoint; fun_prop)
      (by intro t; norm_num [initialMellinPoint])
  have hw : Continuous (fun t : ℝ × ℝ × ℝ => W (initialMellinPoint t).2.1) :=
    h6.continuous.comp (by unfold initialMellinPoint; fun_prop)
  have hcont : Continuous (fun t : ℝ × ℝ × ℝ => tripleMellinWeight P X Y Z
      (initialMellinPoint t).1 (initialMellinPoint t).2.1 (initialMellinPoint t).2.2) := by
    change Continuous (fun t => comparisonRealPower X (1 / 2 - (initialMellinPoint t).2.2) *
      comparisonRealPower Z ((initialMellinPoint t).1 + (initialMellinPoint t).2.2 - 1) *
      comparisonRealPower Y ((initialMellinPoint t).2.1 - 1) *
      Complex.exp (((initialMellinPoint t).1 + (initialMellinPoint t).2.2 - 1)^2) *
      M (initialMellinPoint t).2.2 * W (initialMellinPoint t).2.1)
    apply Continuous.mul _ hw
    apply Continuous.mul _ hm
    unfold comparisonRealPower initialMellinPoint
    fun_prop
  have hpow (q : ℝ) (hq : 0 < q) (s : ℂ) : ‖comparisonRealPower q s‖ = q ^ s.re := by
    rw [comparisonRealPower, Complex.norm_exp, Complex.mul_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.ofReal_re, Real.rpow_def_of_pos hq, mul_comm]
  apply ((comparisonHeightEnvelope_integrable 0 le_rfl).const_mul
    (X ^ (-(3 / 2 : ℝ)) * Z ^ (5 : ℝ) * Y ^ (3 : ℝ) * C)).mono' hcont.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  have hp : (initialMellinPoint t).1 ∈ comparisonClosedStrip 4 4 ∧
      (initialMellinPoint t).2.1 ∈ comparisonClosedStrip 4 4 ∧
      (initialMellinPoint t).2.2 ∈ comparisonClosedStrip 2 2 := by
    norm_num [initialMellinPoint, comparisonClosedStrip]
  have hh := hbound _ _ _ hp.1 hp.2.1 hp.2.2
  simp only [Real.rpow_zero, mul_one] at hh
  have hn : ‖tripleMellinWeight P X Y Z (initialMellinPoint t).1
      (initialMellinPoint t).2.1 (initialMellinPoint t).2.2‖ =
      X ^ (-(3 / 2 : ℝ)) * Z ^ (5 : ℝ) * Y ^ (3 : ℝ) *
      ‖comparisonGaussianMellinWeight M W (initialMellinPoint t).1
        (initialMellinPoint t).2.1 (initialMellinPoint t).2.2‖ := by
    change ‖comparisonRealPower X (1 / 2 - (initialMellinPoint t).2.2) *
      comparisonRealPower Z ((initialMellinPoint t).1 + (initialMellinPoint t).2.2 - 1) *
      comparisonRealPower Y ((initialMellinPoint t).2.1 - 1) *
      Complex.exp (((initialMellinPoint t).1 + (initialMellinPoint t).2.2 - 1)^2) *
      M (initialMellinPoint t).2.2 * W (initialMellinPoint t).2.1‖ = _
    simp only [norm_mul, hpow X hX, hpow Z hZ, hpow Y hY, comparisonGaussianMellinWeight]
    norm_num [initialMellinPoint, norm_mul]
    ring
  rw [hn]
  have hnonneg : 0 ≤ X ^ (-(3 / 2 : ℝ)) * Z ^ (5 : ℝ) * Y ^ (3 : ℝ) := by positivity
  have hh' := mul_le_mul_of_nonneg_left hh hnonneg
  simpa [initialMellinPoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_zero, zero_mul, zero_add, add_zero,
    mul_one, mul_assoc, Complex.natCast_im] using hh'

private theorem mellinSeriesIndex_countable (P : PrincipalData A σ η hS) :
    Countable (MellinSeriesIndex P) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have he := (ProbeExteriorIdealCount.ideal_norm_summable F A.cS 2 (by norm_num)).countable_support
  have hall : Function.support (fun I : A.Exterior => (idealNorm I.val) ^ (-(2 : ℝ))) =
      Set.univ := by
    ext I
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (A.exteriorNorm_pos I) _).ne'
  rw [hall] at he
  letI : Countable A.Exterior := Set.countable_univ_iff.mp he
  change Countable ({u // u ∈ P.frequencies.reps} ×
    ({I : A.Exterior // Squarefree I.val} × A.Exterior × A.Exterior × A.Exterior))
  letI : Countable A.R := inferInstance
  exact inferInstance

theorem tripleMellin_majorant_of_integrable_weight (P : PrincipalData A σ η hS)
    (X Y Z : ℝ)
    (hweight : Integrable (fun t : ℝ × ℝ × ℝ =>
      tripleMellinWeight P X Y Z (initialMellinPoint t).1
        (initialMellinPoint t).2.1 (initialMellinPoint t).2.2)) :
    Integrable (initialAbsoluteMellinMajorant P X Y Z) ∧
    (∀ i : MellinSeriesIndex P, Integrable (initialTripleMellinSummand P X Y Z i)) ∧
    Summable (fun i : MellinSeriesIndex P =>
      ∫ t : ℝ × ℝ × ℝ, ‖initialTripleMellinSummand P X Y Z i t‖) := by
  letI : Countable (MellinSeriesIndex P) := mellinSeriesIndex_countable P
  let weight := fun t : ℝ × ℝ × ℝ => tripleMellinWeight P X Y Z
    (initialMellinPoint t).1 (initialMellinPoint t).2.1 (initialMellinPoint t).2.2
  let term := fun (i : MellinSeriesIndex P) (t : ℝ × ℝ × ℝ) =>
    weightedSeparatedSummand P i (initialMellinPoint t).1
      (initialMellinPoint t).2.1 (initialMellinPoint t).2.2
  let bound := fun i : MellinSeriesIndex P => separatedSeriesMajorant P i 4 4 2
  have hb : Summable bound := separatedSeriesMajorant_summable P 4 4 2
    (by norm_num) (by norm_num) (by norm_num)
  have hb0 (i : MellinSeriesIndex P) : 0 ≤ bound i := by
    dsimp [bound, separatedSeriesMajorant]
    have hc := (A.exteriorNorm_pos i.2.1.val).le
    have hn := (A.exteriorNorm_pos i.2.2.1).le
    have hs := (A.exteriorNorm_pos i.2.2.2.1).le
    have hr := (A.exteriorNorm_pos i.2.2.2.2).le
    positivity
  have hterm (i : MellinSeriesIndex P) (t : ℝ × ℝ × ℝ) : ‖term i t‖ ≤ bound i := by
    simpa [term, bound, initialMellinPoint] using
      weightedSeparatedSummand_norm_le P i (initialMellinPoint t).1
        (initialMellinPoint t).2.1 (initialMellinPoint t).2.2
  have hm (i : MellinSeriesIndex P) : AEStronglyMeasurable (term i) := by
    exact ((weightedSeparatedSummand_continuous P i).comp
      (by unfold initialMellinPoint; fun_prop)).aestronglyMeasurable
  have hn (t : ℝ × ℝ × ℝ) : Summable (fun i : MellinSeriesIndex P => ‖term i t‖) :=
    hb.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hterm i t)
  have hi (i : MellinSeriesIndex P) : Integrable (initialTripleMellinSummand P X Y Z i) := by
    apply (hweight.norm.const_mul (bound i)).mono'
      (hweight.aestronglyMeasurable.mul (hm i))
    apply Filter.Eventually.of_forall
    intro t
    change ‖weight t * term i t‖ ≤ bound i * ‖weight t‖
    rw [norm_mul, mul_comm (bound i)]
    exact mul_le_mul_of_nonneg_left (hterm i t) (norm_nonneg _)
  refine ⟨?_, hi, ?_⟩
  · apply (hweight.norm.const_mul (∑' i, bound i)).mono'
      (hweight.aestronglyMeasurable.norm.mul (AEStronglyMeasurable.tsum (fun i => (hm i).norm)))
    apply Filter.Eventually.of_forall
    intro t
    change ‖‖weight t‖ * ∑' i, ‖term i t‖‖ ≤ (∑' i, bound i) * ‖weight t‖
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (tsum_nonneg (fun _ => norm_nonneg _))),
      mul_comm (∑' i, bound i)]
    exact mul_le_mul_of_nonneg_left ((hn t).tsum_le_tsum (fun i => hterm i t) hb) (norm_nonneg _)
  · apply (hb.mul_right (∫ t, ‖weight t‖)).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    intro i
    calc
      (∫ t, ‖initialTripleMellinSummand P X Y Z i t‖) ≤
          ∫ t, bound i * ‖weight t‖ :=
        integral_mono (hi i).norm (hweight.norm.const_mul (bound i)) (fun t => by
          change ‖weight t * term i t‖ ≤ bound i * ‖weight t‖
          rw [norm_mul, mul_comm (bound i)]
          exact mul_le_mul_of_nonneg_left (hterm i t) (norm_nonneg _))
      _ = bound i * ∫ t, ‖weight t‖ := integral_const_mul _ _

theorem tripleMellin_integrable_majorant_of_nontrivialTrace (P : PrincipalData A σ η hS)
    (hne : ∀ v, P.finiteTrace v ≠ 1)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Integrable (initialAbsoluteMellinMajorant P X Y Z) ∧
    (∀ i : MellinSeriesIndex P, Integrable (initialTripleMellinSummand P X Y Z i)) ∧
    Summable (fun i : MellinSeriesIndex P =>
      ∫ t : ℝ × ℝ × ℝ, ‖initialTripleMellinSummand P X Y Z i t‖) :=
  tripleMellin_majorant_of_integrable_weight P X Y Z
    (tripleMellinWeight_integrable_of_nontrivialTrace P hne X Y Z hX hY hZ)

theorem tripleMellin_integrable_majorant (P : PrincipalData A σ η hS)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Integrable (initialAbsoluteMellinMajorant P X Y Z) ∧
    (∀ i : MellinSeriesIndex P, Integrable (initialTripleMellinSummand P X Y Z i)) ∧
    Summable (fun i : MellinSeriesIndex P =>
      ∫ t : ℝ × ℝ × ℝ, ‖initialTripleMellinSummand P X Y Z i t‖) := by
  have hne : ∀ v, P.finiteTrace v ≠ 1 := by
    intro v heq
    obtain ⟨x, hx⟩ := PrincipalData.finiteTrace_ne_one A σ η hS P v
    exact hx (by rw [heq]; rfl)
  exact tripleMellin_integrable_majorant_of_nontrivialTrace P hne X Y Z hX hY hZ

theorem tripleMellin_sum_integral_interchange (P : PrincipalData A σ η hS)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Integrable (fun t : ℝ × ℝ × ℝ =>
      ∑' i : MellinSeriesIndex P, initialTripleMellinSummand P X Y Z i t) ∧
    (∫ t : ℝ × ℝ × ℝ,
        ∑' i : MellinSeriesIndex P, initialTripleMellinSummand P X Y Z i t) =
      ∑' i : MellinSeriesIndex P,
        ∫ t : ℝ × ℝ × ℝ, initialTripleMellinSummand P X Y Z i t := by
  letI : Countable (MellinSeriesIndex P) := mellinSeriesIndex_countable P
  obtain ⟨hmajorant, hint, hsum⟩ := tripleMellin_integrable_majorant P X Y Z hX hY hZ
  refine ⟨hmajorant.mono' (AEStronglyMeasurable.tsum (fun i => (hint i).1)) ?_,
    (integral_tsum_of_summable_integral_norm hint hsum).symm⟩
  apply Filter.Eventually.of_forall
  intro t
  have hd : initialMellinPoint t ∈ separatedSeriesDomain := by
    norm_num [initialMellinPoint, separatedSeriesDomain, Complex.mul_re,
      Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
  have hn := (separatedSeries_absolute_locallyUniform P).1 (initialMellinPoint t) hd
  have htn : Summable (fun i : MellinSeriesIndex P =>
      ‖initialTripleMellinSummand P X Y Z i t‖) := by
    simpa only [initialTripleMellinSummand, norm_mul] using
      hn.mul_left (‖tripleMellinWeight P X Y Z (initialMellinPoint t).1
        (initialMellinPoint t).2.1 (initialMellinPoint t).2.2‖)
  calc
    ‖∑' i : MellinSeriesIndex P, initialTripleMellinSummand P X Y Z i t‖ ≤
        ∑' i : MellinSeriesIndex P, ‖initialTripleMellinSummand P X Y Z i t‖ :=
      norm_tsum_le_tsum_norm htn
    _ = initialAbsoluteMellinMajorant P X Y Z t := by
      simp only [initialTripleMellinSummand, initialAbsoluteMellinMajorant, norm_mul,
        tsum_mul_left]

end
end NormalizedProbe
end DedekindZetaZeroFree
