module

public import DedekindZetaZeroFree.LFunctions.Hecke.MaskedMeromorphicContinuation
public import DedekindZetaZeroFree.Moments.Principal.Corrections.CoordinateHolomorphy
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.SeparatedHeckeFactors

@[expose] public section

open scoped NumberField Classical Topology

noncomputable section
namespace DedekindZetaZeroFree.MeromorphicSeparationGluing
set_option autoImplicit false

open LocalFiniteSums CorrectionFactors MaskedHeckeMeromorphic FrequencyCharacterMasks

def initialRegion : Set Coordinates :=
  {x | 4 < x.1.re ∧ 4 < x.2.1.re ∧ 2 < x.2.2.re}

def openPolydisc (c : Coordinates) (r : ℝ × ℝ × ℝ) : Set Coordinates :=
  {x | x.1 ∈ Metric.ball c.1 r.1 ∧
    x.2.1 ∈ Metric.ball c.2.1 r.2.1 ∧ x.2.2 ∈ Metric.ball c.2.2 r.2.2}

def SeparatelyHolomorphicOn (f : Coordinates → ℂ) (S : Set Coordinates) : Prop :=
  (∀ w z : ℂ, DifferentiableOn ℂ (fun ξ => f (ξ, w, z))
    {ξ : ℂ | (ξ, w, z) ∈ S}) ∧
  (∀ ξ z : ℂ, DifferentiableOn ℂ (fun w => f (ξ, w, z))
    {w : ℂ | (ξ, w, z) ∈ S}) ∧
  (∀ ξ w : ℂ, DifferentiableOn ℂ (fun z => f (ξ, w, z))
    {z : ℂ | (ξ, w, z) ∈ S})

def regularLocus (D : Coordinates → ℂ) : Set Coordinates :=
  {x | x ∈ Omega ∧ D x ≠ 0}

def CrossMultipliedOn (N D N' D' : Coordinates → ℂ)
    (S : Set Coordinates) : Prop :=
  ∀ x ∈ S, N x * D' x = N' x * D x

structure GlobalQuotientCertificate (N D G : Coordinates → ℂ) : Prop where
  numerator_continuous : ContinuousOn N Omega
  denominator_continuous : ContinuousOn D Omega
  numerator_separately_holomorphic : SeparatelyHolomorphicOn N Omega
  denominator_separately_holomorphic : SeparatelyHolomorphicOn D Omega
  denominator_not_identically_zero : ∀ (c : Coordinates) (r : ℝ × ℝ × ℝ),
    0 < r.1 → 0 < r.2.1 → 0 < r.2.2 →
    (openPolydisc c r).Nonempty → openPolydisc c r ⊆ Omega →
    ∃ x ∈ openPolydisc c r, D x ≠ 0
  regular_locus_open : IsOpen (regularLocus D)
  initial_cleared_identity : ∀ x ∈ Omega ∩ initialRegion, D x * G x = N x
  initial_regular_equality : ∀ x ∈ regularLocus D ∩ initialRegion, G x = N x / D x

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}

def numerator (U : Frequency C) (P : PrimitiveInducers U)
    (R : ∀ i : Row, RowContinuation U P i) (x : Coordinates) : ℂ :=
  (∏' p : ExteriorPrime A, localFactor C U p x.1 x.2.1 x.2.2) *
    (R .principal).J (6 * x.2.2) * deletionProduct U P .principal (6 * x.2.2) *
    (R .plus).J x.2.1 * deletionProduct U P .plus x.2.1 *
    (x.1 - 1) ^ poleIndicator (primitive U P .minus)

def denominator (U : Frequency C) (P : PrimitiveInducers U)
    (R : ∀ i : Row, RowContinuation U P i) (x : Coordinates) : ℂ :=
  (6 * x.2.2 - 1) * (x.2.1 - 1) ^ poleIndicator (primitive U P .plus) *
    (R .minus).J x.1 * deletionProduct U P .minus x.1

private lemma omega_positive {x : Coordinates} (hx : x ∈ Omega) :
    0 < x.1.re ∧ 0 < x.2.1.re ∧ 0 < (6 * x.2.2).re := by
  rcases hx with hx | hx <;>
    simp only [omegaFirst, omegaSecond, Set.mem_setOf_eq] at hx <;>
    norm_num [Complex.mul_re] at * <;>
    refine ⟨?_, ?_, ?_⟩ <;> linarith [hx.1, hx.2.1, hx.2.2]
private lemma diff_sep {f : Coordinates → ℂ} (hf : DifferentiableOn ℂ f Omega) :
    SeparatelyHolomorphicOn f Omega := by
  refine ⟨?_, ?_, ?_⟩
  · intro w z
    exact hf.comp (differentiable_id.prodMk ((differentiable_const w).prodMk
      (differentiable_const z))).differentiableOn (fun _ h => h)
  · intro ξ z
    exact hf.comp ((differentiable_const ξ).prodMk (differentiable_id.prodMk
      (differentiable_const z))).differentiableOn (fun _ h => h)
  · intro ξ w
    exact hf.comp ((differentiable_const ξ).prodMk ((differentiable_const w).prodMk
      differentiable_id)).differentiableOn (fun _ h => h)
private lemma ball_ne (c a : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ x ∈ Metric.ball c r, x ≠ a := by
  by_cases h : c = a
  · subst c
    have hb : ∀ᶠ x in 𝓝[≠] a, x ∈ Metric.ball a r :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds a hr)
    have hn : ∀ᶠ x in 𝓝[≠] a, x ≠ a := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using hx
    exact (hb.and hn).exists
  · exact ⟨c, Metric.mem_ball_self hr, h⟩
private lemma row_matches (U : Frequency C) (s : ℂ) :
    incompleteL U .principal s = InitialSeparatedEuler.zetaS A s ∧
    incompleteL U .plus s = InitialSeparatedEuler.plusL U s ∧
    incompleteL U .minus s = InitialSeparatedEuler.minusL U s := by
  have hsupport (i : Row) : Function.support (fun I : Ideal (𝓞 F) =>
      coefficient U i I * (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
      {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ A.cS = ⊤} := by
    intro I hI
    by_contra hn
    change ¬ (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) at hn
    apply hI
    cases i <;> simp [coefficient, principalCoefficient, plusCoefficient, minusCoefficient, hn]
  have he (i : Row) := (tsum_subtype_eq_of_support_subset (hsupport i)).symm
  refine ⟨?_, ?_, ?_⟩
  · change incompleteL U .principal s = _
    rw [show incompleteL U .principal s = _ from he .principal]
    unfold InitialSeparatedEuler.zetaS
    apply tsum_congr
    intro I
    simp [coefficient, principalCoefficient, I.property.1, I.property.2]
  · change incompleteL U .plus s = _
    rw [show incompleteL U .plus s = _ from he .plus]
    unfold InitialSeparatedEuler.plusL InitialSeparatedEuler.dirichletSeries
    apply tsum_congr
    intro I
    simp [coefficient, plusCoefficient, I.property.1, I.property.2, InitialSeparatedEuler.plusL,
      InitialSeparatedEuler.dirichletSeries, ExteriorIdealEuler.summand]
  · change incompleteL U .minus s = _
    rw [show incompleteL U .minus s = _ from he .minus]
    unfold InitialSeparatedEuler.minusL InitialSeparatedEuler.dirichletSeries
    apply tsum_congr
    intro I
    simp [coefficient, plusCoefficient, minusCoefficient, I.property.1, I.property.2,
      minusExteriorCoefficient, ExteriorIdealEuler.summand]
private lemma factors_regular (U : Frequency C) (P : PrimitiveInducers U)
    (R : ∀ i : Row, RowContinuation U P i) :
    DifferentiableOn ℂ (fun x : Coordinates =>
      (R .principal).J (6*x.2.2) * deletionProduct U P .principal (6*x.2.2) *
      (R .plus).J x.2.1 * deletionProduct U P .plus x.2.1 *
      (x.1-1)^poleIndicator (primitive U P .minus)) Omega ∧
    DifferentiableOn ℂ (denominator U P R) Omega := by
  have hξ : DifferentiableOn ℂ (fun x : Coordinates => x.1) Omega := differentiable_id.fst.differentiableOn
  have hw : DifferentiableOn ℂ (fun x : Coordinates => x.2.1) Omega := differentiable_id.snd.fst.differentiableOn
  have hz : DifferentiableOn ℂ (fun x : Coordinates => 6*x.2.2) Omega :=
    ((differentiable_const (6 : ℂ)).mul differentiable_id.snd.snd).differentiableOn
  have jξ := (R .minus).J_holomorphic.differentiableOn.comp hξ (fun x hx => (omega_positive hx).1)
  have bξ := (R .minus).B_holomorphic.differentiableOn.comp hξ (fun x hx => (omega_positive hx).1)
  have jw := (R .plus).J_holomorphic.differentiableOn.comp hw (fun x hx => (omega_positive hx).2.1)
  have bw := (R .plus).B_holomorphic.differentiableOn.comp hw (fun x hx => (omega_positive hx).2.1)
  have jz := (R .principal).J_holomorphic.differentiableOn.comp hz (fun x hx => (omega_positive hx).2.2)
  have bz := (R .principal).B_holomorphic.differentiableOn.comp hz (fun x hx => (omega_positive hx).2.2)
  exact ⟨((((jz.mul bz).mul jw).mul bw).mul ((hξ.sub_const 1).pow _)),
    (((hz.sub_const 1).mul ((hw.sub_const 1).pow _)).mul jξ).mul bξ⟩
private lemma denominator_nonzero (U : Frequency C) (P : PrimitiveInducers U)
    (R : ∀ i : Row, RowContinuation U P i) (c : Coordinates) (r : ℝ × ℝ × ℝ)
    (hr1 : 0 < r.1) (hr2 : 0 < r.2.1) (hr3 : 0 < r.2.2)
    (hsub : openPolydisc c r ⊆ Omega) :
    ∃ x ∈ openPolydisc c r, denominator U P R x ≠ 0 := by
  obtain ⟨w, hw, hw1⟩ := ball_ne c.2.1 1 hr2
  obtain ⟨z, hz, hz1⟩ := ball_ne c.2.2 (1/6) hr3
  have hξpos : ∀ ξ ∈ Metric.ball c.1 r.1, 0 < ξ.re := fun ξ hξ =>
    (omega_positive (hsub (show (ξ,w,z) ∈ openPolydisc c r from ⟨hξ, hw, hz⟩))).1
  have hj : ∃ ξ ∈ Metric.ball c.1 r.1, (R .minus).J ξ ≠ 0 := by
    by_contra hn
    have hzero : ∀ ξ ∈ Metric.ball c.1 r.1, (R .minus).J ξ = 0 := by
      simpa only [not_exists, not_and, not_not] using hn
    have heq := (R .minus).J_holomorphic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_re_gt 0).isPreconnected (hξpos c.1 (Metric.mem_ball_self hr1))
      (by filter_upwards [Metric.ball_mem_nhds c.1 hr1] with ξ hξ; exact hzero ξ hξ)
    obtain ⟨s, hs, hns⟩ := (R .minus).J_not_identically_zero
    exact hns (heq hs)
  obtain ⟨ξ, hξ, hjξ⟩ := hj
  refine ⟨(ξ,w,z), ⟨hξ,hw,hz⟩, ?_⟩
  unfold denominator
  have hz6 : 6*z-1 ≠ 0 := by intro he; apply hz1; linear_combination he / 6
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hz6 (pow_ne_zero _ (sub_ne_zero.mpr hw1))) hjξ)
    ((R .minus).B_nowhere_zero ξ (hξpos ξ hξ))
private lemma initial_identity (U : Frequency C) (P : PrimitiveInducers U)
    (R : ∀ i : Row, RowContinuation U P i)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction)
    (x : Coordinates) (hx : x ∈ Omega ∩ initialRegion) :
    denominator U P R x * comparisonEulerPoissonSeries F A D U.u x.1 x.2.1 x.2.2 =
      numerator U P R x := by
  obtain ⟨hξ, hw, hz⟩ := hx.2
  have hz6 : 1 < (6*x.2.2).re := by
    norm_num [Complex.mul_re] at *; linarith
  have he := (InitialSeparatedEuler.initial_separated_euler U D hD x.1 x.2.1 x.2.2 hξ hw hz).2
  rw [← (row_matches U x.1).2.2, ← (row_matches U x.2.1).2.1,
    ← (row_matches U (6*x.2.2)).1] at he
  rw [(R .minus).regular_equality _ (by linarith),
    (R .plus).regular_equality _ (by linarith), (R .principal).regular_equality _ hz6] at he
  unfold quotientRepresentative at he
  rw [principal_indicator] at he
  simp only [pow_one, H_u] at he
  have hnξ : x.1 - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re (sub_eq_zero.mp h); simp at this; linarith
  have hnw : x.2.1 - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re (sub_eq_zero.mp h); simp at this; linarith
  have hnz : 6*x.2.2 - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re (sub_eq_zero.mp h); simp at this; linarith
  field_simp [hnξ, hnw, hnz] at he
  unfold numerator denominator
  linear_combination he

theorem meromorphic_separation_gluing
     (U : Frequency C)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction) :
    ∃ (P : PrimitiveInducers U) (R : ∀ i : Row, RowContinuation U P i),
      GlobalQuotientCertificate (numerator U P R) (denominator U P R)
        (fun x => comparisonEulerPoissonSeries F A D U.u x.1 x.2.1 x.2.2) := by
  obtain ⟨P, hP⟩ := masked_hecke_meromorphic U
  let R : ∀ i : Row, RowContinuation U P i := fun i => Classical.choice (hP i)
  have hreg := factors_regular U P R
  let H : Coordinates → ℂ := fun x => ∏' p : ExteriorPrime A, localFactor C U p x.1 x.2.1 x.2.2
  have hH : ContinuousOn H Omega := by
    exact continuousOn_iff_continuous_restrict.mpr (continuous_H_u C U)
  have hHs : SeparatelyHolomorphicOn H Omega :=
    ⟨differentiableOn_H_u_xi C U, differentiableOn_H_u_w C U, differentiableOn_H_u_z C U⟩
  have hn : ContinuousOn (numerator U P R) Omega := by
    convert hH.mul hreg.1.continuousOn using 1
    ext x
    simp only [numerator, H, Pi.mul_apply]
    ring
  have hns : SeparatelyHolomorphicOn (numerator U P R) Omega := by
    have hs := diff_sep hreg.1
    refine ⟨?_, ?_, ?_⟩
    · intro w z
      convert (hHs.1 w z).mul (hs.1 w z) using 1
      ext ξ
      simp only [numerator, H, Pi.mul_apply]; ring
    · intro ξ z
      convert (hHs.2.1 ξ z).mul (hs.2.1 ξ z) using 1
      ext w
      simp only [numerator, H, Pi.mul_apply]; ring
    · intro ξ w
      convert (hHs.2.2 ξ w).mul (hs.2.2 ξ w) using 1
      ext z
      simp only [numerator, H, Pi.mul_apply]; ring
  refine ⟨P, R, ⟨hn, hreg.2.continuousOn, hns, diff_sep hreg.2, ?_, ?_, ?_, ?_⟩⟩
  · intro c r hr1 hr2 hr3 _ hsub
    exact denominator_nonzero U P R c r hr1 hr2 hr3 hsub
  · exact hreg.2.continuousOn.isOpen_inter_preimage isOpen_Omega (isOpen_compl_singleton)
  · exact initial_identity U P R D hD
  · intro x hx
    exact (eq_div_iff hx.1.2).mpr (by
      rw [mul_comm]; exact initial_identity U P R D hD x ⟨hx.1.1, hx.2⟩)

 def c₁ : ℝ := (499 / 500 : ℝ) - 1 / 100000
 def c₂ : ℝ := (3 / 1000 : ℝ) - 1 / 100000
 def c₃ : ℝ := (2 / 5 : ℝ) - 1 / 100000
 def c₂' : ℝ := (19 / 20 : ℝ) - 1 / 100000
 def c₃' : ℝ := (4 / 25 : ℝ) - 1 / 100000

private lemma c₂_lt_four : c₂ < 4 := by norm_num [c₂]
private lemma c₃_lt_two : c₃ < 2 := by norm_num [c₃]
private lemma c₁_lt_four : c₁ < 4 := by norm_num [c₁]
private lemma c₂_lt_c₂' : c₂ < c₂' := by norm_num [c₂, c₂']
private lemma c₃'_lt_c₃ : c₃' < c₃ := by norm_num [c₃, c₃']
private lemma c₃'_lt_two : c₃' < 2 := by norm_num [c₃']

private lemma mem_omegaFirst {x : Coordinates} :
    x ∈ omegaFirst ↔ c₁ < x.1.re ∧ c₂ < x.2.1.re ∧ c₃ < x.2.2.re := by
  simp [omegaFirst, c₁, c₂, c₃]

private lemma mem_omegaSecond {x : Coordinates} :
    x ∈ omegaSecond ↔ c₁ < x.1.re ∧ c₂' < x.2.1.re ∧ c₃' < x.2.2.re := by
  simp [omegaSecond, c₁, c₂', c₃']

private lemma mem_Omega_iff {x : Coordinates} :
    x ∈ Omega ↔ (c₁ < x.1.re ∧ c₂ < x.2.1.re ∧ c₃ < x.2.2.re) ∨
      (c₁ < x.1.re ∧ c₂' < x.2.1.re ∧ c₃' < x.2.2.re) := by
  rw [Omega, Set.mem_union, mem_omegaFirst, mem_omegaSecond]

private lemma slice_fst {w z : ℂ} (hw : 4 < w.re) (hz : 2 < z.re) :
    {ξ : ℂ | ((ξ, w, z) : Coordinates) ∈ Omega} = {ξ : ℂ | c₁ < ξ.re} := by
  ext ξ
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, mem_Omega_iff]
  constructor
  · intro h
    rcases h with ⟨h1, _, _⟩ | ⟨h1, _, _⟩
    · exact h1
    · exact h1
  · intro h
    exact Or.inl ⟨h, lt_trans c₂_lt_four hw, lt_trans c₃_lt_two hz⟩

private lemma slice_snd {ξ z : ℂ} (hξ : c₁ < ξ.re) (hz : 2 < z.re) :
    {w : ℂ | ((ξ, w, z) : Coordinates) ∈ Omega} = {w : ℂ | c₂ < w.re} := by
  ext w
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, mem_Omega_iff]
  constructor
  · intro h
    rcases h with ⟨_, h1, _⟩ | ⟨_, h1, _⟩
    · exact h1
    · exact lt_trans c₂_lt_c₂' h1
  · intro h
    exact Or.inl ⟨hξ, h, lt_trans c₃_lt_two hz⟩

private lemma slice_trd_first {ξ w : ℂ} (hξ : c₁ < ξ.re) (hw : c₂ < w.re)
    (hw' : ¬ c₂' < w.re) :
    {z : ℂ | ((ξ, w, z) : Coordinates) ∈ Omega} = {z : ℂ | c₃ < z.re} := by
  ext z
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, mem_Omega_iff]
  constructor
  · intro h
    rcases h with ⟨_, _, h1⟩ | ⟨_, h2, _⟩
    · exact h1
    · exact absurd h2 hw'
  · intro h
    exact Or.inl ⟨hξ, hw, h⟩

private lemma slice_trd_second {ξ w : ℂ} (hξ : c₁ < ξ.re) (hw' : c₂' < w.re) :
    {z : ℂ | ((ξ, w, z) : Coordinates) ∈ Omega} = {z : ℂ | c₃' < z.re} := by
  ext z
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, mem_Omega_iff]
  constructor
  · intro h
    rcases h with ⟨_, _, h1⟩ | ⟨_, _, h1⟩
    · exact lt_trans c₃'_lt_c₃ h1
    · exact h1
  · intro h
    exact Or.inr ⟨hξ, hw', h⟩

private lemma eq_zero_on_halfSpace (f : ℂ → ℂ) {c d : ℝ} (hcd : c < d)
    (hdiff : DifferentiableOn ℂ f {s : ℂ | c < s.re})
    (hzero : ∀ s : ℂ, d < s.re → f s = 0) :
    ∀ s : ℂ, c < s.re → f s = 0 := by
  have hT : IsOpen {s : ℂ | c < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hU : IsPreconnected {s : ℂ | c < s.re} := (convex_halfSpace_re_gt c).isPreconnected
  have hmem : ∀ s : ℂ, c < s.re → s ∈ {s : ℂ | c < s.re} := fun s hs => hs
  have hzero' : ∀ s : ℂ, d < s.re → s ∈ {s : ℂ | c < s.re} → f s = 0 :=
    fun s hs _ => hzero s hs
  have hball : {s : ℂ | d < s.re} ∈ 𝓝 (((d + 1 : ℝ)) : ℂ) :=
    IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) (by
      simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith)
  intro s hs
  exact (hdiff.analyticOnNhd hT).eqOn_zero_of_preconnected_of_eventuallyEq_zero hU
    (z₀ := (((d + 1 : ℝ)) : ℂ)) (by
      simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith)
    (by filter_upwards [hball] with y hy; exact hzero y hy) hs

theorem cross_multiplication_unique (N D N' D' G : Coordinates → ℂ)
    (h : GlobalQuotientCertificate N D G)
    (h' : GlobalQuotientCertificate N' D' G) :
    CrossMultipliedOn N D N' D' Omega := by
  let E : Coordinates → ℂ := fun y => N y * D' y - N' y * D y
  have hEsep : SeparatelyHolomorphicOn E Omega := by
    refine ⟨?_, ?_, ?_⟩
    · intro w z
      show DifferentiableOn ℂ (fun ξ : ℂ =>
        N (ξ, w, z) * D' (ξ, w, z) - N' (ξ, w, z) * D (ξ, w, z)) _
      exact ((h.numerator_separately_holomorphic.1 w z).mul
        (h'.denominator_separately_holomorphic.1 w z)).sub
        ((h'.numerator_separately_holomorphic.1 w z).mul
          (h.denominator_separately_holomorphic.1 w z))
    · intro ξ z
      show DifferentiableOn ℂ (fun w : ℂ =>
        N (ξ, w, z) * D' (ξ, w, z) - N' (ξ, w, z) * D (ξ, w, z)) _
      exact ((h.numerator_separately_holomorphic.2.1 ξ z).mul
        (h'.denominator_separately_holomorphic.2.1 ξ z)).sub
        ((h'.numerator_separately_holomorphic.2.1 ξ z).mul
          (h.denominator_separately_holomorphic.2.1 ξ z))
    · intro ξ w
      show DifferentiableOn ℂ (fun z : ℂ =>
        N (ξ, w, z) * D' (ξ, w, z) - N' (ξ, w, z) * D (ξ, w, z)) _
      exact ((h.numerator_separately_holomorphic.2.2 ξ w).mul
        (h'.denominator_separately_holomorphic.2.2 ξ w)).sub
        ((h'.numerator_separately_holomorphic.2.2 ξ w).mul
          (h.denominator_separately_holomorphic.2.2 ξ w))
  have hE0 : ∀ y ∈ Omega ∩ initialRegion, E y = 0 := by
    intro y hy
    obtain ⟨hyO, hyI⟩ := hy
    have h1 := h.initial_cleared_identity y ⟨hyO, hyI⟩
    have h2 := h'.initial_cleared_identity y ⟨hyO, hyI⟩
    have hgoal : N y * D' y - N' y * D y = 0 := by
      rw [← h1, ← h2]
      ring
    exact hgoal

  have step1 : ∀ ξ w z : ℂ, 4 < w.re → 2 < z.re → c₁ < ξ.re → E (ξ, w, z) = 0 := by
    intro ξ w z hw hz hξ
    refine eq_zero_on_halfSpace (fun s : ℂ => E (s, w, z)) c₁_lt_four ?_ ?_ ξ hξ
    · have hd := hEsep.1 w z
      rw [slice_fst hw hz] at hd
      exact hd
    · intro s hs4
      refine hE0 (s, w, z) ⟨?_, ?_⟩
      · rw [mem_Omega_iff]
        exact Or.inl ⟨lt_trans c₁_lt_four hs4, lt_trans c₂_lt_four hw,
          lt_trans c₃_lt_two hz⟩
      · exact ⟨hs4, hw, hz⟩

  have step2 : ∀ ξ w z : ℂ, c₁ < ξ.re → 2 < z.re → c₂ < w.re → E (ξ, w, z) = 0 := by
    intro ξ w z hξ hz hw
    refine eq_zero_on_halfSpace (fun s : ℂ => E (ξ, s, z)) c₂_lt_four ?_ ?_ w hw
    · have hd := hEsep.2.1 ξ z
      rw [slice_snd hξ hz] at hd
      exact hd
    · intro s hs4
      exact step1 ξ s z hs4 hz hξ

  have step3 : ∀ ξ w z : ℂ, c₁ < ξ.re → c₂ < w.re →
      ((ξ, w, z) : Coordinates) ∈ Omega → E (ξ, w, z) = 0 := by
    intro ξ w z hξ hw hxO
    have hzero : ∀ s : ℂ, 2 < s.re → E (ξ, w, s) = 0 := fun s hs => step2 ξ w s hξ hs hw
    by_cases hw' : c₂' < w.re
    · have hd := hEsep.2.2 ξ w
      rw [slice_trd_second hξ hw'] at hd
      have hz : c₃' < z.re := by
        rcases mem_Omega_iff.mp hxO with ⟨_, _, h3⟩ | ⟨_, _, h3⟩
        · exact lt_trans c₃'_lt_c₃ h3
        · exact h3
      exact eq_zero_on_halfSpace (fun s : ℂ => E (ξ, w, s)) c₃'_lt_two hd hzero z hz
    · have hd := hEsep.2.2 ξ w
      rw [slice_trd_first hξ hw hw'] at hd
      have hz : c₃ < z.re := by
        rcases mem_Omega_iff.mp hxO with ⟨_, _, h3⟩ | ⟨_, h2, _⟩
        · exact h3
        · exact absurd h2 hw'
      exact eq_zero_on_halfSpace (fun s : ℂ => E (ξ, w, s)) c₃_lt_two hd hzero z hz
  rintro ⟨ξ, w, z⟩ hxO
  show N (ξ, w, z) * D' (ξ, w, z) = N' (ξ, w, z) * D (ξ, w, z)
  have hzero : E (ξ, w, z) = 0 := by
    rcases mem_Omega_iff.mp hxO with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · exact step3 ξ w z h1 h2 hxO
    · exact step3 ξ w z h1 (lt_trans c₂_lt_c₂' h2) hxO
  exact sub_eq_zero.mp hzero

end DedekindZetaZeroFree.MeromorphicSeparationGluing

end
