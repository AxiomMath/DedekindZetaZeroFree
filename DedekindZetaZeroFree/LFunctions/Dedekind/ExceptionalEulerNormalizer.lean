module

public import DedekindZetaZeroFree.Arithmetic.Kummer.TwelfthRootsTotallyComplex
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveTrivialCharacter
public import DedekindZetaZeroFree.LFunctions.Hecke.EntireRegularizations
public import DedekindZetaZeroFree.LFunctions.Dedekind.PositiveExteriorZetaResidue

@[expose] public section

namespace DedekindZetaZeroFree.GlobalZetaNormalizer

noncomputable section
open scoped NumberField Topology
open Filter IsDedekindDomain

 def principalCharacter (F : Type) [Field F] [NumberField F] :
    RayClassCharacter F (⊤ : Ideal (𝓞 F)) :=
  Classical.choose (PrincipalMu12Pointwise.principal_primitive_top_character_exists F)

 theorem principalCharacter_principal (F : Type) [Field F] [NumberField F] :
    (principalCharacter F).IsPrincipal :=
  (Classical.choose_spec
    (PrincipalMu12Pointwise.principal_primitive_top_character_exists F)).1

 theorem principalCharacter_primitive (F : Type) [Field F] [NumberField F] :
    (principalCharacter F).IsPrimitive :=
  (Classical.choose_spec
    (PrincipalMu12Pointwise.principal_primitive_top_character_exists F)).2

def principalData
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    PrincipalRayHeckeData F ⊤ (principalCharacter F) :=
  principalRayHeckeData  F (primitive12_totallyComplex F ζ hζ) ⊤ top_ne_bot
    (principalCharacter F) (principalCharacter_primitive F) (principalCharacter_principal F)

def zetaRegularization
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (z : ℂ) : ℂ :=
  principalHeckeEntireRegularization F ⊤ (principalCharacter F)
    (principalData  F ζ hζ) z

def zeta
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (z : ℂ) : ℂ :=
  zetaRegularization  F ζ hζ z / (z - 1)

def exteriorZeta
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : ℂ) : ℂ :=
  zeta  F ζ hζ z * PositiveZetaResidue.exteriorEulerFactor F S z

def exteriorRegularization
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : ℂ) : ℂ :=
  zetaRegularization  F ζ hζ z * PositiveZetaResidue.exteriorEulerFactor F S z

def exceptionalNormalizer
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℂ) : ℂ :=
  exteriorZeta  F ζ hζ S (1 + 6 * s) /
    exteriorZeta  F ζ hζ S (2 + 6 * s)

def exceptionalRegularization
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℂ) : ℂ :=
  exteriorRegularization  F ζ hζ S (1 + 6 * s) /
    (6 * exteriorZeta  F ζ hζ S (2 + 6 * s))

theorem actual_principal_continuation

    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    let Z := zeta  F ζ hζ
    let R := zetaRegularization  F ζ hζ
    let P := principalData  F ζ hζ
    MeromorphicOn Z Set.univ ∧ DifferentiableOn ℂ Z {1}ᶜ ∧
    Differentiable ℂ R ∧
    (∀ z : ℂ, z ≠ 1 → R z = (z - 1) * Z z) ∧
    (∀ z : ℂ, 0 < z.re → R z = P.R z) ∧
    (∀ z : ℂ, 0 < z.re → z ≠ 1 → Z z = P.L z) ∧
    (∀ z : ℂ, 1 < z.re → Z z = NumberField.dedekindZeta F z) ∧
    (∀ z : ℂ, 1 < z.re →
      HasSum (fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℂ) ^ (-z)) (Z z)) := by
  dsimp only
  let P := principalData  F ζ hζ
  let R := zetaRegularization  F ζ hζ
  have hR : Differentiable ℂ R :=
    principalHeckeEntireRegularization_differentiable F
      (primitive12_totallyComplex F ζ hζ) ⊤ top_ne_bot (principalCharacter F) P
  have hbridge : ∀ z : ℂ, 0 < z.re → R z = P.R z := fun z hz =>
    principalHeckeEntireRegularization_eq_bridge F
      (primitive12_totallyComplex F ζ hζ) ⊤ top_ne_bot (principalCharacter F) P z hz
  have hL : ∀ z : ℂ, 0 < z.re → z ≠ 1 → zeta  F ζ hζ z = P.L z := by
    intro z hz hz1
    change R z / (z - 1) = P.L z
    rw [hbridge z hz, P.regularized z hz hz1, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hz1)]
  have hZ : MeromorphicOn (zeta  F ζ hζ) Set.univ := by
    exact (hR.differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn.div
      ((analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn)
  refine ⟨hZ, ?_, hR, ?_, hbridge, hL, ?_, ?_⟩
  · intro z hz
    exact ((hR z).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr (by simpa using hz))).differentiableWithinAt
  · intro z hz
    change R z = (z - 1) * (R z / (z - 1))
    field_simp
  · intro z hz
    rw [hL z (zero_lt_one.trans hz) (by intro h; rw [h] at hz; norm_num at hz)]
    exact PositiveZetaResidue.principal_continuation_eq_dedekindZeta F
      (principalCharacter F) (principalCharacter_principal F) P z hz
  · intro z hz
    rw [hL z (zero_lt_one.trans hz) (by intro h; rw [h] at hz; norm_num at hz)]
    convert P.series z hz using 1
    ext I
    by_cases hI : I = ⊥
    · subst I
      simp [(principalCharacter F).eq_zero_iff', Complex.zero_cpow
        (show -z ≠ 0 by intro h; have := congrArg Complex.re h; simp at this; linarith)]
    · rw [principalCharacter_principal F I hI (by simp), one_mul]

theorem exterior_zeta_at_two_pos

    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (exteriorZeta  F ζ hζ S 2).im = 0 ∧
    0 < (exteriorZeta  F ζ hζ S 2).re := by
  have hs := (actual_principal_continuation  F ζ hζ).2.2.2.2.2.2.2 2 (by norm_num)
  have hterm (I : Ideal (𝓞 F)) :
      (Ideal.absNorm I : ℂ) ^ (-(2 : ℂ)) = (((Ideal.absNorm I : ℝ) ^ 2)⁻¹ : ℝ) := by
    simp [Complex.cpow_neg, Complex.cpow_two]
  have hre := Complex.hasSum_re hs
  have him := Complex.hasSum_im hs
  simp_rw [hterm, Complex.ofReal_re] at hre
  simp_rw [hterm, Complex.ofReal_im] at him
  have hZi : (zeta  F ζ hζ 2).im = 0 := by simpa using him.tsum_eq.symm
  have hZp : 0 < (zeta  F ζ hζ 2).re := by
    rw [← hre.tsum_eq]
    apply hre.summable.tsum_pos (i := (⊤ : Ideal (𝓞 F)))
    · intro I; positivity
    · simp
  have he : PositiveZetaResidue.exteriorEulerFactor F S 2 =
      ((∏ p ∈ S, (1 - ((Ideal.absNorm p.asIdeal : ℝ) ^ 2)⁻¹) : ℝ) : ℂ) := by
    simp [PositiveZetaResidue.exteriorEulerFactor, hterm, Complex.ofReal_prod]
  have hep : 0 < ∏ p ∈ S, (1 - ((Ideal.absNorm p.asIdeal : ℝ) ^ 2)⁻¹) := by
    apply Finset.prod_pos
    intro p hp
    have hn : (1 : ℝ) < Ideal.absNorm p.asIdeal := by
      exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm p
    have hn2 : (1 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) ^ 2 := by nlinarith
    exact sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr hn2)
  simp only [exteriorZeta, he, Complex.mul_im, Complex.mul_re, Complex.ofReal_im,
    Complex.ofReal_re, hZi, mul_zero, zero_mul, add_zero, sub_zero]
  exact ⟨trivial, mul_pos hZp hep⟩

private theorem euler_differentiable (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Differentiable ℂ (PositiveZetaResidue.exteriorEulerFactor F S) := by
  intro s
  apply DifferentiableAt.fun_finset_prod
  intro p hp
  apply (differentiableAt_const (1 : ℂ)).sub
  apply differentiableAt_id.neg.const_cpow
  left
  exact_mod_cast (zero_lt_one.trans
    (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm p)).ne'

theorem exterior_positive_simple_residue

    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    let ZS := exteriorZeta  F ζ hζ S
    let RS := exteriorRegularization  F ζ hζ S
    let rS := PositiveZetaResidue.exteriorResidue F S
    MeromorphicOn ZS Set.univ ∧
    0 < rS ∧ RS 1 = (rS : ℂ) ∧
    (∃ V : Set ℂ, IsOpen V ∧ (1 : ℂ) ∈ V ∧ DifferentiableOn ℂ RS V ∧
      (∀ z ∈ V, z ≠ 1 → RS z = (z - 1) * ZS z)) ∧
    meromorphicOrderAt ZS 1 = (-1 : WithTop ℤ) ∧
    Tendsto (fun z : ℂ => (z - 1) * ZS z) (𝓝[≠] 1) (𝓝 (rS : ℂ)) := by
  dsimp only
  let ZS := exteriorZeta  F ζ hζ S
  let RS := exteriorRegularization  F ζ hζ S
  have hc := actual_principal_continuation  F ζ hζ
  have hg : Differentiable ℂ RS := hc.2.2.1.mul (euler_differentiable F S)
  have hm : MeromorphicOn ZS Set.univ := hc.1.mul
    (((euler_differentiable F S).differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn)
  have hv : RS 1 = (PositiveZetaResidue.exteriorResidue F S : ℂ) := by
    change zetaRegularization  F ζ hζ 1 * _ = _
    rw [hc.2.2.2.2.1 1 (by norm_num)]
    exact PositiveZetaResidue.exterior_regularization_at_one F (principalCharacter F)
      (principalCharacter_principal F) (principalData  F ζ hζ) S
  have hp := PositiveZetaResidue.exterior_residue_pos F S
  have heq : ∀ z : ℂ, z ≠ 1 → RS z = (z - 1) * ZS z := by
    intro z hz
    dsimp [RS, ZS, exteriorRegularization, exteriorZeta]
    rw [hc.2.2.2.1 z hz, mul_assoc]
  have hev : ∀ᶠ z in 𝓝[≠] (1 : ℂ), ZS z = (z - 1) ^ (-1 : ℤ) • RS z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hn : z - 1 ≠ 0 := sub_ne_zero.mpr (by simpa using hz)
    rw [heq z (by simpa using hz), zpow_neg_one, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hn, one_mul]
  have han : AnalyticAt ℂ RS 1 := hg.differentiableOn.analyticOnNhd isOpen_univ 1 trivial
  have hne : RS 1 ≠ 0 := by rw [hv]; exact_mod_cast hp.ne'
  refine ⟨hm, hp, hv, ⟨Set.univ, isOpen_univ, trivial, hg.differentiableOn,
    fun z _ hz => heq z hz⟩, ?_, ?_⟩
  · exact (meromorphicOrderAt_eq_int_iff (hm 1 trivial)).mpr ⟨RS, han, hne, hev⟩
  · rw [← hv]
    apply (hg.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact heq z (by simpa using hz)

theorem positive_simple_exceptional_normalizer

    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    let ZS := exteriorZeta  F ζ hζ S
    let rS := PositiveZetaResidue.exteriorResidue F S
    let cS := exceptionalNormalizer  F ζ hζ S
    let gS := exceptionalRegularization  F ζ hζ S
    ∃ ε : ℝ, 0 < ε ∧
      (∀ s ∈ Metric.ball (0 : ℂ) ε, ZS (2 + 6 * s) ≠ 0) ∧
      MeromorphicOn cS (Metric.ball (0 : ℂ) ε) ∧
      DifferentiableOn ℂ gS (Metric.ball (0 : ℂ) ε) ∧
      (∀ s ∈ Metric.ball (0 : ℂ) ε, s ≠ 0 → gS s = s * cS s) ∧
      gS 0 = (rS : ℂ) / (6 * ZS 2) ∧
      (gS 0).im = 0 ∧ 0 < (gS 0).re ∧
      meromorphicOrderAt cS 0 = (-1 : WithTop ℤ) ∧
      Tendsto (fun s : ℂ => s * cS s) (𝓝[≠] 0)
        (𝓝 ((rS : ℂ) / (6 * ZS 2))) := by
  dsimp only
  let ZS := exteriorZeta  F ζ hζ S
  let RS := exteriorRegularization  F ζ hζ S
  let rS := PositiveZetaResidue.exteriorResidue F S
  let cS := exceptionalNormalizer  F ζ hζ S
  let gS := exceptionalRegularization  F ζ hζ S
  let A : ℂ → ℂ := fun s => 1 + 6 * s
  let B : ℂ → ℂ := fun s => 2 + 6 * s
  have hA : Differentiable ℂ A := (differentiable_const (1 : ℂ)).add
    ((differentiable_const (6 : ℂ)).mul differentiable_id)
  have hB : Differentiable ℂ B := (differentiable_const (2 : ℂ)).add
    ((differentiable_const (6 : ℂ)).mul differentiable_id)
  have hc := actual_principal_continuation  F ζ hζ
  have hr := exterior_positive_simple_residue  F ζ hζ S
  have hR : Differentiable ℂ RS := hc.2.2.1.mul (euler_differentiable F S)
  have hZ : DifferentiableOn ℂ ZS {1}ᶜ := hc.2.1.mul (euler_differentiable F S).differentiableOn
  have htwo := exterior_zeta_at_two_pos  F ζ hζ S
  have htwo_ne : ZS 2 ≠ 0 := by
    intro h
    have he : (ZS 2).re = 0 := congrArg Complex.re h
    exact (ne_of_gt htwo.2) he
  let U : Set ℂ := {s | B s ≠ 1}
  have hU : IsOpen U := isOpen_ne.preimage hB.continuous
  have h0U : (0 : ℂ) ∈ U := by norm_num [U, B]
  have hD : DifferentiableOn ℂ (ZS ∘ B) U :=
    hZ.comp hB.differentiableOn (fun s hs => by simpa [U] using hs)
  have hD0 : ContinuousAt (ZS ∘ B) 0 :=
    (hD.differentiableAt (hU.mem_nhds h0U)).continuousAt
  have hDne : ∀ᶠ s in 𝓝 (0 : ℂ), ZS (B s) ≠ 0 :=
    hD0.eventually_ne (by simpa [B] using htwo_ne)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hDne.and (hU.mem_nhds h0U))
  have hg : DifferentiableOn ℂ gS (Metric.ball 0 ε) := by
    apply (hR.comp hA).differentiableOn.div
      ((differentiable_const (6 : ℂ)).differentiableOn.mul
        (hD.mono (fun s hs => (hball s hs).2)))
    intro s hs
    exact mul_ne_zero (by norm_num) (hball s hs).1
  have hm : MeromorphicOn cS (Metric.ball 0 ε) :=
    (hr.1.comp_analyticOnNhd (hA.differentiableOn.analyticOnNhd Metric.isOpen_ball)
      (fun _ _ => trivial)).div
    (hr.1.comp_analyticOnNhd (hB.differentiableOn.analyticOnNhd Metric.isOpen_ball)
      (fun _ _ => trivial))
  have heq : ∀ s : ℂ, s ≠ 0 → gS s = s * cS s := by
    intro s hs
    dsimp [gS, cS, exceptionalRegularization, exceptionalNormalizer,
      exteriorRegularization, exteriorZeta, zeta]
    have h6 : (6 : ℂ) * s ≠ 0 := mul_ne_zero (by norm_num) hs
    simp only [add_sub_cancel_left]
    field_simp
  have hv : gS 0 = (rS : ℂ) / (6 * ZS 2) := by
    simpa [gS, exceptionalRegularization, rS] using
      congrArg (fun w : ℂ => w / (6 * ZS 2)) hr.2.2.1
  have hreal : ZS 2 = ((ZS 2).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using htwo.1
  have hp : 0 < rS / (6 * (ZS 2).re) := div_pos hr.2.1 (mul_pos (by norm_num) htwo.2)
  have hvreal : gS 0 = ((rS / (6 * (ZS 2).re) : ℝ) : ℂ) := by
    rw [hv, hreal]
    push_cast
    rfl
  have hg0 : AnalyticAt ℂ gS 0 := hg.analyticAt (Metric.ball_mem_nhds 0 hε)
  have hgne : gS 0 ≠ 0 := by rw [hvreal]; exact_mod_cast hp.ne'
  have hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), cS s = (s - 0) ^ (-1 : ℤ) • gS s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hn : s ≠ 0 := by simpa using hs
    rw [heq s hn, sub_zero, zpow_neg_one, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hn, one_mul]
  have horder : meromorphicOrderAt cS 0 = (-1 : WithTop ℤ) :=
    (meromorphicOrderAt_eq_int_iff (hm 0 (Metric.mem_ball_self hε))).mpr
      ⟨gS, hg0, hgne, hev⟩
  have ht : Tendsto (fun s : ℂ => s * cS s) (𝓝[≠] 0)
      (𝓝 ((rS : ℂ) / (6 * ZS 2))) := by
    rw [← hv]
    apply (hg0.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact heq s (by simpa using hs)
  refine ⟨ε, hε, fun s hs => ?_, hm, hg, fun s _ hs => heq s hs, hv, ?_, ?_, horder, ht⟩
  · exact (hball s hs).1
  · change (gS 0).im = 0
    rw [hvreal]
    exact Complex.ofReal_im _
  · change 0 < (gS 0).re
    rw [hvreal]; exact hp

end
end DedekindZetaZeroFree.GlobalZetaNormalizer
