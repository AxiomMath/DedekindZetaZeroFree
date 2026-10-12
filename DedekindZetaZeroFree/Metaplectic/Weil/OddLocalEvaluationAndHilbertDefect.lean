module

public import DedekindZetaZeroFree.Metaplectic.Weil.SquareScalingAndPhaseNorms
public import DedekindZetaZeroFree.Metaplectic.Weil.ParityEvaluationHilbertDefect

@[expose] public section

section
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory
noncomputable section
namespace DedekindZetaZeroFree.OddEvaluation
variable {F : Type} [Field F] [NumberField F]
private theorem unit_norm (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletionIntegers F)ˣ) :
    ‖(localUnit v u : v.adicCompletion F)‖ = 1 := by
  have h1 := norm_le_one_of_mem_adicCompletionIntegers v u.val.property
  have h2 := norm_le_one_of_mem_adicCompletionIntegers v (u⁻¹).val.property
  change ‖(localUnit v u : v.adicCompletion F)‖ ≤ 1 at h1
  change ‖(localUnit v (u⁻¹) : v.adicCompletion F)‖ ≤ 1 at h2
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  exact le_antisymm h1 ((inv_le_one₀ (norm_pos_iff.mpr (localUnit v u).ne_zero)).mp h2)
private theorem two_norm (v : HeightOneSpectrum (𝓞 F)) (hodd : ringChar (Residue v) ≠ 2) :
    ‖(2 : v.adicCompletion F)‖ = 1 := by
  have hu : IsUnit (2 : v.adicCompletionIntegers F) := by
    by_contra h
    have hm : (2 : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).mpr h
    have hz : IsLocalRing.residue (v.adicCompletionIntegers F) 2 = 0 :=
      (IsLocalRing.residue_eq_zero_iff 2).mpr hm
    have hz' : (2 : Residue v) = 0 := by
      rw [← map_ofNat (IsLocalRing.residue (v.adicCompletionIntegers F)) 2]
      exact hz
    exact Ring.two_ne_zero hodd hz'
  obtain ⟨u, hu⟩ := hu
  have he : (localUnit v u : v.adicCompletion F) = 2 := by
    exact congrArg Subtype.val hu
  rw [← he]
  exact unit_norm v u
private theorem scaled_annihilator (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (hc : conductor v π hπ c) (z : v.adicCompletion F) :
    (∀ h : v.adicCompletionIntegers F,
      ResidueTrace.localTraceCharacter v ((uniformizer v π hπ ^ c : (v.adicCompletion F)ˣ) * z * (h : v.adicCompletion F)) = 1) ↔
      z ∈ v.adicCompletionIntegers F := by
  constructor
  · intro hz
    by_contra hzo
    have hn : 1 < ‖z‖ := lt_of_not_ge (fun h => hzo (mem_adicCompletionIntegers_of_norm_le_one v h))
    have hzne : z ≠ 0 := by intro h; simp [h] at hn; linarith
    let zi : v.adicCompletionIntegers F := ⟨z⁻¹, mem_adicCompletionIntegers_of_norm_le_one v (by
      rw [norm_inv]; exact (inv_le_one₀ (by positivity)).mpr hn.le)⟩
    have hzi : ¬ IsUnit zi := by
      rintro ⟨u, hu⟩
      have huN := unit_norm v u
      have he : (localUnit v u : v.adicCompletion F) = z⁻¹ := congrArg Subtype.val hu
      rw [he, norm_inv] at huN
      have hn' : ‖z‖ = 1 := by exact (inv_eq_one.mp huN)
      linarith
    have hmem : zi ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).mpr hzi
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
      Ideal.mem_span_singleton] at hmem
    obtain ⟨t, ht⟩ := hmem
    have ht' : (π : v.adicCompletion F) * (t : v.adicCompletion F) = z⁻¹ :=
      (congrArg Subtype.val ht).symm
    obtain ⟨w, hw⟩ := hc.2
    have hh := hz (t*w)
    apply hw
    have hp : (π : v.adicCompletion F) ≠ 0 := (uniformizer v π hπ).ne_zero
    have he : ((uniformizer v π hπ ^ c : (v.adicCompletion F)ˣ) : v.adicCompletion F) * z * ↑(t*w) =
        ((uniformizer v π hπ ^ (c-1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * ↑w := by
      simp only [Units.val_zpow_eq_zpow_val]
      have htw : ((t*w : v.adicCompletionIntegers F) : v.adicCompletion F) = (t : v.adicCompletion F) * (w : v.adicCompletion F) := rfl
      rw [htw]
      change (π : v.adicCompletion F) ^ c * z * ((t : v.adicCompletion F) * ↑w) = (π : v.adicCompletion F) ^ (c-1) * ↑w
      rw [zpow_sub₀ hp, zpow_one]
      have hzt : z * (t : v.adicCompletion F) = (π : v.adicCompletion F)⁻¹ := by
        apply (mul_left_cancel₀ hp)
        calc
          ↑π * (z * ↑t) = z * (↑π * ↑t) := by ring
          _ = 1 := by rw [ht', mul_inv_cancel₀ hzne]
          _ = ↑π * (↑π)⁻¹ := (mul_inv_cancel₀ hp).symm
      rw [mul_assoc, ← mul_assoc z, hzt]
      simp [div_eq_mul_inv, mul_assoc]
    rwa [he] at hh
  · intro hz h
    simpa only [mul_assoc] using hc.1 ⟨z * (h : v.adicCompletion F), (v.adicCompletionIntegers F).mul_mem _ _ hz h.property⟩
open SArithmeticData in

theorem gamma_conductor_class (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hodd : ringChar (Residue v) ≠ 2)
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (hc : conductor v π hπ c) (u : (v.adicCompletionIntegers F)ˣ) :
    A.finiteGamma v (localUnit v u * uniformizer v π hπ ^ c) = 1 := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  letI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let O := (v.adicCompletionIntegers F).toSubring.toAddSubgroup
  let a := localUnit v u * uniformizer v π hπ ^ c
  have htwo := two_norm v hodd
  have hu := unit_norm v u
  have hq : ∀ h ∈ O, ResidueTrace.localTraceCharacter v ((a : v.adicCompletion F) * h ^ 2) = 1 := by
    intro h hh
    have hm : (localUnit v u : v.adicCompletion F) * h^2 ∈ v.adicCompletionIntegers F :=
      (v.adicCompletionIntegers F).mul_mem _ _ u.val.property ((v.adicCompletionIntegers F).pow_mem hh 2)
    convert hc.1 ⟨_, hm⟩ using 1
    change ResidueTrace.localTraceCharacter v ((↑(localUnit v u) * ↑(uniformizer v π hπ ^ c)) * h ^ 2) = _
    congr 1
    ring
  have hL : finiteStationarySubgroup v a O = O := by
    ext z
    change (∀ h ∈ O, ResidueTrace.localTraceCharacter v (h * (2 * (a : v.adicCompletion F) * z)) = 1) ↔ z ∈ O
    have he : (∀ h ∈ O, ResidueTrace.localTraceCharacter v (h * (2 * (a : v.adicCompletion F) * z)) = 1) ↔
        2 * (localUnit v u : v.adicCompletion F) * z ∈ v.adicCompletionIntegers F := by
      rw [← scaled_annihilator v π hπ c hc (2 * (localUnit v u : v.adicCompletion F) * z)]
      constructor
      · intro H h
        convert H h h.property using 1
        change ResidueTrace.localTraceCharacter v (↑(uniformizer v π hπ ^ c) * (2 * ↑(localUnit v u) * z) * ↑h) =
          ResidueTrace.localTraceCharacter v (↑h * (2 * (↑(localUnit v u) * ↑(uniformizer v π hπ ^ c)) * z))
        congr 1
        ring
      · intro H h hh
        convert H ⟨h, hh⟩ using 1
        change ResidueTrace.localTraceCharacter v (h * (2 * (↑(localUnit v u) * ↑(uniformizer v π hπ ^ c)) * z)) =
          ResidueTrace.localTraceCharacter v (↑(uniformizer v π hπ ^ c) * (2 * ↑(localUnit v u) * z) * h)
        congr 1
        ring
    rw [he]
    constructor
    · intro hz
      apply mem_adicCompletionIntegers_of_norm_le_one v
      simpa only [norm_mul, htwo, hu, one_mul] using norm_le_one_of_mem_adicCompletionIntegers v hz
    · intro hz
      apply mem_adicCompletionIntegers_of_norm_le_one v
      simpa only [norm_mul, htwo, hu, one_mul] using norm_le_one_of_mem_adicCompletionIntegers v hz
  have hH : FiniteQuadraticAdmissible v a O := by
    refine ⟨⟨1, ?_⟩, hq, ?_⟩
    · ext x
      simp [AddSubgroup.mem_map, O]
    · rw [hL]
  have hQ : Subsingleton (finiteStationaryQuotient v a O) := by
    apply QuotientAddGroup.subsingleton_iff.mpr
    ext x
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_top, iff_true]
    exact (show finiteStationarySubgroup v a O ≤ O from le_of_eq hL) x.property
  letI := hQ
  have hp : finiteStationaryPhase v a O 0 = 1 := by
    have he := finiteStationaryPhase_mk v a O hH 0
    have hzero : (QuotientAddGroup.mk' (O.comap (finiteStationarySubgroup v a O).subtype)) 0 = (0 : finiteStationaryQuotient v a O) := Subsingleton.elim _ _
    rw [hzero] at he
    simpa using he
  have hG : A.finiteStationaryGauss v a O =
      (((A.finiteTraceHaar v) (O : Set (v.adicCompletion F))).toReal : ℂ) := by
    unfold finiteStationaryGauss
    rw [finsum_eq_single _ 0 (fun x hx => False.elim (hx (Subsingleton.elim _ _))), hp]
    simp
  have hv := A.finiteOscillatoryValue_eq_gauss v a O hH
  rw [hG, finiteOscillatoryValue] at hv
  have hs : (Real.sqrt ‖(2 : v.adicCompletion F) * (a : v.adicCompletion F)‖ : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply (Real.sqrt_pos.mpr (norm_pos_iff.mpr _)).ne'
    exact mul_ne_zero (by exact_mod_cast (show (2 : F) ≠ 0 from two_ne_zero)) a.ne_zero
  have he := (div_eq_iff hs).mp hv
  have hn := A.norm_finiteGamma v a
  rw [he, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  rw [he, ← Complex.ofReal_mul, hn]
  rfl
end DedekindZetaZeroFree.OddEvaluation

end

end

section
noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.OddEvaluation
variable {F : Type} [Field F] [NumberField F]
private theorem square_sum_eq_gauss {k : Type*} [Field k] [Fintype k]
    (hodd : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) :
    (∑ x : k, ψ (x^2)) = gaussSum ((quadraticChar k).ringHomComp (Int.castRingHom ℂ)) ψ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun x : k => x^2) (fun x => ψ (x^2))]
  have count (y : k) : (Finset.univ.filter (fun x : k => x^2 = y)).card =
      (quadraticChar k y : ℂ) + 1 := by
    exact_mod_cast (by simpa only [Set.toFinset_setOf] using quadraticChar_card_sqrts hodd y)
  have inner (y : k) :
      (∑ x ∈ Finset.univ with x^2 = y, ψ (x^2)) =
        ((quadraticChar k y : ℂ) + 1) * ψ y := by
    trans (∑ _x ∈ Finset.univ with _x^2 = y, ψ y)
    · apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    · rw [Finset.sum_const, nsmul_eq_mul, count]
  simp_rw [inner, add_mul, one_mul]
  rw [Finset.sum_add_distrib, AddChar.sum_eq_zero_of_ne_one hψ, add_zero]
  rfl

 private theorem square_sum_unit_dependence {k : Type*} [Field k] [Fintype k]
    (hodd : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (u : kˣ) :
    (∑ x : k, ψ ((u : k) * x^2)) =
      (quadraticChar k (u : k) : ℂ) * ∑ x : k, ψ (x^2) := by
  let χ := (quadraticChar k).ringHomComp (Int.castRingHom ℂ)
  have hshift : ψ.mulShift (u : k) ≠ 1 := by
    intro he
    apply hψ
    ext x
    have hx := congrArg (fun f : AddChar k ℂ => f ((u⁻¹ : kˣ) * x)) he
    simpa [AddChar.mulShift_apply, mul_assoc] using hx
  have hs := gaussSum_mulShift χ ψ u
  have hχ : χ (u : k) * χ (u : k) = 1 := by
    change (quadraticChar k (u : k) : ℂ) * (quadraticChar k (u : k) : ℂ) = 1
    exact_mod_cast (by simpa only [pow_two] using quadraticChar_sq_one u.ne_zero)
  have he : gaussSum χ (ψ.mulShift (u : k)) = χ (u : k) * gaussSum χ ψ := by
    rw [← hs, ← mul_assoc, hχ, one_mul]
  rw [← square_sum_eq_gauss hodd ψ hψ] at he
  simpa [χ, AddChar.mulShift_apply] using (square_sum_eq_gauss hodd (ψ.mulShift (u : k)) hshift).trans he

 private theorem positive_normalization_from_norm {q r : ℝ} (hq : 0 < q) (hr : 0 ≤ r)
    (z : ℂ) (hz : ‖z‖ = Real.sqrt q) (hphase : ‖(r : ℂ) * z‖ = 1) :
    r = (Real.sqrt q)⁻¹ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, hz] at hphase
  simpa only [one_div] using (eq_div_iff (Real.sqrt_pos.mpr hq).ne').mpr hphase

 private theorem square_sum_norm {k : Type*} [Field k] [Fintype k]
    (hodd : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) :
    ‖∑ x : k, ψ (x^2)‖ = Real.sqrt (Fintype.card k) := by
  let χ := (quadraticChar k).ringHomComp (Int.castRingHom ℂ)
  have hχ : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := ℂ))).mpr
      (quadraticChar_ne_one hodd)
  have hs := gaussSum_sq hχ ((quadraticChar_isQuadratic _).comp _) (AddChar.IsPrimitive.of_ne_one hψ)
  have hneg : ‖χ (-1)‖ = 1 := by
    have hh : χ (-1) ^ 2 = 1 := by
      change (quadraticChar k (-1) : ℂ) ^ 2 = 1
      exact_mod_cast quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero : (1:k) ≠ 0))
    have hn := congrArg norm hh
    simp only [norm_pow, norm_one] at hn
    nlinarith [norm_nonneg (χ (-1))]
  rw [← square_sum_eq_gauss hodd ψ hψ] at hs
  have hn := congrArg norm hs
  simp only [norm_pow, norm_mul, hneg, one_mul, Complex.norm_natCast] at hn
  have hq : 0 ≤ (Fintype.card k : ℝ) := by positivity
  have hsqrt := Real.sq_sqrt hq
  nlinarith [norm_nonneg (∑ x : k, ψ (x^2)), Real.sqrt_nonneg (Fintype.card k)]

 abbrev psi0 (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ) :=
  (ResidueTrace.localTraceCharacter v).compAddMonoidHom
    (AddMonoidHom.mulLeft (((uniformizer v π hπ)^c : (v.adicCompletion F)ˣ) : v.adicCompletion F))
private theorem theta_on_lift (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (hc : conductor v π hπ c) (x : v.adicCompletionIntegers F) :
    theta v π hπ c (IsLocalRing.residue _ x) =
      psi0 v π hπ c ((x : v.adicCompletion F) / (π : v.adicCompletion F)) := by
  set y : v.adicCompletionIntegers F := Classical.choose
    (IsLocalRing.residue_surjective (IsLocalRing.residue _ x)) with hy
  have hres : IsLocalRing.residue (v.adicCompletionIntegers F) y =
      IsLocalRing.residue (v.adicCompletionIntegers F) x := by
    rw [hy]
    exact Classical.choose_spec (IsLocalRing.residue_surjective (IsLocalRing.residue _ x))
  have hmem : y - x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    rw [map_sub, hres, sub_self]
  have hspan : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (hspan ▸ hmem)
  have hpi : (π : v.adicCompletion F) ≠ 0 := by
    intro h
    exact hπ.ne_zero (Subtype.ext h)
  have hK : (z : v.adicCompletion F) * (π : v.adicCompletion F) =
      (y : v.adicCompletion F) - (x : v.adicCompletion F) := by
    have h := congrArg (fun w : v.adicCompletionIntegers F => (w : v.adicCompletion F)) hz
    push_cast at h
    exact h
  have hdiv : (y : v.adicCompletion F) / (π : v.adicCompletion F) =
      (x : v.adicCompletion F) / (π : v.adicCompletion F) +
        (z : v.adicCompletion F) := by
    rw [div_eq_iff hpi, add_mul, div_mul_cancel₀ _ hpi, hK]
    ring
  change psi0 v π hπ c ((y : v.adicCompletion F) / (π : v.adicCompletion F)) = _
  rw [hdiv, AddChar.map_add_eq_mul, show psi0 v π hπ c (z : v.adicCompletion F) = 1 from hc.1 z, mul_one]

private theorem theta_additive_nontrivial (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (hc : conductor v π hπ c) :
    theta v π hπ c 0 = 1 ∧
      (∀ x y, theta v π hπ c (x+y) = theta v π hπ c x * theta v π hπ c y) ∧
      ∃ x, theta v π hπ c x ≠ 1 := by
  let r := IsLocalRing.residue (v.adicCompletionIntegers F)
  let lift (x : Residue v) : v.adicCompletionIntegers F := Classical.choose
    (IsLocalRing.residue_surjective x)
  have hlift (x : Residue v) : r (lift x) = x := Classical.choose_spec
    (IsLocalRing.residue_surjective x)
  have key : ∀ a : v.adicCompletionIntegers F,
      psi0 v π hπ c ((a : v.adicCompletion F) / (π : v.adicCompletion F)) =
        theta v π hπ c (r a) := fun a => (theta_on_lift v π hπ c hc a).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_zero r, ← key 0]
    simp
  · intro x y
    rw [← hlift x, ← hlift y, ← map_add, ← key, Subring.coe_add, add_div, AddChar.map_add_eq_mul, key, key]
  · obtain ⟨x, hx⟩ := hc.2
    refine ⟨r x, ?_⟩
    rw [← key]
    intro h
    apply hx
    change ResidueTrace.localTraceCharacter v
      ((((uniformizer v π hπ)^c : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
        ((x : v.adicCompletion F) / (π : v.adicCompletion F))) = 1 at h
    have hpi : (π : v.adicCompletion F) ≠ 0 := by
      intro h; exact hπ.ne_zero (Subtype.ext h)
    have he : (((uniformizer v π hπ)^c : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
        ((x : v.adicCompletion F) / (π : v.adicCompletion F)) =
        (((uniformizer v π hπ)^(c-1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
        (x : v.adicCompletion F) := by
      simp only [Units.val_zpow_eq_zpow_val]
      change (π : v.adicCompletion F)^c * ((x : v.adicCompletion F) / (π : v.adicCompletion F)) =
        (π : v.adicCompletion F)^(c-1) * (x : v.adicCompletion F)
      rw [zpow_sub₀ hpi, zpow_one]
      ring
    rwa [he] at h
set_option maxHeartbeats 1000000 in

private theorem psi0_selfDual (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (hc : conductor v π hπ c) (y : v.adicCompletion F) :
    (∀ x : v.adicCompletionIntegers F,
      psi0 v π hπ c (y * x) = 1) ↔
        y ∈ v.adicCompletionIntegers F := by
  constructor
  · intro hy
    by_contra hn
    have hy0 : y ≠ 0 := by intro h; apply hn; simp [h]
    have hi : y⁻¹ ∈ v.adicCompletionIntegers F :=
      ((v.adicCompletionIntegers F).mem_or_inv_mem y).resolve_left hn
    let yi : v.adicCompletionIntegers F := ⟨y⁻¹, hi⟩
    have hni : ¬ IsUnit yi := by
      intro hu
      obtain ⟨u, hu⟩ := hu
      have he : ((u⁻¹).val : v.adicCompletion F) = y := by
        have hm : ((u⁻¹).val : v.adicCompletion F) * y⁻¹ = 1 := by
          rw [← show (u.val : v.adicCompletion F) = y⁻¹ from congrArg Subtype.val hu]
          exact congrArg Subtype.val u.inv_val
        simpa using (eq_div_iff (inv_ne_zero hy0)).mpr hm
      exact hn (he ▸ (u⁻¹).val.property)
    have hm : yi ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
      (IsLocalRing.mem_maximalIdeal yi).mpr hni
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ] at hm
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hm
    have hzK : (z : v.adicCompletion F) * (π : v.adicCompletion F) = y⁻¹ :=
      congrArg Subtype.val hz
    obtain ⟨x, hx⟩ := hc.2
    have hpi : (π : v.adicCompletion F) ≠ 0 := by
      intro h; exact hπ.ne_zero (Subtype.ext h)
    have harg : y * ((x * z : v.adicCompletionIntegers F) : v.adicCompletion F) =
        (x : v.adicCompletion F) / (π : v.adicCompletion F) := by
      apply (eq_div_iff hpi).mpr
      change y * ((x : v.adicCompletion F) * (z : v.adicCompletion F)) * _ = _
      calc
        _ = (x : v.adicCompletion F) * (y * ((z : v.adicCompletion F) * (π : v.adicCompletion F))) := by ring
        _ = (x : v.adicCompletion F) := by rw [hzK, mul_inv_cancel₀ hy0, mul_one]
    have ht := hy (x*z)
    rw [harg] at ht
    apply hx
    change ResidueTrace.localTraceCharacter v
      ((((uniformizer v π hπ)^c : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
        ((x : v.adicCompletion F) / (π : v.adicCompletion F))) = 1 at ht
    have he : (((uniformizer v π hπ)^c : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
        ((x : v.adicCompletion F) / (π : v.adicCompletion F)) =
        (((uniformizer v π hπ)^(c-1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
          (x : v.adicCompletion F) := by
      simp only [Units.val_zpow_eq_zpow_val]
      change (π : v.adicCompletion F)^c * ((x : v.adicCompletion F) / (π : v.adicCompletion F)) =
        (π : v.adicCompletion F)^(c-1) * (x : v.adicCompletion F)
      rw [zpow_sub₀ hpi, zpow_one]
      ring
    rw [he] at ht
    exact ht
  · intro hy x
    have hh := hc.1 (⟨y, hy⟩ * x)
    change psi0 v π hπ c (y * (x : v.adicCompletion F)) = 1 at hh
    exact hh

 abbrev piLattice (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) :=
  (v.adicCompletionIntegers F).toSubring.toAddSubgroup.map
    (AddMonoidHom.mulLeft (π : v.adicCompletion F))

 theorem stationary_piLattice (v : HeightOneSpectrum (𝓞 F))
    (hodd : ringChar (Residue v) ≠ 2)
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (hc : conductor v π hπ c) (u : (v.adicCompletionIntegers F)ˣ) :
    SArithmeticData.finiteStationarySubgroup v
      (localUnit v u * uniformizer v π hπ ^ (c-1)) (piLattice v π) =
        (v.adicCompletionIntegers F).toSubring.toAddSubgroup := by
  have hpi : (π : v.adicCompletion F) ≠ 0 := by
    intro h; exact hπ.ne_zero (Subtype.ext h)
  have h2 : IsUnit (2 : v.adicCompletionIntegers F) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [map_ofNat]
    exact Ring.two_ne_zero hodd
  obtain ⟨d, hd⟩ := h2.mul u.isUnit
  have hdu : (d : v.adicCompletion F) = 2 * (u : v.adicCompletion F) :=
    congrArg Subtype.val hd
  have hunit (y : v.adicCompletion F) :
      (d : v.adicCompletion F) * y ∈ v.adicCompletionIntegers F ↔
        y ∈ v.adicCompletionIntegers F := by
    constructor
    · intro h
      have hh := (v.adicCompletionIntegers F).toSubring.mul_mem (x := ((d⁻¹).val : v.adicCompletion F))
        (d⁻¹).val.property h
      change y ∈ (v.adicCompletionIntegers F).toSubring
      simpa only [← mul_assoc, show ((d⁻¹).val : v.adicCompletion F) * (d : v.adicCompletion F) = 1 from
        congrArg Subtype.val d.inv_val, one_mul] using hh
    · exact (v.adicCompletionIntegers F).toSubring.mul_mem d.val.property
  ext y
  change (∀ x ∈ piLattice v π, ResidueTrace.localTraceCharacter v
      (x * (2 * ((localUnit v u * uniformizer v π hπ ^ (c-1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y)) = 1) ↔ _
  have he (t : v.adicCompletionIntegers F) :
      ResidueTrace.localTraceCharacter v
        (((π : v.adicCompletion F) * (t : v.adicCompletion F)) *
          (2 * ((localUnit v u * uniformizer v π hπ ^ (c-1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y)) =
      psi0 v π hπ c (((d : v.adicCompletion F) * y) * (t : v.adicCompletion F)) := by
    change ResidueTrace.localTraceCharacter v _ = ResidueTrace.localTraceCharacter v _
    congr 1
    change _ = (((uniformizer v π hπ)^c : (v.adicCompletion F)ˣ) : v.adicCompletion F) * _
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
    change (π : v.adicCompletion F) * (t : v.adicCompletion F) *
      (2 * ((u : v.adicCompletion F) * (π : v.adicCompletion F)^(c-1)) * y) =
      (π : v.adicCompletion F)^c * (((d : v.adicCompletion F) * y) * (t : v.adicCompletion F))
    rw [hdu, zpow_sub₀ hpi, zpow_one]
    field_simp
    <;> ring
  change _ ↔ y ∈ v.adicCompletionIntegers F
  rw [← hunit, ← psi0_selfDual v π hπ c hc]
  constructor
  · intro h t
    rw [← he t]
    exact h _ (AddSubgroup.mem_map.mpr ⟨t, t.property, rfl⟩)
  · intro h x hx
    obtain ⟨t, ht, rfl⟩ := AddSubgroup.mem_map.mp hx
    exact (he ⟨t, ht⟩).trans (h ⟨t, ht⟩)

set_option maxHeartbeats 1000000 in
private theorem piLattice_admissible (v : HeightOneSpectrum (𝓞 F))
    (hodd : ringChar (Residue v) ≠ 2)
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (hc : conductor v π hπ c) (u : (v.adicCompletionIntegers F)ˣ) :
    SArithmeticData.FiniteQuadraticAdmissible v
      (localUnit v u * uniformizer v π hπ ^ (c-1)) (piLattice v π) := by
  refine ⟨⟨uniformizer v π hπ, rfl⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := AddSubgroup.mem_map.mp hx
    have hpi : (π : v.adicCompletion F) ≠ 0 := by
      intro h; exact hπ.ne_zero (Subtype.ext h)
    have he : ((localUnit v u * uniformizer v π hπ ^ (c-1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
        ((π : v.adicCompletion F) * t)^2 =
      (((uniformizer v π hπ)^c : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
        ((u : v.adicCompletion F) * (π : v.adicCompletion F) * t^2) := by
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
      change (u : v.adicCompletion F) * (π : v.adicCompletion F)^(c-1) * ((π : v.adicCompletion F) * t)^2 =
        (π : v.adicCompletion F)^c * ((u : v.adicCompletion F) * (π : v.adicCompletion F) * t^2)
      rw [zpow_sub₀ hpi, zpow_one]
      field_simp
      <;> ring
    change ResidueTrace.localTraceCharacter v (_ * ((π : v.adicCompletion F) * t)^2) = 1
    rw [he]
    have hh := hc.1 ((u : v.adicCompletionIntegers F) * π * (⟨t, ht⟩ : v.adicCompletionIntegers F)^2)
    convert hh using 1
  · rw [stationary_piLattice v hodd π hπ c hc u]
    rintro x hx
    obtain ⟨t, ht, rfl⟩ := AddSubgroup.mem_map.mp hx
    exact (v.adicCompletionIntegers F).toSubring.mul_mem π.property ht

 theorem piLattice_residue_kernel (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π)
    (x : v.adicCompletionIntegers F) :
    (x : v.adicCompletion F) ∈ piLattice v π ↔ IsLocalRing.residue _ x = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
  constructor
  · intro hx
    obtain ⟨t, ht, he⟩ := AddSubgroup.mem_map.mp hx
    exact ⟨⟨t, ht⟩, Subtype.ext he.symm⟩
  · rintro ⟨t, ht⟩
    exact AddSubgroup.mem_map.mpr ⟨t, t.property, (congrArg Subtype.val ht).symm⟩

 noncomputable def stationary_residue_equiv (v : HeightOneSpectrum (𝓞 F))
    (hodd : ringChar (Residue v) ≠ 2)
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (hc : conductor v π hπ c) (u : (v.adicCompletionIntegers F)ˣ) :
    SArithmeticData.finiteStationaryQuotient v
      (localUnit v u * uniformizer v π hπ ^ (c-1)) (piLattice v π) ≃+ Residue v := by
  let a := localUnit v u * uniformizer v π hπ ^ (c-1)
  let L := SArithmeticData.finiteStationarySubgroup v a (piLattice v π)
  have hL : L = (v.adicCompletionIntegers F).toSubring.toAddSubgroup :=
    stationary_piLattice v hodd π hπ c hc u
  let f : L →+ Residue v :=
    { toFun := fun x => IsLocalRing.residue _ ⟨x, (show (x : v.adicCompletion F) ∈ (v.adicCompletionIntegers F).toSubring.toAddSubgroup from hL ▸ x.property)⟩
      map_zero' := by exact map_zero (IsLocalRing.residue _)
      map_add' := by
        intro x y
        convert map_add (IsLocalRing.residue (v.adicCompletionIntegers F)) _ _ using 1
        congr 1 }
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective z
    refine ⟨⟨x, hL.symm ▸ x.property⟩, ?_⟩
    exact hx
  have hk : (piLattice v π).comap L.subtype = f.ker := by
    ext x
    change (x : v.adicCompletion F) ∈ piLattice v π ↔ f x = 0
    exact piLattice_residue_kernel v π hπ ⟨x, (show (x : v.adicCompletion F) ∈ (v.adicCompletionIntegers F).toSubring.toAddSubgroup from hL ▸ x.property)⟩
  exact (QuotientAddGroup.quotientAddEquivOfEq hk).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hf)

private theorem stationary_residue_equiv_mk (v : HeightOneSpectrum (𝓞 F))
    (hodd : ringChar (Residue v) ≠ 2)
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (hc : conductor v π hπ c) (u : (v.adicCompletionIntegers F)ˣ)
    (x : SArithmeticData.finiteStationarySubgroup v
      (localUnit v u * uniformizer v π hπ ^ (c-1)) (piLattice v π)) :
    stationary_residue_equiv v hodd π hπ c hc u (QuotientAddGroup.mk x) =
      IsLocalRing.residue _ ⟨x, (show (x : v.adicCompletion F) ∈
        (v.adicCompletionIntegers F).toSubring.toAddSubgroup from
          stationary_piLattice v hodd π hπ c hc u ▸ x.property)⟩ := by
  unfold stationary_residue_equiv
  rw [AddEquiv.trans_apply, QuotientAddGroup.quotientAddEquivOfEq_mk]
  rfl

private theorem stationary_phase_residue (v : HeightOneSpectrum (𝓞 F))
    (hodd : ringChar (Residue v) ≠ 2)
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (hc : conductor v π hπ c) (u : (v.adicCompletionIntegers F)ˣ)
    (x : SArithmeticData.finiteStationaryQuotient v
      (localUnit v u * uniformizer v π hπ ^ (c-1)) (piLattice v π)) :
    SArithmeticData.finiteStationaryPhase v
      (localUnit v u * uniformizer v π hπ ^ (c-1)) (piLattice v π) x =
      theta v π hπ c (IsLocalRing.residue _ (u : v.adicCompletionIntegers F) *
        (stationary_residue_equiv v hodd π hπ c hc u x)^2) := by
  induction x using Quotient.inductionOn with
  | h x =>
    change SArithmeticData.finiteStationaryPhase v _ _ (QuotientAddGroup.mk' _ x) = _
    rw [SArithmeticData.finiteStationaryPhase_mk v _ _ (piLattice_admissible v hodd π hπ c hc u),
      stationary_residue_equiv_mk]
    let xi : v.adicCompletionIntegers F := ⟨x, (show (x : v.adicCompletion F) ∈
      (v.adicCompletionIntegers F).toSubring.toAddSubgroup from
        stationary_piLattice v hodd π hπ c hc u ▸ x.property)⟩
    rw [← map_pow, ← map_mul, theta_on_lift v π hπ c hc]
    change ResidueTrace.localTraceCharacter v _ = ResidueTrace.localTraceCharacter v _
    congr 1
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
    change (u : v.adicCompletion F) * (π : v.adicCompletion F)^(c-1) * (x : v.adicCompletion F)^2 =
      (π : v.adicCompletion F)^c * (((u : v.adicCompletion F) * (x : v.adicCompletion F)^2) / (π : v.adicCompletion F))
    have hpi : (π : v.adicCompletion F) ≠ 0 := by
      intro h; exact hπ.ne_zero (Subtype.ext h)
    rw [zpow_sub₀ hpi, zpow_one]
    ring

attribute [local instance] residueFintype
open MeasureTheory
set_option maxHeartbeats 1000000 in

theorem gamma_preconductor_class (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hodd : ringChar (Residue v) ≠ 2)
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (hc : conductor v π hπ c) (u : (v.adicCompletionIntegers F)ˣ) :
    A.finiteGamma v (localUnit v u * uniformizer v π hπ ^ (c-1)) =
      quadratic v (IsLocalRing.residue _ (u : v.adicCompletionIntegers F)) *
        epsilon v π hπ c := by
  let a := localUnit v u * uniformizer v π hπ ^ (c-1)
  let H := piLattice v π
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  letI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  letI : Finite (SArithmeticData.finiteStationaryQuotient v a H) :=
    SArithmeticData.finiteStationaryQuotient_finite v a H (piLattice_admissible v hodd π hπ c hc u)
  letI : Fintype (SArithmeticData.finiteStationaryQuotient v a H) := Fintype.ofFinite _
  obtain ⟨h0, hadd, z, hz⟩ := theta_additive_nontrivial v π hπ c hc
  let θ : AddChar (Residue v) Circle := ⟨theta v π hπ c, h0, hadd⟩
  let ψ : AddChar (Residue v) ℂ := Circle.coeHom.compAddChar θ
  have hψ : ψ ≠ 1 := by
    intro h
    apply hz
    apply Circle.coe_injective
    exact congrArg (fun f : AddChar (Residue v) ℂ => f z) h
  let ur : (Residue v)ˣ := Units.map (IsLocalRing.residue (v.adicCompletionIntegers F)).toMonoidHom u
  have hsum : (∑ᶠ x : SArithmeticData.finiteStationaryQuotient v a H,
      (SArithmeticData.finiteStationaryPhase v a H x : ℂ)) =
        (quadratic v (ur : Residue v)) * ∑ x : Residue v, ψ (x^2) := by
    rw [finsum_eq_sum_of_fintype]
    calc
      _ = ∑ x : Residue v, ψ ((ur : Residue v) * x^2) :=
        Fintype.sum_equiv (stationary_residue_equiv v hodd π hπ c hc u).toEquiv _ _
          (fun x => congrArg (fun t : Circle => (t : ℂ)) (stationary_phase_residue v hodd π hπ c hc u x))
      _ = _ := square_sum_unit_dependence hodd ψ hψ ur
  let r := Real.sqrt ‖(2 : v.adicCompletion F) * (a : v.adicCompletion F)‖ *
    (A.finiteTraceHaar v (H : Set (v.adicCompletion F))).toReal
  have hr : 0 ≤ r := mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg
  have hgamma : A.finiteGamma v a = (r : ℂ) *
      ((quadratic v (ur : Residue v)) * ∑ x : Residue v, ψ (x^2)) := by
    have he := A.finiteOscillatoryValue_eq_gauss v a H (piLattice_admissible v hodd π hπ c hc u)
    unfold SArithmeticData.finiteOscillatoryValue SArithmeticData.finiteStationaryGauss at he
    rw [hsum] at he
    have hs : (Real.sqrt ‖(2 : v.adicCompletion F) * (a : v.adicCompletion F)‖ : ℂ) ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      apply (Real.sqrt_pos.mpr (norm_pos_iff.mpr ?_)).ne'
      exact mul_ne_zero (by exact_mod_cast (show (2:F) ≠ 0 from two_ne_zero)) a.ne_zero
    rw [div_eq_iff hs] at he
    rw [he]
    simp only [r, Complex.ofReal_mul]
    ring
  have hχnorm : ‖quadratic v (ur : Residue v)‖ = 1 := by
    have hs : (quadratic v (ur : Residue v))^2 = 1 := by
      exact_mod_cast quadraticChar_sq_one ur.ne_zero
    have hn := congrArg norm hs
    simp only [norm_pow, norm_one] at hn
    nlinarith [norm_nonneg (quadratic v (ur : Residue v))]
  have hrval : r = (Real.sqrt (Fintype.card (Residue v)))⁻¹ := by
    apply positive_normalization_from_norm (by exact_mod_cast Fintype.card_pos) hr
      ((quadratic v (ur : Residue v)) * ∑ x : Residue v, ψ (x^2))
    · rw [norm_mul, hχnorm, one_mul, square_sum_norm hodd ψ hψ]
    · rw [← hgamma, A.norm_finiteGamma]
  rw [hgamma, hrval]
  change _ = (quadratic v (ur : Residue v)) * ((∑ x : Residue v, ψ (x^2)) / _)
  simp only [Complex.ofReal_inv, div_eq_mul_inv]
  ring

end DedekindZetaZeroFree.OddEvaluation

end

end

section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SArithmeticData

variable {F : Type} [Field F] [NumberField F]

abbrev OddLocalResidue (v : HeightOneSpectrum (𝓞 F)) :=
  IsLocalRing.ResidueField (v.adicCompletionIntegers F)

theorem oddLocalResidue_finite (v : HeightOneSpectrum (𝓞 F)) :
    Finite (OddLocalResidue v) := by
  exact exteriorLocalResidue_finite v

noncomputable instance oddLocalResidueFintype (v : HeightOneSpectrum (𝓞 F)) :
    Fintype (OddLocalResidue v) := by
  letI := oddLocalResidue_finite v
  exact Fintype.ofFinite _

def oddLocalReduction (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletionIntegers F →+* OddLocalResidue v :=
  IsLocalRing.residue _

def oddLocalResidueLift (v : HeightOneSpectrum (𝓞 F))
    (x : OddLocalResidue v) : v.adicCompletionIntegers F :=
  Classical.choose (IsLocalRing.residue_surjective x)

def oddLocalUnit (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletionIntegers F)ˣ →* (v.adicCompletion F)ˣ :=
  Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom

def oddUniformizerUnit (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) :
    (v.adicCompletion F)ˣ :=
  Units.mk0 (π : v.adicCompletion F) (by
    intro h
    apply hπ.ne_zero
    exact Subtype.ext h)

def OddTraceConductor (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ) : Prop :=
  (∀ x : v.adicCompletionIntegers F,
    ResidueTrace.localTraceCharacter v
      (((oddUniformizerUnit v π hπ)^c : (v.adicCompletion F)ˣ) *
        (x : v.adicCompletion F)) = 1) ∧
  ∃ x : v.adicCompletionIntegers F,
    ResidueTrace.localTraceCharacter v
      (((oddUniformizerUnit v π hπ)^(c-1) : (v.adicCompletion F)ˣ) *
        (x : v.adicCompletion F)) ≠ 1

def oddConductorZeroCharacter (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ) :
    AddChar (v.adicCompletion F) Circle :=
  (ResidueTrace.localTraceCharacter v).compAddMonoidHom
    (AddMonoidHom.mulLeft (((oddUniformizerUnit v π hπ)^c :
      (v.adicCompletion F)ˣ) : v.adicCompletion F))

def oddResidueTheta (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (x : OddLocalResidue v) : Circle :=
  oddConductorZeroCharacter v π hπ c
    ((oddLocalResidueLift v x : v.adicCompletion F) / (π : v.adicCompletion F))

def oddResidueQuadraticChar (v : HeightOneSpectrum (𝓞 F))
    (x : OddLocalResidue v) : ℂ := (quadraticChar (OddLocalResidue v) x : ℂ)

def oddResidueEpsilon (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ) : ℂ :=
  (∑ x : OddLocalResidue v, (oddResidueTheta v π hπ c (x^2) : ℂ)) /
    (Real.sqrt (Fintype.card (OddLocalResidue v)) : ℂ)

def finiteQuadraticHilbertCoefficient (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a b : (v.adicCompletion F)ˣ) : ℂ :=
  if A.actualLocalSymbol v 2 (Or.inl rfl) a b = 1 then 1 else -1

private theorem oddLocalReduction_lift (v : HeightOneSpectrum (𝓞 F))
    (x : OddLocalResidue v) :
    oddLocalReduction v (oddLocalResidueLift v x) = x :=
  Classical.choose_spec (IsLocalRing.residue_surjective x)

private theorem oddConductorZeroCharacter_integral (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (hc : OddTraceConductor v π hπ c) (z : v.adicCompletionIntegers F) :
    oddConductorZeroCharacter v π hπ c (z : v.adicCompletion F) = 1 :=
  hc.1 z

theorem oddResidueTheta_on_lift (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (hc : OddTraceConductor v π hπ c) (x : v.adicCompletionIntegers F) :
    oddResidueTheta v π hπ c (oddLocalReduction v x) =
      oddConductorZeroCharacter v π hπ c
        ((x : v.adicCompletion F) / (π : v.adicCompletion F)) := by
  set y : v.adicCompletionIntegers F := oddLocalResidueLift v (oddLocalReduction v x) with hy
  have hres : IsLocalRing.residue (v.adicCompletionIntegers F) y =
      IsLocalRing.residue (v.adicCompletionIntegers F) x := by
    rw [hy]
    exact Classical.choose_spec (IsLocalRing.residue_surjective (oddLocalReduction v x))
  have hmem : y - x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    rw [map_sub, hres, sub_self]
  have hspan : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (hspan ▸ hmem)
  have hpi : (π : v.adicCompletion F) ≠ 0 := by
    intro h
    exact hπ.ne_zero (Subtype.ext h)
  have hK : (z : v.adicCompletion F) * (π : v.adicCompletion F) =
      (y : v.adicCompletion F) - (x : v.adicCompletion F) := by
    have h := congrArg (fun w : v.adicCompletionIntegers F => (w : v.adicCompletion F)) hz
    push_cast at h
    exact h
  have hdiv : (y : v.adicCompletion F) / (π : v.adicCompletion F) =
      (x : v.adicCompletion F) / (π : v.adicCompletion F) +
        (z : v.adicCompletion F) := by
    rw [div_eq_iff hpi]
    rw [add_mul, div_mul_cancel₀ _ hpi]
    rw [hK]
    ring
  change oddConductorZeroCharacter v π hπ c
      ((y : v.adicCompletion F) / (π : v.adicCompletion F)) =
    oddConductorZeroCharacter v π hπ c
      ((x : v.adicCompletion F) / (π : v.adicCompletion F))
  rw [hdiv, AddChar.map_add_eq_mul, oddConductorZeroCharacter_integral v π hπ c hc z, mul_one]

theorem oddResidueTheta_additive_nontrivial (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (hc : OddTraceConductor v π hπ c) :
    oddResidueTheta v π hπ c 0 = 1 ∧
    (∀ x y, oddResidueTheta v π hπ c (x+y) =
      oddResidueTheta v π hπ c x * oddResidueTheta v π hπ c y) ∧
    ∃ x, oddResidueTheta v π hπ c x ≠ 1 := by
  have key : ∀ a : v.adicCompletionIntegers F,
      oddConductorZeroCharacter v π hπ c ((a : v.adicCompletion F) / (π : v.adicCompletion F)) =
        oddResidueTheta v π hπ c (oddLocalReduction v a) :=
    fun a => (oddResidueTheta_on_lift v π hπ c hc a).symm
  have hpi : (π : v.adicCompletion F) ≠ 0 := by
    intro h
    exact hπ.ne_zero (Subtype.ext h)
  have hupow : ∀ n : ℤ,
      (((oddUniformizerUnit v π hπ)^n : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        (π : v.adicCompletion F)^n := by
    intro n
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_zero (oddLocalReduction v), ← key 0]
    simp
  · intro x y
    have hx : oddLocalReduction v (oddLocalResidueLift v x) = x :=
      oddLocalReduction_lift v x
    have hy : oddLocalReduction v (oddLocalResidueLift v y) = y :=
      oddLocalReduction_lift v y
    have hxy : oddLocalReduction v
        (oddLocalResidueLift v x + oddLocalResidueLift v y) = x + y := by
      rw [map_add, hx, hy]
    have h1 : oddResidueTheta v π hπ c (x + y) =
        oddConductorZeroCharacter v π hπ c
          ((oddLocalResidueLift v x : v.adicCompletion F) / (π : v.adicCompletion F) +
           (oddLocalResidueLift v y : v.adicCompletion F) / (π : v.adicCompletion F)) := by
      rw [← hxy, oddResidueTheta_on_lift v π hπ c hc]
      push_cast
      rw [add_div]
    have e1 : oddConductorZeroCharacter v π hπ c
        ((oddLocalResidueLift v x : v.adicCompletion F) / (π : v.adicCompletion F)) =
        oddResidueTheta v π hπ c x := by
      rw [← oddResidueTheta_on_lift v π hπ c hc (oddLocalResidueLift v x), hx]
    have e2 : oddConductorZeroCharacter v π hπ c
        ((oddLocalResidueLift v y : v.adicCompletion F) / (π : v.adicCompletion F)) =
        oddResidueTheta v π hπ c y := by
      rw [← oddResidueTheta_on_lift v π hπ c hc (oddLocalResidueLift v y), hy]
    rw [h1, AddChar.map_add_eq_mul, e1, e2]
  · obtain ⟨x', hx'⟩ := hc.2
    refine ⟨oddLocalReduction v x', ?_⟩
    rw [← key x']
    intro hcon
    change ResidueTrace.localTraceCharacter v
      ((((oddUniformizerUnit v π hπ)^c : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
        ((x' : v.adicCompletion F) / (π : v.adicCompletion F))) = 1 at hcon
    have harg : ((oddUniformizerUnit v π hπ ^ c : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
        ((x' : v.adicCompletion F) / (π : v.adicCompletion F)) =
        ((oddUniformizerUnit v π hπ ^ (c-1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
          (x' : v.adicCompletion F) := by
      rw [hupow c, hupow (c-1), ← mul_div_assoc, div_eq_iff hpi, mul_assoc,
        mul_comm (x' : v.adicCompletion F) (π : v.adicCompletion F), ← mul_assoc,
        ← zpow_add_one₀ hpi (c-1), sub_add_cancel]
    rw [harg] at hcon
    exact hx' hcon

theorem finiteGamma_odd_parity_reduction (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (u : (v.adicCompletionIntegers F)ˣ) (n : ℤ)
    (heven : A.finiteGamma v (oddLocalUnit v u * oddUniformizerUnit v π hπ ^ c) = 1)
    (hodd : A.finiteGamma v (oddLocalUnit v u * oddUniformizerUnit v π hπ ^ (c-1)) =
      oddResidueQuadraticChar v (oddLocalReduction v (u : v.adicCompletionIntegers F)) *
        oddResidueEpsilon v π hπ c) :
    A.finiteGamma v (oddLocalUnit v u * oddUniformizerUnit v π hπ ^ n) =
      if Even (n-c) then 1 else
        oddResidueQuadraticChar v (oddLocalReduction v (u : v.adicCompletionIntegers F)) *
          oddResidueEpsilon v π hπ c := by
  have scale (r k : ℤ) :
      A.finiteGamma v (oddLocalUnit v u * oddUniformizerUnit v π hπ ^ (r+2*k)) =
        A.finiteGamma v (oddLocalUnit v u * oddUniformizerUnit v π hπ ^ r) := by
    have heq : oddLocalUnit v u * oddUniformizerUnit v π hπ ^ (r+2*k) =
        (oddLocalUnit v u * oddUniformizerUnit v π hπ ^ r) *
          (oddUniformizerUnit v π hπ ^ k)^2 := by
      rw [zpow_add, mul_assoc, ← zpow_natCast, ← zpow_mul]
      congr 3
      omega
    rw [heq, A.finiteGamma_mul_sq]
  by_cases hn : Even (n-c)
  · rw [if_pos hn]
    obtain ⟨k, hk⟩ := hn
    have heq : n = c + 2*k := by omega
    rw [heq, scale, heven]
  · rw [if_neg hn]
    obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hn
    have heq : n = (c-1) + 2*(k+1) := by omega
    rw [heq, scale, hodd]

theorem finiteGamma_odd_evaluation (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hodd : ringChar (OddLocalResidue v) ≠ 2)
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (hc : OddTraceConductor v π hπ c)
    (u : (v.adicCompletionIntegers F)ˣ) (n : ℤ) :
    A.finiteGamma v (oddLocalUnit v u * oddUniformizerUnit v π hπ ^ n) =
      if Even (n-c) then 1 else
        oddResidueQuadraticChar v (oddLocalReduction v (u : v.adicCompletionIntegers F)) *
          oddResidueEpsilon v π hπ c := by
  apply A.finiteGamma_odd_parity_reduction v π hπ c u n
  · exact OddEvaluation.gamma_conductor_class A v hodd π hπ c hc u
  · exact OddEvaluation.gamma_preconductor_class A v hodd π hπ c hc u

private theorem square_sum_eq_gauss {k : Type*} [Field k] [Fintype k]
    (hodd : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) :
    (∑ x : k, ψ (x^2)) = gaussSum ((quadraticChar k).ringHomComp (Int.castRingHom ℂ)) ψ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun x : k => x^2) (fun x => ψ (x^2))]
  have count (y : k) : (Finset.univ.filter (fun x : k => x^2 = y)).card =
      (quadraticChar k y : ℂ) + 1 := by
    exact_mod_cast (by simpa only [Set.toFinset_setOf] using quadraticChar_card_sqrts hodd y)
  have inner (y : k) :
      (∑ x ∈ Finset.univ with x^2 = y, ψ (x^2)) =
        ((quadraticChar k y : ℂ) + 1) * ψ y := by
    trans (∑ _x ∈ Finset.univ with _x^2 = y, ψ y)
    · apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    · rw [Finset.sum_const, nsmul_eq_mul, count]
  simp_rw [inner, add_mul, one_mul]
  rw [Finset.sum_add_distrib, AddChar.sum_eq_zero_of_ne_one hψ, add_zero]
  rfl

private theorem residue_neg_one (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) : quadraticChar (OddLocalResidue v) (-1) = 1 := by
  let z : v.adicCompletion F := algebraMap F (v.adicCompletion F) (A.zeta12 ^ 3)
  have hz : z ^ 2 = -1 := weil_finite_minus_one_square F A v
  have hn : ‖z‖ ≤ 1 := by
    have h : ‖z‖ ^ 2 = 1 := by simpa only [norm_pow, norm_neg, norm_one] using congrArg (fun t : v.adicCompletion F => ‖t‖) hz
    nlinarith [norm_nonneg z]
  let zi : v.adicCompletionIntegers F := ⟨z, mem_adicCompletionIntegers_of_norm_le_one v hn⟩
  have hzi : zi ^ 2 = -1 := Subtype.ext hz
  have hres : oddLocalReduction v zi ^ 2 = -1 := by
    simpa only [map_pow, map_neg, map_one] using congrArg (oddLocalReduction v) hzi
  exact (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
    ⟨oddLocalReduction v zi, by simpa only [pow_two] using hres.symm⟩

theorem oddResidueEpsilon_sq (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hodd : ringChar (OddLocalResidue v) ≠ 2)
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) (c : ℤ)
    (hc : OddTraceConductor v π hπ c) :
    oddResidueEpsilon v π hπ c ^ 2 = 1 := by
  obtain ⟨h0, hadd, x, hx⟩ := oddResidueTheta_additive_nontrivial v π hπ c hc
  let θ : AddChar (OddLocalResidue v) Circle := ⟨oddResidueTheta v π hπ c, h0, hadd⟩
  let ψ : AddChar (OddLocalResidue v) ℂ := Circle.coeHom.compAddChar θ
  have hψ : ψ ≠ 1 := by
    intro h
    apply hx
    apply Subtype.ext
    have e := congrArg (fun f : AddChar (OddLocalResidue v) ℂ => f x) h
    exact e
  let χ := (quadraticChar (OddLocalResidue v)).ringHomComp (Int.castRingHom ℂ)
  have hχ : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := ℂ))).mpr
      (quadraticChar_ne_one hodd)
  have hs := gaussSum_sq hχ ((quadraticChar_isQuadratic _).comp _) (AddChar.IsPrimitive.of_ne_one hψ)
  have hneg : χ (-1) = 1 := by
    change (quadraticChar (OddLocalResidue v) (-1) : ℂ) = 1
    rw [residue_neg_one A v, Int.cast_one]
  rw [hneg, one_mul] at hs
  have hsum := square_sum_eq_gauss hodd ψ hψ
  change ((∑ x : OddLocalResidue v, ψ (x^2)) /
    (Real.sqrt (Fintype.card (OddLocalResidue v)) : ℂ)) ^ 2 = 1
  rw [hsum, div_pow, hs]
  have hcard : 0 < (Fintype.card (OddLocalResidue v) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsqrt : (Real.sqrt (Fintype.card (OddLocalResidue v)) : ℂ) ^ 2 =
      (Fintype.card (OddLocalResidue v) : ℂ) := by
    exact_mod_cast Real.sq_sqrt hcard.le
  rw [hsqrt, div_self]
  exact_mod_cast Fintype.card_ne_zero

theorem finiteWeilPhase_odd_hilbert_defect (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hodd : ringChar (OddLocalResidue v) ≠ 2)
    (a b : (v.adicCompletion F)ˣ) :
    A.finiteWeilPhase v a * A.finiteWeilPhase v b =
      A.finiteQuadraticHilbertCoefficient v a b * A.finiteWeilPhase v (a*b) := by
  apply OddEvaluation.hilbert_defect_of_parity_evaluation A v hodd
  · intro π hπ c hc u n
    exact A.finiteGamma_odd_evaluation v hodd π hπ c hc u n
  · intro π hπ c hc
    exact A.oddResidueEpsilon_sq v hodd π hπ c hc

end DedekindZetaZeroFree.SArithmeticData

end

end
