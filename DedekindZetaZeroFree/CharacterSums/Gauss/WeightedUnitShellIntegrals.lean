module

public import DedekindZetaZeroFree.Arithmetic.Units.PrincipalizingRayCharacterContext
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.FiniteExceptionalRepresentationData

@[expose] public section

section

open scoped Valued ValuativeRel ENNReal
open MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPExteriorWeightedShellIntegrals

noncomputable section
set_option autoImplicit false

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Fintype 𝓀[K]]

def weightedIntegrand (f : 𝓀[K] → ℂ) (ψ : AddChar K ℂ)
    (π : 𝒪[K]) (n : ℤ) (x : K) : ℂ := by
  classical
  exact if hx : x ∈ (𝒪[K] : Set K) then
    f (IsLocalRing.residue 𝒪[K] ⟨x, hx⟩) * star (ψ ((π : K) ^ n * x))
  else 0

def weightedShellIntegral [MeasurableSpace K] (μ : Measure K)
    (f : 𝓀[K] → ℂ) (ψ : AddChar K ℂ) (π : 𝒪[K]) (n : ℤ) : ℂ :=
  ∫ x in KPTameGauss.integerUnitShell K, weightedIntegrand f ψ π n x ∂μ

theorem weightedShellIntegral_nonnegative [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] (hμ : μ (𝒪[K] : Set K) = 1)
    (π : 𝒪[K]) (hπ : Irreducible π) (ψ : AddChar K ℂ)
    (hψO : ∀ u : 𝒪[K], ψ (u : K) = 1)
    (f : 𝓀[K] → ℂ) (hf : f 0 = 0) (n : ℤ) (hn : 0 ≤ n) :
    weightedShellIntegral μ f ψ π n =
      (∑ a : 𝓀[K], f a) / (Fintype.card 𝓀[K] : ℂ) := by
  classical
  let R := (valuation K).integer
  let k := IsLocalRing.ResidueField R
  let r : R →+* k := IsLocalRing.residue R
  letI : Fintype k := ‹Fintype 𝓀[K]›
  letI : MeasurableSpace k := ⊤
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  have hR : MeasurableSet (R : Set K) := (Valued.isClosed_integer K).measurableSet
  let ν : Measure R := μ.comap R.subtype
  haveI : ν.IsAddLeftInvariant := Measure.IsAddLeftInvariant.comap μ
    (f := R.subtype.toAddMonoidHom) (MeasurableEmbedding.subtype_coe hR)
  have hr : Measurable r := by
    apply measurable_to_countable
    intro y
    have he : r ⁻¹' {r y} = (fun u : R => u - y) ⁻¹' (IsLocalRing.maximalIdeal R : Set R) := by
      ext u
      change r u = r y ↔ u - y ∈ IsLocalRing.maximalIdeal R
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    rw [he]
    exact (IsNoetherianRing.isClosed_ideal _).measurableSet.preimage (by fun_prop)
  let ρ : Measure k := ν.map r
  haveI : ρ.IsAddLeftInvariant := isAddLeftInvariant_map r.toAddMonoidHom.toAddHom hr
    IsLocalRing.residue_surjective
  have hmass : ρ Set.univ = 1 := by
    rw [Measure.map_apply hr MeasurableSet.univ, Set.preimage_univ]
    calc
      ν Set.univ = μ (Subtype.val '' (Set.univ : Set R)) := by
        exact comap_subtype_coe_apply hR μ Set.univ
      _ = μ (R : Set K) := by congr 1; ext x; simp
      _ = 1 := hμ
  haveI : IsFiniteMeasure ρ := ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩
  have hsingle (x : k) : ρ {x} = ρ {0} := by
    have he : (fun y : k => -x + y) ⁻¹' {0} = {x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor <;> intro h
      · linear_combination h
      · rw [h]; simp
    rw [← he, measure_preimage_add]
  have hsinglemass : (Fintype.card k : ℝ≥0∞) * ρ {0} = 1 := by
    have H := sum_measure_singleton (μ := ρ) (s := Finset.univ)
    simp only [hsingle, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at H
    simpa [hmass] using H
  have hreal (x : k) : ρ.real {x} = 1 / (Fintype.card k : ℝ) := by
    have H := congrArg ENNReal.toReal hsinglemass
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at H
    change (ρ {x}).toReal = _
    rw [hsingle]
    exact (eq_div_iff (by exact_mod_cast Fintype.card_pos.ne')).mpr (by simpa [mul_comm] using H)
  let F : k → ℂ := f
  have hi : (∫ u : R, F (r u) ∂ν) =
      (∑ a : k, f a) / (Fintype.card k : ℂ) := by
    rw [← integral_map hr.aemeasurable ((measurable_of_countable F).aestronglyMeasurable),
      integral_fintype Integrable.of_finite]
    change (∑ x : k, ρ.real {x} • F x) = _
    simp only [hreal, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
    simp only [one_div, ← Finset.mul_sum, ← div_eq_inv_mul]
    rw [← Finset.sum_div]
  have hzero : F 0 = 0 := by simp [F, hf]
  have hs : KPTameGauss.integerUnitShell K = R.subtype '' {u : R | IsUnit u} := by
    ext x
    simp [KPTameGauss.integerUnitShell, R, and_comm]
  have hS : MeasurableSet (KPTameGauss.integerUnitShell K) := by
    rw [hs]
    apply (MeasurableEmbedding.subtype_coe hR).measurableSet_image.mpr
    have he : {u : R | IsUnit u} = (r ⁻¹' {0})ᶜ := by
      ext u
      simpa only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff] using
          (IsLocalRing.residue_ne_zero_iff_isUnit u).symm
    rw [he]
    exact (hr (measurableSet_singleton _)).compl
  have he : (KPTameGauss.integerUnitShell K).indicator (weightedIntegrand f ψ π n) =
      (R : Set K).indicator (fun x => if hx : x ∈ (R : Set K) then F (r ⟨x,hx⟩) else 0) := by
    funext x
    by_cases hx : x ∈ (R : Set K)
    · let u : R := ⟨x,hx⟩
      by_cases hu : IsUnit u
      · have hxs : x ∈ KPTameGauss.integerUnitShell K := ⟨u,rfl,hu⟩
        have hcond : x ∈ ((valuation K).integer : Set K) := hx
        simp only [Set.indicator_of_mem hxs, Set.indicator_of_mem hx, dif_pos hx,
          weightedIntegrand, dif_pos hcond, F]
        obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hn
        have hp : ψ ((π : K) ^ n * x) = 1 := by
          simpa [hm] using hψO (π ^ m * u)
        rw [hp, star_one, mul_one]
      · have hxs : x ∉ KPTameGauss.integerUnitShell K := by
          rintro ⟨v,hv,hvu⟩
          have : v = u := Subtype.ext hv
          exact hu (this ▸ hvu)
        have hz : r u = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hu
        rw [Set.indicator_of_notMem hxs, Set.indicator_of_mem hx, dif_pos hx]
        change 0 = F (r u)
        rw [hz, hzero]
    · have hxs : x ∉ KPTameGauss.integerUnitShell K := by
        rintro ⟨v,rfl,-⟩
        exact hx v.property
      simp [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hx]
  rw [weightedShellIntegral, ← integral_indicator hS, he, integral_indicator hR,
    ← integral_subtype_comap hR]
  convert hi using 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [dif_pos x.property]
  rfl

end
end DedekindZetaZeroFree.KPExteriorWeightedShellIntegrals

end

section

namespace DedekindZetaZeroFree.KPExteriorWeightedShellIntegrals
noncomputable section
set_option autoImplicit false

theorem even_sextic_residue_sums
    {k : Type*} [Field k] [Fintype k] (χ : MulChar k ℂ)
    (hχ : orderOf χ = 6) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (l : ℤ) :
    (∑ a : k, (χ ^ (-2 * l)) a) =
      (if (3 : ℤ) ∣ l then (Fintype.card k : ℂ) - 1 else 0) ∧
    (∑ a : k, (χ ^ (-2 * l)) a * star (ψ a)) =
      (if (3 : ℤ) ∣ l then -1 else gaussSum (χ ^ (-2 * l)) ψ) := by
  classical
  have h3dvd : (3 : ℤ) ∣ l ↔ (6 : ℤ) ∣ (-2 * l) := by
    constructor <;> intro h <;> omega
  have hpow_one : χ ^ (-2 * l) = 1 ↔ (3 : ℤ) ∣ l := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hχ]
    exact h3dvd.symm
  have hχn_neg_one : (χ ^ (-2 * l)) (-1) = 1 := by
    have h : (-1 : kˣ) ^ (-2 * l) = 1 := by
      rw [show (-2 * l : ℤ) = 2 * (-l) by ring, zpow_mul,
        show (-1 : kˣ) ^ (2 : ℤ) = 1 by norm_num, one_zpow]
    have hcoe := MulChar.zpow_apply_coe χ (-2 * l) (-1 : kˣ)
    rw [h] at hcoe
    simpa using hcoe
  have hstar : ∀ a : k, star (ψ a) = ψ⁻¹ a := by
    intro a
    rw [AddChar.inv_apply, AddChar.map_neg_eq_conj]
    rfl
  have hmain : (∑ a : k, (χ ^ (-2 * l)) a * star (ψ a)) =
      gaussSum (χ ^ (-2 * l)) ψ := by
    have h1 : (∑ a : k, (χ ^ (-2 * l)) a * star (ψ a)) =
        ∑ a : k, (χ ^ (-2 * l)) a * ψ⁻¹ a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hstar a]
    have h2 : (∑ a : k, (χ ^ (-2 * l)) a * ψ⁻¹ a) =
        gaussSum (χ ^ (-2 * l)) ψ⁻¹ := by rw [gaussSum]
    have h3 : gaussSum (χ ^ (-2 * l)) ψ⁻¹ = gaussSum (χ ^ (-2 * l)) ψ := by
      have hh := mul_gaussSum_inv_eq_gaussSum (χ ^ (-2 * l)) ψ
      rwa [hχn_neg_one, one_mul] at hh
    rw [h1, h2, h3]
  constructor
  · by_cases h : (3 : ℤ) ∣ l
    · rw [if_pos h, hpow_one.mpr h, MulChar.sum_one_eq_card_units, Fintype.card_units,
        Nat.cast_sub (by have := Fintype.card_pos (α := k); omega)]
      norm_num
    · rw [if_neg h]
      exact MulChar.sum_eq_zero_of_ne_one (fun hc => h (hpow_one.mp hc))
  · rw [hmain]
    by_cases h : (3 : ℤ) ∣ l
    · rw [if_pos h, hpow_one.mpr h, gaussSum_one_left hψ]
    · rw [if_neg h]

end
end DedekindZetaZeroFree.KPExteriorWeightedShellIntegrals

end

section

open scoped Valued ValuativeRel ENNReal
open MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPExteriorWeightedShellIntegrals
noncomputable section
set_option autoImplicit false
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Fintype 𝓀[K]]

theorem weightedShellIntegral_terminal [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] (hμ : μ (𝒪[K] : Set K) = 1)
    (π : 𝒪[K]) (hπ : Irreducible π) (ψ : AddChar K ℂ)
    (hψO : ∀ u : 𝒪[K], ψ (u : K) = 1)
    (ψbar : AddChar 𝓀[K] ℂ)
    (hbar : ∀ u : 𝒪[K], ψbar (IsLocalRing.residue 𝒪[K] u) =
      ψ ((π : K)⁻¹ * (u : K)))
    (f : 𝓀[K] → ℂ) (hf : f 0 = 0) :
    weightedShellIntegral μ f ψ π (-1) =
      (∑ a : 𝓀[K], f a * star (ψbar a)) / (Fintype.card 𝓀[K] : ℂ) := by
  classical
  let R := (valuation K).integer
  let k := IsLocalRing.ResidueField R
  let r : R →+* k := IsLocalRing.residue R
  letI : Fintype k := ‹Fintype 𝓀[K]›
  letI : MeasurableSpace k := ⊤
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  have hR : MeasurableSet (R : Set K) := (Valued.isClosed_integer K).measurableSet
  let ν : Measure R := μ.comap R.subtype
  haveI : ν.IsAddLeftInvariant := Measure.IsAddLeftInvariant.comap μ
    (f := R.subtype.toAddMonoidHom) (MeasurableEmbedding.subtype_coe hR)
  have hr : Measurable r := by
    apply measurable_to_countable
    intro y
    have he : r ⁻¹' {r y} = (fun u : R => u - y) ⁻¹' (IsLocalRing.maximalIdeal R : Set R) := by
      ext u
      change r u = r y ↔ u - y ∈ IsLocalRing.maximalIdeal R
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    rw [he]
    exact (IsNoetherianRing.isClosed_ideal _).measurableSet.preimage (by fun_prop)
  let ρ : Measure k := ν.map r
  haveI : ρ.IsAddLeftInvariant := isAddLeftInvariant_map r.toAddMonoidHom.toAddHom hr
    IsLocalRing.residue_surjective
  have hmass : ρ Set.univ = 1 := by
    rw [Measure.map_apply hr MeasurableSet.univ, Set.preimage_univ]
    calc
      ν Set.univ = μ (Subtype.val '' (Set.univ : Set R)) := by
        exact comap_subtype_coe_apply hR μ Set.univ
      _ = μ (R : Set K) := by congr 1; ext x; simp
      _ = 1 := hμ
  haveI : IsFiniteMeasure ρ := ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩
  have hsingle (x : k) : ρ {x} = ρ {0} := by
    have he : (fun y : k => -x + y) ⁻¹' {0} = {x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor <;> intro h
      · linear_combination h
      · rw [h]; simp
    rw [← he, measure_preimage_add]
  have hsinglemass : (Fintype.card k : ℝ≥0∞) * ρ {0} = 1 := by
    have H := sum_measure_singleton (μ := ρ) (s := Finset.univ)
    simp only [hsingle, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at H
    simpa [hmass] using H
  have hreal (x : k) : ρ.real {x} = 1 / (Fintype.card k : ℝ) := by
    have H := congrArg ENNReal.toReal hsinglemass
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at H
    change (ρ {x}).toReal = _
    rw [hsingle]
    exact (eq_div_iff (by exact_mod_cast Fintype.card_pos.ne')).mpr (by simpa [mul_comm] using H)
  let F : k → ℂ := fun x => f x * star (ψbar x)
  have hi : (∫ u : R, F (r u) ∂ν) =
      (∑ a : k, f a * star (ψbar a)) / (Fintype.card k : ℂ) := by
    rw [← integral_map hr.aemeasurable ((measurable_of_countable F).aestronglyMeasurable),
      integral_fintype Integrable.of_finite]
    change (∑ x : k, ρ.real {x} • F x) = _
    simp only [hreal, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
    simp only [one_div, ← Finset.mul_sum, ← div_eq_inv_mul]
    rw [← Finset.sum_div]
  have hzero : F 0 = 0 := by simp [F, hf]
  have hs : KPTameGauss.integerUnitShell K = R.subtype '' {u : R | IsUnit u} := by
    ext x
    simp [KPTameGauss.integerUnitShell, R, and_comm]
  have hS : MeasurableSet (KPTameGauss.integerUnitShell K) := by
    rw [hs]
    apply (MeasurableEmbedding.subtype_coe hR).measurableSet_image.mpr
    have he : {u : R | IsUnit u} = (r ⁻¹' {0})ᶜ := by
      ext u
      simpa only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff] using
          (IsLocalRing.residue_ne_zero_iff_isUnit u).symm
    rw [he]
    exact (hr (measurableSet_singleton _)).compl
  have he : (KPTameGauss.integerUnitShell K).indicator (weightedIntegrand f ψ π (-1)) =
      (R : Set K).indicator (fun x => if hx : x ∈ (R : Set K) then F (r ⟨x,hx⟩) else 0) := by
    funext x
    by_cases hx : x ∈ (R : Set K)
    · let u : R := ⟨x,hx⟩
      by_cases hu : IsUnit u
      · have hxs : x ∈ KPTameGauss.integerUnitShell K := ⟨u,rfl,hu⟩
        have hcond : x ∈ ((valuation K).integer : Set K) := hx
        simp only [Set.indicator_of_mem hxs, Set.indicator_of_mem hx, dif_pos hx,
          weightedIntegrand, dif_pos hcond, F]
        rw [show (π : K) ^ (-1 : ℤ) * x = (π : K)⁻¹ * (u : K) by rw [zpow_neg_one]]
        rw [← hbar u]
      · have hxs : x ∉ KPTameGauss.integerUnitShell K := by
          rintro ⟨v,hv,hvu⟩
          have : v = u := Subtype.ext hv
          exact hu (this ▸ hvu)
        have hz : r u = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hu
        rw [Set.indicator_of_notMem hxs, Set.indicator_of_mem hx, dif_pos hx]
        change 0 = F (r u)
        rw [hz, hzero]
    · have hxs : x ∉ KPTameGauss.integerUnitShell K := by
        rintro ⟨v,rfl,-⟩
        exact hx v.property
      simp [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hx]
  rw [weightedShellIntegral, ← integral_indicator hS, he, integral_indicator hR,
    ← integral_subtype_comap hR]
  convert hi using 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [dif_pos x.property]
  rfl

end
end DedekindZetaZeroFree.KPExteriorWeightedShellIntegrals

end

section

open scoped Valued ValuativeRel
open MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPExteriorWeightedShellIntegrals
noncomputable section
set_option autoImplicit false
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Fintype 𝓀[K]]

theorem weightedShellIntegral_deep [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] (hμ : μ (𝒪[K] : Set K) = 1)
    (π : 𝒪[K]) (hπ : Irreducible π) (ψ : AddChar K ℂ)
    (hψcont : Continuous ψ) (hψunitary : ∀ x : K, ‖ψ x‖ = 1)
    (hψO : ∀ u : 𝒪[K], ψ (u : K) = 1)
    (hψnontrivial : ∃ u : 𝒪[K], ψ ((π : K)⁻¹ * (u : K)) ≠ 1)
    (f : 𝓀[K] → ℂ) (n : ℤ) (hn : n < -1) :
    weightedShellIntegral μ f ψ π n = 0 := by
  classical
  have hπ0 : (π : K) ≠ 0 := by exact_mod_cast hπ.ne_zero
  obtain ⟨u₀, hu₀⟩ := hψnontrivial
  set kk : ℕ := (-n - 1).toNat with hkk
  have hkk_eq : (kk : ℤ) = -n - 1 := by
    rw [hkk]; exact Int.toNat_of_nonneg (by omega)
  let aR : 𝒪[K] := π ^ kk * u₀
  let a : K := (aR : K)
  have ha_def : a = (π : K) ^ kk * (u₀ : K) := by simp [a, aR]
  have haR_max : aR ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
    refine ⟨π ^ (kk - 1) * u₀, ?_⟩
    have hpow : π ^ kk = π * π ^ (kk - 1) := by
      conv_lhs => rw [show kk = (kk - 1) + 1 by omega]
      rw [pow_succ']
    show π ^ kk * u₀ = π * (π ^ (kk - 1) * u₀)
    rw [hpow]; ring
  have hres_a : IsLocalRing.residue 𝒪[K] aR = 0 :=
    (IsLocalRing.residue_eq_zero_iff aR).mpr haR_max
  have hpa : (π : K) ^ n * a = (π : K)⁻¹ * (u₀ : K) := by
    rw [ha_def, ← mul_assoc, ← zpow_natCast (π : K) kk, ← zpow_add₀ hπ0, hkk_eq]
    rw [show n + (-n - 1) = (-1 : ℤ) by omega, zpow_neg_one]
  set c : ℂ := star (ψ ((π : K) ^ n * a)) with hc
  have hc_ne : c ≠ 1 := by
    rw [hc, hpa]
    intro h
    exact hu₀ (by simpa using congrArg star h)
  set S : Set K := KPTameGauss.integerUnitShell K with hSdef
  set G : K → ℂ := weightedIntegrand f ψ π n with hGdef
  have hS_closed : IsClosed S := by
    rw [hSdef]
    have he : KPTameGauss.integerUnitShell K = {u | valuation K u = 1} := by
      ext u
      constructor
      · rintro ⟨u, rfl, hu⟩
        exact (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp hu
      · intro hu
        exact ⟨⟨u, hu.le⟩, rfl,
          (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mpr hu⟩
    rw [he]
    letI : TopologicalSpace (ValueGroupWithZero K) := WithZeroTopology.topologicalSpace
    letI : T5Space (ValueGroupWithZero K) := WithZeroTopology.t5Space
    exact (isClosed_singleton (x := (1 : ValueGroupWithZero K))).preimage
      (IsValuativeTopology.continuous_valuation (R := K))
  have hS_meas : MeasurableSet S := hS_closed.measurableSet
  have hmem : ∀ x : K, x + a ∈ S ↔ x ∈ S := by
    intro x
    rw [hSdef]
    constructor
    · rintro ⟨v, hv, hvu⟩
      refine ⟨v - aR, ?_, ?_⟩
      · change (v : K) - (aR : K) = x
        rw [hv]; ring
      · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, hres_a, sub_zero]
        exact (IsLocalRing.residue_ne_zero_iff_isUnit v).mpr hvu
    · rintro ⟨u, hu, huu⟩
      refine ⟨u + aR, ?_, ?_⟩
      · change (u : K) + (aR : K) = x + a
        rw [hu]
      · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_add, hres_a, add_zero]
        exact (IsLocalRing.residue_ne_zero_iff_isUnit u).mpr huu
  have hrel : Set.EqOn (fun x => G (x + a)) (fun x => c * G x) S := by
    intro x hx
    rw [hSdef] at hx
    obtain ⟨u, hu, huu⟩ := hx
    have hxR : x ∈ (𝒪[K] : Set K) := by rw [← hu]; exact u.property
    have hxaR : x + a ∈ (𝒪[K] : Set K) := by
      have hh : x + a = ((u + aR : 𝒪[K]) : K) := by
        rw [← hu]
        change (u : K) + a = (u : K) + (aR : K)
        rfl
      rw [hh]; exact (u + aR).property
    have hres : IsLocalRing.residue 𝒪[K] ⟨x + a, hxaR⟩ =
        IsLocalRing.residue 𝒪[K] ⟨x, hxR⟩ := by
      have hsum : (⟨x + a, hxaR⟩ : 𝒪[K]) = ⟨x, hxR⟩ + aR := by
        apply Subtype.ext
        change x + a = x + (aR : K)
        rfl
      rw [hsum, map_add, hres_a, add_zero]
    have hphase : star (ψ ((π : K) ^ n * (x + a))) =
        star (ψ ((π : K) ^ n * x)) * c := by
      rw [mul_add, ψ.map_add_eq_mul, star_mul, hc]
      ring
    rw [hGdef]
    simp only [weightedIntegrand, dif_pos hxaR, dif_pos hxR]
    rw [hres, hphase]
    ring
  have hshift : (∫ x in S, G (x + a) ∂μ) = ∫ x in S, G x ∂μ := by
    have he : (fun x => S.indicator G (x + a)) = S.indicator (fun x => G (x + a)) := by
      funext x
      by_cases hx : x ∈ S <;> simp [Set.indicator, hx, hmem x]
    have hi := integral_add_right_eq_self (μ := μ) (S.indicator G) a
    rw [he, integral_indicator hS_meas, integral_indicator hS_meas] at hi
    exact hi
  have h2 : (∫ x in S, G (x + a) ∂μ) = ∫ x in S, c * G x ∂μ :=
    setIntegral_congr_fun hS_meas hrel
  have h3 : (∫ x in S, c * G x ∂μ) = c * ∫ x in S, G x ∂μ :=
    integral_const_mul c (fun x => G x)
  have h4 : ∫ x in S, G x ∂μ = c * ∫ x in S, G x ∂μ :=
    hshift.symm.trans (h2.trans h3)
  have h5 : (1 - c) * (∫ x in S, G x ∂μ) = 0 := by
    rw [sub_mul, one_mul, h4.symm, sub_self]
  have h1c : (1 - c) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc_ne)
  have hzero : ∫ x in S, G x ∂μ = 0 := (mul_eq_zero.mp h5).resolve_left h1c
  simpa [weightedShellIntegral, hSdef, hGdef] using hzero

end
end DedekindZetaZeroFree.KPExteriorWeightedShellIntegrals

end

section

open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPExteriorUnitShellIntegrals

noncomputable section
set_option autoImplicit false

section Local

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

def ConductorZero (ψ : AddChar K ℂ) (π : 𝒪[K]) : Prop :=
  (∀ u : 𝒪[K], ψ (u : K) = 1) ∧
    ∃ u : 𝒪[K], ψ ((π : K)⁻¹ * (u : K)) ≠ 1

theorem residuePhase_lift_independent
    (π : 𝒪[K]) (hπ : Irreducible π)
    (ψ : AddChar K ℂ) (hψcont : Continuous ψ)
    (hψunitary : ∀ x : K, ‖ψ x‖ = 1) (hcond : ConductorZero ψ π)
    (u v : 𝒪[K])
    (huv : IsLocalRing.residue 𝒪[K] u = IsLocalRing.residue 𝒪[K] v) :
    ψ ((π : K)⁻¹ * (u : K)) = ψ ((π : K)⁻¹ * (v : K)) := by
  obtain ⟨ψbar, hbar, _⟩ := KPTameGauss.exists_residue_addChar π hπ ψ hψcont
    hcond.1 (by simpa [div_eq_mul_inv, mul_comm] using hcond.2)
  simpa [div_eq_mul_inv, mul_comm] using (hbar.2 u).symm.trans
    ((congrArg ψbar huv).trans (hbar.2 v))

theorem exists_unique_residue_addChar
    (π : 𝒪[K]) (hπ : Irreducible π)
    (ψ : AddChar K ℂ) (hψcont : Continuous ψ)
    (hψunitary : ∀ x : K, ‖ψ x‖ = 1) (hcond : ConductorZero ψ π) :
    ∃! ψbar : AddChar 𝓀[K] ℂ,
      ψbar ≠ 1 ∧ ψbar.IsPrimitive ∧
        ∀ u : 𝒪[K], ψbar (IsLocalRing.residue 𝒪[K] u) =
          ψ ((π : K)⁻¹ * (u : K)) := by
  obtain ⟨ψbar, hbar, huniq⟩ := KPTameGauss.exists_residue_addChar π hπ ψ hψcont
    hcond.1 (by simpa [div_eq_mul_inv, mul_comm] using hcond.2)
  refine ⟨ψbar, ⟨hbar.1, AddChar.IsPrimitive.of_ne_one hbar.1, ?_⟩, ?_⟩
  · simpa [div_eq_mul_inv, mul_comm] using hbar.2
  · intro ψbar' hbar'
    apply huniq ψbar'
    exact ⟨hbar'.1, by simpa [div_eq_mul_inv, mul_comm] using hbar'.2.2⟩

variable [Fintype 𝓀[K]]

def qPower (r : ℝ) : ℂ :=
  (Real.rpow (Fintype.card 𝓀[K] : ℝ) r : ℂ)

def g (χκ : MulChar 𝓀[K] ℂ) (ψbar : AddChar 𝓀[K] ℂ) (j : ℤ) : ℂ :=
  qPower (K := K) (-(1 / 2 : ℝ)) * gaussSum (χκ ^ j) ψbar

theorem g_eq_normalizedGaussPower (χκ : MulChar 𝓀[K] ℂ)
    (ψbar : AddChar 𝓀[K] ℂ) (j : ℕ) :
    g χκ ψbar (j : ℤ) = FiniteGauss.normalizedGaussPower χκ ψbar j := by
  have hQ : (0 : ℝ) ≤ Fintype.card 𝓀[K] := by positivity
  unfold g qPower FiniteGauss.normalizedGaussPower FiniteGauss.gaussPower
  rw [Real.rpow_eq_pow, Real.rpow_neg hQ, ← Real.sqrt_eq_rpow]
  simp only [zpow_natCast, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]

theorem g_periodic (χκ : MulChar 𝓀[K] ℂ) (hχκ : orderOf χκ = 6)
    (ψbar : AddChar 𝓀[K] ℂ) (j : ℤ) :
    g χκ ψbar (j + 6) = g χκ ψbar j := by
  have h6 : χκ ^ (6 : ℤ) = 1 := by
    have H := pow_orderOf_eq_one χκ
    rw [hχκ] at H
    exact_mod_cast H
  simp only [g, zpow_add, h6, mul_one]

theorem g_two_mul_four (χκ : MulChar 𝓀[K] ℂ) (hχκ : orderOf χκ = 6)
    (ψbar : AddChar 𝓀[K] ℂ) (hψbar : ψbar ≠ 1) :
    g χκ ψbar 2 * g χκ ψbar 4 = 1 := by
  have ho : orderOf (χκ ^ 2) = 3 := by
    rw [orderOf_pow' _ (by norm_num : (2 : ℕ) ≠ 0), hχκ]
    norm_num
  have hn : χκ ^ 2 ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have hv : (χκ ^ 2) (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) (by
      rw [← pow_mul]
      norm_num
      exact hχκ ▸ pow_orderOf_eq_one χκ)
  have H := gaussSum_mul_gaussSum_pow_orderOf_sub_one hn
    (AddChar.IsPrimitive.of_ne_one hψbar)
  have hprod : FiniteGauss.gaussPower χκ ψbar 2 *
      FiniteGauss.gaussPower χκ ψbar 4 = (Fintype.card 𝓀[K] : ℂ) := by
    simpa [FiniteGauss.gaussPower, ho, ← pow_mul, hv] using H
  have hpos : (0 : ℝ) < Fintype.card 𝓀[K] := by exact_mod_cast Fintype.card_pos
  have hs2 : (Real.sqrt (Fintype.card 𝓀[K]) : ℂ) ^ 2 = Fintype.card 𝓀[K] := by
    norm_cast
    exact Real.sq_sqrt hpos.le
  rw [show (2 : ℤ) = (2 : ℕ) by rfl, show (4 : ℤ) = (4 : ℕ) by rfl,
    g_eq_normalizedGaussPower, g_eq_normalizedGaussPower]
  rw [FiniteGauss.normalizedGaussPower, FiniteGauss.normalizedGaussPower,
    div_mul_div_comm, hprod, ← pow_two, hs2]
  exact div_self (by exact_mod_cast Fintype.card_pos.ne')

def unitCharacter (χκ : MulChar 𝓀[K] ℂ) (u : 𝒪[K]ˣ) : ℂ :=
  χκ (IsLocalRing.residue 𝒪[K] (u : 𝒪[K]))

def shellIntegrand (χκ : MulChar 𝓀[K] ℂ) (ψ : AddChar K ℂ)
    (π : 𝒪[K]) (e : ℕ) (l : ℤ) (x : K) : ℂ := by
  classical
  exact if hx : x ∈ (𝒪[K] : Set K) then
    χκ (IsLocalRing.residue 𝒪[K] ⟨x, hx⟩) ^ (-2 * l) *
      star (ψ ((π : K) ^ ((e : ℤ) - l) * x))
  else 0

def A [MeasurableSpace K] (μ : Measure K) (χκ : MulChar 𝓀[K] ℂ)
    (ψ : AddChar K ℂ) (π : 𝒪[K]) (e : ℕ) (l : ℤ) : ℂ :=
  ∫ x in KPTameGauss.integerUnitShell K, shellIntegrand χκ ψ π e l x ∂μ

def shellValue (χκ : MulChar 𝓀[K] ℂ) (ψbar : AddChar 𝓀[K] ℂ)
    (e : ℕ) (l : ℤ) : ℂ :=
  if l ≤ (e : ℤ) then
    if (3 : ℤ) ∣ l then 1 - qPower (K := K) (-1) else 0
  else if l = (e : ℤ) + 1 then
    if (3 : ℤ) ∣ l then -qPower (K := K) (-1)
    else qPower (K := K) (-(1 / 2 : ℝ)) * g χκ ψbar (-2 * l)
  else 0

private theorem character_zpow_apply_nonzero (χ : MulChar 𝓀[K] ℂ)
    (j : ℤ) (a : 𝓀[K]) (hj : j ≠ 0) :
    (χ ^ j) a = χ a ^ j := by
  by_cases ha : a = 0
  · rw [ha, MulChar.map_zero, MulChar.map_zero, zero_zpow j hj]
  · let u := Units.mk0 a ha
    calc
      (χ ^ j) a = χ (u ^ j : 𝓀[K]ˣ) := MulChar.zpow_apply_coe χ j u
      _ = χ a ^ j := by
        have H := congrArg (fun z : ℂˣ => (z : ℂ)) (map_zpow χ.toUnitHom u j)
        simpa only [MulChar.coe_toUnitHom, Units.val_zpow_eq_zpow_val,
          Units.val_mk0, u] using H

private theorem A_eq_weightedShellIntegral [MeasurableSpace K]
    (μ : Measure K) (χ : MulChar 𝓀[K] ℂ) (ψ : AddChar K ℂ)
    (π : 𝒪[K]) (e : ℕ) (l : ℤ) (hl : 1 ≤ l) :
    A μ χ ψ π e l =
      KPExteriorWeightedShellIntegrals.weightedShellIntegral μ
        (fun a => (χ ^ (-2 * l) : MulChar 𝓀[K] ℂ) a) ψ π ((e : ℤ) - l) := by
  unfold A KPExteriorWeightedShellIntegrals.weightedShellIntegral
  congr 1
  funext x
  unfold shellIntegrand KPExteriorWeightedShellIntegrals.weightedIntegrand
  split_ifs with hx
  · dsimp only
    rw [character_zpow_apply_nonzero χ (-2 * l) _ (by omega)]
  · rfl

private theorem qPower_neg_one : qPower (K := K) (-1) =
    (Fintype.card 𝓀[K] : ℂ)⁻¹ := by
  simp [qPower, Real.rpow_neg_one]

private theorem qPower_neg_half_sq :
    qPower (K := K) (-(1 / 2 : ℝ)) * qPower (K := K) (-(1 / 2 : ℝ)) =
      (Fintype.card 𝓀[K] : ℂ)⁻¹ := by
  have hpos : (0 : ℝ) < Fintype.card 𝓀[K] := by
    exact_mod_cast Fintype.card_pos
  simp only [qPower, Real.rpow_eq_pow]
  rw [← Complex.ofReal_mul, ← Real.rpow_add hpos]
  norm_num
  rw [Real.rpow_neg_one, Complex.ofReal_inv]
  simp

theorem unit_shell_integral [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] (hμ : μ (𝒪[K] : Set K) = 1)
    (π : 𝒪[K]) (hπ : Irreducible π)
    (ψ : AddChar K ℂ) (hψcont : Continuous ψ)
    (hψunitary : ∀ x : K, ‖ψ x‖ = 1) (hcond : ConductorZero ψ π)
    (χκ : MulChar 𝓀[K] ℂ) (hχκ : orderOf χκ = 6)
    (ψbar : AddChar 𝓀[K] ℂ)
    (hbar : ∀ u : 𝒪[K], ψbar (IsLocalRing.residue 𝒪[K] u) =
      ψ ((π : K)⁻¹ * (u : K))) (e : ℕ) (l : ℤ) (hl : 1 ≤ l) :
    A μ χκ ψ π e l = shellValue χκ ψbar e l := by
  have hψbar : ψbar ≠ 1 := by
    intro H
    obtain ⟨u, hu⟩ := hcond.2
    apply hu
    rw [← hbar u, H]
    rfl
  obtain ⟨hsum, hgauss⟩ :=
    KPExteriorWeightedShellIntegrals.even_sextic_residue_sums χκ hχκ ψbar hψbar l
  rw [A_eq_weightedShellIntegral μ χκ ψ π e l hl]
  have hQ : (Fintype.card 𝓀[K] : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  by_cases hin : l ≤ (e : ℤ)
  · rw [KPExteriorWeightedShellIntegrals.weightedShellIntegral_nonnegative
      μ hμ π hπ ψ hcond.1 (fun a => (χκ ^ (-2 * l) : MulChar 𝓀[K] ℂ) a)
      ((χκ ^ (-2 * l)).map_zero) ((e : ℤ) - l) (by omega), hsum]
    by_cases hd : (3 : ℤ) ∣ l
    · simp only [shellValue, hin, hd, if_true, qPower_neg_one]
      field_simp
    · simp [shellValue, hin, hd]
  · by_cases hterminal : l = (e : ℤ) + 1
    · have hn : (e : ℤ) - l = -1 := by omega
      rw [hn, KPExteriorWeightedShellIntegrals.weightedShellIntegral_terminal
        μ hμ π hπ ψ hcond.1 ψbar hbar
        (fun a => (χκ ^ (-2 * l) : MulChar 𝓀[K] ℂ) a)
        ((χκ ^ (-2 * l)).map_zero), hgauss]
      by_cases hd : (3 : ℤ) ∣ l
      · rw [shellValue, if_neg hin, if_pos hterminal, if_pos hd, if_pos hd,
          qPower_neg_one]
        simp [div_eq_mul_inv]
      · rw [shellValue, if_neg hin, if_pos hterminal, if_neg hd, if_neg hd, g,
          ← mul_assoc, qPower_neg_half_sq]
        simp [div_eq_mul_inv, mul_comm]
    · rw [KPExteriorWeightedShellIntegrals.weightedShellIntegral_deep
        μ hμ π hπ ψ hψcont hψunitary hcond.1 hcond.2
        (fun a => (χκ ^ (-2 * l) : MulChar 𝓀[K] ℂ) a) ((e : ℤ) - l) (by omega)]
      simp [shellValue, hin, hterminal]

end Local

section Arithmetic

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : HeightOneSpectrum (𝓞 F))

def arithmeticUnitCharacter
    (hgood : valuation (KPLocalExceptionalConstruction.LocalField F v)
      (6 : KPLocalExceptionalConstruction.LocalField F v) = 1)
    (u : (valuation (KPLocalExceptionalConstruction.LocalField F v)).integerˣ) : ℂ :=
  (KPLocalCover.coefficientEmbedding F ζ hζ
    (KPHilbert.residueSixCharacter F v ζ hζ hgood u) : ℂ)

theorem exists_unique_arithmetic_residue_character
    (hgood : valuation (KPLocalExceptionalConstruction.LocalField F v)
      (6 : KPLocalExceptionalConstruction.LocalField F v) = 1) :
    ∃! χκ : MulChar (IsLocalRing.ResidueField (valuation (KPLocalExceptionalConstruction.LocalField F v)).integer) ℂ,
      orderOf χκ = 6 ∧
        ∀ u : (valuation (KPLocalExceptionalConstruction.LocalField F v)).integerˣ,
          unitCharacter χκ u = arithmeticUnitCharacter F ζ hζ v hgood u := by
  classical
  let K := KPLocalExceptionalConstruction.LocalField F v
  let k := IsLocalRing.ResidueField (valuation K).integer
  letI : Fintype k := Fintype.ofFinite k
  have hd : 6 ∣ Fintype.card k - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact LocalClassFieldTheory.Kummer.dvd_residueCard_sub_one_of_primitiveRoots K 6
      hgood (KPHilbert.localRootsSix F v ζ hζ)
  let t : rootsOfUnity 6 k →* ℂˣ :=
    (KPLocalCover.coefficientEmbedding F ζ hζ).comp
      ((KPHilbert.finiteRootsSix F ζ hζ v).symm.toMonoidHom.comp
        ((KummerTheory.nthRootsSubgroupEquivRootsOfUnity K 6).toMonoidHom.comp
          (LocalClassFieldTheory.Kummer.localNthRootsReductionEquiv K 6 hgood
            (KPHilbert.localRootsSix F v ζ hζ)).symm.toMonoidHom))
  have ht : Function.Injective t := by
    exact (KPLocalCover.coefficientEmbedding_injective F ζ hζ).comp
      ((KPHilbert.finiteRootsSix F ζ hζ v).symm.injective.comp
        ((KummerTheory.nthRootsSubgroupEquivRootsOfUnity K 6).injective.comp
          (LocalClassFieldTheory.Kummer.localNthRootsReductionEquiv K 6 hgood
            (KPHilbert.localRootsSix F v ζ hζ)).symm.injective))
  let f := AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol k 6 hd
  let χ := MulChar.ofUnitHom (t.comp f)
  have hχ6 : χ ^ 6 = 1 := by
    apply MulChar.ext
    intro u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    rw [show χ u = (t (f u) : ℂ) from MulChar.ofUnitHom_coe _ _]
    have H : (f u) ^ 6 = 1 := by
      apply Subtype.ext
      exact (f u).property
    exact congrArg (fun z : ℂˣ => (z : ℂ)) ((map_pow t (f u) 6).symm.trans
      ((congrArg t H).trans (map_one t)))
  have hχorder : orderOf χ = 6 := by
    obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := kˣ)
    have huorder : orderOf u = Fintype.card k - 1 := by
      rw [hu, Nat.card_units, Nat.card_eq_fintype_card]
    have hfu : orderOf (f u) = 6 := by
      have hp : orderOf (u ^ ((Fintype.card k - 1) / 6)) = 6 := by
        rw [← huorder]
        apply orderOf_pow_orderOf_div
        · rw [huorder]; exact Nat.ne_of_gt (by have := Fintype.one_lt_card (α := k); omega)
        · rwa [huorder]
      have H := orderOf_injective (rootsOfUnity 6 k).subtype Subtype.val_injective (f u)
      calc
        orderOf (f u) = orderOf ((f u).val) := H.symm
        _ = 6 := hp
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hχ6)
    have H : (t (f u)) ^ orderOf χ = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one,
        ← show χ u = (t (f u) : ℂ) from MulChar.ofUnitHom_coe _ _,
        ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]
    exact (hfu ▸ (orderOf_injective t ht (f u)) ▸ orderOf_dvd_of_pow_eq_one H)
  have hχactual (u : (valuation K).integerˣ) :
      unitCharacter χ u = arithmeticUnitCharacter F ζ hζ v hgood u := by
    change χ ((Units.map (IsLocalRing.residue (valuation K).integer).toMonoidHom u : kˣ) : k) = _
    rw [MulChar.ofUnitHom_coe]
    rfl
  refine ⟨χ, ⟨hχorder, hχactual⟩, ?_⟩
  intro χ' hχ'
  apply MulChar.ext
  intro x
  obtain ⟨u, hu⟩ := IsLocalRing.residue_surjective (R := (valuation K).integer) (x : k)
  have huunit : IsUnit u := (IsLocalRing.residue_ne_zero_iff_isUnit u).1
    (by rw [hu]; exact Units.ne_zero x)
  obtain ⟨u', rfl⟩ := huunit
  have H := (hχ'.2 u').trans (hχactual u').symm
  change χ' (IsLocalRing.residue (valuation K).integer u'.val) =
    χ (IsLocalRing.residue (valuation K).integer u'.val) at H
  rw [hu] at H
  exact H

theorem arithmetic_unit_shell_integrals
    [Fintype (IsLocalRing.ResidueField
      (valuation (KPLocalExceptionalConstruction.LocalField F v)).integer)]
    (hgood : valuation (KPLocalExceptionalConstruction.LocalField F v)
      (6 : KPLocalExceptionalConstruction.LocalField F v) = 1)
    (μ : Measure (KPLocalExceptionalConstruction.LocalField F v))
    [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (KPLocalExceptionalConstruction.LocalField F v)).integer :
      Set (KPLocalExceptionalConstruction.LocalField F v)) = 1)
    (π : (valuation (KPLocalExceptionalConstruction.LocalField F v)).integer)
    (hπ : Irreducible π)
    (ψ : AddChar (KPLocalExceptionalConstruction.LocalField F v) ℂ)
    (hψcont : Continuous ψ)
    (hψunitary : ∀ x, ‖ψ x‖ = 1) (hcond : ConductorZero ψ π)
    (χκ : MulChar (IsLocalRing.ResidueField
      (valuation (KPLocalExceptionalConstruction.LocalField F v)).integer) ℂ)
    (hactual : ∀ u, unitCharacter χκ u =
      arithmeticUnitCharacter F ζ hζ v hgood u) :
    orderOf χκ = 6 ∧
      ∃ ψbar : AddChar (IsLocalRing.ResidueField
        (valuation (KPLocalExceptionalConstruction.LocalField F v)).integer) ℂ,
        ψbar ≠ 1 ∧ ψbar.IsPrimitive ∧
        (∀ u, ψbar (IsLocalRing.residue _ u) =
          ψ ((π : KPLocalExceptionalConstruction.LocalField F v)⁻¹ *
            (u : KPLocalExceptionalConstruction.LocalField F v))) ∧
        (∀ j : ℤ, g χκ ψbar (j + 6) = g χκ ψbar j) ∧
        g χκ ψbar 2 * g χκ ψbar 4 = 1 ∧
        ∀ (e : ℕ) (l : ℤ), 1 ≤ l →
          A μ χκ ψ π e l = shellValue χκ ψbar e l := by
  obtain ⟨χ₀, hχ₀, huniq⟩ := exists_unique_arithmetic_residue_character F ζ hζ v hgood
  have hχeq : χκ = χ₀ := by
    apply MulChar.ext
    intro x
    obtain ⟨u, hu⟩ := IsLocalRing.residue_surjective (R :=
      (valuation (KPLocalExceptionalConstruction.LocalField F v)).integer) (x : _)
    have huunit : IsUnit u := (IsLocalRing.residue_ne_zero_iff_isUnit u).1
      (by rw [hu]; exact Units.ne_zero x)
    obtain ⟨u', rfl⟩ := huunit
    have H := (hactual u').trans (hχ₀.2 u').symm
    simpa only [unitCharacter, hu] using H
  have hχ : orderOf χκ = 6 := hχeq ▸ hχ₀.1
  obtain ⟨ψbar, hbar, _⟩ := exists_unique_residue_addChar π hπ ψ hψcont hψunitary hcond
  refine ⟨hχ, ψbar, hbar.1, hbar.2.1, hbar.2.2, ?_, ?_, ?_⟩
  · exact g_periodic χκ hχ ψbar
  · exact g_two_mul_four χκ hχ ψbar hbar.1
  · exact fun e l hl => unit_shell_integral μ hμ π hπ ψ hψcont hψunitary hcond
      χκ hχ ψbar hbar.2.2 e l hl

end Arithmetic

end
end DedekindZetaZeroFree.KPExteriorUnitShellIntegrals

end
