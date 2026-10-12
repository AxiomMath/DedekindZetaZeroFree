module

public import DedekindZetaZeroFree.Metaplectic.Torus.LocalCubicHeisenbergPairing
public import DedekindZetaZeroFree.CharacterSums.Gauss.NormalizedSexticPowerIdentities

@[expose] public section

namespace DedekindZetaZeroFree.KPTameGauss

variable {k : Type*} [Field k] [Fintype k]

noncomputable def cubicGaussSum (κ : MulChar k ℂ) (ψ : AddChar k ℂ)
    (j : ZMod 3) : ℂ :=
  FiniteGauss.gaussPower κ ψ j.val

theorem cubicGaussSum_zero (κ : MulChar k ℂ) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) :
    cubicGaussSum κ ψ 0 = -1 := by
  simpa [cubicGaussSum, FiniteGauss.gaussPower] using gaussSum_one_left hψ

section LocalShell

open ValuativeRel MeasureTheory
open scoped Valued ENNReal

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

noncomputable def residueShellIntegrand (κ : MulChar 𝓀[K] ℂ)
    (ψ : AddChar K ℂ) (π : 𝒪[K]) (j : ZMod 3) (x : K) : ℂ := by
  classical
  exact if hx : x ∈ (𝒪[K] : Subring K) then
    κ (IsLocalRing.residue 𝒪[K] ⟨x, hx⟩) ^ j.val * ψ (x / (π : K))
  else 0

def integerUnitShell (K : Type*) [Field K] [ValuativeRel K] : Set K :=
  {x | ∃ u : 𝒪[K], (u : K) = x ∧ IsUnit u}

theorem exists_residue_addChar (π : 𝒪[K]) (hπ : Irreducible π)
    (ψ : AddChar K ℂ) (hψcont : Continuous ψ)
    (hO : ∀ u : 𝒪[K], ψ (u : K) = 1)
    (hexact : ∃ u : 𝒪[K], ψ ((u : K) / (π : K)) ≠ 1) :
    ∃! ψbar : AddChar 𝓀[K] ℂ,
      ψbar ≠ 1 ∧ ∀ u : 𝒪[K],
        ψbar (IsLocalRing.residue 𝒪[K] u) = ψ ((u : K) / (π : K)) := by
  classical
  have hπ0 : (π : K) ≠ 0 := by
    exact_mod_cast hπ.ne_zero
  let r := IsLocalRing.residue 𝒪[K]
  have hfiber (u v : 𝒪[K]) (h : r u = r v) :
      ψ ((u : K) / (π : K)) = ψ ((v : K) / (π : K)) := by
    have hm : u - v ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      simpa only [map_sub, sub_eq_zero] using h
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    obtain ⟨w, hw⟩ := hm
    have he : (u : K) / (π : K) = (v : K) / (π : K) + (w : K) := by
      have H : (u : K) - (v : K) = (π : K) * (w : K) := by
        exact_mod_cast hw
      field_simp
      linear_combination H
    rw [he, ψ.map_add_eq_mul, hO, mul_one]
  let s : 𝓀[K] → 𝒪[K] := fun x => (IsLocalRing.residue_surjective x).choose
  have hs (x : 𝓀[K]) : r (s x) = x := (IsLocalRing.residue_surjective x).choose_spec
  let χ : AddChar 𝓀[K] ℂ :=
    { toFun := fun x => ψ ((s x : K) / (π : K))
      map_zero_eq_one' := by
        rw [hfiber (s 0) 0 (by simpa using hs 0)]
        simp
      map_add_eq_mul' := by
        intro x y
        rw [hfiber (s (x + y)) (s x + s y) (by simp [hs]), Subring.coe_add,
          add_div, ψ.map_add_eq_mul] }
  have hχ (u : 𝒪[K]) : χ (r u) = ψ ((u : K) / (π : K)) :=
    hfiber _ _ (hs _)
  refine ⟨χ, ⟨?_, hχ⟩, ?_⟩
  · obtain ⟨u, hu⟩ := hexact
    intro h
    have H := hχ u
    rw [h, AddChar.one_apply] at H
    exact hu H.symm
  · intro χ' hχ'
    apply AddChar.ext
    intro x
    obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective x
    exact (hχ'.2 u).trans (hχ u).symm

theorem additive_haar_shell_integral [Fintype 𝓀[K]]
    [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure]
    (hμ : μ (𝒪[K] : Set K) = 1)
    (π : 𝒪[K]) (hπ : Irreducible π)
    (κ : MulChar 𝓀[K] ℂ) (ψ : AddChar K ℂ) (hψcont : Continuous ψ)
    (ψbar : AddChar 𝓀[K] ℂ)
    (hbar : ∀ u : 𝒪[K],
      ψbar (IsLocalRing.residue 𝒪[K] u) = ψ ((u : K) / (π : K)))
    (j : ZMod 3) :
    (∫ x in integerUnitShell K, residueShellIntegrand κ ψ π j x ∂μ) =
      cubicGaussSum κ ψbar j / (Fintype.card 𝓀[K] : ℂ) := by
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
  let f : k → ℂ := fun x => (κ ^ j.val) x * ψbar x
  have hi : (∫ u : R, f (r u) ∂ν) = cubicGaussSum κ ψbar j / (Fintype.card k : ℂ) := by
    rw [← integral_map hr.aemeasurable ((measurable_of_countable f).aestronglyMeasurable),
      integral_fintype Integrable.of_finite]
    change (∑ x : k, ρ.real {x} • f x) = _
    simp only [hreal, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
    simp only [one_div, ← Finset.mul_sum, ← div_eq_inv_mul]
    rw [← Finset.sum_div]
    rfl
  have hzero : f 0 = 0 := by simp [f, MulChar.map_zero]
  have hs : integerUnitShell K = R.subtype '' {u : R | IsUnit u} := by
    ext x
    simp [integerUnitShell, R, and_comm]
  have hS : MeasurableSet (integerUnitShell K) := by
    rw [hs]
    apply (MeasurableEmbedding.subtype_coe hR).measurableSet_image.mpr
    have he : {u : R | IsUnit u} = (r ⁻¹' {0})ᶜ := by
      ext u
      simpa only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff] using
          (IsLocalRing.residue_ne_zero_iff_isUnit u).symm
    rw [he]
    exact (hr (measurableSet_singleton _)).compl
  have he : (integerUnitShell K).indicator (residueShellIntegrand κ ψ π j) =
      (R : Set K).indicator (fun x => if hx : x ∈ (R : Set K) then f (r ⟨x,hx⟩) else 0) := by
    funext x
    by_cases hx : x ∈ (R : Set K)
    · let u : R := ⟨x,hx⟩
      by_cases hu : IsUnit u
      · have hxs : x ∈ integerUnitShell K := ⟨u,rfl,hu⟩
        simp only [Set.indicator_of_mem hxs, Set.indicator_of_mem hx, dif_pos hx]
        simp only [residueShellIntegrand, show x ∈ ((valuation K).integer : Subring K) from hx,
          dif_pos, f]
        change κ (r u) ^ j.val * ψ ((u : K) / (π : K)) = (κ ^ j.val) (r u) * ψbar (r u)
        have hp := MulChar.pow_apply_coe κ j.val (hu.map r).unit
        simpa only [IsUnit.unit_spec] using congrArg₂ (fun a b : ℂ => a * b) hp.symm (hbar u).symm
      · have hxs : x ∉ integerUnitShell K := by
          rintro ⟨v,hv,hvu⟩
          have : v = u := Subtype.ext hv
          exact hu (this ▸ hvu)
        have hz : r u = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hu
        simp only [Set.indicator_of_notMem hxs, Set.indicator_of_mem hx, dif_pos hx]
        change 0 = f (r u)
        rw [hz,hzero]
    · have hxs : x ∉ integerUnitShell K := by
        rintro ⟨v,rfl,-⟩
        exact hx v.property
      simp [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hx]
  rw [← integral_indicator hS, he, integral_indicator hR, ← integral_subtype_comap hR]
  convert hi using 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [dif_pos x.property]
  rfl

end LocalShell

end DedekindZetaZeroFree.KPTameGauss
