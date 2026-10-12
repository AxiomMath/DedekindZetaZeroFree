module

public import DedekindZetaZeroFree.Adeles.RestrictedProduct.LocalTopology
public import ClassFieldTheory.All

@[expose] public section

namespace DedekindZetaZeroFree.ThetaFiniteCutoff.PhaseSublevels

open NumberField IsDedekindDomain
open scoped ValuativeRel
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField

theorem small_sixth_power_congruence
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (V : Set (v.adicCompletion F)ˣ) (hV : IsOpen V)
    (h1 : (1 : (v.adicCompletion F)ˣ) ∈ V) :
    ∃ (H : AddSubgroup (v.adicCompletion F))
      (U : Subgroup (v.adicCompletion F)ˣ),
      IsCompact (H : Set (v.adicCompletion F)) ∧
      IsOpen (H : Set (v.adicCompletion F)) ∧
      IsCompact (U : Set (v.adicCompletion F)ˣ) ∧
      IsOpen (U : Set (v.adicCompletion F)ˣ) ∧
      (U : Set (v.adicCompletion F)ˣ) ⊆ V ∧
      U ≤ (powMonoidHom 6).range ∧
      (∀ y ∈ U, (y : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
        ((y⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
          v.adicCompletionIntegers F) ∧
      ∀ y : (v.adicCompletion F)ˣ,
        y ∈ U ↔ (y : v.adicCompletion F) - 1 ∈ H := by
  classical
  let K := v.adicCompletion F
  letI : ValuativeRel K := ClassFieldTheory.finitePlaceCompletionValuativeRel F v
  letI : IsNonarchimedeanLocalField K := ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  letI : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hO : (ValuativeRel.valuation K).integer = (v.adicCompletionIntegers F).toSubring := by
    ext x
    change ValuativeRel.valuation K x ≤ 1 ↔ (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) x ≤ 1
    rw [← Valuation.vle_one_iff, ← Valuation.vle_one_iff]
  obtain ⟨E, hE⟩ := LocalClassFieldTheory.exists_finiteGalois_normSubgroup_le_powMonoidHom_range K ⟨6, by norm_num⟩ (by norm_num)
  let L := E.toIntermediateField
  letI : FiniteDimensional K L := E.finiteDimensional
  letI : IsGalois K L := E.isGalois
  have hnorm := LocalClassFieldTheory.localNormSubgroup_isOpen K L
  let W : Set Kˣ := V ∩ (localNormSubgroup K L : Set Kˣ)
  have hW : IsOpen W := hV.inter hnorm
  have hW1 : (1 : Kˣ) ∈ W := ⟨h1, (localNormSubgroup K L).one_mem⟩
  obtain ⟨B, hB, hWB⟩ := Units.isEmbedding_val₀.isOpen_iff.mp hW
  have hB1 : (1 : K) ∈ B := by
    have : (1 : Kˣ) ∈ Units.val ⁻¹' B := hWB.symm ▸ hW1
    exact this
  let s : Set 𝒪[K] := {a | (a : K) + 1 ∈ B}
  have hs : s ∈ nhds (0 : 𝒪[K]) := by
    apply (hB.preimage (continuous_subtype_val.add continuous_const)).mem_nhds
    simpa [s] using hB1
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_subset_nhds_zero K s hs
  let n := N + 1
  let I : Ideal 𝒪[K] := 𝓂[K] ^ n
  let H : AddSubgroup K := I.toAddSubgroup.map (ValuativeRel.valuation K).integer.subtype.toAddMonoidHom
  let U : Subgroup Kˣ := (principalUnits K n).map (integerUnitsToFieldUnits K)
  have hmem (y : Kˣ) : y ∈ U ↔ (y : K) - 1 ∈ H := by
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(u : 𝒪[K]) - 1, (mem_principalUnits_iff K u n).mp hu, ?_⟩
      change ((u : 𝒪[K]) : K) - 1 = ((u : 𝒪[K]) : K) - 1
      rfl
    · rintro ⟨a, ha, hea⟩
      have hau : IsUnit (1 + a) := isUnit_one_add_of_mem_maximalIdeal_pow K (Nat.succ_pos N) a ha
      obtain ⟨u, hu⟩ := hau
      refine ⟨u, ?_, ?_⟩
      · apply (mem_principalUnits_iff K u n).mpr
        rw [hu]
        simpa using ha
      · apply Units.ext
        change ((u : 𝒪[K]) : K) = (y : K)
        rw [hu]
        change (1 : K) + (a : K) = (y : K)
        change (a : K) = (y : K) - 1 at hea
        rw [hea]
        ring
  have hIc : IsCompact (I : Set 𝒪[K]) := (isClosed_maximalIdeal_pow K n).isCompact
  have hIo : IsOpen (I : Set 𝒪[K]) := I.toAddSubgroup.isOpen_of_mem_nhds (maximalIdeal_pow_mem_nhds_zero K n)
  have hHc : IsCompact (H : Set K) := by
    exact hIc.image continuous_subtype_val
  have hHo : IsOpen (H : Set K) := by
    exact (Valuation.isOpen_integer (v := ValuativeRel.valuation K)).isOpenMap_subtype_val _ hIo
  have hUc : IsCompact (U : Set Kˣ) := by
    have hpc : IsCompact (principalUnits K n : Set (𝒪[K]ˣ)) := by
      apply IsClosed.isCompact
      exact (isClosed_maximalIdeal_pow K n).preimage (Units.continuous_val.sub continuous_const)
    exact hpc.image (Units.continuous_map continuous_subtype_val)
  have hUo : IsOpen (U : Set Kˣ) := by
    have heq : (U : Set Kˣ) = (fun y : Kˣ => (y : K) - 1) ⁻¹' (H : Set K) := Set.ext hmem
    rw [heq]
    exact hHo.preimage (Units.continuous_val.sub continuous_const)
  have hUW : (U : Set Kˣ) ⊆ W := by
    rintro y ⟨u, hu, rfl⟩
    have huI := (mem_principalUnits_iff K u n).mp hu
    have hs' := hN (Ideal.pow_le_pow_right (Nat.le_succ N) huI)
    have hB' : (((u : 𝒪[K]) : K)) ∈ B := by simpa [s] using hs'
    rw [← hWB]
    exact hB'
  refine ⟨H, U, hHc, hHo, hUc, hUo, fun y hy => (hUW hy).1, fun y hy => hE (hUW hy).2, ?_, hmem⟩
  rintro y ⟨u, hu, rfl⟩
  constructor
  · change (((u : 𝒪[K]) : K)) ∈ (v.adicCompletionIntegers F).toSubring
    rw [← hO]
    exact (u : 𝒪[K]).property
  · change ((((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) : K)) ∈ (v.adicCompletionIntegers F).toSubring
    rw [← hO]
    exact (u⁻¹ : 𝒪[K]ˣ).val.property

end DedekindZetaZeroFree.ThetaFiniteCutoff.PhaseSublevels
