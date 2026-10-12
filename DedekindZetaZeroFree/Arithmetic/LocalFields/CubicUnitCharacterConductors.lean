module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.FilteredCubicCharacterCounts
public import DedekindZetaZeroFree.Arithmetic.LocalFields.TruncatedCubicUnitIndices
public import DedekindZetaZeroFree.Arithmetic.LocalFields.CubicConductorWeightedSums

@[expose] public section

namespace DedekindZetaZeroFree
namespace CubicUnitCharacters

open scoped ValuativeRel

noncomputable def unitFiltration (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) : Subgroup (𝒪[K])ˣ :=
  if n = 0 then ⊤ else
    (Units.map (Ideal.Quotient.mk (𝓂[K] ^ n)).toMonoidHom).ker

abbrev Character (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] :=
  CubicCharacters.Character (𝒪[K])ˣ

noncomputable def residueCard (K : Type*) [Field K] [ValuativeRel K] : ℕ := Nat.card 𝓀[K]

noncomputable def conductor (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (χ : Character K) : ℕ :=
  CubicCharacters.conductor (unitFiltration K) χ

end CubicUnitCharacters

section LocalCountProof
open scoped ValuativeRel Topology
open CubicUnitCharacters
variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
local instance : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
local instance : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
private lemma filtration_eq (j : ℕ) : unitFiltration K j = KPCubicUnitIndices.principalUnits K j := by
  unfold unitFiltration
  split_ifs with h
  · subst j
    unfold KPCubicUnitIndices.principalUnits
    symm
    apply top_unique
    intro u hu
    change Units.map _ u = 1
    rw [Units.ext_iff]
    change Ideal.Quotient.mk _ (u : 𝒪[K]) = 1
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    simp
  · rfl
private lemma filtration_mem (j : ℕ) (u : (𝒪[K])ˣ) :
    u ∈ unitFiltration K j ↔ (u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ j := by
  rw [filtration_eq]
  change Units.map _ u = 1 ↔ _
  rw [Units.ext_iff]
  change Ideal.Quotient.mk _ (u : 𝒪[K]) = 1 ↔ _
  rw [← map_one (Ideal.Quotient.mk (𝓂[K] ^ j)), Ideal.Quotient.eq]
private lemma filtration_anti : Antitone (unitFiltration K) := by
  intro i j hij u hu
  rw [filtration_mem] at hu ⊢
  exact Ideal.pow_le_pow_right hij hu
private lemma filtration_open (j : ℕ) : IsOpen (unitFiltration K j : Set (𝒪[K])ˣ) := by
  have he : (unitFiltration K j : Set (𝒪[K])ˣ) =
      (fun u : (𝒪[K])ˣ => (u : 𝒪[K]) - 1) ⁻¹' ((𝓂[K] ^ j : Ideal (𝒪[K])) : Set (𝒪[K])) := by
    ext u
    exact filtration_mem K j u
  rw [he]
  exact (IsLocalRing.isOpen_maximalIdeal_pow (𝒪[K]) j).preimage (by fun_prop)
private lemma filtration_basis : ∀ W ∈ 𝓝 (1 : (𝒪[K])ˣ),
    ∃ j, (unitFiltration K j : Set (𝒪[K])ˣ) ⊆ W := by
  intro W hW
  have hi : (⋂ j, (unitFiltration K j : Set (𝒪[K])ˣ)) ⊆ {1} := by
    intro u hu
    have hm : (u : 𝒪[K]) - 1 ∈ ⨅ j : ℕ, 𝓂[K] ^ j := by
      simp only [Submodule.mem_iInf]
      intro j
      exact (filtration_mem K j u).mp (Set.mem_iInter.mp hu j)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'] at hm
    apply Units.ext
    simpa only [Ideal.mem_bot, sub_eq_zero, Units.val_one] using hm
  exact exists_subset_nhds_of_compactSpace (filtration_anti K).directed_ge
    (fun j => (unitFiltration K j).isClosed_of_isOpen (filtration_open K j)) (by
      apply mem_nhdsSet_iff_forall.mpr
      intro x hx
      have : x = 1 := Set.mem_singleton_iff.mp (hi hx)
      simpa [this] using hW)
private lemma filtration_finite (j : ℕ) : (unitFiltration K j).FiniteIndex := by
  letI := (unitFiltration K j).quotient_finite_of_isOpen (filtration_open K j)
  exact Subgroup.finiteIndex_of_finite_quotient
private lemma root_lift (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    ∃ z : KPCubicUnitIndices.Integers K, IsPrimitiveRoot z 3 := by
  have hv : (ValuativeRel.valuation K) ζ = 1 := by
    have hp := congrArg (ValuativeRel.valuation K) hζ.pow_eq_one
    rw [map_pow, map_one] at hp
    exact (pow_eq_one_iff_of_nonneg zero_le (by decide : 3 ≠ 0)).mp hp
  let z : KPCubicUnitIndices.Integers K := ⟨ζ, hv.le⟩
  exact ⟨z, hζ.of_map_of_injective (f := (KPCubicUnitIndices.Integers K).subtype)
    Subtype.val_injective⟩
private lemma local_counts (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    ∃ r : ℕ, 2 ≤ residueCard K ∧
      Finite (Character K) ∧
      (∀ χ : Character K, ∃ j, unitFiltration K j ≤ χ.toMonoidHom.ker) ∧
      (∀ χ : Character K, unitFiltration K (conductor K χ) ≤ χ.toMonoidHom.ker) ∧
      (∀ χ : Character K, conductor K χ ≤ 3 * r + 1) ∧
      (∀ j, 1 ≤ j → Nat.card {χ : Character K // conductor K χ = j} =
        CubicCharacters.levelIndex (unitFiltration K) j -
          CubicCharacters.levelIndex (unitFiltration K) (j - 1)) ∧
      (∀ χ : Character K, conductor K χ = 0 ↔ χ = 1) ∧
      Nat.card {χ : Character K // conductor K χ = 0} = 1 ∧
      CubicCharacters.levelIndex (unitFiltration K) 0 = 1 ∧
      (∀ j, 1 ≤ j → j ≤ 3*r → CubicCharacters.levelIndex (unitFiltration K) j =
        residueCard K ^ (j - (j + 2) / 3)) ∧
      (∀ j, 3*r < j → CubicCharacters.levelIndex (unitFiltration K) j =
        3 * residueCard K ^ (2*r)) := by
  obtain ⟨z, hz⟩ := root_lift K ζ hζ
  have he (j : ℕ) : CubicCharacters.levelIndex (unitFiltration K) j =
      KPCubicUnitIndices.truncatedIndex K j := by
    simp only [CubicCharacters.levelIndex, KPCubicUnitIndices.truncatedIndex,
      CubicCharacters.cubes, KPCubicUnitIndices.cubeUnits, filtration_eq]
  have hi := kp_cubic_unit_truncated_indices K z hz
  dsimp only at hi
  have hq : KPCubicUnitIndices.residueCard K = residueCard K := rfl
  have hf := kp_filtered_cubic_character_count (unitFiltration K)
    (by simp [unitFiltration]) (filtration_anti K) (filtration_open K)
    (filtration_finite K) (filtration_basis K)
    (fun j => by
      letI := filtration_finite K j
      exact Subgroup.finiteIndex_of_le le_sup_right)
    (3 * KPCubicUnitIndices.rootDepth K z + 1)
    (by simpa only [he] using kp_cubic_unit_truncated_indices_stable K z hz)
  refine ⟨KPCubicUnitIndices.rootDepth K z, ?_, hf.1, hf.2.1, hf.2.2.1,
    hf.2.2.2.1, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.1,
    hf.2.2.2.2.2.2.2, ?_, ?_, ?_⟩
  · simpa only [hq] using hi.1
  · simpa only [he] using hi.2.1
  · simpa only [he, hq] using hi.2.2.1
  · simpa only [he, hq] using hi.2.2.2
private lemma sum_by_conductor {X : Type*} [Finite X] (c : X → ℕ) (N : ℕ)
    (hb : ∀ x, c x ≤ N) (t : ℝ) :
    (∑ᶠ x : X, t ^ c x) = ∑ j ∈ Finset.range (N + 1),
      (Nat.card {x : X // c x = j} : ℝ) * t ^ j := by
  classical
  letI := Fintype.ofFinite X
  rw [finsum_eq_sum_of_fintype,
    ← Finset.sum_fiberwise_of_maps_to (g := c) (t := Finset.range (N + 1))
      (fun x _ => Finset.mem_range.mpr (by have := hb x; omega))]
  apply Finset.sum_congr rfl
  intro j hj
  have he : ∑ x ∈ Finset.univ.filter (fun x : X => c x = j), t ^ c x =
      ∑ x ∈ Finset.univ.filter (fun x : X => c x = j), t ^ j := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [he, Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
private lemma sum_triples (g : ℕ → ℝ) (r : ℕ) :
    (∑ j ∈ Finset.range (3*r), g (j+1)) =
      ∑ i ∈ Finset.range r, (g (3*i+1) + g (3*i+2) + g (3*i+3)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 3 * (r+1) = 3*r+3 by omega, Finset.sum_range_add, ih,
      Finset.sum_range_succ]
    simp [Finset.sum_range_succ, Nat.add_assoc]
private lemma sum_from_indices {X : Type*} [Finite X] (c : X → ℕ) (q r : ℕ)
    (hq : 2 ≤ q) (A : ℕ → ℕ)
    (hb : ∀ x, c x ≤ 3*r+1)
    (hzero : Nat.card {x : X // c x = 0} = 1)
    (hd : ∀ j, 1 ≤ j → Nat.card {x : X // c x = j} = A j - A (j-1))
    (ha0 : A 0 = 1)
    (has : ∀ j, 1 ≤ j → j ≤ 3*r → A j = q ^ (j-(j+2)/3))
    (hat : ∀ j, 3*r < j → A j = 3*q^(2*r)) :
    (∑ᶠ x : X, ((q : ℝ)⁻¹) ^ c x) = 1 + 2 * (q : ℝ)⁻¹ := by
  classical
  have hs (j : ℕ) (hj : j ≤ 3*r) : A j = q ^ (j-(j+2)/3) := by
    by_cases hz : j = 0
    · subst j; simp [ha0]
    · exact has j (by omega) hj
  have h1 (i : ℕ) (hi : i < r) : Nat.card {x : X // c x = 3*i+1} = 0 := by
    rw [hd _ (by omega), hs _ (by omega), hs _ (by omega)]
    rw [show 3*i+1-(3*i+1+2)/3 = 2*i by omega,
      show (3*i+1-1)-((3*i+1-1)+2)/3 = 2*i by omega, Nat.sub_self]
  have h2 (i : ℕ) (hi : i < r) : Nat.card {x : X // c x = 3*i+2} =
      (q-1)*q^(2*i) := by
    rw [hd _ (by omega), hs _ (by omega), hs _ (by omega)]
    rw [show 3*i+2-(3*i+2+2)/3 = 2*i+1 by omega,
      show (3*i+2-1)-((3*i+2-1)+2)/3 = 2*i by omega,
      pow_succ]
    simpa only [Nat.sub_mul, Nat.one_mul, mul_comm]
  have h3 (i : ℕ) (hi : i < r) : Nat.card {x : X // c x = 3*i+3} =
      (q-1)*q^(2*i+1) := by
    rw [hd _ (by omega), hs _ (by omega), hs _ (by omega)]
    rw [show 3*i+3-(3*i+3+2)/3 = (2*i+1)+1 by omega,
      show (3*i+3-1)-((3*i+3-1)+2)/3 = 2*i+1 by omega,
      pow_succ]
    simpa only [Nat.sub_mul, Nat.one_mul, mul_comm]
  have ht : Nat.card {x : X // c x = 3*r+1} = 2*q^(2*r) := by
    rw [hd _ (by omega), hat _ (by omega), hs _ (by omega)]
    rw [show (3*r+1-1)-((3*r+1-1)+2)/3 = 2*r by omega]
    omega
  rw [sum_by_conductor c (3*r+1) hb, Finset.sum_range_succ,
    Finset.sum_range_succ', hzero, ht]
  simp only [Nat.cast_one, pow_zero, mul_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  rw [sum_triples (fun j => (Nat.card {x : X // c x = j} : ℝ) * (q : ℝ)⁻¹ ^ j) r]
  have hg : (∑ i ∈ Finset.range r,
      ((Nat.card {x : X // c x = 3*i+1} : ℝ) * (q : ℝ)⁻¹ ^ (3*i+1) +
       (Nat.card {x : X // c x = 3*i+2} : ℝ) * (q : ℝ)⁻¹ ^ (3*i+2) +
       (Nat.card {x : X // c x = 3*i+3} : ℝ) * (q : ℝ)⁻¹ ^ (3*i+3))) =
      ∑ i ∈ Finset.range r,
        (((q : ℝ)-1)*(q : ℝ)^(2*i)*(q : ℝ)⁻¹^(3*i+2) +
          ((q : ℝ)-1)*(q : ℝ)^(2*i+1)*(q : ℝ)⁻¹^(3*i+3)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [h1 i (Finset.mem_range.mp hi), h2 i (Finset.mem_range.mp hi),
      h3 i (Finset.mem_range.mp hi)]
    simp [Nat.cast_sub (show 1 ≤ q by omega), mul_assoc]
  rw [hg]
  have hw := kp_cubic_conductor_weighted_sum q r hq
  dsimp at hw
  rw [div_eq_mul_inv] at hw
  linarith
end LocalCountProof

open scoped ValuativeRel
open ValuativeRel

namespace CubicUnitCharacters

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem t2Space_of_isValuativeTopology [IsValuativeTopology K] [ValuativeRel.IsNontrivial K] :
    T2Space K := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => ?_
  refine ⟨{z : K | valuation K z < valuation K x}, ?_, by simp⟩
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨Units.mk0 (valuation K x) (by simpa using hx), ?_⟩
  intro z hz
  simpa using hz

theorem unitFiltration_mem_iff (j : ℕ) (u : (𝒪[K])ˣ) :
    u ∈ unitFiltration K j ↔ ((u : 𝒪[K]) - 1) ∈ 𝓂[K] ^ j := by
  by_cases hj : j = 0
  · rw [unitFiltration, if_pos hj, hj]
    simp
  · rw [unitFiltration, if_neg hj, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map,
      Units.val_one]
    change (Ideal.Quotient.mk (𝓂[K] ^ j)) (u : 𝒪[K]) = 1 ↔ ((u : 𝒪[K]) - 1) ∈ 𝓂[K] ^ j
    rw [← map_one (Ideal.Quotient.mk (𝓂[K] ^ j)), Ideal.Quotient.mk_eq_mk_iff_sub_mem]

theorem unitFiltration_antitone : Antitone (unitFiltration K) := by
  intro a b hab u hu
  rw [unitFiltration_mem_iff K] at hu ⊢
  exact Ideal.pow_le_pow_right hab hu

theorem isOpen_unitFiltration (j : ℕ) : IsOpen (unitFiltration K j : Set (𝒪[K])ˣ) := by
  haveI : T2Space K := t2Space_of_isValuativeTopology K
  haveI : T2Space 𝒪[K] := inferInstance
  have hopen : IsOpen (((𝓂[K] ^ j : Ideal 𝒪[K]) : Set 𝒪[K])) :=
    IsLocalRing.isOpen_maximalIdeal_pow 𝒪[K] j
  have hcont : Continuous fun x : 𝒪[K] => x - 1 := continuous_id.sub continuous_const
  have hset : (unitFiltration K j : Set (𝒪[K])ˣ) =
      Units.val ⁻¹' ((fun x : 𝒪[K] => x - 1) ⁻¹' ((𝓂[K] ^ j : Ideal 𝒪[K]) : Set 𝒪[K])) := by
    ext u
    rw [Set.mem_preimage, Set.mem_preimage]
    exact unitFiltration_mem_iff K j u
  rw [hset]
  exact (hopen.preimage hcont).preimage Units.continuous_val

end CubicUnitCharacters

theorem kp_local_unramified_character_count
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    Finite (CubicUnitCharacters.Character K) ∧
    (∀ χ : CubicUnitCharacters.Character K,
      ∃ n, CubicUnitCharacters.unitFiltration K n ≤ χ.toMonoidHom.ker) ∧
    (∀ χ : CubicUnitCharacters.Character K,
      CubicUnitCharacters.unitFiltration K (CubicUnitCharacters.conductor K χ) ≤
        χ.toMonoidHom.ker) ∧
    (∀ χ : CubicUnitCharacters.Character K,
      CubicUnitCharacters.conductor K χ = 0 ↔ χ = 1) ∧
    (∑ᶠ χ : CubicUnitCharacters.Character K,
      ((CubicUnitCharacters.residueCard K : ℝ)⁻¹) ^
        CubicUnitCharacters.conductor K χ) =
      1 + 2 * (CubicUnitCharacters.residueCard K : ℝ)⁻¹ := by
  classical
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  obtain ⟨r, hq, hfin, hex, hmin, hb, hd, hz, hzcard, ha0, has, hat⟩ :=
    local_counts K ζ hζ
  letI := hfin
  refine ⟨hfin, hex, hmin, hz, ?_⟩
  exact sum_from_indices (CubicUnitCharacters.conductor K)
    (CubicUnitCharacters.residueCard K) r hq
    (CubicCharacters.levelIndex (CubicUnitCharacters.unitFiltration K))
    hb hzcard hd ha0 has hat

end DedekindZetaZeroFree
