module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree
namespace CubicUnitBalls

variable {K : Type*} [Field K]

abbrev Ring (v : AddValuation K (WithTop ℤ)) := v.toValuation.valuationSubring

def principalUnits (v : AddValuation K (WithTop ℤ)) (j : ℕ) : Set (Ring v)ˣ :=
  if j = 0 then Set.univ else
    {u | (u : Ring v) - 1 ∈ (IsLocalRing.maximalIdeal (Ring v)) ^ j}

def cubicPreimage (v : AddValuation K (WithTop ℤ)) (j : ℕ) : Set (Ring v)ˣ :=
  {u | u ^ 3 ∈ principalUnits v j}

def cubeRoots (v : AddValuation K (WithTop ℤ)) (ζ : (Ring v)ˣ) : Set (Ring v)ˣ :=
  {1, ζ, ζ ^ 2}

def rootCoset (v : AddValuation K (WithTop ℤ)) (ξ : (Ring v)ˣ) (j : ℕ) : Set (Ring v)ˣ :=
  (fun u => ξ * u) '' principalUnits v j

noncomputable def rootDepth (v : AddValuation K (WithTop ℤ)) (ζ : (Ring v)ˣ) : ℕ :=
  (v (1 - ((ζ : Ring v) : K))).untopD 0 |>.toNat

theorem rootDepth_spec [CharZero K] (v : AddValuation K (WithTop ℤ))
    (hnormalized : ∃ π : K, v π = (1 : WithTop ℤ))
    (ζ : (Ring v)ˣ) (hζ : IsPrimitiveRoot ((ζ : Ring v) : K) 3) :
    v (1 - ((ζ : Ring v) : K)) = (rootDepth v ζ : WithTop ℤ) := by
  have hne : v (1 - ((ζ : Ring v) : K)) ≠ ⊤ := by
    exact fun h => (hζ.ne_one (by decide)) ((sub_eq_zero.mp (v.top_iff.mp h)).symm)
  have hnonneg : 0 ≤ v (1 - ((ζ : Ring v) : K)) := by
    exact ((1 - (ζ : Ring v)) : Ring v).property
  generalize he : v (1 - ((ζ : Ring v) : K)) = a at *
  cases a with
  | top => exact (hne rfl).elim
  | coe a =>
    have ha : 0 ≤ a := by exact_mod_cast hnonneg
    simp only [rootDepth, he, WithTop.untopD_coe]
    exact_mod_cast (Int.toNat_of_nonneg ha).symm

theorem mem_maximalIdeal_pow_iff {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
    (hnormalized : ∃ π : K, v π = (1 : WithTop ℤ))
    (a : Ring v) (j : ℕ) :
    a ∈ (IsLocalRing.maximalIdeal (Ring v)) ^ j ↔ (j : WithTop ℤ) ≤ v (a : K) := by
  obtain ⟨π, hπ⟩ := hnormalized
  let p : Ring v := ⟨π, by change 0 ≤ v π; rw [hπ]; decide⟩
  have hp : v (p : K) = 1 := hπ
  have hm : IsLocalRing.maximalIdeal (Ring v) = Ideal.span {p} := by
    ext b
    rw [Valuation.mem_maximalIdeal_iff, Ideal.mem_span_singleton,
      (Valuation.valuationSubring.integers v.toValuation).dvd_iff_le]
    change 0 < v (b : K) ↔ v (p : K) ≤ v (b : K)
    rw [hp]
    cases v (b : K) with
    | top => simp
    | coe b => norm_cast
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    (Valuation.valuationSubring.integers v.toValuation).dvd_iff_le]
  change v ((p : K) ^ j) ≤ v (a : K) ↔ _
  rw [v.map_pow, hp]
  have hn : j • (1 : WithTop ℤ) = (j : WithTop ℤ) := by
    change j • (↑(1 : ℤ) : WithTop ℤ) = ↑(j : ℤ)
    rw [← WithTop.coe_nsmul]
    simp
  rw [hn]

theorem mem_principalUnits_iff (v : AddValuation K (WithTop ℤ)) (hn : ∃ π : K, v π = 1)
    (u : (Ring v)ˣ) (j : ℕ) (hj : j ≠ 0) :
    u ∈ principalUnits v j ↔ (j : WithTop ℤ) ≤ v (((u : Ring v) : K) - 1) := by
  rw [principalUnits, if_neg hj]
  change (u : Ring v) - 1 ∈ IsLocalRing.maximalIdeal (Ring v) ^ j ↔ _
  rw [mem_maximalIdeal_pow_iff v hn]
  convert Iff.rfl using 2 <;> simp

theorem unit_valuation_eq_zero (v : AddValuation K (WithTop ℤ)) (u : (Ring v)ˣ) : v ((u : Ring v) : K) = 0 := by
  have h := (Valuation.valuationSubring.integers v.toValuation).one_of_isUnit u.isUnit
  exact h
theorem cubeRoots_sub_valuation [CharZero K] (v : AddValuation K (WithTop ℤ))
    (hn : ∃ π : K, v π = 1) (ζ : (Ring v)ˣ) (hz : IsPrimitiveRoot ((ζ : Ring v) : K) 3)
    (ξ η : (Ring v)ˣ) (hξ : ξ ∈ cubeRoots v ζ) (hη : η ∈ cubeRoots v ζ) (hne : ξ ≠ η) :
    v (((ξ : Ring v) : K) - ((η : Ring v) : K)) = (rootDepth v ζ : WithTop ℤ) := by
  have hp : (((ζ : Ring v) : K)) ^ 3 = 1 := hz.pow_eq_one
  have hs : 1 - (((ζ : Ring v) : K)) ^ 2 = - (((ζ : Ring v) : K)) ^ 2 * (1 - ((ζ : Ring v) : K)) := by
    calc
      _ = - (((ζ : Ring v) : K)) ^ 2 * (1 - ((ζ : Ring v) : K)) + (1 - (((ζ : Ring v) : K)) ^ 3) := by ring
      _ = _ := by rw [hp]; ring
  have hv2 : v (1 - (((ζ : Ring v) : K)) ^ 2) = (rootDepth v ζ : WithTop ℤ) := by
    rw [hs, v.map_mul, v.map_neg, v.map_pow, unit_valuation_eq_zero, rootDepth_spec v hn ζ hz]
    simp
  have hv12 : v (((ζ : Ring v) : K) - (((ζ : Ring v) : K)) ^ 2) = (rootDepth v ζ : WithTop ℤ) := by
    rw [show ((ζ : Ring v) : K) - (((ζ : Ring v) : K)) ^ 2 = ((ζ : Ring v) : K) * (1 - ((ζ : Ring v) : K)) by ring,
      v.map_mul, unit_valuation_eq_zero, rootDepth_spec v hn ζ hz, zero_add]
  have hv1 := rootDepth_spec v hn ζ hz
  simp only [cubeRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hξ hη
  rcases hξ with hξ | hξ | hξ <;> rcases hη with hη | hη | hη
  all_goals try exact (hne (hξ.trans hη.symm)).elim
  all_goals try (simpa [hξ, hη] using hv1)
  all_goals try (simpa [hξ, hη] using hv2)
  all_goals try (simpa [hξ, hη] using hv12)
  all_goals try (simpa [hξ, hη, v.map_sub_swap] using hv1)
  all_goals try (simpa [hξ, hη, v.map_sub_swap] using hv2)
  all_goals try (simpa [hξ, hη, v.map_sub_swap] using hv12)
theorem rootCoset_valuation_le (v : AddValuation K (WithTop ℤ))
    (hn : ∃ π : K, v π = 1) (ξ u : (Ring v)ˣ) (j : ℕ) (hj : j ≠ 0)
    (hu : u ∈ rootCoset v ξ j) :
    (j : WithTop ℤ) ≤ v (((u : Ring v) : K) - ((ξ : Ring v) : K)) := by
  obtain ⟨a, ha, rfl⟩ := hu
  have ha' : (j : WithTop ℤ) ≤ v (((a : Ring v) : K) - 1) := by
    have h := (mem_maximalIdeal_pow_iff v hn ((a : Ring v) - 1) j).mp
      (by simpa [principalUnits, hj] using ha)
    convert h using 1 <;> simp
  have hf : (((ξ * a : (Ring v)ˣ) : Ring v) : K) - ((ξ : Ring v) : K) =
      ((ξ : Ring v) : K) * (((a : Ring v) : K) - 1) := by simp; ring
  rw [hf, v.map_mul, unit_valuation_eq_zero, zero_add]
  exact ha'

theorem rootCosets_pairwise_disjoint [CharZero K] (v : AddValuation K (WithTop ℤ))
    (hnormalized : ∃ π : K, v π = (1 : WithTop ℤ))
    (ζ : (Ring v)ˣ) (hζ : IsPrimitiveRoot ((ζ : Ring v) : K) 3)
    (j : ℕ) (hj : 1 ≤ j) (hdeep : 3 * rootDepth v ζ < j) :
    (cubeRoots v ζ).Pairwise (fun ξ η =>
      Disjoint (rootCoset v ξ (j - 2 * rootDepth v ζ))
        (rootCoset v η (j - 2 * rootDepth v ζ))) := by
  intro ξ hξ η hη hne
  apply Set.disjoint_left.mpr
  intro u huξ huη
  have hj0 : j - 2 * rootDepth v ζ ≠ 0 := by omega
  have h1 := rootCoset_valuation_le v hnormalized ξ u (j - 2 * rootDepth v ζ) hj0 huξ
  have h2 := rootCoset_valuation_le v hnormalized η u (j - 2 * rootDepth v ζ) hj0 huη
  have h3 : (↑(j - 2 * rootDepth v ζ) : WithTop ℤ) ≤
      v (((ξ : Ring v) : K) - ((η : Ring v) : K)) := by
    have h := v.map_sub (((u : Ring v) : K) - ((η : Ring v) : K))
      (((u : Ring v) : K) - ((ξ : Ring v) : K))
    have hf : (((u : Ring v) : K) - ((η : Ring v) : K)) -
      (((u : Ring v) : K) - ((ξ : Ring v) : K)) =
      ((ξ : Ring v) : K) - ((η : Ring v) : K) := by ring
    rw [hf] at h
    exact le_trans (le_min h2 h1) h
  rw [cubeRoots_sub_valuation v hnormalized ζ hζ ξ η hξ hη hne] at h3
  have h4 : ((j - 2 * rootDepth v ζ : ℕ) : ℤ) ≤ (rootDepth v ζ : ℤ) := by
    exact_mod_cast h3
  omega

private theorem cubic_factor [CharZero K] (v : AddValuation K (WithTop ℤ))
    (ζ : (Ring v)ˣ) (hz : IsPrimitiveRoot ((ζ : Ring v) : K) 3) (x : K) :
    v (x ^ 3 - 1) = v (x - 1) + v (x - ((ζ : Ring v) : K)) +
      v (x - ((ζ : Ring v) : K) ^ 2) := by
  let z : K := ((ζ : Ring v) : K)
  have hp : z ^ 2 + z + 1 = 0 := by
    have : (z - 1) * (z ^ 2 + z + 1) = 0 := by
      calc
        _ = z ^ 3 - 1 := by ring
        _ = 0 := by rw [hz.pow_eq_one]; ring
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (hz.ne_one (by decide)))
  have hf : x ^ 3 - 1 = (x - 1) * (x - z) * (x - z ^ 2) := by
    calc
      _ = (x - 1) * (x - z) * (x - z ^ 2) +
        (x - 1) * x * (z ^ 2 + z + 1) - (x - 1) * (z ^ 3 - 1) := by ring
      _ = _ := by rw [hp, hz.pow_eq_one]; ring
  rw [hf, v.map_mul, v.map_mul]

private theorem distance_large (v : AddValuation K (WithTop ℤ)) (x a b : K)
    (h : v (a - b) < v (x - a)) : v (x - b) = v (a - b) := by
  rw [show x - b = (x - a) + (a - b) by ring]
  exact v.map_add_eq_of_lt_right h

private theorem rootCoset_valuation_iff (v : AddValuation K (WithTop ℤ))
    (hn : ∃ π : K, v π = 1) (ξ u : (Ring v)ˣ) (j : ℕ) (hj : j ≠ 0) :
    u ∈ rootCoset v ξ j ↔ (j : WithTop ℤ) ≤ v (((u : Ring v) : K) - ((ξ : Ring v) : K)) := by
  constructor
  · exact rootCoset_valuation_le v hn ξ u j hj
  · intro hu
    refine ⟨ξ⁻¹ * u, ?_, by simp⟩
    rw [mem_principalUnits_iff v hn _ j hj]
    have hf : (((ξ⁻¹ * u : (Ring v)ˣ) : Ring v) : K) - 1 =
        (((ξ⁻¹ : (Ring v)ˣ) : Ring v) : K) * (((u : Ring v) : K) - ((ξ : Ring v) : K)) := by
      have hh : (((ξ⁻¹ : (Ring v)ˣ) : Ring v) : K) * ((ξ : Ring v) : K) = 1 := by
        have h := ξ.inv_mul
        exact_mod_cast h
      change (((ξ⁻¹ : (Ring v)ˣ) : Ring v) : K) * ((u : Ring v) : K) - 1 = _
      rw [mul_sub, hh]
    rw [hf, v.map_mul, unit_valuation_eq_zero, zero_add]
    exact hu

private theorem root_gaps [CharZero K] (v : AddValuation K (WithTop ℤ))
    (hn : ∃ π : K, v π = 1) (ζ : (Ring v)ˣ)
    (hz : IsPrimitiveRoot ((ζ : Ring v) : K) 3) :
    v (1 - ((ζ : Ring v) : K)) = (rootDepth v ζ : WithTop ℤ) ∧
    v (1 - ((ζ : Ring v) : K) ^ 2) = (rootDepth v ζ : WithTop ℤ) ∧
    v (((ζ : Ring v) : K) - ((ζ : Ring v) : K) ^ 2) =
      (rootDepth v ζ : WithTop ℤ) := by
  have hzn : ζ ≠ 1 := by
    intro h
    apply hz.ne_one (by decide)
    simpa [h]
  have hzn2 : ζ ^ 2 ≠ 1 := by
    intro h
    exact hz.pow_ne_one_of_pos_of_lt (by decide : 2 ≠ 0) (by decide : 2 < 3)
      (by simpa using congrArg (fun a : (Ring v)ˣ => ((a : Ring v) : K)) h)
  have hzn12 : ζ ≠ ζ ^ 2 := by
    intro h
    have he := congrArg (fun t : (Ring v)ˣ => ζ⁻¹ * t) h
    have hh : 1 = ζ := by simpa [pow_two, mul_assoc] using he
    exact hzn hh.symm
  refine ⟨rootDepth_spec v hn ζ hz, ?_, ?_⟩
  · have h := cubeRoots_sub_valuation v hn ζ hz 1 (ζ ^ 2)
      (by simp [cubeRoots]) (by simp [cubeRoots]) (Ne.symm hzn2)
    simpa using h
  · exact cubeRoots_sub_valuation v hn ζ hz ζ (ζ ^ 2)
      (by simp [cubeRoots]) (by simp [cubeRoots]) hzn12

private theorem depth_shift (t : WithTop ℤ) (j r : ℕ) (h : 2 * r ≤ j) :
    (j : WithTop ℤ) ≤ t + (r : WithTop ℤ) + r ↔
      ((j - 2 * r : ℕ) : WithTop ℤ) ≤ t := by
  cases t with
  | top => simp
  | coe t =>
    change (↑(j : ℤ) : WithTop ℤ) ≤ ↑t + ↑(r : ℤ) + ↑(r : ℤ) ↔
      (↑((j - 2 * r : ℕ) : ℤ) : WithTop ℤ) ≤ ↑t
    rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    omega

private theorem three_balls (v : AddValuation K (WithTop ℤ)) (x a b c : K)
    (r j : ℕ) (hj : 3 * r < j)
    (hab : v (a - b) = (r : WithTop ℤ))
    (hac : v (a - c) = (r : WithTop ℤ))
    (hbc : v (b - c) = (r : WithTop ℤ)) :
    (j : WithTop ℤ) ≤ v (x - a) + v (x - b) + v (x - c) ↔
    ((j - 2 * r : ℕ) : WithTop ℤ) ≤ v (x - a) ∨
    ((j - 2 * r : ℕ) : WithTop ℤ) ≤ v (x - b) ∨
    ((j - 2 * r : ℕ) : WithTop ℤ) ≤ v (x - c) := by
  have hdr : (r : WithTop ℤ) < ((j - 2 * r : ℕ) : WithTop ℤ) := by
    exact_mod_cast (show r < j - 2 * r by omega)
  have hba : v (b - a) = (r : WithTop ℤ) := by rw [v.map_sub_swap, hab]
  have hca : v (c - a) = (r : WithTop ℤ) := by rw [v.map_sub_swap, hac]
  have hcb : v (c - b) = (r : WithTop ℤ) := by rw [v.map_sub_swap, hbc]
  have caseA (h : (r : WithTop ℤ) < v (x - a)) :
      v (x - b) = (r : WithTop ℤ) ∧ v (x - c) = (r : WithTop ℤ) := by
    exact ⟨(distance_large v x a b (by rwa [hab])).trans hab,
      (distance_large v x a c (by rwa [hac])).trans hac⟩
  have caseB (h : (r : WithTop ℤ) < v (x - b)) :
      v (x - a) = (r : WithTop ℤ) ∧ v (x - c) = (r : WithTop ℤ) := by
    exact ⟨(distance_large v x b a (by rwa [hba])).trans hba,
      (distance_large v x b c (by rwa [hbc])).trans hbc⟩
  have caseC (h : (r : WithTop ℤ) < v (x - c)) :
      v (x - a) = (r : WithTop ℤ) ∧ v (x - b) = (r : WithTop ℤ) := by
    exact ⟨(distance_large v x c a (by rwa [hca])).trans hca,
      (distance_large v x c b (by rwa [hcb])).trans hcb⟩
  have shift := fun t => depth_shift t j r (by omega)
  constructor
  · intro h
    by_cases ha : (r : WithTop ℤ) < v (x - a)
    · obtain ⟨hb, hc⟩ := caseA ha
      rw [hb, hc] at h
      exact Or.inl ((shift _).mp h)
    by_cases hb : (r : WithTop ℤ) < v (x - b)
    · obtain ⟨ha, hc⟩ := caseB hb
      rw [ha, hc, add_comm (r : WithTop ℤ) (v (x - b))] at h
      exact Or.inr (Or.inl ((shift _).mp h))
    by_cases hc : (r : WithTop ℤ) < v (x - c)
    · obtain ⟨ha, hb⟩ := caseC hc
      rw [ha, hb] at h
      have he : (r : WithTop ℤ) + r + v (x - c) = v (x - c) + r + r := by ac_rfl
      rw [he] at h
      exact Or.inr (Or.inr ((shift _).mp h))
    have hle : (j : WithTop ℤ) ≤ (r : WithTop ℤ) + r + r :=
      h.trans (add_le_add (add_le_add (le_of_not_gt ha) (le_of_not_gt hb)) (le_of_not_gt hc))
    change (↑(j : ℤ) : WithTop ℤ) ≤ ↑(r : ℤ) + ↑(r : ℤ) + ↑(r : ℤ) at hle
    rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hle
    omega
  · rintro (h | h | h)
    · obtain ⟨hb, hc⟩ := caseA (hdr.trans_le h)
      rw [hb, hc]
      exact (shift _).mpr h
    · obtain ⟨ha, hc⟩ := caseB (hdr.trans_le h)
      rw [ha, hc, add_comm (r : WithTop ℤ) (v (x - b))]
      exact (shift _).mpr h
    · obtain ⟨ha, hb⟩ := caseC (hdr.trans_le h)
      rw [ha, hb]
      have he : (r : WithTop ℤ) + r + v (x - c) = v (x - c) + r + r := by ac_rfl
      rw [he]
      exact (shift _).mpr h

theorem cubicPreimage_deep [CharZero K] (v : AddValuation K (WithTop ℤ))
    (hnormalized : ∃ π : K, v π = (1 : WithTop ℤ))
    (ζ : (Ring v)ˣ) (hζ : IsPrimitiveRoot ((ζ : Ring v) : K) 3)
    (j : ℕ) (hj : 1 ≤ j) (hdeep : 3 * rootDepth v ζ < j) :
    cubicPreimage v j = ⋃ ξ ∈ cubeRoots v ζ, rootCoset v ξ (j - 2 * rootDepth v ζ) := by
  ext u
  rw [cubicPreimage, Set.mem_setOf_eq,
    mem_principalUnits_iff v hnormalized _ j (by omega)]
  change (j : WithTop ℤ) ≤ v (((u : Ring v) : K) ^ 3 - 1) ↔ _
  rw [cubic_factor v ζ hζ]
  obtain ⟨hg1, hg2, hg3⟩ := root_gaps v hnormalized ζ hζ
  rw [three_balls v ((u : Ring v) : K) 1 ((ζ : Ring v) : K)
    (((ζ : Ring v) : K) ^ 2) (rootDepth v ζ) j hdeep hg1 hg2 hg3]
  have hd : j - 2 * rootDepth v ζ ≠ 0 := by omega
  simp only [cubeRoots, Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h | h)
    · refine ⟨1, Or.inl rfl, ?_⟩
      exact (rootCoset_valuation_iff v hnormalized 1 u _ hd).mpr (by simpa using h)
    · refine ⟨ζ, Or.inr (Or.inl rfl), ?_⟩
      exact (rootCoset_valuation_iff v hnormalized ζ u _ hd).mpr h
    · refine ⟨ζ ^ 2, Or.inr (Or.inr rfl), ?_⟩
      exact (rootCoset_valuation_iff v hnormalized (ζ ^ 2) u _ hd).mpr (by simpa using h)
  · rintro ⟨ξ, hξ, hu⟩
    have h := (rootCoset_valuation_iff v hnormalized ξ u _ hd).mp hu
    rcases hξ with rfl | rfl | rfl
    · exact Or.inl (by simpa using h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by simpa using h))

end CubicUnitBalls
end DedekindZetaZeroFree
