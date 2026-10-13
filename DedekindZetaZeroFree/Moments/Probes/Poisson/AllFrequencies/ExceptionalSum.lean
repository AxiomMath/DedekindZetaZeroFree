module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.LowContour
public import DedekindZetaZeroFree.Moments.Probes.Poisson.DyadicRows
public import DedekindZetaZeroFree.Analysis.DyadicGeometricPowerSums

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawExceptionalRowsSum31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open DedekindZetaZeroFree.Quantitative.RawDetectorHeightPrefix31
open DedekindZetaZeroFree.Quantitative.RawRowSumDefinitions31
open scoped Classical

private theorem dyad_geom (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ K : Finset ℕ, (∀ k ∈ K, (2:ℝ)^k ≤ X) →
      ∑ k ∈ K, ((2:ℝ)^k)^β ≤ C * X^β := by
  have ht : (1:ℝ) < (2:ℝ)^β := Real.one_lt_rpow (by norm_num) hβ
  have hid : ∀ k : ℕ, ((2:ℝ)^k)^β = ((2:ℝ)^β)^k := fun k => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  refine ⟨(2:ℝ)^β / ((2:ℝ)^β - 1), div_pos (by linarith) (by linarith), ?_⟩
  intro X hX K hK
  set N := Nat.log 2 ⌊X⌋₊ with hN
  have hfl : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa using hX)
  have hpowN : (2:ℝ)^N ≤ X := by
    have h1 : 2^N ≤ ⌊X⌋₊ := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2^N : ℕ) : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (Nat.floor_le (by linarith))
  have hsub : K ⊆ Finset.range (N+1) := by
    intro k hk
    rw [Finset.mem_range]
    have h1 : (2:ℝ)^k ≤ X := hK k hk
    have h2 : 2^k ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast h1)
    have h3 : k ≤ Nat.log 2 ⌊X⌋₊ := Nat.le_log_of_pow_le (by norm_num) h2
    omega
  calc ∑ k ∈ K, ((2:ℝ)^k)^β ≤ ∑ k ∈ Finset.range (N+1), ((2:ℝ)^k)^β :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ k ∈ Finset.range (N+1), ((2:ℝ)^β)^k := Finset.sum_congr rfl (fun k _ => hid k)
    _ = (((2:ℝ)^β)^(N+1) - 1) / ((2:ℝ)^β - 1) := geom_sum_eq (ne_of_gt ht) _
    _ ≤ (((2:ℝ)^β)^(N+1)) / ((2:ℝ)^β - 1) := by
        have : (0:ℝ) < (2:ℝ)^β - 1 := by linarith
        gcongr
        linarith [pow_pos (show (0:ℝ) < (2:ℝ)^β by positivity) (N+1)]
    _ = (2:ℝ)^β / ((2:ℝ)^β - 1) * (((2:ℝ)^N)^β) := by
        rw [hid N, pow_succ]; ring
    _ ≤ (2:ℝ)^β / ((2:ℝ)^β - 1) * X^β := by
        apply mul_le_mul_of_nonneg_left _ (by apply div_nonneg <;> linarith)
        exact Real.rpow_le_rpow (by positivity) hpowN (by linarith)

private theorem kappa_s_ge (U₀ Z : ℝ) (hU : 0 ≤ U₀) (hZ : (2*U₀)^5 ≤ Z) :
    2 * U₀ ≤ Z ^ DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent := by
  have h1 : ((2*U₀)^(5:ℕ) : ℝ) ^ (DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent) ≤ Z ^ (DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent) :=
    Real.rpow_le_rpow (by positivity) hZ (by unfold DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent; norm_num)
  have h2 : ((2*U₀)^(5:ℕ) : ℝ) ^ (DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent) = 2*U₀ := by
    have : DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent = ((5:ℕ):ℝ)⁻¹ := by
      unfold DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent; norm_num
    rw [this]
    exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
  linarith

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

private theorem sum_reassoc (K : Finset ℕ) (C1 C2 Z E α c : ℝ) (hZ : 0 < Z) :
    ∑ k ∈ K, (C2 * ((2:ℝ)^k) ^ α) * (C1 * Z ^ E * ((2:ℝ)^k) ^ c)
      = (C1 * C2 * Z ^ E) * ∑ k ∈ K, ((2:ℝ)^k) ^ (α + c) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hpos : (0:ℝ) < (2:ℝ)^k := by positivity
  rw [Real.rpow_add hpos]
  ring

theorem finset_norm_sum_le (A ρ : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (hρ : HeightSpec D A ρ) :
    ∃ C : ℝ, 0 < C ∧ ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → ∀ G : Finset (Frequency D.recipe),
      (↑G : Set (Frequency D.recipe)) ⊆ exceptionalMedium D ρ Z →
        ∑ u ∈ G, ‖initialRowIntegral D u Z‖ ≤ C * Z ^ ((717 : ℝ) / 2000) := by
  obtain ⟨C1, hC1, hrow⟩ :=
    DedekindZetaZeroFree.Quantitative.RawLowRowContour31.initialRowIntegral_dyad_bound D ((1:ℝ)/4000) (by norm_num)
  obtain ⟨C2, hC2, U₀, hU₀, hcard⟩ :=
    DedekindZetaZeroFree.Quantitative.RawDetectorCount31.rawExceptionalSet_card D A ρ hA hρ
  obtain ⟨C3, hC3, hgeom⟩ := dyad_geom ((317:ℝ)/500 + ((1:ℝ)/25 + (1:ℝ)/4000)) (by norm_num)
  refine ⟨C1 * C2 * C3, by positivity, max 2 ((2 * U₀)^5), le_max_left _ _, ?_⟩
  intro Z hZ G hG
  have hZ2 : 2 ≤ Z := le_trans (le_max_left _ _) hZ
  have hZ1 : 1 ≤ Z := by linarith
  have hZ5 : (2 * U₀)^5 ≤ Z := le_trans (le_max_right _ _) hZ
  have hZs : 2 * U₀ ≤ Z ^ DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent := kappa_s_ge U₀ Z (by linarith) hZ5

  have hlow : ∀ u ∈ G, U₀ ≤ (2:ℝ) ^ dyadIndex D u ∧ (2:ℝ) ^ dyadIndex D u ≤ Z ^ DedekindZetaZeroFree.Quantitative.Scales.largeCutoffExponent := by
    intro u hu
    have hm := hG (Finset.mem_coe.mpr hu)
    have hd := dyadIndex_spec' D u
    have hs : Z ^ DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent < q D u := hm.1.2.1
    have hl : q D u ≤ Z ^ DedekindZetaZeroFree.Quantitative.Scales.largeCutoffExponent := hm.1.2.2
    constructor
    · linarith [hd.2]
    · linarith [hd.1]
  have hrowb : ∀ u ∈ G, ‖initialRowIntegral D u Z‖ ≤
      C1 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine DedekindZetaZeroFree.Quantitative.Scales.zLine)
        * ((2:ℝ) ^ dyadIndex D u) ^ ((1:ℝ)/25 + (1:ℝ)/4000) := by
    intro u hu
    have hm := hG (Finset.mem_coe.mpr hu)
    have hex := exceptionalMedium_mem_dyad D hm
    have hd := dyadIndex_spec' D u
    have hl := hlow u hu
    have h2 : (2:ℝ) ≤ (2:ℝ) ^ dyadIndex D u := le_trans hU₀ hl.1
    exact hrow u hm.1.1 ((2:ℝ) ^ dyadIndex D u) h2 hd.1 hd.2 Z hZ2

  set K : Finset ℕ := G.image (fun u => dyadIndex D u) with hK
  have hKmem : ∀ k ∈ K, ∃ u ∈ G, dyadIndex D u = k := by
    intro k hk
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨u, hu, rfl⟩
  have hKlow : ∀ k ∈ K, U₀ ≤ (2:ℝ)^k ∧ (2:ℝ)^k ≤ Z ^ DedekindZetaZeroFree.Quantitative.Scales.largeCutoffExponent := by
    intro k hk
    obtain ⟨u, hu, rfl⟩ := hKmem k hk
    exact hlow u hu
  have hcount : ∀ k ∈ K, ((G.filter (fun u => dyadIndex D u = k)).card : ℝ) ≤
      C2 * ((2:ℝ)^k) ^ DedekindZetaZeroFree.Quantitative.DetectorDef.α := by
    intro k hk
    have hcb := (hcard ((2:ℝ)^k) (hKlow k hk).1)
    have hsub : ((G.filter (fun u => dyadIndex D u = k) : Finset (Frequency D.recipe)) : Set (Frequency D.recipe))
        ⊆ rawExceptionalSet D ρ ((2:ℝ)^k) := by
      intro u hu
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe] at hu
      have hm := hG (Finset.mem_coe.mpr hu.1)
      have hex := (exceptionalMedium_mem_dyad D hm).1
      rw [hu.2] at hex
      exact hex
    have := Set.ncard_le_ncard hsub hcb.1
    rw [Set.ncard_coe_finset] at this
    have h3 : ((G.filter (fun u => dyadIndex D u = k)).card : ℝ) ≤
        ((rawExceptionalSet D ρ ((2:ℝ)^k)).ncard : ℝ) := by exact_mod_cast this
    exact h3.trans hcb.2
  have hfinal : Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine DedekindZetaZeroFree.Quantitative.Scales.zLine)
      * (Z ^ DedekindZetaZeroFree.Quantitative.Scales.largeCutoffExponent) ^ ((317:ℝ)/500 + ((1:ℝ)/25 + (1:ℝ)/4000))
      ≤ Z ^ ((717 : ℝ) / 2000) := by
    rw [← Real.rpow_mul (by linarith), ← Real.rpow_add (by linarith)]
    apply Real.rpow_le_rpow_of_exponent_le hZ1
    norm_num [DedekindZetaZeroFree.Quantitative.Scales.kernelExponent, DedekindZetaZeroFree.Quantitative.Scales.xExponent, DedekindZetaZeroFree.Quantitative.Scales.yExponent,
      DedekindZetaZeroFree.Quantitative.Scales.smoothingExponent, DedekindZetaZeroFree.Quantitative.Scales.rightLine, DedekindZetaZeroFree.Quantitative.Scales.contourOffset,
      DedekindZetaZeroFree.Quantitative.Scales.wLine, DedekindZetaZeroFree.Quantitative.Scales.zLine, DedekindZetaZeroFree.Quantitative.Scales.largeCutoffExponent]
  have hZE : 0 ≤ Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine DedekindZetaZeroFree.Quantitative.Scales.zLine) :=
    Real.rpow_nonneg (by linarith) _
  have hC12 : 0 ≤ C1 * C2 := by positivity
  have hZpos : (0:ℝ) < Z := by linarith
  have hα : DedekindZetaZeroFree.Quantitative.DetectorDef.α = (317:ℝ)/500 := by
    norm_num [DedekindZetaZeroFree.Quantitative.DetectorDef.α]
  calc ∑ u ∈ G, ‖initialRowIntegral D u Z‖
      ≤ ∑ u ∈ G, C1 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine DedekindZetaZeroFree.Quantitative.Scales.zLine)
          * ((2:ℝ) ^ dyadIndex D u) ^ ((1:ℝ)/25 + (1:ℝ)/4000) := Finset.sum_le_sum hrowb
    _ = ∑ k ∈ K, ∑ u ∈ G.filter (fun u => dyadIndex D u = k),
          C1 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine DedekindZetaZeroFree.Quantitative.Scales.zLine)
          * ((2:ℝ) ^ dyadIndex D u) ^ ((1:ℝ)/25 + (1:ℝ)/4000) :=
        (Finset.sum_fiberwise_of_maps_to (g := fun u => dyadIndex D u)
          (fun u hu => Finset.mem_image_of_mem _ hu) _).symm
    _ = ∑ k ∈ K, ∑ u ∈ G.filter (fun u => dyadIndex D u = k),
          C1 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine DedekindZetaZeroFree.Quantitative.Scales.zLine)
          * ((2:ℝ) ^ k) ^ ((1:ℝ)/25 + (1:ℝ)/4000) := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro u hu
        rw [(Finset.mem_filter.mp hu).2]
    _ = ∑ k ∈ K, ((G.filter (fun u => dyadIndex D u = k)).card : ℝ) *
          (C1 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine DedekindZetaZeroFree.Quantitative.Scales.zLine)
          * ((2:ℝ) ^ k) ^ ((1:ℝ)/25 + (1:ℝ)/4000)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ K, (C2 * ((2:ℝ)^k) ^ DedekindZetaZeroFree.Quantitative.DetectorDef.α) *
          (C1 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine DedekindZetaZeroFree.Quantitative.Scales.zLine)
          * ((2:ℝ) ^ k) ^ ((1:ℝ)/25 + (1:ℝ)/4000)) := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_right (hcount k hk)
        have : (0:ℝ) ≤ (2:ℝ)^k := by positivity
        have := Real.rpow_nonneg this ((1:ℝ)/25 + (1:ℝ)/4000)
        positivity
    _ = (C1 * C2 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine DedekindZetaZeroFree.Quantitative.Scales.zLine))
          * ∑ k ∈ K, ((2:ℝ)^k) ^ ((317:ℝ)/500 + ((1:ℝ)/25 + (1:ℝ)/4000)) := by
        rw [hα]
        exact sum_reassoc K C1 C2 _ _ _ _ hZpos
    _ ≤ (C1 * C2 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine DedekindZetaZeroFree.Quantitative.Scales.zLine))
          * (C3 * (Z ^ DedekindZetaZeroFree.Quantitative.Scales.largeCutoffExponent) ^ ((317:ℝ)/500 + ((1:ℝ)/25 + (1:ℝ)/4000))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hgeom (Z ^ DedekindZetaZeroFree.Quantitative.Scales.largeCutoffExponent) (Real.one_le_rpow hZ1 (by norm_num [DedekindZetaZeroFree.Quantitative.Scales.largeCutoffExponent])) K
          (fun k hk => (hKlow k hk).2)
    _ = (C1 * C2 * C3) * (Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine DedekindZetaZeroFree.Quantitative.Scales.zLine)
          * (Z ^ DedekindZetaZeroFree.Quantitative.Scales.largeCutoffExponent) ^ ((317:ℝ)/500 + ((1:ℝ)/25 + (1:ℝ)/4000))) := by ring
    _ ≤ (C1 * C2 * C3) * Z ^ ((717 : ℝ) / 2000) :=
        mul_le_mul_of_nonneg_left hfinal (by positivity)

theorem exceptionalRows_norm_tsum_le (A ρ : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (hρ : HeightSpec D A ρ) :
    ∃ C : ℝ, 0 < C ∧ ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      Summable (fun u : exceptionalMedium D ρ Z => ‖initialRowIntegral D u.1 Z‖) ∧
        ∑' u : exceptionalMedium D ρ Z, ‖initialRowIntegral D u.1 Z‖ ≤
          C * Z ^ ((717 : ℝ) / 2000) := by
  obtain ⟨C, hC, Z₀, hZ₀, h⟩ := finset_norm_sum_le D A ρ hA hconv hρ
  refine ⟨C, hC, Z₀, hZ₀, fun Z hZ => ?_⟩
  have hfin : (exceptionalMedium D ρ Z).Finite :=
    (mediumSet_finite D Z).subset (exceptionalMedium_subset D ρ Z)
  haveI : Finite (exceptionalMedium D ρ Z) := hfin.to_subtype
  refine ⟨Summable.of_finite, ?_⟩
  apply Summable.tsum_le_of_sum_le Summable.of_finite
  intro s
  have hsub : ((s.map (Function.Embedding.subtype _) : Finset (Frequency D.recipe)) : Set (Frequency D.recipe))
      ⊆ exceptionalMedium D ρ Z := by
    intro u hu
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hu
    obtain ⟨v, _, rfl⟩ := hu
    exact v.2
  have := h Z hZ _ hsub
  rwa [Finset.sum_map] at this

end

end DedekindZetaZeroFree.Quantitative.RawExceptionalRowsSum31
