module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.SmallFrequencySum
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.ExceptionalSum
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.GoodSum
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.LargeFrequencyShift
public import DedekindZetaZeroFree.Moments.Probes.Poisson.CompactScaleBound

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawOmittedRowsAssembly31

open DedekindZetaZeroFree
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawRowSumDefinitions31

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem large_norm_le (D : DedekindZetaZeroFree.Quantitative.FixedData S η) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      Summable (fun u : ↥(largeSet D Z) =>
        ‖RawFixed.FixedData.initialRowIntegral D u.1 Z‖) ∧
      ∑' u : ↥(largeSet D Z), ‖RawFixed.FixedData.initialRowIntegral D u.1 Z‖ ≤
        C * Z ^ ((717 : ℝ) / 2000) := by
  obtain ⟨C0, hC0, H⟩ := RawLargeRowShift31.raw_large_row_bound D 1 one_pos
  obtain ⟨K, hK0, hK⟩ := RawFrequencyCount.frequency_count_lt D.recipe
  have hcount : ∀ Y : ℝ, 1 ≤ Y →
      ((({a : Frequency D.recipe | q D a ≤ Y}).ncard : ℕ) : ℝ) ≤ (2 * K) * Y := by
    intro Y hY
    have hsub : {a : Frequency D.recipe | q D a ≤ Y} ⊆
        {u : Frequency D.recipe | frequencyNorm D.recipe u < Y + 1} := by
      intro u hu
      have h1 : frequencyNorm D.recipe u ≤ Y := hu
      show frequencyNorm D.recipe u < Y + 1
      linarith
    have h1 := (hK (Y + 1) (by linarith)).1
    have h2 := (hK (Y + 1) (by linarith)).2
    calc ((({a : Frequency D.recipe | q D a ≤ Y}).ncard : ℕ) : ℝ)
        ≤ ((({u : Frequency D.recipe | frequencyNorm D.recipe u < Y + 1}).ncard : ℕ) : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hsub h1
      _ ≤ K * (Y + 1) := h2
      _ ≤ (2 * K) * Y := by nlinarith
  have hp : (1 : ℝ) < Scales.tailShift - 1 := by unfold Scales.tailShift; norm_num
  obtain ⟨Ct, hCt, ht⟩ := FrequencyPowerTails.tail_dominated (q D) (Scales.tailShift - 1) (2 * K) hp
    (fun Y => finite_q_le D Y) hcount
  refine ⟨C0 * Ct, mul_pos hC0 hCt, fun Z hZ => ?_⟩
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hZ1 : (1 : ℝ) ≤ Z := by linarith
  have hX : (1 : ℝ) ≤ Z ^ Scales.largeCutoffExponent :=
    Real.one_le_rpow hZ1 (by unfold Scales.largeCutoffExponent; norm_num)
  have hB : 0 ≤ C0 * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) := by positivity
  have hbound : ∀ a ∈ largeSet D Z,
      0 ≤ ‖RawFixed.FixedData.initialRowIntegral D a Z‖ ∧
      ‖RawFixed.FixedData.initialRowIntegral D a Z‖ ≤
        (C0 * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift)) *
          q D a ^ (-(Scales.tailShift - 1)) := by
    intro a ha
    refine ⟨norm_nonneg _, ?_⟩
    have h := (H a ha.1 Z hZ).2
    have hq : (-(Scales.tailShift - 1)) = -Scales.tailShift + 1 := by ring
    show _ ≤ _ * frequencyNorm D.recipe a ^ (-(Scales.tailShift - 1))
    rw [hq]
    exact h
  obtain ⟨hsum, hle⟩ := ht (Z ^ Scales.largeCutoffExponent) hX _ hB (largeSet D Z)
    (fun u => ‖RawFixed.FixedData.initialRowIntegral D u Z‖)
    (fun a ha => ha.2) (fun a ha => hbound a ha)
  have hcomb : C0 * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) * Ct *
      (Z ^ Scales.largeCutoffExponent) ^ (1 - (Scales.tailShift - 1)) =
      (C0 * Ct) * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift +
        Scales.largeCutoffExponent * (1 - (Scales.tailShift - 1))) := by
    have e1 : (Z ^ Scales.largeCutoffExponent) ^ (1 - (Scales.tailShift - 1)) =
        Z ^ (Scales.largeCutoffExponent * (1 - (Scales.tailShift - 1))) := (Real.rpow_mul hZ0.le _ _).symm
    have e2 : Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift +
        Scales.largeCutoffExponent * (1 - (Scales.tailShift - 1))) =
        Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
          Z ^ (Scales.largeCutoffExponent * (1 - (Scales.tailShift - 1))) := Real.rpow_add hZ0 _ _
    rw [e1, e2]
    ring
  have hfin : Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift +
      Scales.largeCutoffExponent * (1 - (Scales.tailShift - 1))) ≤ Z ^ ((717 : ℝ) / 2000) :=
    Real.rpow_le_rpow_of_exponent_le hZ1 (by unfold Scales.tailShift Scales.largeCutoffExponent; norm_num)
  refine ⟨hsum, ?_⟩
  calc ∑' u : ↥(largeSet D Z), ‖RawFixed.FixedData.initialRowIntegral D u.1 Z‖
      ≤ C0 * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) * Ct *
          (Z ^ Scales.largeCutoffExponent) ^ (1 - (Scales.tailShift - 1)) := hle
    _ = (C0 * Ct) * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift +
        Scales.largeCutoffExponent * (1 - (Scales.tailShift - 1))) := hcomb
    _ ≤ (C0 * Ct) * Z ^ ((717 : ℝ) / 2000) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)

theorem rawOmittedSum_bound (D : DedekindZetaZeroFree.Quantitative.FixedData S η) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖PoissonFrequencyDecomposition.omittedSum D Z‖ ≤ C * Z ^ (717 / 2000 : ℝ) := by
  obtain ⟨A, ρ, hA, hconv, hρ, -⟩ := RawDetector31.detector_exists D
  obtain ⟨Cs, hCs, hs⟩ := RawSmallRowsSum31.smallRows_norm_tsum_le D
  obtain ⟨Ce, hCe, Ze, hZe, he⟩ :=
    RawExceptionalRowsSum31.exceptionalRows_norm_tsum_le D A ρ hA hconv hρ
  obtain ⟨Cg, hCg, Zg, hZg, hg⟩ := RawGoodRowsSum31.raw_good_rows_sum_abs D A ρ hA hconv hρ
  obtain ⟨Cl, hCl, hl⟩ := large_norm_le D
  have hbd : ∀ Z : ℝ, max Ze Zg ≤ Z →
      ‖PoissonFrequencyDecomposition.omittedSum D Z‖ ≤
        (Cs + Ce + Cg + Cl) * Z ^ ((717 : ℝ) / 2000) := by
    intro Z hZ
    have hZ2 : 2 ≤ Z := le_trans hZe (le_trans (le_max_left _ _) hZ)
    have hZe' : Ze ≤ Z := le_trans (le_max_left _ _) hZ
    have hZg' : Zg ≤ Z := le_trans (le_max_right _ _) hZ
    have hZpos : 0 < Z := by linarith
    obtain ⟨hsE, hE⟩ := he Z hZe'
    obtain ⟨hsG, hG⟩ := hg Z hZg'
    obtain ⟨hsS, hS⟩ := hs Z hZ2
    obtain ⟨hsL, hL⟩ := hl Z hZ2
    have hrow : ∀ u : Frequency D.recipe,
        RawInitialKernel31.rawinitialRowIntegral D u Z =
          RawFixed.FixedData.initialRowIntegral D u Z :=
      fun u => (RawInitialKernel31.initialRowIntegral_eq D u Z hZpos).symm
    rw [RawInitialKernel31.omittedSum_eq_twisted D Z hZpos]
    simp only [hrow]
    set G : Frequency D.recipe → ℝ := fun u => ‖RawFixed.FixedData.initialRowIntegral D u Z‖
      with hGdef
    have hG0 : ∀ u, 0 ≤ G u := fun u => norm_nonneg _
    set T : Set (Frequency D.recipe) := {u | u ≠ principalFrequency D.recipe} with hTdef
    set sm := smallSet D Z with hsmdef
    set ex := exceptionalMedium D ρ Z with hexdef
    set gd := goodMedium D ρ Z with hgdef
    set lg := largeSet D Z with hlgdef
    have key : ∀ u ∈ T, u ∈ sm ∨ u ∈ ex ∨ u ∈ gd ∨ u ∈ lg := by
      intro u hu
      have h1 : u ∈ {u : Frequency D.recipe | u ≠ principalFrequency D.recipe} := hu
      rw [nonprincipal_cover D Z] at h1
      rcases h1 with (h1 | h1) | h1
      · exact Or.inl h1
      · have h2 : u ∈ exceptionalMedium D ρ Z ∪ goodMedium D ρ Z := by
          rw [exceptional_good_union D ρ Z]; exact h1
        rcases h2 with h2 | h2
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (Or.inr h1))
    have hI : ∀ s : Set (Frequency D.recipe), ∀ u, 0 ≤ s.indicator G u :=
      fun s u => Set.indicator_nonneg (fun v _ => hG0 v) u
    have hcover : ∀ u, T.indicator G u ≤
        sm.indicator G u + ex.indicator G u + gd.indicator G u + lg.indicator G u := by
      intro u
      by_cases hu : u ∈ T
      · rcases key u hu with h | h | h | h
        · rw [Set.indicator_of_mem hu, Set.indicator_of_mem h]
          linarith [hI ex u, hI gd u, hI lg u]
        · rw [Set.indicator_of_mem hu, Set.indicator_of_mem h]
          linarith [hI sm u, hI gd u, hI lg u]
        · rw [Set.indicator_of_mem hu, Set.indicator_of_mem h]
          linarith [hI sm u, hI ex u, hI lg u]
        · rw [Set.indicator_of_mem hu, Set.indicator_of_mem h]
          linarith [hI sm u, hI ex u, hI gd u]
      · rw [Set.indicator_of_notMem hu]
        linarith [hI sm u, hI ex u, hI gd u, hI lg u]
    have hsmS : Summable (sm.indicator G) := (summable_subtype_iff_indicator).mp hsS
    have hexS : Summable (ex.indicator G) := (summable_subtype_iff_indicator).mp hsE
    have hgdS : Summable (gd.indicator G) := (summable_subtype_iff_indicator).mp hsG
    have hlgS : Summable (lg.indicator G) := (summable_subtype_iff_indicator).mp hsL
    have hsumFour : Summable (fun u => sm.indicator G u + ex.indicator G u + gd.indicator G u +
        lg.indicator G u) := ((hsmS.add hexS).add hgdS).add hlgS
    have hTS : Summable (T.indicator G) :=
      Summable.of_nonneg_of_le (fun u => hI T u) hcover hsumFour
    have hVS : Summable (fun f : TwistedProbeRowDefinitions.TwistedRow D => G f.val) := by
      refine Summable.of_nonneg_of_le (fun f => hG0 f.val) (fun f => ?_)
        (hTS.comp_injective Subtype.val_injective)
      have hmem : f.val ∈ T := RawInitialKernel31.twisted_ne_principal D f
      show G f.val ≤ T.indicator G f.val
      rw [Set.indicator_of_mem hmem]
    have hle1 : ∑' f : TwistedProbeRowDefinitions.TwistedRow D, G f.val ≤ ∑' u, T.indicator G u :=
      Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun c hc => hI T c)
        (fun f => by
          have hmem : f.val ∈ T := RawInitialKernel31.twisted_ne_principal D f
          show G f.val ≤ T.indicator G f.val
          rw [Set.indicator_of_mem hmem])
        hVS hTS
    have hS' : ∑' u : ↥sm, G u ≤ Cs * Z ^ ((717 : ℝ) / 2000) := hS
    have hE' : ∑' u : ↥ex, G u ≤ Ce * Z ^ ((717 : ℝ) / 2000) := hE
    have hG' : ∑' u : ↥gd, G u ≤ Cg * Z ^ ((717 : ℝ) / 2000) := hG
    have hL' : ∑' u : ↥lg, G u ≤ Cl * Z ^ ((717 : ℝ) / 2000) := hL
    have hT1 : ∑' u : ↥sm, G u = ∑' u, sm.indicator G u := tsum_subtype sm G
    have hT2 : ∑' u : ↥ex, G u = ∑' u, ex.indicator G u := tsum_subtype ex G
    have hT3 : ∑' u : ↥gd, G u = ∑' u, gd.indicator G u := tsum_subtype gd G
    have hT4 : ∑' u : ↥lg, G u = ∑' u, lg.indicator G u := tsum_subtype lg G
    have hsplit : ∑' u, (sm.indicator G u + ex.indicator G u + gd.indicator G u +
        lg.indicator G u) = ∑' u, sm.indicator G u + ∑' u, ex.indicator G u +
        ∑' u, gd.indicator G u + ∑' u, lg.indicator G u := by
      rw [Summable.tsum_add ((hsmS.add hexS).add hgdS) hlgS,
        Summable.tsum_add (hsmS.add hexS) hgdS, Summable.tsum_add hsmS hexS]
    have hmain : ∑' u, T.indicator G u ≤ ∑' u, sm.indicator G u + ∑' u, ex.indicator G u +
        ∑' u, gd.indicator G u + ∑' u, lg.indicator G u := by
      rw [← hsplit]
      exact hTS.tsum_le_tsum hcover hsumFour
    have hnormle : ‖∑' f : TwistedProbeRowDefinitions.TwistedRow D,
        RawFixed.FixedData.initialRowIntegral D f.val Z‖ ≤ ∑' f : TwistedProbeRowDefinitions.TwistedRow D, G f.val :=
      norm_tsum_le_tsum_norm (f := fun f : TwistedProbeRowDefinitions.TwistedRow D =>
        RawFixed.FixedData.initialRowIntegral D f.val Z) hVS
    have hfin : ∑' u, sm.indicator G u + ∑' u, ex.indicator G u +
        ∑' u, gd.indicator G u + ∑' u, lg.indicator G u ≤
        (Cs + Ce + Cg + Cl) * Z ^ ((717 : ℝ) / 2000) := by
      rw [← hT1, ← hT2, ← hT3, ← hT4]
      have : (Cs + Ce + Cg + Cl) * Z ^ ((717 : ℝ) / 2000) =
          Cs * Z ^ ((717 : ℝ) / 2000) + Ce * Z ^ ((717 : ℝ) / 2000) +
          Cg * Z ^ ((717 : ℝ) / 2000) + Cl * Z ^ ((717 : ℝ) / 2000) := by ring
      rw [this]
      linarith
    linarith
  obtain ⟨C', hC', h'⟩ := RawCompactScale31.omittedSum_bound_all_of_bound_ge D
    (by norm_num : (0 : ℝ) < 717 / 2000) (le_max_of_le_left hZe) hbd
  exact ⟨C', hC', h'⟩

end DedekindZetaZeroFree.Quantitative.RawOmittedRowsAssembly31
