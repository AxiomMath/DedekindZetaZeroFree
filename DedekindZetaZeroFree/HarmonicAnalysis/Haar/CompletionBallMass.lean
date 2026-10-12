module

public import ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.FinitePlaceCompletion
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar

@[expose] public section

noncomputable section
open scoped Classical nonZeroDivisors WithZero Pointwise ENNReal NNReal
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.CompletionHaarModule

variable (F : Type*) [Field F] [NumberField F]

local instance completionMeasurable (v : HeightOneSpectrum (RingOfIntegers F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance completionBorel (v : HeightOneSpectrum (RingOfIntegers F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private theorem norm_lt_one_iff_le_inv_absNorm (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) (x : v.adicCompletion F) :
    ‖x‖ < 1 ↔ ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ) := by
  have hq : (0 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  by_cases hx : x = 0
  · simp [hx, (zpow_pos hq (-1)).le]
  · have hv : Valued.v x ≠ 0 :=
      (Valuation.ne_zero_iff (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).mpr hx
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, NNReal.coe_zpow]
    rw [← zpow_zero (v.asIdeal.absNorm : ℝ)]
    have hq1 : (1 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    change (v.asIdeal.absNorm : ℝ) ^ (Valued.v x).log < _ ↔
      (v.asIdeal.absNorm : ℝ) ^ (Valued.v x).log ≤ _
    rw [zpow_lt_zpow_iff_right₀ hq1, zpow_le_zpow_iff_right₀ hq1]
    omega

private theorem mem_maximalIdeal_iff_norm_lt_one (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) (x : v.adicCompletionIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔
      ‖(x : v.adicCompletion F)‖ < 1 := by
  have h := Valuation.mem_maximalIdeal_iff (v.adicCompletion F)
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (a := x)
  exact h.trans Valued.toNormedField.norm_lt_one_iff.symm

 noncomputable def residueEquiv (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    (RingOfIntegers F ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
  GlobalClassFieldTheory.ClassFieldAxiom.ringOfIntegersQuotientEquivAdicResidueField v

private theorem residue_card (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) =
      v.asIdeal.absNorm := by
  rw [← Nat.card_congr (residueEquiv F v).toEquiv, Ideal.absNorm_apply]
  rfl

set_option maxHeartbeats 800000 in

private theorem one_step (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hfinite : μ {x | ‖x‖ ≤ 1} ≠ ⊤) :
    (v.asIdeal.absNorm : ℝ) * μ.real {x | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ)} =
      μ.real {x | ‖x‖ ≤ 1} := by
  let O := v.adicCompletionIntegers F
  let κ := IsLocalRing.ResidueField O
  letI : Finite κ := Finite.of_equiv (RingOfIntegers F ⧸ v.asIdeal)
    (residueEquiv F v).toEquiv
  letI : Fintype κ := Fintype.ofFinite κ
  let r : κ → O := fun z => (IsLocalRing.residue_surjective (R := O) z).choose
  have hr (z : κ) : IsLocalRing.residue O (r z) = z :=
    (IsLocalRing.residue_surjective (R := O) z).choose_spec
  let U : Set (v.adicCompletion F) := {x | ‖x‖ < 1}
  let a : κ → v.adicCompletion F := fun z => r z
  have hU : MeasurableSet U := by
    exact (isOpen_lt continuous_norm continuous_const).measurableSet
  have hUfin : μ U ≠ ⊤ := ne_top_of_le_ne_top hfinite
    (measure_mono (by intro x hx; exact le_of_lt (show ‖x‖ < 1 from hx)))
  have hcoset (x : v.adicCompletion F) (hx : ‖x‖ ≤ 1) (z : κ) :
      x ∈ a z +ᵥ U ↔ IsLocalRing.residue O ⟨x, mem_adicCompletionIntegers_of_norm_le_one v hx⟩ = z := by
    rw [Set.mem_vadd_set]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hn : ‖x - a z‖ < 1 := by
        change ‖y‖ < 1 at hy
        have heq : x - a z = y := by change a z + y = x at hxy; rw [← hxy]; abel
        simpa only [heq] using hy
      have hm : (⟨x, mem_adicCompletionIntegers_of_norm_le_one v hx⟩ : O) - r z ∈
          IsLocalRing.maximalIdeal O :=
        (mem_maximalIdeal_iff_norm_lt_one F v _).mpr hn
      have heq := (IsLocalRing.residue_eq_zero_iff _).mpr hm
      rw [map_sub, hr, sub_eq_zero] at heq
      exact heq
    · intro heq
      have hm : (⟨x, mem_adicCompletionIntegers_of_norm_le_one v hx⟩ : O) - r z ∈
          IsLocalRing.maximalIdeal O := by
        apply (IsLocalRing.residue_eq_zero_iff _).mp
        rw [map_sub, heq, hr, sub_self]
      have hn := (mem_maximalIdeal_iff_norm_lt_one F v
        ((⟨x, mem_adicCompletionIntegers_of_norm_le_one v hx⟩ : O) - r z)).mp hm
      refine ⟨x - a z, ?_, ?_⟩
      · exact hn
      · change a z + (x - a z) = x
        abel
  have hsub (z : κ) : a z +ᵥ U ⊆ {x : v.adicCompletion F | ‖x‖ ≤ 1} := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_vadd_set.mp hx
    change ‖a z + y‖ ≤ 1
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (norm_le_one_of_mem_adicCompletionIntegers v (r z).property) (le_of_lt hy))
  have hcover : {x : v.adicCompletion F | ‖x‖ ≤ 1} = ⋃ z : κ, a z +ᵥ U := by
    ext x
    constructor
    · intro hx
      apply Set.mem_iUnion.mpr
      exact ⟨IsLocalRing.residue O ⟨x, mem_adicCompletionIntegers_of_norm_le_one v hx⟩,
        (hcoset x hx _).mpr rfl⟩
    · intro hx
      obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hx
      exact hsub z hz
  have hdisj : Pairwise (fun z w : κ => Disjoint (a z +ᵥ U) (a w +ᵥ U)) := by
    intro z w hzw
    apply Set.disjoint_left.mpr
    intro x hxz hxw
    have hx := hsub z hxz
    exact hzw (((hcoset x hx z).mp hxz).symm.trans ((hcoset x hx w).mp hxw))
  have hmass : μ.real {x | ‖x‖ ≤ 1} = (Nat.card κ : ℝ) * μ.real U := by
    rw [hcover, measureReal_iUnion_fintype hdisj (fun z => hU.const_vadd (a z))
      (fun z => by simpa only [measure_vadd] using hUfin)]
    simp only [Measure.real, measure_vadd, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [residue_card F v] at hmass
  rw [hmass]
  congr 2
  ext x
  exact (norm_lt_one_iff_le_inv_absNorm F v x).symm

private theorem smul_ball {K : Type*} [NormedField K] (d : Kˣ) :
    d • {x : K | ‖x‖ ≤ 1} = {x : K | ‖x‖ ≤ ‖(d : K)‖} := by
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ‖(d : K) * y‖ ≤ ‖(d : K)‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hy
  · intro hx
    refine ⟨(d : K)⁻¹ * x, ?_, ?_⟩
    · change ‖(d : K)⁻¹ * x‖ ≤ 1
      rw [norm_mul, norm_inv]
      exact (inv_mul_le_iff₀ (norm_pos_iff.mpr d.ne_zero)).mpr (by simpa using hx)
    · change (d : K) * ((d : K)⁻¹ * x) = x
      rw [← mul_assoc, mul_inv_cancel₀ d.ne_zero, one_mul]

private theorem mass_scale {K : Type*} [NormedField K] [IsUltrametricDist K]
    [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] (d : Kˣ) :
    μ.real {x | ‖x‖ ≤ ‖(d : K)‖} = (distribHaarChar K d : ℝ) * μ.real {x | ‖x‖ ≤ 1} := by
  have hs : IsOpen {x : K | ‖x‖ ≤ 1} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (IsUltrametricDist.isOpen_closedBall (0 : K) (one_ne_zero : (1 : ℝ) ≠ 0))
  have h := Measure.measure_isAddHaarMeasure_eq_smul_of_isOpen (DomMulAct.mk d • μ) μ hs
  rw [addHaarScalarFactor_smul_eq_distribHaarChar μ d] at h
  have hm : μ {x | ‖x‖ ≤ ‖(d : K)‖} = (distribHaarChar K d : ℝ≥0∞) * μ {x | ‖x‖ ≤ 1} := by
    simpa only [Measure.domSMul_apply, Equiv.symm_apply_apply, ENNReal.smul_def, smul_eq_mul, smul_ball] using h
  exact congrArg ENNReal.toReal hm |>.trans (by simp [Measure.real, ENNReal.toReal_mul])

private theorem unit_ball_finite (v : HeightOneSpectrum (RingOfIntegers F))
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] :
    μ {x : v.adicCompletion F | ‖x‖ ≤ 1} ≠ ⊤ := by
  exact (show IsCompact {x : v.adicCompletion F | ‖x‖ ≤ 1} from by
    simpa only [Metric.closedBall, dist_zero_right] using
      isCompact_closedBall (0 : v.adicCompletion F) 1).measure_lt_top.ne

private theorem exists_uniformizer_norm (v : HeightOneSpectrum (RingOfIntegers F)) :
    ∃ d : (v.adicCompletion F)ˣ,
      ‖(d : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ) := by
  have hq : 0 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  obtain ⟨p, hp⟩ := v.valuation_exists_uniformizer F
  let π := FinitePlace.embedding v p
  have hnorm : ‖π‖ = (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ) := by
    have hqn : (v.asIdeal.absNorm : ℝ≥0) ≠ 0 := HeightOneSpectrum.absNorm_ne_zero v
    have hπ : (WithZero.exp (-1 : ℤ)) ≠ (0 : ℤᵐ⁰) := by simp
    rw [FinitePlace.norm_embedding', hp, WithZeroMulInt.toNNReal_neg_apply hqn hπ,
      NNReal.coe_zpow]
    rfl
  have hπ : π ≠ 0 := norm_pos_iff.mp (hnorm ▸ zpow_pos hq (-1))
  exact ⟨Units.mk0 π hπ, hnorm⟩

private theorem uniformizer_character (v : HeightOneSpectrum (RingOfIntegers F))
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (d : (v.adicCompletion F)ˣ)
    (hd : ‖(d : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ)) :
    (distribHaarChar (v.adicCompletion F) d : ℝ) = (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ) := by
  have hq : 0 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  have hs : IsOpen {x : v.adicCompletion F | ‖x‖ ≤ 1} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (IsUltrametricDist.isOpen_closedBall (0 : v.adicCompletion F)
        (one_ne_zero : (1 : ℝ) ≠ 0))
  have hmasspos : 0 < μ.real {x : v.adicCompletion F | ‖x‖ ≤ 1} :=
    ENNReal.toReal_pos (hs.measure_ne_zero μ ⟨0, by simp⟩) (unit_ball_finite F v μ)
  have hscale := mass_scale μ d
  rw [hd] at hscale
  have hone := one_step F v μ (unit_ball_finite F v μ)
  rw [hscale] at hone
  have he : (v.asIdeal.absNorm : ℝ) * (distribHaarChar (v.adicCompletion F) d : ℝ) = 1 := by
    nlinarith
  rw [zpow_neg_one, ← one_div]
  apply (eq_div_iff hq.ne').mpr
  simpa [mul_comm] using he

private theorem character_eq_norm (v : HeightOneSpectrum (RingOfIntegers F))
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (c : (v.adicCompletion F)ˣ) :
    (distribHaarChar (v.adicCompletion F) c : ℝ) = ‖(c : v.adicCompletion F)‖ := by
  obtain ⟨d, hd⟩ := exists_uniformizer_norm F v
  have hc := uniformizer_character F v μ d hd
  let k : ℤ := -(Valued.v (c : v.adicCompletion F)).log
  have hcnorm : ‖(c : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ) ^ (-k) := by
    have hv : Valued.v (c : v.adicCompletion F) ≠ 0 :=
      (Valuation.ne_zero_iff (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).mpr c.ne_zero
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, NNReal.coe_zpow]
    simp only [k, neg_neg]
    rfl
  have hdk : ‖((d ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ =
      (v.asIdeal.absNorm : ℝ) ^ (-k) := by
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, hd, ← zpow_mul]
    congr 1
    omega
  have hs : IsOpen {x : v.adicCompletion F | ‖x‖ ≤ 1} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (IsUltrametricDist.isOpen_closedBall (0 : v.adicCompletion F)
        (one_ne_zero : (1 : ℝ) ≠ 0))
  have hmasspos : 0 < μ.real {x : v.adicCompletion F | ‖x‖ ≤ 1} :=
    ENNReal.toReal_pos (hs.measure_ne_zero μ ⟨0, by simp⟩) (unit_ball_finite F v μ)
  have hpow := mass_scale μ (d ^ k)
  rw [hdk, map_zpow, NNReal.coe_zpow, hc, ← zpow_mul] at hpow
  have hscale := mass_scale μ c
  rw [hcnorm] at hscale
  have hchar : (distribHaarChar (v.adicCompletion F) c : ℝ) =
      (v.asIdeal.absNorm : ℝ) ^ ((-1 : ℤ) * k) := by
    have heq : (distribHaarChar (v.adicCompletion F) c : ℝ) *
        μ.real {x : v.adicCompletion F | ‖x‖ ≤ 1} =
        (v.asIdeal.absNorm : ℝ) ^ ((-1 : ℤ) * k) *
        μ.real {x : v.adicCompletion F | ‖x‖ ≤ 1} := by
      simpa only [neg_one_mul] using hscale.symm.trans hpow
    exact mul_right_cancel₀ hmasspos.ne' heq
  rw [hchar, hcnorm, neg_one_mul]

theorem map_mul (v : HeightOneSpectrum (RingOfIntegers F))
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (c : (v.adicCompletion F)ˣ) :
    Measure.map (fun x : v.adicCompletion F => (c : v.adicCompletion F) * x) μ =
      (ENNReal.ofReal ‖(c : v.adicCompletion F)‖)⁻¹ • μ := by
  have h := Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk c⁻¹ • μ) μ
  rw [addHaarScalarFactor_smul_eq_distribHaarChar μ] at h
  have hchar : (distribHaarChar (v.adicCompletion F) c : ℝ≥0∞) =
      ENNReal.ofReal ‖(c : v.adicCompletion F)‖ := by
    rw [← character_eq_norm F v μ c]
    simp
  rw [(distribHaarChar (v.adicCompletion F)).map_inv] at h
  have hmap : DomMulAct.mk c⁻¹ • μ =
      Measure.map (fun x : v.adicCompletion F => (c : v.adicCompletion F) * x) μ := by
    rfl
  rw [hmap] at h
  ext s
  rw [h]
  simp only [Measure.smul_apply, NNReal.smul_def, ENNReal.smul_def, smul_eq_mul,
    ENNReal.coe_inv (ne_of_gt distribHaarChar_pos), hchar]

theorem closedBall_measure (v : HeightOneSpectrum (RingOfIntegers F))
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] (k : ℤ) :
    μ.real {x : v.adicCompletion F | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ k} =
      (v.asIdeal.absNorm : ℝ) ^ k * μ.real {x : v.adicCompletion F | ‖x‖ ≤ 1} := by
  obtain ⟨d, hd⟩ := exists_uniformizer_norm F v
  have hdk : ‖((d ^ (-k) : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ =
      (v.asIdeal.absNorm : ℝ) ^ k := by
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, hd, ← zpow_mul]
    congr 1
    omega
  have h := mass_scale μ (d ^ (-k))
  rw [character_eq_norm F v μ, hdk] at h
  exact h

end DedekindZetaZeroFree.CompletionHaarModule

end
