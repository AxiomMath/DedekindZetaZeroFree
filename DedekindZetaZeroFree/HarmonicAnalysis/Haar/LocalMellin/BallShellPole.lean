module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.LocalFieldHalfPlaneIntegrability
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

@[expose] public section

section

noncomputable section

namespace DedekindZetaZeroFree.KPRankOneMellin.FiniteShellExpansion

theorem mellin_shell_series_eq_geometric_tail
    (q m : ℝ) (hq : 1 < q) (N : ℤ) (s : ℂ) (hs : 0 < s.re) :
    (∑' k : ℕ,
      (↑(m * (1 - q⁻¹) * q ^ (-(N + (k : ℤ)))) : ℂ) *
        ((q ^ (-(N + (k : ℤ))) : ℝ) : ℂ) ^ (s - 1)) =
      (↑(m * (1 - q⁻¹)) : ℂ) *
        (Complex.exp (-s * (Real.log q : ℂ))) ^ N /
        (1 - Complex.exp (-s * (Real.log q : ℂ))) := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  let Q : ℂ := Complex.exp (-s * (Real.log q : ℂ))
  have hQ : ‖Q‖ < 1 := by
    dsimp [Q]
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    simpa using neg_neg_of_pos (mul_pos hs (Real.log_pos hq))
  have hterm (n : ℤ) :
      ((q ^ (-n) : ℝ) : ℂ) * ((q ^ (-n) : ℝ) : ℂ) ^ (s - 1) = Q ^ n := by
    have hxpos : 0 < q ^ (-n) := zpow_pos hqpos _
    have hx : ((q ^ (-n) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hxpos
    have hcombine : ((q ^ (-n) : ℝ) : ℂ) *
        ((q ^ (-n) : ℝ) : ℂ) ^ (s - 1) =
        ((q ^ (-n) : ℝ) : ℂ) ^ s := by
      calc
        _ = ((q ^ (-n) : ℝ) : ℂ) ^ (1 + (s - 1)) := by
          rw [Complex.cpow_add 1 (s - 1) hx, Complex.cpow_one]
        _ = _ := by congr 1; ring
    rw [hcombine,
      Complex.cpow_def_of_ne_zero hx, ← Complex.ofReal_log hxpos.le,
      Real.log_zpow]
    dsimp [Q]
    rw [← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  have heq (k : ℕ) :
      (↑(m * (1 - q⁻¹) * q ^ (-(N + (k : ℤ)))) : ℂ) *
          ((q ^ (-(N + (k : ℤ))) : ℝ) : ℂ) ^ (s - 1) =
        ((↑(m * (1 - q⁻¹)) : ℂ) * Q ^ N) * Q ^ k := by
    rw [Complex.ofReal_mul, mul_assoc, hterm, zpow_add₀ (Complex.exp_ne_zero _)]
    simp [Q, mul_assoc]
  simp_rw [heq]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hQ, div_eq_mul_inv]

end DedekindZetaZeroFree.KPRankOneMellin.FiniteShellExpansion

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPRankOneMellin.FiniteShellExpansion

open MeasureTheory IsDedekindDomain NumberField
open scoped WithZero

set_option backward.isDefEq.respectTransparency false in

theorem q_shell_haar_mass
    (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] :
    μ {0} = 0 ∧ ∀ n : ℤ,
      μ {x : v.adicCompletion F | ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-n)} =
        ENNReal.ofReal
          ((μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))).toReal *
            (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) *
            (Ideal.absNorm v.asIdeal : ℝ) ^ (-n)) := by
  constructor
  · have hq : (1 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    obtain ⟨p, hp⟩ := v.valuation_exists_uniformizer F
    have hn : ‖FinitePlace.embedding v p‖ = (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ) := by
      rw [FinitePlace.norm_embedding', hp,
        WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v) (by simp),
        NNReal.coe_zpow]
      rfl
    borelize (v.adicCompletion F)
    have hp0 : FinitePlace.embedding v p ≠ 0 := by
      apply norm_pos_iff.mp
      rw [hn]
      exact zpow_pos (by linarith) _
    let d : (v.adicCompletion F)ˣ := Units.mk0 _ hp0
    have hmap := DedekindZetaZeroFree.CompletionHaarModule.map_mul F v μ d
    have heq := congrArg (fun ν : Measure (v.adicCompletion F) => ν {0}) hmap
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)] at heq
    have hpre : (fun x : v.adicCompletion F => (d : v.adicCompletion F) * x) ⁻¹' {0} = {0} := by
      ext x; simp [d, hp0]
    rw [hpre, Measure.smul_apply, smul_eq_mul] at heq
    have hfin : μ {0} ≠ ⊤ := isCompact_singleton.measure_lt_top.ne
    have hr := congrArg ENNReal.toReal heq
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (norm_nonneg _)] at hr
    change (μ {0}).toReal = ‖FinitePlace.embedding v p‖⁻¹ * (μ {0}).toReal at hr
    rw [hn, zpow_neg_one, inv_inv] at hr
    have hz : (μ {0}).toReal = 0 := by nlinarith
    exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right hfin
  · intro n
    borelize (v.adicCompletion F)
    have hq1 : (1 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    have hq : (0 : ℝ) < (v.asIdeal.absNorm : ℝ) := by linarith
    have hdiscrete (x : v.adicCompletion F) :
        ‖x‖ < (v.asIdeal.absNorm : ℝ) ^ (-n) ↔
        ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-n - 1) := by
      by_cases hx : x = 0
      · simp [hx, (zpow_pos hq _).le, zpow_pos hq]
      · have hv : Valued.v x ≠ 0 :=
          (Valuation.ne_zero_iff (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).mpr hx
        rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, NNReal.coe_zpow]
        change (v.asIdeal.absNorm : ℝ) ^ (Valued.v x).log < _ ↔
          (v.asIdeal.absNorm : ℝ) ^ (Valued.v x).log ≤ _
        rw [zpow_lt_zpow_iff_right₀ hq1, zpow_le_zpow_iff_right₀ hq1]
        omega
    have hset : {x : v.adicCompletion F | ‖x‖ = (v.asIdeal.absNorm : ℝ) ^ (-n)} =
        {x : v.adicCompletion F | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-n)} \
        {x : v.adicCompletion F | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-n - 1)} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_diff, ← hdiscrete x, not_lt]
      exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
    have hfinite (k : ℤ) : μ {x : v.adicCompletion F | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ k} ≠ ⊤ := by
      exact (show IsCompact {x : v.adicCompletion F | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ k} from by
        simpa only [Metric.closedBall, dist_zero_right] using
          isCompact_closedBall (0 : v.adicCompletion F) ((v.asIdeal.absNorm : ℝ) ^ k)).measure_lt_top.ne
    have hsubset : {x : v.adicCompletion F | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-n - 1)} ⊆
        {x : v.adicCompletion F | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-n)} := by
      intro x hx
      exact (hdiscrete x).mpr hx |>.le
    have hmeas : MeasurableSet {x : v.adicCompletion F | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-n - 1)} :=
      (isClosed_le continuous_norm continuous_const).measurableSet
    have hsfin : μ {x : v.adicCompletion F | ‖x‖ = (v.asIdeal.absNorm : ℝ) ^ (-n)} ≠ ⊤ := by
      apply ne_top_of_le_ne_top (hfinite (-n))
      exact measure_mono (by intro x hx; exact (show ‖x‖ = _ from hx).le)
    have hO : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = {x | ‖x‖ ≤ 1} := by
      ext x
      exact ⟨fun hx => norm_le_one_of_mem_adicCompletionIntegers v hx,
        fun hx => mem_adicCompletionIntegers_of_norm_le_one v hx⟩
    rw [← ENNReal.ofReal_toReal hsfin]
    congr 1
    change μ.real {x : v.adicCompletion F | ‖x‖ = (v.asIdeal.absNorm : ℝ) ^ (-n)} = _
    rw [hset, measureReal_sdiff hsubset hmeas (hfinite (-n)),
      DedekindZetaZeroFree.CompletionHaarModule.closedBall_measure F v μ (-n),
      DedekindZetaZeroFree.CompletionHaarModule.closedBall_measure F v μ (-n - 1), hO,
      zpow_sub₀ hq.ne', zpow_one]
    simp only [Measure.real]
    ring

end DedekindZetaZeroFree.KPRankOneMellin.FiniteShellExpansion

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPRankOneMellin.FiniteShellExpansion

open MeasureTheory IsDedekindDomain NumberField

theorem q_ball_mellin_integrable
    (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (N : ℤ) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun x : v.adicCompletion F =>
      (Metric.closedBall (0 : v.adicCompletion F)
        ((Ideal.absNorm v.asIdeal : ℝ) ^ (-N))).indicator
        (fun _ => (1 : ℂ)) x * (‖x‖ : ℂ) ^ (s - 1)) μ := by
  classical
  let B := Metric.closedBall (0 : v.adicCompletion F)
    ((Ideal.absNorm v.asIdeal : ℝ) ^ (-N))
  have hq : 0 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact lt_trans zero_lt_one (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
  have hBc : IsClopen B := IsUltrametricDist.isClopen_closedBall _ (zpow_pos hq _).ne'
  have hlc : IsLocallyConstant (B.indicator (fun _ => (1 : ℂ))) := by
    exact (LocallyConstant.charFn ℂ hBc).isLocallyConstant
  have hcs : HasCompactSupport (B.indicator (fun _ => (1 : ℂ))) := by
    rw [HasCompactSupport]
    apply (isCompact_closedBall (0 : v.adicCompletion F) _).of_isClosed_subset
    · exact isClosed_tsupport _
    · apply closure_minimal
      · exact Set.support_indicator_subset
      · exact hBc.isClosed
  exact DedekindZetaZeroFree.KPRankOneMellin.AdditiveMellinIntegrability.additive_mellin_integrable
    F v μ _ hlc hcs s hs

end DedekindZetaZeroFree.KPRankOneMellin.FiniteShellExpansion

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPRankOneMellin.FiniteShellExpansion

open MeasureTheory IsDedekindDomain NumberField

theorem q_ball_mellin_eq_shell_series
    (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (N : ℤ) (s : ℂ) (hs : 0 < s.re) :
    (∫ x : v.adicCompletion F,
      (Metric.closedBall (0 : v.adicCompletion F)
        ((Ideal.absNorm v.asIdeal : ℝ) ^ (-N))).indicator
        (fun _ => (1 : ℂ)) x * (‖x‖ : ℂ) ^ (s - 1) ∂μ) =
      ∑' k : ℕ,
        (↑((μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))).toReal *
          (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) *
          (Ideal.absNorm v.asIdeal : ℝ) ^ (-(N + (k : ℤ)))) : ℂ) *
        (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(N + (k : ℤ))) : ℝ) : ℂ) ^ (s - 1) := by
  let q : ℝ := Ideal.absNorm v.asIdeal
  let B : Set (v.adicCompletion F) := Metric.closedBall 0 (q ^ (-N))
  let A (k : ℕ) : Set (v.adicCompletion F) := {x | ‖x‖ = q ^ (-(N + (k : ℤ)))}
  let f (x : v.adicCompletion F) : ℂ := B.indicator (fun _ => (1 : ℂ)) x * (‖x‖ : ℂ) ^ (s - 1)
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hA (k : ℕ) : MeasurableSet (A k) :=
    isClosed_eq continuous_norm continuous_const |>.measurableSet
  have hsingle : μ ({0} : Set (v.adicCompletion F)) = 0 :=
    (q_shell_haar_mass F v μ).1
  have hnorm (x : v.adicCompletion F) (hx : x ≠ 0) : ∃ n : ℤ, ‖x‖ = q ^ n := by
    refine ⟨WithZero.log (Valued.v x), ?_⟩
    rw [FinitePlace.norm_def]
    rw [WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v)
      (by simpa [Valued.v] using hx)]
    rw [NNReal.coe_zpow]
    rfl
  have hsub (k : ℕ) : A k ⊆ B := by
    intro x hx
    change ‖x‖ = q ^ (-(N + (k : ℤ))) at hx
    change x ∈ Metric.closedBall 0 (q ^ (-N))
    rw [Metric.mem_closedBall, dist_zero_right, hx]
    apply zpow_le_zpow_right₀ hq.le
    omega
  have hcover : (⋃ k, A k) = B \ {0} := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      refine ⟨hsub k hk, ?_⟩
      intro hx0
      have hxpos : 0 < q ^ (-(N + (k : ℤ))) := zpow_pos hq0 _
      simp only [Set.mem_singleton_iff] at hx0
      subst x
      have : (0 : ℝ) = q ^ (-(N + (k : ℤ))) := by simpa [A] using hk
      exact (ne_of_lt hxpos) this
    · rintro ⟨hxB, hx0⟩
      have hx0' : x ≠ 0 := by simpa using hx0
      obtain ⟨n, hn⟩ := hnorm x hx0'
      have hle : n ≤ -N := by
        apply (zpow_le_zpow_iff_right₀ hq).mp
        rw [← hn]
        simpa [B, Metric.mem_closedBall] using hxB
      refine Set.mem_iUnion.mpr ⟨(-N-n).toNat, ?_⟩
      have hk : ((-N-n).toNat : ℤ) = -N-n := Int.toNat_of_nonneg (by omega)
      change ‖x‖ = q ^ (-(N + (((-N-n).toNat : ℕ) : ℤ)))
      rw [hk]
      convert hn using 1 <;> congr 1 <;> omega
  have hdis : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have heq : q ^ (-(N + (i : ℤ))) = q ^ (-(N + (j : ℤ))) :=
      (show ‖x‖ = _ from hxi).symm.trans (show ‖x‖ = _ from hxj)
    have := zpow_right_injective₀ hq0 (ne_of_gt hq) heq
    exact hij (by omega)
  have hf : Integrable f μ := q_ball_mellin_integrable F v μ N s hs
  have hset : (∫ x, f x ∂μ) = ∫ x in ⋃ k, A k, f x ∂μ := by
    rw [← integral_indicator (MeasurableSet.iUnion hA)]
    apply integral_congr_ae
    apply ae_iff.mpr
    apply measure_mono_null (t := ({0} : Set (v.adicCompletion F))) ?_ hsingle
    intro x hx
    change x ∈ ({0} : Set (v.adicCompletion F))
    by_contra hxne
    have hxne' : x ≠ 0 := by simpa using hxne
    by_cases hb : x ∈ B
    · have hmem : x ∈ ⋃ k, A k := hcover.symm ▸ ⟨hb, hxne⟩
      exact False.elim (hx (by simp [Set.indicator_of_mem hmem]))
    · have hnmem : x ∉ ⋃ k, A k := fun h => hb (hcover ▸ h).1
      exact False.elim (hx (by simp [f, Set.indicator_of_notMem hb,
        Set.indicator_of_notMem hnmem]))
  rw [hset, integral_iUnion hA hdis hf.integrableOn]
  congr 1
  ext k
  have hAk := hA k
  rw [setIntegral_congr_fun hAk (g := fun _ =>
      ((q ^ (-(N + (k : ℤ))) : ℝ) : ℂ) ^ (s - 1)) (by
    intro x hx
    have hb : x ∈ B := hsub k hx
    simp only [f, Set.indicator_of_mem hb, one_mul]
    rw [show ‖x‖ = q ^ (-(N + (k : ℤ))) from hx])]
  rw [setIntegral_const, RCLike.real_smul_eq_coe_mul]
  have hmass := (q_shell_haar_mass F v μ).2 (N + (k : ℤ))
  have hcoeff : 0 ≤ (μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))).toReal *
      (1 - q⁻¹) * q ^ (-(N + (k : ℤ))) := by
    apply mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ?_) (le_of_lt (zpow_pos hq0 _))
    have : q⁻¹ ≤ 1 := inv_le_one₀ hq0 |>.mpr hq.le
    linarith
  have hmass' : (μ.real (A k)) =
      (μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))).toReal *
      (1 - q⁻¹) * q ^ (-(N + (k : ℤ))) := by
    rw [measureReal_def, show μ (A k) = _ from hmass, ENNReal.toReal_ofReal hcoeff]
  rw [hmass']
  rfl

end DedekindZetaZeroFree.KPRankOneMellin.FiniteShellExpansion

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPRankOneMellin

open MeasureTheory IsDedekindDomain NumberField Filter
open scoped Topology

variable (F : Type*) [Field F] [NumberField F]
  (v : HeightOneSpectrum (RingOfIntegers F))
  [MeasurableSpace (v.adicCompletion F)]
  [hBorel : BorelSpace (v.adicCompletion F)]

abbrev q : ℕ := Ideal.absNorm v.asIdeal

def multiplicativeMeasure (μ : Measure (v.adicCompletion F)) :
    Measure (v.adicCompletion F) :=
  (μ.restrict {0}ᶜ).withDensity (fun x => ENNReal.ofReal (‖x‖⁻¹))

def mellin (μ : Measure (v.adicCompletion F))
    (φ : v.adicCompletion F → ℂ) (s : ℂ) : ℂ :=
  ∫ x, φ x * (‖x‖ : ℂ) ^ s ∂multiplicativeMeasure F v μ

open scoped Valued

theorem completion_addHaar_nullSingletonClass (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] :
    NullSingletonClass μ := by
  obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one (v.adicCompletion F)
  have hi : Function.Injective (fun n : ℕ => x ^ n) := by
    intro a b hab
    have hn : ‖x‖ ^ a = ‖x‖ ^ b := by simpa only [norm_pow] using congrArg norm hab
    exact (pow_right_strictAnti₀ hx0 hx1).injective hn
  have hK := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx1).isCompact_insert_range
  constructor
  intro a
  by_contra ha
  have h0 : μ {0} ≠ 0 := by simpa only [Measure.addHaar_singleton] using ha
  have ht : μ (insert 0 (Set.range fun n : ℕ => x ^ n)) = ⊤ :=
    ((Set.infinite_range_of_injective hi).mono (Set.subset_insert _ _)).meas_eq_top
      ⟨μ {0}, h0, fun a _ => (Measure.addHaar_singleton μ a).ge⟩
  exact hK.measure_lt_top.ne ht

private theorem density_smul_eq (φ : v.adicCompletion F → ℂ) (s : ℂ)
    (x : v.adicCompletion F) (hx : x ≠ 0) :
    (ENNReal.ofReal ‖x‖⁻¹).toReal • (φ x * (‖x‖ : ℂ) ^ s) =
      φ x * (‖x‖ : ℂ) ^ (s - 1) := by
  have hn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hx)
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (norm_nonneg _)),
    Complex.cpow_sub _ _ hn, Complex.cpow_one, Complex.real_smul,
    Complex.ofReal_inv]
  ring

theorem mellin_eq_additive_integral (μ : Measure (v.adicCompletion F)) [NullSingletonClass μ]
    (φ : v.adicCompletion F → ℂ) (s : ℂ) :
    mellin F v μ φ s = ∫ x, φ x * (‖x‖ : ℂ) ^ (s - 1) ∂μ := by
  have hm : Measurable (fun x : v.adicCompletion F => ENNReal.ofReal ‖x‖⁻¹) := by
    fun_prop
  have ht : ∀ᵐ x ∂μ.restrict {0}ᶜ, ENNReal.ofReal ‖x‖⁻¹ < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hμ : μ.restrict {0}ᶜ = μ := by simp
  unfold mellin multiplicativeMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hm ht, hμ]
  apply integral_congr_ae
  filter_upwards [show ∀ᵐ x ∂μ, x ≠ 0 from μ.ae_ne 0] with x hx
  exact density_smul_eq F v φ s x hx

theorem mellin_integrable_iff_additive (μ : Measure (v.adicCompletion F)) [NullSingletonClass μ]
    (φ : v.adicCompletion F → ℂ) (s : ℂ) :
    Integrable (fun x => φ x * (‖x‖ : ℂ) ^ s) (multiplicativeMeasure F v μ) ↔
      Integrable (fun x => φ x * (‖x‖ : ℂ) ^ (s - 1)) μ := by
  have hm : Measurable (fun x : v.adicCompletion F => ENNReal.ofReal ‖x‖⁻¹) := by
    fun_prop
  have ht : ∀ᵐ x ∂μ.restrict {0}ᶜ, ENNReal.ofReal ‖x‖⁻¹ < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hμ : μ.restrict {0}ᶜ = μ := by simp
  unfold multiplicativeMeasure
  rw [integrable_withDensity_iff_integrable_smul' hm ht, hμ]
  apply integrable_congr
  filter_upwards [show ∀ᵐ x ∂μ, x ≠ 0 from μ.ae_ne 0] with x hx
  exact density_smul_eq F v φ s x hx

end DedekindZetaZeroFree.KPRankOneMellin

end

end
