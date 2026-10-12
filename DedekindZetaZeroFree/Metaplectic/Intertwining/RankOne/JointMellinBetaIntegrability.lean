module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.CubicCharacterExpansion
public import DedekindZetaZeroFree.Arithmetic.LocalFields.SecondCountability

@[expose] public section

section

noncomputable section

namespace DedekindZetaZeroFree.KPJointRegulator.MellinBetaIntegrability

open MeasureTheory

theorem multiplicativeHaar_sigmaFinite
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
    (dx : Measure K) [dx.IsAddHaarMeasure] :
    SigmaFinite (KPCubicHaar.multiplicativeHaar K dx) := by
  classical
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  letI : SigmaCompactSpace K := by
    apply SigmaCompactSpace_iff_exists_compact_covering.mpr
    refine ⟨fun n => {x | ValuativeRel.valuation K x ≤ e.symm (WithZero.exp (n : ℤ))},
      fun n => IsNonarchimedeanLocalField.isCompact_closedBall K _, ?_⟩
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x = 0
    · subst x; simp
    have hv : e (ValuativeRel.valuation K x) ≠ 0 := by simpa [e] using hx
    let l := WithZero.log (e (ValuativeRel.valuation K x))
    refine Set.mem_iUnion.mpr ⟨l.toNat, ?_⟩
    change ValuativeRel.valuation K x ≤ e.symm (WithZero.exp (l.toNat : ℤ))
    rw [← e.toOrderIso.le_iff_le]
    change e (ValuativeRel.valuation K x) ≤ e (e.symm (WithZero.exp (l.toNat : ℤ)))
    rw [e.apply_symm_apply, ← WithZero.exp_log hv, WithZero.exp_le_exp]
    change l ≤ (l.toNat : ℤ)
    omega
  letI : T2Space K := CubicUnitCharacters.t2Space_of_isValuativeTopology K
  letI : BorelSpace Kˣ := ⟨by
    change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
    rw [(Units.isEmbedding_val₀ (G₀ := K)).eq_induced, borel_comap]
    congr 1
    exact BorelSpace.measurable_eq⟩
  have hf : MeasurableEmbedding (fun x : Kˣ => (x : K)) :=
    IsOpenUnits.isOpenEmbedding_unitsVal.measurableEmbedding
  unfold KPCubicHaar.multiplicativeHaar
  apply SigmaFinite.of_map _ hf.measurable.aemeasurable
  rw [hf.map_comap]
  infer_instance

end DedekindZetaZeroFree.KPJointRegulator.MellinBetaIntegrability

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPJointRegulator.MellinBetaIntegrability

open MeasureTheory

theorem mellin_integrable
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
    (dx : Measure K) [dx.IsAddHaarMeasure]
    (φ : K → ℂ) (hφlc : IsLocallyConstant φ) (hφcs : HasCompactSupport φ)
    (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun x : Kˣ => φ (x : K) *
      Complex.exp (s * (Real.log (KPCubicHaar.abs K (x : K)) : ℂ)))
      (KPCubicHaar.multiplicativeHaar K dx) := by
  classical
  letI : T2Space K := CubicUnitCharacters.t2Space_of_isValuativeTopology K
  letI : BorelSpace Kˣ := ⟨by
    change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
    rw [(Units.isEmbedding_val₀ (G₀ := K)).eq_induced, borel_comap]
    congr 1
    exact BorelSpace.measurable_eq⟩
  let A := KPCubicHaar.abs K
  let q : ℝ := KPCubicUnitIndices.residueCard K
  let ν := KPCubicHaar.multiplicativeHaar K dx
  let f : Kˣ → ℂ := fun x => φ (x : K) * Complex.exp (s * (Real.log (A (x : K)) : ℂ))
  have hq : 1 < q := by
    have hh : 1 < KPCubicUnitIndices.residueCard K := lt_of_lt_of_le (by decide : 1 < 2) (KPCubicUnitIndices.two_le_residueCard K)
    dsimp [q]
    exact_mod_cast hh
  have hqc : 0 < q := zero_lt_one.trans hq
  have hA : Measurable A := KPRamifiedBetaConductorSeries.normalizedAbs_measurable K
  have he : MeasurableEmbedding (fun x : Kˣ => (x : K)) := by
    apply Units.isEmbedding_val₀.measurableEmbedding
    have hr : Set.range (fun x : Kˣ => (x : K)) = {0}ᶜ := by
      ext x
      simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
    rw [hr]
    exact (measurableSet_singleton 0).compl
  obtain ⟨B, hB⟩ := hφlc.continuous.bounded_above_of_compact_support hφcs
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  open scoped WithZeroTopology in
    obtain ⟨γ, hγ⟩ := hφcs.bddAbove_image
      (IsValuativeTopology.continuous_valuation (R := K)).continuousOn
  let M : ℤ := WithZero.log (e (max γ 1))
  have hmax : e (max γ 1) ≠ 0 := by
    have hh : (0 : ValuativeRel.ValueGroupWithZero K) < max γ 1 :=
      lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    simpa using (e.toOrderIso.strictMono hh).ne'
  let shell : ℕ → Set Kˣ := fun n => {x | A (x : K) = q ^ (M - (n : ℤ))}
  have hm (n : ℕ) : MeasurableSet (shell n) :=
    (hA.comp he.measurable) (measurableSet_singleton _)
  have hO : dx ((ValuativeRel.valuation K).integer : Set K) ≠ ⊤ :=
    (IsNonarchimedeanLocalField.isCompact_closedBall K 1).measure_lt_top.ne
  have hmass (n : ℕ) : ν (shell n) ≤ dx ((ValuativeRel.valuation K).integer : Set K) := by
    dsimp [ν, KPCubicHaar.multiplicativeHaar]
    rw [Measure.comap_apply _ he.injective (fun t ht => he.measurableSet_image.mpr ht) _ (hm n)]
    apply le_trans (measure_mono ?_) (KPRamifiedBetaConductorSeries.multiplicative_shell_mass_le K dx (M - (n : ℤ)))
    rintro x ⟨u, hu, rfl⟩
    exact hu
  have hfinite (n : ℕ) : ν (shell n) ≠ ⊤ := ne_top_of_le_ne_top hO (hmass n)
  let w : ℕ → ℂ := fun n => Complex.exp (s * (Real.log (q ^ (M - (n : ℤ)))) )
  have hi (n : ℕ) : IntegrableOn f (shell n) ν := by
    have hc : IntegrableOn (fun _ : Kˣ => w n) (shell n) ν := integrableOn_const (hfinite n)
    have hd : IntegrableOn (fun x : Kˣ => φ (x : K) * w n) (shell n) ν := hc.bdd_mul (hφlc.continuous.comp Units.continuous_val).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x : Kˣ => hB (x : K)))
    exact hd.congr_fun (fun x hx => by simp only [f, shell, Set.mem_setOf_eq] at *; rw [hx]) (hm n)
  let r := Real.exp (-s.re * Real.log q)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hs) (Real.log_pos hq))
  have hw (n : ℕ) : ‖w n‖ = Real.exp (s.re * ((M : ℝ) * Real.log q)) * r ^ n := by
    rw [Complex.norm_exp]
    simp only [w, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Real.log_zpow, Int.cast_sub, Int.cast_natCast]
    rw [show s.re * (((M : ℝ) - (n : ℝ)) * Real.log q) =
      s.re * ((M : ℝ) * Real.log q) + (n : ℝ) * (-s.re * Real.log q) by ring,
      Real.exp_add, Real.exp_nat_mul]
  have hb (n : ℕ) : (∫ x in shell n, ‖f x‖ ∂ν) ≤
      (B * Real.exp (s.re * ((M : ℝ) * Real.log q)) * dx.real ((ValuativeRel.valuation K).integer : Set K)) * r ^ n := by
    have hk : ∀ x ∈ shell n, ‖f x‖ ≤ B * ‖w n‖ := by
      intro x hx
      have hf : f x = φ (x : K) * w n := by dsimp [f, w]; rw [show A (x : K) = _ from hx]
      rw [hf, norm_mul]
      exact mul_le_mul_of_nonneg_right (hB (x : K)) (norm_nonneg _)
    calc
      _ ≤ ∫ _ in shell n, B * ‖w n‖ ∂ν :=
        setIntegral_mono_on (hi n).norm (integrableOn_const (hfinite n)) (hm n) hk
      _ = (B * ‖w n‖) * ν.real (shell n) := by simp [mul_comm]
      _ ≤ (B * ‖w n‖) * dx.real ((ValuativeRel.valuation K).integer : Set K) :=
        mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hO (hmass n)) (mul_nonneg (le_trans (norm_nonneg (φ 0)) (hB 0)) (norm_nonneg _))
      _ = _ := by rw [hw]; ring
  have hint : IntegrableOn f (⋃ n, shell n) ν :=
    integrableOn_iUnion_of_summable_integral_norm hi
      (Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _)) hb
        ((summable_geometric_of_lt_one hr0 hr1).mul_left _))
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hint
  intro x hx
  have hxφ : (x : K) ∈ tsupport φ := subset_tsupport φ (by
    intro hh
    exact hx (by simp [f, hh]))
  let k : ℤ := WithZero.log (e (ValuativeRel.valuation K (x : K)))
  have hek : e (ValuativeRel.valuation K (x : K)) ≠ 0 := by
    simpa [e] using (Valuation.ne_zero_iff _).mpr x.ne_zero
  have hk : k ≤ M := (WithZero.log_le_log hek hmax).mpr
    (e.toOrderIso.monotone ((hγ ⟨(x : K), hxφ, rfl⟩).trans (le_max_left _ _)))
  refine Set.mem_iUnion.mpr ⟨(M - k).toNat, ?_⟩
  have hnk : M - (((M - k).toNat : ℕ) : ℤ) = k := by rw [Int.toNat_of_nonneg (sub_nonneg.mpr hk)]; omega
  change A (x : K) = q ^ (M - (((M - k).toNat : ℕ) : ℤ))
  rw [hnk]
  simp only [A, KPCubicHaar.abs, if_neg x.ne_zero]
  rfl

end DedekindZetaZeroFree.KPJointRegulator.MellinBetaIntegrability

end

end

section

noncomputable section
open scoped Classical

namespace DedekindZetaZeroFree.KPJointRegulator.MellinBetaIntegrability

open MeasureTheory
open scoped Topology ValuativeRel

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem exists_uniformizer_units :
    ∃ π : Kˣ, ValuativeRel.valuation K (π : K) = ValuativeRel.uniformizer K := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective
    (K := K) (ValuativeRel.uniformizer K)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact (ValuativeRel.uniformizer_ne_zero (R := K)) hx.symm
  exact ⟨Units.mk0 x hx0, by simpa using hx⟩

theorem abs_eq_rpow_valuationExponent (y : Kˣ) :
    KPCubicHaar.abs K (y : K) =
      (KPCubicUnitIndices.residueCard K : ℝ) ^ (-KPCubicExpansion.valuationExponent K y) := by
  rw [KPCubicHaar.abs, if_neg (Units.ne_zero y)]
  congr 1
  simp only [KPCubicExpansion.valuationExponent, neg_neg]

end DedekindZetaZeroFree.KPJointRegulator.MellinBetaIntegrability

end

end

section

noncomputable section

namespace DedekindZetaZeroFree
namespace KPJointRegulator

open MeasureTheory

def cone (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (t : ℂˣ) (s : ℂ) : Prop :=
  0 < s.re ∧ s.re < 1 ∧
    (KPCubicUnitIndices.residueCard K : ℝ).rpow (-3 * s.re) < ‖(t : ℂ)‖ ∧
    ‖(t : ℂ)‖ < 1

def mellinIntegrand (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (φ : K → ℂ) (s : ℂ) (x : Kˣ) : ℂ :=
  φ (x : K) * Complex.exp (s * (Real.log (KPCubicHaar.abs K (x : K)) : ℂ))

end KPJointRegulator

open MeasureTheory KPJointRegulator

namespace KPJointRegulator
open MeasureTheory
variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

lemma abs_pos (x : K) (hx : x ≠ 0) : 0 < KPCubicHaar.abs K x := by
  have hq : 0 < (KPCubicUnitIndices.residueCard K : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2)
      (KPCubicUnitIndices.two_le_residueCard K))
  simp only [KPCubicHaar.abs, if_neg hx]
  exact zpow_pos hq _

lemma abs_continuousAt (x : K) (hx : x ≠ 0) : ContinuousAt (KPCubicHaar.abs K) x := by
  have hv := (ValuativeRel.valuation K).locally_const
    ((Valuation.ne_zero_iff (ValuativeRel.valuation K)).mpr hx)
  apply Filter.EventuallyEq.continuousAt (y := KPCubicHaar.abs K x)
  filter_upwards [hv] with y hy
  have hy0 : y ≠ 0 := by
    intro hy0
    have : ValuativeRel.valuation K x = 0 := by simpa [hy0] using hy.symm
    exact hx ((Valuation.zero_iff (ValuativeRel.valuation K)).mp this)
  simp only [KPCubicHaar.abs, if_neg hx, if_neg hy0, hy]

variable [MeasurableSpace K] [BorelSpace K]

open scoped Classical

lemma mellin_continuous (φ : K → ℂ) (hφ : IsLocallyConstant φ) (s : ℂ) :
    Continuous (mellinIntegrand K φ s) := by
  have hab : Continuous (fun x : Kˣ => KPCubicHaar.abs K (x : K)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (abs_continuousAt K _ (Units.ne_zero x)).comp Units.continuous_val.continuousAt
  unfold mellinIntegrand
  exact (hφ.continuous.comp Units.continuous_val).mul
    (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (hab.log (fun x =>
        ne_of_gt (abs_pos K _ (Units.ne_zero x)))))))

end KPJointRegulator

end DedekindZetaZeroFree

end

end
