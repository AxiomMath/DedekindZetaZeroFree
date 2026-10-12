module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.AllCuspSource
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.BelowThresholdResolvent
public import DedekindZetaZeroFree.Eisenstein.Continuation.SphericalL2ResolventFormula

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree

private lemma analyticAt_clm_apply' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : ℂ → E →L[ℂ] E} {B : ℂ → E} {x : ℂ}
    (hA : AnalyticAt ℂ A x) (hB : AnalyticAt ℂ B x) :
    AnalyticAt ℂ (fun z => A z (B z)) x :=
  (ContinuousLinearMap.analyticAt_bilinear (ContinuousLinearMap.id ℂ (E →L[ℂ] E))
    (A x, B x)).comp₂ hA hB

private lemma meromorphicAt_clm_apply' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : ℂ → E →L[ℂ] E} {B : ℂ → E} {x : ℂ}
    (hA : MeromorphicAt A x) (hB : AnalyticAt ℂ B x) :
    MeromorphicAt (fun z => A z (B z)) x := by
  obtain ⟨n, hn⟩ := hA
  refine ⟨n, (analyticAt_clm_apply' hn hB).congr ?_⟩
  filter_upwards with z
  simp [ContinuousLinearMap.smul_apply]

open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private lemma analyticAt_clear {A : ℂ → E} {x : ℂ} (hA : AnalyticAt ℂ A x) :
    AnalyticAt ℂ (fun s : ℂ => (s-x) • A s) x :=
  (show AnalyticAt ℂ (fun s : ℂ => s-x) x by fun_prop).smul hA

private lemma clear_zero (A : E) (x : ℂ) : (x-x) • A = 0 := by simp

private lemma analytic_cleared_source {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {G : ℂ → V →L[ℂ] V} {h : ℂ → V} {x : ℂ}
    (hG : AnalyticAt ℂ G x) (hh : AnalyticAt ℂ h x) :
    AnalyticAt ℂ (fun s => -(G s (h s))) x := (analyticAt_clm_apply' hG hh).neg

private lemma cleared_source_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (G A : V →L[ℂ] V) (u : V) (c : ℂ) (heq : c • A = G) :
    -(G u) = c • (-(A u)) := by rw [← heq]; simp

private lemma cleared_source_center {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (G P : V →L[ℂ] V) (u : V) (c : ℂ) (heq : G = -c • P) :
    -(G u) = c • P u := by rw [heq]; simp

private lemma cleared_source_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (G : V →L[ℂ] V) (u : V) (heq : G = 0) : -(G u) = 0 := by rw [heq]; simp

private lemma clear_simple {A : ℂ → E} {x : ℂ} {L : E}
    (hA : MeromorphicAt A x) (ho : (-1 : WithTop ℤ) ≤ meromorphicOrderAt A x)
    (hl : Tendsto (fun s => (s-x) • A s) (𝓝[≠] x) (𝓝 L)) :
    ∃ G : ℂ → E, AnalyticAt ℂ G x ∧
      (fun s => (s-x) • A s) =ᶠ[𝓝[≠] x] G ∧ G x = L := by
  have hm : MeromorphicAt (fun s => (s-x) • A s) x :=
    (show AnalyticAt ℂ (fun s => s-x) x by fun_prop).meromorphicAt.smul hA
  have hn : 0 ≤ meromorphicOrderAt (fun s => (s-x) • A s) x := by
    change 0 ≤ meromorphicOrderAt ((fun s => s-x) • A) x
    rw [meromorphicOrderAt_smul (show MeromorphicAt (fun s => s-x) x from
      (show AnalyticAt ℂ (fun s => s-x) x by fun_prop).meromorphicAt) hA]
    simp only [meromorphicOrderAt_id_sub_const]
    calc
      0 = (1 : WithTop ℤ) + (-1) := by norm_num
      _ ≤ 1 + meromorphicOrderAt A x := add_le_add_right ho _
  obtain ⟨G, hG, heq⟩ := hm.meromorphicOrderAt_nonneg_iff.mp hn
  refine ⟨G, hG, heq, ?_⟩
  exact tendsto_nhds_unique (hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hl.congr' heq)

private lemma pull_limit {A : ℂ → E} {a : ℂ → ℂ} {x : ℂ} {L : E}
    (ha : HasDerivAt a (deriv a x) x) (hne : deriv a x ≠ 0)
    (hinj : ∀ᶠ s in 𝓝 x, a s = a x → s = x)
    (hl : Tendsto (fun z => (z-a x) • A z) (𝓝[≠] (a x)) (𝓝 L)) :
    Tendsto (fun s => (s-x) • A (a s)) (𝓝[≠] x) (𝓝 ((deriv a x)⁻¹ • L)) := by
  have hat : Tendsto a (𝓝[≠] x) (𝓝[≠] (a x)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [hinj.filter_mono nhdsWithin_le_nhds,
        eventually_mem_nhdsWithin] with s hs hsx
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (fun h => hsx (hs h))
  have ht := (ha.tendsto_slope.inv₀ hne).smul (hl.comp hat)
  apply ht.congr'
  filter_upwards [eventually_mem_nhdsWithin, hat.eventually eventually_mem_nhdsWithin] with s hs hsa
  have hs' : s-x ≠ 0 := sub_ne_zero.mpr hs
  have hsa' : a s-a x ≠ 0 := sub_ne_zero.mpr hsa
  change ((s-x)⁻¹ * (a s-a x))⁻¹ • ((a s-a x) • A (a s)) = (s-x) • A (a s)
  rw [← mul_smul]
  congr 1
  field_simp

private lemma exists_ball_inter_subset_singleton {α : Type*} [MetricSpace α]
    {S : Set α} {z : α} {r : ℝ} (hr : 0 < r)
    (hfin : (S ∩ Metric.closedBall z r).Finite) (hz : z ∈ S) :
    ∃ r' : ℝ, 0 < r' ∧ S ∩ Metric.ball z r' ⊆ {z} := by
  by_cases hempty : (S ∩ Metric.closedBall z r) \ {z} = ∅
  · have hsub : S ∩ Metric.closedBall z r ⊆ {z} := by
      intro w hw
      by_contra hwz
      have hmem : w ∈ (S ∩ Metric.closedBall z r) \ {z} :=
        ⟨hw, by simpa [Set.mem_singleton_iff] using hwz⟩
      rw [hempty] at hmem
      exact hmem
    refine ⟨r / 2, by linarith, ?_⟩
    intro w hw
    obtain ⟨hwS, hwb⟩ := hw
    have hd : dist w z < r / 2 := Metric.mem_ball.mp hwb
    exact hsub ⟨hwS, Metric.mem_closedBall.mpr (by linarith)⟩
  · have hne : ((S ∩ Metric.closedBall z r) \ {z}).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨a, ha, hmin⟩ := Set.exists_min_image ((S ∩ Metric.closedBall z r) \ {z})
      (fun w => dist w z) (hfin.subset Set.sdiff_subset) hne
    have haz : a ≠ z := by
      intro h; exact ha.2 (by simpa [Set.mem_singleton_iff, h] using rfl)
    have hpos : 0 < dist a z := dist_pos.mpr haz
    refine ⟨min (dist a z) r / 2, by positivity, ?_⟩
    intro w hw
    by_contra hwz
    obtain ⟨hwS, hwb⟩ := hw
    have hd : dist w z < min (dist a z) r / 2 := Metric.mem_ball.mp hwb
    have hwa : w ∈ (S ∩ Metric.closedBall z r) \ {z} :=
      ⟨⟨hwS, Metric.mem_closedBall.mpr (by linarith [min_le_right (dist a z) r])⟩,
        by simpa [Set.mem_singleton_iff] using hwz⟩
    have := hmin w hwa
    linarith [hd, this, min_le_left (dist a z) r]

private lemma exists_ball_disjoint_of_finite {α : Type*} [MetricSpace α]
    {S : Set α} {z : α} (hfin : S.Finite) (hz : z ∉ S) :
    ∃ r : ℝ, 0 < r ∧ S ∩ Metric.ball z r = ∅ := by
  by_cases hempty : S = ∅
  · exact ⟨1, one_pos, by rw [hempty]; simp⟩
  · obtain ⟨a, ha, hmin⟩ := Set.exists_min_image S (fun w => dist w z) hfin
      (Set.nonempty_iff_ne_empty.mpr hempty)
    have haz : a ≠ z := fun h => hz (h ▸ ha)
    have hpos : 0 < dist a z := dist_pos.mpr haz
    refine ⟨dist a z / 2, by linarith, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro w hw
    obtain ⟨hwS, hwb⟩ := hw
    have hd : dist w z < dist a z / 2 := Metric.mem_ball.mp hwb
    have := hmin w hwS
    linarith [hd, this]

end DedekindZetaZeroFree

namespace DedekindZetaZeroFree.KPContActualHilbertSimpleGerms

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "Hactual" => KPContActualAllCuspSource.Sector F ζ hζ C R P H U
local notation "d" => (Module.finrank ℚ F / 2 : ℕ)
local notation "a" => KPContinuation.spectralCoordinate (d : ℤ)

variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)

local notation "Bactual" => KPContActualSectorFriedrichsSynthesis.B_U
  F ζ hζ level R P H μG hμG hR realization
local notation "Δactual" => KPContActualSectorFriedrichsSynthesis.Δ_U
  F ζ hζ level R P H μG hμG hR realization

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
variable (Ω : Set ℂ) (f : ℂ → S)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)

def v (s : ℂ) : Hactual :=
  -(KPResolventPencil.shiftedResolvent Bactual (a s) (source.h s))

def Sigma : Set ℂ :=
  {s ∈ Ω | a s ∈ KPBelowThresholdResolvent.poleSet Δactual (d : ℝ)}

local notation "vactual" => v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source
local notation "Σactual" => Sigma F ζ hζ C R P H U μG hμG hR realization Ω

structure Properties : Prop where

  poles_locally_finite : ∀ s₀ ∈ Ω, ∃ r : ℝ, 0 < r ∧
    Metric.ball s₀ r ⊆ Ω ∧ (Σactual ∩ Metric.closedBall s₀ r).Finite
  hilbert_meromorphic : MeromorphicOn vactual Ω

  simple_germs : ∀ s₀ ∈ Ω, ∃ r : ℝ, 0 < r ∧
    Metric.ball s₀ r ⊆ Ω ∧ Metric.ball s₀ r ∩ Σactual ⊆ {s₀} ∧
    ∃ w : ℂ → Hactual, DifferentiableOn ℂ w (Metric.ball s₀ r) ∧
      (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → w s = (s - s₀) • vactual s) ∧
      (s₀ ∈ Σactual → ∀ μ : ℝ, a s₀ = (μ : ℂ) →
        w s₀ = (deriv a s₀)⁻¹ • KPBelowThresholdResolvent.poleProjection Bactual μ (source.h s₀)) ∧
      (s₀ ∉ Σactual → w s₀ = 0)

  cleared_hilbert_germs : ∀ s₀ ∈ Ω, KPSphericalL2Formula.ClearedHilbertGerm vactual Ω s₀

  cleared_at_zero : 0 ∈ Ω → KPSphericalL2Formula.ClearedHilbertGerm vactual Ω 0

  domain_equation : ∀ s ∈ Ω \ Σactual, ∃ hv : vactual s ∈ (Δactual).domain,
    Δactual ⟨vactual s, hv⟩ - a s • vactual s = -(source.h s)

set_option synthInstance.maxSize 256 in
private theorem aux
    (hι : Function.Injective ι)
    (hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (hΩopen : IsOpen Ω) (hΩ : Ω ⊆ KPContinuation.spectralDomain)
    (hf : DifferentiableOn ℂ f Ω) :
    Properties F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source := by
  classical
  haveI : NumberField.IsTotallyComplex F :=
    NumberField.nrRealPlaces_eq_zero_iff.mp H.totallyComplex
  have hfin : Module.finrank ℚ F = 2 * NumberField.InfinitePlace.nrComplexPlaces F :=
    NumberField.IsTotallyComplex.finrank F
  have hnat : (Module.finrank ℚ F / 2 : ℕ) = NumberField.InfinitePlace.nrComplexPlaces F := by
    rw [hfin]; omega
  have hdcast : (d : ℝ) = (Module.finrank ℚ F : ℝ) / 2 := by
    have h1 : d = NumberField.InfinitePlace.nrComplexPlaces F := hnat
    rw [h1, hfin]; push_cast; ring
  have hdZ : (0 : ℤ) < (d : ℤ) := by
    have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
    have : (0 : ℕ) < d := by
      rw [show d = NumberField.InfinitePlace.nrComplexPlaces F from hnat]
      omega
    exact_mod_cast this

  have ha_inj : Set.InjOn a KPContinuation.spectralDomain := by
    intro s hs s' hs' heq
    have hdne : (d : ℂ) ≠ 0 := by
      have hdR : (0 : ℝ) < (d : ℝ) := by
        rw [hdcast]
        have : (0 : ℝ) < (Module.finrank ℚ F : ℝ) := by
          exact_mod_cast Module.finrank_pos
        linarith
      have : ((d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hdR)
      simpa using this
    simp only [KPContinuation.spectralCoordinate] at heq
    have hu : ((1 : ℂ) / 3 + 2 * s) ^ 2 = ((1 : ℂ) / 3 + 2 * s') ^ 2 := by
      have h1 := mul_left_cancel₀ hdne heq
      linear_combination -h1
    have hprod : (((1 : ℂ) / 3 + 2 * s) - ((1 : ℂ) / 3 + 2 * s')) *
        (((1 : ℂ) / 3 + 2 * s) + ((1 : ℂ) / 3 + 2 * s')) = 0 := by
      linear_combination hu
    rcases mul_eq_zero.mp hprod with h | h
    · have h2 : 2 * s = 2 * s' := by linear_combination h
      exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h2
    · exfalso
      have hre := congrArg Complex.re h
      have hs2 : -(1 : ℝ) / 6 < s.re := hs
      have hs3 : -(1 : ℝ) / 6 < s'.re := hs'
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
      norm_num at hre
      linarith

  have hspec := kp_cont_actual_sector_resolvent_specialization
    F ζ hζ μG hμG level R hR P H realization
  let RR : ℂ → Hactual →L[ℂ] Hactual := KPResolventPencil.shiftedResolvent Bactual
  have ha_an (s : ℂ) : AnalyticAt ℂ a s := by
    unfold KPContinuation.spectralCoordinate
    fun_prop
  have ha_dom (s : ℂ) (hs : s ∈ Ω) :
      a s ∈ KPBelowThresholdResolvent.domain ((Module.finrank ℚ F : ℝ) / 2) := by
    have hh := KPContinuation.spectralCoordinate_avoids_thresholdRay (d : ℤ) hdZ
      (Set.mem_image_of_mem _ (hΩ hs))
    intro hp
    obtain ⟨μ, hμ, heq⟩ := hp
    apply hh
    have heq' : a s = (μ : ℂ) := heq.symm
    change (a s).im = 0 ∧ ((d : ℤ) : ℝ) ≤ (a s).re
    rw [heq']
    simpa only [Int.cast_natCast, Complex.ofReal_im, Complex.ofReal_re,
      hdcast, Set.mem_Ici, true_and] using hμ
  have hRa (s : ℂ) (hs : s ∈ Ω) : MeromorphicAt (fun s => RR (a s)) s :=
    (hspec.norm_meromorphic (a s) (ha_dom s hs)).comp_analyticAt (ha_an s)
  have hmero : MeromorphicOn vactual Ω := by
    intro s hs
    exact (meromorphicAt_clm_apply' (hRa s hs)
      (source.hilbert_holomorphic.analyticAt (hΩopen.mem_nhds hs))).neg
  have hop : ∀ s₀ ∈ Ω, ∃ G : ℂ → Hactual →L[ℂ] Hactual,
      AnalyticAt ℂ G s₀ ∧
      (fun s => (s-s₀) • RR (a s)) =ᶠ[𝓝[≠] s₀] G ∧
      (s₀ ∈ Σactual → ∀ μ : ℝ, a s₀ = (μ : ℂ) →
        G s₀ = -(deriv a s₀)⁻¹ • KPBelowThresholdResolvent.poleProjection Bactual μ) ∧
      (s₀ ∉ Σactual → G s₀ = 0) := by
    intro s₀ hs₀
    by_cases hp : s₀ ∈ Σactual
    · obtain ⟨_, μ, hμd, hμe, hμeq⟩ := hp
      have hpkeep : s₀ ∈ Σactual := ⟨hs₀, μ, hμd, hμe, hμeq⟩
      have hμd' : μ < (Module.finrank ℚ F : ℝ) / 2 := by simpa [hdcast] using hμd
      obtain ⟨_, _, _, _, _, _, _, hlim, _⟩ := hspec.full_orthogonal_laurent μ hμd' hμe
      have hμeq' : a s₀ = (μ : ℂ) := hμeq
      have hinj : ∀ᶠ s in 𝓝 s₀, a s = a s₀ → s = s₀ := by
        filter_upwards [hΩopen.mem_nhds hs₀] with s hs h
        exact ha_inj (hΩ hs) (hΩ hs₀) h
      have hlim' : Filter.Tendsto (fun s => (s-s₀) • RR (a s)) (𝓝[≠] s₀)
          (𝓝 ((deriv a s₀)⁻¹ • (-KPBelowThresholdResolvent.poleProjection Bactual μ))) := by
        apply pull_limit (A := RR) (L := -KPBelowThresholdResolvent.poleProjection Bactual μ) ((KPContinuation.spectralCoordinate_hasDerivAt (d : ℤ) s₀).differentiableAt.hasDerivAt)
          (KPContinuation.spectralCoordinate_deriv_ne_zero (d : ℤ) hdZ s₀ (hΩ hs₀)) hinj
        simpa only [hμeq', RR, KPContActualSectorResolventSpecialization.R_U] using hlim
      have ho : (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun s => RR (a s)) s₀ := by
        have he := (hspec.exact_simple_poles (a s₀) (ha_dom s₀ hs₀)).mp
          (by simpa only [hdcast] using (show a s₀ ∈ KPBelowThresholdResolvent.poleSet Δactual (d : ℝ) from hpkeep.2))
        rw [show (fun s => RR (a s)) = RR ∘ a from rfl,
          meromorphicOrderAt_comp_of_deriv_ne_zero (ha_an s₀)
          (KPContinuation.spectralCoordinate_deriv_ne_zero (d : ℤ) hdZ s₀ (hΩ hs₀))]
        exact le_of_eq he.symm
      obtain ⟨G, hG, heq, hval⟩ := clear_simple (hRa s₀ hs₀) ho hlim'
      refine ⟨G, hG, heq, ?_, fun hn => (hn hpkeep).elim⟩
      intro _ ν hν
      have : ν = μ := Complex.ofReal_injective (hν.symm.trans hμeq')
      subst ν
      simpa only [smul_neg, neg_smul] using hval
    · have hn : a s₀ ∈ KPBelowThresholdResolvent.domain ((Module.finrank ℚ F : ℝ) / 2) \
          KPBelowThresholdResolvent.poleSet Δactual ((Module.finrank ℚ F : ℝ) / 2) :=
        ⟨ha_dom s₀ hs₀, by simpa only [← hdcast, Sigma, Set.mem_setOf_eq, not_and,
          hs₀, true_implies] using hp⟩
      have hAn : AnalyticAt ℂ (fun s => RR (a s)) s₀ :=
        (hspec.norm_holomorphic_off_poles (a s₀) hn).comp (ha_an s₀)
      refine ⟨fun s => (s-s₀) • RR (a s), analyticAt_clear hAn,
        Filter.EventuallyEq.rfl, fun hp' => (hp hp').elim, ?_⟩
      intro _
      exact clear_zero (RR (a s₀)) s₀
  have hfinite : ∀ s₀ ∈ Ω, ∃ r : ℝ, 0 < r ∧
      Metric.ball s₀ r ⊆ Ω ∧ (Σactual ∩ Metric.closedBall s₀ r).Finite := by
    intro s₀ hs₀
    obtain ⟨ρ, hρ, hfin⟩ := hspec.poles_locally_finite (a s₀) (ha_dom s₀ hs₀)
    have hevent : ∀ᶠ s in 𝓝 s₀, s ∈ Ω ∧ a s ∈ Metric.ball (a s₀) ρ :=
      Filter.Eventually.and (hΩopen.mem_nhds hs₀) ((ha_an s₀).continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ))
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hevent
    refine ⟨r/2, by positivity, ?_, ?_⟩
    · intro s hs
      exact (hball (lt_trans (Metric.mem_ball.mp hs) (by linarith))).1
    · apply Set.Finite.of_finite_image (f := a)
      · apply hfin.subset
        rintro z ⟨s, hs, rfl⟩
        have hsnear : dist s s₀ < r := lt_of_le_of_lt (Metric.mem_closedBall.mp hs.2) (by linarith)
        exact ⟨by simpa only [hdcast] using hs.1.2,
          Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp (hball hsnear).2))⟩
      · intro s hs t ht heq
        exact ha_inj (hΩ hs.1.1) (hΩ ht.1.1) heq
  have hisolate : ∀ s₀ ∈ Ω, ∃ r : ℝ, 0 < r ∧ Metric.ball s₀ r ⊆ Ω ∧
      Metric.ball s₀ r ∩ Σactual ⊆ {s₀} := by
    intro s₀ hs₀
    obtain ⟨r, hr, hrΩ, hfin⟩ := hfinite s₀ hs₀
    by_cases hp : s₀ ∈ Σactual
    · obtain ⟨r', hr', hiso⟩ := exists_ball_inter_subset_singleton hr hfin hp
      refine ⟨min r r', lt_min hr hr', (Metric.ball_subset_ball (min_le_left _ _)).trans hrΩ, ?_⟩
      intro s hs
      exact hiso ⟨hs.2, Metric.ball_subset_ball (min_le_right _ _) hs.1⟩
    · obtain ⟨r', hr', hiso⟩ := exists_ball_disjoint_of_finite hfin (by intro h; exact hp h.1)
      refine ⟨min r r', lt_min hr hr', (Metric.ball_subset_ball (min_le_left _ _)).trans hrΩ, ?_⟩
      intro s hs
      have hem : s ∈ (Σactual ∩ Metric.closedBall s₀ r) ∩ Metric.ball s₀ r' :=
        ⟨⟨hs.2, Metric.mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le (Metric.mem_ball.mp hs.1) (min_le_left _ _)))⟩,
          Metric.ball_subset_ball (min_le_right _ _) hs.1⟩
      rw [hiso] at hem
      exact hem.elim
  have hgerms : ∀ s₀ ∈ Ω, ∃ r : ℝ, 0 < r ∧
      Metric.ball s₀ r ⊆ Ω ∧ Metric.ball s₀ r ∩ Σactual ⊆ {s₀} ∧
      ∃ w : ℂ → Hactual, DifferentiableOn ℂ w (Metric.ball s₀ r) ∧
        (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → w s = (s - s₀) • vactual s) ∧
        (s₀ ∈ Σactual → ∀ μ : ℝ, a s₀ = (μ : ℂ) →
          w s₀ = (deriv a s₀)⁻¹ • KPBelowThresholdResolvent.poleProjection Bactual μ (source.h s₀)) ∧
        (s₀ ∉ Σactual → w s₀ = 0) := by
    intro s₀ hs₀
    obtain ⟨G, hG, heq, hcenter, hzero⟩ := hop s₀ hs₀
    let w : ℂ → Hactual := fun s => -(G s (source.h s))
    have hw : AnalyticAt ℂ w s₀ := analytic_cleared_source hG
      (source.hilbert_holomorphic.analyticAt (hΩopen.mem_nhds hs₀))
    have heq' : ∀ᶠ s in 𝓝 s₀, s ≠ s₀ → (s-s₀) • RR (a s) = G s :=
      eventually_nhdsWithin_iff.mp heq
    obtain ⟨ρ, hρ, hρprop⟩ := Metric.eventually_nhds_iff.mp (hw.eventually_analyticAt.and heq')
    obtain ⟨r, hr, hrΩ, hiso⟩ := hisolate s₀ hs₀
    refine ⟨min r ρ, lt_min hr hρ, (Metric.ball_subset_ball (min_le_left _ _)).trans hrΩ,
      ?_, w, ?_, ?_, ?_, ?_⟩
    · intro s hs
      exact hiso ⟨Metric.ball_subset_ball (min_le_left _ _) hs.1, hs.2⟩
    · intro s hs
      exact (hρprop (lt_of_lt_of_le (Metric.mem_ball.mp hs) (min_le_right _ _))).1.differentiableAt.differentiableWithinAt
    · intro s hs hne
      exact cleared_source_eq (G s) (RR (a s)) (source.h s) (s-s₀)
        ((hρprop (lt_of_lt_of_le (Metric.mem_ball.mp hs) (min_le_right _ _))).2 hne)
    · intro hp μ hμ
      exact cleared_source_center (G s₀) (KPBelowThresholdResolvent.poleProjection Bactual μ)
        (source.h s₀) (deriv a s₀)⁻¹ (hcenter hp μ hμ)
    · intro hp
      exact cleared_source_zero (G s₀) (source.h s₀) (hzero hp)
  have hcleared : ∀ s₀ ∈ Ω, KPSphericalL2Formula.ClearedHilbertGerm vactual Ω s₀ := by
    intro s₀ hs₀
    obtain ⟨r, hr, hrΩ, _, w, hw, heq, _, _⟩ := hgerms s₀ hs₀
    exact ⟨r, hr, hrΩ, w, hw, heq⟩
  refine ⟨hfinite, hmero, hgerms, hcleared, hcleared 0, ?_⟩
  intro s hs
  have hz : a s ∈ KPBelowThresholdResolvent.domain ((Module.finrank ℚ F : ℝ) / 2) \
      KPBelowThresholdResolvent.poleSet Δactual ((Module.finrank ℚ F : ℝ) / 2) :=
    ⟨ha_dom s hs.1, by
      intro hp
      apply hs.2
      exact ⟨hs.1, by simpa only [hdcast] using hp⟩⟩
  obtain ⟨hInv, _, _⟩ := hspec.genuine_inverse_off_poles (a s) hz
  obtain ⟨hRange, hEq, _⟩ := hInv
  have hv : vactual s ∈ (Δactual).domain := (Δactual).domain.neg_mem (hRange (source.h s))
  refine ⟨hv, ?_⟩
  have heq := hEq (source.h s)
  change Δactual ⟨-(RR (a s) (source.h s)), hv⟩ - a s • (-(RR (a s) (source.h s))) = -(source.h s)
  have hneg : (⟨-(RR (a s) (source.h s)), hv⟩ : (Δactual).domain) =
      -⟨RR (a s) (source.h s), hRange (source.h s)⟩ := rfl
  rw [hneg]
  rw [LinearPMap.map_neg, smul_neg]
  simpa only [neg_sub, neg_sub_neg, RR, KPContActualSectorResolventSpecialization.R_U] using congrArg Neg.neg heq

end DedekindZetaZeroFree.KPContActualHilbertSimpleGerms

namespace DedekindZetaZeroFree

theorem kp_cont_actual_hilbert_simple_germs
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (_hι : Function.Injective ι)
    (_hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (Ω : Set ℂ) (_hΩopen : IsOpen Ω) (_hΩ : Ω ⊆ KPContinuation.spectralDomain)
    (f : ℂ → S) (_hf : DifferentiableOn ℂ f Ω)
    {T : ℝ}
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ) :
    KPContActualHilbertSimpleGerms.Properties
      F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source := by
  exact KPContActualHilbertSimpleGerms.aux F ζ hζ C R P H U μG hμG hR realization
    ι buffer Ω f χ source _hι _hStage _hΩopen _hΩ _hf
end DedekindZetaZeroFree

end
