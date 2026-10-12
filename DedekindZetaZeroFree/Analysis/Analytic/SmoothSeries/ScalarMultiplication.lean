module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothSections.CompactJetHolomorphy
public import DedekindZetaZeroFree.Theta.Periods.MeromorphicContinuationAndResidues

@[expose] public section

section

noncomputable section
open scoped Classical Topology BigOperators
set_option backward.isDefEq.respectTransparency false

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.SmoothSeriesAlgebra

open KPGlobalEisensteinData

variable {G V J : Type*} [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
variable (D : J → V →ₗ[ℂ] C(G, ℂ))

theorem powerSeries_mono {z : ℂ} {r R : ℝ} {a : ℕ → V} {f : ℂ → V}
    (hf : SmoothPowerSeriesOn D z R a f) (hr : r ≤ R) :
    SmoothPowerSeriesOn D z r a f := by
  intro i t ht htr ε hε
  exact hf i t ht (htr.trans_le hr) ε hε

theorem powerSeries_add {z : ℂ} {r : ℝ} {a b : ℕ → V} {f g : ℂ → V}
    (hf : SmoothPowerSeriesOn D z r a f) (hg : SmoothPowerSeriesOn D z r b g) :
    SmoothPowerSeriesOn D z r (fun n => a n + b n) (fun s => f s + g s) := by
  intro i t ht htr ε hε
  obtain ⟨N, hN⟩ := hf i t ht htr (ε / 2) (by positivity)
  obtain ⟨L, hL⟩ := hg i t ht htr (ε / 2) (by positivity)
  refine ⟨max N L, ?_⟩
  intro M hM s hs
  have heq : (∑ n ∈ Finset.range M, (s-z)^n • (a n + b n)) - (f s + g s) =
      ((∑ n ∈ Finset.range M, (s-z)^n • a n) - f s) +
      ((∑ n ∈ Finset.range M, (s-z)^n • b n) - g s) := by
    simp only [smul_add, Finset.sum_add_distrib]
    abel
  rw [heq]
  exact lt_of_le_of_lt (map_add_le_add (smoothSeminorm D i) _ _)
    (by linarith [hN M ((le_max_left N L).trans hM) s hs,
      hL M ((le_max_right N L).trans hM) s hs])

theorem holomorphic_add {O : Set ℂ} {f g : ℂ → V}
    (hf : SmoothHolomorphicOn D f O) (hg : SmoothHolomorphicOn D g O) :
    SmoothHolomorphicOn D (fun s => f s + g s) O := by
  intro z hz
  obtain ⟨r, hr, hO, a, ha⟩ := hf z hz
  obtain ⟨t, ht, _, b, hb⟩ := hg z hz
  refine ⟨min r t, lt_min hr ht,
    (Metric.ball_subset_ball (min_le_left r t)).trans hO,
    (fun n => a n + b n), ?_⟩
  exact powerSeries_add D (powerSeries_mono D ha (min_le_left r t))
    (powerSeries_mono D hb (min_le_right r t))

theorem holomorphic_sum {ι : Type*} (S : Finset ι) {O : Set ℂ}
    (hO : IsOpen O) (f : ι → ℂ → V) (hf : ∀ j ∈ S, SmoothHolomorphicOn D (f j) O) :
    SmoothHolomorphicOn D (fun s => ∑ j ∈ S, f j s) O := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, LinearMap.zero_apply] using
      (FiniteStageAnalytic.holomorphic_into_smooth D (0 : ℂ →ₗ[ℂ] V)
        hO (differentiableOn_const (0 : ℂ)))
  | @insert j S hj ih =>
    simpa only [Finset.sum_insert hj] using holomorphic_add D
      (hf j (Finset.mem_insert_self j S))
      (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

theorem powerSeries_const_smul {z : ℂ} {r : ℝ} {a : ℕ → V} {f : ℂ → V}
    (c : ℂ) (hf : SmoothPowerSeriesOn D z r a f) :
    SmoothPowerSeriesOn D z r (fun n => c • a n) (fun s => c • f s) := by
  intro i t ht htr ε hε
  obtain ⟨N,hN⟩ := hf i t ht htr (ε / (‖c‖ + 1)) (by positivity)
  refine ⟨N, ?_⟩
  intro M hM s hs
  have heq : (∑ n ∈ Finset.range M, (s-z)^n • (c • a n)) - c • f s =
      c • ((∑ n ∈ Finset.range M, (s-z)^n • a n) - f s) := by
    simp only [smul_sub, Finset.smul_sum, smul_comm c]
  rw [heq, map_smul_eq_mul]
  have hb := (lt_div_iff₀ (by positivity : 0 < ‖c‖ + 1)).mp (hN M hM s hs)
  have hn : 0 ≤ (smoothSeminorm D i)
    ((∑ n ∈ Finset.range M, (s-z)^n • a n) - f s) := by positivity
  nlinarith

theorem holomorphic_const_smul {O : Set ℂ} {f : ℂ → V} (c : ℂ)
    (hf : SmoothHolomorphicOn D f O) : SmoothHolomorphicOn D (fun s => c • f s) O := by
  intro z hz
  obtain ⟨r,hr,hO,a,ha⟩ := hf z hz
  exact ⟨r,hr,hO,(fun n => c • a n),powerSeries_const_smul D c ha⟩

def addGerm {f g : ℂ → V} (hf : SimplePoleGerm D f) (hg : SimplePoleGerm D g) :
    SimplePoleGerm D (fun s => f s + g s) where
  radius := min hf.radius hg.radius
  radius_pos := lt_min hf.radius_pos hg.radius_pos
  cleared s := hf.cleared s + hg.cleared s
  holomorphic := by
    apply holomorphic_add D
    · intro z hz
      obtain ⟨r,hr,hO,a,ha⟩ := hf.holomorphic z
        ((Metric.ball_subset_ball (min_le_left hf.radius hg.radius)) hz)
      obtain ⟨t,ht,hB⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball z hz
      exact ⟨min r t,lt_min hr ht,
        (Metric.ball_subset_ball (min_le_right r t)).trans hB,a,
        powerSeries_mono D ha (min_le_left r t)⟩
    · intro z hz
      obtain ⟨r,hr,hO,a,ha⟩ := hg.holomorphic z
        ((Metric.ball_subset_ball (min_le_right hf.radius hg.radius)) hz)
      obtain ⟨t,ht,hB⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball z hz
      exact ⟨min r t,lt_min hr ht,
        (Metric.ball_subset_ball (min_le_right r t)).trans hB,a,
        powerSeries_mono D ha (min_le_left r t)⟩
  clears s hs hne := by
    rw [hf.clears s ((Metric.ball_subset_ball (min_le_left hf.radius hg.radius)) hs) hne,
      hg.clears s ((Metric.ball_subset_ball (min_le_right hf.radius hg.radius)) hs) hne,
      smul_add]

@[simp] theorem addGerm_residue {f g : ℂ → V}
    (hf : SimplePoleGerm D f) (hg : SimplePoleGerm D g) :
    residue (addGerm D hf hg) = residue hf + residue hg := rfl

def constSmulGerm {f : ℂ → V} (c : ℂ) (hf : SimplePoleGerm D f) :
    SimplePoleGerm D (fun s => c • f s) where
  radius := hf.radius
  radius_pos := hf.radius_pos
  cleared s := c • hf.cleared s
  holomorphic := holomorphic_const_smul D c hf.holomorphic
  clears s hs hn := by rw [hf.clears s hs hn, smul_comm]

@[simp] theorem constSmulGerm_residue {f : ℂ → V}
    (c : ℂ) (hf : SimplePoleGerm D f) :
    residue (constSmulGerm D c hf) = c • residue hf := rfl

end DedekindZetaZeroFree.KPGlobalResidualConstruction.SmoothSeriesAlgebra

end

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical Topology BigOperators NNReal
open Filter
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.AnalyticScalarMultiplication
open KPGlobalEisensteinData

variable {G V J : Type*} [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
variable (D : J → V →ₗ[ℂ] C(G, ℂ))

 def compactJet (i : DifferentialCompact G J) : V →ₗ[ℂ] C(i.compact, ℂ) where
  toFun v := (D i.operator v).restrict i.compact
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

 theorem compactJet_series (i : DifferentialCompact G J)
    {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {a : ℕ → V} {f : ℂ → V}
    (hf : SmoothPowerSeriesOn D z ρ a f) :
    letI : CompactSpace i.compact := isCompact_iff_compactSpace.mp i.isCompact
    HasFPowerSeriesOnBall (fun s => compactJet D i (f s))
      (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (compactJet D i (a n)))
      z (ENNReal.ofReal ρ) := by
  letI : CompactSpace i.compact := isCompact_iff_compactSpace.mp i.isCompact
  let T := compactJet D i
  let p : FormalMultilinearSeries ℂ ℂ C(i.compact, ℂ) :=
    fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (T (a n))
  have hlim (x : ℂ) (hx : ‖x‖ < ρ) :
      Tendsto (fun M => p.partialSum M x) atTop (𝓝 (T (f (z+x)))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N,hN⟩ := hf i ‖x‖ (norm_nonneg _) hx ε hε
    refine ⟨N, fun M hM => ?_⟩
    have hz : z+x ∈ Metric.closedBall z ‖x‖ := by simp [Metric.mem_closedBall, dist_eq_norm]
    have hn := hN M hM (z+x) hz
    have hn' : ‖T ((∑ n ∈ Finset.range M, x^n • a n) - f (z+x))‖ < ε := by
      convert hn using 1 <;> simp [T, compactJet, smoothSeminorm, derivativeRestriction]
    simpa [map_sub, map_sum, map_smul, p, FormalMultilinearSeries.partialSum,
      dist_eq_norm] using hn'
  have hr : ENNReal.ofReal ρ ≤ p.radius := by
    apply ENNReal.le_of_forall_pos_nnreal_lt
    intro r hr hrρ
    have hrρ' : (r : ℝ) < ρ := by simpa only [ENNReal.coe_lt_ofReal] using hrρ
    have ht := hlim (r : ℂ) (by simpa using hrρ')
    have hd := (ht.comp (tendsto_add_atTop_nat 1)).sub ht
    have hn : Tendsto (fun n => (r : ℂ)^n • T (a n)) atTop (𝓝 0) := by
      simpa [p, FormalMultilinearSeries.partialSum, Finset.sum_range_succ] using hd
    have hb : Tendsto (fun n => ‖p n‖ * (r : ℝ)^n) atTop (𝓝 0) := by
      simpa [p, norm_smul, Complex.norm_real, abs_of_nonneg r.coe_nonneg, mul_comm]
        using hn.norm
    exact p.le_radius_of_tendsto hb
  refine ⟨hr, ENNReal.ofReal_pos.mpr hρ, ?_⟩
  intro x hx
  have hx' : ‖x‖ < ρ := by simpa [Metric.eball_ofReal, Metric.mem_ball, dist_eq_norm] using hx
  have hs : Summable (fun n => p n (fun _ => x)) := p.summable (hx.trans_le hr)
  apply hs.hasSum_iff_tendsto_nat.mpr
  exact hlim x hx'

def coefficientConvolution {W : Type*} [AddCommGroup W] [Module ℂ W]
    (b : ℕ → ℂ) (a : ℕ → W) (n : ℕ) : W :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, b ij.1 • a ij.2

private theorem ring_product_series {R : Type*} [NormedCommRing R] [NormedAlgebra ℂ R]
    [CompleteSpace R] {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {p q : FormalMultilinearSeries ℂ ℂ R} {f g : ℂ → R}
    (hf : HasFPowerSeriesOnBall f p z (ENNReal.ofReal ρ))
    (hg : HasFPowerSeriesOnBall g q z (ENNReal.ofReal ρ)) :
    HasFPowerSeriesOnBall (fun s => f s * g s)
      (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
        (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, p.coeff ij.1 * q.coeff ij.2))
      z (ENNReal.ofReal ρ) := by
  let c : ℕ → R := fun n => ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, p.coeff ij.1 * q.coeff ij.2
  let P : FormalMultilinearSeries ℂ ℂ R :=
    fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (c n)
  have heq (x : ℂ) (n : ℕ) : x^n • c n =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        (x^ij.1 • p.coeff ij.1) * (x^ij.2 • q.coeff ij.2) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [smul_mul_smul_comm, ← pow_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hij]
  have hnorm (r : ℝ≥0) (hr : (r : ENNReal) < ENNReal.ofReal ρ) :
      Summable (fun n => ‖c n‖ * (r : ℝ)^n) := by
    have hp := p.summable_norm_apply (x := (r : ℂ)) (by
      simpa [Metric.mem_eball, edist_dist, dist_eq_norm,
        Complex.norm_real, abs_of_nonneg r.coe_nonneg, ENNReal.ofReal_coe_nnreal] using hr.trans_le hf.r_le)
    have hq := q.summable_norm_apply (x := (r : ℂ)) (by
      simpa [Metric.mem_eball, edist_dist, dist_eq_norm,
        Complex.norm_real, abs_of_nonneg r.coe_nonneg, ENNReal.ofReal_coe_nnreal] using hr.trans_le hg.r_le)
    have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hp hq
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, ← heq,
      norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg r.coe_nonneg, mul_comm] using h
  refine ⟨?_, ENNReal.ofReal_pos.mpr hρ, ?_⟩
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro r hr hrρ
    apply P.le_radius_of_summable
    simpa only [P, ContinuousMultilinearMap.norm_mkPiRing] using hnorm r hrρ
  · intro x hx
    have hp := p.summable_norm_apply (hx.trans_le hf.r_le)
    have hq := q.summable_norm_apply (hx.trans_le hg.r_le)
    have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hp hq
    have hs := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hp hq
    rw [(hf.hasSum hx).tsum_eq, (hg.hasSum hx).tsum_eq] at hs
    have hh := h.of_norm.hasSum
    rw [← hs] at hh
    simpa only [P, c, ContinuousMultilinearMap.mkPiRing_apply,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, ← heq] using hh

theorem powerSeries_smul {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {b : ℂ → ℂ}
    (hb : HasFPowerSeriesOnBall b p z (ENNReal.ofReal ρ))
    {a : ℕ → V} {f : ℂ → V} (hf : SmoothPowerSeriesOn D z ρ a f) :
    SmoothPowerSeriesOn D z ρ (coefficientConvolution p.coeff a) (fun s => b s • f s) := by
  intro i r hr hrρ ε hε
  letI : CompactSpace i.compact := isCompact_iff_compactSpace.mp i.isCompact
  let T := compactJet D i
  let S : ℂ →L[ℂ] C(i.compact, ℂ) :=
    (LinearMap.toSpanSingleton ℂ C(i.compact, ℂ) 1).toContinuousLinearMap
  have hS (x : ℂ) : S x = ContinuousMap.const i.compact x := by
    ext; simp [S]
  have hscalar := S.comp_hasFPowerSeriesOnBall hb
  have hvector := compactJet_series D i hρ hf
  have hprod := ring_product_series hρ hscalar hvector
  let R : NNReal := ⟨(r+ρ)/2, by positivity⟩
  have hR : (R : ENNReal) < ENNReal.ofReal ρ := by
    rw [ENNReal.coe_lt_ofReal]
    change (r+ρ)/2 < ρ
    linarith
  have hlim := hprod.tendstoUniformlyOn' hR
  rw [Metric.tendstoUniformlyOn_iff] at hlim
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim ε hε)
  refine ⟨N, fun M hM s hs => ?_⟩
  have hsR : s ∈ Metric.ball z (R : ℝ) := by
    apply Metric.mem_ball.mpr
    apply (Metric.mem_closedBall.mp hs).trans_lt
    change r < (r+ρ)/2
    linarith
  have hn := hN M hM s hsR
  have hc (n : ℕ) :
      (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        (S.compFormalMultilinearSeries p).coeff ij.1 *
          FormalMultilinearSeries.coeff
            (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (T (a n))) ij.2) =
      T (coefficientConvolution p.coeff a n) := by
    have hpc (k : ℕ) : (S.compFormalMultilinearSeries p).coeff k = S (p.coeff k) := rfl
    have hac (k : ℕ) : FormalMultilinearSeries.coeff
        (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (T (a n))) k = T (a k) := by
      simp only [FormalMultilinearSeries.coeff, ContinuousMultilinearMap.mkPiRing_apply,
        Pi.one_apply, Finset.prod_const_one, one_smul]
    unfold coefficientConvolution
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [hpc, hac, map_smul, hS]
    ext x
    rfl
  have heq : (∑ q ∈ Finset.range M, (s-z)^q • T (coefficientConvolution p.coeff a q)) -
      (S (b s) * T (f s)) =
      T ((∑ q ∈ Finset.range M, (s-z)^q • coefficientConvolution p.coeff a q) - b s • f s) := by
    simp only [map_sub, map_sum, map_smul]
    congr 1
    rw [hS]
    ext x
    rfl
  have hn' : ‖T ((∑ q ∈ Finset.range M, (s-z)^q • coefficientConvolution p.coeff a q) -
      b s • f s)‖ < ε := by
    have hn'' : ‖(∑ q ∈ Finset.range M, (s-z)^q • T (coefficientConvolution p.coeff a q)) -
        S (b s) * T (f s)‖ < ε := by
      change dist (S (b s) * T (f s))
        (FormalMultilinearSeries.partialSum (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
          (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            (S.compFormalMultilinearSeries p).coeff ij.1 *
            FormalMultilinearSeries.coeff
              (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (T (a n))) ij.2))
          M (s-z)) < ε at hn
      simpa only [FormalMultilinearSeries.partialSum, ContinuousMultilinearMap.mkPiRing_apply,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, hc,
        dist_eq_norm, norm_sub_rev] using hn
    rw [heq] at hn''
    exact hn''
  exact hn'

theorem holomorphic_smul {O : Set ℂ} (hO : IsOpen O) {b : ℂ → ℂ} {f : ℂ → V}
    (hb : AnalyticOnNhd ℂ b O) (hf : SmoothHolomorphicOn D f O) :
    SmoothHolomorphicOn D (fun s => b s • f s) O := by
  intro z hz
  obtain ⟨r,hr,hball,a,ha⟩ := hf z hz
  obtain ⟨t,ht,htO⟩ := Metric.isOpen_iff.mp hO z hz
  let ρ : ℝ := min r t / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ ≤ r := by dsimp [ρ]; linarith [min_le_left r t]
  have hρt : ρ < t := by dsimp [ρ]; linarith [min_le_right r t]
  have hclosed : Metric.closedBall z ρ ⊆ O := by
    intro s hs
    exact htO (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hs).trans_lt hρt))
  have hp := (hb.differentiableOn.mono hclosed).hasFPowerSeriesOnBall
    (R := ⟨ρ,hρ.le⟩) hρ
  have hp' : HasFPowerSeriesOnBall b (cauchyPowerSeries b z ρ) z (ENNReal.ofReal ρ) := by
    convert hp using 1
    · rfl
    · exact ENNReal.ofReal_coe_nnreal (p := (⟨ρ,hρ.le⟩ : NNReal))
  exact ⟨ρ,hρ,(Metric.ball_subset_ball hρr).trans hball,
    coefficientConvolution (cauchyPowerSeries b z ρ).coeff a,
    powerSeries_smul D hρ hp' (SmoothSeriesAlgebra.powerSeries_mono D ha hρr)⟩

def smulGerm {b : ℂ → ℂ} {f : ℂ → V} (germ : SimplePoleGerm D f)
    (hb : AnalyticOnNhd ℂ b (Metric.ball 0 germ.radius)) :
    SimplePoleGerm D (fun s => b s • f s) where
  radius := germ.radius
  radius_pos := germ.radius_pos
  cleared s := b s • germ.cleared s
  holomorphic := holomorphic_smul D Metric.isOpen_ball hb germ.holomorphic
  clears s hs hn := by rw [germ.clears s hs hn, smul_comm]

@[simp] theorem smulGerm_residue {b : ℂ → ℂ} {f : ℂ → V}
    (germ : SimplePoleGerm D f) (hb : AnalyticOnNhd ℂ b (Metric.ball 0 germ.radius)) :
    residue (smulGerm D germ hb) = b 0 • residue germ := rfl

end DedekindZetaZeroFree.KPGlobalResidualConstruction.AnalyticScalarMultiplication

end

end
