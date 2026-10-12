module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree

def closedGradientGraph
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) : Submodule ℂ (WithLp 2 (H × V)) :=
  D.closure.graph.comap (WithLp.linearEquiv 2 ℂ (H × V)).toLinearMap

abbrev ClosedGradientSpace
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) := ↥(closedGradientGraph D)

def closedGradientEmbedding
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) : ClosedGradientSpace D →L[ℂ] H :=
  (WithLp.fstL 2 ℂ H V).comp (closedGradientGraph D).subtypeL

def closedGradientCoordinate
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) : ClosedGradientSpace D →L[ℂ] V :=
  (WithLp.sndL 2 ℂ H V).comp (closedGradientGraph D).subtypeL

def closedGradientForm
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) (u v : D.closure.domain) : ℂ :=
  inner ℂ (D.closure u) (D.closure v)

def closedGradientEnergy
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) (u : D.closure.domain) : ℝ := ‖D.closure u‖ ^ 2

def closedGradientEnergyNorm
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) (u : D.closure.domain) : ℝ :=
  Real.sqrt (‖(u : H)‖ ^ 2 + closedGradientEnergy D u)

theorem closedGradientGraph_isClosed
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) (hclosable : D.IsClosable) :
    IsClosed (closedGradientGraph D : Set (WithLp 2 (H × V))) := by
  exact hclosable.closure_isClosed.preimage (WithLp.prod_continuous_ofLp 2 H V)

theorem closedGradientSpace_complete
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : H →ₗ.[ℂ] V) (hclosable : D.IsClosable) :
    CompleteSpace (ClosedGradientSpace D) := by
  exact (closedGradientGraph_isClosed D hclosable).completeSpace_coe

theorem closedGradientEmbedding_properties
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : H →ₗ.[ℂ] V) (hdense : Dense (D.domain : Set H))
    (hclosable : D.IsClosable) :
    ‖closedGradientEmbedding D‖ ≤ 1 ∧
      Function.Injective (closedGradientEmbedding D) ∧
      DenseRange (closedGradientEmbedding D) ∧
      Set.range (closedGradientEmbedding D) = (D.closure.domain : Set H) := by
  have hrange : Set.range (closedGradientEmbedding D) = (D.closure.domain : Set H) := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact D.closure.mem_domain_of_mem_graph w.property
    · intro hx
      refine ⟨⟨WithLp.toLp 2 (x, D.closure ⟨x, hx⟩), D.closure.mem_graph ⟨x, hx⟩⟩, rfl⟩
  refine ⟨ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => ?_), ?_, ?_, hrange⟩
  · change ‖(w.val).fst‖ ≤ 1 * ‖w.val‖
    simpa using WithLp.norm_fst_le H (w : WithLp 2 (H × V))
  · intro w z hwz
    apply Subtype.ext
    apply (WithLp.linearEquiv 2 ℂ (H × V)).injective
    apply Prod.ext hwz
    exact D.closure.mem_graph_snd_inj' w.property z.property hwz
  · change Dense (Set.range (closedGradientEmbedding D))
    rw [hrange]
    exact hdense.mono D.le_closure.1

theorem closedGradientSpace_inner
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) (w z : ClosedGradientSpace D) :
    inner ℂ w z =
      inner ℂ (closedGradientEmbedding D w) (closedGradientEmbedding D z) +
      inner ℂ (closedGradientCoordinate D w) (closedGradientCoordinate D z) := by
  exact WithLp.prod_inner_apply (w : WithLp 2 (H × V)) (z : WithLp 2 (H × V))

theorem closedGradientEnergyNorm_eq_graphNorm
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) (u : D.closure.domain) :
    closedGradientEnergyNorm D u = ‖WithLp.toLp 2 ((u : H), D.closure u)‖ := by
  exact (WithLp.prod_norm_eq_of_L2 (WithLp.toLp 2 ((u : H), D.closure u))).symm

theorem closedGradientForm_nonnegative_dense
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) (hdense : Dense (D.domain : Set H))
    (hclosable : D.IsClosable) :
    Dense (D.closure.domain : Set H) ∧
      ∀ u : D.closure.domain,
        0 ≤ closedGradientEnergy D u ∧
        closedGradientForm D u u = (closedGradientEnergy D u : ℂ) := by
  refine ⟨hdense.mono D.le_closure.1, fun u => ⟨sq_nonneg _, ?_⟩⟩
  simpa [closedGradientForm, closedGradientEnergy] using
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (D.closure u))

theorem closedGradientForm_closed
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : H →ₗ.[ℂ] V) (hclosable : D.IsClosable)
    (u : ℕ → D.closure.domain)
    (hcauchy : CauchySeq (fun n => WithLp.toLp 2 ((u n : H), D.closure (u n)))) :
    ∃ v : D.closure.domain,
      Filter.Tendsto (fun n => closedGradientEnergyNorm D (u n - v))
        Filter.atTop (nhds 0) := by
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hwmem : w ∈ closedGradientGraph D := by
    apply (closedGradientGraph_isClosed D hclosable).mem_of_tendsto hw
    exact Filter.Eventually.of_forall fun n => D.closure.mem_graph (u n)
  obtain ⟨v, hvH, hvV⟩ := D.closure.mem_graph_iff.mp hwmem
  have heq : WithLp.toLp 2 ((v : H), D.closure v) = w := by
    apply (WithLp.linearEquiv 2 ℂ (H × V)).injective
    exact Prod.ext hvH hvV
  refine ⟨v, ?_⟩
  have hn := (hw.sub_const w).norm
  simpa only [sub_self, norm_zero, ← heq, closedGradientEnergyNorm_eq_graphNorm,
    Submodule.coe_sub, LinearPMap.map_sub, ← WithLp.toLp_sub, Prod.mk_sub_mk] using hn

theorem closedGradientForm_core
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : H →ₗ.[ℂ] V) (hclosable : D.IsClosable) (u : D.closure.domain) :
    ∃ s : ℕ → D.domain,
      Filter.Tendsto (fun n => (s n : H)) Filter.atTop (nhds (u : H)) ∧
      Filter.Tendsto (fun n => D (s n)) Filter.atTop (nhds (D.closure u)) ∧
      Filter.Tendsto (fun n => ‖D (s n)‖ ^ 2) Filter.atTop
        (nhds (closedGradientEnergy D u)) := by
  have hu : ((u : H), D.closure u) ∈ closure (D.graph : Set (H × V)) := by
    change ((u : H), D.closure u) ∈ D.graph.topologicalClosure
    rw [hclosable.graph_closure_eq_closure_graph]
    exact D.closure.mem_graph u
  obtain ⟨a, ha, hlim⟩ := mem_closure_iff_seq_limit.mp hu
  choose s hs using fun n => (D.mem_graph_iff.mp (ha n))
  have hH : Filter.Tendsto (fun n => (s n : H)) Filter.atTop (nhds (u : H)) := by
    simpa only [Function.comp_def, funext (fun n => (hs n).1)] using ((continuous_fst.tendsto _).comp hlim)
  have hV : Filter.Tendsto (fun n => D (s n)) Filter.atTop (nhds (D.closure u)) := by
    simpa only [Function.comp_def, funext (fun n => (hs n).2)] using ((continuous_snd.tendsto _).comp hlim)
  exact ⟨s, hH, hV, hV.norm.pow 2⟩

theorem closedGradientForm_extends
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) (s t : D.domain) :
    closedGradientForm D ⟨(s : H), D.le_closure.1 s.property⟩
      ⟨(t : H), D.le_closure.1 t.property⟩ = inner ℂ (D s) (D t) := by
  unfold closedGradientForm
  congr 1
  · exact (D.le_closure.2 (rfl : (s : H) = (⟨(s : H), D.le_closure.1 s.property⟩ : D.closure.domain))).symm
  · exact (D.le_closure.2 (rfl : (t : H) = (⟨(t : H), D.le_closure.1 t.property⟩ : D.closure.domain))).symm

theorem closedGradientForm_closure_characterization
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : H →ₗ.[ℂ] V) (hclosable : D.IsClosable) (s : ℕ → D.domain) (u : H)
    (hlimit : Filter.Tendsto (fun n => (s n : H)) Filter.atTop (nhds u))
    (hcauchy : CauchySeq (fun n => D (s n))) :
    ∃ hu : u ∈ D.closure.domain,
      Filter.Tendsto (fun n => D (s n)) Filter.atTop (nhds (D.closure ⟨u, hu⟩)) ∧
      Filter.Tendsto (fun n => ‖D (s n)‖ ^ 2) Filter.atTop
        (nhds (closedGradientEnergy D ⟨u, hu⟩)) := by
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hgraph : (u, v) ∈ D.closure.graph := by
    apply hclosable.closure_isClosed.mem_of_tendsto (hlimit.prodMk_nhds hv)
    exact Filter.Eventually.of_forall fun n =>
      LinearPMap.le_graph_of_le D.le_closure (D.mem_graph (s n))
  obtain ⟨u', hu', hv'⟩ := D.closure.mem_graph_iff.mp hgraph
  have hu : u ∈ D.closure.domain := by simpa only [hu'] using u'.property
  have heq : D.closure ⟨u, hu⟩ = v := by
    have he : (⟨u, hu⟩ : D.closure.domain) = u' := Subtype.ext hu'.symm
    simpa only [he] using hv'
  refine ⟨hu, ?_, ?_⟩
  · simpa only [heq] using hv
  · simpa only [closedGradientEnergy, heq] using hv.norm.pow 2

theorem gradientQuadraticForm_closable
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : H →ₗ.[ℂ] V) (hclosable : D.IsClosable) (s : ℕ → D.domain)
    (hzero : Filter.Tendsto (fun n => (s n : H)) Filter.atTop (nhds 0))
    (hcauchy : CauchySeq (fun n => D (s n))) :
    Filter.Tendsto (fun n => D (s n)) Filter.atTop (nhds 0) := by
  obtain ⟨hu, hgrad, _⟩ := closedGradientForm_closure_characterization D hclosable s 0 hzero hcauchy
  have hz : (⟨0, hu⟩ : D.closure.domain) = 0 := Subtype.ext rfl
  simpa only [hz, LinearPMap.map_zero] using hgrad

end DedekindZetaZeroFree

end
