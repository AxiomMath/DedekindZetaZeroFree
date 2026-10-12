module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberJets.CutoffDefectTests
public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.DomainJetEquations
public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothSections.CompactL2ParameterJets

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators ContDiff
open MeasureTheory Topology Filter
set_option maxHeartbeats 2400000

namespace DedekindZetaZeroFree.KPContActualChamberGraphHolomorphy

section CompactClassIdentification
open KPContActualCompactSectionL2Jets
open KPContSectorSmoothFramesSupport
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem compact_section_classes_successor_derivatives
    (O : Set ℂ) (hO : IsOpen O)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (w : ℂ → Sections F ζ hζ U R P H) (hc : Conclusions w O K)
    (wk : ℕ → ℂ → Sections F ζ hζ U R P H)
    (hd : ∀ k s, s ∈ O → ∀ i x,
      (wk k s i).val x = iteratedDerivWithin k (fun t => (w t i).val x) O s)
    (W : ℕ → ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (hW : ∀ k s, s ∈ O → Represents (W k s) (wk k s)) :
    ∀ k s, s ∈ O → HasDerivWithinAt (W k) (W (k+1) s) O s := by
  obtain ⟨v,V,hv0,hsupp,hvder,hrep,hhol,hiter,hbound,hframe,hlift⟩ := hc
  have hsame : ∀ k s, s ∈ O → wk k s = v k s := by
    intro k s hs
    funext i
    apply Subtype.ext
    funext x
    exact (hd k s hs i x).trans (hvder k s hs i x).symm
  have hclasses : ∀ k, Set.EqOn (W k) (V k) O := by
    intro k s hs
    apply represents_unique (hW k s hs)
    rw [hsame k s hs]
    exact (hrep k s hs).1
  have hstep : ∀ k s, s ∈ O → HasDerivWithinAt (V k) (V (k+1) s) O s := by
    intro k s hs
    have he : derivWithin (V k) O s = V (k+1) s := by
      rw [← hiter (k+1) s hs, iteratedDerivWithin_succ]
      exact (derivWithin_congr (fun t ht => hiter k t ht) (hiter k s hs)).symm
    exact he ▸ (hhol k s hs).hasDerivWithinAt
  intro k s hs
  have hh := (hstep k s hs).congr (fun t ht => hclasses k ht) (hclasses k hs)
  have he : W (k+1) s = V (k+1) s := hclasses (k+1) hs
  exact he.symm ▸ hh

theorem actual_test_iota_represents
    (φ : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H) :
    Represents (KPContActualSectorTestEmbeddings.iota φ)
      (KPContActualSectorSmoothTestModules.scalarSections φ) := by
  have hspec := Classical.choose_spec (KPContActualSectorSmoothTestModules.scalar_gluing φ)
  have hmeas : Measurable (KPContActualSectorSmoothTestModules.scalarCovered φ).val := by
    exact ((KPContSectorLineL2Isometry.continuous_iff F ζ hζ U R P H _).mp
      (fun i => (hspec.1.1 i).continuous)).measurable
  let b : KPContSectorLineL2Isometry.BorelL2Scalars F ζ hζ U R :=
    ⟨KPContActualSectorSmoothTestModules.scalarCovered φ,
      hmeas, KPContActualSectorTestEmbeddings.scalar_memLp φ⟩
  have he : KPContSectorLineL2Isometry.scalarEmbedding F ζ hζ U R P H b =
      KPContActualSectorTestEmbeddings.iota φ := by
    apply Subtype.ext
    exact KPContSectorLineL2Isometry.scalarEmbedding_coe F ζ hζ U R P H b
  have hval : (KPContSectorLineL2Isometry.borelS F ζ hζ U R P H b).val =
      KPContActualSectorSmoothTestModules.scalarSections φ := by
    change KPContSectorScalarLineAlgebra.S F ζ hζ U R P H
      (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H
        (KPContActualSectorSmoothTestModules.scalarSections φ)) = _
    rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm, LinearEquiv.apply_symm_apply]
  rw [← he, ← hval]
  exact toSector_represents (KPContSectorLineL2Isometry.borelS F ζ hζ U R P H b)

theorem actual_test_graph_successor_of_section_jets
    (O : Set ℂ) (hO : IsOpen O) (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (φ : ℕ → ℂ → KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H)
    (hc : Conclusions (fun s => KPContActualSectorSmoothTestModules.scalarSections (φ 0 s)) O K)
    (hΔc : Conclusions (fun s => KPContActualSectorSmoothTestModules.scalarSections
      (KPContActualSectorTestDifferentialDescent.δ_U
        (KPContActualSectorTestDifferentialDescent.D_U (φ 0 s)))) O K)
    (hd : ∀ k s, s ∈ O → ∀ i x,
      (KPContActualSectorSmoothTestModules.scalarSections (φ k s) i).val x =
        iteratedDerivWithin k (fun t =>
          (KPContActualSectorSmoothTestModules.scalarSections (φ 0 t) i).val x) O s)
    (hΔd : ∀ k s, s ∈ O → ∀ i x,
      (KPContActualSectorSmoothTestModules.scalarSections
        (KPContActualSectorTestDifferentialDescent.δ_U
          (KPContActualSectorTestDifferentialDescent.D_U (φ k s))) i).val x =
        iteratedDerivWithin k (fun t =>
          (KPContActualSectorSmoothTestModules.scalarSections
            (KPContActualSectorTestDifferentialDescent.δ_U
              (KPContActualSectorTestDifferentialDescent.D_U (φ 0 t))) i).val x) O s) :
    ∀ k s, s ∈ O → HasDerivWithinAt
      (fun t => (KPContActualSectorTestEmbeddings.iota (φ k t),
        KPContActualSectorTestEmbeddings.iota (KPContActualSectorTestDifferentialDescent.δ_U
          (KPContActualSectorTestDifferentialDescent.D_U (φ k t)))))
      (KPContActualSectorTestEmbeddings.iota (φ (k+1) s),
        KPContActualSectorTestEmbeddings.iota (KPContActualSectorTestDifferentialDescent.δ_U
          (KPContActualSectorTestDifferentialDescent.D_U (φ (k+1) s)))) O s := by
  have hv := compact_section_classes_successor_derivatives O hO K _ hc
    (fun k s => KPContActualSectorSmoothTestModules.scalarSections (φ k s)) hd
    (fun k s => KPContActualSectorTestEmbeddings.iota (φ k s))
    (fun k s _ => actual_test_iota_represents (φ k s))
  have hδ := compact_section_classes_successor_derivatives O hO K _ hΔc
    (fun k s => KPContActualSectorSmoothTestModules.scalarSections
      (KPContActualSectorTestDifferentialDescent.δ_U
        (KPContActualSectorTestDifferentialDescent.D_U (φ k s)))) hΔd
    (fun k s => KPContActualSectorTestEmbeddings.iota
      (KPContActualSectorTestDifferentialDescent.δ_U
        (KPContActualSectorTestDifferentialDescent.D_U (φ k s))))
    (fun k s _ => actual_test_iota_represents _)
  exact fun k s hs => (hv k s hs).prodMk (hδ k s hs)

theorem finite_actual_chart_cover
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsCompact K) :
    ∃ (m : ℕ) (charts : Fin m → KPContActualSectorSmoothTestModules.ActualChart (U := U) (H := H)),
      K ⊆ ⋃ i, (charts i).baseDomain := by
  obtain ⟨_,hc⟩ := kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H
  let c := Classical.choice hc
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover (fun n => (c.chart n).baseDomain)
    (fun n => (c.properties n).base_open) (by rw [c.covers]; exact Set.subset_univ K)
  refine ⟨I.card,fun i => c.chart ((I.equivFin.symm i).val),?_⟩
  intro x hx
  obtain ⟨j,hj,hxj⟩ := Set.mem_iUnion₂.mp (hI hx)
  exact Set.mem_iUnion.mpr ⟨I.equivFin ⟨j,hj⟩, by simpa only [Equiv.symm_apply_apply] using hxj⟩

end CompactClassIdentification

section CoordinateConversion
open KPContLocalNorm

end CoordinateConversion

private theorem graph_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : Submodule ℂ E) (g : ℂ → p) (g' : p) (O : Set ℂ) (s : ℂ) (hs : s ∈ O)
    (hd : HasDerivWithinAt (fun z => (g z : E)) (g' : E) O s) :
    HasDerivWithinAt g g' O s := by
  have hc : ContinuousWithinAt g O s :=
    Topology.IsInducing.subtypeVal.continuousWithinAt_iff.mpr hd.continuousWithinAt
  have hcomp : p.subtypeL ∘ g =ᶠ[𝓝[O] s] (fun z => (g z : E)) := Filter.EventuallyEq.rfl
  have hh : HasFDerivWithinAt (fun z => (g z : E))
      (p.subtypeL ∘L (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) g')) O s := by
    convert hd.hasFDerivWithinAt using 1
    ext
    simp [ContinuousLinearMap.toSpanSingleton]
  have hf := HasFDerivWithinAt.of_comp_of_isEmbedding
    (t := Set.univ) (g := g) (f := p.subtypeL)
    (hc.tendsto.mono_right (by simp))
    p.subtypeL.hasFDerivWithinAt
    Topology.IsEmbedding.subtypeVal hh hcomp hs
  simpa using hf.hasDerivWithinAt

private theorem jets_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ℕ → ℂ → E) (O : Set ℂ)
    (hd : ∀ k, DifferentiableOn ℂ (u k) O)
    (hi : ∀ k s, s ∈ O → iteratedDerivWithin k (u 0) O s = u k s)
    (k : ℕ) (s : ℂ) (hs : s ∈ O) : HasDerivWithinAt (u k) (u (k+1) s) O s := by
  have hD : derivWithin (u k) O s = u (k+1) s := by
    rw [← hi (k+1) s hs, iteratedDerivWithin_succ]
    exact (derivWithin_congr (hi k) (hi k s hs)).symm
  exact hD ▸ (hd k s hs).hasDerivWithinAt

private theorem jets_identification {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ℕ → ℂ → E) (O : Set ℂ) (hO : UniqueDiffOn ℂ O)
    (hd : ∀ k s, s ∈ O → HasDerivWithinAt (u k) (u (k+1) s) O s) :
    ∀ k s, s ∈ O → iteratedDerivWithin k (u 0) O s = u k s := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro s hs
    rw [iteratedDerivWithin_succ]
    rw [derivWithin_congr ih (ih s hs)]
    exact (hd k s hs).derivWithin (hO s hs)

theorem successor_derivatives_of_locally_uniform_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (O : Set ℂ) (hO : IsOpen O) (f : ℕ → ℕ → ℂ → E) (u : ℕ → ℂ → E)
    (hlim : ∀ k, TendstoLocallyUniformlyOn (fun n => f n k) (u k) (atTop : Filter ℕ) O)
    (hstep : ∀ n k s, s ∈ O → HasDerivWithinAt (f n k) (f n (k+1) s) O s) :
    ∀ k s, s ∈ O → HasDerivWithinAt (u k) (u (k+1) s) O s := by
  have hhol : ∀ n k, DifferentiableOn ℂ (f n k) O :=
    fun n k s hs => (hstep n k s hs).differentiableWithinAt
  intro k s hs
  have hd := (hlim k).differentiableOn (Eventually.of_forall (fun n => hhol n k)) hO
  have hderlim := ((hlim k).deriv (Eventually.of_forall (fun n => hhol n k)) hO).tendsto_at hs
  have hder : ∀ n, deriv (f n k) s = f n (k+1) s := by
    intro n
    rw [← derivWithin_of_isOpen hO hs]
    exact (hstep n k s hs).derivWithin (hO.uniqueDiffWithinAt hs)
  have heq : deriv (u k) s = u (k+1) s := by
    apply tendsto_nhds_unique hderlim
    simpa only [Function.comp_apply, hder] using (hlim (k+1)).tendsto_at hs
  have hhd := (hd s hs).hasDerivWithinAt
  rwa [derivWithin_of_isOpen hO hs, heq] at hhd

open KPContActualChamberThreeL2Tails

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
  (level F ζ hζ C R P H U) R P H)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (hι : Function.Injective ι) (f : ℂ → S)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
  KPContinuation.spectralDomain f χ)
variable {r : KPContActualSectorCutoffGraphLimit.Cutoffs
  (U := level F ζ hζ C R P H U) (H := H)}
variable (domainEquations : KPContActualChamberDomainEquations.Properties
  F ζ hζ C R P H U μG hμG hR realization ι hι f hf buffer χ source r)

local notation "Δ" => KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ
  (level F ζ hζ C R P H U) R P H μG hμG hR realization
local notation "u" => UJet F ζ hζ C R P H U ι f buffer χ source hι hf
local notation "h" => HJet F ζ hζ C R P H U ι f buffer χ source hι hf

def ZJet (k : ℕ) (s : ℂ) : Sector F ζ hζ C R P H U × Sector F ζ hζ C R P H U :=
  if hs : s ∈ V then
    (u k s, (Δ) ⟨u k s, domainEquations.mem_domain k s hs⟩)
  else 0

def graphJet (k : ℕ) (s : ℂ) : (Δ).graph :=
  ⟨ZJet F ζ hζ C R P H U μG hμG hR realization ι hι f hf buffer χ source
      domainEquations k s, by
    by_cases hs : s ∈ V
    · simp only [ZJet, dif_pos hs]
      exact LinearPMap.mem_graph (Δ) ⟨u k s, domainEquations.mem_domain k s hs⟩
    · simp only [ZJet, dif_neg hs]
      exact Submodule.zero_mem _⟩

local notation "z" => ZJet F ζ hζ C R P H U μG hμG hR realization
  ι hι f hf buffer χ source domainEquations
local notation "zg" => graphJet F ζ hζ C R P H U μG hμG hR realization
  ι hι f hf buffer χ source domainEquations

structure Properties : Prop where
  value_holomorphic : ∀ k : ℕ, DifferentiableOn ℂ (u k) V
  product_holomorphic : ∀ k : ℕ, DifferentiableOn ℂ (z k) V
  value_derivatives : ∀ (k : ℕ) (s : ℂ), s ∈ V →
    iteratedDerivWithin k (u 0) V s = u k s
  product_derivatives : ∀ (k : ℕ) (s : ℂ), s ∈ V →
    iteratedDerivWithin k (z 0) V s = z k s

  graph_holomorphic : ∀ k : ℕ, DifferentiableOn ℂ (zg k) V
  graph_inclusion : ∀ (k : ℕ) (s : ℂ),
    (zg k s : Sector F ζ hζ C R P H U × Sector F ζ hζ C R P H U) = z k s
  graph_derivatives : ∀ (k : ℕ) (s : ℂ), s ∈ V →
    iteratedDerivWithin k (zg 0) V s = zg k s

  graph_closed : (Δ).IsClosed
  graph_complete : CompleteSpace (Δ).graph

  graph_norm_equivalence : ∀ x : (Δ).graph,
    ‖x‖ ≤ ‖x.val.1‖ + ‖x.val.2‖ ∧ ‖x.val.1‖ + ‖x.val.2‖ ≤ 2 * ‖x‖
  derivative_mem_domain : ∀ (k : ℕ) (s : ℂ), s ∈ V →
    iteratedDerivWithin k (u 0) V s ∈ (Δ).domain

  derivative_graph_bounds : ∀ (L : Set ℂ), IsCompact L → ∀ (hL : L ⊆ V) (k : ℕ),
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (s : ℂ) (hs : s ∈ L),
      KPChamberL2Defect.graphNorm (Δ)
        ⟨iteratedDerivWithin k (u 0) V s, derivative_mem_domain k s (hL hs)⟩ ≤ B

  differentiated_equation : ∀ (k : ℕ) (s : ℂ) (hs : s ∈ V),
    (Δ) ⟨iteratedDerivWithin k (u 0) V s, derivative_mem_domain k s hs⟩ -
      KPContActualChamberCasimirJets.lambda F s • iteratedDerivWithin k (u 0) V s =
    -h k s + ∑ j ∈ Finset.Icc 1 (min k 2),
      ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) •
        iteratedDerivWithin (k-j) (u 0) V s

theorem actual_graph_pairs_tendsto_locally_uniformly (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun n s => KPContActualSectorCutoffGraphLimit.graphPair μG hμG hR realization r n
        (smoothG F ζ hζ C R P H U ι f buffer χ source hι hf k s))
      (z k) (atTop : Filter ℕ) V := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact KPChamberL2Defect.chamber_isOpen]
  intro L hLV hL
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := domainEquations.uniform_graph_limit L hL hLV k ε hε
  filter_upwards [eventually_ge_atTop N] with n hn s hs
  have hb := hN n hn s hs
  have he : z k s = (u k s, (Δ) ⟨u k s, domainEquations.mem_domain k s (hLV hs)⟩) := by
    simp only [ZJet, dif_pos (hLV hs)]
  rw [he, dist_comm]
  exact hb

theorem properties_of_product_jets
    (hhol : ∀ k : ℕ, DifferentiableOn ℂ (z k) V)
    (hjets : ∀ (k : ℕ) (s : ℂ), s ∈ V →
      iteratedDerivWithin k (z 0) V s = z k s) :
    Properties F ζ hζ C R P H U μG hμG hR realization ι hι f hf buffer χ source domainEquations := by
  have hV : IsOpen V := KPChamberL2Defect.chamber_isOpen
  have hstep := jets_step z V hhol hjets
  have hfirst : ∀ k, Set.EqOn (fun s => (z k s).1) (u k) V := by
    intro k s hs
    simp only [ZJet, dif_pos hs]
  have hvalue : ∀ k s, s ∈ V → HasDerivWithinAt (u k) (u (k+1) s) V s := by
    intro k s hs
    have hp := (ContinuousLinearMap.fst ℂ (Sector F ζ hζ C R P H U)
      (Sector F ζ hζ C R P H U)).hasFDerivAt.comp_hasDerivWithinAt s (hstep k s hs)
    have hp' : HasDerivWithinAt (fun z' => (z k z').1) (u (k+1) s) V s := by
      change HasDerivWithinAt (fun z' => (z k z').1) (z (k+1) s).1 V s at hp
      have he : (z (k+1) s).1 = u (k+1) s := hfirst (k+1) hs
      exact he ▸ hp
    exact hp'.congr (fun t ht => (hfirst k ht).symm) (hfirst k hs).symm
  have hvid := jets_identification u V hV.uniqueDiffOn hvalue
  have hgstep : ∀ k s, s ∈ V → HasDerivWithinAt (zg k) (zg (k+1) s) V s := by
    intro k s hs
    exact graph_deriv (Δ).graph (zg k) (zg (k+1) s) V s hs (hstep k s hs)
  have hgid := jets_identification zg V hV.uniqueDiffOn hgstep
  have hclosed : (Δ).IsClosed :=
    (kp_cont_actual_sector_test_friedrichs F ζ hζ μG hμG
      (level F ζ hζ C R P H U) R hR P H realization).friedrichs.laplacian_closed
  have hmem : ∀ k s, s ∈ V → iteratedDerivWithin k (u 0) V s ∈ (Δ).domain := by
    intro k s hs
    rw [hvid k s hs]
    exact domainEquations.mem_domain k s hs
  refine {
    value_holomorphic := fun k s hs => (hvalue k s hs).differentiableWithinAt
    product_holomorphic := hhol
    value_derivatives := hvid
    product_derivatives := hjets
    graph_holomorphic := ?_
    graph_inclusion := fun _ _ => rfl
    graph_derivatives := hgid
    graph_closed := hclosed
    graph_complete := hclosed.isComplete.completeSpace_coe
    graph_norm_equivalence := ?_
    derivative_mem_domain := hmem
    derivative_graph_bounds := ?_
    differentiated_equation := ?_ }
  · intro k s hs
    exact (hgstep k s hs).hasFDerivWithinAt.differentiableWithinAt
  · intro x
    change max ‖x.val.1‖ ‖x.val.2‖ ≤ ‖x.val.1‖ + ‖x.val.2‖ ∧
      ‖x.val.1‖ + ‖x.val.2‖ ≤ 2 * max ‖x.val.1‖ ‖x.val.2‖
    constructor
    · exact max_le (le_add_of_nonneg_right (norm_nonneg _))
        (le_add_of_nonneg_left (norm_nonneg _))
    · have ha := le_max_left ‖x.val.1‖ ‖x.val.2‖
      have hb := le_max_right ‖x.val.1‖ ‖x.val.2‖
      linarith
  · intro L hL hLV k
    obtain ⟨B, hB, hbound⟩ := domainEquations.uniform_bounds L hL hLV k
    refine ⟨B, hB, ?_⟩
    intro s hs
    simpa only [KPChamberL2Defect.graphNorm, hvid k s (hLV hs)] using (hbound s hs).2
  · intro k s hs
    simpa only [hvid k s hs, hvid (k-_) s hs] using domainEquations.equation k s hs

theorem properties_of_product_successor_derivatives
    (hstep : ∀ (k : ℕ) (s : ℂ), s ∈ V →
      HasDerivWithinAt (z k) (z (k+1) s) V s) :
    Properties F ζ hζ C R P H U μG hμG hR realization ι hι f hf buffer χ source domainEquations := by
  apply properties_of_product_jets F ζ hζ C R P H U μG hμG hR realization
    ι hι f hf buffer χ source domainEquations
  · exact fun k s hs => (hstep k s hs).differentiableWithinAt
  · exact jets_identification z V KPChamberL2Defect.chamber_isOpen.uniqueDiffOn hstep

theorem properties_of_raw_compact_test_jets
    (hr : KPContActualSectorCutoffGraphLimit.Properties F ζ hζ
      (level F ζ hζ C R P H U) R P H μG hμG hR realization r)
    (hraw : ∀ n : ℕ,
      let φ := fun k s => KPContActualSectorCutoffGraphLimit.cutoffTest r n
        (smoothG F ζ hζ C R P H U ι f buffer χ source hι hf k s)
      let σ := fun (b : Bool) k s => KPContActualSectorSmoothTestModules.scalarSections
        (if b then KPContActualSectorTestDifferentialDescent.δ_U
          (KPContActualSectorTestDifferentialDescent.D_U (φ k s)) else φ k s)
      ∃ K : Set (Base F ζ hζ C R P H U), IsCompact K ∧
        (∀ (b : Bool) s, s ∈ V →
          KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ
            (level F ζ hζ C R P H U) R P H (σ b 0 s) ∧
          tsupport (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ
            (level F ζ hζ C R P H U) R P H (σ b 0 s)) ⊆ K) ∧
        (∀ (b : Bool) (a : KPContActualSectorSmoothTestModules.ActualChart
            (U := level F ζ hζ C R P H U) (H := H)),
          KPContActualCompactSectionL2Jets.ChartHolomorphicOn a (σ b 0) V) ∧
        (∀ (b : Bool) (k : ℕ) (s : ℂ), s ∈ V → ∀ i x,
          (σ b k s i).val x = iteratedDerivWithin k (fun t => (σ b 0 t i).val x) V s)) :
    Properties F ζ hζ C R P H U μG hμG hR realization ι hι f hf buffer χ source domainEquations := by
  apply properties_of_product_successor_derivatives F ζ hζ C R P H U μG hμG hR realization
    ι hι f hf buffer χ source domainEquations
  apply successor_derivatives_of_locally_uniform_limit V KPChamberL2Defect.chamber_isOpen
    (fun n k s => KPContActualSectorCutoffGraphLimit.graphPair μG hμG hR realization r n
      (smoothG F ζ hζ C R P H U ι f buffer χ source hι hf k s))
  · exact fun k => actual_graph_pairs_tendsto_locally_uniformly F ζ hζ C R P H U μG hμG hR realization
      ι hι f hf buffer χ source domainEquations k
  · intro n
    obtain ⟨K,hK,hsmooth,hholo,hder⟩ := hraw n
    obtain ⟨m,charts,hcover⟩ := finite_actual_chart_cover K hK
    let φ := fun k s => KPContActualSectorCutoffGraphLimit.cutoffTest r n
      (smoothG F ζ hζ C R P H U ι f buffer χ source hι hf k s)
    have hc (b : Bool) := (kp_cont_actual_compact_section_l2_jets F ζ hζ
      (level F ζ hζ C R P H U) R P H realization V KPChamberL2Defect.chamber_isOpen K hK
      (fun s => KPContActualSectorSmoothTestModules.scalarSections
        (if b then KPContActualSectorTestDifferentialDescent.δ_U
          (KPContActualSectorTestDifferentialDescent.D_U (φ 0 s)) else φ 0 s))
      (fun s hs => (hsmooth b s hs).1) (fun s hs => (hsmooth b s hs).2)
      m charts hcover (fun i => hholo b (charts i))).1
    have hstep := actual_test_graph_successor_of_section_jets V
      KPChamberL2Defect.chamber_isOpen K φ (hc false) (hc true) (hder false) (hder true)
    intro k s hs
    have he (k : ℕ) (t : ℂ) :
        KPContActualSectorCutoffGraphLimit.graphPair μG hμG hR realization r n
          (smoothG F ζ hζ C R P H U ι f buffer χ source hι hf k t) =
        (KPContActualSectorTestEmbeddings.iota (φ k t),
          KPContActualSectorTestEmbeddings.iota (KPContActualSectorTestDifferentialDescent.δ_U
            (KPContActualSectorTestDifferentialDescent.D_U (φ k t)))) := by
      apply Prod.ext
      · rfl
      · exact hr.test_action n _
    simpa only [he] using hstep k s hs

end DedekindZetaZeroFree.KPContActualChamberGraphHolomorphy

namespace DedekindZetaZeroFree

theorem kp_cont_actual_chamber_graph_holomorphy
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
    (hι : Function.Injective ι) (f : ℂ → S)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
      KPContinuation.spectralDomain f χ) :
    ∃ r : KPContActualSectorCutoffGraphLimit.Cutoffs
        (U := KPContActualAllCuspSource.level F ζ hζ C R P H U) (H := H),
      KPContActualSectorCutoffGraphLimit.Properties F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H μG hμG hR realization r ∧
      ∃ domainEquations : KPContActualChamberDomainEquations.Properties
          F ζ hζ C R P H U μG hμG hR realization ι hι f hf buffer χ source r,
        KPContActualChamberGraphHolomorphy.Properties
          F ζ hζ C R P H U μG hμG hR realization ι hι f hf buffer χ source domainEquations := by
  obtain ⟨r, hr, domainEquations⟩ := kp_cont_actual_chamber_domain_equations
    F ζ hζ C R P H U μG hμG hR realization ι hι f hf buffer χ source
  refine ⟨r, hr, domainEquations, ?_⟩
  apply KPContActualChamberGraphHolomorphy.properties_of_raw_compact_test_jets
    F ζ hζ C R P H U μG hμG hR realization ι hι f hf buffer χ source domainEquations hr

  intro n
  exact KPContActualChamberGraphHolomorphy.raw_actual_cutoff_test_section_jets
    F ζ hζ C R P H U ι hι f hf buffer χ source r n

end DedekindZetaZeroFree

end
