module

public import DedekindZetaZeroFree.Analysis.EllipticRegularity.SolutionGraphHolomorphy
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightDifferentialWords.CoordinateJetEstimates
public import DedekindZetaZeroFree.Eisenstein.Continuation.SphericalL2ResolventFormula

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPClearedResolvent

open MeasureTheory
open KPContLocalNorm

def GraphHolomorphicOn {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Δ : H →ₗ.[ℂ] H) (w F : ℂ → H) (O : Set ℂ) : Prop :=
  ∃ g : ℂ → Δ.graph, DifferentiableOn ℂ g O ∧
    ∀ s ∈ O, (g s : H × H) = (w s, F s)

def parameterPoleSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Δ : H →ₗ.[ℂ] H) (d : ℕ) : Set ℂ :=
  {s | KPContinuation.spectralCoordinate (d : ℤ) s ∈
    KPBelowThresholdResolvent.poleSet Δ (d : ℝ)}

def correction {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (d : ℕ) (baseInverse : H →L[ℂ] H) (h : ℂ → H) (s : ℂ) : H :=
  KPResolventPencil.shiftedResolvent baseInverse
    (KPContinuation.spectralCoordinate (d : ℤ) s) (h s)

def RightSmoothHolomorphicOn {m b : ℕ} (T : LocalBall m)
    (fields : Fin b → Space m → Space m) (u : ℂ → Space m → ℂ)
    (O : Set ℂ) : Prop :=
  (∀ s ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (u s) T.carrier) ∧
    ∀ (K : Set (Space m)) (hK : IsCompact K), K ⊆ T.carrier →
      ∀ terms : List (ℂ × List (Fin b)),
        letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
        ∃ j : ℂ → C(K, ℂ), DifferentiableOn ℂ j O ∧
          ∀ s ∈ O, ∀ x : K,
            j s x = KPContRightJets.rightCombination fields terms (u s) x

end KPClearedResolvent

private lemma cleared_graph_projection {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (Δ : H →ₗ.[ℂ] H) (hc : Δ.IsClosed) :
    ∃ P : (H × H) →L[ℂ] Δ.graph, ∀ x : Δ.graph, P x = x := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ H H
  let K := Δ.graph.comap e.toLinearEquiv.toLinearMap
  have hK : IsClosed (K : Set (WithLp 2 (H × H))) := hc.preimage e.continuous
  letI : IsClosed (K : Set (WithLp 2 (H × H))) := hK
  letI : CompleteSpace K := IsClosed.completeSpace_coe
  let L : K →L[ℂ] Δ.graph :=
    (e.toContinuousLinearMap.comp K.subtypeL).codRestrict Δ.graph (fun x => x.property)
  refine ⟨(L.comp K.orthogonalProjectionOnto).comp e.symm.toContinuousLinearMap, ?_⟩
  intro x
  have hx : e.symm (x : H × H) ∈ K := by
    change e (e.symm (x : H × H)) ∈ Δ.graph
    simpa using x.property
  have hp := K.orthogonalProjectionOnto_mem_subspace_eq_self ⟨e.symm x, hx⟩
  change L (K.orthogonalProjectionOnto (e.symm x)) = x
  rw [hp]
  apply Subtype.ext
  exact e.apply_symm_apply x

theorem kp_cont_local_cleared_resolvent
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Δ : H →ₗ.[ℂ] H) (hclosed : Δ.IsClosed)
    (d : ℕ) (hd : 0 < d) (baseInverse : H →L[ℂ] H)
    (s₀ : ℂ) (r : ℝ) (hr : 0 < r)
    (hΩ : Metric.ball s₀ r ⊆ KPContinuation.spectralDomain)
    (hdiscrete : IsDiscrete
      (Metric.ball s₀ r ∩ KPClearedResolvent.parameterPoleSet Δ d))
    (hR : ∀ s ∈ Metric.ball s₀ r \ KPClearedResolvent.parameterPoleSet Δ d,
      KPResolventPencil.GenuineInverse Δ
        (KPContinuation.spectralCoordinate (d : ℤ) s)
        (KPResolventPencil.shiftedResolvent baseInverse
          (KPContinuation.spectralCoordinate (d : ℤ) s)))
    (h w : ℂ → H) (q : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h (Metric.ball s₀ r))
    (hq : DifferentiableOn ℂ q (Metric.ball s₀ r))
    (hqne : ∃ s ∈ Metric.ball s₀ r, q s ≠ 0)
    (hw : DifferentiableOn ℂ w (Metric.ball s₀ r))
    (hclears : ∀ s ∈ Metric.ball s₀ r \ KPClearedResolvent.parameterPoleSet Δ d,
      w s = q s • KPClearedResolvent.correction d baseInverse h s) :
    (∀ s ∈ Metric.ball s₀ r, ∃ hs : w s ∈ Δ.domain,
      Δ ⟨w s, hs⟩ = KPContinuation.spectralCoordinate (d : ℤ) s • w s + q s • h s) ∧
    KPClearedResolvent.GraphHolomorphicOn Δ w
      (fun s => KPContinuation.spectralCoordinate (d : ℤ) s • w s + q s • h s)
      (Metric.ball s₀ r) := by
  let O := Metric.ball s₀ r
  let S := KPClearedResolvent.parameterPoleSet Δ d
  let a := KPContinuation.spectralCoordinate (d : ℤ)
  let F : ℂ → H := fun s => a s • w s + q s • h s
  let p : ℂ → H × H := fun s => (w s, F s)
  have ha : Differentiable ℂ a := by
    change Differentiable ℂ (fun s : ℂ => (d : ℂ) * (1 - ((1 : ℂ) / 3 + 2 * s) ^ 2))
    fun_prop
  have hF : DifferentiableOn ℂ F O := (ha.differentiableOn.smul hw).add (hq.smul hh)
  have hp : DifferentiableOn ℂ p O := hw.prodMk hF
  have hoff : Set.MapsTo p (O \ S) Δ.graph := by
    intro s hs
    rcases hR s hs with ⟨hdom, heq, _⟩
    let v := KPClearedResolvent.correction d baseInverse h s
    have hv : v ∈ Δ.domain := hdom (h s)
    have hvEq : Δ ⟨v, hv⟩ = a s • v + h s := by
      have he := heq (h s)
      change Δ ⟨v, hv⟩ - a s • v = h s at he
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp he)
    have hweq : w s = q s • v := hclears s hs
    have hwdom : w s ∈ Δ.domain := hweq ▸ Δ.domain.smul_mem (q s) hv
    apply Δ.mem_graph_iff'.mpr
    refine ⟨⟨w s, hwdom⟩, ?_⟩
    apply Prod.ext
    · rfl
    · change Δ ⟨w s, hwdom⟩ = F s
      have hsub : (⟨w s, hwdom⟩ : Δ.domain) = q s • ⟨v, hv⟩ := Subtype.ext hweq
      rw [hsub, Δ.map_smul, hvEq]
      dsimp [F]
      rw [hweq, smul_add]
      congr 1
      exact smul_comm (q s) (a s) v
  have hc : (O ∩ S).Countable := IsLindelof.of_coe.countable_of_isDiscrete hdiscrete
  have hdense : Dense (O ∩ S)ᶜ := hc.dense_compl ℂ
  have hmem : ∀ s ∈ O, p s ∈ Δ.graph := by
    intro s hs
    have hcl : s ∈ closure (O \ S) := by
      have ht := Metric.isOpen_ball.inter_closure ⟨hs, hdense s⟩
      apply closure_mono _ ht
      intro t ht
      exact ⟨ht.1, fun hS => ht.2 ⟨ht.1, hS⟩⟩
    have hcp : ContinuousWithinAt p (O \ S) s :=
      (hp.continuousOn s hs).mono Set.diff_subset
    have ht := hcp.mem_closure hcl hoff
    rwa [hclosed.closure_eq] at ht
  constructor
  · intro s hs
    rcases Δ.mem_graph_iff.mp (hmem s hs) with ⟨v, hv, heq⟩
    change (v : H) = w s at hv
    have hws : w s ∈ Δ.domain := hv ▸ v.property
    refine ⟨hws, ?_⟩
    have hvs : v = ⟨w s, hws⟩ := Subtype.ext hv
    simpa only [hvs] using heq
  · rcases cleared_graph_projection Δ hclosed with ⟨P, hP⟩
    refine ⟨fun s => P (p s), P.differentiable.comp_differentiableOn hp, ?_⟩
    intro s hs
    have he := hP ⟨p s, hmem s hs⟩
    exact congrArg Subtype.val he

end DedekindZetaZeroFree

end
