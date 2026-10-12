module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SphericalScalarPoleClearing

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open Filter
namespace DedekindZetaZeroFree.ResidueContinuity.ScalarSourceJointContinuity
open KPContActualSphericalRightFieldIdentification KPContLocalNorm
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

 theorem right_holomorphic_joint (D : GroupChart F ζ hζ U R P H)
    (O : Set ℂ) (hO : IsOpen O) (f : ℂ → Space (groupDimension F) → ℂ)
    (hf : KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields f O) :
    ContinuousOn (fun p : ℂ × Space (groupDimension F) => f p.1 p.2)
      (O ×ˢ D.T.carrier) := by
  intro p hp
  obtain ⟨r, hr, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (Metric.isOpen_ball.mem_nhds hp.2)
  let K := Metric.closedBall p.2 r
  have hK : IsCompact K := isCompact_closedBall _ _
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨j, hj, he⟩ := hf.2 K hK hb [(1, [])]
  have hje : ∀ s ∈ O, ∀ x : K, j s x = f s x := by
    intro s hs x
    simpa [KPContRightJets.rightCombination, KPContRightJets.rightWord] using he s hs x
  have hsN : ∀ᶠ q : ℂ × Space (groupDimension F) in 𝓝 p, q.1 ∈ O :=
    continuous_fst.continuousAt.preimage_mem_nhds (hO.mem_nhds hp.1)
  have hxN : ∀ᶠ q : ℂ × Space (groupDimension F) in 𝓝 p, q.2 ∈ K :=
    continuous_snd.continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds _ hr)
  have hcj : ContinuousAt j p.1 := hj.continuousOn.continuousAt (hO.mem_nhds hp.1)
  apply ContinuousAt.continuousWithinAt
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hjN := Metric.tendsto_nhds.mp (hcj.comp continuous_fst.continuousAt) (ε / 2) (by positivity)
  have hx : ∀ᶠ q : ℂ × Space (groupDimension F) in 𝓝 p,
      dist (f p.1 q.2) (f p.1 p.2) < ε / 2 :=
    Metric.tendsto_nhds.mp
      (((hf.1 p.1 hp.1).continuousOn.continuousAt
        (Metric.isOpen_ball.mem_nhds hp.2)).comp continuous_snd.continuousAt)
      (ε / 2) (by positivity)
  filter_upwards [hsN, hxN, hjN, hx] with q hqs hqx hqj hqd
  have hd : dist (f q.1 q.2) (f p.1 q.2) < ε / 2 := by
    rw [← hje q.1 hqs ⟨q.2, hqx⟩, ← hje p.1 hp.1 ⟨q.2, hqx⟩]
    exact (ContinuousMap.dist_apply_le_dist ⟨q.2, hqx⟩).trans_lt hqj
  exact (dist_triangle _ (f p.1 q.2) _).trans_lt (by linarith)

 theorem actual_joint_of_groupCharts (E : ℂ → KPSmoothLocalQuotientCharts.ActualCover F ζ hζ → ℂ)
    (O : Set ℂ) (hO : IsOpen O)
    (hlevel : ∀ s ∈ O, ∀ g, ∀ u : U.toOpenSubgroup,
      E s (g * (u.val : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)) = E s g)
    (hchart : ∀ D : GroupChart F ζ hζ U R P H,
      KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields
        (fun s x => E s (D.groupLift x)) O) :
    ContinuousOn (fun p : ℂ × KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => E p.1 p.2)
      (O ×ˢ Set.univ) := by
  intro p hp
  obtain ⟨D, hD⟩ := chart_at_point F ζ hζ U R P H p.2
  have hc := right_holomorphic_joint D O hO _ (hchart D)
  have hc0 : ContinuousAt (fun q : ℂ × Space (groupDimension F) => E q.1 (D.groupLift q.2)) (p.1, 0) :=
    hc.continuousAt ((hO.prod Metric.isOpen_ball).mem_nhds ⟨hp.1, D.zero_mem⟩)
  apply ContinuousAt.continuousWithinAt
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := Metric.tendsto_nhds.mp hc0 ε hε
  change {q : ℂ × Space (groupDimension F) |
    dist (E q.1 (D.groupLift q.2)) (E p.1 (D.groupLift 0)) < ε} ∈ 𝓝 (p.1, 0) at he
  rw [nhds_prod_eq, Filter.mem_prod_iff] at he
  obtain ⟨A, hA, B, hB, hAB⟩ := he
  have hBT : B ∩ D.T.carrier ∈ 𝓝 (0 : Space (groupDimension F)) :=
    inter_mem hB (Metric.isOpen_ball.mem_nhds D.zero_mem)
  have hg := D.piece_nhds (B ∩ D.T.carrier) hBT Set.inter_subset_right
  have hsN : ∀ᶠ q : ℂ × KPSmoothLocalQuotientCharts.ActualCover F ζ hζ in 𝓝 p, q.1 ∈ A ∩ O :=
    continuous_fst.continuousAt.preimage_mem_nhds (inter_mem hA (hO.mem_nhds hp.1))
  have hgN : ∀ᶠ q : ℂ × KPSmoothLocalQuotientCharts.ActualCover F ζ hζ in 𝓝 p,
      q.2 ∈ D.piece (B ∩ D.T.carrier) :=
    continuous_snd.continuousAt.preimage_mem_nhds (hD ▸ hg)
  filter_upwards [hsN, hgN] with q hqs hqg
  obtain ⟨x, hx, u, heq⟩ := hqg
  rw [heq, hlevel q.1 hqs.2 _ u, ← hD]
  exact hAB (show (q.1, x) ∈ A ×ˢ B from ⟨hqs.1, hx.1⟩)

 theorem actual_word_right_level
    (f : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ → ℂ)
    (hf : ∀ g, ∀ u : U.toOpenSubgroup,
      f (g * (u.val : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)) = f g)
    (w : List (Fin (groupDimension F))) (g) (u : U.toOpenSubgroup) :
    actualRightWord F ζ hζ w f (g * (u.val : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)) =
      actualRightWord F ζ hζ w f g := by
  induction w generalizing g with
  | nil => exact hf g u
  | cons b w ih =>
    change deriv _ 0 = deriv _ 0
    congr 1
    funext t
    have hc := RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ
      (KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single (lieEnumeration F b) 1))
      (show PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ from
        ⟨u.val.val, by
          have hu : u.val.val ∈ KPFiniteCuspAtlas.FiniteCover F ζ hζ := u.val.property
          simpa only [KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_finiteSubgroup_eq F ζ hζ] using hu⟩)
    change Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single (lieEnumeration F b) 1)))
      (u.val : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) at hc
    rw [mul_assoc, hc.eq.symm, ← mul_assoc]
    exact ih _

end DedekindZetaZeroFree.ResidueContinuity.ScalarSourceJointContinuity

end
