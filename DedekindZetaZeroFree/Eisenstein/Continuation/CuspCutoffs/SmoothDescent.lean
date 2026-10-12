module

public import DedekindZetaZeroFree.Eisenstein.Continuation.IncomingCuspModes.SmoothZeroExtension

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators ContDiff
open Topology

namespace DedekindZetaZeroFree.KPContActualCutoffSmoothDescent

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)

def cutoffScalar (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (f : ℂ → S) (s : ℂ) : Covered F ζ hζ C R P H U → ℂ :=
  KPCutoffSource.cutoffSum (ends F ζ hζ C R P H U B) (height F ζ hζ C R P H U B)
    (fun a => (χ a).toFun) (incomingRealization F ζ hζ C R P H U ι B) f s

def commutatorScalar (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (f : ℂ → S) (s : ℂ) : Covered F ζ hζ C R P H U → ℂ :=
  KPCutoffSource.commutatorSum (Module.finrank ℚ F / 2)
    (ends F ζ hζ C R P H U B) (height F ζ hζ C R P H U B)
    (fun a => (χ a).toFun) (incomingRealization F ζ hζ C R P H U ι B) f s

abbrev SmoothSections := KPContSectorSmoothFramesSupport.smoothSections F ζ hζ
  (level F ζ hζ C R P H U) R P H

def scalar (w : SmoothSections F ζ hζ C R P H U) : Covered F ζ hζ C R P H U → ℂ :=
  ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ (level F ζ hζ C R P H U)
    R P H).symm w).val.val

def lift (w : SmoothSections F ζ hζ C R P H U) : KPSmoothLocalQuotientCharts.X F ζ hζ → ℂ :=
  scalar F ζ hζ C R P H U w ∘
    KPContSectorQuotientRelationsComparison.piTilde F ζ hζ (level F ζ hζ C R P H U)

def frameValue (w : SmoothSections F ζ hζ C R P H U)
    (a : Cusps F ζ hζ C R P H U) (z : KPCuspCharts.Coordinates F) : ℂ :=
  (KPContSectorSmoothFramesSupport.cuspCoefficient F ζ hζ (level F ζ hζ C R P H U)
    R P H w.val a.1 a.2 z : ℂ)

theorem coveredPoint_eq_central (a : Cusps F ζ hζ C R P H U) (ε : rootsOfUnity 3 F)
    (z : KPCuspCharts.Coordinates F) :
    coveredPoint F ζ hζ C R P H U a ε z =
      KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε
        (coveredPoint F ζ hζ C R P H U a 1 z) := by
  simp [coveredPoint, KPContSectorCoveredQuotientVocabulary.z_mk,
    map_one]

theorem coveredPoint_base (a : Cusps F ζ hζ C R P H U) (ε : rootsOfUnity 3 F)
    (z : KPCuspCharts.Coordinates F) :
    KPContSectorCoveredQuotientVocabulary.q F ζ hζ (level F ζ hζ C R P H U)
      (coveredPoint F ζ hζ C R P H U a ε z) =
      KPContActualCollarBuffer.chartLift F ζ hζ (level F ζ hζ C R P H U) R P H a z := by
  rw [coveredPoint_eq_central, KPContSectorCoveredQuotientVocabulary.q_z]
  simp [coveredPoint, KPContSectorCoveredQuotientVocabulary.q_mk,
    map_one, KPContActualCollarBuffer.chartLift,
    KPContSectorSmoothFramesSupport.cuspPoint, KPContFlatCuspIncomingEvaluation.atlas]

theorem height_coveredPoint (a : Cusps F ζ hζ C R P H U) (ε : rootsOfUnity 3 F)
    (z : KPCuspCharts.Coordinates F) (hz : B.τ < z.2) :
    height F ζ hζ C R P H U B a (coveredPoint F ζ hζ C R P H U a ε z) = z.2 := by
  unfold height
  rw [coveredPoint_base]
  exact B.height_coordinates a z hz

theorem coveredPoint_mem_end (a : Cusps F ζ hζ C R P H U) (ε : rootsOfUnity 3 F)
    (z : KPCuspCharts.Coordinates F) (hz : B.τ < z.2) :
    coveredPoint F ζ hζ C R P H U a ε z ∈ ends F ζ hζ C R P H U B a := by
  change KPContSectorCoveredQuotientVocabulary.q F ζ hζ (level F ζ hζ C R P H U)
    (coveredPoint F ζ hζ C R P H U a ε z) ∈
      KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H B.τ a
  rw [coveredPoint_base, ← B.lift_range a]
  exact ⟨z, hz, rfl⟩

theorem ends_pairwise_disjoint : Pairwise (fun a b => Disjoint
    (ends F ζ hζ C R P H U B a) (ends F ζ hζ C R P H U B b)) := by
  intro a b hab
  exact (B.disjoint_ends hab).preimage _

theorem scalar_off_ends
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (f : ℂ → S) (s : ℂ) (x : Covered F ζ hζ C R P H U)
    (hx : ∀ a, x ∉ ends F ζ hζ C R P H U B a) :
    cutoffScalar F ζ hζ C R P H U ι B χ f s x = 0 ∧
      commutatorScalar F ζ hζ C R P H U ι B χ f s x = 0 := by
  simp [cutoffScalar, commutatorScalar, KPCutoffSource.cutoffSum,
    KPCutoffSource.commutatorSum, hx]

theorem cutoffScalar_tail
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (f : ℂ → S) (s : ℂ) (a : Cusps F ζ hζ C R P H U)
    (x : Covered F ζ hζ C R P H U) (hx : x ∈ ends F ζ hζ C R P H U B a)
    (ht : T + 1 ≤ height F ζ hζ C R P H U B a x) :
    cutoffScalar F ζ hζ C R P H U ι B χ f s x =
      incomingRealization F ζ hζ C R P H U ι B s (f s) x := by
  exact KPCutoffSource.cutoffSum_at_every_cusp _
    (ends_pairwise_disjoint F ζ hζ C R P H U B) _ χ _ f a s x hx ht

private theorem multiplier_zero_off_collar (d : ℕ) (χ : KPCutoffSource.SmoothCuspCutoff T)
    (s : ℂ) (t : ℝ) (ht : t ∉ Set.Icc T (T + 1)) :
    KPCutoffSource.incomingCommutatorMultiplier d χ.toFun s t = 0 := by
  have hw := Function.support_subset_iff'.mp
    (subset_trans subset_closure (KPCutoffSource.incoming_commutator_support d χ s 1)) t ht
  simpa [KPIncomingCasimir.heightFactor, Complex.exp_ne_zero] using hw

theorem commutatorScalar_covered_support
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (f : ℂ → S) (s : ℂ) :
    tsupport (commutatorScalar F ζ hζ C R P H U ι B χ f s) ⊆
      KPContActualCollarBuffer.coveredCollars F ζ hζ (level F ζ hζ C R P H U)
        R P H B.τ T := by
  have hclosed : IsClosed (KPContActualCollarBuffer.coveredCollars F ζ hζ
      (level F ζ hζ C R P H U) R P H B.τ T) := by
    apply IsClosed.preimage (KPContSectorQuotientRelationsComparison.q_continuous
      F ζ hζ (level F ζ hζ C R P H U))
    exact isClosed_iUnion_of_finite (fun _ => isClosed_closure)
  apply closure_minimal _ hclosed
  apply Function.support_subset_iff'.mpr
  intro x hx
  unfold commutatorScalar KPCutoffSource.commutatorSum
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with ha
  · have ht : height F ζ hζ C R P H U B a x ∉ Set.Icc T (T + 1) := by
      intro ht
      apply hx
      apply Set.mem_iUnion.mpr
      refine ⟨a, subset_closure ?_⟩
      exact ⟨ha, ht⟩
    rw [multiplier_zero_off_collar _ (χ a) s _ ht, zero_mul]
  · rfl

private theorem cutoff_derivatives_zero_germ
    (a : Cusps F ζ hζ C R P H U) (χ : KPCutoffSource.SmoothCuspCutoff T)
    (x : Covered F ζ hζ C R P H U) (hx : x ∉ ends F ζ hζ C R P H U B a) :
    ∀ᶠ y in 𝓝 x, y ∈ ends F ζ hζ C R P H U B a →
      χ.toFun (height F ζ hζ C R P H U B a y) = 0 ∧
      deriv χ.toFun (height F ζ hζ C R P H U B a y) = 0 ∧
      deriv (deriv χ.toFun) (height F ζ hζ C R P H U B a y) = 0 := by
  let q := KPContSectorCoveredQuotientVocabulary.q F ζ hζ (level F ζ hζ C R P H U)
  let E := KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H B.τ a
  have hc : Continuous q := KPContSectorQuotientRelationsComparison.q_continuous _ _ _ _
  by_cases hxcl : q x ∈ closure E
  · have hxf : q x ∈ frontier E := by
      rw [frontier, (B.open_ends a).interior_eq]
      exact ⟨hxcl, hx⟩
    obtain ⟨V, hV, hxV, hz⟩ := B.boundary_zero_extension a (q x) hxf
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hV.mem_nhds hxV)] with y hy he
    have he' : q y ∈ KPContActualCollarBuffer.endSet F ζ hζ
      (level F ζ hζ C R P H U) R P H B.τ a := he
    simpa only [KPContActualCollarBuffer.zeroExtension, Set.indicator_of_mem he',
      KPContActualCutoffSmoothDescent.height, q] using hz χ (q y) hy
  · filter_upwards [hc.continuousAt.preimage_mem_nhds
      (isClosed_closure.isOpen_compl.mem_nhds hxcl)] with y hy he
    exact False.elim (hy (subset_closure he))

theorem cutoff_commutator_zero_germ
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (f : ℂ → S) (s : ℂ) (x : Covered F ζ hζ C R P H U)
    (hx : ∀ a, x ∉ ends F ζ hζ C R P H U B a) :
    ∀ᶠ y in 𝓝 x, cutoffScalar F ζ hζ C R P H U ι B χ f s y = 0 ∧
      commutatorScalar F ζ hζ C R P H U ι B χ f s y = 0 := by
  have hz := Filter.eventually_all.mpr (fun a =>
    cutoff_derivatives_zero_germ F ζ hζ C R P H U B a (χ a) x (hx a))
  filter_upwards [hz] with y hy
  constructor
  · unfold cutoffScalar KPCutoffSource.cutoffSum
    apply Finset.sum_eq_zero
    intro a _
    split_ifs with he
    · dsimp only
      rw [(hy a he).1, Complex.ofReal_zero, zero_mul]
    · rfl
  · unfold commutatorScalar KPCutoffSource.commutatorSum
    apply Finset.sum_eq_zero
    intro a _
    split_ifs with he
    · simp only [KPCutoffSource.incomingCommutatorMultiplier, (hy a he).2.1,
        (hy a he).2.2, Complex.ofReal_zero, mul_zero, zero_mul, add_zero, sub_zero]
    · rfl

theorem cutoffScalar_on_end
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (f : ℂ → S) (s : ℂ) (a : Cusps F ζ hζ C R P H U)
    (x : Covered F ζ hζ C R P H U) (hx : x ∈ ends F ζ hζ C R P H U B a) :
    cutoffScalar F ζ hζ C R P H U ι B χ f s x =
      ((χ a).toFun (height F ζ hζ C R P H U B a x) : ℂ) *
        incomingRealization F ζ hζ C R P H U ι B s (f s) x := by
  unfold cutoffScalar KPCutoffSource.cutoffSum
  rw [Finset.sum_eq_single a]
  · simp [hx]
  · intro b _ hba
    have hb : x ∉ ends F ζ hζ C R P H U B b := fun hb =>
      Set.disjoint_left.mp (ends_pairwise_disjoint F ζ hζ C R P H U B hba) hb hx
    simp [hb]
  · simp

theorem commutatorScalar_on_end
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (f : ℂ → S) (s : ℂ) (a : Cusps F ζ hζ C R P H U)
    (x : Covered F ζ hζ C R P H U) (hx : x ∈ ends F ζ hζ C R P H U B a) :
    commutatorScalar F ζ hζ C R P H U ι B χ f s x =
      KPCutoffSource.incomingCommutatorMultiplier (Module.finrank ℚ F / 2)
        (χ a).toFun s (height F ζ hζ C R P H U B a x) *
        incomingRealization F ζ hζ C R P H U ι B s (f s) x := by
  unfold commutatorScalar KPCutoffSource.commutatorSum
  rw [Finset.sum_eq_single a]
  · simp [hx]
  · intro b _ hba
    have hb : x ∉ ends F ζ hζ C R P H U B b := fun hb =>
      Set.disjoint_left.mp (ends_pairwise_disjoint F ζ hζ C R P H U B hba) hb hx
    simp [hb]
  · simp

theorem endLift_iff_mem_end (x : Covered F ζ hζ C R P H U) :
    Nonempty (EndLift F ζ hζ C R P H U B x) ↔
      ∃ a, x ∈ ends F ζ hζ C R P H U B a := by
  constructor
  · rintro ⟨l⟩
    have hl := coveredPoint_mem_end F ζ hζ C R P H U B
      l.cusp l.sheet l.coordinates l.high
    rw [l.point] at hl
    exact ⟨l.cusp, hl⟩
  · rintro ⟨a, hx⟩
    change KPContSectorCoveredQuotientVocabulary.q F ζ hζ (level F ζ hζ C R P H U) x ∈
      KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H B.τ a at hx
    rw [← B.lift_range a] at hx
    obtain ⟨z, hz, he⟩ := hx
    have hq := (coveredPoint_base F ζ hζ C R P H U a 1 z).trans he
    obtain ⟨ε, hε⟩ := (KPContSectorQuotientRelationsComparison.q_eq_iff F ζ hζ
      (level F ζ hζ C R P H U) _ x).mp hq
    refine ⟨⟨a, ε, z, hz, ?_⟩⟩
    exact (coveredPoint_eq_central F ζ hζ C R P H U a ε z).trans hε.symm

theorem endLift_cusp_eq (x : Covered F ζ hζ C R P H U)
    (l m : EndLift F ζ hζ C R P H U B x) : l.cusp = m.cusp := by
  by_contra hne
  have hl := l.point ▸ coveredPoint_mem_end F ζ hζ C R P H U B
    l.cusp l.sheet l.coordinates l.high
  have hm := m.point ▸ coveredPoint_mem_end F ζ hζ C R P H U B
    m.cusp m.sheet m.coordinates m.high
  exact Set.disjoint_left.mp (ends_pairwise_disjoint F ζ hζ C R P H U B hne) hl hm

theorem endLift_height_eq (x : Covered F ζ hζ C R P H U)
    (l m : EndLift F ζ hζ C R P H U B x) : l.coordinates.2 = m.coordinates.2 := by
  have hl := height_coveredPoint F ζ hζ C R P H U B
    l.cusp l.sheet l.coordinates l.high
  have hm := height_coveredPoint F ζ hζ C R P H U B
    m.cusp m.sheet m.coordinates m.high
  rw [l.point] at hl
  rw [m.point, ← endLift_cusp_eq F ζ hζ C R P H U B x l m] at hm
  exact hl.symm.trans hm

theorem incomingValue_height_formula (a : Cusps F ζ hζ C R P H U)
    (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (v : S)
    (z : KPCuspCharts.Coordinates F) :
    incomingValue F ζ hζ C R P H U ι a s v z =
      KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s z.2 *
        ((KPContFlatCuspIncomingEvaluation.b F ζ hζ C R P H U a ι s hs v).val z.1.2).val
          (QuotientAddGroup.mk z.1.1) := by
  unfold incomingValue
  rw [KPContFlatCuspIncomingEvaluation.incoming_formula]
  rfl

theorem incomingRealization_eq_of_transport (s : ℂ) (v : S)
    (htransport : ∀ (x : Covered F ζ hζ C R P H U)
      (l m : EndLift F ζ hζ C R P H U B x),
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ l.sheet : ℂ) *
        incomingValue F ζ hζ C R P H U ι l.cusp s v l.coordinates =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ m.sheet : ℂ) *
        incomingValue F ζ hζ C R P H U ι m.cusp s v m.coordinates)
    (a : Cusps F ζ hζ C R P H U) (ε : rootsOfUnity 3 F)
    (z : KPCuspCharts.Coordinates F) (hz : B.τ < z.2) :
    incomingRealization F ζ hζ C R P H U ι B s v
      (coveredPoint F ζ hζ C R P H U a ε z) =
        (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
          incomingValue F ζ hζ C R P H U ι a s v z := by
  let m : EndLift F ζ hζ C R P H U B (coveredPoint F ζ hζ C R P H U a ε z) :=
    ⟨a, ε, z, hz, rfl⟩
  have hm : Nonempty (EndLift F ζ hζ C R P H U B
      (coveredPoint F ζ hζ C R P H U a ε z)) := ⟨m⟩
  change (if h : Nonempty (EndLift F ζ hζ C R P H U B
      (coveredPoint F ζ hζ C R P H U a ε z)) then _ else _) = _
  rw [dif_pos hm]
  exact htransport _ (Classical.choice hm) m

theorem scalar_coveredPoint (w : SmoothSections F ζ hζ C R P H U)
    (a : Cusps F ζ hζ C R P H U) (ε : rootsOfUnity 3 F)
    (z : KPCuspCharts.Coordinates F) :
    scalar F ζ hζ C R P H U w (coveredPoint F ζ hζ C R P H U a ε z) =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
        frameValue F ζ hζ C R P H U w a z := by
  let g := ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
    (level F ζ hζ C R P H U) R P H).symm w).val
  have hg : KPContSectorScalarLineAlgebra.S F ζ hζ
      (level F ζ hζ C R P H U) R P H g = w.val := by
    exact congrArg Subtype.val ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
      (level F ζ hζ C R P H U) R P H).apply_symm_apply w)
  have he := KPContSectorSmoothFramesSupport.phase_lift_formula F ζ hζ
    (level F ζ hζ C R P H U) R P H g a.1 ε
    (KPContSectorSmoothFramesSupport.cuspPoint F ζ hζ
      (level F ζ hζ C R P H U) R P H a.1 a.2 z)
  rw [hg] at he
  exact he

theorem cutoff_sheet_of_incoming
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (f : ℂ → S) (s : ℂ) (w : SmoothSections F ζ hζ C R P H U)
    (hw : scalar F ζ hζ C R P H U w = cutoffScalar F ζ hζ C R P H U ι B χ f s)
    (a : Cusps F ζ hζ C R P H U) (ε : rootsOfUnity 3 F)
    (z : KPCuspCharts.Coordinates F) (hz : B.τ < z.2)
    (hin : incomingRealization F ζ hζ C R P H U ι B s (f s)
      (coveredPoint F ζ hζ C R P H U a ε z) =
        (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
          incomingValue F ζ hζ C R P H U ι a s (f s) z) :
    scalar F ζ hζ C R P H U w (coveredPoint F ζ hζ C R P H U a ε z) =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
        (((χ a).toFun z.2 : ℂ) * incomingValue F ζ hζ C R P H U ι a s (f s) z) := by
  rw [hw, cutoffScalar_on_end F ζ hζ C R P H U ι B χ f s a _
    (coveredPoint_mem_end F ζ hζ C R P H U B a ε z hz),
    height_coveredPoint F ζ hζ C R P H U B a ε z hz, hin]
  ring

theorem commutator_sheet_of_incoming
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (f : ℂ → S) (s : ℂ) (w : SmoothSections F ζ hζ C R P H U)
    (hw : scalar F ζ hζ C R P H U w = commutatorScalar F ζ hζ C R P H U ι B χ f s)
    (a : Cusps F ζ hζ C R P H U) (ε : rootsOfUnity 3 F)
    (z : KPCuspCharts.Coordinates F) (hz : B.τ < z.2)
    (hin : incomingRealization F ζ hζ C R P H U ι B s (f s)
      (coveredPoint F ζ hζ C R P H U a ε z) =
        (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
          incomingValue F ζ hζ C R P H U ι a s (f s) z) :
    scalar F ζ hζ C R P H U w (coveredPoint F ζ hζ C R P H U a ε z) =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
        (KPCutoffSource.incomingCommutatorMultiplier (Module.finrank ℚ F / 2)
          (χ a).toFun s z.2 * incomingValue F ζ hζ C R P H U ι a s (f s) z) := by
  rw [hw, commutatorScalar_on_end F ζ hζ C R P H U ι B χ f s a _
    (coveredPoint_mem_end F ζ hζ C R P H U B a ε z hz),
    height_coveredPoint F ζ hζ C R P H U B a ε z hz, hin]
  ring

theorem cutoff_frame_of_incoming
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (f : ℂ → S) (s : ℂ) (w : SmoothSections F ζ hζ C R P H U)
    (hw : scalar F ζ hζ C R P H U w = cutoffScalar F ζ hζ C R P H U ι B χ f s)
    (a : Cusps F ζ hζ C R P H U) (z : KPCuspCharts.Coordinates F) (hz : B.τ < z.2)
    (hin : incomingRealization F ζ hζ C R P H U ι B s (f s)
      (coveredPoint F ζ hζ C R P H U a 1 z) =
        incomingValue F ζ hζ C R P H U ι a s (f s) z) :
    frameValue F ζ hζ C R P H U w a z =
      ((χ a).toFun z.2 : ℂ) * incomingValue F ζ hζ C R P H U ι a s (f s) z := by
  have h := cutoff_sheet_of_incoming F ζ hζ C R P H U ι B χ f s w hw a 1 z hz
    (by simpa using hin)
  rw [scalar_coveredPoint] at h
  simpa using h

theorem commutator_frame_of_incoming
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (f : ℂ → S) (s : ℂ) (w : SmoothSections F ζ hζ C R P H U)
    (hw : scalar F ζ hζ C R P H U w = commutatorScalar F ζ hζ C R P H U ι B χ f s)
    (a : Cusps F ζ hζ C R P H U) (z : KPCuspCharts.Coordinates F) (hz : B.τ < z.2)
    (hin : incomingRealization F ζ hζ C R P H U ι B s (f s)
      (coveredPoint F ζ hζ C R P H U a 1 z) =
        incomingValue F ζ hζ C R P H U ι a s (f s) z) :
    frameValue F ζ hζ C R P H U w a z =
      KPCutoffSource.incomingCommutatorMultiplier (Module.finrank ℚ F / 2)
        (χ a).toFun s z.2 * incomingValue F ζ hζ C R P H U ι a s (f s) z := by
  have h := commutator_sheet_of_incoming F ζ hζ C R P H U ι B χ f s w hw a 1 z hz
    (by simpa using hin)
  rw [scalar_coveredPoint] at h
  simpa using h

theorem incomingValue_contDiff (a : Cusps F ζ hζ C R P H U)
    (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (v : S) :
    ContDiff ℝ (⊤ : ℕ∞) (incomingValue F ζ hζ C R P H U ι a s v) := by
  have he : incomingValue F ζ hζ C R P H U ι a s v =
      fun z : KPCuspCharts.Coordinates F =>
        KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s z.2 *
          KPContFlatCuspIncomingEvaluation.projectedScalar F ζ hζ C R P H U a
            (KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U a ι s v) := by
    funext z
    rw [incomingValue_height_formula F ζ hζ C R P H U ι a s hs v z]
    rfl
  rw [he]
  unfold KPIncomingCasimir.heightFactor
  have hz : ContDiff ℝ (⊤ : ℕ∞) (fun z : KPCuspCharts.Coordinates F => (z.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_snd
  exact (Complex.contDiff_exp.comp (contDiff_const.mul hz)).mul contDiff_const

theorem cutoff_local_contDiff
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (a : Cusps F ζ hζ C R P H U) (s : ℂ)
    (hs : s ∈ KPContinuation.spectralDomain) (v : S) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : KPCuspCharts.Coordinates F =>
      ((χ a).toFun z.2 : ℂ) * incomingValue F ζ hζ C R P H U ι a s v z) := by
  exact (Complex.ofRealCLM.contDiff.comp ((χ a).smooth.comp contDiff_snd)).mul
    (incomingValue_contDiff F ζ hζ C R P H U ι a s hs v)

theorem commutator_local_contDiff
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (a : Cusps F ζ hζ C R P H U) (s : ℂ)
    (hs : s ∈ KPContinuation.spectralDomain) (v : S) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : KPCuspCharts.Coordinates F =>
      KPCutoffSource.incomingCommutatorMultiplier (Module.finrank ℚ F / 2)
        (χ a).toFun s z.2 * incomingValue F ζ hζ C R P H U ι a s v z) := by
  have hfirst : ContDiff ℝ (⊤ : ℕ∞) (deriv (χ a).toFun) :=
    (contDiff_infty_iff_deriv.mp (χ a).smooth).2
  have hsecond : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv (χ a).toFun)) :=
    (contDiff_infty_iff_deriv.mp hfirst).2
  have hc₁ := Complex.ofRealCLM.contDiff.comp (hfirst.comp
    (contDiff_snd : ContDiff ℝ (⊤ : ℕ∞) (Prod.snd : KPCuspCharts.Coordinates F → ℝ)))
  have hc₂ := Complex.ofRealCLM.contDiff.comp (hsecond.comp
    (contDiff_snd : ContDiff ℝ (⊤ : ℕ∞) (Prod.snd : KPCuspCharts.Coordinates F → ℝ)))
  exact (((contDiff_const.mul hc₂).add (contDiff_const.mul hc₁)).sub
    (contDiff_const.mul hc₁)).mul (incomingValue_contDiff F ζ hζ C R P H U ι a s hs v)

theorem incomingValue_stabilizer (a : Cusps F ζ hζ C R P H U)
    (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (v : S)
    (g : KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U a)
    (z : KPCuspCharts.Coordinates F) :
    (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ
      (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U a g) : ℂ) *
        incomingValue F ζ hζ C R P H U ι a s v z =
      incomingValue F ζ hζ C R P H U ι a s v z := by
  rw [incomingValue_height_formula F ζ hζ C R P H U ι a s hs v z]
  change _ * (_ * KPContFlatCuspIncomingEvaluation.projectedScalar F ζ hζ C R P H U a
    (KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U a ι s v)) = _
  rw [mul_left_comm]
  exact congrArg (fun b => KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s z.2 * b)
    (KPContFlatCuspIncomingEvaluation.projectedScalar_stabilizer F ζ hζ C R P H U a ι s hs v g)

theorem section_support_of_commutator_formula
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (f : ℂ → S) (s : ℂ) (w : SmoothSections F ζ hζ C R P H U)
    (hw : scalar F ζ hζ C R P H U w = commutatorScalar F ζ hζ C R P H U ι B χ f s) :
    tsupport (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ
      (level F ζ hζ C R P H U) R P H w.val) ⊆
      KPContActualCollarBuffer.collars F ζ hζ (level F ζ hζ C R P H U) R P H B.τ T := by
  let g := ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
    (level F ζ hζ C R P H U) R P H).symm w).val
  have hg : KPContSectorScalarLineAlgebra.S F ζ hζ
      (level F ζ hζ C R P H U) R P H g = w.val := by
    exact congrArg Subtype.val ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
      (level F ζ hζ C R P H U) R P H).apply_symm_apply w)
  rw [← hg, KPContSectorSmoothFramesSupport.tsupport_sectionNorm]
  rintro x ⟨y, hy, rfl⟩
  have hy' : y ∈ tsupport (commutatorScalar F ζ hζ C R P H U ι B χ f s) := by
    change y ∈ tsupport (scalar F ζ hζ C R P H U w) at hy
    rwa [hw] at hy
  exact commutatorScalar_covered_support F ζ hζ C R P H U ι B χ f s hy'

def LiftCovariance (w : SmoothSections F ζ hζ C R P H U) : Prop :=
  (∀ (g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) (ε : rootsOfUnity 3 F),
    lift F ζ hζ C R P H U w (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g)) =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
        lift F ζ hζ C R P H U w (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) ∧
  (∀ (g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)
      (u : (level F ζ hζ C R P H U).toOpenSubgroup),
    lift F ζ hζ C R P H U w (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (g * (u.val : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ))) =
        lift F ζ hζ C R P H U w (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) ∧
  (∀ (g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)
      (k : KPContSectorArchSphericalFibers.KInfinity F),
    lift F ζ hζ C R P H U w (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val)) =
        lift F ζ hζ C R P H U w (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g))

private theorem split_cover (g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :
    ∃ (a : KPSmoothActualFlowData.GInfinity F)
      (c : KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ),
      g = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c := by
  let e := (PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ).choose
  obtain ⟨a, c, hac⟩ : ∃ a c, e.symm g = (a, c) := ⟨_, _, rfl⟩
  have h := e.apply_symm_apply g
  rw [hac] at h
  rw [(PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ).choose_spec.1] at h
  refine ⟨a, ⟨c.val, ?_⟩, h.symm⟩
  change c.val ∈ KPFiniteCuspAtlas.FiniteCover F ζ hζ
  rw [← KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_finiteSubgroup_eq]
  exact c.property

private theorem central_comm_cover (ε : rootsOfUnity 3 F)
    (g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :
    KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g =
      g * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε := by
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε, rfl⟩) g).symm

theorem lift_covariance (w : SmoothSections F ζ hζ C R P H U) :
    LiftCovariance F ζ hζ C R P H U w := by
  constructor
  · intro g ε
    obtain ⟨a, c, rfl⟩ := split_cover F ζ hζ g
    have he : KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε *
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c) =
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
          (KPCuspGenuineMonodromy.central F ζ hζ ε * c) := by
      rw [← mul_assoc, central_comm_cover, mul_assoc]
      rfl
    simp only [lift, Function.comp_apply]
    rw [he]
    change scalar F ζ hζ C R P H U w
      (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ (level F ζ hζ C R P H U)
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
          (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
            ((KPCuspGenuineMonodromy.central F ζ hζ ε * c :
              KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ) :
                KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)))) = _
    rw [KPContSectorQuotientRelationsComparison.piTilde_quotientMap,
      KPContSectorQuotientRelationsComparison.piTilde_quotientMap,
      ← KPContSectorCoveredQuotientVocabulary.z_mk]
    exact ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
      (level F ζ hζ C R P H U) R P H).symm w).val.property ε _
  · constructor
    · intro g u
      apply congrArg (scalar F ζ hζ C R P H U w)
      unfold KPContSectorQuotientRelationsComparison.piTilde
      apply congrArg (KPContSectorQuotientRelationsComparison.e F ζ hζ
        (level F ζ hζ C R P H U))
      rw [KPContSectorCoveredQuotientVocabulary.coveredActualMap_mk,
        KPContSectorCoveredQuotientVocabulary.coveredActualMap_mk]
      apply Eq.symm
      apply DoubleCoset.eq.mpr
      refine ⟨1, Subgroup.one_mem _, u.val, ?_, by simp⟩
      apply Subgroup.subset_closure
      exact Set.mem_union_right _ ⟨u.val, u.property, rfl⟩
    · intro g k
      apply congrArg (scalar F ζ hζ C R P H U w)
      unfold KPContSectorQuotientRelationsComparison.piTilde
      apply congrArg (KPContSectorQuotientRelationsComparison.e F ζ hζ
        (level F ζ hζ C R P H U))
      rw [KPContSectorCoveredQuotientVocabulary.coveredActualMap_mk,
        KPContSectorCoveredQuotientVocabulary.coveredActualMap_mk]
      apply Eq.symm
      apply DoubleCoset.eq.mpr
      refine ⟨1, Subgroup.one_mem _, KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val,
        ?_, by simp⟩
      apply Subgroup.subset_closure
      exact Set.mem_union_left _ ⟨k.val, k.property, rfl⟩

private theorem deriv_zero_below {A : ℝ} (φ : ℝ → ℝ)
    (hzero : ∀ t, t ≤ A → φ t = 0) (t : ℝ) (ht : t ≤ A) : deriv φ t = 0 := by
  have hc : HasDerivWithinAt φ 0 (Set.Iic t) t :=
    (hasDerivWithinAt_const t (Set.Iic t) (0 : ℝ)).congr
      (fun x hx => hzero x (le_trans hx ht)) (hzero t ht)
  exact hc.deriv_eq_zero (uniqueDiffWithinAt_Iic t)

private theorem incoming_multiplier_smooth (d : ℕ)
    (χ : KPCutoffSource.SmoothCuspCutoff T) (s : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (KPCutoffSource.incomingCommutatorMultiplier d χ.toFun s) := by
  have h₁ := (contDiff_infty_iff_deriv.mp χ.smooth).2
  have h₂ := (contDiff_infty_iff_deriv.mp h₁).2
  have hc₁ := Complex.ofRealCLM.contDiff.comp h₁
  have hc₂ := Complex.ofRealCLM.contDiff.comp h₂
  exact ((contDiff_const.mul hc₂).add (contDiff_const.mul hc₁)).sub
    (contDiff_const.mul hc₁)

private theorem incoming_multiplier_zero_below (d : ℕ)
    (χ : KPCutoffSource.SmoothCuspCutoff T) (s : ℂ) (t : ℝ) (ht : t ≤ T) :
    KPCutoffSource.incomingCommutatorMultiplier d χ.toFun s t = 0 := by
  have h₁ := deriv_zero_below χ.toFun χ.zero_below t ht
  have h₂ := deriv_zero_below (deriv χ.toFun)
    (deriv_zero_below χ.toFun χ.zero_below) t ht
  simp [KPCutoffSource.incomingCommutatorMultiplier, h₁, h₂]

private theorem incoming_sum_smooth_section (s : ℂ)
    (hs : s ∈ KPContinuation.spectralDomain) (v : S)
    (φ : Cusps F ζ hζ C R P H U → ℝ → ℂ)
    (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a))
    (hzero : ∀ a t, t ≤ T → φ a t = 0) :
    ∃ w : SmoothSections F ζ hζ C R P H U,
      scalar F ζ hζ C R P H U w = fun x => ∑ a,
        (ends F ζ hζ C R P H U B a).indicator
          (fun y => φ a (height F ζ hζ C R P H U B a y) *
            incomingRealization F ζ hζ C R P H U ι B s v y) x := by
  choose g hg using (fun a => actual_incoming_smooth_zero_extension
    F ζ hζ C R P H U ι B a s hs v (φ a) (hφ a) (hzero a))
  refine ⟨KPContSectorSmoothFramesSupport.smoothS F ζ hζ
    (level F ζ hζ C R P H U) R P H (∑ a, g a), ?_⟩
  unfold scalar
  rw [LinearEquiv.symm_apply_apply]
  funext x
  simp only [Submodule.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun a _ => congrFun (hg a) x)

private theorem cutoff_commutator_sections_exist
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (f : ℂ → S) (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) :
    (∃ w : SmoothSections F ζ hζ C R P H U,
      scalar F ζ hζ C R P H U w = cutoffScalar F ζ hζ C R P H U ι B χ f s) ∧
    (∃ w : SmoothSections F ζ hζ C R P H U,
      scalar F ζ hζ C R P H U w = commutatorScalar F ζ hζ C R P H U ι B χ f s) := by
  constructor
  · obtain ⟨w, hw⟩ := incoming_sum_smooth_section F ζ hζ C R P H U ι B s hs (f s)
      (fun a t => ((χ a).toFun t : ℂ))
      (fun a => Complex.ofRealCLM.contDiff.comp (χ a).smooth)
      (fun a t ht => by simp [(χ a).zero_below t ht])
    refine ⟨w, hw.trans ?_⟩
    funext x
    simp only [cutoffScalar, KPCutoffSource.cutoffSum, Set.indicator_apply]
  · obtain ⟨w, hw⟩ := incoming_sum_smooth_section F ζ hζ C R P H U ι B s hs (f s)
      (fun a => KPCutoffSource.incomingCommutatorMultiplier (Module.finrank ℚ F / 2)
        (χ a).toFun s)
      (fun a => incoming_multiplier_smooth _ (χ a) s)
      (fun a => incoming_multiplier_zero_below _ (χ a) s)
    refine ⟨w, hw.trans ?_⟩
    funext x
    simp only [commutatorScalar, KPCutoffSource.commutatorSum, Set.indicator_apply]

structure Descent (Ω : Set ℂ) (f : ℂ → S)
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T) where
  cutoff : ℂ → SmoothSections F ζ hζ C R P H U
  commutator : ℂ → SmoothSections F ζ hζ C R P H U
  cutoff_formula : ∀ s ∈ Ω, scalar F ζ hζ C R P H U (cutoff s) =
    cutoffScalar F ζ hζ C R P H U ι B χ f s
  commutator_formula : ∀ s ∈ Ω, scalar F ζ hζ C R P H U (commutator s) =
    commutatorScalar F ζ hζ C R P H U ι B χ f s

  cutoff_lift : ∀ s ∈ Ω, ∀ x,
    lift F ζ hζ C R P H U (cutoff s) x =
      KPCutoffSource.cutoffSum (ends F ζ hζ C R P H U B) (height F ζ hζ C R P H U B)
        (fun a => (χ a).toFun) (incomingRealization F ζ hζ C R P H U ι B) f s
        (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ (level F ζ hζ C R P H U) x)
  commutator_lift : ∀ s ∈ Ω, ∀ x,
    lift F ζ hζ C R P H U (commutator s) x =
      KPCutoffSource.commutatorSum (Module.finrank ℚ F / 2)
        (ends F ζ hζ C R P H U B) (height F ζ hζ C R P H U B)
        (fun a => (χ a).toFun) (incomingRealization F ζ hζ C R P H U ι B) f s
        (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ (level F ζ hζ C R P H U) x)

  incoming_lift_formula : ∀ s ∈ Ω, ∀ (v : S) a ε z, B.τ < z.2 →
    incomingRealization F ζ hζ C R P H U ι B s v
      (coveredPoint F ζ hζ C R P H U a ε z) =
        (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
          incomingValue F ζ hζ C R P H U ι a s v z
  incoming_height_formula : ∀ (s : ℂ) (hs : s ∈ Ω) (hΩ : Ω ⊆ KPContinuation.spectralDomain)
      (v : S) a z,
    incomingValue F ζ hζ C R P H U ι a s v z =
      KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s z.2 *
        ((KPContFlatCuspIncomingEvaluation.b F ζ hζ C R P H U a ι s (hΩ hs) v).val
          z.1.2).val (QuotientAddGroup.mk z.1.1)
  cutoff_frame : ∀ s ∈ Ω, ∀ a z, B.τ < z.2 →
    frameValue F ζ hζ C R P H U (cutoff s) a z =
      ((χ a).toFun z.2 : ℂ) * incomingValue F ζ hζ C R P H U ι a s (f s) z
  commutator_frame : ∀ s ∈ Ω, ∀ a z, B.τ < z.2 →
    frameValue F ζ hζ C R P H U (commutator s) a z =
      KPCutoffSource.incomingCommutatorMultiplier (Module.finrank ℚ F / 2)
        (χ a).toFun s z.2 * incomingValue F ζ hζ C R P H U ι a s (f s) z
  cutoff_sheet : ∀ s ∈ Ω, ∀ a ε z, B.τ < z.2 →
    scalar F ζ hζ C R P H U (cutoff s) (coveredPoint F ζ hζ C R P H U a ε z) =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
        (((χ a).toFun z.2 : ℂ) * incomingValue F ζ hζ C R P H U ι a s (f s) z)
  commutator_sheet : ∀ s ∈ Ω, ∀ a ε z, B.τ < z.2 →
    scalar F ζ hζ C R P H U (commutator s) (coveredPoint F ζ hζ C R P H U a ε z) =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
        (KPCutoffSource.incomingCommutatorMultiplier (Module.finrank ℚ F / 2)
          (χ a).toFun s z.2 * incomingValue F ζ hζ C R P H U ι a s (f s) z)
  covariance : ∀ s ∈ Ω, LiftCovariance F ζ hζ C R P H U (cutoff s) ∧
    LiftCovariance F ζ hζ C R P H U (commutator s)
  off_ends : ∀ s ∈ Ω, ∀ x, (∀ a, x ∉ ends F ζ hζ C R P H U B a) →
    scalar F ζ hζ C R P H U (cutoff s) x = 0 ∧
      scalar F ζ hζ C R P H U (commutator s) x = 0
  support : ∀ s ∈ Ω, tsupport
    (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ (level F ζ hζ C R P H U)
      R P H (commutator s).val) ⊆
        KPContActualCollarBuffer.collars F ζ hζ (level F ζ hζ C R P H U) R P H B.τ T
  covered_support : ∀ s ∈ Ω, tsupport (scalar F ζ hζ C R P H U (commutator s)) ⊆
    KPContActualCollarBuffer.coveredCollars F ζ hζ (level F ζ hζ C R P H U) R P H B.τ T
  tail : ∀ s ∈ Ω, ∀ a x, x ∈ ends F ζ hζ C R P H U B a →
    T + 1 ≤ height F ζ hζ C R P H U B a x →
      scalar F ζ hζ C R P H U (cutoff s) x =
        incomingRealization F ζ hζ C R P H U ι B s (f s) x
  tail_frame : ∀ s ∈ Ω, ∀ a z, B.τ < z.2 → T + 1 ≤ z.2 →
    frameValue F ζ hζ C R P H U (cutoff s) a z =
      incomingValue F ζ hζ C R P H U ι a s (f s) z

end DedekindZetaZeroFree.KPContActualCutoffSmoothDescent

namespace DedekindZetaZeroFree

theorem kp_cont_actual_cutoff_smooth_descent
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (_hR : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H)
    {T : ℝ} (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H T)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (hι : Function.Injective ι)
    (_hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (Ω : Set ℂ) (hΩ : Ω ⊆ KPContinuation.spectralDomain)
    (f : ℂ → S) (hf : DifferentiableOn ℂ f Ω)
    (χ : KPContActualCutoffSmoothDescent.Cusps F ζ hζ C R P H U →
      KPCutoffSource.SmoothCuspCutoff T) :
    Nonempty (KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι B Ω f χ) := by
  classical
  let cutoff (s : ℂ) : KPContActualCutoffSmoothDescent.SmoothSections F ζ hζ C R P H U :=
    if hs : s ∈ Ω then Classical.choose
      (KPContActualCutoffSmoothDescent.cutoff_commutator_sections_exist
        F ζ hζ C R P H U ι B χ f s (hΩ hs)).1 else 0
  let commutator (s : ℂ) : KPContActualCutoffSmoothDescent.SmoothSections F ζ hζ C R P H U :=
    if hs : s ∈ Ω then Classical.choose
      (KPContActualCutoffSmoothDescent.cutoff_commutator_sections_exist
        F ζ hζ C R P H U ι B χ f s (hΩ hs)).2 else 0
  have hc : ∀ s ∈ Ω, KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (cutoff s) =
      KPContActualCutoffSmoothDescent.cutoffScalar F ζ hζ C R P H U ι B χ f s := by
    intro s hs
    dsimp only [cutoff]
    rw [dif_pos hs]
    exact Classical.choose_spec (KPContActualCutoffSmoothDescent.cutoff_commutator_sections_exist
      F ζ hζ C R P H U ι B χ f s (hΩ hs)).1
  have hm : ∀ s ∈ Ω, KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (commutator s) =
      KPContActualCutoffSmoothDescent.commutatorScalar F ζ hζ C R P H U ι B χ f s := by
    intro s hs
    dsimp only [commutator]
    rw [dif_pos hs]
    exact Classical.choose_spec (KPContActualCutoffSmoothDescent.cutoff_commutator_sections_exist
      F ζ hζ C R P H U ι B χ f s (hΩ hs)).2
  have hin : ∀ s ∈ Ω, ∀ (v : S) a ε z, B.τ < z.2 →
      KPContActualCutoffSmoothDescent.incomingRealization F ζ hζ C R P H U ι B s v
        (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a ε z) =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
        KPContActualCutoffSmoothDescent.incomingValue F ζ hζ C R P H U ι a s v z := by
    intro s hs v a ε z hz
    exact KPContActualCutoffSmoothDescent.incomingRealization_eq_of_transport
      F ζ hζ C R P H U ι B s v
      (KPContActualCutoffSmoothDescent.actual_endLift_incoming_transport
        F ζ hζ C R P H U ι B s (hΩ hs) v) a ε z hz
  have hcf : ∀ s ∈ Ω, ∀ a z, B.τ < z.2 →
      KPContActualCutoffSmoothDescent.frameValue F ζ hζ C R P H U (cutoff s) a z =
        ((χ a).toFun z.2 : ℂ) *
          KPContActualCutoffSmoothDescent.incomingValue F ζ hζ C R P H U ι a s (f s) z := by
    intro s hs a z hz
    exact KPContActualCutoffSmoothDescent.cutoff_frame_of_incoming
      F ζ hζ C R P H U ι B χ f s (cutoff s) (hc s hs) a z hz
      (by simpa using hin s hs (f s) a 1 z hz)
  refine ⟨{
    cutoff := cutoff
    commutator := commutator
    cutoff_formula := hc
    commutator_formula := hm
    cutoff_lift := ?_
    commutator_lift := ?_
    incoming_lift_formula := hin
    incoming_height_formula := ?_
    cutoff_frame := hcf
    commutator_frame := ?_
    cutoff_sheet := ?_
    commutator_sheet := ?_
    covariance := ?_
    off_ends := ?_
    support := ?_
    covered_support := ?_
    tail := ?_
    tail_frame := ?_ }⟩
  · intro s hs x
    exact congrFun (hc s hs) _
  · intro s hs x
    exact congrFun (hm s hs) _
  · intro s hs hΩ' v a z
    exact KPContActualCutoffSmoothDescent.incomingValue_height_formula
      F ζ hζ C R P H U ι a s (hΩ' hs) v z
  · intro s hs a z hz
    exact KPContActualCutoffSmoothDescent.commutator_frame_of_incoming
      F ζ hζ C R P H U ι B χ f s (commutator s) (hm s hs) a z hz
      (by simpa using hin s hs (f s) a 1 z hz)
  · intro s hs a ε z hz
    exact KPContActualCutoffSmoothDescent.cutoff_sheet_of_incoming
      F ζ hζ C R P H U ι B χ f s (cutoff s) (hc s hs) a ε z hz
      (hin s hs (f s) a ε z hz)
  · intro s hs a ε z hz
    exact KPContActualCutoffSmoothDescent.commutator_sheet_of_incoming
      F ζ hζ C R P H U ι B χ f s (commutator s) (hm s hs) a ε z hz
      (hin s hs (f s) a ε z hz)
  · intro s hs
    exact ⟨KPContActualCutoffSmoothDescent.lift_covariance F ζ hζ C R P H U (cutoff s),
      KPContActualCutoffSmoothDescent.lift_covariance F ζ hζ C R P H U (commutator s)⟩
  · intro s hs x hx
    rw [hc s hs, hm s hs]
    exact KPContActualCutoffSmoothDescent.scalar_off_ends F ζ hζ C R P H U ι B χ f s x hx
  · intro s hs
    exact KPContActualCutoffSmoothDescent.section_support_of_commutator_formula
      F ζ hζ C R P H U ι B χ f s (commutator s) (hm s hs)
  · intro s hs
    rw [hm s hs]
    exact KPContActualCutoffSmoothDescent.commutatorScalar_covered_support
      F ζ hζ C R P H U ι B χ f s
  · intro s hs a x hx ht
    rw [hc s hs]
    exact KPContActualCutoffSmoothDescent.cutoffScalar_tail
      F ζ hζ C R P H U ι B χ f s a x hx ht
  · intro s hs a z hz ht
    rw [hcf s hs a z hz, (χ a).one_above z.2 ht, Complex.ofReal_one, one_mul]

end DedekindZetaZeroFree

end
