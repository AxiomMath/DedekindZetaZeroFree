module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.FiniteCoefficientReconstruction
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.SmoothSupportedSections

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

open KPContSectorSmoothFramesSupport KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy

section CompactReconstruction
variable {X C : Type*} [MeasurableSpace X]
  [TopologicalSpace C] [CompactSpace C] [MeasurableSpace C] [BorelSpace C]
variable (μ : Measure X) (q : X → C) (hq : Measurable q)
  (a : X → ℂ) (ha : MemLp a 2 μ)

include hq ha in
 theorem reconstruction_memLp (f : ContinuousMap C ℂ) :
    MemLp (fun x => a x * f (q x)) 2 μ := by
  apply ha.of_le_mul (c := ‖f‖)
    (ha.aestronglyMeasurable.mul ((f.continuous.measurable.comp hq).aestronglyMeasurable))
  filter_upwards [] with x
  change ‖a x * f (q x)‖ ≤ ‖f‖ * ‖a x‖
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm f _) (norm_nonneg _)

 def reconstructionLinear : ContinuousMap C ℂ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (reconstruction_memLp μ q hq a ha f).toLp (fun x => a x * f (q x))
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (reconstruction_memLp μ q hq a ha (f+g)),
      MemLp.coeFn_toLp (reconstruction_memLp μ q hq a ha f),
      MemLp.coeFn_toLp (reconstruction_memLp μ q hq a ha g),
      Lp.coeFn_add ((reconstruction_memLp μ q hq a ha f).toLp _) ((reconstruction_memLp μ q hq a ha g).toLp _)] with x hfg hf hg hadd
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hfg, hf, hg]
    simp only [ContinuousMap.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (reconstruction_memLp μ q hq a ha (c • f)),
      MemLp.coeFn_toLp (reconstruction_memLp μ q hq a ha f),
      Lp.coeFn_smul c ((reconstruction_memLp μ q hq a ha f).toLp _)] with x hcf hf hsmul
    simp only [RingHom.id_apply]
    rw [hsmul]
    simp only [Pi.smul_apply]
    rw [hcf, hf]
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    ring

end CompactReconstruction

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem smooth_supported_mem_borelL2
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsCompact K)
    (v : Sections F ζ hζ U R P H)
    (hv : IsSmoothSections F ζ hζ U R P H v)
    (hs : tsupport (sectionNorm F ζ hζ U R P H v) ⊆ K) :
    v ∈ BorelL2Sections F ζ hζ U R P H := by
  have hc : ∀ i, Continuous (v i).val := fun i => (hv i).continuous
  have hs' : HasCompactSupport (sectionNorm F ζ hζ U R P H v) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hs
  have hscalar : HasCompactSupport (scalarRepresentative F ζ hζ U R P H v).val := by
    apply (hasCompactSupport_iff F ζ hζ U R P H _).mpr
    simpa [scalarRepresentative_eq_symm] using hs'
  have hlp := KPContSectorFixedMeasureLocalFiniteness.compactSupport_memLp
    F ζ hζ R U _ ((continuous_iff F ζ hζ U R P H v).mp hc) hscalar
  exact ⟨fun i => (hc i).measurable,
    (finite_integral_iff F ζ hζ U R P H v (fun i => (hc i).measurable)).mpr hlp⟩

theorem toSector_represents (b : BorelL2Sections F ζ hζ U R P H) :
    Represents (toSector F ζ hζ U R P H b) b.val := by
  exact ⟨MemLp.coeFn_toLp (representative_memLp F ζ hζ U R P H b), b, rfl, rfl⟩

theorem represents_unique {v : Sections F ζ hζ U R P H}
    {V W : KPContSectorClosedLpSubspace.H F ζ hζ R U}
    (hV : Represents V v) (hW : Represents W v) : V = W := by
  apply Subtype.ext
  apply Lp.ext
  exact hV.1.trans hW.1.symm

section Calculus
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
private lemma clm_iterated (T : E →L[ℂ] G) (j : ℂ → E) (O : Set ℂ) (hO : IsOpen O)
    (hj : DifferentiableOn ℂ j O) (k : ℕ) (s : ℂ) (hs : s ∈ O) :
    iteratedDerivWithin k (fun z => T (j z)) O s = T (iteratedDerivWithin k j O s) := by
  unfold iteratedDerivWithin
  exact congrArg (fun f => f (fun _ => 1)) (T.iteratedFDerivWithin_comp_left
    (hj.contDiffOn hO (n := (⊤ : WithTop ℕ∞)) s hs) hO.uniqueDiffOn hs (i := k) le_top)
private lemma jet_differentiable (j : ℂ → E) (O : Set ℂ) (hO : IsOpen O)
    (hj : DifferentiableOn ℂ j O) (k : ℕ) :
    DifferentiableOn ℂ (iteratedDerivWithin k j O) O := by
  have hd := (hj.contDiffOn hO (n := (⊤ : WithTop ℕ∞))).differentiableOn_iteratedFDerivWithin
    (by simp : (k : WithTop ℕ∞) < ⊤) hO.uniqueDiffOn
  exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ) E (fun _ => 1)).differentiable.comp_differentiableOn hd)
end Calculus

private lemma scalar_jets (w : ℂ → Sections F ζ hζ U R P H) (O : Set ℂ) (k : ℕ) (s : ℂ)
    (x : CoveredSpherical F ζ hζ U) :
    (scalarRepresentative F ζ hζ U R P H (pointwiseJets w O k s)).val x =
      iteratedDerivWithin k (fun z => (scalarRepresentative F ζ hζ U R P H (w z)).val x) O s := by
  obtain ⟨⟨i,v⟩,rfl⟩ := (KPContSectorPhaseComponentCharts.componentHomeomorph F ζ hζ U R P H).surjective x
  refine Quotient.inductionOn v ?_
  rintro ⟨m,y⟩
  refine Quotient.inductionOn m ?_
  intro e
  have hf : ∀ a : Sections F ζ hζ U R P H,
      (scalarRepresentative F ζ hζ U R P H a).val
        (KPContSectorPhaseComponentCharts.componentHomeomorph F ζ hζ U R P H
          ⟨i,Quotient.mk _ (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U e,y)⟩) =
      (chi F ζ hζ e : ℂ) * (a i).val y := by
    intro a
    have ht := phase_component_restriction F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H a) i
      (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U e) y
    have hS : KPContSectorScalarLineAlgebra.S F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H a) = a :=
      (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H).apply_symm_apply a
    rw [hS, phaseCoefficient_class] at ht
    exact ht
  have hf' : ∀ a : Sections F ζ hζ U R P H,
      (scalarRepresentative F ζ hζ U R P H a).val
        (KPContSectorPhaseComponentCharts.componentHomeomorph F ζ hζ U R P H
          ⟨i,Quotient.mk _ (Quotient.mk _ e,y)⟩) = (chi F ζ hζ e : ℂ) * (a i).val y := hf
  rw [hf']
  have he : (fun z => (scalarRepresentative F ζ hζ U R P H (w z)).val
      (KPContSectorPhaseComponentCharts.componentHomeomorph F ζ hζ U R P H
        ⟨i, Quotient.mk _ (Quotient.mk _ e,y)⟩)) = fun z => (chi F ζ hζ e : ℂ) * (w z i).val y := by
    funext z; exact hf (w z)
  rw [he, pointwiseJets_apply, iteratedDerivWithin_const_mul_field]

theorem parameter_jets_sector_classes_source
    (O : Set ℂ) (_hO : IsOpen O)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (_hK : IsCompact K)
    (w : ℂ → Sections F ζ hζ U R P H)
    (wk : ℕ → ℂ → Sections F ζ hζ U R P H)
    (_hwk0 : ∀ s ∈ O, wk 0 s = w s)
    (_hsupp : ∀ k s, s ∈ O → IsSmoothSections F ζ hζ U R P H (wk k s) ∧
      tsupport (sectionNorm F ζ hζ U R P H (wk k s)) ⊆ K)
    (_hderiv : ∀ k s, s ∈ O → ∀ i x,
      (wk k s i).val x = iteratedDerivWithin k (fun z => (w z i).val x) O s)
    (m : ℕ) (charts : Fin m → ActualChart (U := U) (H := H))
    (_cover : K ⊆ ⋃ i, (charts i).baseDomain)
    (_holomorphic : ∀ i, ChartHolomorphicOn (charts i) w O) :
    ∃ W : ℕ → ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U,
      (∀ k s, s ∈ O → Represents (W k s) (wk k s) ∧
        ∀ V : KPContSectorClosedLpSubspace.H F ζ hζ R U,
          Represents V (wk k s) → V = W k s) ∧
      (∀ k, DifferentiableOn ℂ (W k) O) ∧
      (∀ k s, s ∈ O → iteratedDerivWithin k (W 0) O s = W k s) ∧
      (∀ k (L : Set ℂ), IsCompact L → L ⊆ O →
        ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ L, ‖W k s‖ ≤ B) ∧
      (∀ k s, s ∈ O →
        (W k s : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) =ᵐ[coveredMeasure F ζ hζ R U]
        (fun x => iteratedDerivWithin k
          (fun z => (scalarRepresentative F ζ hζ U R P H (w z)).val x) O s)) := by
  obtain ⟨C,hC,hD,hcov,T,hT⟩ := finite_compact_coefficient_reconstruction_source K _hK m charts _cover
  letI : ∀ i, CompactSpace (C i) := fun i => isCompact_iff_compactSpace.mp (hC i)
  choose j hj he using fun i => _holomorphic i (C i) (hC i) (hD i) 0 (fun x => Fin.elim0 x)
  have he' : ∀ i s, s ∈ O → ∀ x : C i, j i s x = (isotropyChart (charts i)).coefficient (w s) x.val := by
    intro i s hs x
    simpa [iteratedFDerivWithin_zero_apply] using he i s hs x
  let J : ℂ → ((i : Fin m) → ContinuousMap (C i) ℂ) := fun s i => j i s
  have hJ : DifferentiableOn ℂ J O := differentiableOn_pi.mpr hj
  have hwpoint : ∀ k s, s ∈ O → wk k s = pointwiseJets w O k s := by
    intro k s hs
    funext i; apply Subtype.ext; funext x
    exact _hderiv k s hs i x
  let b : ∀ k s, s ∈ O → BorelL2Sections F ζ hζ U R P H := fun k s hs =>
    ⟨wk k s, smooth_supported_mem_borelL2 K _hK (wk k s) (_hsupp k s hs).1 (_hsupp k s hs).2⟩
  let W : ℕ → ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U := fun k s =>
    if hs : s ∈ O then toSector F ζ hζ U R P H (b k s hs) else 0
  have hrep : ∀ k s (hs : s ∈ O), Represents (W k s) (wk k s) := by
    intro k s hs
    simpa only [W, dite_eq_left hs] using toSector_represents (b k s hs)
  have hcoeff : ∀ k s (hs : s ∈ O) i (x : C i),
      iteratedDerivWithin k J O s i x = (isotropyChart (charts i)).coefficient (wk k s) x.val := by
    intro k s hs i x
    let E := ((i : Fin m) → ContinuousMap (C i) ℂ)
    let ev : E →L[ℂ] ℂ := (ContinuousMap.evalCLM ℂ x).comp (ContinuousLinearMap.proj i)
    have hd := clm_iterated ev J O _hO hJ k s hs
    change iteratedDerivWithin k (fun z => j i z x) O s = iteratedDerivWithin k J O s i x at hd
    rw [← hd, hwpoint k s hs, pointwiseJets_frame]
    exact iteratedDerivWithin_congr (n := k) (fun z hz => he' i z hz x) hs
  have hclass : ∀ k s (hs : s ∈ O), T (iteratedDerivWithin k J O s) =
      (W k s : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) := by
    intro k s hs
    have ht := hT (wk k s) (_hsupp k s hs).1 (_hsupp k s hs).2
      (iteratedDerivWithin k J O s) (hcoeff k s hs) (b k s hs) rfl
    simpa only [W, dite_eq_left hs] using ht
  let Pj := (KPContSectorClosedLpSubspace.H F ζ hζ R U).orthogonalProjectionOnto
  have hpr : ∀ k s (hs : s ∈ O), Pj (T (iteratedDerivWithin k J O s)) = W k s := by
    intro k s hs
    rw [hclass k s hs]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (W k s)
  have hdiff : ∀ k, DifferentiableOn ℂ (W k) O := by
    intro k
    exact (Pj.differentiable.comp_differentiableOn
      (T.differentiable.comp_differentiableOn (jet_differentiable J O _hO hJ k))).congr
        (fun s hs => (hpr k s hs).symm)
  refine ⟨W, (fun k s hs => ⟨hrep k s hs, fun V hV => represents_unique hV (hrep k s hs)⟩), hdiff, ?_, ?_, ?_⟩
  · intro k s hs
    have h0 : Set.EqOn (W 0) (fun z => Pj (T (J z))) O := by
      intro z hz
      simpa only [iteratedDerivWithin_zero] using (hpr 0 z hz).symm
    rw [iteratedDerivWithin_congr (n := k) h0 hs]
    change iteratedDerivWithin k (fun z => (Pj.comp T) (J z)) O s = W k s
    rw [clm_iterated (Pj.comp T) J O _hO hJ k s hs]
    exact hpr k s hs
  · intro k L hL hLO
    obtain ⟨B,hB⟩ := hL.exists_bound_of_continuousOn ((hdiff k).continuousOn.mono hLO)
    exact ⟨max 0 B, le_max_left _ _, fun s hs => (hB s hs).trans (le_max_right _ _)⟩
  · intro k s hs
    have hp := (hrep k s hs).1
    rw [hwpoint k s hs] at hp
    exact hp.trans (Filter.Eventually.of_forall (scalar_jets w O k s))

end DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

end
