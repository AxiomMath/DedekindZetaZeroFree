module

public import DedekindZetaZeroFree.Analysis.ComplexAnalysis.CompactBanachDiskSeries
public import DedekindZetaZeroFree.Eisenstein.Continuation.RightJets.CompactChartRefinement
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.RaisingOperators.SphericalDerivativeReconstruction

@[expose] public section

noncomputable section
open scoped Classical NumberField
open Topology Filter

namespace DedekindZetaZeroFree.KPContActualCommonDiskRightHolomorphy

open KPContLocalNorm KPContActualChartRestrictionDensity
open KPContSectorCoveredQuotientVocabulary KPContSectorSmoothFramesSupport
open KPContSectorLineL2Isometry

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

abbrev Combination :=
  List (ℂ × List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)))

def lift (u : Sections F ζ hζ U R P H) :
    KPSmoothLocalQuotientCharts.ActualCover F ζ hζ → ℂ :=
  fun g => (scalarRepresentative F ζ hζ U R P H u).val
    (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g))

def rightCombination (D : Combination F)
    (f : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ → ℂ) :
    KPSmoothLocalQuotientCharts.ActualCover F ζ hζ → ℂ :=
  fun g => (D.map (fun t => t.1 *
    KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ t.2 f g)).sum

def baseProjection : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ →
    KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  fun g => q F ζ hζ U
    (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g))

def CoherentSeries (W : ℂ → smoothSections F ζ hζ U R P H)
    (b : ℕ → smoothSections F ζ hζ U R P H) (c : ℂ) (r : ℝ) : Prop :=
  ∀ A : KPContActualSmoothLineGluing.ChartBall F ζ hζ U R P H,
    SmoothPowerSeriesOn A.ball c r
      (fun j => KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H (b j).val A)
      (fun s => KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H (W s).val A)

structure CompactBaseCover
    (C : Set (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)) where
  count : ℕ
  chart : Fin count → KPContActualSmoothLineGluing.ChartBall F ζ hζ U R P H
  compact : Fin count → Set (Space (KPCuspLogShape.dimension F * 3))
  isCompact : ∀ j, IsCompact (compact j)
  contained : ∀ j, compact j ⊆ (chart j).ball.carrier
  base : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)
  base_compact : IsCompact base
  base_eq : base = ⋃ j, basePoint F ζ hζ U R P H (chart j).component '' compact j
  projection_contained : baseProjection F ζ hζ U '' C ⊆ base

structure CompactEstimate
    (C : Set (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)) (D : Combination F) where
  cover : CompactBaseCover F ζ hζ U R P H C
  constant : ℝ
  positive : 0 < constant
  seminorm_bound : ∀ (u : Sections F ζ hζ U R P H)
    (hu : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞)
      (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u (cover.chart j))
      (cover.chart j).ball.carrier),
    sSup ((fun g => ‖rightCombination F ζ hζ D (lift F ζ hζ U R P H u) g‖) '' C) ≤
      constant * ∑ j, compactJetSeminorm (KPContRightJets.combinationOrder D)
        (cover.chart j).ball (cover.compact j) (cover.isCompact j) (cover.contained j)
        (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u (cover.chart j)) (hu j)
  raw_bound : ∀ (u : Sections F ζ hζ U R P H),
    (∀ j, ContDiffOn ℝ (⊤ : ℕ∞)
      (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u (cover.chart j))
      (cover.chart j).ball.carrier) →
    ∀ B : ℝ, 0 ≤ B →
      (∀ j, ∀ α : MultiIndex (KPCuspLogShape.dimension F * 3)
          (KPContRightJets.combinationOrder D), ∀ x ∈ cover.compact j,
        ‖coordinateDerivative α
          (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u (cover.chart j)) x‖ ≤ B) →
      sSup ((fun g => ‖rightCombination F ζ hζ D (lift F ζ hζ U R P H u) g‖) '' C) ≤
        constant * B

def UniformRightSeries
    (C : Set (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)) (D : Combination F)
    (W : ℂ → smoothSections F ζ hζ U R P H)
    (b : ℕ → smoothSections F ζ hζ U R P H) (c : ℂ) (r : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t < r → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ M ≥ N, ∀ s ∈ Metric.closedBall c t, ∀ g ∈ C,
      ‖(∑ j ∈ Finset.range M, (s - c) ^ j *
          rightCombination F ζ hζ D (lift F ζ hζ U R P H (b j).val) g) -
        rightCombination F ζ hζ D (lift F ζ hζ U R P H (W s).val) g‖ < ε

def CompactRightHolomorphic
    (C : Set (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)) (hC : IsCompact C)
    (D : Combination F) (W : ℂ → smoothSections F ζ hζ U R P H)
    (b : ℕ → smoothSections F ζ hζ U R P H) (c : ℂ) (r : ℝ) : Prop :=
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  ∃ f : ℂ → ContinuousMap C ℂ, ∃ a : ℕ → ContinuousMap C ℂ,
    (∀ s ∈ Metric.ball c r, ∀ g : C,
      f s g = rightCombination F ζ hζ D (lift F ζ hζ U R P H (W s).val) g) ∧
    (∀ j, ∀ g : C,
      a j g = rightCombination F ζ hζ D (lift F ζ hζ U R P H (b j).val) g) ∧
    DifferentiableOn ℂ f (Metric.ball c r) ∧
    (∀ s ∈ Metric.ball c r, HasSum (fun j => (s - c) ^ j • a j) (f s)) ∧
    (∀ t : ℝ, 0 ≤ t → t < r → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ M ≥ N, ∀ s ∈ Metric.closedBall c t,
        ‖(∑ j ∈ Finset.range M, (s - c) ^ j • a j) - f s‖ < ε)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

private lemma coord_smooth {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    (u : Space n → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (l : List (Fin n)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l u) U := by
  induction l with
  | nil => exact hu
  | cons i l ih =>
    exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

private lemma coord_perm {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    (u : Space n → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    {l r : List (Fin n)} (hp : l.Perm r) :
    Set.EqOn (coordinateDerivativeList l u) (coordinateDerivativeList r u) U := by
  induction hp with
  | nil => intro x hx; rfl
  | cons i hp ih =>
    intro x hx
    have heq : coordinateDerivativeList _ u =ᶠ[nhds x] coordinateDerivativeList _ u :=
      Filter.Eventually.mono (hU.mem_nhds hx) fun y hy => ih hy
    exact congrArg (fun f : Space n →L[ℝ] ℂ => f (EuclideanSpace.single i 1)) heq.fderiv_eq
  | swap i j l =>
    intro x hx
    let f := coordinateDerivativeList l u
    have hf := coord_smooth hU u hu l
    have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
    have hd := hfd.differentiableOn (by simp)
    have hfx := (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
    have hdx := hd.differentiableAt (hU.mem_nhds hx)
    have hsym := second_derivative_symmetric_of_eventually_of_real
      (Filter.Eventually.mono (hU.mem_nhds hx) fun y hy =>
        ((hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy)).hasFDerivAt)
      hdx.hasFDerivAt (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    simp only [coordinateDerivativeList]
    rw [fderiv_clm_apply hdx (differentiableAt_const _),
      fderiv_clm_apply hdx (differentiableAt_const _)]
    simpa using hsym.symm
  | trans h1 h2 ih1 ih2 => exact fun x hx => (ih1 hx).trans (ih2 hx)

private lemma list_index {n k : ℕ} (l : List (Fin n)) (hl : l.length ≤ k) :
    ∃ α : MultiIndex n k, α.directions.Perm l := by
  classical
  have hsum : ∑ i : Fin n, l.count i = l.length := by
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.count_cons, beq_iff_eq]
      simp [Finset.sum_add_distrib, ih (by simpa using Nat.le_of_succ_le hl)]
  let α : MultiIndex n k := ⟨fun i => ⟨l.count i, Nat.lt_succ_of_le (List.count_le_length.trans hl)⟩,
    by simpa using hsum.trans_le hl⟩
  refine ⟨α, List.perm_iff_count.mpr ?_⟩
  intro i
  simp only [MultiIndex.directions, List.count_flatMap, Function.comp_def, List.count_replicate]
  change ((List.finRange n).map (fun j => if (j == i) = true then l.count j else 0)).sum = l.count i
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp
private lemma vector_decomp {n : ℕ} (v : Space n) :
    v = ∑ i : Fin n, (v i) • EuclideanSpace.single i 1 := by
  apply PiLp.ext
  intro j
  simp [EuclideanSpace.single, Pi.single_apply]

private lemma pull_deriv {n m : ℕ} {U : Set (Space m)} {V : Set (Space n)}
    (hU : IsOpen U) (hV : IsOpen V) (π : Space m → Space n)
    (hπ : ContDiffOn ℝ (⊤ : ℕ∞) π U) (himage : π '' U ⊆ V)
    (u : Space n → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u V)
    (l : List (Fin n)) (g : Space m) (hg : g ∈ U) (v : Space m) :
    fderiv ℝ (fun x => coordinateDerivativeList l u (π x)) g v =
      ∑ i : Fin n, ((fderiv ℝ π g v) i : ℂ) * coordinateDerivativeList (i :: l) u (π g) := by
  have hgV := himage ⟨g, hg, rfl⟩
  have hdπ := (hπ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hdu := ((coord_smooth hV u hu l).differentiableOn (by simp)).differentiableAt (hV.mem_nhds hgV)
  change fderiv ℝ (coordinateDerivativeList l u ∘ π) g v = _
  rw [fderiv_comp g hdu hdπ]
  change fderiv ℝ (coordinateDerivativeList l u) (π g) (fderiv ℝ π g v) = _
  conv_lhs => arg 2; rw [vector_decomp (fderiv ℝ π g v)]
  rw [map_sum]
  simp [coordinateDerivativeList]

private lemma word_expansion {n m b : ℕ} {U : Set (Space m)} {V : Set (Space n)}
    (hU : IsOpen U) (hV : IsOpen V) (π : Space m → Space n) (frame : Space m → ℂ)
    (fields : Fin b → Space m → Space m)
    (hπ : ContDiffOn ℝ (⊤ : ℕ∞) π U)
    (hframe : ContDiffOn ℝ (⊤ : ℕ∞) frame U)
    (hfields : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fields i) U)
    (himage : π '' U ⊆ V) (w : List (Fin b)) :
    ∃ ts : List ((Space m → ℂ) × List (Fin n)),
      (∀ t ∈ ts, ContDiffOn ℝ (⊤ : ℕ∞) t.1 U ∧ t.2.length ≤ w.length) ∧
      ∀ u : Space n → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) u V →
        ∀ g ∈ U, KPContRightJets.rightWord fields w (KPContRightJets.scalarLift π frame u) g =
          (ts.map (fun t => t.1 g * coordinateDerivativeList t.2 u (π g))).sum := by
  induction w with
  | nil =>
    refine ⟨[(frame, [])], ?_, ?_⟩
    · intro t ht; simp only [List.mem_singleton] at ht; subst t; exact ⟨hframe, by simp⟩
    · intro u hu g hg; simp [KPContRightJets.rightWord, KPContRightJets.scalarLift, coordinateDerivativeList]
  | cons i w ih =>
    obtain ⟨ts, hts, heq⟩ := ih
    let expand : ((Space m → ℂ) × List (Fin n)) → List ((Space m → ℂ) × List (Fin n)) :=
      fun t => (fun g => fderiv ℝ t.1 g (fields i g), t.2) ::
        (List.finRange n).map (fun j =>
          (fun g => t.1 g * ((fderiv ℝ π g (fields i g)) j : ℂ), j :: t.2))
    refine ⟨ts.flatMap expand, ?_, ?_⟩
    · intro t ht
      obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨hsm, hsl⟩ := hts s hs
      simp only [expand, List.mem_cons, List.mem_map] at ht
      rcases ht with rfl | ⟨j, hj, rfl⟩
      · exact ⟨(hsm.fderiv_of_isOpen hU (by simp)).clm_apply (hfields i), by simpa using hsl.trans (Nat.le_succ _)⟩
      · refine ⟨hsm.mul ?_, by simpa using Nat.succ_le_succ hsl⟩
        have hdπ : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ π) U := hπ.fderiv_of_isOpen hU (by simp)
        exact Complex.ofRealCLM.contDiff.comp_contDiffOn
          (((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn (hdπ.clm_apply (hfields i))))
    · intro u hu g hg
      have hevent : KPContRightJets.rightWord fields w (KPContRightJets.scalarLift π frame u) =ᶠ[nhds g]
          (fun x => (ts.map (fun t => t.1 x * coordinateDerivativeList t.2 u (π x))).sum) :=
        Filter.Eventually.mono (hU.mem_nhds hg) fun x hx => heq u hu x hx
      simp only [KPContRightJets.rightWord]
      rw [hevent.fderiv_eq]
      have term_deriv (s : (Space m → ℂ) × List (Fin n)) (hs : s ∈ ts) :
          fderiv ℝ (fun x => s.1 x * coordinateDerivativeList s.2 u (π x)) g (fields i g) =
          ((expand s).map (fun t => t.1 g * coordinateDerivativeList t.2 u (π g))).sum := by
        have hd1 := ((hts s hs).1.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
        have hdc := ((coord_smooth hV u hu s.2).comp hπ (fun x hx => himage ⟨x,hx,rfl⟩)).differentiableOn (by simp)
        dsimp only [Function.comp_def] at hdc
        rw [fderiv_fun_mul hd1 (hdc.differentiableAt (hU.mem_nhds hg))]
        simp only [add_apply, smul_apply, smul_eq_mul]
        rw [pull_deriv hU hV π hπ himage u hu s.2 g hg (fields i g)]
        simp only [expand, List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
        rw [← List.ofFn_eq_map, List.sum_ofFn]
        simp only [Finset.mul_sum]
        ring_nf
      have sum_deriv : ∀ ss : List ((Space m → ℂ) × List (Fin n)),
          (∀ s ∈ ss, s ∈ ts) →
          fderiv ℝ (fun x => (ss.map (fun t => t.1 x * coordinateDerivativeList t.2 u (π x))).sum) g (fields i g) =
          ((ss.flatMap expand).map (fun t => t.1 g * coordinateDerivativeList t.2 u (π g))).sum := by
        intro ss hss
        induction ss with
        | nil => simp
        | cons s ss ih =>
          have hs := hss s (by simp)
          have hterm (t) (ht : t ∈ ss) := (hts t (hss t (by simp [ht]))).1.mul
            ((coord_smooth hV u hu t.2).comp hπ (fun x hx => himage ⟨x,hx,rfl⟩))
          have list_smooth : ∀ ll : List ((Space m → ℂ) × List (Fin n)),
              (∀ t ∈ ll, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => t.1 x * coordinateDerivativeList t.2 u (π x)) U) →
              ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (ll.map (fun t => t.1 x * coordinateDerivativeList t.2 u (π x))).sum) U := by
            intro ll hall
            induction ll with
            | nil => exact contDiffOn_const
            | cons t ll ih =>
              exact (hall t (by simp)).add (ih (fun z hz => hall z (by simp [hz])))
          have htail := list_smooth ss hterm
          have hhead := (hts s hs).1.mul ((coord_smooth hV u hu s.2).comp hπ (fun x hx => himage ⟨x,hx,rfl⟩))
          dsimp only [Function.comp_def] at hhead
          simp only [List.map_cons, List.sum_cons]
          rw [fderiv_fun_add (hhead.differentiableOn (by simp) |>.differentiableAt (hU.mem_nhds hg))
            (htail.differentiableOn (by simp) |>.differentiableAt (hU.mem_nhds hg))]
          simp only [add_apply, List.flatMap_cons, List.map_append, List.sum_append]
          rw [term_deriv s hs, ih (fun t ht => hss t (by simp [ht]))]
      exact sum_deriv ts (fun _ h => h)

private lemma word_congr {m b : ℕ} {V : Set (Space m)} (hV : IsOpen V)
    (fields : Fin b → Space m → Space m) (w : List (Fin b))
    {f g : Space m → ℂ} (h : Set.EqOn f g V) :
    Set.EqOn (KPContRightJets.rightWord fields w f) (KPContRightJets.rightWord fields w g) V := by
  induction w with
  | nil => exact h
  | cons i w ih =>
    intro x hx
    have he : KPContRightJets.rightWord fields w f =ᶠ[nhds x]
        KPContRightJets.rightWord fields w g :=
      Filter.Eventually.mono (hV.mem_nhds hx) fun y hy => ih hy
    exact congrArg (fun d : Space m →L[ℝ] ℂ => d (fields i x)) he.fderiv_eq

private lemma word_smooth {m b : ℕ} {V : Set (Space m)} (hV : IsOpen V)
    (fields : Fin b → Space m → Space m)
    (hfields : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fields i) V)
    (w : List (Fin b)) (f : Space m → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V) :
    ContDiffOn ℝ (⊤ : ℕ∞) (KPContRightJets.rightWord fields w f) V := by
  induction w with
  | nil => exact hf
  | cons i w ih => exact (ih.fderiv_of_isOpen hV (by simp)).clm_apply (hfields i)

private lemma jets_lower {n k l : ℕ} (hkl : k ≤ l)
    (u : Space n → ℂ) (K : Set (Space n)) (B : ℝ)
    (h : ∀ α : MultiIndex n l, ∀ x ∈ K, ‖coordinateDerivative α u x‖ ≤ B) :
    ∀ α : MultiIndex n k, ∀ x ∈ K, ‖coordinateDerivative α u x‖ ≤ B := by
  intro α x hx
  let β : MultiIndex n l := ⟨fun i => ⟨(α.val i).val,
    lt_of_lt_of_le (α.val i).isLt (Nat.add_le_add_right hkl 1)⟩, le_trans α.property hkl⟩
  exact h β x hx

private lemma word_bound {n m b : ℕ} {V : Set (Space m)} {T : Set (Space n)}
    (hV : IsOpen V) (hT : IsOpen T) (π : Space m → Space n) (frame : Space m → ℂ)
    (fields : Fin b → Space m → Space m)
    (hπ : ContDiffOn ℝ (⊤ : ℕ∞) π V) (hf : ContDiffOn ℝ (⊤ : ℕ∞) frame V)
    (hfields : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fields i) V) (himage : Set.MapsTo π V T)
    (K : Set (Space m)) (hK : IsCompact K) (hKV : K ⊆ V) (w : List (Fin b)) :
    ∃ A : ℝ, 0 < A ∧ ∀ u : Space n → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) u T →
      ∀ B : ℝ, 0 ≤ B →
      (∀ α : MultiIndex n w.length, ∀ x ∈ π '' K, ‖coordinateDerivative α u x‖ ≤ B) →
      ∀ x ∈ K, ‖KPContRightJets.rightWord fields w (KPContRightJets.scalarLift π frame u) x‖ ≤ A * B := by
  obtain ⟨ts, hts, heq⟩ := word_expansion hV hT π frame fields hπ hf hfields
    (by rintro _ ⟨x,hx,rfl⟩; exact himage hx) w
  have hsum : ContinuousOn (fun x => (ts.map (fun t => ‖t.1 x‖)).sum) K := by
    have aux : ∀ ss : List ((Space m → ℂ) × List (Fin n)), (∀ s ∈ ss, s ∈ ts) →
        ContinuousOn (fun x => (ss.map (fun t => ‖t.1 x‖)).sum) K := by
      intro ss hs
      induction ss with
      | nil => exact continuousOn_const
      | cons s ss ih =>
        exact ((hts s (hs s (by simp))).1.continuousOn.mono hKV).norm.add
          (ih (fun t ht => hs t (by simp [ht])))
    exact aux ts (fun _ h => h)
  obtain ⟨M,hM⟩ := hK.bddAbove_image hsum
  refine ⟨max 0 M + 1, by positivity, ?_⟩
  intro u hu B hB hj x hx
  rw [heq u hu x (hKV hx)]
  have hjlist (t : (Space m → ℂ) × List (Fin n)) (ht : t ∈ ts) :
      ‖coordinateDerivativeList t.2 u (π x)‖ ≤ B := by
    obtain ⟨α,hα⟩ := list_index t.2 (hts t ht).2
    rw [← coord_perm hT u hu hα (himage (hKV hx))]
    exact hj α (π x) ⟨x,hx,rfl⟩
  have aux : ∀ ss : List ((Space m → ℂ) × List (Fin n)), (∀ t ∈ ss, t ∈ ts) →
      ‖(ss.map (fun t => t.1 x * coordinateDerivativeList t.2 u (π x))).sum‖ ≤
        (ss.map (fun t => ‖t.1 x‖)).sum * B := by
    intro ss hall
    induction ss with
    | nil => simp
    | cons t ss ih =>
      simp only [List.map_cons,List.sum_cons,add_mul]
      exact (norm_add_le _ _).trans (add_le_add
        (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hjlist t (hall t (by simp))) (norm_nonneg _))
        (ih (fun s hs => hall s (by simp [hs]))))
  exact (aux ts (fun _ h => h)).trans (mul_le_mul_of_nonneg_right
    ((hM ⟨x,hx,rfl⟩).trans ((le_max_right 0 M).trans (le_add_of_nonneg_right zero_le_one))) hB)

private lemma combination_bound {n m b : ℕ} {V : Set (Space m)} {T : Set (Space n)}
    (hV : IsOpen V) (hT : IsOpen T) (π : Space m → Space n) (frame : Space m → ℂ)
    (fields : Fin b → Space m → Space m)
    (hπ : ContDiffOn ℝ (⊤ : ℕ∞) π V) (hf : ContDiffOn ℝ (⊤ : ℕ∞) frame V)
    (hfields : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fields i) V) (himage : Set.MapsTo π V T)
    (K : Set (Space m)) (hK : IsCompact K) (hKV : K ⊆ V)
    (D : List (ℂ × List (Fin b))) :
    ∃ A : ℝ, 0 < A ∧ ∀ u : Space n → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) u T →
      ∀ B : ℝ, 0 ≤ B →
      (∀ α : MultiIndex n (KPContRightJets.combinationOrder D), ∀ x ∈ π '' K,
        ‖coordinateDerivative α u x‖ ≤ B) →
      ∀ x ∈ K, ‖KPContRightJets.rightCombination fields D (KPContRightJets.scalarLift π frame u) x‖ ≤ A * B := by
  induction D with
  | nil => exact ⟨1,by norm_num,fun u hu B hB hj x hx => by simpa [KPContRightJets.rightCombination] using hB⟩
  | cons t ts ih =>
    obtain ⟨Aw,hAw,hw⟩ := word_bound hV hT π frame fields hπ hf hfields himage K hK hKV t.2
    obtain ⟨At,hAt,ht⟩ := ih
    refine ⟨‖t.1‖ * Aw + At, add_pos_of_nonneg_of_pos (mul_nonneg (norm_nonneg _) hAw.le) hAt, ?_⟩
    intro u hu B hB hj x hx
    have hw' := hw u hu B hB (jets_lower (by simp [KPContRightJets.combinationOrder]) u _ B hj) x hx
    have ht' := ht u hu B hB (jets_lower (by simp [KPContRightJets.combinationOrder]) u _ B hj) x hx
    simp only [KPContRightJets.rightCombination,List.map_cons,List.sum_cons]
    calc
      _ ≤ ‖t.1 * KPContRightJets.rightWord fields t.2 (KPContRightJets.scalarLift π frame u) x‖ +
          ‖KPContRightJets.rightCombination fields ts (KPContRightJets.scalarLift π frame u) x‖ := norm_add_le _ _
      _ ≤ ‖t.1‖ * (Aw * B) + At * B := by
        rw [norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_left hw' (norm_nonneg _)) ht'
      _ = _ := by ring

 lemma level_projection (u : U.toOpenSubgroup)
    (g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :
    KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (g * (u.val : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ))) =
    KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
  unfold KPContSectorQuotientRelationsComparison.piTilde
  dsimp only [Function.comp_def]
  rw [KPContSectorCoveredQuotientVocabulary.coveredActualMap_mk,
    KPContSectorCoveredQuotientVocabulary.coveredActualMap_mk]
  congr 1
  apply DoubleCoset.eq.mpr
  refine ⟨1, (KPContSectorCoveredQuotientVocabulary.Gamma F ζ hζ).one_mem,
    ((u.val : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)⁻¹), ?_, by simp⟩
  apply Subgroup.inv_mem
  exact Subgroup.subset_closure (Set.mem_union_right _ ⟨u.val,u.property,rfl⟩)

private lemma insertion_commutes (a : KPSmoothActualFlowData.GInfinity F)
    (v : FiniteCover F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a)
      (v.val : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) := by
  let e := (PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ).choose
  let v' : PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ :=
    ⟨v.val, by
      rw [KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_finiteSubgroup_eq F ζ hζ]
      exact v.property⟩
  have he := (PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ).choose_spec.1
  have ha : e (a,1) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a := by
    exact (he a 1).trans (mul_one _)
  have hv : e (1,v') = v.val := by
    have hh : e (1,v') = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ 1 * v.val := he 1 v'
    rw [(KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1, one_mul] at hh
    exact hh
  rw [← ha,← hv]
  exact (show Commute (a, (1 : PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ)) (1,v') from by
    change (a,1) * (1,v') = (1,v') * (a,1); simp).map e.toMonoidHom

private lemma word_level (u : U.toOpenSubgroup)
    (f : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ → ℂ)
    (hf : ∀ g, f (g * (u.val : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)) = f g)
    (w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))) :
    ∀ g, KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w f
      (g * (u.val : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)) =
      KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w f g := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    intro g
    unfold KPContActualSphericalRightFieldIdentification.actualRightWord
      KPContActualSphericalRightFieldIdentification.actualRight
    congr 1
    funext t
    rw [mul_assoc, (insertion_commutes F ζ hζ _ u.val).eq.symm, ← mul_assoc, ih]

private lemma piece_combination
    (p : KPContActualRightCanonicalRefinement.Piece (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H))
    (u : Sections F ζ hζ U R P H)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞)
      (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u p.chart) p.chart.ball.carrier)
    (D : Combination F) (x : Space (KPContActualSphericalRightFieldIdentification.groupDimension F))
    (hx : x ∈ p.openSet) (v : U.toOpenSubgroup) :
    rightCombination F ζ hζ D (lift F ζ hζ U R P H u)
      (p.group.groupLift x * (v.val : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)) =
    KPContRightJets.rightCombination p.group.fields D
      (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u p.chart ∘ p.projection) x := by
  have hs : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => lift F ζ hζ U R P H u (p.group.groupLift y)) p.openSet :=
    (hu.comp p.smooth_projection p.projection_inside).congr (fun y hy => p.scalar_formula u y hy)
  unfold rightCombination KPContRightJets.rightCombination
  congr 1
  apply List.map_congr_left
  intro t ht
  congr 1
  rw [word_level F ζ hζ U v _ (fun g =>
    congrArg (fun z => (scalarRepresentative F ζ hζ U R P H u).val z)
      (level_projection F ζ hζ U v g))]
  rw [p.local_word _ hs t.2 x hx]
  exact word_congr p.isOpen p.group.fields t.2 (p.scalar_formula u) hx

private lemma coefficient_smooth (u : smoothSections F ζ hζ U R P H)
    (A : KPContActualSmoothLineGluing.ChartBall F ζ hζ U R P H) :
    ContDiff ℝ (⊤ : ℕ∞) (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u.val A) := by
  unfold KPContActualSmoothLineGluing.coefficient frameCoefficient
  rw [scalarRepresentative_eq_symm, LinearEquiv.apply_symm_apply]
  obtain ⟨ε,hε⟩ := Quotient.exists_rep A.phase
  rw [← hε]
  have he : (fun x => (liftFrame F ζ hζ U (coordinates F x)
      (phaseCoefficient F ζ hζ U R P H u.val A.component (Quotient.mk _ ε) (coordinates F x)) : ℂ)) =
      fun x => (chi F ζ hζ ε : ℂ) * (u.val A.component).val (coordinates F x) := by
    funext x
    exact phaseCoefficient_class F ζ hζ U R P H u.val A.component ε (coordinates F x)
  rw [he]
  exact contDiff_const.mul ((u.property A.component).comp
    (CoreChartLocalizers.CutoffConstruction.ChartDensityConstruction.coordinates_contDiff _))

private lemma piece_bound
    (p : KPContActualRightCanonicalRefinement.Piece (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H)) (D : Combination F) :
    ∃ A : ℝ, 0 < A ∧ ∀ u : Sections F ζ hζ U R P H,
      ContDiffOn ℝ (⊤ : ℕ∞)
        (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u p.chart) p.chart.ball.carrier →
      ∀ B : ℝ, 0 ≤ B →
      (∀ α : MultiIndex (KPCuspLogShape.dimension F * 3) (KPContRightJets.combinationOrder D),
        ∀ x ∈ p.projection '' p.compact,
          ‖coordinateDerivative α (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u p.chart) x‖ ≤ B) →
      ∀ g ∈ p.group.piece p.compact,
        ‖rightCombination F ζ hζ D (lift F ζ hζ U R P H u) g‖ ≤ A * B := by
  obtain ⟨A,hA,hbound⟩ := combination_bound p.isOpen Metric.isOpen_ball p.projection
    (fun _ => 1) p.group.fields p.smooth_projection contDiffOn_const p.fields_smooth
    p.projection_inside p.compact p.isCompact p.compact_inside D
  refine ⟨A,hA,?_⟩
  intro u hu B hB hj g hg
  obtain ⟨x,hx,v,rfl⟩ := hg
  rw [piece_combination F ζ hζ U R P H p u hu D x (p.compact_inside hx) v]
  have hh := hbound _ hu B hB hj x hx
  have he : KPContRightJets.scalarLift p.projection (fun _ => 1)
      (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u p.chart) =
      (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u p.chart ∘ p.projection) := by
    funext y; simp only [KPContRightJets.scalarLift,one_mul,Function.comp_def]
  rw [he] at hh
  exact hh

 def cover_of_pieces {n : ℕ}
    (p : Fin n → KPContActualRightCanonicalRefinement.Piece (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H))
    (C : Set (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ))
    (hp : C ⊆ ⋃ j, (p j).group.piece (p j).compact) :
    CompactBaseCover F ζ hζ U R P H C where
  count := n
  chart j := (p j).chart
  compact j := (p j).projection '' (p j).compact
  isCompact j := (p j).compact_projection
  contained j := by rintro _ ⟨x,hx,rfl⟩; exact (p j).projection_inside ((p j).compact_inside hx)
  base := ⋃ j, basePoint F ζ hζ U R P H (p j).chart.component '' ((p j).projection '' (p j).compact)
  base_compact := isCompact_iUnion (fun j => (p j).compact_projection.image
    (by
      have he : basePoint F ζ hζ U R P H (p j).chart.component =
          fun x => Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
            (coordinates F x,(H.atlas U).representative (p j).chart.component) := by
        funext x; exact (H.atlas U).components_formula _ _
      rw [he]
      exact continuous_quotient_mk'.comp ((coordinates F).continuous.prodMk continuous_const)))
  base_eq := rfl
  projection_contained := by
    rintro _ ⟨g,hg,rfl⟩
    obtain ⟨j,x,hx,v,rfl⟩ := Set.mem_iUnion.mp (hp hg)
    apply Set.mem_iUnion.mpr
    refine ⟨j,(p j).projection x,⟨x,hx,rfl⟩,?_⟩
    unfold baseProjection
    rw [level_projection F ζ hζ U v]
    exact ((p j).base_formula x ((p j).compact_inside hx)).symm

private lemma sup_bound {G : Type*} (C : Set G) (f : G → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ g ∈ C, ‖f g‖ ≤ B) : sSup ((fun g => ‖f g‖) '' C) ≤ B := by
  rcases C.eq_empty_or_nonempty with rfl | hC
  · simpa using hB
  · exact csSup_le (hC.image _) (by rintro _ ⟨g,hg,rfl⟩; exact h g hg)

private lemma jet_bound {n : ℕ} (l : ℕ) (T : LocalBall n) (K : Set (Space n))
    (hK : IsCompact K) (hKT : K ⊆ T.carrier) (u : Space n → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u T.carrier) (α : MultiIndex n l) (x : K) :
    ‖coordinateDerivative α u x‖ ≤ compactJetSeminorm l T K hK hKT u hu := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact (ContinuousMap.norm_coe_le_norm (compactJet T K hKT u hu α) x).trans
    (norm_le_pi_norm (compactJet (m := l) T K hKT u hu) α)

private lemma estimate_of_pieces {n : ℕ}
    (p : Fin n → KPContActualRightCanonicalRefinement.Piece (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H))
    (C : Set (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ))
    (hp : C ⊆ ⋃ j, (p j).group.piece (p j).compact) (D : Combination F) :
    Nonempty (CompactEstimate F ζ hζ U R P H C D) := by
  choose A hA hb using (fun j => piece_bound F ζ hζ U R P H (p j) D)
  let E := cover_of_pieces F ζ hζ U R P H p C hp
  let B : ℝ := 1 + ∑ j, A j
  have hB : 0 < B := by
    have hh : 0 ≤ ∑ j, A j := Finset.sum_nonneg (fun j _ => (hA j).le)
    dsimp [B]; linarith
  have hAj (j : Fin n) : A j ≤ B := by
    have hh := Finset.single_le_sum (fun j _ => (hA j).le) (Finset.mem_univ j)
    dsimp [B]; linarith
  have raw (u : Sections F ζ hζ U R P H)
      (hu : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞)
        (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u (E.chart j)) (E.chart j).ball.carrier)
      (b : ℝ) (hbb : 0 ≤ b)
      (hj : ∀ j, ∀ α : MultiIndex (KPCuspLogShape.dimension F * 3) (KPContRightJets.combinationOrder D),
        ∀ x ∈ E.compact j,
          ‖coordinateDerivative α (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u (E.chart j)) x‖ ≤ b) :
      sSup ((fun g => ‖rightCombination F ζ hζ D (lift F ζ hζ U R P H u) g‖) '' C) ≤ B * b := by
    apply sup_bound C _ (mul_nonneg hB.le hbb)
    intro g hg
    obtain ⟨j,hjC⟩ := Set.mem_iUnion.mp (hp hg)
    exact (hb j u (hu j) b hbb (hj j) g hjC).trans (mul_le_mul_of_nonneg_right (hAj j) hbb)
  refine ⟨{ cover := E, constant := B, positive := hB, raw_bound := raw, seminorm_bound := ?_ }⟩
  intro u hu
  let qj (j : Fin E.count) := compactJetSeminorm (KPContRightJets.combinationOrder D)
    (E.chart j).ball (E.compact j) (E.isCompact j) (E.contained j)
    (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u (E.chart j)) (hu j)
  have hqj (j : Fin E.count) : 0 ≤ qj j := by
    letI : CompactSpace (E.compact j) := isCompact_iff_compactSpace.mp (E.isCompact j)
    dsimp [qj,compactJetSeminorm]
    unfold jetMaxNorm
    exact norm_nonneg _
  apply raw u hu
  · exact Finset.sum_nonneg (fun j _ => hqj j)
  · intro j α x hx
    exact (jet_bound _ _ _ (E.isCompact j) (E.contained j) _ (hu j) α ⟨x,hx⟩).trans
      (Finset.single_le_sum (f := qj) (fun k _ => hqj k) (Finset.mem_univ j))

private lemma word_sum_sub {m b : ℕ} (T : Set (Space m)) (hT : IsOpen T)
    (fields : Fin b → Space m → Space m)
    (hfields : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fields i) T)
    (w : List (Fin b)) (s : Finset ℕ) (c : ℕ → ℂ)
    (f : ℕ → Space m → ℂ) (v : Space m → ℂ)
    (hf : ∀ q ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (f q) T)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v T) :
    ∀ g ∈ T,
      KPContRightJets.rightWord fields w (fun x => (∑ q ∈ s, c q * f q x) - v x) g =
        (∑ q ∈ s, c q * KPContRightJets.rightWord fields w (f q) g) - KPContRightJets.rightWord fields w v g := by
  induction w with
  | nil => intro g hg; rfl
  | cons i w ih =>
    intro g hg
    have hn := hT.mem_nhds hg
    have hd (q : ℕ) (hq : q ∈ s) :
        DifferentiableAt ℝ (KPContRightJets.rightWord fields w (f q)) g :=
      ((word_smooth hT fields hfields w _ (hf q hq)).differentiableOn
        (by simp)).differentiableAt hn
    have hdv : DifferentiableAt ℝ (KPContRightJets.rightWord fields w v) g :=
      ((word_smooth hT fields hfields w _ hv).differentiableOn
        (by simp)).differentiableAt hn
    have heq : KPContRightJets.rightWord fields w (fun x => (∑ q ∈ s, c q * f q x) - v x) =ᶠ[
        nhds g] (fun x => (∑ q ∈ s, c q * KPContRightJets.rightWord fields w (f q) x) -
          KPContRightJets.rightWord fields w v x) := Filter.Eventually.mono hn (fun x hx => ih x hx)
    simp only [KPContRightJets.rightWord]
    rw [heq.fderiv_eq, fderiv_fun_sub
      (DifferentiableAt.fun_sum (fun q hq => (hd q hq).const_mul (c q))) hdv,
      fderiv_fun_sum (fun q hq => (hd q hq).const_mul (c q))]
    simp only [sub_apply, sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    rw [fderiv_const_mul (hd q hq)]
    rfl

private lemma combination_sum_sub {m b : ℕ} (T : Set (Space m)) (hT : IsOpen T)
    (fields : Fin b → Space m → Space m)
    (hfields : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fields i) T)
    (D : List (ℂ × List (Fin b))) (s : Finset ℕ) (c : ℕ → ℂ)
    (f : ℕ → Space m → ℂ) (v : Space m → ℂ)
    (hf : ∀ q ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (f q) T)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v T) :
    ∀ x ∈ T,
      KPContRightJets.rightCombination fields D (fun y => (∑ q ∈ s, c q * f q y) - v y) x =
        (∑ q ∈ s, c q * KPContRightJets.rightCombination fields D (f q) x) -
          KPContRightJets.rightCombination fields D v x := by
  intro x hx
  induction D with
  | nil => simp [KPContRightJets.rightCombination]
  | cons t ts ih =>
    simp only [KPContRightJets.rightCombination,List.map_cons,List.sum_cons] at ih ⊢
    rw [word_sum_sub T hT fields hfields t.2 s c f v hf hv x hx, ih]
    simp only [mul_sub,mul_add,Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    simp only [mul_left_comm (t.1)]
    ring

private lemma piece_series
    (p : KPContActualRightCanonicalRefinement.Piece (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H)) (D : Combination F)
    (W : ℂ → smoothSections F ζ hζ U R P H) (b : ℕ → smoothSections F ζ hζ U R P H)
    (c : ℂ) (r : ℝ) (hc : CoherentSeries F ζ hζ U R P H W b c r) :
    UniformRightSeries F ζ hζ U R P H (p.group.piece p.compact) D W b c r := by
  obtain ⟨A,hA,he⟩ := combination_bound p.isOpen Metric.isOpen_ball p.projection
    (fun _ => 1) p.group.fields p.smooth_projection contDiffOn_const p.fields_smooth
    p.projection_inside p.compact p.isCompact p.compact_inside D
  intro t ht htr ε hε
  have hδ : 0 < ε / (2 * A) := div_pos hε (mul_pos (by norm_num) hA)
  obtain ⟨N,hN⟩ := (hc p.chart).2.2 (p.projection '' p.compact) p.compact_projection
    (by rintro _ ⟨x,hx,rfl⟩; exact p.projection_inside (p.compact_inside hx))
    (KPContRightJets.combinationOrder D) t ht htr (ε / (2*A)) hδ
  refine ⟨N,?_⟩
  intro M hM s hs g hg
  obtain ⟨x,hx,v,rfl⟩ := hg
  let a := fun j => KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H (b j).val p.chart
  let u := KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H (W s).val p.chart
  let tail := fun y => (∑ j ∈ Finset.range M, (s-c)^j * a j y) - u y
  have ha j : ContDiffOn ℝ (⊤ : ℕ∞) (a j) p.chart.ball.carrier := (hc p.chart).1 j
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) u p.chart.ball.carrier :=
    (hc p.chart).2.1 s (Metric.closedBall_subset_ball htr hs)
  have htail : ContDiffOn ℝ (⊤ : ℕ∞) tail p.chart.ball.carrier :=
    (ContDiffOn.sum (fun j _ => contDiffOn_const.mul (ha j))).sub hu
  have hbnd := he tail htail (ε / (2*A)) hδ.le
    (fun α y hy => (hN M hM s hs α ⟨y,hy⟩).le) x hx
  have hap j : ContDiffOn ℝ (⊤ : ℕ∞) (a j ∘ p.projection) p.openSet :=
    (ha j).comp p.smooth_projection p.projection_inside
  have hup : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ p.projection) p.openSet :=
    hu.comp p.smooth_projection p.projection_inside
  have hformula : KPContRightJets.scalarLift p.projection (fun _ => 1) tail =
      fun y => (∑ j ∈ Finset.range M, (s-c)^j * (a j ∘ p.projection) y) -
        (u ∘ p.projection) y := by funext y; simp [KPContRightJets.scalarLift,tail]
  rw [hformula,combination_sum_sub p.openSet p.isOpen p.group.fields p.fields_smooth D
    (Finset.range M) (fun j => (s-c)^j) (fun j => a j ∘ p.projection) (u ∘ p.projection)
    (fun j _ => hap j) hup x (p.compact_inside hx)] at hbnd
  have hbformula j : rightCombination F ζ hζ D (lift F ζ hζ U R P H (b j).val)
      (p.group.groupLift x * (v.val : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)) =
      KPContRightJets.rightCombination p.group.fields D (a j ∘ p.projection) x :=
    piece_combination F ζ hζ U R P H p (b j).val (ha j) D x (p.compact_inside hx) v
  rw [piece_combination F ζ hζ U R P H p (W s).val hu D x (p.compact_inside hx) v]
  simp_rw [hbformula]
  apply lt_of_le_of_lt hbnd
  have hh : A * (ε / (2*A)) = ε/2 := by field_simp
  rw [hh]; linarith

private lemma series_of_pieces {n : ℕ}
    (p : Fin n → KPContActualRightCanonicalRefinement.Piece (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H))
    (C : Set (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ))
    (hp : C ⊆ ⋃ j, (p j).group.piece (p j).compact) (D : Combination F)
    (W : ℂ → smoothSections F ζ hζ U R P H) (b : ℕ → smoothSections F ζ hζ U R P H)
    (c : ℂ) (r : ℝ) (hc : CoherentSeries F ζ hζ U R P H W b c r) :
    UniformRightSeries F ζ hζ U R P H C D W b c r := by
  intro t ht htr ε hε
  choose N hN using (fun j => piece_series F ζ hζ U R P H (p j) D W b c r hc t ht htr ε hε)
  refine ⟨Finset.univ.sup N,?_⟩
  intro M hM s hs g hg
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hp hg)
  exact hN j M ((Finset.le_sup (Finset.mem_univ j)).trans hM) s hs g hj

private lemma combination_smooth {m b : ℕ} (T : Set (Space m)) (hT : IsOpen T)
    (fields : Fin b → Space m → Space m)
    (hfields : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fields i) T)
    (D : List (ℂ × List (Fin b))) (f : Space m → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f T) :
    ContDiffOn ℝ (⊤ : ℕ∞) (KPContRightJets.rightCombination fields D f) T := by
  induction D with
  | nil => exact contDiffOn_const
  | cons t ts ih => exact (contDiffOn_const.mul (word_smooth hT fields hfields t.2 f hf)).add ih

private lemma piece_continuous
    (p : KPContActualRightCanonicalRefinement.Piece (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H)) (D : Combination F)
    (u : smoothSections F ζ hζ U R P H) :
    ContinuousOn (rightCombination F ζ hζ D (lift F ζ hζ U R P H u.val))
      (p.group.piece p.compact) := by
  letI : T2Space (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  letI : CompactSpace p.compact := isCompact_iff_compactSpace.mp p.isCompact
  letI : CompactSpace U.toOpenSubgroup := isCompact_iff_compactSpace.mp U.isCompact
  let φ : p.compact × U.toOpenSubgroup → p.group.piece p.compact := fun z =>
    ⟨p.group.groupLift z.1.val * (z.2.val : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ),
      ⟨z.1.val,z.1.property,z.2,rfl⟩⟩
  have hφ : Continuous φ := by
    apply Continuous.subtype_mk
    exact (((p.group.groupLift_continuous.mono
      (p.compact_inside.trans p.contained)).domRestrict).comp continuous_fst).mul
      ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd)
  have hsurj : Function.Surjective φ := by
    intro g
    obtain ⟨x,hx,v,hg⟩ := g.property
    exact ⟨(⟨x,hx⟩,v),Subtype.ext hg.symm⟩
  have hquot : IsQuotientMap φ := hφ.isClosedMap.isQuotientMap hφ hsurj
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hquot.continuous_iff.mpr
  have hcoef : ContDiffOn ℝ (⊤ : ℕ∞)
      (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u.val p.chart) p.chart.ball.carrier :=
    (coefficient_smooth F ζ hζ U R P H u p.chart).contDiffOn
  have hc := combination_smooth p.openSet p.isOpen p.group.fields p.fields_smooth D
    _ (hcoef.comp p.smooth_projection p.projection_inside)
  have hcomp : Continuous (fun z : p.compact × U.toOpenSubgroup =>
      KPContRightJets.rightCombination p.group.fields D
        (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u.val p.chart ∘ p.projection) z.1.val) :=
    ((hc.continuousOn.mono p.compact_inside).domRestrict).comp continuous_fst
  apply hcomp.congr
  intro z
  exact (piece_combination F ζ hζ U R P H p u.val hcoef D z.1.val
    (p.compact_inside z.1.property) z.2).symm

private lemma finite_compact_continuous {G : Type*} [TopologicalSpace G] [T2Space G]
    {ι : Type*} [Fintype ι] (K : ι → Set G) (hK : ∀ i, IsCompact (K i))
    (f : G → ℂ) (hf : ∀ i, ContinuousOn f (K i)) : ContinuousOn f (⋃ i, K i) := by
  have aux (S : Finset ι) : ContinuousOn f (⋃ i ∈ S, K i) ∧ IsCompact (⋃ i ∈ S, K i) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.set_biUnion_insert]
      exact ⟨(hf i).union_of_isClosed ih.1 (hK i).isClosed ih.2.isClosed,(hK i).union ih.2⟩
  simpa using (aux Finset.univ).1

 lemma continuous_of_pieces {n : ℕ}
    (p : Fin n → KPContActualRightCanonicalRefinement.Piece (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H))
    (C : Set (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ))
    (hp : C ⊆ ⋃ j, (p j).group.piece (p j).compact) (D : Combination F)
    (u : smoothSections F ζ hζ U R P H) :
    ContinuousOn (rightCombination F ζ hζ D (lift F ζ hζ U R P H u.val)) C := by
  letI : T2Space (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  exact (finite_compact_continuous (fun j => (p j).group.piece (p j).compact)
    (fun j => (p j).piece_compact) _ (fun j => piece_continuous F ζ hζ U R P H (p j) D u)).mono hp

end DedekindZetaZeroFree.KPContActualCommonDiskRightHolomorphy

namespace DedekindZetaZeroFree

open KPContSectorSmoothFramesSupport KPContActualCommonDiskRightHolomorphy

theorem kp_cont_actual_common_disk_right_holomorphy
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (_actual : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (O : Set ℂ) (_hO : IsOpen O)
    (W : ℂ → smoothSections F ζ hζ U R P H)
    (b : ℕ → smoothSections F ζ hζ U R P H)
    (c : ℂ) (r : ℝ) (_hr : 0 < r) (_disk : Metric.ball c r ⊆ O)
    (_coherent : CoherentSeries F ζ hζ U R P H W b c r) :
    ∀ (C : Set (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)) (hC : IsCompact C)
      (D : Combination F),
      Nonempty (CompactEstimate F ζ hζ U R P H C D) ∧
      UniformRightSeries F ζ hζ U R P H C D W b c r ∧
      CompactRightHolomorphic F ζ hζ U R P H C hC D W b c r := by
  intro C hC D
  obtain ⟨n,p,hp⟩ := KPContActualRightCanonicalRefinement.compact_refinement _actual C hC
  have hest := estimate_of_pieces F ζ hζ U R P H p C hp D
  have hseries := series_of_pieces F ζ hζ U R P H p C hp D W b c r _coherent
  refine ⟨hest,hseries,?_⟩
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let f : ℂ → ContinuousMap C ℂ := fun s =>
    ⟨fun g => rightCombination F ζ hζ D (lift F ζ hζ U R P H (W s).val) g,
      (continuous_of_pieces F ζ hζ U R P H p C hp D (W s)).domRestrict⟩
  let a : ℕ → ContinuousMap C ℂ := fun j =>
    ⟨fun g => rightCombination F ζ hζ D (lift F ζ hζ U R P H (b j).val) g,
      (continuous_of_pieces F ζ hζ U R P H p C hp D (b j)).domRestrict⟩
  have hh := KPContCompactBanachSeries.compact_pointwise_series f a c r _hr
    (fun t ht htr ε hε => by
      obtain ⟨N,hN⟩ := hseries t ht htr ε hε
      exact ⟨N,fun M hM s hs g => hN M hM s hs g.val g.property⟩)
  exact ⟨f,a,by intros; rfl,by intros; rfl,hh.1,hh.2.1,hh.2.2⟩

end DedekindZetaZeroFree

end
