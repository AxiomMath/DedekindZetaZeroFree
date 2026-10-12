module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Cotangent.IntrinsicL2Space

@[expose] public section

noncomputable section

open scoped Classical NumberField ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentChartZeroExtension
open KPContActualCotangentCountableShrinking KPContActualCotangentMeasurableFamilies
open KPContActualCotangentPieceHilbertSum KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy KPContCotangentActualOverlap
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

 def sectorTestOverlapEnumeration (b a : ShrunkChart F ζ hζ U R P H) :
    KPContCotangentCorrectedNullEquivalence.NonsingularEnumeration2 b a :=
  KPContCotangentCorrectedNullEquivalence.withNonsingularity2
    (Classical.choice (enumeration_exists b a))

private theorem coordinates_originalPoint_ext (a : ShrunkChart F ζ hζ U R P H) (x : omega a) :
    coordinates a (KPContActualCotangentPieceReconstruction.originalPoint a x) = x := by
  apply Subtype.ext
  simp [KPContActualCotangentPieceReconstruction.originalPoint, coordinates, labeledA, labeledAInv]

private lemma continuous_q (a : ShrunkChart F ζ hζ U R P H) : Continuous (q a) := by
  have hcm : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U
      ((H.atlas U).representative a.component)) := by
    have he : KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component) =
        (H.atlas U).components ∘ Sigma.mk a.component := by
      funext x; exact ((H.atlas U).components_formula a.component x).symm
    rw [he]
    exact ((H.atlas U).components.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk).continuous
  have hproj : Continuous (KPCuspSiegel.projection F
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)) :=
    continuous_quotient_mk'
  have hcomp : q a = KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)
      ∘ KPCuspSiegel.projection F (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)
      ∘ labeledA (placeEquiv F ζ hζ) := rfl
  rw [hcomp]
  exact hcm.comp (hproj.comp continuous_labeledA_placeEquiv)

private lemma T_symm_coord {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H) i}
    (ψ : Arrow a b) (x : M F) (hx : x ∈ ψ.domain) (w : E F)
    (k : Fin (d F) × Fin 3) :
    (T ψ x hx).symm w k =
      inner ℂ (twistedOperator ψ x (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k)) w := by
  have hb : T ψ x hx (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k)
      = twistedOperator ψ x (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k) := rfl
  have h1 : (T ψ x hx).symm w k
      = inner ℂ (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k) ((T ψ x hx).symm w) := by
    simpa using (EuclideanSpace.basisFun_inner (ι := Fin (d F) × Fin 3) (𝕜 := ℂ)
      ((T ψ x hx).symm w) k).symm
  rw [h1, ← inner_conj_symm]
  conv_lhs =>
    rw [← (T ψ x hx).symm_apply_apply (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k),
      LinearIsometryEquiv.inner_map_map (T ψ x hx).symm w
        (T ψ x hx (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k))]
  rw [inner_conj_symm, hb]

theorem extendedFields_zero_off_base_support (a : ShrunkChart F ζ hζ U R P H)
    (f : omega a → E F) (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (hfK : ∀ y : omega a, f y ≠ 0 → q a y.val ∈ K)
    (b : ShrunkChart F ζ hζ U R P H) (x : omega b) (hx : q b x.val ∉ K) :
    extendedFields a (liftField a f) b x = 0 := by
  by_cases hb : q b x.val ∈ a.baseDomain
  · dsimp only [extendedFields]
    rw [dite_eq_left hb]
    let k := Nat.find (directDomainExists b a x hb)
    let e := (sectorTestOverlapEnumeration b a).branch k
    have he : x.val ∈ e.domain := Nat.find_spec (directDomainExists b a x hb)
    have ht : e.psi x.val ∈ omega a := ((sectorTestOverlapEnumeration b a).properties k).target_subset ⟨x.val, he, rfl⟩
    have hz : f ⟨e.psi x.val, ht⟩ = 0 := by
      by_contra hn
      apply hx
      rw [← ((sectorTestOverlapEnumeration b a).properties k).quotient_compatibility x.val he]
      exact hfK _ hn
    change (e.transport x.val he).symm (liftField a f
      (KPContActualCotangentPieceReconstruction.originalPoint a ⟨e.psi x.val, ht⟩)) = 0
    rw [liftField, coordinates_originalPoint_ext, hz, map_zero]
  · exact extendedFields_zero_off a _ b x hb

set_option maxHeartbeats 1200000 in
theorem smooth_extended_base_support (a : ShrunkChart F ζ hζ U R P H)
    (f : omega a → E F) (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (hK : IsClosed K) (hKa : K ⊆ a.baseDomain)
    (hfK : ∀ y : omega a, f y ≠ 0 → q a y.val ∈ K)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) (ambientField a f) (omega a))
    (he : PointwiseEquivariant a (liftField a f))
    (b : ShrunkChart F ζ hζ U R P H) :
    ContDiffOn ℝ (⊤ : ℕ∞) (ambientField b (extendedFields a (liftField a f) b)) (omega b) := by
  intro x hx
  by_cases hb : q b x ∈ a.baseDomain
  · let z : omega b := ⟨x, hx⟩
    let k := Nat.find (directDomainExists b a z hb)
    let e := (sectorTestOverlapEnumeration b a).branch k
    have hx' : x ∈ e.domain := Nat.find_spec (directDomainExists b a z hb)
    have hat : ∀ (d : Branch b a) (hd : d.Properties), x ∈ d.domain →
        ContDiffAt ℝ (⊤ : ℕ∞) (ambientField b (extendedFields a (liftField a f) b)) x := by
      intro d hd hxd
      cases d with
      | none => exact False.elim hxd
      | some d =>
        let g : M F → E F := fun y => WithLp.toLp 2 (fun j => inner ℂ
          (twistedOperator d.arrow y (EuclideanSpace.basisFun _ ℂ j))
          (ambientField a f (d.arrow.psi y)))
        have hψ := (smooth_metric d.arrow).1.contDiffAt (d.arrow.isOpen_domain.mem_nhds hxd)
        have ht := (smooth_operators d.arrow).2.contDiffAt (d.arrow.isOpen_domain.mem_nhds hxd)
        have htarget := d.target_shrinking hxd
        have ho : IsOpen (omega a) := continuous_labeledA_placeEquiv.isOpen_preimage _ a.domain_open
        have hf := (hs.contDiffAt (ho.mem_nhds htarget)).comp x hψ
        have hg : ContDiffAt ℝ (⊤ : ℕ∞) g x := by
          apply (contDiffAt_piLp 2).mpr
          intro j
          have htR := (ContinuousLinearMap.restrictScalarsL ℂ (E F) (E F) ℝ ℝ).contDiff.contDiffAt.comp x ht
          exact (htR.clm_apply (contDiffAt_const (c := EuclideanSpace.basisFun _ ℂ j))).inner ℂ hf
        apply hg.congr_of_eventuallyEq
        filter_upwards [d.arrow.isOpen_domain.mem_nhds hxd] with y hy
        have hys := d.source_shrinking hy
        have hyt := d.target_shrinking hy
        have hc : Continuous f := by
          convert hs.continuousOn.restrict using 1
          funext w
          change f w = ambientField a f w.val
          rw [ambientField, dite_eq_left w.property]
        have hmeas : Measurable (liftField a f) := (hc.comp (coordinates_continuous a)).measurable
        rw [ambientField, dite_eq_left hys]
        rw [extendedFields_overlap a (liftField a f) hmeas he b d y hy]
        apply PiLp.ext
        intro j
        rw [T_symm_coord]
        dsimp only [g]
        rw [ambientField, dite_eq_left hyt, liftField, coordinates_originalPoint_ext]
    exact (hat e ((sectorTestOverlapEnumeration b a).properties k) hx').contDiffWithinAt
  · have hxq : q b x ∉ K := fun h => hb (hKa h)
    have hn : ∀ᶠ y in 𝓝 x, q b y ∉ K :=
      (hK.isOpen_compl.preimage (continuous_q b)).mem_nhds hxq
    apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_const (c := (0 : E F))).congr_of_eventuallyEq
    filter_upwards [hn] with y hy
    unfold ambientField
    split_ifs with hyb
    · exact extendedFields_zero_off_base_support a f K hfK b ⟨y, hyb⟩ hy
    · rfl

end DedekindZetaZeroFree.KPContActualCotangentChartZeroExtension

namespace DedekindZetaZeroFree.KPContActualSectorSmoothTestModules

open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
open KPContCotangentActualGenuineTwistIsotropy KPContCotangentOverlapRationalBranches
open KPContActualCotangentMeasurableFamilies KPContSectorSmoothFramesSupport
open KPContSectorScalarLineAlgebra KPContSectorCoveredQuotientVocabulary

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

abbrev ActualChart := ShrunkChart F ζ hζ U R P H

def SmoothOnLift {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (a : ActualChart (U := U) (H := H)) (f : omega a → W) : Prop :=
  ∃ g : M F → W, ContDiffOn ℝ (⊤ : ℕ∞) g (omega a) ∧ ∀ x : omega a, g x.val = f x

abbrev ScalarFields (F : Type) [Field F] [NumberField F] (ζ : F)
    (hζ : IsPrimitiveRoot ζ 12) (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) :=
  ∀ a : ShrunkChart F ζ hζ U R P H, omega a → ℂ

def ScalarEquivariant (a : ActualChart (U := U) (H := H)) (f : omega a → ℂ) : Prop :=
  ∀ (γ : Gamma a) (x : M F) (hx : x ∈ omega a),
    f ⟨(isotropyArrow a γ).psi x, isotropy_mem a γ x hx⟩ =
      (isotropyArrow a γ).phase x * f ⟨x, hx⟩

def ScalarCompatible (f : ScalarFields F ζ hζ U R P H) : Prop :=
  (∀ a, ScalarEquivariant a (f a)) ∧
  (∀ (a b : ActualChart (U := U) (H := H)) (e : ActualBranch a b)
      (x : M F) (hx : x ∈ e.arrow.domain),
    f b ⟨e.arrow.psi x, e.target_shrinking hx⟩ =
      e.arrow.phase x * f a ⟨x, e.source_shrinking hx⟩)

def scalarSupport (f : ScalarFields F ζ hζ U R P H) :
    Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  closure {x | ∃ (a : ActualChart (U := U) (H := H)) (y : omega a),
    q a y.val = x ∧ f a y ≠ 0}

theorem scalarSupport_add_subset (f g : ScalarFields F ζ hζ U R P H) :
    scalarSupport (f + g) ⊆ scalarSupport f ∪ scalarSupport g := by
  unfold scalarSupport
  rw [← closure_union]
  apply closure_mono
  rintro x ⟨a, y, hq, hne⟩
  by_cases hf : f a y = 0
  · exact Or.inr ⟨a, y, hq, fun hg => hne (by simp [hf, hg])⟩
  · exact Or.inl ⟨a, y, hq, hf⟩

theorem scalarSupport_smul_subset (c : ℂ) (f : ScalarFields F ζ hζ U R P H) :
    scalarSupport (c • f) ⊆ scalarSupport f := by
  apply closure_mono
  rintro x ⟨a, y, hq, hne⟩
  exact ⟨a, y, hq, fun hf => hne (by simp [hf])⟩

def scalarTests : Submodule ℂ (ScalarFields F ζ hζ U R P H) where
  carrier := {f | (∀ a, SmoothOnLift a (f a)) ∧ ScalarCompatible f ∧ IsCompact (scalarSupport f)}
  zero_mem' := by
    refine ⟨fun a => ⟨fun _ => 0, contDiffOn_const, fun _ => rfl⟩, ⟨?_, ?_⟩, ?_⟩
    · intro a γ x hx
      simp
    · intro a b e x hx
      simp
    · have hs : scalarSupport (0 : ScalarFields F ζ hζ U R P H) = ∅ := by
        simp only [scalarSupport, Pi.zero_apply, ne_eq, not_true_eq_false,
          and_false, exists_false, Set.setOf_false, closure_empty]
      rw [hs]
      exact isCompact_empty
  add_mem' := by
    intro f g hf hg
    have hs : scalarSupport (f + g) ⊆ scalarSupport f ∪ scalarSupport g := by
      unfold scalarSupport
      rw [← closure_union]
      apply closure_mono
      rintro x ⟨a, y, hq, hne⟩
      by_cases h : f a y = 0
      · exact Or.inr ⟨a, y, hq, fun hz => hne (by simp [h, hz])⟩
      · exact Or.inl ⟨a, y, hq, h⟩
    refine ⟨?_, ⟨?_, ?_⟩, (hf.2.2.union hg.2.2).of_isClosed_subset isClosed_closure hs⟩
    · intro a
      rcases hf.1 a with ⟨f', hf', hfl⟩
      rcases hg.1 a with ⟨g', hg', hgl⟩
      exact ⟨fun x => f' x + g' x, hf'.add hg', fun x => by simp [hfl, hgl]⟩
    · intro a γ x hx
      simp only [Pi.add_apply, hf.2.1.1 a γ x hx, hg.2.1.1 a γ x hx, mul_add]
    · intro a b e x hx
      simp only [Pi.add_apply, hf.2.1.2 a b e x hx, hg.2.1.2 a b e x hx, mul_add]
  smul_mem' := by
    intro c f hf
    have hs : scalarSupport (c • f) ⊆ scalarSupport f := by
      unfold scalarSupport
      apply closure_mono
      rintro x ⟨a, y, hq, hne⟩
      exact ⟨a, y, hq, fun hz => hne (by simp [hz])⟩
    refine ⟨?_, ⟨?_, ?_⟩, hf.2.2.of_isClosed_subset isClosed_closure hs⟩
    · intro a
      rcases hf.1 a with ⟨f', hf', hfl⟩
      exact ⟨fun x => c • f' x, hf'.const_smul c, fun x => by simp [hfl]⟩
    · intro a γ x hx
      simp only [Pi.smul_apply, smul_eq_mul, hf.2.1.1 a γ x hx]
      exact mul_left_comm _ _ _
    · intro a b e x hx
      simp only [Pi.smul_apply, smul_eq_mul, hf.2.1.2 a b e x hx]
      exact mul_left_comm _ _ _

abbrev S_U (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) :=
  ↥(scalarTests (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H))

def cotangentSupport (v : Family (U := U) (H := H)) :
    Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  closure {x | ∃ (a : ActualChart (U := U) (H := H)) (y : omega a),
    q a y.val = x ∧ coefficient v a y ≠ 0}

theorem exists_actual_lift (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∃ (a : ActualChart (U := U) (H := H)) (y : omega a), q a y.val = x := by
  let cover := Classical.choice
    (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  have hx : x ∈ ⋃ n, (cover.chart n).baseDomain := by rw [cover.covers]; trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  obtain ⟨z, hz⟩ := hn
  let y := labeledAInv (placeEquiv F ζ hζ) z.val
  have hy : labeledA (placeEquiv F ζ hζ) y = z.val := by
    funext k
    simp [y, labeledA, labeledAInv]
  refine ⟨cover.chart n, ⟨y, ?_⟩, ?_⟩
  · change labeledA (placeEquiv F ζ hζ) y ∈ (cover.chart n).domain
    rw [hy]
    exact z.property
  · change q (cover.chart n) y = x
    simpa only [KPContCotangentOverlapRationalBranches.q, hy, ShrunkChart.toBase] using hz

theorem cotangentSupport_eq (v : Family (U := U) (H := H)) :
    cotangentSupport v = tsupport (normSquare v) := by
  unfold cotangentSupport tsupport
  congr 1
  ext x
  constructor
  · rintro ⟨a, y, rfl, hne⟩
    simpa only [Function.mem_support, normSquare_chart, ne_eq, pow_eq_zero_iff,
      OfNat.ofNat_ne_zero, not_false_eq_true, NNReal.coe_eq_zero, nnnorm_eq_zero] using hne
  · intro hx
    obtain ⟨a, y, hq⟩ := exists_actual_lift x
    refine ⟨a, y, hq, ?_⟩
    rw [← hq] at hx
    simpa only [Function.mem_support, normSquare_chart, ne_eq, pow_eq_zero_iff,
      OfNat.ofNat_ne_zero, not_false_eq_true, NNReal.coe_eq_zero, nnnorm_eq_zero] using hx

theorem cotangentSupport_add (v w : Family (U := U) (H := H)) :
    cotangentSupport (v + w) ⊆ cotangentSupport v ∪ cotangentSupport w := by
  unfold cotangentSupport
  rw [← closure_union]
  apply closure_mono
  rintro x ⟨a, y, hq, hne⟩
  by_cases h : coefficient v a y = 0
  · exact Or.inr ⟨a, y, hq, fun hz => hne (by
      change coefficient v a y + coefficient w a y = 0
      simp only [h, hz, add_zero])⟩
  · exact Or.inl ⟨a, y, hq, h⟩

theorem cotangentSupport_smul (c : ℂ) (v : Family (U := U) (H := H)) :
    cotangentSupport (c • v) ⊆ cotangentSupport v := by
  unfold cotangentSupport
  apply closure_mono
  rintro x ⟨a, y, hq, hne⟩
  exact ⟨a, y, hq, fun hz => hne (by
    change c • coefficient v a y = 0
    simp only [hz, smul_zero])⟩

def cotangentTests : Submodule ℂ (Family (U := U) (H := H)) where
  carrier := {v | (∀ a, SmoothOnLift a (coefficient v a)) ∧ HasCompactSupport (normSquare v)}
  zero_mem' := by
    refine ⟨fun a => ⟨fun _ => 0, contDiffOn_const, fun _ => rfl⟩, ?_⟩
    change IsCompact (tsupport (normSquare (0 : Family (U := U) (H := H))))
    rw [← cotangentSupport_eq]
    have hs : cotangentSupport (0 : Family (U := U) (H := H)) = ∅ := by
      simp only [cotangentSupport, coefficient, Submodule.coe_zero, Pi.zero_apply,
        ne_eq, not_true_eq_false, and_false, exists_false, Set.setOf_false, closure_empty]
    rw [hs]
    exact isCompact_empty
  add_mem' := by
    intro v w hv hw
    refine ⟨?_, ?_⟩
    · intro a
      rcases hv.1 a with ⟨v', hv', hvl⟩
      rcases hw.1 a with ⟨w', hw', hwl⟩
      refine ⟨fun x => v' x + w' x, hv'.add hw', ?_⟩
      intro x
      change v' x.val + w' x.val = coefficient v a x + coefficient w a x
      rw [hvl, hwl]
    · change IsCompact (tsupport (normSquare (v + w)))
      rw [← cotangentSupport_eq]
      exact ((hv.2 : IsCompact (tsupport (normSquare v))).union
        (hw.2 : IsCompact (tsupport (normSquare w)))).of_isClosed_subset
          isClosed_closure (by simpa only [cotangentSupport_eq] using cotangentSupport_add v w)
  smul_mem' := by
    intro c v hv
    refine ⟨?_, ?_⟩
    · intro a
      rcases hv.1 a with ⟨v', hv', hvl⟩
      refine ⟨fun x => c • v' x, hv'.const_smul c, ?_⟩
      intro x
      change c • v' x.val = c • coefficient v a x
      rw [hvl]
    · change IsCompact (tsupport (normSquare (c • v)))
      rw [← cotangentSupport_eq]
      exact (hv.2 : IsCompact (tsupport (normSquare v))).of_isClosed_subset
        isClosed_closure (by simpa only [cotangentSupport_eq] using cotangentSupport_smul c v)

abbrev T_U (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) :=
  ↥(cotangentTests (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H))

def sectionFields (s : Sections F ζ hζ U R P H) : ScalarFields F ζ hζ U R P H :=
  fun a x => (isotropyChart a).coefficient s x.val

theorem sectionFields_add (s t : Sections F ζ hζ U R P H) :
    sectionFields (s + t) = sectionFields s + sectionFields t := by
  funext a x
  simp [sectionFields, LiftedChart.coefficient, mul_add]

theorem sectionFields_smul (c : ℂ) (s : Sections F ζ hζ U R P H) :
    sectionFields (c • s) = c • sectionFields s := by
  funext a x
  simp [sectionFields, LiftedChart.coefficient, mul_left_comm]

theorem sectionNorm_chart (s : Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (y : omega a) :
    sectionNorm F ζ hζ U R P H s (q a y.val) = ‖sectionFields s a y‖ := by
  rw [show q a y.val = (H.atlas U).components
      ⟨a.component, Quotient.mk _ (labeledA (placeEquiv F ζ hζ) y.val)⟩ from
    ((H.atlas U).components_formula _ _).symm]
  rw [sectionNorm_component]
  simp [sectionFields, LiftedChart.coefficient, isotropyChart,
    ChartKind.representative]

theorem sectionFields_injective :
    Function.Injective (sectionFields (F := F) (U := U) (H := H)) := by
  intro s t h
  have hz : sectionFields (s - t) = 0 := by
    have hsub : sectionFields (s - t) = sectionFields s - sectionFields t := by
      funext a x
      simp [sectionFields, LiftedChart.coefficient, mul_sub]
    rw [hsub, h, sub_self]
  have hn : ∀ x, sectionNorm F ζ hζ U R P H (s - t) x = 0 := by
    intro x
    obtain ⟨a, y, hy⟩ := exists_actual_lift x
    rw [← hy, sectionNorm_chart, hz]
    simp
  have he : s - t = 0 := by
    funext i
    apply Subtype.ext
    funext x
    have hn' := hn ((H.atlas U).components ⟨i, Quotient.mk _ x⟩)
    rw [sectionNorm_component] at hn'
    exact norm_eq_zero.mp hn'
  exact sub_eq_zero.mp he

theorem scalarSupport_sectionFields (s : Sections F ζ hζ U R P H) :
    scalarSupport (sectionFields s) = tsupport (sectionNorm F ζ hζ U R P H s) := by
  unfold scalarSupport tsupport
  congr 1
  ext x
  constructor
  · rintro ⟨a, y, rfl, hne⟩
    simpa only [Function.mem_support, sectionNorm_chart, norm_ne_zero_iff] using hne
  · intro hx
    obtain ⟨a, y, hq⟩ := exists_actual_lift x
    refine ⟨a, y, hq, ?_⟩
    rw [← hq] at hx
    simpa only [Function.mem_support, sectionNorm_chart, norm_ne_zero_iff] using hx

open KPContSectorPhaseComponentCharts in
 theorem shrink_exists (i : Fin (H.atlas U).componentCount) (p : SymmetricSpace F) :
    ∃ C : ShrunkChart F ζ hζ U R P H, C.component = i ∧ C.center = p ∧ p ∈ C.domain := by
  let O := Classical.choice (KPContSectorPhaseComponentCharts.orbifoldChart_exists F ζ hζ U R P H i p)
  letI : Finite (MulAction.stabilizer (Component F ζ hζ U R P H i) p) :=
    chart_stabilizer_finite F ζ hζ U R P H i p O
  letI := Fintype.ofFinite (MulAction.stabilizer (Component F ζ hζ U R P H i) p)
  obtain ⟨W,hWo,hpW,hWsub,hWc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := p)) O.isOpen (Set.singleton_subset_iff.mpr O.center_mem)
  let V := ⋂ g : MulAction.stabilizer (Component F ζ hζ U R P H i) p,
    (fun x : SymmetricSpace F => (g.val : KPCuspArithmetic.PGL2 F) • x) ⁻¹' W
  have hopen : IsOpen V := isOpen_iInter_of_finite fun g =>
    hWo.preimage (KPCuspSiegel.continuous_action F g.val.val)
  have hsub : V ⊆ W := by
    intro x hx
    simpa using Set.mem_iInter.mp hx (1 : MulAction.stabilizer (Component F ζ hζ U R P H i) p)
  have hp : p ∈ V := by
    apply Set.mem_iInter.mpr; intro g
    change g.val • p ∈ W
    rw [MulAction.mem_stabilizer_iff.mp g.property]
    exact hpW (Set.mem_singleton p)
  refine ⟨⟨i,p,O,V,hopen,hWc.of_isClosed_subset isClosed_closure (closure_mono hsub),
    (closure_mono hsub).trans hWsub,?_⟩,rfl,rfl,hp⟩
  intro g
  ext x; constructor
  · rintro ⟨y,hy,rfl⟩
    apply Set.mem_iInter.mpr; intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, ← mul_smul] using Set.mem_iInter.mp hy (h*g)
  · intro hx
    refine ⟨(g.val : KPCuspArithmetic.PGL2 F)⁻¹ • x,?_, smul_inv_smul _ _⟩
    apply Set.mem_iInter.mpr; intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, Subgroup.coe_inv, ← mul_smul]
      using Set.mem_iInter.mp hx (h*g⁻¹)

 def coord (g : KPCuspArithmetic.PGL2 F) (x : M F) :=
  labeledAInv (placeEquiv F ζ hζ) (g • labeledA (placeEquiv F ζ hζ) x)
 theorem coord_continuous (g : KPCuspArithmetic.PGL2 F) : Continuous (coord (ζ:=ζ) (hζ:=hζ) g) := by
  apply (CotangentLogCoframe.A (d F)).symm.continuous.comp
  apply continuous_pi
  intro k
  exact (continuous_apply _).comp ((KPCuspSiegel.continuous_action F g).comp (by
    apply continuous_pi
    intro k
    exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous))
 theorem chart_coord (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component)) :
    coordinateMap (isotropyChart a) (targetChart a b h) g = coord (ζ:=ζ) (hζ:=hζ) g.val := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  funext x
  simp [coordinateMap, isotropyChart, targetChart, ChartKind.representative, coord]
 theorem chart_omega (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component) :
    (targetChart a b h).omega = (isotropyChart b).omega := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  rfl
 theorem omega_open (a : ShrunkChart F ζ hζ U R P H) : IsOpen (omega a) := by
  apply a.domain_open.preimage
  apply continuous_pi
  intro k
  exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
 def make (a b : ShrunkChart F ζ hζ U R P H) (h : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component)) :
    ActualBranch a b := by
  let he := KPCuspGenuineMonodromy.finiteComparison_exists F ζ hζ U _ g
  let r := he.choose
  let u := he.choose_spec.choose
  have hu := he.choose_spec.choose_spec
  have ht : Set.MapsTo (coordinateMap (isotropyChart a) (targetChart a b h) g)
      (omega a ∩ coord (ζ:=ζ) (hζ:=hζ) g.val ⁻¹' omega b) (isotropyChart b).omega := by
    rw [chart_coord a b h g]
    exact fun _ hx => omega_subset_larger b hx.2
  exact {
    component_eq := h
    arrow := {
      gamma := g, root := r⁻¹, levelLift := u,
      finite_comparison := by simpa only [inv_inv] using hu
      domain := omega a ∩ coord (ζ:=ζ) (hζ:=hζ) g.val ⁻¹' omega b
      isOpen_domain := (omega_open a).inter ((omega_open b).preimage (coord_continuous g.val))
      source := fun _ hx => omega_subset_larger a hx.1
      target := by rw [chart_omega a b h]; exact ht }
    source_shrinking := fun _ hx => hx.1
    target_shrinking := by
      change Set.MapsTo (coordinateMap (isotropyChart a) (targetChart a b h) g)
        (omega a ∩ coord (ζ:=ζ) (hζ:=hζ) g.val ⁻¹' omega b) (omega b)
      rw [chart_coord a b h g]
      exact fun _ hx => hx.2
    target_larger := ht }

private theorem scalarCompatible_transform (f : ScalarFields F ζ hζ U R P H)
    (hf : ScalarCompatible f) (a b : ActualChart (U := U) (H := H))
    (hc : a.component = b.component)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component))
    (x : omega a) (y : omega b) (hy : y.val = coord (ζ := ζ) (hζ := hζ) g.val x.val) :
    f b y = (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line a.component).rho g) : ℂ) * f a x := by
  let e := make a b hc g
  obtain ⟨u, hu⟩ := ((H.atlas U).line a.component).finite_comparison g
  let e' : ActualBranch a b := { e with arrow := { e.arrow with
    root := ((H.atlas U).line a.component).rho g
    levelLift := u
    finite_comparison := hu } }
  have hx : x.val ∈ e'.arrow.domain := by
    change x.val ∈ omega a ∩ coord (ζ := ζ) (hζ := hζ) g.val ⁻¹' omega b
    refine ⟨x.property, ?_⟩
    change coord (ζ := ζ) (hζ := hζ) g.val x.val ∈ omega b
    rw [← hy]; exact y.property
  have heq : e'.arrow.psi x.val = y.val := by
    change coordinateMap (isotropyChart a) (targetChart a b hc) g x.val = y.val
    rw [chart_coord]
    exact hy.symm
  have h := hf.2 a b e' x.val hx
  have htarget : (⟨e'.arrow.psi x.val, e'.target_shrinking hx⟩ : omega b) = y := Subtype.ext heq
  rw [htarget] at h
  convert h using 1
  rcases a with ⟨i, ca, oa, da, dao, dac, das, dai⟩
  rcases b with ⟨j, cb, ob, db, dbo, dbc, dbs, dbi⟩
  dsimp at hc
  subst j
  simp [Arrow.phase, e', e, make, targetChart, isotropyChart]

 def pointChart (i : Fin (H.atlas U).componentCount) (y : SymmetricSpace F) :
    ActualChart (U := U) (H := H) :=
  (shrink_exists (H := H) i y).choose
private theorem pointChart_component (i : Fin (H.atlas U).componentCount) (y : SymmetricSpace F) :
    (pointChart (H := H) i y).component = i :=
  (shrink_exists (H := H) i y).choose_spec.1
 theorem pointChart_mem (i : Fin (H.atlas U).componentCount) (y : SymmetricSpace F) :
    y ∈ (pointChart (H := H) i y).domain :=
  (shrink_exists (H := H) i y).choose_spec.2.2
 def pointLift (i : Fin (H.atlas U).componentCount) (y : SymmetricSpace F) :
    omega (pointChart (H := H) i y) :=
  ⟨labeledAInv (placeEquiv F ζ hζ) y, by
    change labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y) ∈ (pointChart (H := H) i y).domain
    have he : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y) = y := by
      funext k; simp [labeledA, labeledAInv]
    rw [he]; exact pointChart_mem i y⟩
 def gluedScalar (f : S_U F ζ hζ U R P H) (i : Fin (H.atlas U).componentCount)
    (y : SymmetricSpace F) : ℂ := f.val (pointChart i y) (pointLift i y)
private theorem gluedScalar_chart (f : S_U F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    gluedScalar f a.component (labeledA (placeEquiv F ζ hζ) x.val) = f.val a x := by
  unfold gluedScalar
  have hc := pointChart_component (H := H) a.component (labeledA (placeEquiv F ζ hζ) x.val)
  have hy : (pointLift (H := H) a.component (labeledA (placeEquiv F ζ hζ) x.val)).val =
      coord (ζ := ζ) (hζ := hζ) (1 : KPCuspArithmetic.PGL2 F) x.val := by
    simp [pointLift, coord, labeledAInv, labeledA]
  have h := scalarCompatible_transform f.val f.property.2.1 a
    (pointChart a.component (labeledA (placeEquiv F ζ hζ) x.val)) hc.symm 1 x
    (pointLift a.component (labeledA (placeEquiv F ζ hζ) x.val)) hy
  simpa using h

def archCoordinates : M F ≃L[ℝ] SymmetricSpace F :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := labeledA (placeEquiv F ζ hζ)
      invFun := labeledAInv (placeEquiv F ζ hζ)
      left_inv := fun x => by simp [labeledAInv, labeledA]
      right_inv := fun y => by funext k; simp [labeledAInv, labeledA]
      map_add' := fun x y => by funext k; simp [labeledA]
      map_smul' := fun c x => by funext k; simp [labeledA] }

 theorem gluedScalar_fiber (f : S_U F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (y : SymmetricSpace F) :
    gluedScalar f i y ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U := by
  intro ε hε
  let a := pointChart (H := H) i y
  let x := pointLift (H := H) i y
  let γ : Gamma a := ⟨(1, ε), central_label_mem a ε hε⟩
  have h := f.property.2.1.1 a γ x.val x.property
  have hψ : (isotropyArrow a γ).psi x.val = x.val := by
    simp [isotropyArrow, γ, Arrow.psi, coordinateMap, isotropyChart,
      ChartKind.representative, labeledAInv, labeledA]
  have hx : (⟨(isotropyArrow a γ).psi x.val, isotropy_mem a γ x.val x.property⟩ : omega a) = x :=
    Subtype.ext hψ
  rw [hx] at h
  have hp : (isotropyArrow a γ).phase x.val = (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) := by
    simp [Arrow.phase, isotropyArrow, isotropyChart, γ]
  rw [hp] at h
  exact h.symm
 theorem gluedScalar_covariant (f : S_U F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount)
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
    (y : SymmetricSpace F) :
    gluedScalar f i (g.val • y) =
      (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line i).rho g) : ℂ) * gluedScalar f i y := by
  let a := pointChart (H := H) i y
  let b := pointChart (H := H) i (g.val • y)
  let x := pointLift (H := H) i y
  let z := pointLift (H := H) i (g.val • y)
  have ha : a.component = i := pointChart_component i y
  have hb : b.component = i := pointChart_component i (g.val • y)
  have hgen : ∀ (j : Fin (H.atlas U).componentCount) (haj : a.component = j)
      (gb : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative j))
      (w : omega b), b.component = j →
      w.val = coord (ζ := ζ) (hζ := hζ) gb.val x.val →
      f.val b w = (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line j).rho gb) : ℂ) * f.val a x := by
    intro j haj gb w hbj hw
    subst j
    exact scalarCompatible_transform f.val f.property.2.1 a b hbj.symm gb x w hw
  exact hgen i ha g z hb (by
    dsimp [z, x, pointLift, coord]
    congr 1
    have hi : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y) = y := by
      funext k; simp [labeledA, labeledAInv]
    rw [hi])

def gluedSections (f : S_U F ζ hζ U R P H) : Sections F ζ hζ U R P H :=
  fun i => ⟨gluedScalar f i, gluedScalar_fiber f i, gluedScalar_covariant f i⟩
theorem gluedSections_fields (f : S_U F ζ hζ U R P H) :
    sectionFields (gluedSections f) = f.val := by
  funext a x
  simpa [sectionFields, LiftedChart.coefficient, isotropyChart,
    ChartKind.representative, gluedSections] using gluedScalar_chart f a x

theorem scalar_gluing (f : S_U F ζ hζ U R P H) :
    ∃! s : Sections F ζ hζ U R P H,
      IsSmoothSections F ζ hζ U R P H s ∧
      HasCompactSupport (sectionNorm F ζ hζ U R P H s) ∧ sectionFields s = f.val := by
  have hsmooth : IsSmoothSections F ζ hζ U R P H (gluedSections f) := by
    intro i
    rw [contDiff_iff_contDiffAt]
    intro y
    let a := pointChart (H := H) i y
    have ha : a.component = i := pointChart_component i y
    obtain ⟨g, hg, he⟩ := f.property.1 a
    let A := archCoordinates (F := F) (ζ := ζ) (hζ := hζ)
    have hmem : A.symm y ∈ omega a := (pointLift (H := H) i y).property
    have hopen : IsOpen (omega a) := a.domain_open.preimage A.continuous
    have hd := (hg.contDiffAt (hopen.mem_nhds hmem)).comp y A.symm.contDiff.contDiffAt
    apply hd.congr_of_eventuallyEq
    have hn : a.domain ∈ 𝓝 y := a.domain_open.mem_nhds (pointChart_mem i y)
    filter_upwards [hn] with z hz
    let x : omega a := ⟨A.symm z, by
      change A (A.symm z) ∈ a.domain
      rw [A.apply_symm_apply]; exact hz⟩
    have hc := gluedScalar_chart f a x
    have hi : labeledA (placeEquiv F ζ hζ) x.val = z := A.apply_symm_apply z
    rw [hi, ha] at hc
    exact hc.trans (he x).symm
  have hsupport : HasCompactSupport (sectionNorm F ζ hζ U R P H (gluedSections f)) := by
    change IsCompact (tsupport _)
    rw [← scalarSupport_sectionFields, gluedSections_fields]
    exact f.property.2.2
  refine ⟨gluedSections f, ⟨hsmooth, hsupport, gluedSections_fields f⟩, ?_⟩
  intro s hs
  exact sectionFields_injective (hs.2.2.trans (gluedSections_fields f).symm)

def scalarSections : S_U F ζ hζ U R P H →ₗ[ℂ] Sections F ζ hζ U R P H where
  toFun f := Classical.choose (scalar_gluing f)
  map_add' := by
    intro f g
    apply sectionFields_injective
    rw [sectionFields_add]
    exact (Classical.choose_spec (scalar_gluing (f + g))).1.2.2.trans
      (congrArg₂ (· + ·) (Classical.choose_spec (scalar_gluing f)).1.2.2
        (Classical.choose_spec (scalar_gluing g)).1.2.2).symm
  map_smul' := by
    intro c f
    apply sectionFields_injective
    rw [sectionFields_smul]
    exact (Classical.choose_spec (scalar_gluing (c • f))).1.2.2.trans
      (congrArg (c • ·) (Classical.choose_spec (scalar_gluing f)).1.2.2).symm

theorem scalarSections_fields (f : S_U F ζ hζ U R P H) :
    sectionFields (scalarSections f) = f.val :=
  (Classical.choose_spec (scalar_gluing f)).1.2.2

theorem scalarSections_smooth (f : S_U F ζ hζ U R P H) :
    IsSmoothSections F ζ hζ U R P H (scalarSections f) :=
  (Classical.choose_spec (scalar_gluing f)).1.1

theorem scalarSections_compact (f : S_U F ζ hζ U R P H) :
    HasCompactSupport (sectionNorm F ζ hζ U R P H (scalarSections f)) :=
  (Classical.choose_spec (scalar_gluing f)).1.2.1

theorem sectionFields_mem (s : Sections F ζ hζ U R P H)
    (hs : IsSmoothSections F ζ hζ U R P H s)
    (hc : HasCompactSupport (sectionNorm F ζ hζ U R P H s)) :
    sectionFields s ∈ scalarTests := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro a
    refine ⟨(isotropyChart a).coefficient s, ?_, fun _ => rfl⟩
    have hA : ContDiff ℝ (⊤ : ℕ∞) (labeledA (placeEquiv F ζ hζ)) := by
      unfold labeledA
      fun_prop
    have he : (isotropyChart a).coefficient s =
        fun x => (s a.component).val (labeledA (placeEquiv F ζ hζ) x) := by
      funext x
      simp [LiftedChart.coefficient, isotropyChart, ChartKind.representative]
    rw [he]
    exact ((hs a.component).comp hA).contDiffOn
  · intro a γ x hx
    exact (unitary_phase (isotropyArrow a γ)).2.2.2 s x
      (a.closure_subset (subset_closure hx))
  · intro a b e x hx
    have hh := (unitary_phase e.arrow).2.2.2 s x hx
    have hcast : ∀ (i j : Fin (H.atlas U).componentCount) (h : i = j)
        (c : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
          (U := U) (R := R) (P := P) (H := H) j),
        (h.symm ▸ c).coefficient s = c.coefficient s := by
      intro i j h c
      subst j
      rfl
    have he : (targetChart a b e.component_eq).coefficient s =
        (isotropyChart b).coefficient s := hcast _ _ e.component_eq _
    simpa only [sectionFields, he] using hh
  · rw [scalarSupport_sectionFields]
    exact hc

set_option maxHeartbeats 800000 in

def groupTests : Submodule ℂ (KPFiniteCuspAtlas.genuineScalars F ζ hζ U) where
  carrier := {f | (∀ c, ContDiff ℝ (⊤ : ℕ∞) (fun x : SymmetricSpace F => f.val (x,c))) ∧
    HasCompactSupport ((J F ζ hζ U).symm f).val}
  zero_mem' := by
    refine ⟨fun c => contDiff_const, ?_⟩
    simpa using (HasCompactSupport.zero : HasCompactSupport
      (0 : CoveredSpherical F ζ hζ U → ℂ))
  add_mem' := by
    intro f g hf hg
    refine ⟨fun c => (hf.1 c).add (hg.1 c), ?_⟩
    simpa only [map_add, Submodule.coe_add] using hf.2.add hg.2
  smul_mem' := by
    intro c f hf
    refine ⟨fun k => (hf.1 k).const_smul c, ?_⟩
    rw [map_smul]
    change IsCompact (tsupport (c • ((J F ζ hζ U).symm f).val))
    apply (hf.2 : IsCompact (tsupport ((J F ζ hζ U).symm f).val)).of_isClosed_subset
      isClosed_closure
    apply closure_mono
    intro x hx
    change c • ((J F ζ hζ U).symm f).val x ≠ 0 at hx
    change ((J F ζ hζ U).symm f).val x ≠ 0
    intro h
    exact hx (by rw [h, smul_zero])

def groupIdentification : S_U F ζ hζ U R P H ≃ₗ[ℂ] groupTests (F := F) (ζ := ζ)
    (hζ := hζ) (U := U) where
  toFun f := ⟨(H.atlas U).scalar_realization.symm (scalarSections f), by
    let g := (H.atlas U).scalar_realization.symm (scalarSections f)
    have he : S F ζ hζ U R P H ((J F ζ hζ U).symm g) = scalarSections f := by
      simp [S, g]
    refine ⟨?_, ?_⟩
    · have hg := (smooth_iff F ζ hζ U R P H ((J F ζ hζ U).symm g)).mpr
        (by rw [he]; exact scalarSections_smooth f)
      simpa only [IsSmoothCovered, LinearEquiv.apply_symm_apply] using hg
    · exact (hasCompactSupport_iff F ζ hζ U R P H ((J F ζ hζ U).symm g)).mpr
        (by rw [he]; exact scalarSections_compact f)⟩
  invFun g := ⟨sectionFields ((H.atlas U).scalar_realization g.val), by
    apply sectionFields_mem
    · have hg : IsSmoothCovered F ζ hζ U ((J F ζ hζ U).symm g.val) := by
        simpa only [IsSmoothCovered, LinearEquiv.apply_symm_apply] using g.property.1
      exact (smooth_iff F ζ hζ U R P H ((J F ζ hζ U).symm g.val)).mp hg
    · exact (hasCompactSupport_iff F ζ hζ U R P H ((J F ζ hζ U).symm g.val)).mp
        g.property.2⟩
  left_inv := by
    intro f
    apply Subtype.ext
    simpa only [LinearEquiv.apply_symm_apply] using scalarSections_fields f
  right_inv := by
    intro g
    apply Subtype.ext
    apply (H.atlas U).scalar_realization.injective
    rw [LinearEquiv.apply_symm_apply]
    apply sectionFields_injective
    exact scalarSections_fields _
  map_add' := by
    intro f g
    apply Subtype.ext
    simp only [map_add, Submodule.coe_add]
  map_smul' := by
    intro c f
    apply Subtype.ext
    simp only [map_smul, Submodule.coe_smul, RingHom.id_apply]

def groupLift (f : KPFiniteCuspAtlas.genuineScalars F ζ hζ U)
    (g : KPSmoothActualFlowData.GInfinity F) (c : FiniteCover F ζ hζ) : ℂ :=
  f.val (KPMsFixedHaarDisintegration.archBasepoint F g,c)

def scalarCovered (f : S_U F ζ hζ U R P H) : GenuineCoveredScalars F ζ hζ U :=
  (J F ζ hζ U).symm (groupIdentification f).val

def scalarRestriction (a : ActualChart (U := U) (H := H)) :
    S_U F ζ hζ U R P H →ₗ[ℂ] (omega a → ℂ) where
  toFun f := f.val a
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def cotangentRestriction (a : ActualChart (U := U) (H := H)) :
    T_U F ζ hζ U R P H →ₗ[ℂ] (omega a → E F) where
  toFun v := coefficient v.val a
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def localSupport {W : Type*} [Zero W] (a : ActualChart (U := U) (H := H))
    (f : omega a → W) : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  closure (q a '' {x : M F | ∃ hx : x ∈ omega a, f ⟨x,hx⟩ ≠ 0})

def localScalarTests (a : ActualChart (U := U) (H := H)) : Submodule ℂ (omega a → ℂ) where
  carrier := {f | SmoothOnLift a f ∧ ScalarEquivariant a f ∧
    IsCompact (localSupport a f) ∧ localSupport a f ⊆ a.baseDomain}
  zero_mem' := by
    have hsupport : localSupport a (0 : omega a → ℂ) = ∅ := by
      simp only [localSupport, Pi.zero_apply, ne_eq, not_true_eq_false,
        exists_false, Set.setOf_false, Set.image_empty, closure_empty]
    refine ⟨⟨fun _ => 0, contDiffOn_const, fun _ => rfl⟩, ?_, ?_, ?_⟩
    · intro γ x hx
      simp
    · rw [hsupport]
      exact isCompact_empty
    · rw [hsupport]
      exact Set.empty_subset _
  add_mem' := by
    intro f g hf hg
    rcases hf with ⟨⟨f', hf', hf'lift⟩, hfEq, hfCompact, hfDomain⟩
    rcases hg with ⟨⟨g', hg', hg'lift⟩, hgEq, hgCompact, hgDomain⟩
    have hsupport : localSupport a (f + g) ⊆ localSupport a f ∪ localSupport a g := by
      unfold localSupport
      rw [← closure_union]
      apply closure_mono
      rintro _ ⟨x, ⟨hx, hne⟩, rfl⟩
      have hnonzero : f ⟨x, hx⟩ ≠ 0 ∨ g ⟨x, hx⟩ ≠ 0 := by
        by_contra h
        push_neg at h
        exact hne (by simp [h.1, h.2])
      rcases hnonzero with hf | hg
      · exact Or.inl ⟨x, ⟨hx, hf⟩, rfl⟩
      · exact Or.inr ⟨x, ⟨hx, hg⟩, rfl⟩
    refine ⟨⟨fun x => f' x + g' x, hf'.add hg', ?_⟩, ?_, ?_, ?_⟩
    · intro x
      simp only [Pi.add_apply, hf'lift, hg'lift]
    · intro γ x hx
      simp only [Pi.add_apply, hfEq γ x hx, hgEq γ x hx, mul_add]
    · exact (hfCompact.union hgCompact).of_isClosed_subset isClosed_closure hsupport
    · exact hsupport.trans (Set.union_subset hfDomain hgDomain)
  smul_mem' := by
    intro c f hf
    rcases hf with ⟨⟨f', hf', hf'lift⟩, hfEq, hfCompact, hfDomain⟩
    have hsupport : localSupport a (c • f) ⊆ localSupport a f := by
      unfold localSupport
      apply closure_mono
      rintro _ ⟨x, ⟨hx, hne⟩, rfl⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      intro hzero
      exact hne (by simp [hzero])
    refine ⟨⟨fun x => c • f' x, hf'.const_smul c, ?_⟩, ?_, ?_, ?_⟩
    · intro x
      simp only [Pi.smul_apply, hf'lift]
    · intro γ x hx
      simp only [Pi.smul_apply, smul_eq_mul, hfEq γ x hx]
      exact mul_left_comm _ _ _
    · exact hfCompact.of_isClosed_subset isClosed_closure hsupport
    · exact hsupport.trans hfDomain

def CotangentEquivariant (a : ActualChart (U := U) (H := H)) (f : omega a → E F) : Prop :=
  ∀ (γ : Gamma a) (x : M F) (hx : x ∈ omega a),
    f ⟨(isotropyArrow a γ).psi x, isotropy_mem a γ x hx⟩ =
      T (isotropyArrow a γ) x (omega_subset_larger a hx) (f ⟨x,hx⟩)

def localCotangentTests (a : ActualChart (U := U) (H := H)) :
    Submodule ℂ (omega a → E F) where
  carrier := {f | SmoothOnLift a f ∧ CotangentEquivariant a f ∧
    IsCompact (localSupport a f) ∧ localSupport a f ⊆ a.baseDomain}
  zero_mem' := by
    have hsupport : localSupport a (0 : omega a → E F) = ∅ := by
      simp only [localSupport, Pi.zero_apply, ne_eq, not_true_eq_false,
        exists_false, Set.setOf_false, Set.image_empty, closure_empty]
    refine ⟨⟨fun _ => 0, contDiffOn_const, fun _ => rfl⟩, ?_, ?_, ?_⟩
    · intro γ x hx
      exact (map_zero _).symm
    · rw [hsupport]
      exact isCompact_empty
    · rw [hsupport]
      exact Set.empty_subset _
  add_mem' := by
    intro f g hf hg
    rcases hf with ⟨⟨f', hf', hf'lift⟩, hfEq, hfCompact, hfDomain⟩
    rcases hg with ⟨⟨g', hg', hg'lift⟩, hgEq, hgCompact, hgDomain⟩
    have hsupport : localSupport a (f + g) ⊆ localSupport a f ∪ localSupport a g := by
      unfold localSupport
      rw [← closure_union]
      apply closure_mono
      rintro _ ⟨x, ⟨hx, hne⟩, rfl⟩
      by_cases h : f ⟨x,hx⟩ = 0
      · exact Or.inr ⟨x, ⟨hx, fun hz => hne (by simp [h, hz])⟩, rfl⟩
      · exact Or.inl ⟨x, ⟨hx, h⟩, rfl⟩
    refine ⟨⟨fun x => f' x + g' x, hf'.add hg', ?_⟩, ?_, ?_, ?_⟩
    · intro x
      simp only [Pi.add_apply, hf'lift, hg'lift]
    · intro γ x hx
      simp only [Pi.add_apply, hfEq γ x hx, hgEq γ x hx, map_add]
    · exact (hfCompact.union hgCompact).of_isClosed_subset isClosed_closure hsupport
    · exact hsupport.trans (Set.union_subset hfDomain hgDomain)
  smul_mem' := by
    intro c f hf
    rcases hf with ⟨⟨f', hf', hf'lift⟩, hfEq, hfCompact, hfDomain⟩
    have hsupport : localSupport a (c • f) ⊆ localSupport a f := by
      unfold localSupport
      apply closure_mono
      rintro _ ⟨x, ⟨hx, hne⟩, rfl⟩
      exact ⟨x, ⟨hx, fun hz => hne (by simp [hz])⟩, rfl⟩
    refine ⟨⟨fun x => c • f' x, hf'.const_smul c, ?_⟩, ?_, ?_, ?_⟩
    · intro x
      simp only [Pi.smul_apply, hf'lift]
    · intro γ x hx
      simp only [Pi.smul_apply, hfEq γ x hx, map_smul]
    · exact hfCompact.of_isClosed_subset isClosed_closure hsupport
    · exact hsupport.trans hfDomain

private theorem coord_smooth (g : KPCuspArithmetic.PGL2 F) :
    ContDiff ℝ (⊤ : ℕ∞) (coord (ζ:=ζ) (hζ:=hζ) g) := by
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  let G : Fin (d F) → Matrix.GeneralLinearGroup (Fin 2) ℂ := fun k =>
    Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F ((placeEquiv F ζ hζ) k)).embedding B
  have he : coord (ζ:=ζ) (hζ:=hζ) (Matrix.ProjGenLinGroup.mk B) =
      fun x => (CotangentLogCoframe.A (d F)).symm
        (KPArch.productAction (d F) G (CotangentLogCoframe.A (d F) x)) := by
    funext x
    simp only [coord, labeledAInv]
    congr 1
    funext k
    change KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk B) (labeledA (placeEquiv F ζ hζ) x) ((placeEquiv F ζ hζ) k) = _
    rw [KPCuspSiegel.action_mk]
    simp [labeledA, KPCuspSiegel.glAction, KPArch.productAction, G]
  rw [he]
  exact (CotangentLogCoframe.A (d F)).symm.contDiff.comp
    (((KPArch.productAction_contDiff (d F) G).of_le
      (show (⊤ : ℕ∞) ≤ (⊤ : ℕ∞ω) from le_top)).comp (CotangentLogCoframe.A (d F)).contDiff)

private theorem separated (b : ShrunkChart F ζ hζ U R P H)
    (g : KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H b.component)
    (x : KPCuspGenuineMonodromy.SymmetricSpace F)
    (hx : x ∈ b.domain) (hg : g • x ∈ b.domain) : g ∈ b.Isotropy := by
  open KPContSectorPhaseComponentCharts in
    let g' : ArchComponent F ζ hζ U R P H b.component :=
      ⟨complexProjectiveEmbedding F g.val, Subgroup.mem_map.mpr ⟨g.val,g.property,rfl⟩⟩
    have hh : g' ∈ MulAction.stabilizer _ b.center :=
      b.larger.separated g' ⟨g • x,
        ⟨x,b.closure_subset (subset_closure hx),complexProjectiveEmbedding_smul F g.val x⟩,
        b.closure_subset (subset_closure hg)⟩
    apply MulAction.mem_stabilizer_iff.mpr
    have ht := MulAction.mem_stabilizer_iff.mp hh
    change complexProjectiveEmbedding F g.val • b.center = b.center at ht
    rwa [complexProjectiveEmbedding_smul] at ht

namespace ScalarExtension

variable (a : ActualChart (U := U) (H := H))
abbrev G := KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component)
 def value (f : localScalarTests a) (y : a.domain) : ℂ :=
  let A := archCoordinates (F := F) (ζ := ζ) (hζ := hζ)
  f.val ⟨A.symm y.val, by
    change A (A.symm y.val) ∈ a.domain
    rw [A.apply_symm_apply]; exact y.property⟩
private theorem value_equivariant (f : localScalarTests a) (g : G a)
    (y : a.domain) (hy : g.val • y.val ∈ a.domain) :
    value a f ⟨g.val • y.val, hy⟩ =
      (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line a.component).rho g) : ℂ) * value a f y := by
  have hg : g ∈ a.Isotropy := separated a g y.val y.property hy
  obtain ⟨u, hu⟩ := ((H.atlas U).line a.component).finite_comparison g
  let γ : Gamma a := ⟨(⟨g, hg⟩, ((H.atlas U).line a.component).rho g), u, hu⟩
  let A := archCoordinates (F := F) (ζ := ζ) (hζ := hζ)
  let x : omega a := ⟨A.symm y.val, by
    change A (A.symm y.val) ∈ a.domain
    rw [A.apply_symm_apply]; exact y.property⟩
  have h := f.property.2.1 γ x.val x.property
  have hψ : (isotropyArrow a γ).psi x.val = A.symm (g.val • y.val) := by
    simp only [isotropyArrow, γ, Arrow.psi, coordinateMap, isotropyChart,
      ChartKind.representative, inv_one, one_mul, mul_one]
    have hi : labeledA (placeEquiv F ζ hζ) x.val = y.val := A.apply_symm_apply _
    rw [hi]; rfl
  have hp : (isotropyArrow a γ).phase x.val =
      (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line a.component).rho g) : ℂ) := by
    simp [Arrow.phase, isotropyArrow, isotropyChart, γ]
  rw [hp] at h
  convert h using 1
  apply congrArg f.val
  exact Subtype.ext hψ.symm
  rfl
 def reachable (z : SymmetricSpace F) : Prop := ∃ g : G a, g.val • z ∈ a.domain
 def extended (f : localScalarTests a) (z : SymmetricSpace F) : ℂ :=
  if hz : reachable a z then
    let g := hz.choose
    (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line a.component).rho g) : ℂ)⁻¹ *
      value a f ⟨g.val • z, hz.choose_spec⟩
  else 0
private theorem extended_at (f : localScalarTests a) (z : SymmetricSpace F)
    (g : G a) (hg : g.val • z ∈ a.domain) :
    extended a f z =
      (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line a.component).rho g) : ℂ)⁻¹ *
      value a f ⟨g.val • z, hg⟩ := by
  have hz : reachable a z := ⟨g, hg⟩
  rw [extended, dif_pos hz]
  let h : G a := hz.choose
  have hh : h.val • z ∈ a.domain := hz.choose_spec
  have ht : (h * g⁻¹).val • (g.val • z) ∈ a.domain := by
    simpa [mul_smul] using hh
  have he := value_equivariant a f (h * g⁻¹) ⟨g.val • z, hg⟩ ht
  have hv : (h * g⁻¹).val • (g.val • z) = h.val • z := by simp [mul_smul]
  have hs : (⟨(h * g⁻¹).val • (g.val • z), ht⟩ : a.domain) = ⟨h.val • z, hh⟩ := Subtype.ext hv
  rw [hs] at he
  dsimp only
  change (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line a.component).rho h) : ℂ)⁻¹ *
      value a f ⟨h.val • z, hh⟩ = _
  rw [he]
  simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp
private theorem extended_source (f : localScalarTests a) (z : a.domain) :
    extended a f z.val = value a f z := by
  have h := extended_at a f z.val 1 (by simpa using z.property)
  simpa using h
 theorem extended_covariant (f : localScalarTests a) (g : G a) (z : SymmetricSpace F) :
    extended a f (g.val • z) =
      (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line a.component).rho g) : ℂ) * extended a f z := by
  by_cases hz : reachable a z
  · obtain ⟨h, hh⟩ := hz
    have ht : (h * g⁻¹).val • (g.val • z) ∈ a.domain := by simpa [mul_smul] using hh
    rw [extended_at a f z h hh, extended_at a f (g.val • z) (h * g⁻¹) ht]
    have hs : (⟨(h * g⁻¹).val • (g.val • z), ht⟩ : a.domain) = ⟨h.val • z, hh⟩ :=
      Subtype.ext (by simp [mul_smul])
    rw [hs]
    simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_rev, inv_inv]
    ring
  · have hgz : ¬ reachable a (g.val • z) := by
      rintro ⟨h, hh⟩
      exact hz ⟨h * g, by simpa [mul_smul] using hh⟩
    simp [extended, hz, hgz]
 theorem extended_fiber (f : localScalarTests a) (z : SymmetricSpace F) :
    extended a f z ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U := by
  by_cases hz : reachable a z
  · obtain ⟨g, hg⟩ := hz
    rw [extended_at a f z g hg]
    intro ε hε
    let γ : Gamma a := ⟨(1, ε), central_label_mem a ε hε⟩
    let A := archCoordinates (F := F) (ζ := ζ) (hζ := hζ)
    let x : omega a := ⟨A.symm (g.val • z), by
      change A (A.symm (g.val • z)) ∈ a.domain
      rw [A.apply_symm_apply]; exact hg⟩
    have h := f.property.2.1 γ x.val x.property
    have hψ : (isotropyArrow a γ).psi x.val = x.val := by
      simp [isotropyArrow, γ, Arrow.psi, coordinateMap, isotropyChart,
        ChartKind.representative, labeledAInv, labeledA]
    have hx : (⟨(isotropyArrow a γ).psi x.val, isotropy_mem a γ x.val x.property⟩ : omega a) = x :=
      Subtype.ext hψ
    rw [hx] at h
    have hp : (isotropyArrow a γ).phase x.val = (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) := by
      simp [Arrow.phase, isotropyArrow, isotropyChart, γ]
    rw [hp] at h
    change _ * (_ * f.val x) = _ * f.val x
    rw [mul_left_comm, ← h]
  · rw [extended, dif_neg hz]
    exact (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).zero_mem
 def base (z : SymmetricSpace F) : KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  (H.atlas U).components ⟨a.component, Quotient.mk _ z⟩
private theorem base_continuous : Continuous (base a) :=
  (H.atlas U).components.continuous.comp (continuous_sigmaMk.comp continuous_quotient_mk')
private theorem base_action (g : G a) (z : SymmetricSpace F) : base a (g.val • z) = base a z := by
  apply congrArg (fun t => (H.atlas U).components ⟨a.component, t⟩)
  exact Quotient.sound ⟨g, rfl⟩
private theorem extended_off_support (f : localScalarTests a) (z : SymmetricSpace F)
    (hz : base a z ∉ localSupport a f.val) : extended a f z = 0 := by
  by_cases hr : reachable a z
  · obtain ⟨g, hg⟩ := hr
    rw [extended_at a f z g hg]
    suffices h : value a f ⟨g.val • z, hg⟩ = 0 by rw [h, mul_zero]
    by_contra hn
    let A := archCoordinates (F := F) (ζ := ζ) (hζ := hζ)
    let x : omega a := ⟨A.symm (g.val • z), by
      change A (A.symm (g.val • z)) ∈ a.domain
      rw [A.apply_symm_apply]; exact hg⟩
    apply hz
    have hq : q a x.val = base a z := by
      rw [show q a x.val = base a (g.val • z) from by
        rw [KPContCotangentOverlapRationalBranches.q, ← (H.atlas U).components_formula]
        change base a (A (A.symm (g.val • z))) = base a (g.val • z)
        rw [A.apply_symm_apply], base_action]
    exact subset_closure ⟨x.val, ⟨x.property, hn⟩, hq⟩
  · exact dif_neg hr
private theorem action_smooth (g : G a) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : SymmetricSpace F => g.val • z) := by
  let A := archCoordinates (F := F) (ζ := ζ) (hζ := hζ)
  have h := A.contDiff.comp ((coord_smooth (ζ := ζ) (hζ := hζ) g.val).comp A.symm.contDiff)
  convert h using 1
  funext z
  change g.val • z = A (A.symm (g.val • A (A.symm z)))
  rw [A.apply_symm_apply, A.apply_symm_apply]
private theorem extended_smooth (f : localScalarTests a) :
    ContDiff ℝ (⊤ : ℕ∞) (extended a f) := by
  let A := archCoordinates (F := F) (ζ := ζ) (hζ := hζ)
  obtain ⟨f', hf', he⟩ := f.property.1
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : reachable a z
  · obtain ⟨g, hg⟩ := hz
    have hmem : A.symm (g.val • z) ∈ omega a := by
      change A (A.symm (g.val • z)) ∈ a.domain
      rw [A.apply_symm_apply]; exact hg
    have ho : IsOpen (omega a) := a.domain_open.preimage A.continuous
    have hd := (hf'.contDiffAt (ho.mem_nhds hmem)).comp z
      (A.symm.contDiff.comp (action_smooth a g)).contDiffAt
    have hc := hd.const_smul
      ((KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line a.component).rho g) : ℂ)⁻¹)
    apply hc.congr_of_eventuallyEq
    have hn : ∀ᶠ w in 𝓝 z, g.val • w ∈ a.domain :=
      (a.domain_open.preimage (action_smooth a g).continuous).mem_nhds hg
    filter_upwards [hn] with w hw
    rw [extended_at a f w g hw]
    congr 1
    exact (he ⟨A.symm (g.val • w), by
      change A (A.symm (g.val • w)) ∈ a.domain
      rw [A.apply_symm_apply]; exact hw⟩).symm
  · have hbase : base a z ∉ a.baseDomain := by
      rintro ⟨y, hy⟩
      have he : Quotient.mk (MulAction.orbitRel (G a) (SymmetricSpace F)) y.val = Quotient.mk _ z := by
        apply (fun heq => eq_of_heq (Sigma.mk.inj ((H.atlas U).components.injective heq)).2)
        change (H.atlas U).components ⟨a.component, KPCuspSiegel.projection F (G a) y.val⟩ =
          (H.atlas U).components ⟨a.component, Quotient.mk _ z⟩
        exact ((H.atlas U).components_formula _ _).trans hy
      obtain ⟨g, hg⟩ := Quotient.exact he
      exact hz ⟨g, by change g.val • z = y.val at hg; rw [hg]; exact y.property⟩
    have hk : base a z ∉ localSupport a f.val := fun h => hbase (f.property.2.2.2 h)
    have hn : ∀ᶠ w in 𝓝 z, base a w ∉ localSupport a f.val :=
      (isClosed_closure.isOpen_compl.preimage (base_continuous a)).mem_nhds hk
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hn] with w hw
    exact extended_off_support a f w hw
 def componentSection (f : localScalarTests a) :
    KPCuspGenuineMonodromy.sections F ζ hζ U ((H.atlas U).representative a.component)
      ((H.atlas U).line a.component).rho :=
  ⟨extended a f, extended_fiber a f, extended_covariant a f⟩

def sections (f : localScalarTests a) : Sections F ζ hζ U R P H :=
  Pi.single a.component (componentSection a f)
 theorem sections_smooth (f : localScalarTests a) :
    IsSmoothSections F ζ hζ U R P H (sections a f) := by
  intro i
  by_cases hi : i = a.component
  · subst i
    simpa only [sections, Pi.single_eq_same, componentSection] using extended_smooth a f
  · have he : (sections a f i).val = 0 := by
      simp [sections, Pi.single_eq_of_ne hi]
    rw [he]; exact contDiff_const
private theorem fields_source (f : localScalarTests a) (x : omega a) :
    sectionFields (sections a f) a x = f.val x := by
  let A := archCoordinates (F := F) (ζ := ζ) (hζ := hζ)
  have hs := extended_source a f ⟨A x.val, x.property⟩
  simp only [sectionFields, LiftedChart.coefficient, isotropyChart, ChartKind.representative,
    sections, Pi.single_eq_same, componentSection, map_one, Units.val_one, one_mul, one_smul]
  change extended a f (A x.val) = f.val x
  rw [hs]
  unfold value
  apply congrArg f.val
  exact Subtype.ext (A.symm_apply_apply _)
private theorem fields_off_support (f : localScalarTests a)
    (b : ActualChart (U := U) (H := H)) (x : omega b)
    (hx : q b x.val ∉ localSupport a f.val) : sectionFields (sections a f) b x = 0 := by
  by_cases hc : b.component = a.component
  · have he : (sections a f b.component).val
        (labeledA (placeEquiv F ζ hζ) x.val) =
        extended a f (labeledA (placeEquiv F ζ hζ) x.val) := by
      rcases b with ⟨j, cb, ob, db, dbo, dbc, dbs, dbi⟩
      dsimp at hc
      subst j
      simp [sections, componentSection]
    simp only [sectionFields, LiftedChart.coefficient, isotropyChart, ChartKind.representative,
      map_one, Units.val_one, one_mul, one_smul]
    rw [he]
    apply extended_off_support a f
    have hq : base a (labeledA (placeEquiv F ζ hζ) x.val) = q b x.val := by
      unfold base KPContCotangentOverlapRationalBranches.q
      rw [← hc, (H.atlas U).components_formula]
      rfl
    rwa [hq]
  · have hs : sections a f b.component = 0 := by simp [sections, Pi.single_eq_of_ne hc]
    simp [sectionFields, LiftedChart.coefficient, hs]
private theorem fields_support (f : localScalarTests a) :
    scalarSupport (sectionFields (sections a f)) = localSupport a f.val := by
  apply Set.Subset.antisymm
  · unfold scalarSupport
    apply closure_minimal _ isClosed_closure
    rintro z ⟨b, x, hx, hn⟩
    by_contra hz
    exact hn (fields_off_support a f b x (by rwa [hx]))
  · unfold scalarSupport localSupport
    apply closure_mono
    rintro z ⟨x, ⟨hx, hn⟩, rfl⟩
    exact ⟨a, ⟨x, hx⟩, rfl, by rwa [fields_source]⟩
 theorem sections_compact (f : localScalarTests a) :
    HasCompactSupport (sectionNorm F ζ hζ U R P H (sections a f)) := by
  change IsCompact (tsupport _)
  rw [← scalarSupport_sectionFields, fields_support]
  exact f.property.2.2.1
end ScalarExtension

def scalarZeroExtension (a : ActualChart (U := U) (H := H)) :
    localScalarTests a →ₗ[ℂ] S_U F ζ hζ U R P H where
  toFun f := ⟨sectionFields (ScalarExtension.sections a f),
    sectionFields_mem _ (ScalarExtension.sections_smooth a f) (ScalarExtension.sections_compact a f)⟩
  map_add' f g := by
    apply Subtype.ext
    have hs : ScalarExtension.sections a (f + g) =
        ScalarExtension.sections a f + ScalarExtension.sections a g := by
      funext i
      by_cases hi : i = a.component
      · subst i
        apply Subtype.ext
        funext z
        simp only [ScalarExtension.sections, Pi.single_eq_same, ScalarExtension.componentSection]
        unfold ScalarExtension.extended
        by_cases hz : ScalarExtension.reachable a z <;>
          simp [hz, ScalarExtension.value, mul_add]
      · simp [ScalarExtension.sections, Pi.single_eq_of_ne hi]
    change sectionFields (ScalarExtension.sections a (f + g)) = _
    rw [hs]
    funext b x
    simp [sectionFields, LiftedChart.coefficient, mul_add]
  map_smul' c f := by
    apply Subtype.ext
    have hs : ScalarExtension.sections a (c • f) = c • ScalarExtension.sections a f := by
      funext i
      by_cases hi : i = a.component
      · subst i
        apply Subtype.ext
        funext z
        simp only [ScalarExtension.sections, Pi.smul_apply, Pi.single_eq_same,
          Submodule.coe_smul, Pi.smul_apply, ScalarExtension.componentSection, smul_eq_mul]
        unfold ScalarExtension.extended
        by_cases hz : ScalarExtension.reachable a z
        · simp only [dif_pos hz, ScalarExtension.value, Submodule.coe_smul,
            Pi.smul_apply, smul_eq_mul]
          exact mul_left_comm _ _ _
        · simp [hz]
      · simp [ScalarExtension.sections, Pi.single_eq_of_ne hi]
    change sectionFields (ScalarExtension.sections a (c • f)) = _
    rw [hs]
    funext b x
    simp only [sectionFields, LiftedChart.coefficient, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul]
    exact mul_left_comm _ _ _

theorem smoothOnLift_ambient (a : ActualChart (U := U) (H := H))
    (f : omega a → E F) (hf : SmoothOnLift a f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (KPContActualCotangentChartZeroExtension.ambientField a f) (omega a) := by
  obtain ⟨g, hg, he⟩ := hf
  apply hg.congr
  intro x hx
  rw [KPContActualCotangentChartZeroExtension.ambientField, dif_pos hx]
  exact (he ⟨x, hx⟩).symm
 theorem localTensor_equivariant (a : ActualChart (U := U) (H := H))
    (f : localCotangentTests a) :
    KPContActualCotangentChartZeroExtension.PointwiseEquivariant a
      (KPContActualCotangentChartZeroExtension.liftField a f.val) := by
  intro γ y
  dsimp only [KPContActualCotangentChartZeroExtension.liftField]
  have hc : KPContActualCotangentPieceHilbertSum.coordinates a
      (KPContActualCotangentPieceHilbertSum.actualActionEquiv a γ y) =
      ⟨(isotropyArrow a γ).psi (KPContActualCotangentPieceHilbertSum.coordinates a y).val,
        isotropy_mem a γ _ (KPContActualCotangentPieceHilbertSum.coordinates a y).property⟩ :=
    Subtype.ext (KPContActualCotangentPieceHilbertSum.coordinates_action a γ y)
  rw [hc]
  exact f.property.2.1 γ _ _
 theorem localTensor_continuous (a : ActualChart (U := U) (H := H))
    (f : localCotangentTests a) : Continuous f.val := by
  obtain ⟨g, hg, he⟩ := f.property.1
  convert hg.continuousOn.restrict using 1
  exact (funext he).symm

def cotangentExtendedFamily (a : ActualChart (U := U) (H := H))
    (f : localCotangentTests a) : Family (U := U) (H := H) :=
  KPContActualCotangentChartZeroExtension.extendedFamily a
    (KPContActualCotangentChartZeroExtension.liftField a f.val)
    ((localTensor_continuous a f).comp
      (KPContActualCotangentPieceHilbertSum.coordinates_continuous a)).measurable
    (localTensor_equivariant a f)
 theorem cotangentExtendedFamily_test (a : ActualChart (U := U) (H := H))
    (f : localCotangentTests a) : cotangentExtendedFamily a f ∈ cotangentTests := by
  have hn : ∀ y : omega a, f.val y ≠ 0 → q a y.val ∈ localSupport a f.val := by
    intro y hy
    exact subset_closure ⟨y.val, ⟨y.property, hy⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · intro b
    refine ⟨KPContActualCotangentChartZeroExtension.ambientField b
      (coefficient (cotangentExtendedFamily a f) b), ?_, ?_⟩
    · exact KPContActualCotangentChartZeroExtension.smooth_extended_base_support a f.val
        (localSupport a f.val) isClosed_closure f.property.2.2.2 hn
        (smoothOnLift_ambient a f.val f.property.1) (localTensor_equivariant a f) b
    · intro x
      exact dif_pos x.property
  · change IsCompact (tsupport (normSquare (cotangentExtendedFamily a f)))
    apply f.property.2.2.1.of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_closure
    intro z hz
    by_contra h
    obtain ⟨b, x, hx⟩ := exists_actual_lift (H := H) z
    apply hz
    rw [← hx, normSquare_chart]
    have he := KPContActualCotangentChartZeroExtension.extendedFields_zero_off_base_support a
      f.val (localSupport a f.val) hn b x (by rwa [hx])
    change ‖KPContActualCotangentChartZeroExtension.extendedFields a
      (KPContActualCotangentChartZeroExtension.liftField a f.val) b x‖₊ ^ 2 = 0
    rw [he]; simp

def cotangentZeroExtension (a : ActualChart (U := U) (H := H)) :
    localCotangentTests a →ₗ[ℂ] T_U F ζ hζ U R P H where
  toFun f := ⟨cotangentExtendedFamily a f, cotangentExtendedFamily_test a f⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext b x
    change KPContActualCotangentChartZeroExtension.extendedFields a
      (KPContActualCotangentChartZeroExtension.liftField a (f + g).val) b x =
      KPContActualCotangentChartZeroExtension.extendedFields a
        (KPContActualCotangentChartZeroExtension.liftField a f.val) b x +
      KPContActualCotangentChartZeroExtension.extendedFields a
        (KPContActualCotangentChartZeroExtension.liftField a g.val) b x
    unfold KPContActualCotangentChartZeroExtension.extendedFields
    split_ifs <;> simp [KPContActualCotangentChartZeroExtension.liftField, map_add]
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    funext b x
    change KPContActualCotangentChartZeroExtension.extendedFields a
      (KPContActualCotangentChartZeroExtension.liftField a (c • f).val) b x =
      c • KPContActualCotangentChartZeroExtension.extendedFields a
        (KPContActualCotangentChartZeroExtension.liftField a f.val) b x
    unfold KPContActualCotangentChartZeroExtension.extendedFields
    split_ifs <;> simp [KPContActualCotangentChartZeroExtension.liftField, map_smul]

theorem cotangentZeroExtension_restrict (a : ActualChart (U := U) (H := H))
    (f : localCotangentTests a) : cotangentRestriction a (cotangentZeroExtension a f) = f.val := by
  funext x
  have hi : KPContActualCotangentPieceHilbertSum.coordinates a
      (KPContActualCotangentPieceReconstruction.originalPoint a x) = x := by
    apply Subtype.ext
    simp [KPContActualCotangentPieceHilbertSum.coordinates,
      KPContActualCotangentPieceReconstruction.originalPoint, labeledA, labeledAInv]
  have h := KPContActualCotangentChartZeroExtension.extendedFields_source a
    (KPContActualCotangentChartZeroExtension.liftField a f.val)
    (((localTensor_continuous a f).comp
      (KPContActualCotangentPieceHilbertSum.coordinates_continuous a)).measurable)
    (localTensor_equivariant a f) (KPContActualCotangentPieceReconstruction.originalPoint a x)
  rw [hi] at h
  exact h.trans (congrArg f.val hi)

theorem cotangentZeroExtension_zero (a : ActualChart (U := U) (H := H))
    (f : localCotangentTests a) (b : ActualChart (U := U) (H := H)) (x : omega b)
    (hx : q b x.val ∉ a.baseDomain) : coefficient (cotangentZeroExtension a f).val b x = 0 :=
  KPContActualCotangentChartZeroExtension.extendedFields_zero_off a _ b x hx

theorem cotangentZeroExtension_support (a : ActualChart (U := U) (H := H))
    (f : localCotangentTests a) :
    tsupport (normSquare (cotangentZeroExtension a f).val) = localSupport a f.val := by
  rw [← cotangentSupport_eq]
  apply Set.Subset.antisymm
  · unfold cotangentSupport
    apply closure_minimal _ isClosed_closure
    rintro z ⟨b, x, hx, hn⟩
    by_contra hz
    exact hn (KPContActualCotangentChartZeroExtension.extendedFields_zero_off_base_support a
      f.val (localSupport a f.val) (fun y hy => subset_closure
        ⟨y.val, ⟨y.property, hy⟩, rfl⟩) b x (by rwa [hx]))
  · unfold localSupport cotangentSupport
    apply closure_mono
    rintro z ⟨y, ⟨hy, hn⟩, rfl⟩
    refine ⟨a, ⟨y, hy⟩, rfl, ?_⟩
    have hr := congrFun (cotangentZeroExtension_restrict a f) ⟨y, hy⟩
    change cotangentRestriction a (cotangentZeroExtension a f) ⟨y, hy⟩ ≠ 0
    rwa [hr]

theorem cotangentRestriction_regular (a : ActualChart (U := U) (H := H))
    (v : T_U F ζ hζ U R P H) :
    SmoothOnLift a (cotangentRestriction a v) ∧ CotangentEquivariant a (cotangentRestriction a v) :=
  ⟨v.property.1 a, v.val.property.2.1 a⟩

theorem scalarRestriction_support_subset (a : ActualChart (U := U) (H := H))
    (f : S_U F ζ hζ U R P H) : localSupport a (scalarRestriction a f) ⊆ scalarSupport f.val := by
  unfold localSupport scalarSupport
  apply closure_mono
  rintro z ⟨x, ⟨hx, hn⟩, rfl⟩
  exact ⟨a, ⟨x, hx⟩, rfl, hn⟩

theorem cotangentRestriction_support_subset (a : ActualChart (U := U) (H := H))
    (v : T_U F ζ hζ U R P H) :
    localSupport a (cotangentRestriction a v) ⊆ tsupport (normSquare v.val) := by
  rw [← cotangentSupport_eq]
  unfold localSupport cotangentSupport
  apply closure_mono
  rintro z ⟨x, ⟨hx, hn⟩, rfl⟩
  exact ⟨a, ⟨x, hx⟩, rfl, hn⟩
private theorem scalar_zero_off_support (f : S_U F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a)
    (hx : q a x.val ∉ scalarSupport f.val) : f.val a x = 0 := by
  by_contra hn
  exact hx (subset_closure ⟨a, x, rfl, hn⟩)
private theorem tensor_zero_off_support (v : T_U F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a)
    (hx : q a x.val ∉ tsupport (normSquare v.val)) : coefficient v.val a x = 0 := by
  rw [← cotangentSupport_eq] at hx
  by_contra hn
  exact hx (subset_closure ⟨a, x, rfl, hn⟩)
private theorem overlap_component (a b : ShrunkChart F ζ hζ U R P H)
    (x : M F) (hx : q a x ∈ b.baseDomain) : a.component = b.component := by
  obtain ⟨y, hy⟩ := hx
  have hh : (H.atlas U).components
      ⟨b.component, KPCuspSiegel.projection F
        (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H b.component) y.val⟩ =
    (H.atlas U).components
      ⟨a.component, KPCuspSiegel.projection F
        (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)
          (labeledA (placeEquiv F ζ hζ) x)⟩ := by
    simpa only [(H.atlas U).components_formula, ShrunkChart.toBase,
      KPContCotangentOverlapRationalBranches.q] using hy
  exact (congrArg Sigma.fst ((H.atlas U).components.injective hh)).symm
private theorem overlap_iff (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component) (x : M F) :
    (x ∈ omega a ∧ q a x ∈ b.baseDomain) ↔
      ∃ g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative a.component),
        x ∈ (make a b h g).arrow.domain := by
  rcases a with ⟨i,ca,oa,da,dao,dac,das,dai⟩
  rcases b with ⟨j,cb,ob,db,dbo,dbc,dbs,dbi⟩
  dsimp at h
  subst j
  constructor
  · rintro ⟨hx, y, hy⟩
    have hi : Function.Injective (KPFiniteCuspAtlas.componentMap F ζ hζ U
        ((H.atlas U).representative i)) := by
      intro u v huv
      have he : (H.atlas U).components ⟨i,u⟩ = (H.atlas U).components ⟨i,v⟩ := by
        simpa only [(H.atlas U).components_formula] using huv
      exact eq_of_heq (Sigma.mk.inj ((H.atlas U).components.injective he)).2
    obtain ⟨g,hg⟩ := Quotient.exact (hi hy)
    change g • labeledA (placeEquiv F ζ hζ) x = y.val at hg
    refine ⟨g, hx, ?_⟩
    change labeledA (placeEquiv F ζ hζ) (coord (ζ:=ζ) (hζ:=hζ) g.val x) ∈ db
    have ha : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ)
        (g • labeledA (placeEquiv F ζ hζ) x)) = g • labeledA (placeEquiv F ζ hζ) x := by
      funext k; simp [labeledA, labeledAInv]
    rw [coord]
    have ha' : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ)
        (g.val • labeledA (placeEquiv F ζ hζ) x)) = g.val • labeledA (placeEquiv F ζ hζ) x := by
      funext k; simp [labeledA, labeledAInv]
    rw [ha']
    change g • labeledA (placeEquiv F ζ hζ) x ∈ db
    rw [hg]
    exact y.property
  · rintro ⟨g,hx,hg⟩
    refine ⟨hx, ⟨⟨labeledA (placeEquiv F ζ hζ) (coord (ζ:=ζ) (hζ:=hζ) g.val x), hg⟩, ?_⟩⟩
    change KPContCotangentOverlapRationalBranches.q _ (coord (ζ:=ζ) (hζ:=hζ) g.val x) =
      KPContCotangentOverlapRationalBranches.q _ x
    unfold KPContCotangentOverlapRationalBranches.q coord
    have ha : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ)
        (g • labeledA (placeEquiv F ζ hζ) x)) = g • labeledA (placeEquiv F ζ hζ) x := by
      funext k; simp [labeledA, labeledAInv]
    have ha' : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ)
        (g.val • labeledA (placeEquiv F ζ hζ) x)) = g.val • labeledA (placeEquiv F ζ hζ) x := by
      funext k; simp [labeledA, labeledAInv]
    rw [ha']
    apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i))
    exact Quotient.sound ⟨g, rfl⟩

theorem scalar_eq_of_restriction (a : ActualChart (U := U) (H := H))
    (f g : S_U F ζ hζ U R P H) (hf : scalarSupport f.val ⊆ a.baseDomain)
    (hg : scalarSupport g.val ⊆ a.baseDomain)
    (he : scalarRestriction a f = scalarRestriction a g) : f = g := by
  apply Subtype.ext
  funext b x
  by_cases hx : q b x.val ∈ a.baseDomain
  · have hc := overlap_component b a x.val hx
    obtain ⟨u, hu⟩ := (overlap_iff b a hc x.val).mp ⟨x.property, hx⟩
    let y : omega a := ⟨coord (ζ := ζ) (hζ := hζ) u.val x.val, hu.2⟩
    have hfy := scalarCompatible_transform f.val f.property.2.1 b a hc u x y rfl
    have hgy := scalarCompatible_transform g.val g.property.2.1 b a hc u x y rfl
    have hy : f.val a y = g.val a y := congrFun he y
    rw [hfy, hgy] at hy
    exact mul_left_cancel₀ (Units.ne_zero _) hy
  · rw [scalar_zero_off_support f b x (fun h => hx (hf h)),
      scalar_zero_off_support g b x (fun h => hx (hg h))]

theorem cotangent_eq_of_restriction (a : ActualChart (U := U) (H := H))
    (v w : T_U F ζ hζ U R P H) (hv : tsupport (normSquare v.val) ⊆ a.baseDomain)
    (hw : tsupport (normSquare w.val) ⊆ a.baseDomain)
    (he : cotangentRestriction a v = cotangentRestriction a w) : v = w := by
  apply Subtype.ext
  apply Subtype.ext
  funext b x
  by_cases hx : q b x.val ∈ a.baseDomain
  · have hc := overlap_component b a x.val hx
    obtain ⟨u, hu⟩ := (overlap_iff b a hc x.val).mp ⟨x.property, hx⟩
    let e := make b a hc u
    let y : omega a := ⟨e.arrow.psi x.val, e.target_shrinking hu⟩
    have hfy := v.val.property.2.2 b a e x.val hu
    have hgy := w.val.property.2.2 b a e x.val hu
    have hy : coefficient v.val a y = coefficient w.val a y := congrFun he y
    change v.val.val a y = w.val.val a y at hy
    rw [hfy, hgy] at hy
    exact (T e.arrow x.val hu).injective hy
  · exact (tensor_zero_off_support v b x (fun h => hx (hv h))).trans
      (tensor_zero_off_support w b x (fun h => hx (hw h))).symm

structure Properties : Prop where
  cotangent_support : ∀ v : Family (U := U) (H := H),
    cotangentSupport v = tsupport (normSquare v)
  scalar_add_support : ∀ f g : S_U F ζ hζ U R P H,
    scalarSupport (f + g).val ⊆ scalarSupport f.val ∪ scalarSupport g.val
  scalar_smul_support : ∀ (c : ℂ) (f : S_U F ζ hζ U R P H),
    scalarSupport (c • f).val ⊆ scalarSupport f.val
  cotangent_add_support : ∀ v w : T_U F ζ hζ U R P H,
    cotangentSupport (v + w).val ⊆ cotangentSupport v.val ∪ cotangentSupport w.val
  cotangent_smul_support : ∀ (c : ℂ) (v : T_U F ζ hζ U R P H),
    cotangentSupport (c • v).val ⊆ cotangentSupport v.val
  scalar_represented : ∀ f : S_U F ζ hζ U R P H,
    sectionFields (scalarSections f) = f.val
  scalar_smooth : ∀ f : S_U F ζ hζ U R P H,
    IsSmoothSections F ζ hζ U R P H (scalarSections f)
  scalar_support : ∀ f : S_U F ζ hζ U R P H,
    scalarSupport f.val = tsupport (sectionNorm F ζ hζ U R P H (scalarSections f))
  original_scalar_realization : ∀ f : S_U F ζ hζ U R P H,
    (groupIdentification f).val = (H.atlas U).scalar_realization.symm (scalarSections f)
  covered_realization : ∀ f : S_U F ζ hζ U R P H,
    S F ζ hζ U R P H (scalarCovered f) = scalarSections f
  covered_support : ∀ f : S_U F ζ hζ U R P H,
    scalarSupport f.val = KPContSectorCoveredQuotientVocabulary.q F ζ hζ U ''
      tsupport (scalarCovered f).val
  group_lift : ∀ (f : S_U F ζ hζ U R P H)
      (g : KPSmoothActualFlowData.GInfinity F) (c : FiniteCover F ζ hζ),
    (scalarCovered f).val (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ g * (c : ActualCover F ζ hζ)))) =
      (groupIdentification f).val.val (KPMsFixedHaarDisintegration.archBasepoint F g, c)
  group_spherical : ∀ (f : S_U F ζ hζ U R P H)
      (g : KPSmoothActualFlowData.GInfinity F)
      (k : KPContSectorArchSphericalFibers.KInfinity F) (c : FiniteCover F ζ hζ),
    groupLift (groupIdentification f).val (g * k.val) c =
      groupLift (groupIdentification f).val g c
  group_level_fixed : ∀ (f : S_U F ζ hζ U R P H)
      (g : KPSmoothActualFlowData.GInfinity F) (c : FiniteCover F ζ hζ)
      (u : U.toOpenSubgroup),
    groupLift (groupIdentification f).val g (c * u.val) =
      groupLift (groupIdentification f).val g c
  group_genuine : ∀ (f : S_U F ζ hζ U R P H)
      (g : KPSmoothActualFlowData.GInfinity F) (c : FiniteCover F ζ hζ)
      (ε : rootsOfUnity 3 F),
    groupLift (groupIdentification f).val g (KPCuspGenuineMonodromy.central F ζ hζ ε * c) =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * groupLift (groupIdentification f).val g c
  covered_smooth_compact : ∀ f : S_U F ζ hζ U R P H,
    IsSmoothCovered F ζ hζ U (scalarCovered f) ∧ HasCompactSupport (scalarCovered f).val
  scalar_restriction_smooth : ∀ a (f : S_U F ζ hζ U R P H),
    SmoothOnLift a (scalarRestriction a f) ∧ ScalarEquivariant a (scalarRestriction a f)
  cotangent_restriction_smooth : ∀ a (v : T_U F ζ hζ U R P H),
    SmoothOnLift a (cotangentRestriction a v) ∧ CotangentEquivariant a (cotangentRestriction a v)
  scalar_restriction_extension : ∀ a (f : localScalarTests (U := U) (H := H) a),
    scalarRestriction a (scalarZeroExtension a f) = f.val
  cotangent_restriction_extension : ∀ a (v : localCotangentTests (U := U) (H := H) a),
    cotangentRestriction a (cotangentZeroExtension a v) = v.val
  scalar_extension_zero : ∀ a (f : localScalarTests (U := U) (H := H) a)
      (b : ActualChart (U := U) (H := H)) (x : omega b),
    q b x.val ∉ a.baseDomain → (scalarZeroExtension a f).val b x = 0
  cotangent_extension_zero : ∀ a (v : localCotangentTests (U := U) (H := H) a)
      (b : ActualChart (U := U) (H := H)) (x : omega b),
    q b x.val ∉ a.baseDomain → coefficient (cotangentZeroExtension a v).val b x = 0
  scalar_extension_support : ∀ a (f : localScalarTests (U := U) (H := H) a),
    scalarSupport (scalarZeroExtension a f).val = localSupport a f.val
  cotangent_extension_support : ∀ a (v : localCotangentTests (U := U) (H := H) a),
    tsupport (normSquare (cotangentZeroExtension a v).val) = localSupport a v.val
  scalar_local_restriction : ∀ a (f : S_U F ζ hζ U R P H),
    scalarSupport f.val ⊆ a.baseDomain → scalarRestriction a f ∈ localScalarTests a
  cotangent_local_restriction : ∀ a (v : T_U F ζ hζ U R P H),
    tsupport (normSquare v.val) ⊆ a.baseDomain → cotangentRestriction a v ∈ localCotangentTests a
  scalar_extension_restriction : ∀ a (f : S_U F ζ hζ U R P H)
      (h : scalarRestriction a f ∈ localScalarTests a),
    scalarSupport f.val ⊆ a.baseDomain → scalarZeroExtension a ⟨scalarRestriction a f,h⟩ = f
  cotangent_extension_restriction : ∀ a (v : T_U F ζ hζ U R P H)
      (h : cotangentRestriction a v ∈ localCotangentTests a),
    tsupport (normSquare v.val) ⊆ a.baseDomain → cotangentZeroExtension a ⟨cotangentRestriction a v,h⟩ = v

end DedekindZetaZeroFree.KPContActualSectorSmoothTestModules

namespace DedekindZetaZeroFree

theorem kp_cont_actual_sector_smooth_test_modules
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualSectorSmoothTestModules.Properties (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H) := by
  letI : T2Space (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
    KPContSectorQuotientRelationsComparison.instT2SpaceRawXU F ζ hζ U
  open KPContActualSectorSmoothTestModules KPContActualCotangentMeasurableFamilies
    KPContSectorSmoothFramesSupport KPContSectorScalarLineAlgebra in
    refine {
      cotangent_support := cotangentSupport_eq
      scalar_add_support := fun f g => scalarSupport_add_subset f.val g.val
      scalar_smul_support := fun c f => scalarSupport_smul_subset c f.val
      cotangent_add_support := fun v w => cotangentSupport_add v.val w.val
      cotangent_smul_support := fun c v => cotangentSupport_smul c v.val
      scalar_represented := scalarSections_fields
      scalar_smooth := scalarSections_smooth
      scalar_support := fun f => by
        rw [← scalarSupport_sectionFields, scalarSections_fields]
      original_scalar_realization := fun _ => rfl
      covered_realization := fun f => by simp [scalarCovered, S, groupIdentification]
      covered_support := fun f => ?_
      group_lift := fun f g c => ?_
      group_spherical := fun f g k c => ?_
      group_level_fixed := fun f g c u => (groupIdentification f).val.property.2.2 _ _ _
      group_genuine := fun f g c ε => (groupIdentification f).val.property.2.1 _ _ _
      covered_smooth_compact := fun f => ?_
      scalar_restriction_smooth := fun a f => ⟨f.property.1 a, f.property.2.1.1 a⟩
      cotangent_restriction_smooth := cotangentRestriction_regular
      scalar_restriction_extension := fun a f => funext (ScalarExtension.fields_source a f)
      cotangent_restriction_extension := cotangentZeroExtension_restrict
      scalar_extension_zero := fun a f b x hx =>
        ScalarExtension.fields_off_support a f b x (fun h => hx (f.property.2.2.2 h))
      cotangent_extension_zero := cotangentZeroExtension_zero
      scalar_extension_support := ScalarExtension.fields_support
      cotangent_extension_support := cotangentZeroExtension_support
      scalar_local_restriction := fun a f hf => ?_
      cotangent_local_restriction := fun a v hv => ?_
      scalar_extension_restriction := fun a f h hf => ?_
      cotangent_extension_restriction := fun a v h hv => ?_ }
    · rw [← tsupport_sectionNorm F ζ hζ U R P H (scalarCovered f)]
      have he : S F ζ hζ U R P H (scalarCovered f) = scalarSections f := by
        simp [scalarCovered, S, groupIdentification]
      rw [he, ← scalarSupport_sectionFields, scalarSections_fields]
    · have he : J F ζ hζ U (scalarCovered f) = (groupIdentification f).val := by
        simp [scalarCovered]
      rw [← he]
      exact group_lift_formula F ζ hζ U (scalarCovered f) g c
    · unfold groupLift
      have he : KPMsFixedHaarDisintegration.archBasepoint F (g * k.val) =
          KPMsFixedHaarDisintegration.archBasepoint F g :=
        ((KPContSectorArchSphericalFibers.archBasepoint_eq_iff F g (g * k.val)).mpr ⟨k, rfl⟩).symm
      rw [he]
    · refine ⟨?_, (groupIdentification f).property.2⟩
      intro c
      simpa [IsSmoothCovered, scalarCovered] using (groupIdentification f).property.1 c
    · have hs := scalarRestriction_support_subset a f
      exact ⟨f.property.1 a, f.property.2.1.1 a,
        f.property.2.2.of_isClosed_subset isClosed_closure hs, hs.trans hf⟩
    · have hs := cotangentRestriction_support_subset a v
      exact ⟨v.property.1 a, v.val.property.2.1 a,
        v.property.2.of_isClosed_subset isClosed_closure hs, hs.trans hv⟩
    · refine scalar_eq_of_restriction a _ f ?_ hf ?_
      · change scalarSupport (sectionFields (ScalarExtension.sections a _)) ⊆ _
        rw [ScalarExtension.fields_support]
        exact (⟨scalarRestriction a f, h⟩ : localScalarTests a).property.2.2.2
      · exact funext (ScalarExtension.fields_source a ⟨scalarRestriction a f, h⟩)
    · refine cotangent_eq_of_restriction a _ v ?_ hv ?_
      · rw [cotangentZeroExtension_support]
        exact (⟨cotangentRestriction a v, h⟩ : localCotangentTests a).property.2.2.2
      · exact cotangentZeroExtension_restrict a ⟨cotangentRestriction a v, h⟩

end DedekindZetaZeroFree

end
