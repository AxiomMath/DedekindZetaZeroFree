module

public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.SmoothScalarAndCotangentTests

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorTestEmbeddings

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualSectorSmoothTestModules
open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra
open KPContSectorFixedPushforwardSupport KPContSectorSmoothFramesSupport
open KPContActualCotangentMeasurableFamilies KPContActualCotangentChartRestriction
open KPContCotangentOverlapRationalBranches
open KPContActualCotangentCountableShrinking KPContActualCotangentPieceHilbertSum
open KPContCotangentActualOverlap

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem scalarCovered_continuous (f : S_U F ζ hζ U R P H) :
    Continuous (scalarCovered f).val := by
  have hspec := Classical.choose_spec
    (scalar_gluing (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) f)
  have hsmooth : IsSmoothSections F ζ hζ U R P H (scalarSections f) := hspec.1.1
  have hcov : scalarCovered f =
      KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H (scalarSections f) := rfl
  rw [hcov]
  exact (KPContSectorLineL2Isometry.continuous_iff F ζ hζ U R P H (scalarSections f)).mp
    (fun i => (hsmooth i).continuous)

private theorem scalarCovered_hasCompactSupport (f : S_U F ζ hζ U R P H) :
    HasCompactSupport (scalarCovered f).val := by
  have hspec := Classical.choose_spec
    (scalar_gluing (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) f)
  have hcomp0 : HasCompactSupport (sectionNorm F ζ hζ U R P H (scalarSections f)) := hspec.1.2.1
  have hcov : scalarCovered f =
      KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H (scalarSections f) := rfl
  have hS : S F ζ hζ U R P H (scalarCovered f) = scalarSections f := by
    rw [hcov, KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
    simp
  rw [hasCompactSupport_iff F ζ hζ U R P H (scalarCovered f), hS]
  exact hcomp0

theorem scalar_memLp (f : S_U F ζ hζ U R P H) :
    MemLp (scalarCovered f).val 2 (coveredMeasure F ζ hζ R U) :=
  KPContSectorFixedMeasureLocalFiniteness.compactSupport_memLp
    F ζ hζ R U (scalarCovered f).val (scalarCovered_continuous f)
    (scalarCovered_hasCompactSupport f)

theorem scalar_class_mem_sector (f : S_U F ζ hζ U R P H) :
    (scalar_memLp f).toLp (scalarCovered f).val ∈
      KPContSectorClosedLpSubspace.H F ζ hζ R U := by
  have hmeas : Measurable (scalarCovered f).val := (scalarCovered_continuous f).measurable
  let fB : KPContSectorLineL2Isometry.BorelL2Scalars F ζ hζ U R :=
    ⟨scalarCovered f, hmeas, scalar_memLp f⟩
  have hmem : (KPContSectorLineL2Isometry.scalarEmbedding F ζ hζ U R P H fB).val ∈
      KPContSectorClosedLpSubspace.H F ζ hζ R U :=
    (KPContSectorLineL2Isometry.scalarEmbedding F ζ hζ U R P H fB).property
  rw [KPContSectorLineL2Isometry.scalarEmbedding_coe F ζ hζ U R P H fB] at hmem
  exact hmem

def iota : S_U F ζ hζ U R P H →ₗ[ℂ] KPContSectorClosedLpSubspace.H F ζ hζ R U where
  toFun f := ⟨(scalar_memLp f).toLp (scalarCovered f).val, scalar_class_mem_sector f⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    change (scalar_memLp (f + g)).toLp (scalarCovered (f + g)).val =
      (scalar_memLp f).toLp (scalarCovered f).val +
        (scalar_memLp g).toLp (scalarCovered g).val
    apply Lp.ext
    have hsc : scalarCovered (f + g) = scalarCovered f + scalarCovered g := by
      simp only [scalarCovered, map_add, Submodule.coe_add]
    filter_upwards [MemLp.coeFn_toLp (scalar_memLp (f + g)),
      MemLp.coeFn_toLp (scalar_memLp f), MemLp.coeFn_toLp (scalar_memLp g),
      Lp.coeFn_add ((scalar_memLp f).toLp (scalarCovered f).val)
        ((scalar_memLp g).toLp (scalarCovered g).val)] with x h1 h2 h3 h4
    rw [h1, h4]
    simp only [Pi.add_apply]
    rw [h2, h3, hsc]
    simp only [Submodule.coe_add, Pi.add_apply]
  map_smul' := by
    intro c f
    apply Subtype.ext
    change (scalar_memLp (c • f)).toLp (scalarCovered (c • f)).val =
      c • (scalar_memLp f).toLp (scalarCovered f).val
    apply Lp.ext
    have hsc : scalarCovered (c • f) = c • scalarCovered f := by
      simp only [scalarCovered, map_smul, Submodule.coe_smul]
    filter_upwards [MemLp.coeFn_toLp (scalar_memLp (c • f)),
      MemLp.coeFn_toLp (scalar_memLp f),
      Lp.coeFn_smul c ((scalar_memLp f).toLp (scalarCovered f).val)] with x h1 h2 h3
    rw [h1, h3]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h2, hsc]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]

private theorem continuous_iff_isQuotientMap {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {q : X → Y} (hq : IsQuotientMap q)
    (f : Y → Z) : Continuous f ↔ Continuous (f ∘ q) := by
  refine ⟨fun h => h.comp hq.continuous, fun h => ?_⟩
  exact Continuous.mk fun s hs => by
    rw [← hq.isOpen_preimage]
    exact h.isOpen_preimage s hs

private lemma q_coordinates (a : ActualChart (U := U) (H := H)) (y : a.domain) :
    q a (coordinates a y).val = a.toBase y := by
  have hi : ∀ z : KPCuspGenuineMonodromy.SymmetricSpace F,
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
    intro z; funext k; simp [labeledA, labeledAInv]
  simp only [ShrunkChart.toBase, KPContCotangentOverlapRationalBranches.q, coordinates]
  rw [hi]

private theorem continuous_normSquare_of_smooth (v : Family (U := U) (H := H))
    (hv : ∀ a, SmoothOnLift a (coefficient v a)) : Continuous (normSquare v) := by
  let cover := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
  refine continuous_of_cover_nhds (s := fun n => (cover.chart n).baseDomain) ?_ ?_
  · intro x
    have hx : x ∈ ⋃ n, (cover.chart n).baseDomain := by
      rw [cover.covers]; exact Set.mem_univ x
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact ⟨n, (cover.properties n).base_open.mem_nhds hn⟩
  · intro n
    set a := cover.chart n
    have hP := every_shrunkChart_properties F ζ hζ U R P H a
    obtain ⟨g, hg, hgval⟩ := hv a
    have hgc : Continuous (fun y : a.domain => g ((coordinates a y).val)) :=
      (hg.continuousOn.domRestrict).comp (coordinates_continuous a)
    have hloc : Continuous (fun y : a.domain => ‖localCoefficient a v y‖₊ ^ 2) := by
      have heq : (fun y : a.domain => ‖localCoefficient a v y‖₊ ^ 2) =
          fun y : a.domain => ‖g ((coordinates a y).val)‖₊ ^ 2 := by
        funext y
        rw [localCoefficient, hgval]
      rw [heq]
      exact (hgc.nnnorm).pow 2
    have hquot : (fun z : a.baseDomain => normSquare v z.val) ∘ a.quotientMap =
        fun y : a.domain => ‖localCoefficient a v y‖₊ ^ 2 := by
      funext y
      show normSquare v (a.toBase y) = ‖localCoefficient a v y‖₊ ^ 2
      rw [← q_coordinates a y, normSquare_chart]
      rfl
    have hF' : Continuous (fun z : a.baseDomain => normSquare v z.val) :=
      (continuous_iff_isQuotientMap hP.quotient _).mpr (hquot ▸ hloc)
    rw [continuousOn_iff_continuous_domRestrict]
    exact hF'

theorem cotangent_squareFinite (W : T_U F ζ hζ U R P H) : squareFinite W.val := by
  have hcont : Continuous (normSquare W.val) :=
    continuous_normSquare_of_smooth W.val W.property.1
  have hcs : HasCompactSupport (normSquare W.val) := W.property.2
  have hcontR : Continuous (fun x => (normSquare W.val x : ℝ)) :=
    continuous_subtype_val.comp hcont
  letI : IsFiniteMeasureOnCompacts (KPContActualSectorCotangentL2.muU F ζ hζ U R P) :=
    KPContSectorFixedMeasureLocalFiniteness.sphericalMeasure_finiteOnCompacts F ζ hζ R P U
  obtain ⟨C, hC⟩ := hcs.isCompact.exists_bound_of_continuousOn hcontR.continuousOn
  have hC' : ∀ x ∈ tsupport (normSquare W.val), (normSquare W.val x : ℝ) ≤ C := by
    intro x hx
    simpa only [Real.norm_of_nonneg (normSquare W.val x).coe_nonneg] using hC x hx
  rw [squareFinite]
  have hK : MeasurableSet (tsupport (normSquare W.val)) := (isClosed_tsupport _).measurableSet
  have key : (∫⁻ x, ENNReal.ofReal ((normSquare W.val x : ℝ))
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) ≤
      ENNReal.ofReal C * (KPContActualSectorCotangentL2.muU F ζ hζ U R P)
        (tsupport (normSquare W.val)) := by
    calc ∫⁻ x, ENNReal.ofReal ((normSquare W.val x : ℝ))
          ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P
        ≤ ∫⁻ x, (tsupport (normSquare W.val)).indicator
            (fun _ => ENNReal.ofReal C) x
          ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
          apply lintegral_mono
          intro x
          by_cases hx : x ∈ tsupport (normSquare W.val)
          · rw [Set.indicator_of_mem hx]
            exact ENNReal.ofReal_le_ofReal (hC' x hx)
          · rw [Set.indicator_of_notMem hx]
            have hz : normSquare W.val x = 0 := image_eq_zero_of_notMem_tsupport hx
            simp [hz]
      _ = ENNReal.ofReal C * (KPContActualSectorCotangentL2.muU F ζ hζ U R P)
            (tsupport (normSquare W.val)) := lintegral_indicator_const hK _
  exact lt_of_le_of_lt key (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hcs.measure_lt_top)

def cotangentSquareFamily : T_U F ζ hζ U R P H →ₗ[ℂ]
    SquareFiniteFamily (U := U) (H := H) where
  toFun W := ⟨W.val, cotangent_squareFinite W⟩
  map_add' := by
    intro W Z
    apply Subtype.ext
    simp only [Submodule.coe_add]
  map_smul' := by
    intro c W
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply]

def j : T_U F ζ hζ U R P H →ₗ[ℂ] KPContActualSectorCotangentL2.V F ζ hζ U R P H :=
  (KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H).comp cotangentSquareFamily

private theorem chi_unit (i : Fin (H.atlas U).componentCount) (ε : rootsOfUnity 3 F) :
    ‖(KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)‖ = 1 :=
  ((H.atlas U).line i).unitary ε

private theorem chi_unit' (i : Fin (H.atlas U).componentCount) (ε : rootsOfUnity 3 F) :
    ‖(chi F ζ hζ ε : ℂ)‖ = 1 := chi_norm F ζ hζ ε

private theorem inner_mul_mul_of_norm_one (c a b : ℂ) (hc : ‖c‖ = 1) :
    inner ℂ (c * a) (c * b) = inner ℂ a b := by
  rw [← smul_eq_mul, ← smul_eq_mul, inner_smul_left, inner_smul_right, ← mul_assoc]
  have h : (starRingEnd ℂ) c * c = 1 := by
    rw [RCLike.conj_mul, hc]
    simp
  rw [h, one_mul]

private theorem scalarPair_covariant (s t : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount)
    (γ : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
    (x : SymmetricSpace F) :
    inner ℂ ((s i).val ((γ : KPCuspArithmetic.PGL2 F) • x))
        ((t i).val ((γ : KPCuspArithmetic.PGL2 F) • x)) =
      inner ℂ ((s i).val x) ((t i).val x) := by
  rw [(s i).property.2 γ x, (t i).property.2 γ x]
  exact inner_mul_mul_of_norm_one _ _ _ (chi_unit (H := H) i (((H.atlas U).line i).rho γ))

 theorem scalarPair_invariant (s t : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x y : SymmetricSpace F)
    (hxy : MulAction.orbitRel
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
      (SymmetricSpace F) x y) :
    inner ℂ ((s i).val x) ((t i).val x) = inner ℂ ((s i).val y) ((t i).val y) := by
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hxy)
  rw [← hγ]
  exact scalarPair_covariant s t i γ y

 def pairOnSigma (s t : Sections F ζ hζ U R P H) :
    (Σ i : Fin (H.atlas U).componentCount,
      KPCuspSiegel.OrbitQuotient F
        (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))) → ℂ :=
  fun p => Quotient.lift (fun x => inner ℂ ((s p.1).val x) ((t p.1).val x))
    (scalarPair_invariant s t p.1) p.2

 def scalarPairSections (s t : Sections F ζ hζ U R P H) :
    KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ :=
  fun b => pairOnSigma s t ((H.atlas U).components.symm b)

private theorem scalarPairSections_components (s t : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (z : SymmetricSpace F) :
    scalarPairSections s t ((H.atlas U).components ⟨i, Quotient.mk _ z⟩) =
      inner ℂ ((s i).val z) ((t i).val z) := by
  have h1 : pairOnSigma s t
      ((H.atlas U).components.symm ((H.atlas U).components ⟨i, Quotient.mk _ z⟩)) =
      pairOnSigma s t ⟨i, Quotient.mk _ z⟩ :=
    congrArg (pairOnSigma s t) (Homeomorph.symm_apply_apply _ _)
  refine h1.trans ?_
  exact Quotient.lift_mk
    (s := MulAction.orbitRel
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
      (SymmetricSpace F))
    (f := fun x => inner ℂ ((s i).val x) ((t i).val x))
    (h := scalarPair_invariant s t i) z

private theorem sectionFields_apply (s : Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    sectionFields s a x = (s a.component).val (labeledA (placeEquiv F ζ hζ) x.val) := by
  have hcoe : (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient s x.val =
      (KPCuspGenuineMonodromy.chi F ζ hζ
          ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).splitting x.val) : ℂ) *
        (s a.component).val
          ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).kind.representative •
            labeledA (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).places x.val) :=
    rfl
  rw [sectionFields, hcoe]
  simp [KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative]

private theorem scalarPairSections_chart (s t : Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    scalarPairSections s t (q a x.val) =
      inner ℂ (sectionFields s a x) (sectionFields t a x) := by
  have hq : q a x.val = (H.atlas U).components
      ⟨a.component, Quotient.mk _ (labeledA (placeEquiv F ζ hζ) x.val)⟩ := by
    simp only [KPContCotangentOverlapRationalBranches.q, KPCuspSiegel.projection,
      (H.atlas U).components_formula]
  rw [hq, scalarPairSections_components, sectionFields_apply, sectionFields_apply]

theorem scalarPair_descends (f g : S_U F ζ hζ U R P H) :
    ∃! p : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ,
      Continuous p ∧ ∀ (a : ActualChart (U := U) (H := H)) (x : omega a),
        p (KPContCotangentOverlapRationalBranches.q a x.val) =
          inner ℂ (f.val a x) (g.val a x) := by
  have hfs := Classical.choose_spec (scalar_gluing (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) f)
  have hgs := Classical.choose_spec (scalar_gluing (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) g)
  have hfsmooth : IsSmoothSections F ζ hζ U R P H (scalarSections f) := hfs.1.1
  have hgsmooth : IsSmoothSections F ζ hζ U R P H (scalarSections g) := hgs.1.1
  have hfval : sectionFields (scalarSections f) = f.val := hfs.1.2.2
  have hgval : sectionFields (scalarSections g) = g.val := hgs.1.2.2
  refine ⟨scalarPairSections (scalarSections f) (scalarSections g), ⟨?_, ?_⟩, ?_⟩
  ·
    let cover := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
    refine continuous_of_cover_nhds (s := fun n => (cover.chart n).baseDomain) ?_ ?_
    · intro x
      have hx : x ∈ ⋃ n, (cover.chart n).baseDomain := by
        rw [cover.covers]; exact Set.mem_univ x
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact ⟨n, (cover.properties n).base_open.mem_nhds hn⟩
    · intro n
      set a := cover.chart n
      have hP := every_shrunkChart_properties F ζ hζ U R P H a
      rw [continuousOn_iff_continuous_domRestrict]
      refine (continuous_iff_isQuotientMap hP.quotient
        (fun z : a.baseDomain =>
          scalarPairSections (scalarSections f) (scalarSections g) z.val)).mpr ?_
      change Continuous (fun y : a.domain =>
        scalarPairSections (scalarSections f) (scalarSections g) (a.toBase y))
      have hbase : (fun y : a.domain =>
            scalarPairSections (scalarSections f) (scalarSections g) (a.toBase y)) =
          fun y : a.domain => inner ℂ ((scalarSections f a.component).val y.val)
            ((scalarSections g a.component).val y.val) := by
        funext y
        have h1 : a.toBase y = (H.atlas U).components
            ⟨a.component, Quotient.mk _ y.val⟩ := by
          simp only [ShrunkChart.toBase, KPCuspSiegel.projection,
            (H.atlas U).components_formula]
        rw [h1, scalarPairSections_components]
      rw [hbase]
      exact continuous_inner.comp
        (((hfsmooth a.component).continuous.comp continuous_subtype_val).prodMk
          ((hgsmooth a.component).continuous.comp continuous_subtype_val))
  · intro a x
    rw [scalarPairSections_chart, hfval, hgval]
  · intro p' hp'
    obtain ⟨-, hchart'⟩ := hp'
    funext z
    let cover := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
    have hz : z ∈ ⋃ n, (cover.chart n).baseDomain := by
      rw [cover.covers]; exact Set.mem_univ z
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    set a := cover.chart n
    obtain ⟨y, hy⟩ := hn
    rw [← hy, ← q_coordinates a y, hchart' a (coordinates a y),
      scalarPairSections_chart (scalarSections f) (scalarSections g) a (coordinates a y),
      hfval, hgval]

def scalarPair (f g : S_U F ζ hζ U R P H) : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ :=
  Classical.choose (scalarPair_descends f g)

def localScalarCoefficient (a : ActualChart (U := U) (H := H))
    (f : S_U F ζ hζ U R P H) (y : a.domain) : ℂ :=
  f.val a (KPContActualCotangentPieceHilbertSum.coordinates a y)

structure Properties : Prop where
  scalar_base_memLp : ∀ f : S_U F ζ hζ U R P H,
    MemLp (sectionNorm F ζ hζ U R P H (scalarSections f)) 2
      (KPContActualSectorCotangentL2.muU F ζ hζ U R P)
  cotangent_base_memLp : ∀ W : T_U F ζ hζ U R P H,
    MemLp (fun x => Real.sqrt (normSquare W.val x : ℝ)) 2
      (KPContActualSectorCotangentL2.muU F ζ hζ U R P)
  scalar_local_memLp : ∀ (a : ActualChart (U := U) (H := H)) (f : S_U F ζ hζ U R P H),
    MemLp (localScalarCoefficient a f) 2 a.liftedMeasure
  cotangent_local_memLp : ∀ (a : ActualChart (U := U) (H := H)) (W : T_U F ζ hζ U R P H),
    MemLp (localCoefficient a W.val) 2 a.liftedMeasure
  iota_injective : Function.Injective (iota (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H))
  j_injective : Function.Injective (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H))
  scalar_continuous : ∀ f : S_U F ζ hζ U R P H, Continuous (scalarCovered f).val
  scalar_represented : ∀ f : S_U F ζ hζ U R P H,
    (iota f : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) =
      (scalar_memLp f).toLp (scalarCovered f).val

  scalar_unique_continuous : ∀ f : S_U F ζ hζ U R P H,
    ∃! g : GenuineCoveredScalars F ζ hζ U,
      Continuous g.val ∧ g.val =ᵐ[coveredMeasure F ζ hζ R U]
        (iota f : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U)
  cotangent_continuous : ∀ (W : T_U F ζ hζ U R P H) (a : ActualChart (U := U) (H := H)),
    Continuous (coefficient W.val a)
  cotangent_represented : ∀ W : T_U F ζ hζ U R P H,
    j W = KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H (cotangentSquareFamily W)

  cotangent_unique_continuous : ∀ W : T_U F ζ hζ U R P H,
    ∃! v : Family (U := U) (H := H),
      (∀ a : ActualChart (U := U) (H := H), Continuous (coefficient v a)) ∧
        AeEquivalent v W.val
  scalar_pair_chart : ∀ (f g : S_U F ζ hζ U R P H)
      (a : ActualChart (U := U) (H := H)) (x : omega a),
    scalarPair f g (KPContCotangentOverlapRationalBranches.q a x.val) =
      inner ℂ (f.val a x) (g.val a x)
  scalar_pair_integrable : ∀ f g : S_U F ζ hζ U R P H,
    Integrable (scalarPair f g) (KPContActualSectorCotangentL2.muU F ζ hζ U R P)
  cotangent_pair_integrable : ∀ W Z : T_U F ζ hζ U R P H,
    Integrable (pair W.val Z.val) (KPContActualSectorCotangentL2.muU F ζ hζ U R P)
  scalar_inner : ∀ f g : S_U F ζ hζ U R P H,
    inner ℂ (iota f) (iota g) =
      ∫ x, scalarPair f g x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P
  cotangent_inner : ∀ W Z : T_U F ζ hζ U R P H,
    inner ℂ (j W) (j Z) =
      ∫ x, pair W.val Z.val x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P

  scalar_chart_integral : ∀ (a : ActualChart (U := U) (H := H)) (f g : S_U F ζ hζ U R P H),
    (∫ x in a.baseDomain, scalarPair f g x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) =
      ∫ y, inner ℂ (localScalarCoefficient a f y) (localScalarCoefficient a g y) ∂a.liftedMeasure
  cotangent_chart_integral : ∀ (a : ActualChart (U := U) (H := H)) (W Z : T_U F ζ hζ U R P H),
    (∫ x in a.baseDomain, pair W.val Z.val x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) =
      ∫ y, inner ℂ (localCoefficient a W.val y) (localCoefficient a Z.val y) ∂a.liftedMeasure

theorem cotangent_local_memLp (a : ActualChart (U := U) (H := H)) (W : T_U F ζ hζ U R P H) :
    MemLp (localCoefficient a W.val) 2 a.liftedMeasure :=
  localCoefficient_memLp (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) a
    ⟨W.val, cotangent_squareFinite W⟩

theorem cotangent_base_memLp (W : T_U F ζ hζ U R P H) :
    MemLp (fun x => Real.sqrt (normSquare W.val x : ℝ)) 2
      (KPContActualSectorCotangentL2.muU F ζ hζ U R P) := by
  have hm : Measurable (fun b => Real.sqrt (normSquare W.val b : ℝ)) :=
    (measurable_normSquare W.val).coe_nnreal_real.sqrt
  have hsq : (fun b => ‖Real.sqrt (normSquare W.val b : ℝ)‖ ^ 2) =
      (fun b => (normSquare W.val b : ℝ)) := by
    funext b
    rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (NNReal.coe_nonneg _)]
  rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable, hsq]
  exact KPContActualCotangentIntrinsicHilbertIntegral.integrable_normSquare
    (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H)
    ⟨W.val, cotangent_squareFinite W⟩

theorem cotangent_pair_integrable (W Z : T_U F ζ hζ U R P H) :
    Integrable (pair W.val Z.val) (KPContActualSectorCotangentL2.muU F ζ hζ U R P) :=
  KPContActualCotangentIntrinsicHilbertIntegral.integrable_pair
    (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H)
    ⟨W.val, cotangent_squareFinite W⟩ ⟨Z.val, cotangent_squareFinite Z⟩

theorem cotangent_inner
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (W Z : T_U F ζ hζ U R P H) :
    inner ℂ (j W) (j Z) =
      ∫ x, pair W.val Z.val x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
  have h := (kp_cont_actual_sector_cotangent_l2 F ζ hζ R.adelicHaar R.adelic_isHaar U R rfl P H
    realization).inner_integral (j W) (j Z) (cotangentSquareFamily W)
      (cotangentSquareFamily Z) rfl rfl
  have hcoe : ∀ Y : T_U F ζ hζ U R P H, (cotangentSquareFamily Y).val = Y.val :=
    fun _ => rfl
  simpa only [hcoe] using h

theorem scalar_pair_chart (f g : S_U F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    scalarPair f g (KPContCotangentOverlapRationalBranches.q a x.val) =
      inner ℂ (f.val a x) (g.val a x) :=
  (Classical.choose_spec (scalarPair_descends f g)).1.2 a x

theorem scalar_pair_continuous (f g : S_U F ζ hζ U R P H) :
    Continuous (scalarPair f g) :=
  (Classical.choose_spec (scalarPair_descends f g)).1.1

theorem scalar_represented (f : S_U F ζ hζ U R P H) :
    (iota f : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) =
      (scalar_memLp f).toLp (scalarCovered f).val := rfl

theorem cotangent_represented (W : T_U F ζ hζ U R P H) :
    j W = KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H (cotangentSquareFamily W) := rfl

theorem S_scalarCovered (f : S_U F ζ hζ U R P H) :
    S F ζ hζ U R P H (scalarCovered f) = scalarSections f := by
  have h1 : (groupIdentification (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P)
      (H := H) f).val = (H.atlas U).scalar_realization.symm (scalarSections f) := rfl
  rw [scalarCovered, h1]
  simp only [S, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

theorem cotangent_continuous (W : T_U F ζ hζ U R P H) (a : ActualChart (U := U) (H := H)) :
    Continuous (coefficient W.val a) := by
  obtain ⟨g, hg, hgval⟩ := W.property.1 a
  have h := hg.continuousOn.domRestrict
  have heq : ((omega a).domRestrict g) = coefficient W.val a := funext fun x => hgval x
  rw [heq] at h
  exact h

theorem iota_injective :
    Function.Injective (iota (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)) := by
  letI : (coveredMeasure F ζ hζ R U).IsOpenPosMeasure :=
    (levelSupport F ζ hζ R P
      (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1 U).covered_open_positive
  intro f g hfg
  have h1 : (scalarCovered f).val =ᵐ[coveredMeasure F ζ hζ R U] (scalarCovered g).val :=
    (MemLp.toLp_eq_toLp_iff (scalar_memLp f) (scalar_memLp g)).mp (congrArg Subtype.val hfg)
  have h2 : scalarCovered f = scalarCovered g :=
    Subtype.ext (Measure.eq_of_ae_eq h1 (scalarCovered_continuous f) (scalarCovered_continuous g))
  have h5 : groupIdentification (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P)
      (H := H) f = groupIdentification (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R)
      (P := P) (H := H) g := by
    apply Subtype.ext
    have h6 := congrArg (fun w : GenuineCoveredScalars F ζ hζ U => J F ζ hζ U w) h2
    simpa only [scalarCovered, LinearEquiv.apply_symm_apply] using h6
  exact (groupIdentification (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P)
    (H := H)).injective h5

theorem scalar_unique_continuous (f : S_U F ζ hζ U R P H) :
    ∃! g : GenuineCoveredScalars F ζ hζ U,
      Continuous g.val ∧ g.val =ᵐ[coveredMeasure F ζ hζ R U]
        (iota f : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) := by
  letI : (coveredMeasure F ζ hζ R U).IsOpenPosMeasure :=
    (levelSupport F ζ hζ R P
      (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1 U).covered_open_positive
  have hae : (scalarCovered f).val =ᵐ[coveredMeasure F ζ hζ R U]
      (iota f : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) :=
    (MemLp.coeFn_toLp (scalar_memLp f)).symm
  refine ⟨scalarCovered f, ⟨scalarCovered_continuous f, hae⟩, ?_⟩
  intro g hg
  exact Subtype.ext (Measure.eq_of_ae_eq (hg.2.trans hae.symm) hg.1 (scalarCovered_continuous f))

theorem scalar_chart_integral (a : ActualChart (U := U) (H := H)) (f g : S_U F ζ hζ U R P H) :
    (∫ x in a.baseDomain, scalarPair f g x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) =
      ∫ y, inner ℂ (localScalarCoefficient a f y) (localScalarCoefficient a g y)
        ∂a.liftedMeasure := by
  have hP := every_shrunkChart_properties F ζ hζ U R P H a
  rw [← hP.exact_pushforward,
    integral_map hP.measurable.aemeasurable (scalar_pair_continuous f g).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with y
  rw [localScalarCoefficient, localScalarCoefficient, ← q_coordinates a y]
  exact scalar_pair_chart f g a (coordinates a y)

private theorem exists_chart_point (b : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∃ (a : ActualChart (U := U) (H := H)) (x : omega a),
      KPContCotangentOverlapRationalBranches.q a x.val = b := by
  let cover := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
  have hb : b ∈ ⋃ n, (cover.chart n).baseDomain := by rw [cover.covers]; trivial
  obtain ⟨n, y, hy⟩ := Set.mem_iUnion.mp hb
  exact ⟨cover.chart n, coordinates (cover.chart n) y, (q_coordinates _ _).trans hy⟩

theorem tsupport_scalarPair_subset (f g : S_U F ζ hζ U R P H) :
    tsupport (scalarPair f g) ⊆ scalarSupport g.val := by
  refine closure_mono (fun x hx => ?_)
  obtain ⟨a, y, hy⟩ := exists_chart_point x
  refine ⟨a, y, hy, ?_⟩
  have hpx : scalarPair f g (q a y.val) ≠ 0 := by rw [hy]; exact hx
  rw [scalar_pair_chart f g a y] at hpx
  intro hw
  exact hpx (by rw [hw, inner_zero_right])

theorem scalar_pair_integrable (f g : S_U F ζ hζ U R P H) :
    Integrable (scalarPair f g) (KPContActualSectorCotangentL2.muU F ζ hζ U R P) := by
  letI : IsFiniteMeasureOnCompacts (KPContActualSectorCotangentL2.muU F ζ hζ U R P) :=
    (KPContSectorFixedMeasureLocalFiniteness.levelLocalFiniteness F ζ hζ R P H U).spherical_finite
  have hcs : HasCompactSupport (scalarPair f g) :=
    g.property.2.2.of_isClosed_subset (isClosed_tsupport _) (tsupport_scalarPair_subset f g)
  exact (scalar_pair_continuous f g).integrable_of_hasCompactSupport hcs

theorem cotangent_chart_integral (a : ActualChart (U := U) (H := H))
    (W Z : T_U F ζ hζ U R P H) :
    (∫ x in a.baseDomain, pair W.val Z.val x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) =
      ∫ y, inner ℂ (localCoefficient a W.val y) (localCoefficient a Z.val y)
        ∂a.liftedMeasure := by
  have hP := every_shrunkChart_properties F ζ hζ U R P H a
  let r : SquareFiniteFamily (U := U) (H := H) := ⟨W.val, cotangent_squareFinite W⟩
  let s : SquareFiniteFamily (U := U) (H := H) := ⟨Z.val, cotangent_squareFinite Z⟩
  have hrm : MemLp (localCoefficient a r.val) 2 a.liftedMeasure :=
    localCoefficient_memLp (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) a r
  have hsm : MemLp (localCoefficient a s.val) 2 a.liftedMeasure :=
    localCoefficient_memLp (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) a s
  have h1 : inner ℂ (familyQ a r) (familyQ a s) =
      ∫ y, inner ℂ
        ((familyQ a r : Lp (KPContCotangentActualGenuineTwistIsotropy.E F) 2 a.liftedMeasure) y)
        ((familyQ a s : Lp (KPContCotangentActualGenuineTwistIsotropy.E F) 2 a.liftedMeasure) y)
        ∂a.liftedMeasure :=
    KPMeasurableLocalL2.Q_inner_eq_integral (localData a) (fullPiece a) (familyQ a r) (familyQ a s)
  have h2 : (∫ y, inner ℂ
        ((familyQ a r : Lp (KPContCotangentActualGenuineTwistIsotropy.E F) 2 a.liftedMeasure) y)
        ((familyQ a s : Lp (KPContCotangentActualGenuineTwistIsotropy.E F) 2 a.liftedMeasure) y)
        ∂a.liftedMeasure) =
      ∫ x in a.baseDomain, pair r.val s.val x
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
    have hae : (fun y => inner ℂ
          ((familyQ a r : Lp (KPContCotangentActualGenuineTwistIsotropy.E F) 2 a.liftedMeasure) y)
          ((familyQ a s : Lp (KPContCotangentActualGenuineTwistIsotropy.E F) 2 a.liftedMeasure) y))
        =ᵐ[a.liftedMeasure] (fun y => pair r.val s.val (a.toBase y)) := by
      filter_upwards [MemLp.coeFn_toLp hrm, MemLp.coeFn_toLp hsm] with y hy1 hy2
      change inner ℂ (familyLp a r y) (familyLp a s y) = pair r.val s.val (a.toBase y)
      simp only [familyLp]
      rw [hy1, hy2, ← q_coordinates a y, pair_chart]
      rfl
    rw [integral_congr_ae hae,
      (integral_map (μ := a.liftedMeasure) (φ := a.toBase) hP.measurable.aemeasurable
        (measurable_pair r.val s.val).aestronglyMeasurable).symm,
      hP.exact_pushforward]
  have h3 : inner ℂ (familyQ a r) (familyQ a s) =
      ∫ y, inner ℂ (localCoefficient a r.val y) (localCoefficient a s.val y)
        ∂a.liftedMeasure := by
    rw [h1]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hrm, MemLp.coeFn_toLp hsm] with y hy1 hy2
    change inner ℂ (familyLp a r y) (familyLp a s y) =
      inner ℂ (localCoefficient a r.val y) (localCoefficient a s.val y)
    simp only [familyLp]
    rw [hy1, hy2]
  have hrv : r.val = W.val := rfl
  have hsv : s.val = Z.val := rfl
  simpa only [hrv, hsv] using h2.symm.trans h3

theorem scalar_base_memLp (f : S_U F ζ hζ U R P H) :
    MemLp (sectionNorm F ζ hζ U R P H (scalarSections f)) 2
      (KPContActualSectorCotangentL2.muU F ζ hζ U R P) := by
  have hmeas : ∀ i, Measurable ((scalarSections f) i).val := fun i =>
    ((Classical.choose_spec (scalar_gluing (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R)
      (P := P) (H := H) f)).1.1 i).continuous.measurable
  have hrep : KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H (scalarSections f) =
      scalarCovered f := by
    rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm, ← S_scalarCovered f]
    exact (S F ζ hζ U R P H).symm_apply_apply (scalarCovered f)
  have hfin : KPContSectorLineL2Isometry.normIntegral F ζ hζ U R P H (scalarSections f) < ⊤ :=
    (KPContSectorLineL2Isometry.finite_integral_iff F ζ hζ U R P H (scalarSections f) hmeas).mpr
      (by rw [hrep]; exact scalar_memLp f)
  let s : KPContSectorLineL2Isometry.BorelL2Sections F ζ hζ U R P H :=
    ⟨scalarSections f, hmeas, hfin⟩
  have hme : Measurable (sectionNorm F ζ hζ U R P H s.val) := by
    let f' := KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H s.val
    have hnorm := (kp_cont_sector_fixed_line_norm_integrals F ζ hζ U R P H f' ((KPContSectorLineL2Isometry.borel_iff F ζ hζ U R P H s.val).mp
        s.property.1)).borel
    have hh : sectionNorm F ζ hζ U R P H s.val =
        fun b => Real.sqrt
          (KPContSectorFixedLineNormIntegrals.lineNorm F ζ hζ U R P H f' b).toReal := by
      funext b
      change _ = Real.sqrt (ENNReal.ofReal
        (sectionNorm F ζ hζ U R P H (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H f')
          b ^ 2)).toReal
      rw [show KPContSectorScalarLineAlgebra.S F ζ hζ U R P H f' = s.val from
        (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H).apply_symm_apply s.val]
      rw [ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq_eq_abs]
      exact (abs_of_nonneg (by
        obtain ⟨⟨i,q⟩,rfl⟩ := (H.atlas U).components.surjective b
        obtain ⟨x,rfl⟩ := Quotient.exists_rep q
        rw [sectionNorm_component]; exact norm_nonneg _)).symm
    rw [hh]
    exact hnorm.ennreal_toReal.sqrt
  have hn : ∀ b, 0 ≤ sectionNorm F ζ hζ U R P H s.val b := by
    intro b
    obtain ⟨⟨i,q⟩,rfl⟩ := (H.atlas U).components.surjective b
    obtain ⟨x,rfl⟩ := Quotient.exists_rep q
    rw [sectionNorm_component]; exact norm_nonneg _
  rw [memLp_two_iff_integrable_sq_norm hme.aestronglyMeasurable]
  refine ⟨hme.norm.pow_const 2 |>.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [Real.norm_eq_abs, sq_abs, Real.enorm_eq_ofReal_abs, abs_pow, sq_abs,
    KPContSectorLineL2Isometry.normIntegral, KPContSectorLineL2Isometry.squaredNorm]
    using s.property.2

private theorem scalar_chart_norm_aux (a : ActualChart (U := U) (H := H))
    (s : Sections F ζ hζ U R P H) (y : a.domain) :
    sectionNorm F ζ hζ U R P H s (a.toBase y) = ‖(a.coefficient s y : ℂ)‖ := by
  change sectionNorm F ζ hζ U R P H s
    (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)
      (Quotient.mk _ y.val)) = ‖(s a.component).val y.val‖
  rw [← (H.atlas U).components_formula]
  exact sectionNorm_component F ζ hζ U R P H s a.component y.val

private theorem scalarCoefficient_memLp (a : ActualChart (U := U) (H := H))
    (s : KPContSectorLineL2Isometry.BorelL2Sections F ζ hζ U R P H) :
    MemLp (fun y : a.domain => (a.coefficient s.val y : ℂ)) 2 a.liftedMeasure := by
  have hmeas : Measurable (fun y : a.domain => (a.coefficient s.val y : ℂ)) :=
    (s.property.1 a.component).comp measurable_subtype_coe
  rw [memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable]
  refine ⟨(hmeas.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have he (y : a.domain) : ‖(‖(a.coefficient s.val y : ℂ)‖ ^ 2 : ℝ)‖ₑ =
      KPContSectorLineL2Isometry.squaredNorm F ζ hζ U R P H s.val (a.toBase y) := by
    rw [Real.enorm_eq_ofReal (sq_nonneg _), KPContSectorLineL2Isometry.squaredNorm,
      scalar_chart_norm_aux]
  simp only [he]
  have ha := every_shrunkChart_properties F ζ hζ U R P H a
  calc
    (∫⁻ y, KPContSectorLineL2Isometry.squaredNorm F ζ hζ U R P H s.val (a.toBase y)
        ∂a.liftedMeasure) =
        ∫⁻ b, KPContSectorLineL2Isometry.squaredNorm F ζ hζ U R P H s.val b
          ∂Measure.map a.toBase a.liftedMeasure :=
      (lintegral_map'
        (KPContSectorLineL2Isometry.squaredNorm_measurable F ζ hζ U R P H s.val
          s.property.1).aemeasurable ha.measurable.aemeasurable).symm
    _ = ∫⁻ b in a.baseDomain, KPContSectorLineL2Isometry.squaredNorm F ζ hζ U R P H s.val b
        ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U := by
      rw [ha.exact_pushforward]
    _ ≤ KPContSectorLineL2Isometry.normIntegral F ζ hζ U R P H s.val :=
      setLIntegral_le_lintegral _ _
    _ < ⊤ := s.property.2

private theorem scalar_field_coefficient_aux (a : ActualChart (U := U) (H := H))
    (s : Sections F ζ hζ U R P H) (y : a.domain) :
    sectionFields s a (coordinates a y) = (a.coefficient s y : ℂ) := by
  have hi : ∀ v : KPCuspGenuineMonodromy.SymmetricSpace F,
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) v) = v := by
    intro v; funext k; simp [labeledA, labeledAInv]
  simp only [sectionFields, KPContCotangentActualOverlap.LiftedChart.coefficient,
    KPContCotangentActualGenuineTwistIsotropy.isotropyChart, coordinates]
  simp [hi, ChartKind.representative, ShrunkChart.coefficient, liftCoefficient]

theorem scalar_local_memLp (a : ActualChart (U := U) (H := H)) (f : S_U F ζ hζ U R P H) :
    MemLp (localScalarCoefficient a f) 2 a.liftedMeasure := by
  have hglue := (Classical.choose_spec (scalar_gluing (F := F) (ζ := ζ) (hζ := hζ) (U := U)
    (R := R) (P := P) (H := H) f)).1
  have hfval : sectionFields (scalarSections f) = f.val := hglue.2.2
  have hmeas : ∀ i, Measurable ((scalarSections f) i).val := fun i => (hglue.1 i).continuous.measurable
  have hrep : KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H (scalarSections f) =
      scalarCovered f := by
    rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm, ← S_scalarCovered f]
    exact (S F ζ hζ U R P H).symm_apply_apply (scalarCovered f)
  have hfin : KPContSectorLineL2Isometry.normIntegral F ζ hζ U R P H (scalarSections f) < ⊤ :=
    (KPContSectorLineL2Isometry.finite_integral_iff F ζ hζ U R P H (scalarSections f) hmeas).mpr
      (by rw [hrep]; exact scalar_memLp f)
  let s : KPContSectorLineL2Isometry.BorelL2Sections F ζ hζ U R P H :=
    ⟨scalarSections f, hmeas, hfin⟩
  have hcoe : localScalarCoefficient a f =
      fun y : a.domain => (a.coefficient (scalarSections f) y : ℂ) := by
    funext y
    rw [localScalarCoefficient, ← congrFun (congrFun hfval a) (coordinates a y),
      scalar_field_coefficient_aux]
  rw [hcoe]
  exact scalarCoefficient_memLp a s

private theorem continuous_normSquare_of_continuous (v : Family (U := U) (H := H))
    (hv : ∀ a, Continuous (coefficient v a)) : Continuous (normSquare v) := by
  let cover := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
  refine continuous_of_cover_nhds (s := fun n => (cover.chart n).baseDomain) ?_ ?_
  · intro x
    have hx : x ∈ ⋃ n, (cover.chart n).baseDomain := by
      rw [cover.covers]; exact Set.mem_univ x
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact ⟨n, (cover.properties n).base_open.mem_nhds hn⟩
  · intro n
    set a := cover.chart n
    have hP := every_shrunkChart_properties F ζ hζ U R P H a
    have hloc : Continuous (fun y : a.domain => ‖localCoefficient a v y‖₊ ^ 2) :=
      (((hv a).comp (coordinates_continuous a)).nnnorm).pow 2
    have hquot : (fun z : a.baseDomain => normSquare v z.val) ∘ a.quotientMap =
        fun y : a.domain => ‖localCoefficient a v y‖₊ ^ 2 := by
      funext y
      show normSquare v (a.toBase y) = ‖localCoefficient a v y‖₊ ^ 2
      rw [← q_coordinates a y, normSquare_chart]
      rfl
    have hF' : Continuous (fun z : a.baseDomain => normSquare v z.val) :=
      (continuous_iff_isQuotientMap hP.quotient _).mpr (hquot ▸ hloc)
    rw [continuousOn_iff_continuous_domRestrict]
    exact hF'

private theorem normSquare_self_sub (v : Family (U := U) (H := H)) :
    normSquare (v - v) = 0 := by
  refine ((Classical.choose_spec (normSquare_descends (v - v))).2
    (fun _ => (0 : NNReal))
    ⟨measurable_const, fun a x => ?_⟩).symm
  have h0 : coefficient (v - v) a x = 0 := by simp [coefficient]
  rw [h0]; simp

theorem j_injective :
    Function.Injective (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)) := by
  letI : (KPContActualSectorCotangentL2.muU F ζ hζ U R P).IsOpenPosMeasure :=
    (levelSupport F ζ hζ R P
      (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1 U).spherical_open_positive
  intro W Z hWZ
  have hae : AeEquivalent W.val Z.val :=
    (KPContActualSectorCotangentL2.ofFamily_eq_iff F ζ hζ U R P H
      (cotangentSquareFamily W) (cotangentSquareFamily Z)).mp hWZ
  have hcoe : ∀ a, coefficient (W.val - Z.val) a = coefficient W.val a - coefficient Z.val a := by
    intro a; funext x
    simp only [coefficient, Submodule.coe_sub, Pi.sub_apply]
  have hsm : ∀ a, SmoothOnLift a (coefficient (W.val - Z.val) a) := by
    intro a
    rw [hcoe a]
    obtain ⟨gW, hgW, hgWv⟩ := W.property.1 a
    obtain ⟨gZ, hgZ, hgZv⟩ := Z.property.1 a
    exact ⟨gW - gZ, hgW.sub hgZ, fun x => by
      simp only [Pi.sub_apply, hgWv x, hgZv x]⟩
  have hcont : Continuous (normSquare (W.val - Z.val)) :=
    continuous_normSquare_of_smooth (W.val - Z.val) hsm
  have hzero : normSquare (W.val - Z.val) = 0 :=
    Measure.eq_of_ae_eq hae hcont continuous_const
  apply Subtype.ext; apply Subtype.ext
  funext a x
  have h := congrFun hzero (KPContCotangentOverlapRationalBranches.q a x.val)
  rw [KPContActualCotangentMeasurableFamilies.normSquare_chart (W.val - Z.val) a x,
    hcoe a] at h
  have h1 : ‖coefficient W.val a x - coefficient Z.val a x‖₊ = 0 :=
    (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h
  exact sub_eq_zero.mp (nnnorm_eq_zero.mp h1)

theorem cotangent_unique_continuous (W : T_U F ζ hζ U R P H) :
    ∃! v : Family (U := U) (H := H),
      (∀ a : ActualChart (U := U) (H := H), Continuous (coefficient v a)) ∧
        AeEquivalent v W.val := by
  letI : (KPContActualSectorCotangentL2.muU F ζ hζ U R P).IsOpenPosMeasure :=
    (levelSupport F ζ hζ R P
      (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1 U).spherical_open_positive
  refine ⟨W.val, ⟨fun a => cotangent_continuous W a, ?_⟩, ?_⟩
  · rw [AeEquivalent]
    filter_upwards with x
    rw [normSquare_self_sub W.val]
    rfl
  · intro v hv
    have hcoe : ∀ a, coefficient (v - W.val) a = coefficient v a - coefficient W.val a := by
      intro a; funext x
      simp only [coefficient, Submodule.coe_sub, Pi.sub_apply]
    have hcont : Continuous (normSquare (v - W.val)) :=
      continuous_normSquare_of_continuous (v - W.val) (fun a => by
        rw [hcoe a]
        exact (hv.1 a).sub (cotangent_continuous W a))
    have hzero : normSquare (v - W.val) = 0 :=
      Measure.eq_of_ae_eq hv.2 hcont continuous_const
    apply Subtype.ext
    funext a x
    have h := congrFun hzero (KPContCotangentOverlapRationalBranches.q a x.val)
    rw [KPContActualCotangentMeasurableFamilies.normSquare_chart (v - W.val) a x,
      hcoe a] at h
    have h1 : ‖coefficient v a x - coefficient W.val a x‖₊ = 0 :=
      (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h
    exact sub_eq_zero.mp (nnnorm_eq_zero.mp h1)

private theorem scalarPair_eq_sections (f g : S_U F ζ hζ U R P H) :
    scalarPair f g = scalarPairSections (scalarSections f) (scalarSections g) := by
  have hfs := Classical.choose_spec (scalar_gluing (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) f)
  have hgs := Classical.choose_spec (scalar_gluing (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) g)
  have hfsmooth : IsSmoothSections F ζ hζ U R P H (scalarSections f) := hfs.1.1
  have hgsmooth : IsSmoothSections F ζ hζ U R P H (scalarSections g) := hgs.1.1
  have hfval : sectionFields (scalarSections f) = f.val := hfs.1.2.2
  have hgval : sectionFields (scalarSections g) = g.val := hgs.1.2.2
  have hcont : Continuous (scalarPairSections (scalarSections f) (scalarSections g)) := by
    let cover := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
    refine continuous_of_cover_nhds (s := fun n => (cover.chart n).baseDomain) ?_ ?_
    · intro x
      have hx : x ∈ ⋃ n, (cover.chart n).baseDomain := by
        rw [cover.covers]; exact Set.mem_univ x
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact ⟨n, (cover.properties n).base_open.mem_nhds hn⟩
    · intro n
      set a := cover.chart n
      have hP := every_shrunkChart_properties F ζ hζ U R P H a
      rw [continuousOn_iff_continuous_domRestrict]
      refine (continuous_iff_isQuotientMap hP.quotient
        (fun z : a.baseDomain =>
          scalarPairSections (scalarSections f) (scalarSections g) z.val)).mpr ?_
      change Continuous (fun y : a.domain =>
        scalarPairSections (scalarSections f) (scalarSections g) (a.toBase y))
      have hbase : (fun y : a.domain =>
            scalarPairSections (scalarSections f) (scalarSections g) (a.toBase y)) =
          fun y : a.domain => inner ℂ ((scalarSections f a.component).val y.val)
            ((scalarSections g a.component).val y.val) := by
        funext y
        have h1 : a.toBase y = (H.atlas U).components
            ⟨a.component, Quotient.mk _ y.val⟩ := by
          simp only [ShrunkChart.toBase, KPCuspSiegel.projection,
            (H.atlas U).components_formula]
        rw [h1, scalarPairSections_components]
      rw [hbase]
      exact continuous_inner.comp
        (((hfsmooth a.component).continuous.comp continuous_subtype_val).prodMk
          ((hgsmooth a.component).continuous.comp continuous_subtype_val))
  have hchart : ∀ (a : ActualChart (U := U) (H := H)) (x : omega a),
      scalarPairSections (scalarSections f) (scalarSections g) (q a x.val) =
        inner ℂ (f.val a x) (g.val a x) := by
    intro a x
    rw [scalarPairSections_chart, hfval, hgval]
  exact ((Classical.choose_spec (scalarPair_descends f g)).2
    (scalarPairSections (scalarSections f) (scalarSections g)) ⟨hcont, hchart⟩).symm

private theorem scalarCovered_inner_eq (f g : S_U F ζ hζ U R P H) :
    (fun v : CoveredSpherical F ζ hζ U =>
        inner ℂ ((scalarCovered f).val v) ((scalarCovered g).val v)) =
      fun v => scalarPair f g (q F ζ hζ U v) := by
  have hSf : S F ζ hζ U R P H (scalarCovered f) = scalarSections f := S_scalarCovered f
  have hSg : S F ζ hζ U R P H (scalarCovered g) = scalarSections g := S_scalarCovered g
  have hpair : scalarPair f g = scalarPairSections (scalarSections f) (scalarSections g) :=
    scalarPair_eq_sections f g
  funext v
  obtain ⟨p, hp⟩ :=
    (KPContSectorPhaseComponentCharts.componentHomeomorph F ζ hζ U R P H).surjective v
  obtain ⟨i, w⟩ := p
  obtain ⟨⟨m, y⟩, rfl⟩ := Quotient.exists_rep w
  rw [← hp]
  obtain ⟨ε, hε⟩ := Quotient.exists_rep m
  rw [← hε]
  rw [KPContSectorSmoothFramesSupport.phase_component_restriction F ζ hζ U R P H
        (scalarCovered f) i (Quotient.mk _ ε) y,
    KPContSectorSmoothFramesSupport.phase_component_restriction F ζ hζ U R P H
        (scalarCovered g) i (Quotient.mk _ ε) y,
    hSf, hSg]
  have hm : KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U ε =
      (Quotient.mk _ ε : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U) := rfl
  conv_lhs => rw [← hm]
  have hfp : KPContSectorPhaseComponentCharts.forgetPhase F ζ hζ U R P H i
      (Quotient.mk _ (Quotient.mk _ ε, y)) = Quotient.mk _ y := rfl
  rw [KPContSectorSmoothFramesSupport.phaseCoefficient_class F ζ hζ U R P H (scalarSections f) i ε y,
    KPContSectorSmoothFramesSupport.phaseCoefficient_class F ζ hζ U R P H (scalarSections g) i ε y,
    inner_mul_mul_of_norm_one _ _ _ (chi_unit' (H := H) i ε),
    hpair,
    KPContSectorPhaseComponentCharts.componentHomeomorph_forget F ζ hζ U R P H i
      (Quotient.mk _ (Quotient.mk _ ε, y)),
    hfp,
    scalarPairSections_components (scalarSections f) (scalarSections g) i y]

theorem scalar_inner
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (f g : S_U F ζ hζ U R P H) :
    inner ℂ (iota f) (iota g) =
      ∫ x, scalarPair f g x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
  have hsub : inner ℂ (iota f) (iota g) =
      inner ℂ ((iota f : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U))
        ((iota g : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U)) := rfl
  rw [hsub, scalar_represented f, scalar_represented g, L2.inner_def]
  have hpt : (fun v => inner ℂ
        (((scalar_memLp f).toLp (scalarCovered f).val :
          Lp ℂ 2 (coveredMeasure F ζ hζ R U)) v)
        (((scalar_memLp g).toLp (scalarCovered g).val :
          Lp ℂ 2 (coveredMeasure F ζ hζ R U)) v)) =ᵐ[coveredMeasure F ζ hζ R U]
      (fun v => inner ℂ ((scalarCovered f).val v) ((scalarCovered g).val v)) := by
    filter_upwards [MemLp.coeFn_toLp (scalar_memLp f), MemLp.coeFn_toLp (scalar_memLp g)]
      with v hv hw
    rw [hv, hw]
  rw [integral_congr_ae hpt, scalarCovered_inner_eq,
    ← integral_map (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable.aemeasurable
      (scalar_pair_continuous f g).aestronglyMeasurable,
    realization.support.pushforward]

end DedekindZetaZeroFree.KPContActualSectorTestEmbeddings

namespace DedekindZetaZeroFree

theorem kp_cont_actual_sector_test_embeddings
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualSectorTestEmbeddings.Properties (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) :=
  { scalar_base_memLp := KPContActualSectorTestEmbeddings.scalar_base_memLp
    cotangent_base_memLp := KPContActualSectorTestEmbeddings.cotangent_base_memLp
    scalar_local_memLp := KPContActualSectorTestEmbeddings.scalar_local_memLp
    cotangent_local_memLp := KPContActualSectorTestEmbeddings.cotangent_local_memLp
    iota_injective := KPContActualSectorTestEmbeddings.iota_injective
    j_injective := KPContActualSectorTestEmbeddings.j_injective
    scalar_continuous := KPContActualSectorTestEmbeddings.scalarCovered_continuous
    scalar_represented := KPContActualSectorTestEmbeddings.scalar_represented
    scalar_unique_continuous := KPContActualSectorTestEmbeddings.scalar_unique_continuous
    cotangent_continuous := KPContActualSectorTestEmbeddings.cotangent_continuous
    cotangent_represented := KPContActualSectorTestEmbeddings.cotangent_represented
    cotangent_unique_continuous := KPContActualSectorTestEmbeddings.cotangent_unique_continuous
    scalar_pair_chart := KPContActualSectorTestEmbeddings.scalar_pair_chart
    scalar_pair_integrable := KPContActualSectorTestEmbeddings.scalar_pair_integrable
    cotangent_pair_integrable := KPContActualSectorTestEmbeddings.cotangent_pair_integrable
    scalar_inner := KPContActualSectorTestEmbeddings.scalar_inner realization
    cotangent_inner := KPContActualSectorTestEmbeddings.cotangent_inner realization
    scalar_chart_integral := KPContActualSectorTestEmbeddings.scalar_chart_integral
    cotangent_chart_integral := KPContActualSectorTestEmbeddings.cotangent_chart_integral }

end DedekindZetaZeroFree

end
