module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.GluedSquareIntegrals
public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.AlmostEverywherePieceTransport
public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.HilbertPieceExtraction

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentGluingInverseIdentities

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualCotangentCountableShrinking KPContActualCotangentBorelRefinement
open KPContActualCotangentExactMeasurableGluing
open KPContActualCotangentPieceExtraction KPContActualCotangentPieceHilbertSum
open KPContActualCotangentGluedPieceIntegral KPContActualCotangentMeasurableFamilies
open KPContCotangentActualGenuineTwistIsotropy KPContCotangentOverlapRationalBranches
open KPContActualCotangentPieceAeTransport
open KPContActualCotangentTransportChoiceAlgebra KPContCotangentActualOverlap

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

def indicatorFields (cover : CountableCover F ζ hζ U R P H)
    (v : Family (U := U) (H := H)) : SequenceFields cover := fun n =>
  {y : omega (cover.chart n) | q (cover.chart n) y.val ∈ basePiece cover n}.indicator
    (coefficient v (cover.chart n))

private lemma q_coordinates (C : ShrunkChart F ζ hζ U R P H) (y : C.domain) :
    q C (coordinates C y).val = C.toBase y := by
  rw [KPContCotangentOverlapRationalBranches.q, ShrunkChart.toBase,
    KPContActualCotangentPieceHilbertSum.coordinates]
  congr 1
  have h : KPContCotangentActualOverlap.labeledA (KPContCotangentActualOverlap.placeEquiv F ζ hζ)
      (KPContCotangentActualOverlap.labeledAInv (KPContCotangentActualOverlap.placeEquiv F ζ hζ) y.val)
      = y.val := by
    funext k
    simp [KPContCotangentActualOverlap.labeledA, KPContCotangentActualOverlap.labeledAInv]
  rw [h]

private lemma coordinates_mem_coordinatePiece_iff (cover : CountableCover F ζ hζ U R P H)
    (n : ℕ) (y : (cover.chart n).domain) :
    coordinates (cover.chart n) y ∈ coordinatePiece cover n ↔ y ∈ liftedPiece cover n := by
  rw [coordinatePiece, Set.mem_preimage, liftedPiece, Set.mem_preimage, q_coordinates]

private lemma indicatorFields_apply_of_mem (cover : CountableCover F ζ hζ U R P H)
    (v : Family (U := U) (H := H)) (n : ℕ) (y : omega (cover.chart n))
    (hy : q (cover.chart n) y.val ∈ basePiece cover n) :
    indicatorFields cover v n y = coefficient v (cover.chart n) y := by
  show ({y : omega (cover.chart n) | q (cover.chart n) y.val ∈ basePiece cover n}).indicator
      (coefficient v (cover.chart n)) y = coefficient v (cover.chart n) y
  exact Set.indicator_of_mem (show y ∈ _ from hy) _

private lemma e_eq_indicatorFields (cover : CountableCover F ζ hζ U R P H)
    (v : Family (U := U) (H := H)) (n : ℕ) (y : (cover.chart n).domain) :
    e cover v n y = indicatorFields cover v n (coordinates (cover.chart n) y) := by
  by_cases h : y ∈ liftedPiece cover n
  · have hy : q (cover.chart n) (coordinates (cover.chart n) y).val ∈ basePiece cover n :=
      (coordinates_mem_coordinatePiece_iff cover n y).mpr h
    rw [show e cover v n y = coefficient v (cover.chart n) (coordinates (cover.chart n) y) from by
          unfold e localCoefficient
          exact Set.indicator_of_mem h _,
      indicatorFields_apply_of_mem cover v n _ hy]
  · have hy : coordinates (cover.chart n) y ∉ coordinatePiece cover n :=
      fun hc => h ((coordinates_mem_coordinatePiece_iff cover n y).mp hc)
    rw [show e cover v n y = 0 from by unfold e; exact Set.indicator_of_notMem h _,
      show indicatorFields cover v n (coordinates (cover.chart n) y) = 0 from by
        unfold indicatorFields
        exact Set.indicator_of_notMem hy _]

private lemma continuous_labeledA_placeEquiv :
    Continuous (labeledA (placeEquiv F ζ hζ)) := by
  apply continuous_pi
  intro k
  exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous

private lemma measurable_q (a : ShrunkChart F ζ hζ U R P H) : Measurable (q a) := by
  have hcm : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U
      ((H.atlas U).representative a.component)) := by
    have he : KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component) =
        (H.atlas U).components ∘ Sigma.mk a.component := by
      funext x; exact ((H.atlas U).components_formula a.component x).symm
    rw [he]
    exact ((H.atlas U).components.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk).continuous
  have hproj : Measurable (KPCuspSiegel.projection F
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)) :=
    measurable_quotient_mk''
  have hcomp : q a = KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)
      ∘ KPCuspSiegel.projection F (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)
      ∘ labeledA (placeEquiv F ζ hζ) := rfl
  rw [hcomp]
  exact hcm.measurable.comp (hproj.comp continuous_labeledA_placeEquiv.measurable)

private lemma labeledAInv_labeledA
    (p : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F)) (x : M F) :
    labeledAInv p (labeledA p x) = x := by
  simp [labeledA, labeledAInv]

private lemma labeledA_labeledAInv
    (p : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F))
    (z : KPCuspGenuineMonodromy.SymmetricSpace F) : labeledA p (labeledAInv p z) = z := by
  funext k
  simp [labeledA, labeledAInv]

 def pt (a : ShrunkChart F ζ hζ U R P H) (x : omega a) : a.domain :=
  ⟨labeledA (placeEquiv F ζ hζ) x.val, x.property⟩

private lemma coordinates_pt (a : ShrunkChart F ζ hζ U R P H) (x : omega a) :
    coordinates a (pt a x) = x := by
  apply Subtype.ext
  exact labeledAInv_labeledA (placeEquiv F ζ hζ) x.val

private lemma pt_coordinates (a : ShrunkChart F ζ hζ U R P H) (y : a.domain) :
    pt a (coordinates a y) = y := by
  apply Subtype.ext
  exact labeledA_labeledAInv (placeEquiv F ζ hζ) y.val

private lemma coordinates_injective (a : ShrunkChart F ζ hζ U R P H) :
    Function.Injective (coordinates a) := by
  intro y₁ y₂ h
  rw [← pt_coordinates a y₁, ← pt_coordinates a y₂, h]

private lemma T_proof_irrel {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (ψ : Arrow a b) (x : M F) (h h' : x ∈ ψ.domain) : T ψ x h = T ψ x h' := rfl

private lemma T_congr {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (ψ : Arrow a b) {x x' : M F} (h : x = x') (hx : x ∈ ψ.domain) (hx' : x' ∈ ψ.domain) :
    T ψ x hx = T ψ x' hx' := by
  cases h; rfl

private lemma e_pt (cover : CountableCover F ζ hζ U R P H)
    (v : Family (U := U) (H := H)) (n : ℕ) (x : omega (cover.chart n)) :
    e cover v n (pt (cover.chart n) x) = indicatorFields cover v n x := by
  rw [e_eq_indicatorFields cover v n (pt (cover.chart n) x), coordinates_pt]

private lemma ambientSequence_apply (cover : CountableCover F ζ hζ U R P H)
    (f : SequenceFields cover) (n : ℕ) (x : M F) (hx : x ∈ omega (cover.chart n)) :
    ambientSequence cover f n x = f n ⟨x, hx⟩ := by
  rw [ambientSequence, dif_pos hx]

private lemma indicatorFields_equivariant (cover : CountableCover F ζ hζ U R P H)
    (v : Family (U := U) (H := H)) (n : ℕ) (γ : Gamma (cover.chart n))
    (y : M F) (hy : y ∈ omega (cover.chart n)) :
    indicatorFields cover v n
        ⟨(isotropyArrow (cover.chart n) γ).psi y, isotropy_mem (cover.chart n) γ y hy⟩ =
      T (isotropyArrow (cover.chart n) γ) y
        (KPContActualCotangentTransportChoiceAlgebra.omega_subset_larger (cover.chart n) hy)
        (indicatorFields cover v n ⟨y, hy⟩) := by
  have hc : (coordinates (cover.chart n) (pt (cover.chart n) ⟨y, hy⟩)).val = y :=
    congrArg Subtype.val (coordinates_pt (cover.chart n) ⟨y, hy⟩)
  have hpt : actualActionEquiv (cover.chart n) γ (pt (cover.chart n) ⟨y, hy⟩) =
      pt (cover.chart n) ⟨(isotropyArrow (cover.chart n) γ).psi y,
        isotropy_mem (cover.chart n) γ y hy⟩ := by
    apply coordinates_injective (cover.chart n)
    apply Subtype.ext
    rw [coordinates_action (cover.chart n) γ (pt (cover.chart n) ⟨y, hy⟩)]
    rw [congrArg Subtype.val (coordinates_pt (cover.chart n) ⟨y, hy⟩)]
    rw [congrArg Subtype.val (coordinates_pt (cover.chart n)
      ⟨(isotropyArrow (cover.chart n) γ).psi y, isotropy_mem (cover.chart n) γ y hy⟩)]
  have hT : actualTensor (cover.chart n) γ (pt (cover.chart n) ⟨y, hy⟩) =
      T (isotropyArrow (cover.chart n) γ) y
        (KPContActualCotangentTransportChoiceAlgebra.omega_subset_larger (cover.chart n) hy) := by
    unfold actualTensor
    exact T_congr (isotropyArrow (cover.chart n) γ) hc _ _
  have hE := e_equivariant cover v n γ (pt (cover.chart n) ⟨y, hy⟩)
  rw [hpt] at hE
  rw [e_pt cover v n ⟨(isotropyArrow (cover.chart n) γ).psi y,
        isotropy_mem (cover.chart n) γ y hy⟩, e_pt cover v n ⟨y, hy⟩, hT] at hE
  exact hE

theorem indicatorFields_isPieceSequence (cover : CountableCover F ζ hζ U R P H)
    (v : Family (U := U) (H := H)) : IsPieceSequence cover (indicatorFields cover v) := by
  have hbase := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hset : MeasurableSet (Subtype.val ⁻¹'
        (q (cover.chart n) ⁻¹' basePiece cover n) : Set (omega (cover.chart n))) :=
      measurable_subtype_coe ((hbase.base_measurable n).preimage (measurable_q (cover.chart n)))
    exact (v.property.1 (cover.chart n)).indicator hset
  · intro n y hy
    exact Set.indicator_of_notMem
      (show y ∉ {y : omega (cover.chart n) | q (cover.chart n) y.val ∈ basePiece cover n}
        from hy) _
  · intro n γ y hy
    have hψy := isotropy_mem (cover.chart n) γ y hy
    rw [ambientSequence_apply cover _ n _ hψy, ambientSequence_apply cover _ n _ hy]
    exact indicatorFields_equivariant cover v n γ y hy

def indicatorSequence (cover : CountableCover F ζ hζ U R P H)
    (v : Family (U := U) (H := H)) : PieceSequence cover :=
  ⟨indicatorFields cover v, indicatorFields_isPieceSequence cover v⟩

private theorem indicatorSequence_represents_aux (cover : CountableCover F ζ hζ U R P H)
    (v : SquareFiniteFamily (U := U) (H := H)) :
    RepresentsComponents cover (indicatorSequence cover v.val)
      (Ext cover (toAeQuotient v)) := by
  intro n
  have h1 : pieceCoefficient cover (indicatorSequence cover v.val) n = e cover v.val n := by
    funext y
    show (indicatorSequence cover v.val).val n (coordinates (cover.chart n) y) = _
    rw [show (indicatorSequence cover v.val).val n = indicatorFields cover v.val n from rfl,
      ← e_eq_indicatorFields cover v.val n y]
  rw [h1, Ext_component cover v n]
  exact (MemLp.coeFn_toLp (memLp_e cover v.val v.property n)).symm

theorem indicatorSequence_represents (cover : CountableCover F ζ hζ U R P H)
    (v : SquareFiniteFamily (U := U) (H := H)) :
    RepresentsComponents cover (indicatorSequence cover v.val)
      (Ext cover (toAeQuotient v)) :=
  indicatorSequence_represents_aux cover v

private lemma inverseTransport_some {a b : ShrunkChart F ζ hζ U R P H}
    (e : ActualBranch a b) (g : M F → E F) (x : M F) (hx : x ∈ e.arrow.domain) :
    inverseTransport (some e) g x hx = (T e.arrow x hx).symm (g (e.arrow.psi x)) := rfl

private lemma inverseTransport_indicator_eq (cover : CountableCover F ζ hζ U R P H)
    (v : SquareFiniteFamily (U := U) (H := H)) (a : ShrunkChart F ζ hζ U R P H)
    (n : ℕ) (br : Branch a (cover.chart n)) (hbr : br.Properties)
    (x : M F) (hxcell : q a x ∈ basePiece cover n) (hx : x ∈ br.domain) :
    inverseTransport br (ambientSequence cover (indicatorFields cover v.val) n) x hx
      = coefficient v.val a ⟨x, hbr.source_subset hx⟩ := by
  cases br with
  | none => exact (Set.notMem_empty x hx).elim
  | some e =>
    have hx' : x ∈ e.arrow.domain := hx
    rw [inverseTransport_some e _ x hx']
    have hq : q (cover.chart n) (e.arrow.psi x) = q a x := hbr.quotient_compatibility x hx'
    have hmemB : q (cover.chart n) (e.arrow.psi x) ∈ basePiece cover n := by
      rw [hq]; exact hxcell
    have hψ : e.arrow.psi x ∈ omega (cover.chart n) := e.target_shrinking hx'
    have hamb : ambientSequence cover (indicatorFields cover v.val) n (e.arrow.psi x)
        = coefficient v.val (cover.chart n) ⟨e.arrow.psi x, hψ⟩ := by
      unfold ambientSequence
      rw [dif_pos hψ]
      exact indicatorFields_apply_of_mem cover v.val n ⟨e.arrow.psi x, hψ⟩ hmemB
    rw [hamb]
    have hcov := v.val.property.2.2 a (cover.chart n) e x hx'
    have hsub : (⟨x, hbr.source_subset hx⟩ : omega a) = ⟨x, e.source_shrinking hx'⟩ :=
      Subtype.ext rfl
    simp only [coefficient] at hcov ⊢
    rw [hsub, hcov, LinearIsometryEquiv.symm_apply_apply]

lemma indicator_gluing_pointwise_aux (cover : CountableCover F ζ hζ U R P H)
    (v : SquareFiniteFamily (U := U) (H := H))
    (a : ShrunkChart F ζ hζ U R P H) (x : omega a) :
    coefficient (G cover (indicatorSequence cover v.val)) a x = coefficient v.val a x := by
  have hmem : x.val ∈ cell cover a (cellIndex cover a x).1 (cellIndex cover a x).2 :=
    cellIndex_mem cover a x
  have key := inverseTransport_indicator_eq cover v a (cellIndex cover a x).1
    ((enumeration cover a (cellIndex cover a x).1).branch (cellIndex cover a x).2)
    ((enumeration cover a (cellIndex cover a x).1).properties (cellIndex cover a x).2)
    x.val hmem.1
    (cell_subset_domain cover a (cellIndex cover a x).1 (cellIndex cover a x).2 hmem)
  change inverseTransport ((enumeration cover a (cellIndex cover a x).1).branch (cellIndex cover a x).2)
      (ambientSequence cover (indicatorFields cover v.val) (cellIndex cover a x).1) x.val
      (cell_subset_domain cover a (cellIndex cover a x).1 (cellIndex cover a x).2 hmem)
    = coefficient v.val a x
  rw [key]

variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
variable (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)

def gluedFamily (cover : CountableCover F ζ hζ U R P H)
    (u : PieceHilbert cover) (f : PieceSequence cover)
    (hf : RepresentsComponents cover f u) : SquareFiniteFamily (U := U) (H := H) :=
  ⟨G cover f,
    (kp_cont_actual_cotangent_glued_piece_integral F ζ hζ μG hμG U R hR P H cover).gluing_squareFinite f u hf⟩

lemma indicator_gluing_family_aux (cover : CountableCover F ζ hζ U R P H)
    (v : SquareFiniteFamily (U := U) (H := H)) :
    G cover (indicatorSequence cover v.val) = v.val :=
  Subtype.ext (funext fun a => funext fun x => indicator_gluing_pointwise_aux cover v a x)

lemma indicator_gluing_quotient_aux (cover : CountableCover F ζ hζ U R P H)
    (v : SquareFiniteFamily (U := U) (H := H)) :
    toAeQuotient (gluedFamily μG hμG hR cover (Ext cover (toAeQuotient v))
      (indicatorSequence cover v.val) (indicatorSequence_represents cover v))
      = toAeQuotient v := by
  rw [show gluedFamily μG hμG hR cover (Ext cover (toAeQuotient v))
      (indicatorSequence cover v.val) (indicatorSequence_represents cover v) = v from
    Subtype.ext (indicator_gluing_family_aux cover v)]

private lemma e_G_eq_pieceCoefficient
    (μ : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμ : μ.IsHaarMeasure)
    (h : R.adelicHaar = μ)
    (cover : CountableCover F ζ hζ U R P H)
    (f : PieceSequence cover) (n : ℕ) :
    e cover (G cover f) n = pieceCoefficient cover f n := by
  funext y
  by_cases hy : y ∈ liftedPiece cover n
  · have hB : q (cover.chart n) (coordinates (cover.chart n) y).val ∈ basePiece cover n :=
      (coordinates_mem_coordinatePiece_iff cover n y).mpr hy
    rw [show e cover (G cover f) n y
        = coefficient (G cover f) (cover.chart n) (coordinates (cover.chart n) y) from by
      unfold e localCoefficient
      exact Set.indicator_of_mem hy _,
      (kp_cont_actual_cotangent_exact_measurable_gluing F ζ hζ μ hμ U R h P H cover).on_piece
        f n (coordinates (cover.chart n) y) hB]
    rfl
  · rw [show e cover (G cover f) n y = 0 from by
      unfold e
      exact Set.indicator_of_notMem hy _]
    have hB : q (cover.chart n) (coordinates (cover.chart n) y).val ∉ basePiece cover n :=
      fun hc => hy ((coordinates_mem_coordinatePiece_iff cover n y).mp hc)
    simp only [pieceCoefficient]
    exact (f.property.2.1 n (coordinates (cover.chart n) y) hB).symm

private lemma measurable_omega (a : ShrunkChart F ζ hζ U R P H) : MeasurableSet (omega a) :=
  a.domain_open.measurableSet.preimage continuous_labeledA_placeEquiv.measurable

private lemma measurable_coordinatePiece (cover : CountableCover F ζ hζ U R P H) (n : ℕ) :
    MeasurableSet (coordinatePiece cover n) :=
  ((kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover).base_measurable n).preimage
    ((measurable_q (cover.chart n)).comp measurable_subtype_coe)

private lemma continuous_pt (a : ShrunkChart F ζ hζ U R P H) : Continuous (pt a) :=
  Continuous.subtype_mk (continuous_labeledA_placeEquiv.comp continuous_subtype_val)
    fun x => x.property

private lemma measurableEmbedding_coordinates (a : ShrunkChart F ζ hζ U R P H) :
    MeasurableEmbedding (coordinates a) := by
  refine MeasurableEmbedding.of_measurable_inverse (coordinates_continuous a).measurable ?_
    (continuous_pt a).measurable (pt_coordinates a)
  rw [Set.eq_univ_of_forall (s := Set.range (coordinates a))
    (fun x => ⟨pt a x, coordinates_pt a x⟩)]
  exact MeasurableSet.univ

private lemma chartMeasure_eq_map (a : ShrunkChart F ζ hζ U R P H) :
    chartMeasure a = Measure.map (coordinates a) a.liftedMeasure := by
  have hf : MeasurableEmbedding (Subtype.val : omega a → M F) :=
    MeasurableEmbedding.subtype_coe (measurable_omega a)
  have hν : KPContCotangentOverlapNullEquivalence.liftedMeasure a
      = Measure.map (Subtype.val : omega a → M F)
          (Measure.map (coordinates a) a.liftedMeasure) := by
    rw [KPContCotangentOverlapNullEquivalence.liftedMeasure,
      Measure.map_map hf.measurable (coordinates_continuous a).measurable]
    rfl
  have hae : ∀ᵐ x ∂(Measure.map (Subtype.val : omega a → M F)
      (Measure.map (coordinates a) a.liftedMeasure)), x ∈ omega a := by
    rw [ae_iff, hf.map_apply]
    simp
  rw [chartMeasure, hν, Measure.restrict_eq_self_of_ae_mem hae,
    hf.comap_map (Measure.map (coordinates a) a.liftedMeasure)]

private lemma chartMeasure_restrict (cover : CountableCover F ζ hζ U R P H) (n : ℕ) :
    (chartMeasure (cover.chart n)).restrict (coordinatePiece cover n)
      = Measure.map (coordinates (cover.chart n))
          ((cover.chart n).liftedMeasure.restrict (liftedPiece cover n)) := by
  rw [chartMeasure_eq_map, Measure.restrict_map (coordinates_continuous _).measurable
    (measurable_coordinatePiece cover n)]
  rw [show coordinates (cover.chart n) ⁻¹' coordinatePiece cover n = liftedPiece cover n from
    Set.ext fun y => coordinates_mem_coordinatePiece_iff cover n y]

private lemma piece_ae_eq_of_represents (cover : CountableCover F ζ hζ U R P H)
    (f g : PieceSequence cover) (u : PieceHilbert cover)
    (hf : RepresentsComponents cover f u) (hg : RepresentsComponents cover g u) :
    ∀ n : ℕ, f.val n =ᵐ[(chartMeasure (cover.chart n)).restrict (coordinatePiece cover n)]
      g.val n := by
  intro n
  have h1 : pieceCoefficient cover f n =ᵐ[(cover.chart n).liftedMeasure]
      pieceCoefficient cover g n := (hf n).trans (hg n).symm
  have h2 : pieceCoefficient cover f n
      =ᵐ[((cover.chart n).liftedMeasure).restrict (liftedPiece cover n)]
      pieceCoefficient cover g n := ae_restrict_of_ae h1
  rw [chartMeasure_restrict cover n]
  exact (measurableEmbedding_coordinates (cover.chart n)).ae_map_iff.mpr h2

structure Properties (cover : CountableCover F ζ hζ U R P H) : Prop where
  extraction_gluing : ∀ (u : PieceHilbert cover) (f : PieceSequence cover)
    (hf : RepresentsComponents cover f u),
    Ext cover (toAeQuotient (gluedFamily μG hμG hR cover u f hf)) = u
  indicator_gluing_pointwise : ∀ (v : SquareFiniteFamily (U := U) (H := H))
    (a : ShrunkChart F ζ hζ U R P H) (x : omega a),
    coefficient (G cover (indicatorSequence cover v.val)) a x = coefficient v.val a x
  indicator_gluing_family : ∀ v : SquareFiniteFamily (U := U) (H := H),
    G cover (indicatorSequence cover v.val) = v.val
  indicator_gluing_quotient : ∀ v : SquareFiniteFamily (U := U) (H := H),
    toAeQuotient (gluedFamily μG hμG hR cover (Ext cover (toAeQuotient v))
      (indicatorSequence cover v.val) (indicatorSequence_represents cover v)) = toAeQuotient v
  arbitrary_gluing_quotient : ∀ (v : SquareFiniteFamily (U := U) (H := H))
    (g : PieceSequence cover) (hg : RepresentsComponents cover g (Ext cover (toAeQuotient v))),
    toAeQuotient (gluedFamily μG hμG hR cover (Ext cover (toAeQuotient v)) g hg) = toAeQuotient v

end DedekindZetaZeroFree.KPContActualCotangentGluingInverseIdentities

namespace DedekindZetaZeroFree

open KPContActualCotangentExactMeasurableGluing KPContActualCotangentPieceExtraction
  KPContActualCotangentMeasurableFamilies

theorem kp_cont_actual_cotangent_gluing_inverse_identities
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (cover : KPContActualCotangentCountableShrinking.CountableCover F ζ hζ U R P H) :
    KPContActualCotangentGluingInverseIdentities.Properties μG hμG hR cover := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u f hf
    rw [KPContActualCotangentPieceExtraction.Ext_toAeQuotient]
    apply lp.ext
    funext n
    apply Subtype.ext
    apply Lp.ext
    have hcoe : ⇑(KPContActualCotangentPieceExtraction.pieceLp cover
        (KPContActualCotangentGluingInverseIdentities.gluedFamily μG hμG hR cover u f hf) n)
        =ᵐ[(cover.chart n).liftedMeasure]
        KPContActualCotangentPieceExtraction.e cover (G cover f) n :=
      MemLp.coeFn_toLp _
    exact hcoe.trans ((Filter.EventuallyEq.of_eq
      (KPContActualCotangentGluingInverseIdentities.e_G_eq_pieceCoefficient
        μG hμG hR cover f n)).trans (hf n))
  · intro v a x
    exact KPContActualCotangentGluingInverseIdentities.indicator_gluing_pointwise_aux cover v a x
  · intro v
    exact KPContActualCotangentGluingInverseIdentities.indicator_gluing_family_aux cover v
  · intro v
    exact KPContActualCotangentGluingInverseIdentities.indicator_gluing_quotient_aux
      (μG := μG) (hμG := hμG) (hR := hR) cover v
  · intro v g hg
    have hpiece := KPContActualCotangentGluingInverseIdentities.piece_ae_eq_of_represents cover
      g (KPContActualCotangentGluingInverseIdentities.indicatorSequence cover v.val)
      (KPContActualCotangentPieceExtraction.Ext cover (toAeQuotient v)) hg
      (KPContActualCotangentGluingInverseIdentities.indicatorSequence_represents cover v)
    have hintr := (kp_cont_actual_cotangent_piece_ae_transport F ζ hζ μG hμG U R hR P H cover).intrinsic
      g (KPContActualCotangentGluingInverseIdentities.indicatorSequence cover v.val) hpiece
    rw [KPContActualCotangentGluingInverseIdentities.indicator_gluing_family_aux cover v] at hintr
    exact (toAeQuotient_eq_iff (U := U) (H := H)
      (KPContActualCotangentGluingInverseIdentities.gluedFamily μG hμG hR cover
        (KPContActualCotangentPieceExtraction.Ext cover (toAeQuotient v)) g hg) v).mpr hintr

end DedekindZetaZeroFree

end
