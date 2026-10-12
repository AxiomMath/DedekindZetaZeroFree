module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.GluingExtractionIdentities

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal BigOperators
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentPieceReconstruction

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualCotangentCountableShrinking KPContActualCotangentBorelRefinement
open KPContActualCotangentExactMeasurableGluing KPContActualCotangentMeasurableFamilies
open KPContActualCotangentPieceHilbertSum KPContActualCotangentPieceExtraction
open KPContActualCotangentGluedPieceIntegral KPContActualCotangentPieceAeTransport
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (cover : CountableCover F ζ hζ U R P H)

def originalPoint (a : ShrunkChart F ζ hζ U R P H) (x : omega a) : a.domain :=
  ⟨labeledA (placeEquiv F ζ hζ) x.val, x.property⟩

def selectedFields (u : PieceHilbert cover) : SequenceFields cover := fun n x =>
  KPMeasurableLocalL2.representative (localData (cover.chart n))
    (supportedPiece cover n) (u n) (originalPoint (cover.chart n) x)

 theorem originalPoint_coordinates (a : ShrunkChart F ζ hζ U R P H)
    (y : a.domain) : originalPoint a (coordinates a y) = y := by
  apply Subtype.ext
  funext k
  simp [originalPoint, coordinates, labeledA, labeledAInv]

 theorem coordinates_originalPoint (a : ShrunkChart F ζ hζ U R P H)
    (x : omega a) : coordinates a (originalPoint a x) = x := by
  apply Subtype.ext
  simp [originalPoint, coordinates, labeledA, labeledAInv]

private theorem selectedFields_zero_off (u : PieceHilbert cover) (n : ℕ)
    (y : omega (cover.chart n)) (hy : q (cover.chart n) y.val ∉ basePiece cover n) :
    selectedFields cover u n y = 0 := by
  have hspec := (KPMeasurableLocalL2.representative_spec (localData (cover.chart n))
    (supportedPiece cover n) (u n)).2.2.1
  refine hspec _ ?_
  intro hmem
  refine hy ?_
  have htb : (cover.chart n).toBase (originalPoint (cover.chart n) y) =
      q (cover.chart n) y.val := rfl
  have hmem' : (cover.chart n).toBase (originalPoint (cover.chart n) y) ∈ basePiece cover n := hmem
  rw [htb] at hmem'
  exact hmem'

private theorem continuous_labeledA :
    Continuous (labeledA (placeEquiv F ζ hζ) :
      M F → KPCuspGenuineMonodromy.SymmetricSpace F) :=
  continuous_pi fun k =>
    (continuous_apply ((placeEquiv F ζ hζ).symm k)).comp
      (CotangentLogCoframe.A (d F)).continuous

 theorem continuous_originalPoint (a : ShrunkChart F ζ hζ U R P H) :
    Continuous (originalPoint a) :=
  Continuous.subtype_mk (continuous_labeledA.comp continuous_subtype_val) fun x => x.property

private theorem selectedFields_measurable (u : PieceHilbert cover) (n : ℕ) :
    Measurable (selectedFields cover u n) :=
  ((KPMeasurableLocalL2.representative_spec (localData (cover.chart n))
    (supportedPiece cover n) (u n)).1).comp (continuous_originalPoint (cover.chart n)).measurable

private theorem labeledA_psi (a : ShrunkChart F ζ hζ U R P H) (γ : Gamma a)
    (y : M F) (hy : y ∈ omega a) :
    labeledA (placeEquiv F ζ hζ) ((isotropyArrow a γ).psi y) =
      (actualActionEquiv a γ (originalPoint a ⟨y, hy⟩)).val := by
  have h3 : labeledAInv (placeEquiv F ζ hζ)
      (actualActionEquiv a γ (originalPoint a ⟨y, hy⟩)).val = (isotropyArrow a γ).psi y := by
    have hc := coordinates_action a γ (originalPoint a ⟨y, hy⟩)
    rw [coordinates_originalPoint a ⟨y, hy⟩] at hc
    simpa [coordinates] using hc
  calc labeledA (placeEquiv F ζ hζ) ((isotropyArrow a γ).psi y)
      = labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ)
          (actualActionEquiv a γ (originalPoint a ⟨y, hy⟩)).val) := by rw [h3]
    _ = (actualActionEquiv a γ (originalPoint a ⟨y, hy⟩)).val := by
        funext k; simp [labeledA, labeledAInv]

private theorem actualTensor_originalPoint (a : ShrunkChart F ζ hζ U R P H) (γ : Gamma a)
    (y : M F) (hy : y ∈ omega a) :
    actualTensor a γ (originalPoint a ⟨y, hy⟩) =
      T (isotropyArrow a γ) y
        (KPContActualCotangentMeasurableFamilies.omega_subset_larger a hy) := by
  simp only [actualTensor, coordinates_originalPoint a ⟨y, hy⟩]

private theorem ambientSequence_of_mem (f : SequenceFields cover) (n : ℕ)
    (x : M F) (hx : x ∈ omega (cover.chart n)) :
    ambientSequence cover f n x = f n ⟨x, hx⟩ := dif_pos hx

private theorem selectedFields_equivariant (u : PieceHilbert cover) (n : ℕ)
    (γ : Gamma (cover.chart n)) (y : M F) (hy : y ∈ omega (cover.chart n)) :
    ambientSequence cover (selectedFields cover u) n
        ((isotropyArrow (cover.chart n) γ).psi y) =
      T (isotropyArrow (cover.chart n) γ) y
        (KPContActualCotangentMeasurableFamilies.omega_subset_larger (cover.chart n) hy)
        (ambientSequence cover (selectedFields cover u) n y) := by
  have hy' : (isotropyArrow (cover.chart n) γ).psi y ∈ omega (cover.chart n) :=
    KPContActualCotangentMeasurableFamilies.isotropy_mem (cover.chart n) γ y hy
  rw [ambientSequence_of_mem cover _ n _ hy', ambientSequence_of_mem cover _ n _ hy]
  simp only [selectedFields]
  have hspec := (KPMeasurableLocalL2.representative_spec (localData (cover.chart n))
    (supportedPiece cover n) (u n)).2.2.2 γ (originalPoint (cover.chart n) ⟨y, hy⟩)
  have harg : originalPoint (cover.chart n) ⟨(isotropyArrow (cover.chart n) γ).psi y, hy'⟩ =
      actualActionEquiv (cover.chart n) γ (originalPoint (cover.chart n) ⟨y, hy⟩) := by
    apply Subtype.ext
    exact labeledA_psi (cover.chart n) γ y hy
  rw [harg]
  simp only [localData] at hspec ⊢
  rw [hspec]
  exact congrArg (fun e => e (KPMeasurableLocalL2.representative (localData (cover.chart n))
    (supportedPiece cover n) (u n) (originalPoint (cover.chart n) ⟨y, hy⟩)))
    (actualTensor_originalPoint (cover.chart n) γ y hy)

theorem selectedFields_isPieceSequence (u : PieceHilbert cover) :
    IsPieceSequence cover (selectedFields cover u) := by
  refine ⟨selectedFields_measurable cover u, fun n y hy => selectedFields_zero_off cover u n y hy, ?_⟩
  intro n γ y hy
  exact selectedFields_equivariant cover u n γ y hy

def selectedSequence (u : PieceHilbert cover) : PieceSequence cover :=
  ⟨selectedFields cover u, selectedFields_isPieceSequence cover u⟩

theorem selectedSequence_represents (u : PieceHilbert cover) :
    RepresentsComponents cover (selectedSequence cover u) u := by
  intro n
  filter_upwards [(KPMeasurableLocalL2.representative_spec (localData (cover.chart n))
    (supportedPiece cover n) (u n)).2.1] with y hy
  simp only [selectedSequence, selectedFields, pieceCoefficient]
  rw [originalPoint_coordinates]
  exact hy

def reconstructFamily (u : PieceHilbert cover) : Family (U := U) (H := H) :=
  G cover (selectedSequence cover u)

theorem reconstructFamily_squareFinite (u : PieceHilbert cover) :
    squareFinite (reconstructFamily cover u) :=
  (kp_cont_actual_cotangent_glued_piece_integral F ζ hζ R.adelicHaar R.adelic_isHaar U R rfl P H
    cover).gluing_squareFinite (selectedSequence cover u) u (selectedSequence_represents cover u)

def reconstruct (u : PieceHilbert cover) : SquareFiniteFamily (U := U) (H := H) :=
  ⟨reconstructFamily cover u, reconstructFamily_squareFinite cover u⟩

private theorem measurable_omega' (a : ShrunkChart F ζ hζ U R P H) :
    MeasurableSet (omega a) :=
  a.domain_open.measurableSet.preimage continuous_labeledA.measurable

 def coordinatesMeasurableEquiv (a : ShrunkChart F ζ hζ U R P H) :
    a.domain ≃ᵐ omega a where
  toFun := coordinates a
  invFun := originalPoint a
  left_inv := originalPoint_coordinates a
  right_inv := coordinates_originalPoint a
  measurable_toFun := (coordinates_continuous a).measurable
  measurable_invFun := (continuous_originalPoint a).measurable

private theorem chartMeasure_eq_map_coordinates (a : ShrunkChart F ζ hζ U R P H) :
    chartMeasure a = Measure.map (coordinates a) a.liftedMeasure := by
  have hω : MeasurableSet (omega a) := measurable_omega' a
  have hf : MeasurableEmbedding (Subtype.val : omega a → M F) :=
    MeasurableEmbedding.subtype_coe hω
  rw [chartMeasure, KPContCotangentOverlapNullEquivalence.liftedMeasure]
  rw [show (fun y : a.domain => labeledAInv (placeEquiv F ζ hζ) y.val)
      = (Subtype.val ∘ coordinates a) from rfl]
  rw [← Measure.map_map measurable_subtype_coe (coordinates_continuous a).measurable]
  rw [hf.comap_restrict]
  rw [show (Subtype.val : omega a → M F) ⁻¹' omega a = Set.univ from
    Set.eq_univ_of_forall (fun x => x.property)]
  rw [Measure.restrict_univ, hf.comap_map]

private theorem q_coordinates' (C : ShrunkChart F ζ hζ U R P H) (y : C.domain) :
    q C (coordinates C y).val = C.toBase y := by
  rw [KPContCotangentOverlapRationalBranches.q, ShrunkChart.toBase,
    KPContActualCotangentPieceHilbertSum.coordinates]
  congr 1
  have h : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y.val) = y.val := by
    funext k; simp [labeledA, labeledAInv]
  rw [h]

private theorem coordinates_preimage_coordinatePiece (cover : CountableCover F ζ hζ U R P H)
    (n : ℕ) :
    coordinates (cover.chart n) ⁻¹' coordinatePiece cover n = liftedPiece cover n := by
  ext y
  rw [Set.mem_preimage, coordinatePiece, Set.mem_preimage, liftedPiece, Set.mem_preimage,
    q_coordinates']

 theorem ae_on_piece_of_ae_liftedMeasure (cover : CountableCover F ζ hζ U R P H)
    (n : ℕ) (f g : omega (cover.chart n) → E F)
    (h : (fun y : (cover.chart n).domain => f (coordinates (cover.chart n) y))
      =ᵐ[(cover.chart n).liftedMeasure]
      (fun y : (cover.chart n).domain => g (coordinates (cover.chart n) y))) :
    f =ᵐ[(chartMeasure (cover.chart n)).restrict (coordinatePiece cover n)] g := by
  have hcoord : MeasurableEmbedding (coordinates (cover.chart n)) :=
    (coordinatesMeasurableEquiv (cover.chart n)).measurableEmbedding
  have hrestr : (chartMeasure (cover.chart n)).restrict (coordinatePiece cover n)
      = Measure.map (coordinates (cover.chart n))
          (((cover.chart n).liftedMeasure).restrict (liftedPiece cover n)) := by
    rw [chartMeasure_eq_map_coordinates, hcoord.restrict_map,
      coordinates_preimage_coordinatePiece]
  rw [hrestr]
  exact (hcoord.ae_map_iff).2 (ae_restrict_of_ae h)

 theorem selectedFields_ae (cover : CountableCover F ζ hζ U R P H)
    (u : PieceHilbert cover) (n : ℕ) :
    (fun y : (cover.chart n).domain =>
        selectedFields cover u n (coordinates (cover.chart n) y))
      =ᵐ[(cover.chart n).liftedMeasure] ((u n).val : (cover.chart n).domain → E F) := by
  have hspec := (KPMeasurableLocalL2.representative_spec (localData (cover.chart n))
    (supportedPiece cover n) (u n)).2.1
  filter_upwards [hspec] with y hy
  rw [selectedFields, originalPoint_coordinates]
  exact hy

def Rec : PieceHilbert cover →ₗ[ℂ] CotangentAeQuotient (U := U) (H := H) where
  toFun := fun u => toAeQuotient (reconstruct cover u)
  map_add' := by
    intro u v
    show toAeQuotient (reconstruct cover (u + v)) =
      toAeQuotient (reconstruct cover u) + toAeQuotient (reconstruct cover v)
    rw [← toAeQuotient_add, toAeQuotient_eq_iff]
    show AeEquivalent (G cover (selectedSequence cover (u + v)))
      (G cover (selectedSequence cover u) + G cover (selectedSequence cover v))
    rw [← (kp_cont_actual_cotangent_exact_measurable_gluing F ζ hζ R.adelicHaar
      R.adelic_isHaar U R rfl P H cover).add (selectedSequence cover u)
      (selectedSequence cover v)]
    refine (kp_cont_actual_cotangent_piece_ae_transport F ζ hζ R.adelicHaar
      R.adelic_isHaar U R rfl P H cover).intrinsic (selectedSequence cover (u + v))
      (selectedSequence cover u + selectedSequence cover v) ?_
    intro n
    refine ae_on_piece_of_ae_liftedMeasure cover n _ _ ?_
    have h1 : (u + v) n = u n + v n := congrFun (lp.coeFn_add u v) n
    have h2 : (fun y : (cover.chart n).domain => ((u + v) n).val y)
        =ᵐ[(cover.chart n).liftedMeasure]
        (fun y => (u n).val y + (v n).val y) := by
      rw [h1]
      exact Lp.coeFn_add _ _
    exact (selectedFields_ae cover (u + v) n).trans (h2.trans
      ((selectedFields_ae cover u n).symm.add (selectedFields_ae cover v n).symm))
  map_smul' := by
    intro c u
    show toAeQuotient (reconstruct cover (c • u)) = c • toAeQuotient (reconstruct cover u)
    rw [← toAeQuotient_smul, toAeQuotient_eq_iff]
    show AeEquivalent (G cover (selectedSequence cover (c • u)))
      (c • G cover (selectedSequence cover u))
    rw [← (kp_cont_actual_cotangent_exact_measurable_gluing F ζ hζ R.adelicHaar
      R.adelic_isHaar U R rfl P H cover).smul c (selectedSequence cover u)]
    refine (kp_cont_actual_cotangent_piece_ae_transport F ζ hζ R.adelicHaar
      R.adelic_isHaar U R rfl P H cover).intrinsic (selectedSequence cover (c • u))
      (c • selectedSequence cover u) ?_
    intro n
    refine ae_on_piece_of_ae_liftedMeasure cover n _ _ ?_
    have h1 : (c • u) n = c • u n := congrFun (lp.coeFn_smul c u) n
    have h2 : (fun y : (cover.chart n).domain => ((c • u) n).val y)
        =ᵐ[(cover.chart n).liftedMeasure]
        (fun y => c • (u n).val y) := by
      rw [h1]
      exact Lp.coeFn_smul _ _
    exact (selectedFields_ae cover (c • u) n).trans (h2.trans
      ((selectedFields_ae cover u n).symm.const_smul c))

theorem extraction_reconstruction (u : PieceHilbert cover) :
    Ext cover (Rec cover u) = u := by
  have h := (kp_cont_actual_cotangent_gluing_inverse_identities F ζ hζ R.adelicHaar
    R.adelic_isHaar U R rfl P H cover).extraction_gluing u (selectedSequence cover u)
    (selectedSequence_represents cover u)
  have heq : reconstruct cover u = KPContActualCotangentGluingInverseIdentities.gluedFamily R.adelicHaar R.adelic_isHaar rfl cover u
      (selectedSequence cover u) (selectedSequence_represents cover u) := Subtype.ext rfl
  rw [show Rec cover u = toAeQuotient (KPContActualCotangentGluingInverseIdentities.gluedFamily R.adelicHaar R.adelic_isHaar rfl cover u
      (selectedSequence cover u) (selectedSequence_represents cover u)) from
    congrArg toAeQuotient heq]
  exact h

theorem reconstruction_extraction (v : CotangentAeQuotient (U := U) (H := H)) :
    Rec cover (Ext cover v) = v := by
  obtain ⟨v₀, hv₀⟩ := toAeQuotient_surjective (U := U) (H := H) v
  have hrep : RepresentsComponents cover (selectedSequence cover (Ext cover v))
      (Ext cover (toAeQuotient v₀)) := by
    rw [hv₀]
    exact selectedSequence_represents cover (Ext cover v)
  have h := (kp_cont_actual_cotangent_gluing_inverse_identities F ζ hζ R.adelicHaar
    R.adelic_isHaar U R rfl P H cover).arbitrary_gluing_quotient v₀
    (selectedSequence cover (Ext cover v)) hrep
  have heq : reconstruct cover (Ext cover v) = KPContActualCotangentGluingInverseIdentities.gluedFamily R.adelicHaar R.adelic_isHaar rfl
      cover (Ext cover v) (selectedSequence cover (Ext cover v))
      (selectedSequence_represents cover (Ext cover v)) := Subtype.ext rfl
  rw [show Rec cover (Ext cover v) = toAeQuotient (KPContActualCotangentGluingInverseIdentities.gluedFamily R.adelicHaar R.adelic_isHaar rfl
      cover (Ext cover v) (selectedSequence cover (Ext cover v))
      (selectedSequence_represents cover (Ext cover v))) from congrArg toAeQuotient heq]
  rw [show toAeQuotient (KPContActualCotangentGluingInverseIdentities.gluedFamily R.adelicHaar R.adelic_isHaar rfl
      cover (Ext cover v) (selectedSequence cover (Ext cover v))
      (selectedSequence_represents cover (Ext cover v))) = toAeQuotient (KPContActualCotangentGluingInverseIdentities.gluedFamily R.adelicHaar
      R.adelic_isHaar rfl cover (Ext cover (toAeQuotient v₀))
      (selectedSequence cover (Ext cover v)) hrep) from congrArg toAeQuotient (Subtype.ext rfl)]
  rw [h, hv₀]

def equiv : PieceHilbert cover ≃ₗ[ℂ] CotangentAeQuotient (U := U) (H := H) where
  toFun := Rec cover
  invFun := Ext cover
  left_inv := extraction_reconstruction cover
  right_inv := reconstruction_extraction cover
  map_add' := (Rec cover).map_add
  map_smul' := (Rec cover).map_smul

def IsComponentRepresentative (u : PieceHilbert cover) (n : ℕ)
    (r : omega (cover.chart n) → E F) : Prop :=
  (fun y : (cover.chart n).domain => r (coordinates (cover.chart n) y))
    =ᵐ[(cover.chart n).liftedMeasure] ((u n).val : (cover.chart n).domain → E F)

structure Properties : Prop where
  selected_represents : ∀ u : PieceHilbert cover,
    RepresentsComponents cover (selectedSequence cover u) u
  pointwise_every_arrow : ∀ (u : PieceHilbert cover)
    (a : ShrunkChart F ζ hζ U R P H) (n : ℕ)
    (ψ : ActualBranch a (cover.chart n)) (x : M F)
    (hx : x ∈ ψ.arrow.domain), q a x ∈ basePiece cover n →
    coefficient (reconstructFamily cover u) a ⟨x, ψ.source_shrinking hx⟩ =
      (T ψ.arrow x hx).symm
        ((selectedSequence cover u).val n ⟨ψ.arrow.psi x, ψ.target_shrinking hx⟩)
  every_arrow : ∀ (u : PieceHilbert cover) (n : ℕ)
    (r : omega (cover.chart n) → E F), IsComponentRepresentative cover u n r →
    ∀ (a : ShrunkChart F ζ hζ U R P H) (ψ : ActualBranch a (cover.chart n)),
      ∀ᵐ x ∂((chartMeasure a).restrict
        {x : omega a | x.val ∈ ψ.arrow.domain ∧ q a x.val ∈ basePiece cover n}),
        ∀ hx : x.val ∈ ψ.arrow.domain,
          coefficient (reconstructFamily cover u) a x =
            (T ψ.arrow x.val hx).symm
              (r ⟨ψ.arrow.psi x.val, ψ.target_shrinking hx⟩)
  branch_independent : ∀ (u : PieceHilbert cover) (n : ℕ)
    (r : omega (cover.chart n) → E F), IsComponentRepresentative cover u n r →
    ∀ (a : ShrunkChart F ζ hζ U R P H)
      (ψ θ : ActualBranch a (cover.chart n)),
      ∀ᵐ x ∂((chartMeasure a).restrict
        {x : omega a | x.val ∈ ψ.arrow.domain ∧ x.val ∈ θ.arrow.domain ∧
          q a x.val ∈ basePiece cover n}),
        ∀ (hψ : x.val ∈ ψ.arrow.domain) (hθ : x.val ∈ θ.arrow.domain),
          (T ψ.arrow x.val hψ).symm
              (r ⟨ψ.arrow.psi x.val, ψ.target_shrinking hψ⟩) =
            (T θ.arrow x.val hθ).symm
              (r ⟨θ.arrow.psi x.val, θ.target_shrinking hθ⟩)
  representative_independent : ∀ (u : PieceHilbert cover) (f : PieceSequence cover),
    RepresentsComponents cover f u → AeEquivalent (G cover f) (reconstructFamily cover u)
  alternative_squareFinite : ∀ (u : PieceHilbert cover) (f : PieceSequence cover),
    RepresentsComponents cover f u → squareFinite (G cover f)
  alternative_class : ∀ (u : PieceHilbert cover) (f : PieceSequence cover)
    (hf : RepresentsComponents cover f u) (hsq : squareFinite (G cover f)),
    toAeQuotient (⟨G cover f, hsq⟩ : SquareFiniteFamily (U := U) (H := H)) = Rec cover u
  covariance : ∀ (u : PieceHilbert cover)
    (a : ShrunkChart F ζ hζ U R P H) (γ : Gamma a) (x : M F) (hx : x ∈ omega a),
    coefficient (reconstructFamily cover u) a
        ⟨(isotropyArrow a γ).psi x, isotropy_mem a γ x hx⟩ =
      T (isotropyArrow a γ) x
        (KPContActualCotangentMeasurableFamilies.omega_subset_larger a hx)
        (coefficient (reconstructFamily cover u) a ⟨x, hx⟩)
  overlap : ∀ (u : PieceHilbert cover) (a b : ShrunkChart F ζ hζ U R P H)
    (θ : ActualBranch a b) (x : M F) (hx : x ∈ θ.arrow.domain),
    coefficient (reconstructFamily cover u) b ⟨θ.arrow.psi x, θ.target_shrinking hx⟩ =
      T θ.arrow x hx
        (coefficient (reconstructFamily cover u) a ⟨x, θ.source_shrinking hx⟩)
  chart_measurable : ∀ (u : PieceHilbert cover) (a : ShrunkChart F ζ hζ U R P H),
    Measurable (coefficient (reconstructFamily cover u) a)
  integral_eq_tsum : ∀ u : PieceHilbert cover,
    (∫⁻ x, ENNReal.ofReal ((normSquare (reconstructFamily cover u) x : ℝ))
      ∂(baseMeasure (R := R) (P := P) (U := U))) =
        ∑' n, pieceSquareIntegral cover (selectedSequence cover u) n
  tsum_eq_norm_sq : ∀ u : PieceHilbert cover,
    (∑' n, pieceSquareIntegral cover (selectedSequence cover u) n) =
      ENNReal.ofReal (‖u‖ ^ 2)
  arbitrary_representative_integrals : ∀ (u : PieceHilbert cover)
    (r : SequenceFields cover), (∀ n, IsComponentRepresentative cover u n (r n)) →
    (∫⁻ x, ENNReal.ofReal ((normSquare (reconstructFamily cover u) x : ℝ))
      ∂(baseMeasure (R := R) (P := P) (U := U))) =
        (∑' n, ∫⁻ y in coordinatePiece cover n, ENNReal.ofReal (‖r n y‖ ^ 2)
          ∂chartMeasure (cover.chart n)) ∧
    (∑' n, ∫⁻ y in coordinatePiece cover n, ENNReal.ofReal (‖r n y‖ ^ 2)
      ∂chartMeasure (cover.chart n)) = ENNReal.ofReal (‖u‖ ^ 2)
  extraction_formula : ∀ (v : SquareFiniteFamily (U := U) (H := H)) (n : ℕ),
    (equiv cover).symm (toAeQuotient v) n = component cover v n
  extraction_reconstruction : ∀ u : PieceHilbert cover, Ext cover (Rec cover u) = u
  reconstruction_extraction : ∀ v : CotangentAeQuotient (U := U) (H := H),
    Rec cover (Ext cover v) = v

end DedekindZetaZeroFree.KPContActualCotangentPieceReconstruction

namespace DedekindZetaZeroFree

open KPContActualCotangentCountableShrinking KPContActualCotangentBorelRefinement
open KPContActualCotangentExactMeasurableGluing KPContActualCotangentMeasurableFamilies
open KPContActualCotangentPieceHilbertSum KPContActualCotangentPieceExtraction
open KPContActualCotangentGluedPieceIntegral KPContActualCotangentPieceAeTransport
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy
open KPContActualCotangentGluingInverseIdentities
open KPContActualCotangentPieceReconstruction

end DedekindZetaZeroFree

end
