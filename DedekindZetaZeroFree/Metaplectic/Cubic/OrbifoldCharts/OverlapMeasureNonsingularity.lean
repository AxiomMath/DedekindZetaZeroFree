module

public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.RationalOverlapBranches

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContCotangentOverlapNullEquivalence

open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
open KPContCotangentOverlapRationalBranches

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

def liftedMeasure (a : ShrunkChart F ζ hζ U R P H) : Measure (M F) :=
  Measure.map (fun y : a.domain => labeledAInv (placeEquiv F ζ hζ) y.val)
    a.liftedMeasure

variable {a b : ShrunkChart F ζ hζ U R P H}

def forward (e : Branch a b) : e.domain → e.targetDomain :=
  fun x => ⟨e.psi x.val, Set.mem_image_of_mem e.psi x.property⟩

def backward (e : Branch a b) (he : e.Properties) : e.targetDomain → e.domain :=
  fun x => ⟨e.inverse x.val, he.inverse_target x.property⟩

structure NullEquivalence (e : Branch a b) (he : e.Properties) : Prop where
  forward_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (forward e)
      (Measure.comap (Subtype.val : e.domain → M F)
        ((liftedMeasure a).restrict e.domain))
      (Measure.comap (Subtype.val : e.targetDomain → M F)
        ((liftedMeasure b).restrict e.targetDomain))
  backward_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (backward e he)
      (Measure.comap (Subtype.val : e.targetDomain → M F)
        ((liftedMeasure b).restrict e.targetDomain))
      (Measure.comap (Subtype.val : e.domain → M F)
        ((liftedMeasure a).restrict e.domain))
  image_null_iff : ∀ (S : Set (M F)), S ⊆ e.domain →
    ((liftedMeasure a).restrict e.domain) S = 0 ↔
      ((liftedMeasure b).restrict e.targetDomain) (e.psi '' S) = 0
  preimage_null_iff : ∀ (Z : Set (M F)), Z ⊆ e.targetDomain →
    ((liftedMeasure b).restrict e.targetDomain) Z = 0 ↔
      ((liftedMeasure a).restrict e.domain) (e.psi ⁻¹' Z) = 0

 def coordHomeomorph : M F ≃ₜ KPCuspGenuineMonodromy.SymmetricSpace F where
  toFun := labeledA (placeEquiv F ζ hζ)
  invFun := labeledAInv (placeEquiv F ζ hζ)
  left_inv x := by simp [labeledAInv, labeledA]
  right_inv x := by funext k; simp [labeledAInv, labeledA]
  continuous_toFun := by
    apply continuous_pi
    intro k
    exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
  continuous_invFun := by
    apply (CotangentLogCoframe.A (d F)).symm.continuous.comp
    exact continuous_pi fun k => continuous_apply _

 def coordinateMeasure : Measure (M F) :=
  Measure.map (coordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)).symm
    (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))

private theorem lifted_formula (a : ShrunkChart F ζ hζ U R P H) :
    liftedMeasure a =
      ((H.disintegration U).componentWeight a.component / (Nat.card a.Isotropy : ℝ≥0∞)) •
        (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)).restrict (omega a) := by
  let c := coordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)
  rw [liftedMeasure, ShrunkChart.liftedMeasure, Measure.map_smul]
  · congr 1
    change Measure.map (c.symm ∘ (Subtype.val : a.domain → _)) _ = _
    rw [← Measure.map_map c.symm.measurable measurable_subtype_coe,
      map_comap_subtype_coe a.domain_open.measurableSet,
      Measure.restrict_restrict a.domain_open.measurableSet]
    simp only [Set.inter_self]
    rw [coordinateMeasure, c.symm.measurableEmbedding.restrict_map]
    have he : c.symm ⁻¹' omega a = a.domain := by
      ext x
      change c (c.symm x) ∈ a.domain ↔ x ∈ a.domain
      rw [c.apply_symm_apply]
    exact congrArg (fun s => Measure.map c.symm
      ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict s)) he.symm
  · exact (c.symm.measurable.comp measurable_subtype_coe).aemeasurable

private theorem lifted_equivalent (a : ShrunkChart F ζ hζ U R P H) :
    liftedMeasure a ≪ (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)).restrict (omega a) ∧
    (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)).restrict (omega a) ≪ liftedMeasure a := by
  rw [lifted_formula]
  refine ⟨Measure.smul_absolutelyContinuous, Measure.absolutelyContinuous_smul ?_⟩
  exact ENNReal.div_ne_zero.mpr ⟨ne_of_gt ((H.disintegration U).positive_componentWeight a.component),
    ENNReal.natCast_ne_top _⟩

private theorem rational_preserving (g : KPCuspArithmetic.PGL2 F) :
    MeasurePreserving (fun x => labeledAInv (placeEquiv F ζ hζ)
      (g • labeledA (placeEquiv F ζ hζ) x))
      (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ))
      (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)) := by
  let c := coordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)
  have hs : MeasurePreserving c.symm
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) coordinateMeasure :=
    ⟨c.symm.measurable, rfl⟩
  exact (hs.comp (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F g)).comp
    (hs.symm c.symm.toMeasurableEquiv)

private theorem cast_fields {i j : Fin (H.atlas U).componentCount}
    (h : j = i) (c : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H) j) :
    (h ▸ c).kind.representative = c.kind.representative ∧ (h ▸ c).places = c.places := by
  cases h
  exact ⟨rfl, rfl⟩

private theorem target_chart_fields (a b : ShrunkChart F ζ hζ U R P H)
    (h : a.component = b.component) :
    (targetChart a b h).kind.representative = 1 ∧
      (targetChart a b h).places = placeEquiv F ζ hζ := by
  exact cast_fields h.symm (KPContCotangentActualGenuineTwistIsotropy.isotropyChart b)

private theorem branch_quasi (e : Branch a b) :
    Measure.QuasiMeasurePreserving e.psi
      (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ))
      (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)) ∧
    Measure.QuasiMeasurePreserving e.inverse
      (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ))
      (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)) := by
  cases e with
  | none => exact ⟨Measure.QuasiMeasurePreserving.id _, Measure.QuasiMeasurePreserving.id _⟩
  | some e =>
    have ht := target_chart_fields a b e.component_eq
    constructor
    · convert (rational_preserving (F := F) (ζ := ζ) (hζ := hζ)
        (e.arrow.gamma : KPCuspArithmetic.PGL2 F)).quasiMeasurePreserving using 1
      funext x
      change labeledAInv (targetChart a b e.component_eq).places
        (((targetChart a b e.component_eq).kind.representative⁻¹ *
          (e.arrow.gamma : KPCuspArithmetic.PGL2 F) * 1) •
            labeledA (placeEquiv F ζ hζ) x) = _
      rw [ht.1, ht.2]
      simp only [inv_one, one_mul, mul_one]
    · convert (rational_preserving (F := F) (ζ := ζ) (hζ := hζ)
        (e.arrow.gamma⁻¹ : KPCuspArithmetic.PGL2 F)).quasiMeasurePreserving using 1
      funext x
      change labeledAInv (placeEquiv F ζ hζ)
        ((1⁻¹ * (e.arrow.gamma⁻¹ : KPCuspArithmetic.PGL2 F) *
          (targetChart a b e.component_eq).kind.representative) •
            labeledA (targetChart a b e.component_eq).places x) = _
      rw [ht.1, ht.2]
      simp only [inv_one, one_mul, mul_one, Subgroup.coe_inv]

private theorem ambient_quasi (e : Branch a b) (he : e.Properties) :
    Measure.QuasiMeasurePreserving e.psi
      ((liftedMeasure a).restrict e.domain) ((liftedMeasure b).restrict e.targetDomain) ∧
    Measure.QuasiMeasurePreserving e.inverse
      ((liftedMeasure b).restrict e.targetDomain) ((liftedMeasure a).restrict e.domain) := by
  have ha := lifted_equivalent a
  have hb := lifted_equivalent b
  have har := ha.1.restrict e.domain
  have ha'r := ha.2.restrict e.domain
  have hbr := hb.1.restrict e.targetDomain
  have hb'r := hb.2.restrict e.targetDomain
  rw [Measure.restrict_restrict_of_subset he.source_subset] at har ha'r
  rw [Measure.restrict_restrict_of_subset he.target_subset] at hbr hb'r
  have hf := (branch_quasi e).1.restrict (Set.mapsTo_image e.psi e.domain)
  have hg := (branch_quasi e).2.restrict he.inverse_target
  exact ⟨(hf.mono_left har).mono_right hb'r, (hg.mono_left hbr).mono_right ha'r⟩

private theorem subtype_quasi (s t : Set (M F)) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (μ ν : Measure (M F)) (f : M F → M F)
    (hq : Measure.QuasiMeasurePreserving f μ ν) (hf : Set.MapsTo f s t) :
    Measure.QuasiMeasurePreserving (fun x : s => (⟨f x.val, hf x.property⟩ : t))
      (Measure.comap (Subtype.val : s → M F) μ)
      (Measure.comap (Subtype.val : t → M F) ν) := by
  let g := fun x : s => (⟨f x.val, hf x.property⟩ : t)
  have hg : Measurable g := (hq.measurable.comp measurable_subtype_coe).subtype_mk
  refine ⟨hg, Measure.AbsolutelyContinuous.mk ?_⟩
  intro Z hZ hnull
  rw [(MeasurableEmbedding.subtype_coe ht).comap_apply] at hnull
  rw [Measure.map_apply hg hZ, (MeasurableEmbedding.subtype_coe hs).comap_apply]
  apply measure_mono_null _ (hq.preimage_null hnull)
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨g x, hx, rfl⟩

private theorem image_null (e : Branch a b) (he : e.Properties)
    (S : Set (M F)) (hS : S ⊆ e.domain) :
    ((liftedMeasure a).restrict e.domain) S = 0 ↔
      ((liftedMeasure b).restrict e.targetDomain) (e.psi '' S) = 0 := by
  have hq := ambient_quasi e he
  constructor
  · intro hnull
    apply measure_mono_null _ (hq.2.preimage_null hnull)
    rintro _ ⟨x, hx, rfl⟩
    simpa only [Set.mem_preimage, he.left_inverse x (hS hx)] using hx
  · intro hnull
    exact measure_mono_null (Set.subset_preimage_image e.psi S) (hq.1.preimage_null hnull)

private theorem preimage_null (e : Branch a b) (he : e.Properties)
    (Z : Set (M F)) (hZ : Z ⊆ e.targetDomain) :
    ((liftedMeasure b).restrict e.targetDomain) Z = 0 ↔
      ((liftedMeasure a).restrict e.domain) (e.psi ⁻¹' Z) = 0 := by
  have hq := ambient_quasi e he
  constructor
  · exact hq.1.preimage_null
  · intro hnull
    apply measure_mono_null _ (hq.2.preimage_null hnull)
    intro x hx
    simpa only [Set.mem_preimage, he.right_inverse x (hZ hx)] using hx

theorem actual_nonsingularity (e : Branch a b) (he : e.Properties) :
    Measure.QuasiMeasurePreserving (forward e)
      (Measure.comap (Subtype.val : e.domain → M F) ((liftedMeasure a).restrict e.domain))
      (Measure.comap (Subtype.val : e.targetDomain → M F) ((liftedMeasure b).restrict e.targetDomain)) ∧
    Measure.QuasiMeasurePreserving (backward e he)
      (Measure.comap (Subtype.val : e.targetDomain → M F) ((liftedMeasure b).restrict e.targetDomain))
      (Measure.comap (Subtype.val : e.domain → M F) ((liftedMeasure a).restrict e.domain)) ∧
    (∀ S : Set (M F), S ⊆ e.domain →
      (((liftedMeasure a).restrict e.domain) S = 0 ↔
        ((liftedMeasure b).restrict e.targetDomain) (e.psi '' S) = 0)) ∧
    (∀ Z : Set (M F), Z ⊆ e.targetDomain →
      (((liftedMeasure b).restrict e.targetDomain) Z = 0 ↔
        ((liftedMeasure a).restrict e.domain) (e.psi ⁻¹' Z) = 0)) := by
  have hq := ambient_quasi e he
  refine ⟨?_, ?_, image_null e he, preimage_null e he⟩
  · exact subtype_quasi _ _ he.source_open.measurableSet he.target_open.measurableSet
      _ _ _ hq.1 (Set.mapsTo_image e.psi e.domain)
  · exact subtype_quasi _ _ he.target_open.measurableSet he.source_open.measurableSet
      _ _ _ hq.2 he.inverse_target

end DedekindZetaZeroFree.KPContCotangentOverlapNullEquivalence

namespace DedekindZetaZeroFree

end DedekindZetaZeroFree

end
