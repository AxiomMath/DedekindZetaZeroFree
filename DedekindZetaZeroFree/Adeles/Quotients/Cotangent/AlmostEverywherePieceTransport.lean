module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.EquivariantBorelGluing

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentPieceAeTransport

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualCotangentCountableShrinking KPContActualCotangentBorelRefinement
open KPContActualCotangentExactMeasurableGluing KPContActualCotangentMeasurableFamilies
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

def coordinatePiece (cover : CountableCover F ζ hζ U R P H) (n : ℕ) :
    Set (omega (cover.chart n)) :=
  (fun y => q (cover.chart n) y.val) ⁻¹' basePiece cover n

structure Properties (cover : CountableCover F ζ hζ U R P H) : Prop where
  all_charts : ∀ (f g : PieceSequence cover),
    (∀ n : ℕ, f.val n =ᵐ[(chartMeasure (cover.chart n)).restrict
      (coordinatePiece cover n)] g.val n) →
    ∀ a : ShrunkChart F ζ hζ U R P H,
      coefficient (G cover f) a =ᵐ[chartMeasure a] coefficient (G cover g) a
  intrinsic : ∀ (f g : PieceSequence cover),
    (∀ n : ℕ, f.val n =ᵐ[(chartMeasure (cover.chart n)).restrict
      (coordinatePiece cover n)] g.val n) →
    AeEquivalent (G cover f) (G cover g)
  every_arrow : ∀ (f : PieceSequence cover) (n : ℕ)
    (r : omega (cover.chart n) → E F),
    r =ᵐ[(chartMeasure (cover.chart n)).restrict (coordinatePiece cover n)] f.val n →
    ∀ (a : ShrunkChart F ζ hζ U R P H)
      (ψ : ActualBranch a (cover.chart n)),
      ∀ᵐ x ∂((chartMeasure a).restrict
        {x : omega a | x.val ∈ ψ.arrow.domain ∧ q a x.val ∈ basePiece cover n}),
        ∀ hx : x.val ∈ ψ.arrow.domain,
          coefficient (G cover f) a x =
            (T ψ.arrow x.val hx).symm
              (r ⟨ψ.arrow.psi x.val, ψ.target_shrinking hx⟩)

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
    KPContCotangentOverlapNullEquivalence.liftedMeasure a =
      ((H.disintegration U).componentWeight a.component / (Nat.card a.Isotropy : ENNReal)) •
        (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)).restrict (omega a) := by
  let c := coordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)
  rw [KPContCotangentOverlapNullEquivalence.liftedMeasure, ShrunkChart.liftedMeasure,
    Measure.map_smul]
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

private theorem lifted_absolutelyContinuous (a : ShrunkChart F ζ hζ U R P H) :
    KPContCotangentOverlapNullEquivalence.liftedMeasure a ≪
        (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)).restrict (omega a) ∧
      (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)).restrict (omega a) ≪
        KPContCotangentOverlapNullEquivalence.liftedMeasure a := by
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
      (targetChart a b h).places = placeEquiv F ζ hζ :=
  cast_fields h.symm (isotropyChart b)

private theorem arrow_psi_formula {a b : ShrunkChart F ζ hζ U R P H}
    (e : ActualBranch a b) :
    e.arrow.psi = fun x => labeledAInv (placeEquiv F ζ hζ)
      ((e.arrow.gamma : KPCuspArithmetic.PGL2 F) • labeledA (placeEquiv F ζ hζ) x) := by
  obtain ⟨hb1, hb2⟩ := target_chart_fields a b e.component_eq
  funext x
  show labeledAInv (targetChart a b e.component_eq).places
      (((targetChart a b e.component_eq).kind.representative⁻¹ *
        (e.arrow.gamma : KPCuspArithmetic.PGL2 F) *
        (isotropyChart a).kind.representative) •
        labeledA (isotropyChart a).places x) = _
  rw [hb1, hb2, show (isotropyChart a).kind.representative = 1 from rfl,
    show (isotropyChart a).places = placeEquiv F ζ hζ from rfl]
  simp

private theorem psi_quasiMeasurePreserving {a b : ShrunkChart F ζ hζ U R P H}
    (e : ActualBranch a b) :
    Measure.QuasiMeasurePreserving e.arrow.psi
      (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ))
      (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)) := by
  rw [arrow_psi_formula e]
  exact (rational_preserving (F := F) (ζ := ζ) (hζ := hζ)
    (e.arrow.gamma : KPCuspArithmetic.PGL2 F)).quasiMeasurePreserving

private theorem labeledA_labeledAInv (p : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F))
    (z : KPCuspGenuineMonodromy.SymmetricSpace F) : labeledA p (labeledAInv p z) = z := by
  funext k
  simp [labeledAInv, labeledA]

 def Qfun (i : Fin (H.atlas U).componentCount) :
    M F → KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  fun x => KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i)
    (KPCuspSiegel.projection F (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i)
      (labeledA (placeEquiv F ζ hζ) x))

private theorem q_eq_Qfun (a : ShrunkChart F ζ hζ U R P H) :
    KPContCotangentOverlapRationalBranches.q a = Qfun (F := F) (ζ := ζ) (hζ := hζ) (U := U)
      (R := R) (P := P) (H := H) a.component := rfl

private theorem branch_quotient_compatibility {a b : ShrunkChart F ζ hζ U R P H}
    (e : ActualBranch a b) (x : M F) (hx : x ∈ e.arrow.domain) :
    KPContCotangentOverlapRationalBranches.q b (e.arrow.psi x)
      = KPContCotangentOverlapRationalBranches.q a x := by
  have hq : KPContCotangentOverlapRationalBranches.q b
      = KPContCotangentOverlapRationalBranches.q a := by
    simpa only [q_eq_Qfun] using congrArg (Qfun (F := F) (ζ := ζ) (hζ := hζ) (U := U)
      (R := R) (P := P) (H := H)) e.component_eq.symm
  rw [hq]
  have hpsi : e.arrow.psi x = labeledAInv (placeEquiv F ζ hζ)
      ((e.arrow.gamma : KPCuspArithmetic.PGL2 F) • labeledA (placeEquiv F ζ hζ) x) := by
    rw [arrow_psi_formula e]
  rw [hpsi, KPContCotangentOverlapRationalBranches.q,
    KPContCotangentOverlapRationalBranches.q,
    labeledA_labeledAInv (placeEquiv F ζ hζ) _]
  congr 1
  exact Quotient.sound (show (e.arrow.gamma : KPCuspArithmetic.PGL2 F) •
      labeledA (placeEquiv F ζ hζ) x ∈
      MulAction.orbit (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)
        (labeledA (placeEquiv F ζ hζ) x) from ⟨e.arrow.gamma, rfl⟩)

private theorem null_transfer {a b : ShrunkChart F ζ hζ U R P H}
    (e : ActualBranch a b) (T : Set (M F)) (hT : T ⊆ omega b)
    (hT0 : (KPContCotangentOverlapNullEquivalence.liftedMeasure b).restrict (omega b) T = 0) :
    (KPContCotangentOverlapNullEquivalence.liftedMeasure a).restrict (omega a)
      (e.arrow.psi ⁻¹' T ∩ omega a) = 0 := by
  have hb := lifted_absolutelyContinuous b
  have ha := lifted_absolutelyContinuous a
  have hcoord : coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ) T = 0 := by
    have h1 : KPContCotangentOverlapNullEquivalence.liftedMeasure b T = 0 := by
      rw [← Measure.restrict_eq_self _ hT]; exact hT0
    have h2 := hb.2 h1
    rwa [Measure.restrict_eq_self _ hT] at h2
  have hpre : coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ) (e.arrow.psi ⁻¹' T) = 0 :=
    (psi_quasiMeasurePreserving e).preimage_null hcoord
  have h2 : (coordinateMeasure (F := F) (ζ := ζ) (hζ := hζ)).restrict (omega a)
      (e.arrow.psi ⁻¹' T ∩ omega a) = 0 := by
    rw [Measure.restrict_eq_self _ (Set.inter_subset_right
      (s := e.arrow.psi ⁻¹' T) (t := omega a))]
    exact measure_mono_null Set.inter_subset_left hpre
  have h3 : KPContCotangentOverlapNullEquivalence.liftedMeasure a
      (e.arrow.psi ⁻¹' T ∩ omega a) = 0 := ha.1 h2
  rw [Measure.restrict_eq_self _ (Set.inter_subset_right
    (s := e.arrow.psi ⁻¹' T) (t := omega a))]
  exact h3

private theorem continuous_labeledA_placeEquiv :
    Continuous (labeledA (placeEquiv F ζ hζ)) := by
  apply continuous_pi
  intro k
  exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous

private theorem measurable_omega (a : ShrunkChart F ζ hζ U R P H) :
    MeasurableSet (omega a) :=
  a.domain_open.measurableSet.preimage continuous_labeledA_placeEquiv.measurable

private theorem measurable_q (a : ShrunkChart F ζ hζ U R P H) :
    Measurable (KPContCotangentOverlapRationalBranches.q a) := by
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
  have hcomp : KPContCotangentOverlapRationalBranches.q a =
      KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)
      ∘ KPCuspSiegel.projection F (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)
      ∘ labeledA (placeEquiv F ζ hζ) := rfl
  rw [hcomp]
  exact hcm.measurable.comp (hproj.comp continuous_labeledA_placeEquiv.measurable)

private theorem T_proof_irrel {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (ψ : Arrow a b) (x : M F) (h h' : x ∈ ψ.domain) : T ψ x h = T ψ x h' := by
  simp only [KPContCotangentActualGenuineTwistIsotropy.T]

private theorem every_arrow_ae
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (cover : CountableCover F ζ hζ U R P H) (f : PieceSequence cover) (n : ℕ)
    (r : omega (cover.chart n) → E F)
    (hr : r =ᵐ[(chartMeasure (cover.chart n)).restrict (coordinatePiece cover n)] f.val n)
    (a : ShrunkChart F ζ hζ U R P H) (ψ : ActualBranch a (cover.chart n)) :
    ∀ᵐ x ∂((chartMeasure a).restrict
      {x : omega a | x.val ∈ ψ.arrow.domain ∧ q a x.val ∈ basePiece cover n}),
      ∀ hx : x.val ∈ ψ.arrow.domain,
        coefficient (G cover f) a x =
          (T ψ.arrow x.val hx).symm (r ⟨ψ.arrow.psi x.val, ψ.target_shrinking hx⟩) := by
  classical
  have hbase := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover
  have hglue := kp_cont_actual_cotangent_exact_measurable_gluing F ζ hζ μG hμG U R hR P H cover
  have hNnull : (chartMeasure (cover.chart n)).restrict (coordinatePiece cover n)
      {y : omega (cover.chart n) | r y ≠ f.val n y} = 0 := by
    rw [← MeasureTheory.ae_iff]; exact hr
  set N : Set (omega (cover.chart n)) := {y | r y ≠ f.val n y} with hNdef
  have hN' : (chartMeasure (cover.chart n)).restrict (coordinatePiece cover n)
      (N ∩ coordinatePiece cover n) = 0 :=
    measure_mono_null Set.inter_subset_left hNnull
  set Tset : Set (M F) := Subtype.val '' (N ∩ coordinatePiece cover n) with hTdef
  have hTsub : Tset ⊆ omega (cover.chart n) := by
    rintro _ ⟨y, -, rfl⟩; exact y.property
  have hTnull : (KPContCotangentOverlapNullEquivalence.liftedMeasure (cover.chart n)).restrict
      (omega (cover.chart n)) Tset = 0 := by
    have h1 : (chartMeasure (cover.chart n)) (N ∩ coordinatePiece cover n) = 0 := by
      rw [← Measure.restrict_eq_self _ (Set.inter_subset_right
        (s := N) (t := coordinatePiece cover n))]
      exact hN'
    have h2 : (chartMeasure (cover.chart n)) (N ∩ coordinatePiece cover n) =
        (KPContCotangentOverlapNullEquivalence.liftedMeasure (cover.chart n)).restrict
          (omega (cover.chart n)) Tset := by
      rw [chartMeasure,
        (MeasurableEmbedding.subtype_coe (measurable_omega (cover.chart n))).comap_apply]
    rw [← h2]; exact h1
  have hBad : (KPContCotangentOverlapNullEquivalence.liftedMeasure a).restrict (omega a)
      (ψ.arrow.psi ⁻¹' Tset ∩ omega a) = 0 := null_transfer ψ Tset hTsub hTnull
  have hcomap : (chartMeasure a) (Subtype.val ⁻¹' (ψ.arrow.psi ⁻¹' Tset ∩ omega a)) = 0 := by
    rw [chartMeasure, (MeasurableEmbedding.subtype_coe (measurable_omega a)).comap_apply]
    have himg : (Subtype.val : omega a → M F) '' (Subtype.val ⁻¹' (ψ.arrow.psi ⁻¹' Tset ∩ omega a))
        = ψ.arrow.psi ⁻¹' Tset ∩ omega a := by
      ext y; constructor
      · rintro ⟨z, hz, rfl⟩; exact hz
      · intro hy; exact ⟨⟨y, hy.2⟩, hy, rfl⟩
    rw [himg]; exact hBad
  have hSmeas : MeasurableSet
      {x : omega a | x.val ∈ ψ.arrow.domain ∧ q a x.val ∈ basePiece cover n} :=
    (ψ.arrow.isOpen_domain.measurableSet.preimage measurable_subtype_coe).inter
      ((hbase.base_measurable n).preimage ((measurable_q a).comp measurable_subtype_coe))
  rw [MeasureTheory.ae_restrict_iff' hSmeas, MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hcomap
  intro x hx
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hx ⊢
  rw [not_imp] at hx
  obtain ⟨hxS, hxQ⟩ := hx
  obtain ⟨hd, hq⟩ := hxS
  refine ⟨?_, x.property⟩
  refine ⟨⟨ψ.arrow.psi x.val, ψ.target_shrinking hd⟩, ⟨?_, ?_⟩, rfl⟩
  · have hneq : r ⟨ψ.arrow.psi x.val, ψ.target_shrinking hd⟩
        ≠ f.val n ⟨ψ.arrow.psi x.val, ψ.target_shrinking hd⟩ := by
      intro heq
      push Not at hxQ
      obtain ⟨hx, hne⟩ := hxQ
      have hg := hglue.every_arrow f a n ψ x.val hd hq
      have h1 : coefficient (G cover f) a x =
          (T ψ.arrow x.val hd).symm (f.val n ⟨ψ.arrow.psi x.val, ψ.target_shrinking hd⟩) := by
        rw [show coefficient (G cover f) a x =
            coefficient (G cover f) a ⟨x.val, ψ.source_shrinking hd⟩ from
          congrArg (coefficient (G cover f) a) (Subtype.ext rfl)]
        exact hg
      have hTx : T ψ.arrow x.val hx = T ψ.arrow x.val hd := T_proof_irrel ψ.arrow x.val hx hd
      have heq' : r ⟨ψ.arrow.psi x.val, ψ.target_shrinking hd⟩ =
          f.val n ⟨ψ.arrow.psi x.val, ψ.target_shrinking hd⟩ := by
        rw [show (⟨ψ.arrow.psi x.val, ψ.target_shrinking hd⟩ : omega (cover.chart n)) =
            ⟨ψ.arrow.psi x.val, ψ.target_shrinking hx⟩ from Subtype.ext rfl]
        exact heq
      exact hne (by
        rw [h1, ← hTx, show r ⟨ψ.arrow.psi x.val, ψ.target_shrinking hx⟩ =
          r ⟨ψ.arrow.psi x.val, ψ.target_shrinking hd⟩ from
            congrArg r (Subtype.ext rfl), heq'])
    exact hneq
  · have hq' : q (cover.chart n) (ψ.arrow.psi x.val) = q a x.val :=
      branch_quotient_compatibility ψ x.val hd
    change q (cover.chart n) (ψ.arrow.psi x.val) ∈ basePiece cover n
    rw [hq']; exact hq

private theorem all_charts_ae
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (cover : CountableCover F ζ hζ U R P H) (f g : PieceSequence cover)
    (hfg : ∀ n : ℕ, f.val n =ᵐ[(chartMeasure (cover.chart n)).restrict
      (coordinatePiece cover n)] g.val n)
    (a : ShrunkChart F ζ hζ U R P H) :
    coefficient (G cover f) a =ᵐ[chartMeasure a] coefficient (G cover g) a := by
  classical
  have hglue := kp_cont_actual_cotangent_exact_measurable_gluing F ζ hζ μG hμG U R hR P H cover
  have hbase := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover
  have hpart := partition_properties cover
  have hAmeas : MeasurableSet
      {x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x} := by
    have heq : {x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x} =
        (fun x => (coefficient (G cover f) a x, coefficient (G cover g) a x)) ⁻¹'
          (Set.diagonal (E F))ᶜ := by
      ext x; simp [Set.mem_diagonal]
    rw [heq]
    exact isClosed_diagonal.isOpen_compl.measurableSet.preimage
      (Measurable.prod (f := fun x : omega a =>
          (coefficient (G cover f) a x, coefficient (G cover g) a x))
        (hglue.chart_measurable f a) (hglue.chart_measurable g a))
  have hcell : ∀ p : ℕ × ℕ, (chartMeasure a).restrict
      {x : omega a | x.val ∈ cell cover a p.1 p.2}
      {x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x} = 0 := by
    rintro ⟨n, k⟩
    cases hb : (enumeration cover a n).branch k with
    | none =>
      have hempty : {x : omega a | x.val ∈ cell cover a n k} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        have h := cell_subset_domain cover a n k hx
        rw [hb] at h
        exact h
      rw [hempty, Measure.restrict_empty]
      simp
    | some e =>
      have hSe : MeasurableSet
          {x : omega a | x.val ∈ e.arrow.domain ∧ q a x.val ∈ basePiece cover n} :=
        (e.arrow.isOpen_domain.measurableSet.preimage measurable_subtype_coe).inter
          ((hbase.base_measurable n).preimage ((measurable_q a).comp measurable_subtype_coe))
      have hSsub : {x : omega a | x.val ∈ cell cover a n k} ⊆
          {x : omega a | x.val ∈ e.arrow.domain ∧ q a x.val ∈ basePiece cover n} :=
        fun x hx => ⟨by
          have h := cell_subset_domain cover a n k hx
          rw [hb] at h
          exact h, hx.1⟩
      have h1 := every_arrow_ae μG hμG hR cover f n (g.val n) ((hfg n).symm) a e
      have h1' : ∀ᵐ x ∂(chartMeasure a), x ∈
          {x : omega a | x.val ∈ e.arrow.domain ∧ q a x.val ∈ basePiece cover n} →
          coefficient (G cover f) a x = coefficient (G cover g) a x := by
        refine ((MeasureTheory.ae_restrict_iff' hSe).mp h1).mono ?_
        intro x hx hxSe
        obtain ⟨hxd, hq⟩ := hxSe
        have hg := hglue.every_arrow g a n e x.val hxd hq
        rw [hx ⟨hxd, hq⟩ hxd]
        exact ((congrArg (coefficient (G cover g) a) (Subtype.ext rfl)).symm.trans hg).symm
      rw [← MeasureTheory.ae_iff]
      refine ae_restrict_of_ae_restrict_of_subset hSsub ?_
      exact (MeasureTheory.ae_restrict_iff' hSe).mpr h1'
  change ∀ᵐ x ∂chartMeasure a, coefficient (G cover f) a x = coefficient (G cover g) a x
  rw [MeasureTheory.ae_iff]
  have hcov : (⋃ p : ℕ × ℕ, {x : omega a | x.val ∈ cell cover a p.1 p.2}) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x.val ∈ ⋃ i : ℕ × ℕ, cell cover a i.1 i.2 := by
      rw [hpart.covers a]; exact x.property
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨p, hp⟩
  have hle : (chartMeasure a)
      {x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x} ≤
      ∑' p : ℕ × ℕ, (chartMeasure a).restrict {x : omega a | x.val ∈ cell cover a p.1 p.2}
        {x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x} := by
    calc (chartMeasure a) {x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x}
        = (chartMeasure a) ({x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x} ∩
            ⋃ p : ℕ × ℕ, {x : omega a | x.val ∈ cell cover a p.1 p.2}) := by
          rw [hcov, Set.inter_univ]
      _ ≤ ∑' p : ℕ × ℕ, (chartMeasure a)
            ({x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x} ∩
              {x : omega a | x.val ∈ cell cover a p.1 p.2}) := by
          rw [Set.inter_iUnion]
          exact measure_iUnion_le _
      _ = ∑' p : ℕ × ℕ, (chartMeasure a).restrict {x : omega a | x.val ∈ cell cover a p.1 p.2}
            {x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x} := by
          refine tsum_congr fun p => ?_
          rw [Measure.restrict_apply hAmeas]
  have hzero : (∑' p : ℕ × ℕ, (chartMeasure a).restrict
      {x : omega a | x.val ∈ cell cover a p.1 p.2}
      {x : omega a | coefficient (G cover f) a x ≠ coefficient (G cover g) a x}) = 0 := by
    simp [hcell]
  exact le_antisymm (hle.trans_eq hzero) (by simp)

end DedekindZetaZeroFree.KPContActualCotangentPieceAeTransport

namespace DedekindZetaZeroFree

theorem kp_cont_actual_cotangent_piece_ae_transport
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (cover : KPContActualCotangentCountableShrinking.CountableCover F ζ hζ U R P H) :
    KPContActualCotangentPieceAeTransport.Properties cover := by
  refine ⟨?_, ?_, ?_⟩
  · intro f g hfg a
    exact KPContActualCotangentPieceAeTransport.all_charts_ae μG hμG hR cover f g hfg a
  · intro f g hfg
    exact (KPContActualCotangentMeasurableFamilies.aeEquivalent_iff_all_charts
      (KPContActualCotangentExactMeasurableGluing.G cover f)
      (KPContActualCotangentExactMeasurableGluing.G cover g)).mpr
      (fun a => KPContActualCotangentPieceAeTransport.all_charts_ae μG hμG hR cover f g hfg a)
  · intro f n r hr a ψ
    exact KPContActualCotangentPieceAeTransport.every_arrow_ae μG hμG hR cover f n r hr a ψ

end DedekindZetaZeroFree

end
