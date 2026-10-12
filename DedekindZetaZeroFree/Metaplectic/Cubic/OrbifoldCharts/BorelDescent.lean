module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.CountableShrinkingCharts

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContCotangentFiniteQuotientBorel

def BorelDescends {Ω B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (q : Ω → B) (f : Ω → S) : Prop :=
  ∃! fbar : B → S, Measurable fbar ∧ ∀ x, fbar (q x) = f x

private theorem borelDescends_of_continuous_surjective
    {Ω B S : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [TopologicalSpace B] [T0Space B] [SecondCountableTopology B]
    [MeasurableSpace B] [BorelSpace B] [MeasurableSpace S]
    (q : Ω → B) (hq : Continuous q) (hsurj : Function.Surjective q)
    (f : Ω → S) (hf : Measurable f) (hcompat : ∀ x y, q x = q y → f x = f y) :
    BorelDescends q f := by
  set fbar : B → S := fun b => f (Function.surjInv hsurj b) with hfbar
  have hcomp : fbar ∘ q = f := by
    funext x
    simp only [Function.comp_apply, hfbar]
    exact (hcompat x (Function.surjInv hsurj (q x))
      (Function.surjInv_eq hsurj (q x)).symm).symm
  have hmeas : Measurable fbar := by
    rw [measurable_iff_comap_le]
    have hmap : MeasurableSpace.map q ‹MeasurableSpace Ω› = ‹MeasurableSpace B› := by
      rw [Continuous.map_eq_borel hq hsurj]
      exact (BorelSpace.measurable_eq (α := B)).symm
    rw [← hmap, ← MeasurableSpace.comap_le_iff_le_map,
      MeasurableSpace.comap_comp, hcomp]
    exact hf.comap_le
  refine ⟨fbar, ⟨hmeas, fun x => congrFun hcomp x⟩, ?_⟩
  rintro g ⟨hg, hgq⟩
  funext b
  obtain ⟨x, rfl⟩ := hsurj b
  rw [hgq x]
  exact (congrFun hcomp x).symm

open KPContSectorPhaseComponentCharts KPContSectorCoveredQuotientVocabulary
open KPContActualCotangentCountableShrinking

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

private lemma projection_orbit {i : Fin (H.atlas U).componentCount}
    {y z : SymmetricSpace F}
    (h : KPCuspSiegel.projection F (Component F ζ hζ U R P H i) y =
      KPCuspSiegel.projection F (Component F ζ hζ U R P H i) z) :
    ∃ γ : Component F ζ hζ U R P H i, γ • z = y := by
  have hrel : MulAction.orbitRel (Component F ζ hζ U R P H i) (SymmetricSpace F) y z :=
    Quotient.exact h
  exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)

private lemma exists_stabilizer_smul_of_projection_eq
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x)
    {y z : SymmetricSpace F} (hy : y ∈ O.neighborhood) (hz : z ∈ O.neighborhood)
    (h : KPCuspSiegel.projection F (Component F ζ hζ U R P H i) y =
      KPCuspSiegel.projection F (Component F ζ hζ U R P H i) z) :
    ∃ σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x,
      (σ.val : KPCuspArithmetic.PGL2 F) • z = y := by
  obtain ⟨γ, hγ⟩ := projection_orbit (F := F) (ζ := ζ) (hζ := hζ) (U := U)
    (R := R) (P := P) (H := H) h
  have himg : y ∈ (fun w : SymmetricSpace F => complexProjectiveEmbedding F γ • w) ''
      O.neighborhood :=
    ⟨z, hz, by
      show complexProjectiveEmbedding F γ • z = y
      rw [complexProjectiveEmbedding_smul F γ z]
      exact hγ⟩
  have hfix : complexProjectiveEmbedding F γ • x = x :=
    MulAction.mem_stabilizer_iff.mp (O.separated
      ⟨complexProjectiveEmbedding F γ, Subgroup.mem_map_of_mem _ γ.property⟩
      ⟨y, himg, hy⟩)
  refine ⟨⟨γ, ?_⟩, hγ⟩
  refine MulAction.mem_stabilizer_iff.mpr ?_
  show (γ : KPCuspArithmetic.PGL2 F) • x = x
  rw [← complexProjectiveEmbedding_smul F γ x]
  exact hfix

def actualChartProjection (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) :
    O.neighborhood → baseChartImage F ζ hζ U R P H i x O :=
  fun y => ⟨(H.atlas U).components
    ⟨i, KPCuspSiegel.projection F (Component F ζ hζ U R P H i) y.val⟩,
      ⟨KPCuspSiegel.projection F (Component F ζ hζ U R P H i) y.val,
        ⟨y.val, y.property, rfl⟩, rfl⟩⟩

def actualChartAction (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x)
    (σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x)
    (y : O.neighborhood) : O.neighborhood :=
  (σ • ((1 : PhaseSheets F ζ hζ U), y)).2

theorem actual_chart_borel_descent
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x)
    {S : Type*} [MeasurableSpace S] (f : O.neighborhood → S) (hf : Measurable f)
    (hinv : ∀ σ y, f (actualChartAction F ζ hζ U R P H i x O σ y) = f y) :
    BorelDescends (actualChartProjection F ζ hζ U R P H i x O) f := by
  haveI : PolishSpace O.neighborhood := O.isOpen.polishSpace
  refine borelDescends_of_continuous_surjective (actualChartProjection F ζ hζ U R P H i x O)
    ?_ ?_ f hf ?_
  · have hF0 : Continuous (fun y : O.neighborhood =>
        (H.atlas U).components ⟨i,
          KPCuspSiegel.projection F (Component F ζ hζ U R P H i) y.val⟩) :=
      ((H.atlas U).components.continuous_toFun).comp
        (continuous_sigmaMk.comp
          (continuous_quotient_mk'.comp continuous_subtype_val))
    exact Continuous.subtype_mk hF0 (fun y =>
      ⟨KPCuspSiegel.projection F (Component F ζ hζ U R P H i) y.val,
        ⟨y.val, y.property, rfl⟩, rfl⟩)
  · intro b
    obtain ⟨v, ⟨w, hw, hvw⟩, hv⟩ := b.property
    refine ⟨⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    simp only [actualChartProjection]
    rw [hvw]
    exact hv
  · intro y z hyz
    have hproj : KPCuspSiegel.projection F (Component F ζ hζ U R P H i) y.val =
        KPCuspSiegel.projection F (Component F ζ hζ U R P H i) z.val := by
      have h1 : (H.atlas U).components ⟨i,
            KPCuspSiegel.projection F (Component F ζ hζ U R P H i) y.val⟩ =
          (H.atlas U).components ⟨i,
            KPCuspSiegel.projection F (Component F ζ hζ U R P H i) z.val⟩ := by
        have := congrArg (fun t : baseChartImage F ζ hζ U R P H i x O =>
          (t : KPFiniteCuspAtlas.rawXU F ζ hζ U)) hyz
        simpa only [actualChartProjection] using this
      have h2 : Sigma.mk i (KPCuspSiegel.projection F (Component F ζ hζ U R P H i) y.val) =
          Sigma.mk i (KPCuspSiegel.projection F (Component F ζ hζ U R P H i) z.val) :=
        (H.atlas U).components.injective h1
      injection h2 with _ hbb
    obtain ⟨σ, hσ⟩ := exists_stabilizer_smul_of_projection_eq F ζ hζ U R P H i x O
      y.property z.property hproj
    have hact : actualChartAction F ζ hζ U R P H i x O σ z = y := by
      apply Subtype.ext
      show ((σ • ((1 : PhaseSheets F ζ hζ U), z)).2 : SymmetricSpace F) = (y : SymmetricSpace F)
      have h2 : ((σ • ((1 : PhaseSheets F ζ hζ U), z)).2 : SymmetricSpace F) =
          (σ.val : KPCuspArithmetic.PGL2 F) • (z : SymmetricSpace F) :=
        congrArg Prod.snd (chartProduct_smul F ζ hζ U R P H i x O σ
          (1 : PhaseSheets F ζ hζ U) z)
      rw [h2]
      exact hσ
    rw [← hact]
    exact hinv σ z

theorem shrunk_chart_borel_descent
    (C : ShrunkChart F ζ hζ U R P H)
    {S : Type*} [MeasurableSpace S] (f : C.domain → S) (hf : Measurable f)
    (hinv : ∀ σ y, f (C.action σ y) = f y) :
    BorelDescends C.quotientMap f := by
  haveI : PolishSpace C.domain := C.domain_open.polishSpace
  refine borelDescends_of_continuous_surjective C.quotientMap ?_ ?_ f hf ?_
  · have htoBase : C.toBase = fun y : C.domain => (H.atlas U).components ⟨C.component,
        KPCuspSiegel.projection F (Component F ζ hζ U R P H C.component) y.val⟩ := by
      funext y
      exact ((H.atlas U).components_formula C.component
        (KPCuspSiegel.projection F (Component F ζ hζ U R P H C.component) y.val)).symm
    have hcont : Continuous C.toBase := by
      rw [htoBase]
      exact ((H.atlas U).components.continuous_toFun).comp
        (continuous_sigmaMk.comp
          (continuous_quotient_mk'.comp continuous_subtype_val))
    exact Continuous.subtype_mk hcont (fun y => Set.mem_range_self y)
  · intro b
    obtain ⟨y, hy⟩ := b.property
    exact ⟨y, Subtype.ext hy⟩
  · intro y z hyz
    have hbase : C.toBase y = C.toBase z := Subtype.ext_iff.mp hyz
    have hproj : KPCuspSiegel.projection F (Component F ζ hζ U R P H C.component) y.val =
        KPCuspSiegel.projection F (Component F ζ hζ U R P H C.component) z.val := by
      have h1 : (H.atlas U).components ⟨C.component,
            KPCuspSiegel.projection F (Component F ζ hζ U R P H C.component) y.val⟩ =
          (H.atlas U).components ⟨C.component,
            KPCuspSiegel.projection F (Component F ζ hζ U R P H C.component) z.val⟩ := by
        rw [← ((H.atlas U).components_formula C.component
            (KPCuspSiegel.projection F (Component F ζ hζ U R P H C.component) y.val)).symm,
          ← ((H.atlas U).components_formula C.component
            (KPCuspSiegel.projection F (Component F ζ hζ U R P H C.component) z.val)).symm]
        exact hbase
      have h2 : Sigma.mk C.component
            (KPCuspSiegel.projection F (Component F ζ hζ U R P H C.component) y.val) =
          Sigma.mk C.component
            (KPCuspSiegel.projection F (Component F ζ hζ U R P H C.component) z.val) :=
        (H.atlas U).components.injective h1
      injection h2 with _ hbb
    obtain ⟨σ, hσ⟩ := exists_stabilizer_smul_of_projection_eq F ζ hζ U R P H C.component
      C.center C.larger (C.closure_subset (subset_closure y.property))
      (C.closure_subset (subset_closure z.property)) hproj
    have hact : C.action σ z = y := by
      apply Subtype.ext
      show (σ.val : KPCuspArithmetic.PGL2 F) • (z : SymmetricSpace F) = (y : SymmetricSpace F)
      exact hσ
    rw [← hact]
    exact hinv σ z

end DedekindZetaZeroFree.KPContCotangentFiniteQuotientBorel

namespace DedekindZetaZeroFree

open KPContCotangentFiniteQuotientBorel KPContActualCotangentCountableShrinking
open KPContSectorPhaseComponentCharts KPContSectorCoveredQuotientVocabulary

theorem kp_cont_cotangent_finite_quotient_borel
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (S : Type*) [MeasurableSpace S] :
    (∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
      (O : OrbifoldChart F ζ hζ U R P H i x) (f : O.neighborhood → S),
      Measurable f →
      (∀ σ y, f (actualChartAction F ζ hζ U R P H i x O σ y) = f y) →
      BorelDescends (actualChartProjection F ζ hζ U R P H i x O) f) ∧
    (∀ (C : ShrunkChart F ζ hζ U R P H) (f : C.domain → S),
      Measurable f → (∀ σ y, f (C.action σ y) = f y) →
      BorelDescends C.quotientMap f) :=
  ⟨fun i x O f hf hinv => actual_chart_borel_descent F ζ hζ U R P H i x O f hf hinv,
    fun C f hf hinv => shrunk_chart_borel_descent F ζ hζ U R P H C f hf hinv⟩

end DedekindZetaZeroFree

end
