module

public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.EquivariantScalarAndCotangentData

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCompactEquivariantDescent

open KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy
open KPContActualCotangentCountableShrinking KPContCotangentOverlapRationalBranches
open KPContActualCotangentChartRestriction KPContActualSectorChartEquivariantInputs
open KPContActualSectorSmoothTestModules KPContActualCotangentMeasurableFamilies
open KPContCotangentRealOrthogonalComplexification

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem mem_omega_iff (C : ShrunkChart F ζ hζ U R P H) (x : M F) :
    x ∈ omega C ↔ baseReindex (F := F) x ∈ chart C := by
  simp only [KPContActualSectorChartEquivariantInputs.chart,
    KPContCotangentOverlapRationalBranches.omega,
    KPContActualSectorChartEquivariantInputs.toActual, Set.mem_preimage,
    LinearIsometryEquiv.symm_apply_apply]

private theorem continuous_labeledA_self :
    Continuous (labeledA (placeEquiv F ζ hζ) :
      M F → KPCuspGenuineMonodromy.SymmetricSpace F) := by
  apply continuous_pi
  intro k
  exact (continuous_apply (placeEquiv F ζ hζ |>.symm k)).comp
    (CotangentLogCoframe.A (d F)).continuous

private theorem continuous_proj_self (C : ShrunkChart F ζ hζ U R P H) :
    Continuous (KPCuspSiegel.projection F
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H C.component)) := by
  show Continuous (Quotient.mk _)
  exact continuous_quotient_mk'

private theorem continuous_componentMap_self (C : ShrunkChart F ζ hζ U R P H) :
    Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U
      ((H.atlas U).representative C.component)) := by
  have hh := (H.atlas U).components.continuous.comp (continuous_sigmaMk (i := C.component))
  simpa only [Function.comp_def, (H.atlas U).components_formula] using hh

private theorem continuous_q (C : ShrunkChart F ζ hζ U R P H) :
    Continuous (KPContCotangentOverlapRationalBranches.q C) :=
  (continuous_componentMap_self C).comp ((continuous_proj_self C).comp continuous_labeledA_self)

private theorem isotropyArrow_phase (C : ShrunkChart F ζ hζ U R P H) (γ : Gamma C)
    (x : M F) :
    (isotropyArrow C γ).phase x =
      (KPCuspGenuineMonodromy.chi F ζ hζ γ.val.2 : ℂ) := by
  simp [KPContCotangentActualOverlap.Arrow.phase, isotropyArrow, isotropyChart]

private theorem scalarCocycle_apply (C : ShrunkChart F ζ hζ U R P H) (γ : Gamma C)
    (x : EuclideanSpace ℝ (Fin (3 * d F))) (v : EuclideanSpace ℂ (Fin 1)) :
    (scalarCocycle C γ x) v =
      scalarReindex ((KPCuspGenuineMonodromy.chi F ζ hζ γ.val.2 : ℂ) *
        (scalarReindex.symm v)) := by
  simp [scalarCocycle, scalarPhase]

private theorem action_eq (C : ShrunkChart F ζ hζ U R P H) (γ : Gamma C) (x : M F) :
    action C γ (baseReindex (F := F) x) =
      baseReindex (F := F) ((isotropyArrow C γ).psi x) := by
  simp [KPContActualSectorChartEquivariantInputs.action,
    LinearIsometryEquiv.symm_apply_apply]

private theorem scalarData_act (C : ShrunkChart F ζ hζ U R P H) :
    (scalarData C).act = action C := rfl

private theorem scalarData_cocycle (C : ShrunkChart F ζ hζ U R P H) :
    (scalarData C).cocycle = scalarCocycle C := rfl

private theorem cotangentData_act (C : ShrunkChart F ζ hζ U R P H) :
    (cotangentData C).act = action C := rfl

private theorem cotangentData_cocycle (C : ShrunkChart F ζ hζ U R P H) :
    (cotangentData C).cocycle = cotangentCocycle C := rfl

private theorem T_apply' {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (ψ : Arrow a b) (x : M F) (hx : x ∈ ψ.domain) (v : E F) :
    T ψ x hx v = ψ.phase x •
      operatorComplexification (Fin (d F) × Fin 3) (Q ψ x) v := by
  have hQ : operatorComplexification (Fin (d F) × Fin 3) (Q ψ x) v =
      orthogonalComplexification (Fin (d F) × Fin 3) (q ψ x hx) v := by
    rw [← q_toContinuousLinearMap ψ x hx,
      ← orthogonalComplexification_toContinuousLinearMap]
    rfl
  rw [T_apply, ← hQ]

theorem scalar (C : ShrunkChart F ζ hζ U R P H)
    (h : EuclideanSpace ℝ (Fin (3 * d F)) → EuclideanSpace ℂ (Fin 1))
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) h (chart C))
    (hcompact : HasCompactSupport h)
    (hsupport : tsupport h ⊆ chart C)
    (hequiv : ∀ (γ : Gamma C) (x : EuclideanSpace ℝ (Fin (3 * d F))),
      x ∈ chart C → h ((scalarData C).act γ x) = (scalarData C).cocycle γ x (h x)) :
    ∃ f : localScalarTests C,
      ∀ x : omega C, scalarReindex (f.val x) = h (baseReindex x.val) := by
  let f : omega C → ℂ := fun x => scalarReindex.symm (h (baseReindex x.val))
  have hKcompact : IsCompact ((baseReindex (F := F)).symm '' tsupport h) :=
    hcompact.isCompact.image (baseReindex (F := F)).symm.continuous
  have hSK : {x : M F | ∃ hx : x ∈ omega C, f ⟨x, hx⟩ ≠ 0} ⊆
      (baseReindex (F := F)).symm '' tsupport h := by
    rintro x ⟨hx, hne⟩
    refine ⟨baseReindex (F := F) x, ?_, ?_⟩
    · by_contra hmem
      have hz : h (baseReindex (F := F) x) = 0 := by
        by_contra hc
        exact hmem (subset_tsupport h hc)
      exact hne (by simp [f, hz])
    · rw [LinearIsometryEquiv.symm_apply_apply]
  have hsub : localSupport C f ⊆
      KPContCotangentOverlapRationalBranches.q C '' ((baseReindex (F := F)).symm '' tsupport h) := by
    rw [localSupport]
    calc closure (KPContCotangentOverlapRationalBranches.q C ''
            {x : M F | ∃ hx : x ∈ omega C, f ⟨x, hx⟩ ≠ 0})
        ⊆ closure (KPContCotangentOverlapRationalBranches.q C ''
            ((baseReindex (F := F)).symm '' tsupport h)) :=
          closure_mono (Set.image_mono hSK)
      _ = KPContCotangentOverlapRationalBranches.q C ''
            ((baseReindex (F := F)).symm '' tsupport h) :=
          (hKcompact.image (continuous_q C)).isClosed.closure_eq
  have himage : KPContCotangentOverlapRationalBranches.q C ''
      ((baseReindex (F := F)).symm '' tsupport h) ⊆ C.baseDomain := by
    rintro z ⟨x, ⟨y, hy, hyx⟩, hqz⟩
    rw [← hqz, ← hyx]
    have hyc : baseReindex (F := F) ((baseReindex (F := F)).symm y) ∈ chart C := by
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact hsupport hy
    have hxω : (baseReindex (F := F)).symm y ∈ omega C := (mem_omega_iff C _).mpr hyc
    rw [show KPContCotangentOverlapRationalBranches.q C ((baseReindex (F := F)).symm y) =
      C.toBase ⟨labeledA (placeEquiv F ζ hζ) ((baseReindex (F := F)).symm y), hxω⟩ from rfl]
    exact Set.mem_range_self _
  have hfmem : f ∈ localScalarTests C := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨fun y => scalarReindex.symm (h (baseReindex y)), ?_, fun x => rfl⟩
      have hL : ContDiff ℝ (⊤ : ℕ∞)
          (fun v : EuclideanSpace ℂ (Fin 1) => scalarReindex.symm v) :=
        (LinearIsometryEquiv.contDiff scalarReindex.symm).restrict_scalars ℝ
      exact hL.contDiffOn.comp
        (hsmooth.comp ((baseReindex (F := F)).contDiff.contDiffOn)
          (fun x hx => (mem_omega_iff C x).mp hx))
        (Set.mapsTo_univ _ _)
    · intro γ x hx
      have hX : baseReindex (F := F) x ∈ chart C := (mem_omega_iff C x).mp hx
      have he' : h (baseReindex (F := F) ((isotropyArrow C γ).psi x)) =
          scalarCocycle C γ (baseReindex (F := F) x) (h (baseReindex (F := F) x)) := by
        have h1 := hequiv γ (baseReindex (F := F) x) hX
        rw [scalarData_act, scalarData_cocycle, action_eq C γ x] at h1
        exact h1
      show f ⟨(isotropyArrow C γ).psi x, isotropy_mem C γ x hx⟩ =
        (isotropyArrow C γ).phase x * f ⟨x, hx⟩
      rw [isotropyArrow_phase C γ x]
      show scalarReindex.symm (h (baseReindex (F := F) ((isotropyArrow C γ).psi x))) =
        (KPCuspGenuineMonodromy.chi F ζ hζ γ.val.2 : ℂ) *
          scalarReindex.symm (h (baseReindex (F := F) x))
      rw [he', scalarCocycle_apply, LinearIsometryEquiv.symm_apply_apply]
    · exact IsCompact.of_isClosed_subset (hKcompact.image (continuous_q C))
        isClosed_closure hsub
    · exact hsub.trans himage
  exact ⟨⟨f, hfmem⟩, fun x => by
    show scalarReindex (scalarReindex.symm (h (baseReindex x.val))) = h (baseReindex x.val)
    rw [LinearIsometryEquiv.apply_symm_apply]⟩

theorem cotangent (C : ShrunkChart F ζ hζ U R P H)
    (h : EuclideanSpace ℝ (Fin (3 * d F)) →
      EuclideanSpace ℂ (Fin (3 * d F)))
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) h (chart C))
    (hcompact : HasCompactSupport h)
    (hsupport : tsupport h ⊆ chart C)
    (hequiv : ∀ (γ : Gamma C) (x : EuclideanSpace ℝ (Fin (3 * d F))),
      x ∈ chart C → h ((cotangentData C).act γ x) = (cotangentData C).cocycle γ x (h x)) :
    ∃ f : localCotangentTests C,
      ∀ x : omega C, coefficientReindex (f.val x) = h (baseReindex x.val) := by
  let f : omega C → E F := fun x => coefficientReindex.symm (h (baseReindex x.val))
  have hKcompact : IsCompact ((baseReindex (F := F)).symm '' tsupport h) :=
    hcompact.isCompact.image (baseReindex (F := F)).symm.continuous
  have hSK : {x : M F | ∃ hx : x ∈ omega C, f ⟨x, hx⟩ ≠ 0} ⊆
      (baseReindex (F := F)).symm '' tsupport h := by
    rintro x ⟨hx, hne⟩
    refine ⟨baseReindex (F := F) x, ?_, ?_⟩
    · by_contra hmem
      have hz : h (baseReindex (F := F) x) = 0 := by
        by_contra hc
        exact hmem (subset_tsupport h hc)
      exact hne (by simp [f, hz])
    · rw [LinearIsometryEquiv.symm_apply_apply]
  have hsub : localSupport C f ⊆
      KPContCotangentOverlapRationalBranches.q C '' ((baseReindex (F := F)).symm '' tsupport h) := by
    rw [localSupport]
    calc closure (KPContCotangentOverlapRationalBranches.q C ''
            {x : M F | ∃ hx : x ∈ omega C, f ⟨x, hx⟩ ≠ 0})
        ⊆ closure (KPContCotangentOverlapRationalBranches.q C ''
            ((baseReindex (F := F)).symm '' tsupport h)) :=
          closure_mono (Set.image_mono hSK)
      _ = KPContCotangentOverlapRationalBranches.q C ''
            ((baseReindex (F := F)).symm '' tsupport h) :=
          (hKcompact.image (continuous_q C)).isClosed.closure_eq
  have himage : KPContCotangentOverlapRationalBranches.q C ''
      ((baseReindex (F := F)).symm '' tsupport h) ⊆ C.baseDomain := by
    rintro z ⟨x, ⟨y, hy, hyx⟩, hqz⟩
    rw [← hqz, ← hyx]
    have hyc : baseReindex (F := F) ((baseReindex (F := F)).symm y) ∈ chart C := by
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact hsupport hy
    have hxω : (baseReindex (F := F)).symm y ∈ omega C := (mem_omega_iff C _).mpr hyc
    rw [show KPContCotangentOverlapRationalBranches.q C ((baseReindex (F := F)).symm y) =
      C.toBase ⟨labeledA (placeEquiv F ζ hζ) ((baseReindex (F := F)).symm y), hxω⟩ from rfl]
    exact Set.mem_range_self _
  have hcoc (γ : Gamma C) (x : M F) (hx : x ∈ omega C)
      (v : EuclideanSpace ℂ (Fin (3 * d F))) :
      (cotangentCocycle C γ (baseReindex (F := F) x)) v =
        coefficientReindex
          (T (isotropyArrow C γ) x (omega_subset_larger C hx) (coefficientReindex.symm v)) := by
    have hsymm : (baseReindex (F := F)).symm (baseReindex (F := F) x) = x :=
      LinearIsometryEquiv.symm_apply_apply _ _
    have hmem : (baseReindex (F := F)).symm (baseReindex (F := F) x) ∈
        (isotropyChart C).omega := by
      rw [hsymm]
      exact omega_subset_larger C hx
    rw [KPContActualSectorChartEquivariantInputs.cotangentCocycle, dif_pos hmem]
    simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
    congr 1
    rw [T_apply' (isotropyArrow C γ) ((baseReindex (F := F)).symm (baseReindex (F := F) x)) hmem,
      T_apply' (isotropyArrow C γ) x (omega_subset_larger C hx), hsymm]
  have hfmem : f ∈ localCotangentTests C := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨fun y => coefficientReindex.symm (h (baseReindex y)), ?_, fun x => rfl⟩
      have hL : ContDiff ℝ (⊤ : ℕ∞)
          (fun v : EuclideanSpace ℂ (Fin (3 * d F)) => coefficientReindex.symm v) :=
        (LinearIsometryEquiv.contDiff coefficientReindex.symm).restrict_scalars ℝ
      exact hL.contDiffOn.comp
        (hsmooth.comp ((baseReindex (F := F)).contDiff.contDiffOn)
          (fun x hx => (mem_omega_iff C x).mp hx))
        (Set.mapsTo_univ _ _)
    · intro γ x hx
      have hX : baseReindex (F := F) x ∈ chart C := (mem_omega_iff C x).mp hx
      have he' : h (baseReindex (F := F) ((isotropyArrow C γ).psi x)) =
          cotangentCocycle C γ (baseReindex (F := F) x) (h (baseReindex (F := F) x)) := by
        have h1 := hequiv γ (baseReindex (F := F) x) hX
        rw [cotangentData_act, cotangentData_cocycle, action_eq C γ x] at h1
        exact h1
      show f ⟨(isotropyArrow C γ).psi x, isotropy_mem C γ x hx⟩ =
        T (isotropyArrow C γ) x (omega_subset_larger C hx) (f ⟨x, hx⟩)
      show coefficientReindex.symm (h (baseReindex (F := F) ((isotropyArrow C γ).psi x))) =
        T (isotropyArrow C γ) x (omega_subset_larger C hx)
          (coefficientReindex.symm (h (baseReindex (F := F) x)))
      rw [he', hcoc γ x hx, LinearIsometryEquiv.symm_apply_apply]
    · exact IsCompact.of_isClosed_subset (hKcompact.image (continuous_q C))
        isClosed_closure hsub
    · exact hsub.trans himage
  exact ⟨⟨f, hfmem⟩, fun x => by
    show coefficientReindex (coefficientReindex.symm (h (baseReindex x.val))) = h (baseReindex x.val)
    rw [LinearIsometryEquiv.apply_symm_apply]⟩

end DedekindZetaZeroFree.KPContActualCompactEquivariantDescent

end
