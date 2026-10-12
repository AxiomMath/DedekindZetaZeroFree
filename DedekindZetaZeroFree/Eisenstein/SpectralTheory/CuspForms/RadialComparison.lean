module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnds.CoframeNormNaturality
public import DedekindZetaZeroFree.Adeles.Quotients.CuspEnds.ParabolicOverlapRigidity
public import DedekindZetaZeroFree.Adeles.Quotients.CuspEnds.CompactHeightBounds
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.TestFriedrichsRealization

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCuspRadialFormComparison

open KPContSectorSmoothFramesSupport KPContActualSectorSmoothTestModules
open KPContActualSectorTestEmbeddings

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def d : ℝ := (Module.finrank ℚ F : ℝ) / 2

abbrev Cusp := KPMsFixedHaarDisintegration.CuspIndex (H.atlas U)

abbrev Stabilizer (c : Cusp F ζ hζ U R P H) :=
  KPCuspArithmetic.conjugatedStabilizer F
    (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
    (((H.atlas U).cuspAtlas c.1).cusp c.2)
    (((H.atlas U).cuspAtlas c.1).representative c.2)

abbrev Y_c (c : Cusp F ζ hζ U R P H) :=
  KPCuspCharts.CrossQuotient F (Stabilizer F ζ hζ U R P H c)

def nu_c (c : Cusp F ζ hζ U R P H) : Measure (Y_c F ζ hζ U R P H c) :=
  (H.disintegration U).componentWeight c.1 •
    (((H.atlas U).cuspAtlas c.1).geometry c.2).sectionMeasure

def endSet (c : Cusp F ζ hζ U R P H) (T : ℝ) : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative c.1) ''
    KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
      (((H.atlas U).cuspAtlas c.1).representative c.2) T

def endChart (c : Cusp F ζ hζ U R P H) (T : ℝ) :
    Y_c F ζ hζ U R P H c × Set.Ioi T → KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  fun z => KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative c.1)
    (KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
      (((H.atlas U).cuspAtlas c.1).cusp c.2)
      (((H.atlas U).cuspAtlas c.1).representative c.2) T
      ((((H.atlas U).cuspAtlas c.1).geometry c.2).highPresentation T z))

abbrev ActualLine (c : Cusp F ζ hζ U R P H) :=
  KPCuspGenuineMonodromy.OrbifoldLine F ζ hζ U ((H.atlas U).representative c.1)
    ((H.atlas U).line c.1).rho

def transverseLineRelation (c : Cusp F ζ hζ U R P H) :
    Setoid (KPCuspCharts.Cross F × Coefficient F ζ hζ U) :=
  Setoid.comap (fun z => (cuspPoint F ζ hζ U R P H c.1 c.2
      (z.1, ((H.atlas U).cuspAtlas c.1).threshold + 1), z.2))
    (KPCuspGenuineMonodromy.flatLineRelation F ζ hζ U
      ((H.atlas U).representative c.1) ((H.atlas U).line c.1).rho)

abbrev L_c (c : Cusp F ζ hζ U R P H) := Quotient (transverseLineRelation F ζ hζ U R P H c)

def endLineRelation (c : Cusp F ζ hζ U R P H) (T : ℝ) :
    Setoid ((KPCuspCharts.Cross F × Set.Ioi T) × Coefficient F ζ hζ U) :=
  Setoid.comap (fun z => (cuspPoint F ζ hζ U R P H c.1 c.2 (z.1.1, z.1.2.val), z.2))
    (KPCuspGenuineMonodromy.flatLineRelation F ζ hζ U
      ((H.atlas U).representative c.1) ((H.atlas U).line c.1).rho)

abbrev EndLine (c : Cusp F ζ hζ U R P H) (T : ℝ) :=
  Quotient (endLineRelation F ζ hζ U R P H c T)

def endLineToActual (c : Cusp F ζ hζ U R P H) (T : ℝ) :
    EndLine F ζ hζ U R P H c T → ActualLine F ζ hζ U R P H c :=
  Quotient.map (fun z => (cuspPoint F ζ hζ U R P H c.1 c.2 (z.1.1, z.1.2.val), z.2))
    (fun _ _ h => h)

 theorem smul_toArch_crossAction (c : Cusp F ζ hζ U R P H)
    (g : Stabilizer F ζ hζ U R P H c) (p : KPCuspCharts.Cross F) (t : ℝ) :
    (g : KPCuspArithmetic.PGL2 F) • KPCuspCharts.toArch F (p, t) =
      KPCuspCharts.toArch F
        ((((H.atlas U).cuspAtlas c.1).geometry c.2).crossAction g p, t) := by
  obtain ⟨A, hA, hA10⟩ := (((H.atlas U).cuspAtlas c.1).parabolic c.2).upper g g.2
  have hsm : (g : KPCuspArithmetic.PGL2 F) • KPCuspCharts.toArch F (p, t) =
      KPCuspSiegel.action F (g : KPCuspArithmetic.PGL2 F)
        (KPCuspCharts.toArch F (p, t)) := rfl
  rw [hsm, (((H.atlas U).cuspAtlas c.1).geometry c.2).actual_action g A hA hA10 (p, t),
    (((H.atlas U).cuspAtlas c.1).geometry c.2).crossAction_formula g A hA hA10]
  rfl

 theorem lineBase_wellDefined (c : Cusp F ζ hζ U R P H)
    (z z' : KPCuspCharts.Cross F × Coefficient F ζ hζ U)
    (h : transverseLineRelation F ζ hζ U R P H c z z') :
    Quotient.mk (KPCuspCharts.crossRelation F (Stabilizer F ζ hζ U R P H c)) z.1 =
      Quotient.mk (KPCuspCharts.crossRelation F (Stabilizer F ζ hζ U R P H c)) z'.1 := by
  obtain ⟨γ, hγ, -⟩ := h
  have hd : 0 < KPCuspLogShape.dimension F :=
    (((H.atlas U).cuspAtlas c.1).geometry c.2).positive_dimension
  let p : {q : KPCuspCharts.Coordinates F //
      ((H.atlas U).cuspAtlas c.1).threshold < q.2} :=
    ⟨(z.1, ((H.atlas U).cuspAtlas c.1).threshold + 1), by linarith⟩
  let p' : {q : KPCuspCharts.Coordinates F //
      ((H.atlas U).cuspAtlas c.1).threshold < q.2} :=
    ⟨(z'.1, ((H.atlas U).cuspAtlas c.1).threshold + 1), by linarith⟩
  have hγ' : (γ : KPCuspArithmetic.PGL2 F) •
        (((H.atlas U).cuspAtlas c.1).representative c.2 • KPCuspCharts.toArch F p.val) =
      ((H.atlas U).cuspAtlas c.1).representative c.2 • KPCuspCharts.toArch F p'.val := by
    have hh := hγ
    simp only [cuspPoint] at hh
    simpa using hh.symm
  have heq : KPFiniteCuspAtlas.endMap F
        (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
        (((H.atlas U).cuspAtlas c.1).cusp c.2)
        (((H.atlas U).cuspAtlas c.1).representative c.2)
        ((H.atlas U).cuspAtlas c.1).threshold (Quotient.mk _ p') =
      KPFiniteCuspAtlas.endMap F
        (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
        (((H.atlas U).cuspAtlas c.1).cusp c.2)
        (((H.atlas U).cuspAtlas c.1).representative c.2)
        ((H.atlas U).cuspAtlas c.1).threshold (Quotient.mk _ p) := by
    simp only [KPFiniteCuspAtlas.endMap, KPCuspSiegel.projection, Quotient.lift_mk]
    exact Quotient.sound (MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨γ, hγ'⟩))
  have hinj := (KPMsFixedHaar.RadialIntegrationSteps.endMap_embedding
    (A := H.atlas U) c ((H.atlas U).cuspAtlas c.1).threshold
    (le_of_eq ((H.atlas U).common_threshold c.1).symm)).injective heq
  have hrel : KPCuspCharts.highRelation F (Stabilizer F ζ hζ U R P H c)
      ((H.atlas U).cuspAtlas c.1).threshold p' p := Quotient.exact hinj
  have hmem : KPCuspCharts.toArch F p'.val ∈
      MulAction.orbit (Stabilizer F ζ hζ U R P H c) (KPCuspCharts.toArch F p.val) :=
    MulAction.orbitRel_apply.mp hrel
  obtain ⟨s, hs'⟩ := MulAction.mem_orbit_iff.mp hmem
  have hs2 : (s : KPCuspArithmetic.PGL2 F) • KPCuspCharts.toArch F
        (z.1, ((H.atlas U).cuspAtlas c.1).threshold + 1) =
      KPCuspCharts.toArch F (z'.1, ((H.atlas U).cuspAtlas c.1).threshold + 1) := by
    simpa only [Subgroup.smul_def, show p.val = (z.1, ((H.atlas U).cuspAtlas c.1).threshold + 1) from rfl,
      show p'.val = (z'.1, ((H.atlas U).cuspAtlas c.1).threshold + 1) from rfl] using hs'
  have hs1 : KPCuspCharts.toArch F (z'.1, 0) =
      (s : KPCuspArithmetic.PGL2 F) • KPCuspCharts.toArch F (z.1, 0) := by
    have hcross : z'.1 = (((H.atlas U).cuspAtlas c.1).geometry c.2).crossAction s z.1 := by
      have h1 : KPCuspCharts.toArch F (z'.1, ((H.atlas U).cuspAtlas c.1).threshold + 1) =
          KPCuspCharts.toArch F
            ((((H.atlas U).cuspAtlas c.1).geometry c.2).crossAction s z.1,
              ((H.atlas U).cuspAtlas c.1).threshold + 1) := by
        rw [← smul_toArch_crossAction F ζ hζ U R P H c s z.1
          (((H.atlas U).cuspAtlas c.1).threshold + 1)]
        simpa only [Subgroup.smul_def] using hs2.symm
      exact (Prod.ext_iff.mp ((KPCuspCharts.toArchHomeomorph F hd).injective h1)).1
    rw [hcross, smul_toArch_crossAction F ζ hζ U R P H c s z.1 0]
  exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr
    ⟨s⁻¹, by
      show (s⁻¹ : KPCuspArithmetic.PGL2 F) • KPCuspCharts.toArch F (z'.1, 0) =
        KPCuspCharts.toArch F (z.1, 0)
      rw [hs1, ← mul_smul, inv_mul_cancel, one_smul]⟩))

def lineBase (c : Cusp F ζ hζ U R P H) : L_c F ζ hζ U R P H c → Y_c F ζ hζ U R P H c :=
  Quotient.lift (fun z => Quotient.mk _ z.1) (lineBase_wellDefined F ζ hζ U R P H c)

def lineNormSq (c : Cusp F ζ hζ U R P H) (l : L_c F ζ hζ U R P H c) : ℝ :=
  ‖(Quotient.out l).2‖ ^ 2

def coefficient (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H)
    (p : KPCuspCharts.Cross F) (t : ℝ) : Coefficient F ζ hζ U :=
  cuspCoefficient F ζ hζ U R P H (scalarSections f) c.1 c.2 (p, t)

def radialDerivative (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H)
    (p : KPCuspCharts.Cross F) (t : ℝ) : ℂ :=
  deriv (fun s => (coefficient F ζ hζ U R P H f c p s : ℂ)) t

theorem radialDerivative_mem (f : S_U F ζ hζ U R P H)
    (c : Cusp F ζ hζ U R P H) (p : KPCuspCharts.Cross F) (t : ℝ) :
    radialDerivative F ζ hζ U R P H f c p t ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U := by
  rcases ((H.atlas U).line c.1).rank with h | h
  · rw [h, Submodule.mem_bot]
    unfold radialDerivative
    have hf : (fun s => (coefficient F ζ hζ U R P H f c p s : ℂ)) = fun _ => (0 : ℂ) := by
      funext s
      have hs : (coefficient F ζ hζ U R P H f c p s : ℂ) = 0 := by
        have hmem : (coefficient F ζ hζ U R P H f c p s : ℂ) ∈
            KPCuspGenuineMonodromy.scalarFiber F ζ hζ U :=
          (coefficient F ζ hζ U R P H f c p s).2
        rw [h] at hmem
        simpa using hmem
      simp [hs]
    rw [hf, deriv_const]
  · rw [h]; exact Submodule.mem_top

 theorem cuspPoint_transition (c : Cusp F ζ hζ U R P H)
    (σ : Stabilizer F ζ hζ U R P H c) (p : KPCuspCharts.Cross F) (t : ℝ) :
    cuspPoint F ζ hζ U R P H c.1 c.2
        ((((H.atlas U).cuspAtlas c.1).geometry c.2).crossAction σ p, t) =
      (KPCuspGenuineMonodromy.cuspInclusion F
        (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
        (((H.atlas U).cuspAtlas c.1).cusp c.2)
        (((H.atlas U).cuspAtlas c.1).representative c.2) σ) •
      cuspPoint F ζ hζ U R P H c.1 c.2 (p, t) := by
  simp only [cuspPoint, Subgroup.smul_def]
  rw [KPCuspGenuineMonodromy.cuspInclusion_formula,
    ← smul_toArch_crossAction F ζ hζ U R P H c σ p t]
  simp only [mul_smul, inv_smul_smul]

def v_c (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H) (t : ℝ) :
    Y_c F ζ hζ U R P H c → L_c F ζ hζ U R P H c :=
  Quotient.lift (fun p => Quotient.mk _ (p, coefficient F ζ hζ U R P H f c p t)) (by
    intro p p' h
    obtain ⟨σ, hσ⟩ := h
    have hd : 0 < KPCuspLogShape.dimension F :=
      (((H.atlas U).cuspAtlas c.1).geometry c.2).positive_dimension
    have hσ' : KPCuspCharts.toArch F (p', 0) =
        ((σ⁻¹ : Stabilizer F ζ hζ U R P H c) : KPCuspArithmetic.PGL2 F) •
          KPCuspCharts.toArch F (p, 0) := by
      have hcong := congrArg
        (fun y => ((σ⁻¹ : Stabilizer F ζ hζ U R P H c) : KPCuspArithmetic.PGL2 F) • y) hσ
      simpa [Subgroup.smul_def] using hcong
    have h1 : KPCuspCharts.toArch F (p', 0) = KPCuspCharts.toArch F
        ((((H.atlas U).cuspAtlas c.1).geometry c.2).crossAction σ⁻¹ p, 0) := by
      rw [hσ', smul_toArch_crossAction F ζ hζ U R P H c σ⁻¹ p 0]
    have hcp : p' = (((H.atlas U).cuspAtlas c.1).geometry c.2).crossAction σ⁻¹ p :=
      (Prod.ext_iff.mp ((KPCuspCharts.toArchHomeomorph F hd).injective h1)).1
    refine Quotient.sound ⟨KPCuspGenuineMonodromy.cuspInclusion F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
      (((H.atlas U).cuspAtlas c.1).cusp c.2)
      (((H.atlas U).cuspAtlas c.1).representative c.2) σ⁻¹, ?_, ?_⟩
    · dsimp only
      rw [hcp, cuspPoint_transition]
      simp only [Subgroup.smul_def]
    · have ht := (cuspCoefficient_transition F ζ hζ U R P H (scalarSections f)
        c.1 c.2 σ⁻¹ p t).1
      dsimp only
      show (coefficient F ζ hζ U R P H f c p' t : ℂ) =
        (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line c.1).rho _) : ℂ) *
          (coefficient F ζ hζ U R P H f c p t : ℂ)
      rw [hcp]
      simp only [coefficient]
      rw [ht]
      rfl)

def nabla_t (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H) (t : ℝ) :
    Y_c F ζ hζ U R P H c → L_c F ζ hζ U R P H c :=
  Quotient.lift (fun p => Quotient.mk _ (p,
    (⟨radialDerivative F ζ hζ U R P H f c p t,
      radialDerivative_mem F ζ hζ U R P H f c p t⟩ : Coefficient F ζ hζ U))) (by
    intro p p' h
    obtain ⟨σ, hσ⟩ := h
    have hd : 0 < KPCuspLogShape.dimension F :=
      (((H.atlas U).cuspAtlas c.1).geometry c.2).positive_dimension
    have hσ' : KPCuspCharts.toArch F (p', 0) =
        ((σ⁻¹ : Stabilizer F ζ hζ U R P H c) : KPCuspArithmetic.PGL2 F) •
          KPCuspCharts.toArch F (p, 0) := by
      have hcong := congrArg
        (fun y => ((σ⁻¹ : Stabilizer F ζ hζ U R P H c) : KPCuspArithmetic.PGL2 F) • y) hσ
      simpa [Subgroup.smul_def] using hcong
    have h1 : KPCuspCharts.toArch F (p', 0) = KPCuspCharts.toArch F
        ((((H.atlas U).cuspAtlas c.1).geometry c.2).crossAction σ⁻¹ p, 0) := by
      rw [hσ', smul_toArch_crossAction F ζ hζ U R P H c σ⁻¹ p 0]
    have hcp : p' = (((H.atlas U).cuspAtlas c.1).geometry c.2).crossAction σ⁻¹ p :=
      (Prod.ext_iff.mp ((KPCuspCharts.toArchHomeomorph F hd).injective h1)).1
    refine Quotient.sound ⟨KPCuspGenuineMonodromy.cuspInclusion F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
      (((H.atlas U).cuspAtlas c.1).cusp c.2)
      (((H.atlas U).cuspAtlas c.1).representative c.2) σ⁻¹, ?_, ?_⟩
    · dsimp only
      rw [hcp, cuspPoint_transition]
      simp only [Subgroup.smul_def]
    · dsimp only
      have hfun : (fun s => (coefficient F ζ hζ U R P H f c p' s : ℂ)) =
          fun s => (KPCuspGenuineMonodromy.chi F ζ hζ
              (((H.atlas U).line c.1).rho (KPCuspGenuineMonodromy.cuspInclusion F
                (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
                (((H.atlas U).cuspAtlas c.1).cusp c.2)
                (((H.atlas U).cuspAtlas c.1).representative c.2) σ⁻¹)) : ℂ) *
            (coefficient F ζ hζ U R P H f c p s : ℂ) := by
        funext s
        have ht := (cuspCoefficient_transition F ζ hζ U R P H (scalarSections f)
          c.1 c.2 σ⁻¹ p s).1
        rw [hcp]
        simp only [coefficient]
        rw [ht]
        rfl
      simp only [radialDerivative]
      rw [hfun, deriv_const_mul_field])

def scalarDensity (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H)
    (y : Y_c F ζ hζ U R P H c) (t : ℝ) : ℝ :=
  Real.exp (-2 * d F * t) * lineNormSq F ζ hζ U R P H c (v_c F ζ hζ U R P H f c t y)

def gradientDensity (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H)
    (y : Y_c F ζ hζ U R P H c) (t : ℝ) : ℝ :=
  Real.exp (-2 * d F * t) * lineNormSq F ζ hζ U R P H c (nabla_t F ζ hζ U R P H f c t y)

variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)

local notation "A" => KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization

abbrev Q_U := ClosedGradientSpace A

abbrev j_U : Q_U F ζ hζ U R P H μG hμG hR realization →L[ℂ]
    KPContSectorClosedLpSubspace.H F ζ hζ R U := closedGradientEmbedding A

abbrev closedGradient : Q_U F ζ hζ U R P H μG hμG hR realization →L[ℂ]
    KPContActualSectorCotangentL2.V F ζ hζ U R P H := closedGradientCoordinate A

def q_U (v : Q_U F ζ hζ U R P H μG hμG hR realization) : ℝ :=
  ‖closedGradient F ζ hζ U R P H μG hμG hR realization v‖ ^ 2

def coreLift (f : S_U F ζ hζ U R P H) : Q_U F ζ hζ U R P H μG hμG hR realization :=
  ⟨WithLp.toLp 2 (iota f,
    (A).closure (KPContActualSectorFriedrichsSynthesis.formTest
      F ζ hζ U R P H μG hμG hR realization f)), by
    exact (A).closure.mem_graph
      (KPContActualSectorFriedrichsSynthesis.formTest F ζ hζ U R P H μG hμG hR realization f)⟩

private theorem chi_norm_one (ε : rootsOfUnity 3 F) :
    ‖(KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)‖ = 1 := by
  apply IsOfFinOrder.norm_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨3, by decide, ?_⟩
  have hp : ε ^ 3 = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity 3 _).mp ε.property
  simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
    congrArg (fun x => (KPCuspGenuineMonodromy.chi F ζ hζ x : ℂ)) hp

private theorem transverse_norm_eq (c : Cusp F ζ hζ U R P H)
    (z z' : KPCuspCharts.Cross F × Coefficient F ζ hζ U)
    (h : transverseLineRelation F ζ hζ U R P H c z z') : ‖z'.2‖ = ‖z.2‖ := by
  obtain ⟨γ, -, h2⟩ := h
  have h2' : ((z'.2 : Coefficient F ζ hζ U) : ℂ) =
      (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line c.1).rho γ) : ℂ) *
        ((z.2 : Coefficient F ζ hζ U) : ℂ) := h2
  rw [show ‖z'.2‖ = ‖(z'.2 : ℂ)‖ from rfl, h2', norm_mul,
    chi_norm_one F ζ hζ (((H.atlas U).line c.1).rho γ), one_mul]
  rfl

private theorem hermitian_norm_proof (c : Cusp F ζ hζ U R P H)
    (p : KPCuspCharts.Cross F) (a : Coefficient F ζ hζ U) :
    lineNormSq F ζ hζ U R P H c (Quotient.mk _ (p,a)) = ‖a‖ ^ 2 := by
  unfold lineNormSq
  congr 1
  exact (transverse_norm_eq F ζ hζ U R P H c _ _
    (Quotient.mk_out (s := transverseLineRelation F ζ hζ U R P H c) (p, a))).symm

private theorem positive_dimension_proof : 0 < d F := by
  unfold d
  have : (0 : ℝ) < Module.finrank ℚ F := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  linarith

private theorem dimension_eq_proof (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    d F = (KPCuspLogShape.dimension F : ℝ) := by
  have h := KPArch.complex_places_of_primitive_twelfth_root F ζ hζ
  have hcast : ((Module.finrank ℚ F / 2 : ℕ) : ℝ) = (Module.finrank ℚ F : ℝ) / 2 := by
    have hrank : Module.finrank ℚ F = 2 * NumberField.InfinitePlace.nrComplexPlaces F := by
      have hn := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank F
      rw [h.1, zero_add] at hn
      exact hn.symm
    rw [hrank]
    have hd : 2 * NumberField.InfinitePlace.nrComplexPlaces F / 2 =
        NumberField.InfinitePlace.nrComplexPlaces F :=
      Nat.mul_div_right _ (by norm_num : 0 < 2)
    rw [hd, Nat.cast_mul]
    ring
  unfold d KPCuspLogShape.dimension
  rw [h.2.1, hcast]

open KPContCotangentActualOverlap

 def radialVector : M F := ∑ i : Fin (KPContCotangentActualOverlap.d F), HyperbolicChart.coordinateVector (KPContCotangentActualOverlap.d F) i 2
 def radialPoint (p : KPCuspCharts.Cross F) (t : ℝ) : M F :=
  labeledAInv (placeEquiv F ζ hζ) (KPCuspCharts.toArch F (p,t))

private theorem radialVector_apply (i : Fin (KPContCotangentActualOverlap.d F)) (k : Fin 3) :
  radialVector F (i,k) = if k=2 then 1 else 0 := by
  by_cases hk : k=2
  · subst k
    simp [radialVector, HyperbolicChart.coordinateVector]
  · simp [radialVector, HyperbolicChart.coordinateVector, hk]
private theorem radialPoint_affine (p : KPCuspCharts.Cross F) (t : ℝ) :
  radialPoint F ζ hζ p t = radialPoint F ζ hζ p 0 + t • radialVector F := by
  apply PiLp.ext
  rintro ⟨i,k⟩
  fin_cases k <;> simp [radialPoint, labeledAInv, CotangentLogCoframe.A,
    PiLp.add_apply, PiLp.smul_apply, KPCuspCharts.toArch, radialVector_apply, add_comm]
private theorem radialPoint_hasDeriv (p : KPCuspCharts.Cross F) (t : ℝ) :
  HasDerivAt (radialPoint F ζ hζ p) (radialVector F) t := by
  have h := (hasDerivAt_id t).smul_const (radialVector F)
  have h2 := h.const_add (radialPoint F ζ hζ p 0)
  simp only [one_smul] at h2
  convert h2 using 1
  funext s
  exact radialPoint_affine F ζ hζ p s
private theorem radial_deriv (g : M F → ℂ) (p : KPCuspCharts.Cross F) (t : ℝ)
    (hg : DifferentiableAt ℝ g (radialPoint F ζ hζ p t)) :
    deriv (fun s => g (radialPoint F ζ hζ p s)) t =
      ∑ i : Fin (KPContCotangentActualOverlap.d F),
        HyperbolicChart.differential (KPContCotangentActualOverlap.d F) g (radialPoint F ζ hζ p t) i 0 := by
  have h := hg.hasFDerivAt.comp_hasDerivAt t (radialPoint_hasDeriv F ζ hζ p t)
  change deriv (g ∘ radialPoint F ζ hζ p) t = _
  rw [h.deriv]
  simp only [radialVector, map_sum, HyperbolicChart.differential,
    Matrix.cons_val_zero, HyperbolicChart.coordinateDerivative]
private theorem radial_energy_le (g : M F → ℂ) (p : KPCuspCharts.Cross F) (t : ℝ)
    (hg : DifferentiableAt ℝ g (radialPoint F ζ hζ p t)) :
    ‖deriv (fun s => g (radialPoint F ζ hζ p s)) t‖^2 ≤
      (KPContCotangentActualOverlap.d F : ℝ) *
        ∑ i : Fin (KPContCotangentActualOverlap.d F), ∑ k : Fin 3,
          ‖HyperbolicChart.differential (KPContCotangentActualOverlap.d F) g (radialPoint F ζ hζ p t) i k‖^2 := by
  rw [radial_deriv F ζ hζ g p t hg]
  calc
    _ ≤ (∑ i : Fin (KPContCotangentActualOverlap.d F),
      ‖HyperbolicChart.differential (KPContCotangentActualOverlap.d F) g (radialPoint F ζ hζ p t) i 0‖)^2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (KPContCotangentActualOverlap.d F : ℝ) * ∑ i : Fin (KPContCotangentActualOverlap.d F),
      ‖HyperbolicChart.differential (KPContCotangentActualOverlap.d F) g (radialPoint F ζ hζ p t) i 0‖^2 := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i : Fin (KPContCotangentActualOverlap.d F) =>
          ‖HyperbolicChart.differential (KPContCotangentActualOverlap.d F) g (radialPoint F ζ hζ p t) i 0‖))
    _ ≤ _ := by
      gcongr with i
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun k : Fin 3 => ‖HyperbolicChart.differential (KPContCotangentActualOverlap.d F)
          g (radialPoint F ζ hζ p t) i k‖^2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ (0 : Fin 3))
 def cuspFlatScalar (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H) (x : M F) : ℂ :=
  ((scalarSections f) c.1).val
    (((H.atlas U).cuspAtlas c.1).representative c.2 • labeledA (placeEquiv F ζ hζ) x)
private theorem labeledA_labeledAInv (z : KPCuspGenuineMonodromy.SymmetricSpace F) :
    labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
  funext i
  simp [labeledA, labeledAInv]
private theorem cuspFlatScalar_radial (f : S_U F ζ hζ U R P H)
    (c : Cusp F ζ hζ U R P H) (p : KPCuspCharts.Cross F) (t : ℝ) :
    cuspFlatScalar F ζ hζ U R P H f c (radialPoint F ζ hζ p t) =
      (coefficient F ζ hζ U R P H f c p t : ℂ) := by
  simp only [cuspFlatScalar, radialPoint, labeledA_labeledAInv]
  rfl
private theorem cuspFlatScalar_smooth
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H) :
    ContDiff ℝ (⊤ : ℕ∞) (cuspFlatScalar F ζ hζ U R P H f c) := by
  have tests := kp_cont_actual_sector_smooth_test_modules F ζ hζ R.adelicHaar
    R.adelic_isHaar U R rfl P H realization
  have hact : ContDiff ℝ (⊤ : ℕ∞) (fun x : KPCuspGenuineMonodromy.SymmetricSpace F =>
      ((H.atlas U).cuspAtlas c.1).representative c.2 • x) := by
    obtain ⟨B,hB⟩ := Matrix.ProjGenLinGroup.mk_surjective
      (((H.atlas U).cuspAtlas c.1).representative c.2)
    rw [← hB]
    have he : (fun x : KPCuspGenuineMonodromy.SymmetricSpace F =>
        (Matrix.ProjGenLinGroup.mk B : KPCuspArithmetic.PGL2 F) • x) = KPCuspSiegel.glAction F B := by
      funext x
      exact KPCuspSiegel.action_mk F B x
    rw [he]
    exact (KPArch.productAction_contDiff (KPCuspLogShape.dimension F)
      (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding B)).of_le le_top
  have hlabel : ContDiff ℝ (⊤ : ℕ∞) (labeledA (placeEquiv F ζ hζ)) := by
    apply contDiff_pi.mpr
    intro i
    exact (contDiff_apply (𝕜 := ℝ) (E := KPArch.H3) (placeEquiv F ζ hζ |>.symm i)).comp
      (CotangentLogCoframe.A (KPContCotangentActualOverlap.d F)).contDiff
  exact ((tests.scalar_smooth f) c.1).comp (hact.comp hlabel)
private theorem actual_radial_height_sum
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H)
    (p : KPCuspCharts.Cross F) (t : ℝ) :
    radialDerivative F ζ hζ U R P H f c p t =
      ∑ i : Fin (KPContCotangentActualOverlap.d F), HyperbolicChart.differential
        (KPContCotangentActualOverlap.d F) (cuspFlatScalar F ζ hζ U R P H f c)
          (radialPoint F ζ hζ p t) i 0 := by
  have he : (fun s => cuspFlatScalar F ζ hζ U R P H f c (radialPoint F ζ hζ p s)) =
      fun s => (coefficient F ζ hζ U R P H f c p s : ℂ) := by
    funext s
    exact cuspFlatScalar_radial F ζ hζ U R P H f c p s
  rw [radialDerivative, ← he]
  exact radial_deriv F ζ hζ _ p t
    ((cuspFlatScalar_smooth F ζ hζ U R P H realization f c).differentiable (by simp)).differentiableAt
private theorem actual_radial_energy_le
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H)
    (p : KPCuspCharts.Cross F) (t : ℝ) :
    ‖radialDerivative F ζ hζ U R P H f c p t‖^2 ≤
      (KPContCotangentActualOverlap.d F : ℝ) *
      ∑ i : Fin (KPContCotangentActualOverlap.d F), ∑ k : Fin 3,
        ‖HyperbolicChart.differential (KPContCotangentActualOverlap.d F)
          (cuspFlatScalar F ζ hζ U R P H f c) (radialPoint F ζ hζ p t) i k‖^2 := by
  have he : (fun s => cuspFlatScalar F ζ hζ U R P H f c (radialPoint F ζ hζ p s)) =
      fun s => (coefficient F ζ hζ U R P H f c p s : ℂ) := by
    funext s
    exact cuspFlatScalar_radial F ζ hζ U R P H f c p s
  rw [radialDerivative, ← he]
  exact radial_energy_le F ζ hζ _ p t
    ((cuspFlatScalar_smooth F ζ hζ U R P H realization f c).differentiable (by simp)).differentiableAt
private theorem actual_radial_joint_continuous
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H) :
    Continuous (fun z : KPCuspCharts.Cross F × ℝ => radialDerivative F ζ hζ U R P H f c z.1 z.2) := by
  have hd := (cuspFlatScalar_smooth F ζ hζ U R P H realization f c).continuous_fderiv (by simp)
  have hp : Continuous (fun z : KPCuspCharts.Cross F × ℝ => radialPoint F ζ hζ z.1 z.2) := by
    unfold radialPoint labeledAInv
    apply Continuous.comp (CotangentLogCoframe.A (KPContCotangentActualOverlap.d F)).symm.continuous
    apply continuous_pi
    intro k
    exact (continuous_apply _).comp (KPCuspCharts.toArch_contDiff F).continuous
  have he : (fun z : KPCuspCharts.Cross F × ℝ => radialDerivative F ζ hζ U R P H f c z.1 z.2) =
      fun z => fderiv ℝ (cuspFlatScalar F ζ hζ U R P H f c)
        (radialPoint F ζ hζ z.1 z.2) (radialVector F) := by
    funext z
    rw [actual_radial_height_sum F ζ hζ U R P H realization f c z.1 z.2]
    simp only [radialVector, map_sum, HyperbolicChart.differential,
      Matrix.cons_val_zero, HyperbolicChart.coordinateDerivative]
  rw [he]
  exact (hd.comp hp).clm_apply continuous_const

theorem radialCoefficient_coframe_bound
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H)
    (p : KPCuspCharts.Cross F) (t : ℝ) :
    (d F)⁻¹ * ‖radialDerivative F ζ hζ U R P H f c p t‖ ^ 2 ≤
      ∑ i : Fin (KPContCotangentActualOverlap.d F), ∑ k : Fin 3,
        ‖HyperbolicChart.differential (KPContCotangentActualOverlap.d F)
          (fun x => ((scalarSections f) c.1).val
            (((H.atlas U).cuspAtlas c.1).representative c.2 •
              labeledA (placeEquiv F ζ hζ) x))
          (labeledAInv (placeEquiv F ζ hζ) (KPCuspCharts.toArch F (p, t))) i k‖ ^ 2 := by
  apply (inv_mul_le_iff₀ (positive_dimension_proof F)).mpr
  have hd : (KPContCotangentActualOverlap.d F : ℝ) = d F := by
    have hn : KPContCotangentActualOverlap.d F = KPCuspLogShape.dimension F := by
      simpa only [Fintype.card_fin] using Fintype.card_congr (placeEquiv F ζ hζ)
    rw [hn, dimension_eq_proof F ζ hζ]
  rw [← hd]
  exact actual_radial_energy_le F ζ hζ U R P H realization f c p t

theorem radialCoefficient_joint_continuous
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H) :
    Continuous (fun z : KPCuspCharts.Cross F × ℝ =>
      radialDerivative F ζ hζ U R P H f c z.1 z.2) := by
  exact actual_radial_joint_continuous F ζ hζ U R P H realization f c

private theorem radialQuotient_map (c : Cusp F ζ hζ U R P H) :
    IsQuotientMap (fun z : KPCuspCharts.Cross F × ℝ =>
      (Quotient.mk (KPCuspCharts.crossRelation F (Stabilizer F ζ hζ U R P H c)) z.1, z.2)) := by
  let G := ((H.atlas U).cuspAtlas c.1).geometry c.2
  have h := G.radialPresentation.symm.isQuotientMap.comp
    (isQuotientMap_quotient_mk' (s := KPCuspCharts.totalRelation F (Stabilizer F ζ hζ U R P H c)))
  have he : (fun z : KPCuspCharts.Cross F × ℝ =>
      (Quotient.mk (KPCuspCharts.crossRelation F (Stabilizer F ζ hζ U R P H c)) z.1, z.2)) =
      G.radialPresentation.symm ∘
        Quotient.mk (KPCuspCharts.totalRelation F (Stabilizer F ζ hζ U R P H c)) := by
    funext z
    apply G.radialPresentation.injective
    simp only [Function.comp_apply, G.radialPresentation_formula, Homeomorph.apply_symm_apply]
  rw [he]
  exact h
private theorem scalarDensity_mk (f : S_U F ζ hζ U R P H)
    (c : Cusp F ζ hζ U R P H) (p : KPCuspCharts.Cross F) (t : ℝ) :
    scalarDensity F ζ hζ U R P H f c (Quotient.mk _ p) t =
      Real.exp (-2 * d F * t) * ‖coefficient F ζ hζ U R P H f c p t‖ ^ 2 := by
  unfold scalarDensity v_c
  rw [Quotient.lift_mk]
  exact congrArg (fun x : ℝ => Real.exp (-2 * d F * t) * x)
    (hermitian_norm_proof F ζ hζ U R P H c p _)
private theorem gradientDensity_mk (f : S_U F ζ hζ U R P H)
    (c : Cusp F ζ hζ U R P H) (p : KPCuspCharts.Cross F) (t : ℝ) :
    gradientDensity F ζ hζ U R P H f c (Quotient.mk _ p) t =
      Real.exp (-2 * d F * t) * ‖radialDerivative F ζ hζ U R P H f c p t‖ ^ 2 := by
  unfold gradientDensity nabla_t
  rw [Quotient.lift_mk]
  exact congrArg (fun x : ℝ => Real.exp (-2 * d F * t) * x)
    (hermitian_norm_proof F ζ hζ U R P H c p _)

private theorem scalarDensity_joint_continuous
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H) :
    Continuous (fun z : Y_c F ζ hζ U R P H c × ℝ =>
      scalarDensity F ζ hζ U R P H f c z.1 z.2) := by
  apply (radialQuotient_map F ζ hζ U R P H c).continuous_iff.mpr
  have tests := kp_cont_actual_sector_smooth_test_modules F ζ hζ R.adelicHaar
    R.adelic_isHaar U R rfl P H realization
  have hc := (cuspCoefficient_smooth F ζ hζ U R P H (scalarSections f)
    (tests.scalar_smooth f) c.1 c.2).continuous
  have he : ((fun z : Y_c F ζ hζ U R P H c × ℝ =>
      scalarDensity F ζ hζ U R P H f c z.1 z.2) ∘
        (fun z : KPCuspCharts.Cross F × ℝ => (Quotient.mk _ z.1, z.2))) =
      fun z : KPCuspCharts.Cross F × ℝ =>
        Real.exp (-2 * d F * z.2) * ‖coefficient F ζ hζ U R P H f c z.1 z.2‖ ^ 2 := by
    funext z
    exact scalarDensity_mk F ζ hζ U R P H f c z.1 z.2
  rw [he]
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).mul (hc.norm.pow 2)

private theorem gradientDensity_joint_continuous
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H) :
    Continuous (fun z : Y_c F ζ hζ U R P H c × ℝ =>
      gradientDensity F ζ hζ U R P H f c z.1 z.2) := by
  apply (radialQuotient_map F ζ hζ U R P H c).continuous_iff.mpr
  have he : ((fun z : Y_c F ζ hζ U R P H c × ℝ =>
      gradientDensity F ζ hζ U R P H f c z.1 z.2) ∘
        (fun z : KPCuspCharts.Cross F × ℝ => (Quotient.mk _ z.1, z.2))) =
      fun z : KPCuspCharts.Cross F × ℝ =>
        Real.exp (-2 * d F * z.2) * ‖radialDerivative F ζ hζ U R P H f c z.1 z.2‖ ^ 2 := by
    funext z
    exact gradientDensity_mk F ζ hζ U R P H f c z.1 z.2
  rw [he]
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).mul
    ((radialCoefficient_joint_continuous F ζ hζ U R P H realization f c).norm.pow 2)

private theorem compact_transverse_proof (c : Cusp F ζ hζ U R P H) :
    CompactSpace (Y_c F ζ hζ U R P H c) :=
  (((H.atlas U).cuspAtlas c.1).geometry c.2).compact_cross

private theorem finite_transverse_proof (c : Cusp F ζ hζ U R P H) :
    IsFiniteMeasure (nu_c F ζ hζ U R P H c) := by
  unfold nu_c
  refine ⟨?_⟩
  rw [Measure.smul_apply]
  refine ENNReal.mul_lt_top ((H.disintegration U).finite_componentWeight c.1) ?_
  exact (((H.atlas U).cuspAtlas c.1).geometry c.2).finite_sectionMeasure.measure_univ_lt_top

private theorem positive_transverse_proof (c : Cusp F ζ hζ U R P H) :
    0 < nu_c F ζ hζ U R P H c Set.univ := by
  unfold nu_c
  rw [Measure.smul_apply]
  refine ENNReal.mul_pos ?_ ?_
  · exact ne_of_gt ((H.disintegration U).positive_componentWeight c.1)
  · exact (((H.atlas U).cuspAtlas c.1).geometry c.2).positive_sectionMeasure

private theorem section_base_proof (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H)
    (t : ℝ) (y : Y_c F ζ hζ U R P H c) :
    lineBase F ζ hζ U R P H c (v_c F ζ hζ U R P H f c t y) = y ∧
    lineBase F ζ hζ U R P H c (nabla_t F ζ hζ U R P H f c t y) = y := by
  constructor <;> induction y using Quotient.inductionOn with
  | h p => rfl

private theorem core_inclusion_proof (f : S_U F ζ hζ U R P H) :
    j_U F ζ hζ U R P H μG hμG hR realization
      (coreLift F ζ hζ U R P H μG hμG hR realization f) = iota f := by
  simp [j_U, coreLift, closedGradientEmbedding]

private theorem core_energy_proof (f : S_U F ζ hζ U R P H) :
    q_U F ζ hζ U R P H μG hμG hR realization
      (coreLift F ζ hζ U R P H μG hμG hR realization f) =
    KPContActualSectorFriedrichsSynthesis.energy F ζ hζ U R P H μG hμG hR realization
      (KPContActualSectorFriedrichsSynthesis.formTest F ζ hζ U R P H μG hμG hR realization f) := by
  simp [q_U, coreLift, closedGradient, closedGradientCoordinate,
    KPContActualSectorFriedrichsSynthesis.energy, closedGradientEnergy]

private theorem transition_coefficient (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H)
    (g : Stabilizer F ζ hζ U R P H c) (p : KPCuspCharts.Cross F) (t : ℝ) :
    coefficient F ζ hζ U R P H f c
        ((((H.atlas U).cuspAtlas c.1).geometry c.2).crossAction g p) t =
      phaseTransport F ζ hζ U (((H.atlas U).line c.1).rho
        (KPCuspGenuineMonodromy.cuspInclusion F
          (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
          (((H.atlas U).cuspAtlas c.1).cusp c.2)
          (((H.atlas U).cuspAtlas c.1).representative c.2) g))
        (coefficient F ζ hζ U R P H f c p t) :=
  (cuspCoefficient_transition F ζ hζ U R P H (scalarSections f) c.1 c.2 g p t).1

private theorem transition_radialDerivative (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H)
    (g : Stabilizer F ζ hζ U R P H c) (p : KPCuspCharts.Cross F) (t : ℝ) :
    radialDerivative F ζ hζ U R P H f c
        ((((H.atlas U).cuspAtlas c.1).geometry c.2).crossAction g p) t =
      (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line c.1).rho
        (KPCuspGenuineMonodromy.cuspInclusion F
          (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
          (((H.atlas U).cuspAtlas c.1).cusp c.2)
          (((H.atlas U).cuspAtlas c.1).representative c.2) g)) : ℂ) *
        radialDerivative F ζ hζ U R P H f c p t := by
  have hfun : (fun s => (coefficient F ζ hζ U R P H f c
        ((((H.atlas U).cuspAtlas c.1).geometry c.2).crossAction g p) s : ℂ)) =
      fun s => (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line c.1).rho
          (KPCuspGenuineMonodromy.cuspInclusion F
            (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
            (((H.atlas U).cuspAtlas c.1).cusp c.2)
            (((H.atlas U).cuspAtlas c.1).representative c.2) g)) : ℂ) *
        (coefficient F ζ hζ U R P H f c p s : ℂ) := by
    funext s
    rw [transition_coefficient F ζ hζ U R P H f c g p s]
    rfl
  simp only [radialDerivative]
  rw [hfun, deriv_const_mul_field]

private theorem componentMap_isEmbedding (c : Cusp F ζ hζ U R P H) :
    Topology.IsEmbedding
      (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative c.1)) := by
  have h1 : KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative c.1) =
      (H.atlas U).components ∘ (Sigma.mk c.1) := by
    funext x
    exact ((H.atlas U).components_formula c.1 x).symm
  rw [h1]
  exact (H.atlas U).components.isEmbedding.comp Topology.IsEmbedding.sigmaMk

private theorem base_embedding_proof (c : Cusp F ζ hζ U R P H) (T : ℝ)
    (hT : ((H.atlas U).cuspAtlas c.1).threshold < T) :
    Topology.IsEmbedding (endChart F ζ hζ U R P H c T) ∧
    Set.range (endChart F ζ hζ U R P H c T) = endSet F ζ hζ U R P H c T := by
  have hd : 0 < KPCuspLogShape.dimension F :=
    (((H.atlas U).cuspAtlas c.1).geometry c.2).positive_dimension
  have hth : (H.atlas U).threshold ≤ T := by
    rw [← (H.atlas U).common_threshold c.1]
    exact le_of_lt hT
  have hemb : Topology.IsEmbedding (KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
      (((H.atlas U).cuspAtlas c.1).cusp c.2)
      (((H.atlas U).cuspAtlas c.1).representative c.2) T) :=
    (KPMsFixedHaar.RadialIntegrationSteps.endMap_embedding (H.atlas U) c T hth)
  let G := ((H.atlas U).cuspAtlas c.1).geometry c.2
  have hpres : Topology.IsEmbedding (G.highPresentation T) :=
    (G.highPresentation T).isEmbedding
  have hfac : endChart F ζ hζ U R P H c T =
      KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative c.1) ∘
        (KPFiniteCuspAtlas.endMap F
          (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
          (((H.atlas U).cuspAtlas c.1).cusp c.2)
          (((H.atlas U).cuspAtlas c.1).representative c.2) T ∘
          (((H.atlas U).cuspAtlas c.1).geometry c.2).highPresentation T) := by
    funext z
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfac]
    exact (componentMap_isEmbedding F ζ hζ U R P H c).comp (hemb.comp hpres)
  · rw [hfac, Set.range_comp, Set.range_comp,
      Set.range_eq_univ.mpr (Homeomorph.surjective _), Set.image_univ]
    rw [KPFiniteCuspAtlas.endMap_range F hd]
    rfl

private theorem fixed_haar_proof (c : Cusp F ζ hζ U R P H) (T : ℝ)
    (hT : ((H.atlas U).cuspAtlas c.1).threshold < T) :
    Measure.map (endChart F ζ hζ U R P H c T)
      ((nu_c F ζ hζ U R P H c).prod
        (Measure.comap (Subtype.val : Set.Ioi T → ℝ)
          (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)))) =
      (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict
        (endSet F ζ hζ U R P H c T) := by
  let At := H.atlas U
  let Gc := ((At.cuspAtlas c.1).geometry c.2)
  letI : T2Space (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
    CoreChartLocalizers.quotient_hausdorff F ζ hζ _ U At
  letI : SecondCountableTopology (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
    CoreChartLocalizers.chart_quotient_secondCountable F ζ hζ _ U At
  have hemb : Topology.IsEmbedding (fun x =>
      KPFiniteCuspAtlas.componentMap F ζ hζ U (At.representative c.1)
        (KPFiniteCuspAtlas.endMap F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (At.representative c.1))
          ((At.cuspAtlas c.1).cusp c.2) ((At.cuspAtlas c.1).representative c.2) T x)) := by
    exact (componentMap_isEmbedding F ζ hζ U R P H c).comp
      (KPMsFixedHaar.RadialIntegrationSteps.endMap_embedding At c T (by
        rw [← At.common_threshold c.1]; exact hT.le))
  letI : T0Space (KPCuspCharts.HighQuotient F (Stabilizer F ζ hζ U R P H c) T) := hemb.t0Space
  letI : SecondCountableTopology (KPCuspCharts.HighQuotient F (Stabilizer F ζ hζ U R P H c) T) :=
    hemb.secondCountableTopology
  letI : PolishSpace {p : KPCuspCharts.Coordinates F // T < p.2} :=
    (isOpen_lt continuous_const continuous_snd).polishSpace
  letI : BorelSpace (KPCuspCharts.HighQuotient F (Stabilizer F ζ hζ U R P H c) T) := inferInstance
  let ν := KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)
  have hfinite : IsFiniteMeasure (Measure.comap (Subtype.val : Set.Ioi T → ℝ) ν) := by
    refine ⟨?_⟩
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioi).comap_apply,
      Set.image_univ, Subtype.range_coe]
    unfold ν KPCuspCharts.radialMeasure
    rw [withDensity_apply _ measurableSet_Ioi]
    have hd : (0 : ℝ) < KPCuspLogShape.dimension F := by
      exact_mod_cast Gc.positive_dimension
    have hi := integrableOn_exp_mul_Ioi (a := -2 * (KPCuspLogShape.dimension F : ℝ))
      (by linarith) T
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      (fun t => (Real.exp_pos _).le))).mp hi.hasFiniteIntegral
  letI := hfinite
  let D := H.disintegration U
  let comp := KPFiniteCuspAtlas.componentMap F ζ hζ U (At.representative c.1)
  let E := KPFiniteCuspAtlas.endSet F
    (KPCuspGenuineMonodromy.Component F ζ hζ U (At.representative c.1))
    ((At.cuspAtlas c.1).representative c.2) T
  have hcomp : Continuous comp := by
    have he : comp = At.components ∘ Sigma.mk c.1 := by
      funext x
      exact (At.components_formula c.1 x).symm
    rw [he]
    exact At.components.continuous.comp continuous_sigmaMk
  have hcompOpen : IsOpenMap comp := by
    have he : comp = At.components ∘ Sigma.mk c.1 := by
      funext x
      exact (At.components_formula c.1 x).symm
    rw [he]
    exact At.components.isOpenMap.comp isOpenMap_sigmaMk
  have hE : MeasurableSet (comp '' E) :=
    (hcompOpen _ (KPFiniteAdelicCuspEnds.component_open_end F _ _ T)).measurableSet
  have hpre : comp ⁻¹' (comp '' E) = E :=
    Set.preimage_image_eq _ (componentMap_isEmbedding F ζ hζ U R P H c).injective
  have hth : At.threshold ≤ T := by
    rw [← At.common_threshold c.1]
    exact hT.le
  have hv := KPMsFixedHaar.RadialIntegrationSteps.end_volume_at_cutoff At c T hth
  have hsub : comp '' E ⊆ Set.range comp := Set.image_subset_range _ _
  have hres : ((KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict
      (Set.range comp)).restrict (comp '' E) =
      (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict (comp '' E) := by
    rw [Measure.restrict_restrict hE, Set.inter_eq_left.mpr hsub]
  change Measure.map (endChart F ζ hζ U R P H c T)
    ((nu_c F ζ hζ U R P H c).prod
      (Measure.comap (Subtype.val : Set.Ioi T → ℝ)
        (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)))) =
    (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict (comp '' E)
  rw [← hres, D.component_measure c.1, Measure.restrict_smul,
    Measure.restrict_map hcomp.measurable hE, hpre, ← hv]
  unfold nu_c endChart
  have hend : Measurable (KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (At.representative c.1))
      ((At.cuspAtlas c.1).cusp c.2) ((At.cuspAtlas c.1).representative c.2) T) := by
    apply measurable_from_quotient.mpr
    exact measurable_quotient_mk''.comp
      ((KPCuspSiegel.continuous_action F _).measurable.comp
        ((KPCuspCharts.toArchHomeomorph F Gc.positive_dimension).continuous.measurable.comp
          measurable_subtype_coe))
  have hpres := (Gc.highPresentation T).continuous.measurable
  have hwhole := (hcomp.measurable.comp hend).comp hpres
  rw [Measure.prod_smul_left]
  have hwh : AEMeasurable (endChart F ζ hζ U R P H c T)
      (Gc.sectionMeasure.prod (Measure.comap (Subtype.val : Set.Ioi T → ℝ) ν)) := hwhole.aemeasurable
  change Measure.map (endChart F ζ hζ U R P H c T)
    (D.componentWeight c.1 • Gc.sectionMeasure.prod (Measure.comap (Subtype.val : Set.Ioi T → ℝ) ν)) = _
  rw [Measure.map_smul _ hwh]
  congr 1
  rw [Measure.map_map hcomp.measurable hend,
    Measure.map_map (hcomp.measurable.comp hend) hpres]
  rfl

private theorem radial_tail_uniform_support
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (c : Cusp F ζ hζ U R P H) (T : ℝ)
    (hT : ((H.atlas U).cuspAtlas c.1).threshold < T)
    (f : S_U F ζ hζ U R P H)
    (hsupp : scalarSupport f.val ⊆ endSet F ζ hζ U R P H c T) :
    ∃ a b : ℝ, T < a ∧ ∀ (p : KPCuspCharts.Cross F) (t : ℝ),
      T < t → (t < a ∨ b < t) →
        (coefficient F ζ hζ U R P H f c p t : ℂ) = 0 ∧
        radialDerivative F ζ hζ U R P H f c p t = 0 := by
  have tests := kp_cont_actual_sector_smooth_test_modules F ζ hζ R.adelicHaar
    R.adelic_isHaar U R rfl P H realization
  have hSupport := tests.scalar_support f
  have hCompact : IsCompact (tsupport (sectionNorm F ζ hζ U R P H (scalarSections f))) := by
    rw [← hSupport]
    exact f.property.2.2
  have hEmb := base_embedding_proof F ζ hζ U R P H c T hT
  have hContained : tsupport (sectionNorm F ζ hζ U R P H (scalarSections f)) ⊆
      Set.range (endChart F ζ hζ U R P H c T) := by
    rw [← hSupport, hEmb.2]
    exact hsupp
  obtain ⟨a, b, ha, hab⟩ := KPRadialTail.compact_embedding_height_bounds T
    (endChart F ζ hζ U R P H c T) hEmb.1 _ hCompact hContained
  have hpoint : ∀ (p : KPCuspCharts.Cross F) (t : ℝ) (ht : T < t),
      endChart F ζ hζ U R P H c T (Quotient.mk _ p, (⟨t, ht⟩ : Set.Ioi T)) =
        (H.atlas U).components ⟨c.1,
          Quotient.mk _ (cuspPoint F ζ hζ U R P H c.1 c.2 (p, t))⟩ := by
    intro p t ht
    unfold endChart
    rw [(((H.atlas U).cuspAtlas c.1).geometry c.2).highPresentation_formula]
    rw [(H.atlas U).components_formula]
    rfl
  have hzero : ∀ (p : KPCuspCharts.Cross F) (t : ℝ),
      T < t → (t < a ∨ b < t) → (coefficient F ζ hζ U R P H f c p t : ℂ) = 0 := by
    intro p t ht hout
    by_contra hne
    have hmem : endChart F ζ hζ U R P H c T (Quotient.mk _ p, (⟨t, ht⟩ : Set.Ioi T)) ∈
        tsupport (sectionNorm F ζ hζ U R P H (scalarSections f)) := by
      apply subset_tsupport
      change sectionNorm F ζ hζ U R P H (scalarSections f) _ ≠ 0
      rw [hpoint p t ht, sectionNorm_component]
      exact norm_ne_zero_iff.mpr hne
    have hz := hab _ hmem
    rcases hout with hout | hout <;> linarith [hz.1, hz.2]
  refine ⟨a, b, ha, fun p t ht hout => ⟨hzero p t ht hout, ?_⟩⟩
  have hopen : IsOpen (Set.Ioi T ∩ (Set.Iio a ∪ Set.Ioi b)) :=
    isOpen_Ioi.inter (isOpen_Iio.union isOpen_Ioi)
  have he : (fun s => (coefficient F ζ hζ U R P H f c p s : ℂ)) =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds (show t ∈ Set.Ioi T ∩ (Set.Iio a ∪ Set.Ioi b) from ⟨ht, hout⟩)] with s hs
    exact hzero p s hs.1 hs.2
  exact he.deriv_eq.trans (deriv_const t (0 : ℂ))

section CompactTailIntegrability
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]
  (ν : Measure Y) [IsFiniteMeasure ν]
private theorem compact_tail_zeroExtension
    (f : Y × ℝ → ℝ) (hf : Continuous f) (T a b : ℝ) (ha : T < a)
    (hz : ∀ y t, T < t → (t < a ∨ b < t) → f (y,t) = 0) :
    Continuous (fun z : Y × ℝ => if T < z.2 then f z else 0) ∧
      HasCompactSupport (fun z : Y × ℝ => if T < z.2 then f z else 0) := by
  let g : Y × ℝ → ℝ := fun z => if T < z.2 then f z else 0
  have hzero : ∀ z : Y × ℝ, z.2 < a → g z = 0 := by
    intro z hza
    by_cases ht : T < z.2
    · simp only [g, if_pos ht]
      exact hz z.1 z.2 ht (Or.inl hza)
    · simp [g, ht]
  refine ⟨?_, ?_⟩
  · apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hza : z.2 < a
    · have he : g =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [(isOpen_Iio.preimage continuous_snd).mem_nhds hza] with w hw
        exact hzero w hw
      exact continuousAt_const.congr_of_eventuallyEq he
    · have ht : T < z.2 := lt_of_lt_of_le ha (le_of_not_gt hza)
      have he : g =ᶠ[𝓝 z] f := by
        filter_upwards [(isOpen_Ioi.preimage continuous_snd).mem_nhds ht] with w hw
        exact if_pos (show T < w.2 from hw)
      exact hf.continuousAt.congr_of_eventuallyEq he
  · apply HasCompactSupport.intro' (K := Set.univ ×ˢ Set.Icc a b)
      (isCompact_univ.prod isCompact_Icc) (isClosed_univ.prod isClosed_Icc)
    intro z hnot
    have hout : z.2 < a ∨ b < z.2 := by
      simpa only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_Icc,
        not_and_or, not_le] using hnot
    by_cases ht : T < z.2
    · simp only [if_pos ht]
      exact hz z.1 z.2 ht hout
    · simp [ht]

private theorem compact_tail_integrable
    (f : Y × ℝ → ℝ) (hf : Continuous f) (T a b : ℝ) (ha : T < a)
    (hz : ∀ y t, T < t → (t < a ∨ b < t) → f (y,t) = 0) :
    (∀ y, IntegrableOn (fun t => f (y,t)) (Set.Ioi T) volume) ∧
      Integrable f (ν.prod (volume.restrict (Set.Ioi T))) := by
  have hg := compact_tail_zeroExtension f hf T a b ha hz
  have hgi := hg.1.integrable_of_hasCompactSupport (μ := ν.prod volume) hg.2
  have he : (fun z : Y × ℝ => if T < z.2 then f z else 0) =
      (Set.univ ×ˢ Set.Ioi T).indicator f := by
    funext z
    simp [Set.indicator, Set.mem_prod]
  rw [he, integrable_indicator_iff (MeasurableSet.univ.prod measurableSet_Ioi)] at hgi
  have hprod : Integrable f (ν.prod (volume.restrict (Set.Ioi T))) := by
    simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] using hgi
  refine ⟨fun y => ?_, hprod⟩
  have hfy : Continuous (fun t : ℝ => f (y,t)) := hf.comp (continuous_const.prodMk continuous_id)
  have hzy : ∀ (_ : Unit) t, T < t → (t < a ∨ b < t) → (fun z : Unit × ℝ => f (y,z.2)) ((),t) = 0 := by
    intro u t ht hout
    exact hz y t ht hout
  have hg' := compact_tail_zeroExtension (fun z : Unit × ℝ => f (y,z.2))
    (hfy.comp continuous_snd) T a b ha hzy
  have hycont := hg'.1.comp ((show Continuous (fun _ : ℝ => ()) from continuous_const).prodMk continuous_id)
  have hycompact : HasCompactSupport (fun t : ℝ => if T < t then f (y,t) else 0) := by
    apply HasCompactSupport.intro' (K := Set.Icc a b) isCompact_Icc isClosed_Icc
    intro t hnot
    have hout : t < a ∨ b < t := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hnot
    by_cases ht : T < t
    · simp [ht, hz y t ht hout]
    · simp [ht]
  have hi := hycont.integrable_of_hasCompactSupport (μ := volume) hycompact
  have he' : (fun t : ℝ => if T < t then f (y,t) else 0) =
      (Set.Ioi T).indicator (fun t => f (y,t)) := by
    funext t
    rfl
  change Integrable (fun t : ℝ => if T < t then f (y,t) else 0) volume at hi
  rwa [he', integrable_indicator_iff measurableSet_Ioi] at hi

end CompactTailIntegrability

theorem radialDensities_integrable
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (c : Cusp F ζ hζ U R P H) (T : ℝ)
    (hT : ((H.atlas U).cuspAtlas c.1).threshold < T)
    (f : S_U F ζ hζ U R P H)
    (hsupp : scalarSupport f.val ⊆ endSet F ζ hζ U R P H c T) :
    (∀ y, IntegrableOn (scalarDensity F ζ hζ U R P H f c y) (Set.Ioi T) volume ∧
      IntegrableOn (gradientDensity F ζ hζ U R P H f c y) (Set.Ioi T) volume) ∧
    Integrable (fun z : Y_c F ζ hζ U R P H c × ℝ =>
      scalarDensity F ζ hζ U R P H f c z.1 z.2)
      ((nu_c F ζ hζ U R P H c).prod (volume.restrict (Set.Ioi T))) ∧
    Integrable (fun z : Y_c F ζ hζ U R P H c × ℝ =>
      gradientDensity F ζ hζ U R P H f c z.1 z.2)
      ((nu_c F ζ hζ U R P H c).prod (volume.restrict (Set.Ioi T))) := by
  letI := compact_transverse_proof F ζ hζ U R P H c
  letI := finite_transverse_proof F ζ hζ U R P H c
  obtain ⟨a, b, ha, hz⟩ := radial_tail_uniform_support F ζ hζ U R P H realization c T hT f hsupp
  have hzero : ∀ (y : Y_c F ζ hζ U R P H c) (t : ℝ),
      T < t → (t < a ∨ b < t) →
      scalarDensity F ζ hζ U R P H f c y t = 0 ∧
      gradientDensity F ζ hζ U R P H f c y t = 0 := by
    intro y t ht hout
    induction y using Quotient.inductionOn with
    | h p =>
      obtain ⟨hc, hd⟩ := hz p t ht hout
      rw [scalarDensity_mk, gradientDensity_mk]
      have hc' : ‖coefficient F ζ hζ U R P H f c p t‖ = 0 := by
        change ‖(coefficient F ζ hζ U R P H f c p t : ℂ)‖ = 0
        rw [hc, norm_zero]
      simp [hc', hd]
  have hs := compact_tail_integrable (nu_c F ζ hζ U R P H c)
    (fun z : Y_c F ζ hζ U R P H c × ℝ => scalarDensity F ζ hζ U R P H f c z.1 z.2)
    (scalarDensity_joint_continuous F ζ hζ U R P H realization f c) T a b ha
    (fun y t ht hout => (hzero y t ht hout).1)
  have hg := compact_tail_integrable (nu_c F ζ hζ U R P H c)
    (fun z : Y_c F ζ hζ U R P H c × ℝ => gradientDensity F ζ hζ U R P H f c z.1 z.2)
    (gradientDensity_joint_continuous F ζ hζ U R P H realization f c) T a b ha
    (fun y t ht hout => (hzero y t ht hout).2)
  exact ⟨fun y => ⟨hs.1 y, hg.1 y⟩, hs.2, hg.2⟩

private theorem iota_norm_integral (f : S_U F ζ hζ U R P H) :
    ‖iota f‖ ^ 2 = ∫ b, sectionNorm F ζ hζ U R P H (scalarSections f) b ^ 2
      ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U := by
  have hsmooth : IsSmoothSections F ζ hζ U R P H (scalarSections f) :=
    (Classical.choose_spec (scalar_gluing f)).1.1
  have hcont : Continuous (scalarCovered f).val :=
    (KPContSectorLineL2Isometry.continuous_iff F ζ hζ U R P H (scalarSections f)).mp
      (fun i => (hsmooth i).continuous)
  have hn := kp_cont_sector_fixed_line_norm_integrals F ζ hζ U R P H (scalarCovered f)
    hcont.measurable
  have he : ‖iota f‖ ^ 2 =
      (∫⁻ b, ENNReal.ofReal (sectionNorm F ζ hζ U R P H (scalarSections f) b ^ 2)
        ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).toReal := by
    have h := hn.lp_norm (scalar_memLp f)
    change ‖(scalar_memLp f).toLp (scalarCovered f).val‖ ^ 2 = _
    rw [h]
    congr 2
    funext b
    simp only [KPContSectorFixedLineNormIntegrals.lineNorm, S_scalarCovered]
  rw [he]
  symm
  apply integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  have hm : Measurable (fun b => ENNReal.ofReal (sectionNorm F ζ hζ U R P H (scalarSections f) b ^ 2)) := by
    have h := hn.borel
    change Measurable (fun b => ENNReal.ofReal
      (sectionNorm F ζ hζ U R P H (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H (scalarCovered f)) b ^ 2)) at h
    rw [S_scalarCovered] at h
    exact h
  have hr : (fun b => sectionNorm F ζ hζ U R P H (scalarSections f) b ^ 2) =
      fun b => (ENNReal.ofReal (sectionNorm F ζ hζ U R P H (scalarSections f) b ^ 2)).toReal := by
    funext b
    rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [hr]
  exact hm.ennreal_toReal.aestronglyMeasurable

theorem scalar_radial_norm
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (c : Cusp F ζ hζ U R P H) (T : ℝ)
    (hT : ((H.atlas U).cuspAtlas c.1).threshold < T)
    (f : S_U F ζ hζ U R P H)
    (hsupp : scalarSupport f.val ⊆ endSet F ζ hζ U R P H c T) :
    ‖iota f‖ ^ 2 = ∫ y, ∫ t in Set.Ioi T,
      scalarDensity F ζ hζ U R P H f c y t ∂volume ∂nu_c F ζ hζ U R P H c := by
  let N := fun b => sectionNorm F ζ hζ U R P H (scalarSections f) b ^ 2
  let L := fun b => ENNReal.ofReal (N b)
  have hsmooth : IsSmoothSections F ζ hζ U R P H (scalarSections f) :=
    (Classical.choose_spec (scalar_gluing f)).1.1
  have hcont : Continuous (scalarCovered f).val :=
    (KPContSectorLineL2Isometry.continuous_iff F ζ hζ U R P H (scalarSections f)).mp
      (fun i => (hsmooth i).continuous)
  have hnorm := kp_cont_sector_fixed_line_norm_integrals F ζ hζ U R P H (scalarCovered f)
    hcont.measurable
  have hL : Measurable L := by
    have h := hnorm.borel
    change Measurable (fun b => ENNReal.ofReal
      (sectionNorm F ζ hζ U R P H (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H (scalarCovered f)) b ^ 2)) at h
    rw [S_scalarCovered] at h
    exact h
  have hNsupp : Function.support L ⊆ endSet F ζ hζ U R P H c T := by
    intro b hb
    apply hsupp
    rw [(kp_cont_actual_sector_smooth_test_modules F ζ hζ R.adelicHaar
      R.adelic_isHaar U R rfl P H realization).scalar_support f]
    apply subset_tsupport
    intro hz
    exact hb (by simp [L, N, hz])
  let ν := KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)
  let μt := Measure.comap (Subtype.val : Set.Ioi T → ℝ) ν
  letI : IsFiniteMeasure μt := by
    refine ⟨?_⟩
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioi).comap_apply,
      Set.image_univ, Subtype.range_coe]
    unfold ν KPCuspCharts.radialMeasure
    rw [withDensity_apply _ measurableSet_Ioi]
    have hd : (0 : ℝ) < KPCuspLogShape.dimension F := by
      exact_mod_cast (((H.atlas U).cuspAtlas c.1).geometry c.2).positive_dimension
    have hi := integrableOn_exp_mul_Ioi (a := -2 * (KPCuspLogShape.dimension F : ℝ))
      (by linarith) T
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      (fun t => (Real.exp_pos _).le))).mp hi.hasFiniteIntegral
  have hemb := (base_embedding_proof F ζ hζ U R P H c T hT).1
  have hpoint : ∀ y t, L (endChart F ζ hζ U R P H c T (y,t)) =
      ENNReal.ofReal (lineNormSq F ζ hζ U R P H c (v_c F ζ hζ U R P H f c t.val y)) := by
    intro y t
    induction y using Quotient.inductionOn with
    | h p =>
      unfold endChart
      rw [(((H.atlas U).cuspAtlas c.1).geometry c.2).highPresentation_formula,
        ← (H.atlas U).components_formula]
      change ENNReal.ofReal (sectionNorm F ζ hζ U R P H (scalarSections f)
        ((H.atlas U).components ⟨c.1, Quotient.mk _ (cuspPoint F ζ hζ U R P H c.1 c.2 (p,t.val))⟩) ^ 2) = _
      rw [sectionNorm_component]
      unfold v_c
      rw [Quotient.lift_mk, hermitian_norm_proof]
      rfl
  have hl : (∫⁻ b, L b ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) =
      ∫⁻ z : Y_c F ζ hζ U R P H c × ℝ,
        ENNReal.ofReal (scalarDensity F ζ hζ U R P H f c z.1 z.2)
        ∂(nu_c F ζ hζ U R P H c).prod (volume.restrict (Set.Ioi T)) := by
    rw [← setLIntegral_eq_of_support_subset hNsupp, ← fixed_haar_proof F ζ hζ U R P H c T hT,
      lintegral_map hL hemb.continuous.measurable]
    have hp := lintegral_prod (μ := nu_c F ζ hζ U R P H c) (ν := μt)
      (fun z : Y_c F ζ hζ U R P H c × Set.Ioi T => L (endChart F ζ hζ U R P H c T z))
      ((hL.comp hemb.continuous.measurable).aemeasurable)
    rw [hp]
    simp_rw [hpoint]
    have hr : ∀ y, (∫⁻ t : Set.Ioi T, ENNReal.ofReal
        (lineNormSq F ζ hζ U R P H c (v_c F ζ hζ U R P H f c t.val y)) ∂μt) =
        ∫⁻ t in Set.Ioi T, ENNReal.ofReal (scalarDensity F ζ hζ U R P H f c y t) ∂volume := by
      intro y
      dsimp only [μt]
      rw [lintegral_subtype_comap measurableSet_Ioi
        (fun t : ℝ => ENNReal.ofReal (lineNormSq F ζ hζ U R P H c
          (v_c F ζ hζ U R P H f c t y)))]
      unfold ν KPCuspCharts.radialMeasure
      rw [restrict_withDensity measurableSet_Ioi]
      have hw : Measurable (fun t : ℝ => ENNReal.ofReal
          (Real.exp (-2 * (KPCuspLogShape.dimension F : ℝ) * t))) :=
        ENNReal.measurable_ofReal.comp ((Real.continuous_exp.comp
          (continuous_const.mul continuous_id)).measurable)
      rw [lintegral_withDensity_eq_lintegral_mul _ hw]
      · apply lintegral_congr
        intro t
        rw [scalarDensity, dimension_eq_proof F ζ hζ,
          ENNReal.ofReal_mul (Real.exp_pos _).le]
        rfl
      · have hc : Continuous (fun t : ℝ => scalarDensity F ζ hζ U R P H f c y t) :=
          (scalarDensity_joint_continuous F ζ hζ U R P H realization f c).comp
            (continuous_const.prodMk continuous_id)
        have hn : Continuous (fun t : ℝ => lineNormSq F ζ hζ U R P H c
            (v_c F ζ hζ U R P H f c t y)) := by
          have hdiv : Continuous (fun t : ℝ => scalarDensity F ζ hζ U R P H f c y t /
              Real.exp (-2 * d F * t)) :=
            hc.div (Real.continuous_exp.comp (continuous_const.mul continuous_id))
              (fun t => (Real.exp_pos _).ne')
          simpa only [scalarDensity, mul_div_cancel_left₀ _ (Real.exp_pos _).ne'] using hdiv
        exact ENNReal.measurable_ofReal.comp hn.measurable
    simp_rw [hr]
    symm
    apply lintegral_prod
    exact (ENNReal.measurable_ofReal.comp
      (scalarDensity_joint_continuous F ζ hζ U R P H realization f c).measurable).aemeasurable
  have hi := (radialDensities_integrable F ζ hζ U R P H realization c T hT f hsupp).2.1
  letI := finite_transverse_proof F ζ hζ U R P H c
  rw [← integral_prod _ hi]
  rw [iota_norm_integral F ζ hζ U R P H f]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (hL.ennreal_toReal.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun b =>
      ENNReal.toReal_ofReal (sq_nonneg _)))]
  rw [hl]
  symm
  apply integral_eq_lintegral_of_nonneg_ae _ hi.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

private theorem actual_lift_exists (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∃ (a : ActualChart (U := U) (H := H))
      (y : KPContCotangentOverlapRationalBranches.omega a),
      KPContCotangentOverlapRationalBranches.q a y.val = x := by
  let C := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
  have hB := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H C
  have hx : x ∈ ⋃ n, KPContActualCotangentBorelRefinement.basePiece C n := by
    rw [hB.covers]
    exact Set.mem_univ x
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y, hy⟩ := Set.mem_range.mp (hB.base_subset n hn)
  refine ⟨C.chart n, KPContActualCotangentPieceHilbertSum.coordinates (C.chart n) y, ?_⟩
  have hi : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y.val) = y.val := by
    funext k
    simp [labeledA, labeledAInv]
  simpa only [KPContCotangentOverlapRationalBranches.q,
    KPContActualCotangentCountableShrinking.ShrunkChart.toBase,
    KPContActualCotangentPieceHilbertSum.coordinates, Subtype.coe_mk, hi] using hy

theorem fullPlacePair_normSquare (W : T_U F ζ hζ U R P H)
    (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    (∑ i : Fin (KPContCotangentActualOverlap.d F),
      KPContActualSectorFriedrichsSynthesis.placePair W W i x).re =
    (KPContActualCotangentMeasurableFamilies.normSquare W.val x : ℝ) := by
  obtain ⟨a, y, rfl⟩ := actual_lift_exists F ζ hζ U R P H x
  simp only [KPContActualCotangentMeasurableFamilies.normSquare_chart,
    map_sum, KPContActualSectorFriedrichsSynthesis.placePair_chart,
    Complex.re_sum,
    Complex.ofReal_re, NNReal.coe_pow, coe_nnnorm, PiLp.norm_sq_eq_of_L2,
    Fintype.sum_prod_type]
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

theorem coreLift_gradient_integral (f : S_U F ζ hζ U R P H) :
    q_U F ζ hζ U R P H μG hμG hR realization
      (coreLift F ζ hζ U R P H μG hμG hR realization f) =
      ∫ x, (KPContActualCotangentMeasurableFamilies.normSquare
        (KPContActualSectorTestDifferentialDescent.D_U f).val x : ℝ)
        ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
  have hgrad : closedGradient F ζ hζ U R P H μG hμG hR realization
      (coreLift F ζ hζ U R P H μG hμG hR realization f) =
      j (KPContActualSectorTestDifferentialDescent.D_U f) := by
    change (A).closure
      (KPContActualSectorFriedrichsSynthesis.formTest F ζ hζ U R P H μG hμG hR realization f) = _
    have h := LinearPMap.apply_comp_inclusion (A).le_closure
      ⟨iota f, LinearMap.mem_range_self iota f⟩
    exact h.symm.trans (KPTestOperator.descend_image _ _ _ _ f)
  rw [q_U, hgrad]
  exact (kp_cont_actual_sector_cotangent_l2 F ζ hζ μG hμG U R hR P H realization).norm_integral
    (j (KPContActualSectorTestDifferentialDescent.D_U f))
    (cotangentSquareFamily (KPContActualSectorTestDifferentialDescent.D_U f)) rfl

theorem radialDerivative_intrinsic_bound
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H)
    (p : KPCuspCharts.Cross F) (t : ℝ) :
    (d F)⁻¹ * ‖radialDerivative F ζ hζ U R P H f c p t‖ ^ 2 ≤
    (KPContActualCotangentMeasurableFamilies.normSquare
      (KPContActualSectorTestDifferentialDescent.D_U f).val
      ((H.atlas U).components ⟨c.1, Quotient.mk _
        (cuspPoint F ζ hζ U R P H c.1 c.2 (p,t))⟩) : ℝ) := by
  have hb := radialCoefficient_coframe_bound F ζ hζ U R P H realization f c p t
  rw [KPContCuspCoframeNaturality.actual_cusp_coframe_placePair F ζ hζ U R P H realization f c p t,
    fullPlacePair_normSquare F ζ hζ U R P H] at hb
  exact hb

theorem radial_energy_comparison
    (c : Cusp F ζ hζ U R P H) (T : ℝ)
    (hT : ((H.atlas U).cuspAtlas c.1).threshold < T)
    (f : S_U F ζ hζ U R P H)
    (hsupp : scalarSupport f.val ⊆ endSet F ζ hζ U R P H c T) :
    (d F)⁻¹ * (∫ y, ∫ t in Set.Ioi T,
      gradientDensity F ζ hζ U R P H f c y t ∂volume ∂nu_c F ζ hζ U R P H c) ≤
      q_U F ζ hζ U R P H μG hμG hR realization
        (coreLift F ζ hζ U R P H μG hμG hR realization f) := by
  let N := fun x => (KPContActualCotangentMeasurableFamilies.normSquare
    (KPContActualSectorTestDifferentialDescent.D_U f).val x : ℝ)
  let L := fun x => ENNReal.ofReal (N x)
  have hN : Measurable N :=
    (KPContActualCotangentMeasurableFamilies.measurable_normSquare _).coe_nnreal_real
  have hL : Measurable L := ENNReal.measurable_ofReal.comp hN
  have hNi : Integrable N (KPContActualSectorCotangentL2.muU F ζ hζ U R P) :=
    KPContActualCotangentIntrinsicHilbertIntegral.integrable_normSquare
      (cotangentSquareFamily (KPContActualSectorTestDifferentialDescent.D_U f))
  let ν := KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)
  let μt := Measure.comap (Subtype.val : Set.Ioi T → ℝ) ν
  letI : IsFiniteMeasure μt := by
    refine ⟨?_⟩
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioi).comap_apply,
      Set.image_univ, Subtype.range_coe]
    unfold ν KPCuspCharts.radialMeasure
    rw [withDensity_apply _ measurableSet_Ioi]
    have hd : (0 : ℝ) < KPCuspLogShape.dimension F := by
      exact_mod_cast (((H.atlas U).cuspAtlas c.1).geometry c.2).positive_dimension
    have hi := integrableOn_exp_mul_Ioi (a := -2 * (KPCuspLogShape.dimension F : ℝ))
      (by linarith) T
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      (fun t => (Real.exp_pos _).le))).mp hi.hasFiniteIntegral
  letI := finite_transverse_proof F ζ hζ U R P H c
  have hi := (radialDensities_integrable F ζ hζ U R P H realization c T hT f hsupp).2.2
  let J := ∫⁻ z : Y_c F ζ hζ U R P H c × ℝ,
    ENNReal.ofReal (gradientDensity F ζ hζ U R P H f c z.1 z.2)
      ∂(nu_c F ζ hζ U R P H c).prod (volume.restrict (Set.Ioi T))
  have hJ : J = ∫⁻ z : Y_c F ζ hζ U R P H c × Set.Ioi T,
      ENNReal.ofReal (lineNormSq F ζ hζ U R P H c
        (nabla_t F ζ hζ U R P H f c z.2.val z.1))
      ∂(nu_c F ζ hζ U R P H c).prod μt := by
    dsimp only [J]
    rw [lintegral_prod (μ := nu_c F ζ hζ U R P H c)
      (ν := volume.restrict (Set.Ioi T))
      (fun z : Y_c F ζ hζ U R P H c × ℝ =>
        ENNReal.ofReal (gradientDensity F ζ hζ U R P H f c z.1 z.2))
      (ENNReal.measurable_ofReal.comp
        (gradientDensity_joint_continuous F ζ hζ U R P H realization f c).measurable).aemeasurable]
    have hr : ∀ y, (∫⁻ t : Set.Ioi T, ENNReal.ofReal
        (lineNormSq F ζ hζ U R P H c (nabla_t F ζ hζ U R P H f c t.val y)) ∂μt) =
        ∫⁻ t in Set.Ioi T, ENNReal.ofReal (gradientDensity F ζ hζ U R P H f c y t) ∂volume := by
      intro y
      dsimp only [μt]
      rw [lintegral_subtype_comap measurableSet_Ioi
        (fun t : ℝ => ENNReal.ofReal (lineNormSq F ζ hζ U R P H c
          (nabla_t F ζ hζ U R P H f c t y)))]
      unfold ν KPCuspCharts.radialMeasure
      rw [restrict_withDensity measurableSet_Ioi]
      have hw : Measurable (fun t : ℝ => ENNReal.ofReal
          (Real.exp (-2 * (KPCuspLogShape.dimension F : ℝ) * t))) :=
        ENNReal.measurable_ofReal.comp ((Real.continuous_exp.comp
          (continuous_const.mul continuous_id)).measurable)
      rw [lintegral_withDensity_eq_lintegral_mul _ hw]
      · apply lintegral_congr
        intro t
        rw [gradientDensity, dimension_eq_proof F ζ hζ,
          ENNReal.ofReal_mul (Real.exp_pos _).le]
        rfl
      · have hc : Continuous (fun t : ℝ => gradientDensity F ζ hζ U R P H f c y t) :=
          (gradientDensity_joint_continuous F ζ hζ U R P H realization f c).comp
            (continuous_const.prodMk continuous_id)
        have hn : Continuous (fun t : ℝ => lineNormSq F ζ hζ U R P H c
            (nabla_t F ζ hζ U R P H f c t y)) := by
          have hdiv : Continuous (fun t : ℝ => gradientDensity F ζ hζ U R P H f c y t /
              Real.exp (-2 * d F * t)) :=
            hc.div (Real.continuous_exp.comp (continuous_const.mul continuous_id))
              (fun t => (Real.exp_pos _).ne')
          simpa only [gradientDensity, mul_div_cancel_left₀ _ (Real.exp_pos _).ne'] using hdiv
        exact ENNReal.measurable_ofReal.comp hn.measurable
    simp_rw [← hr]
    symm
    apply lintegral_prod
    have hcont : Continuous (fun z : Y_c F ζ hζ U R P H c × ℝ =>
        lineNormSq F ζ hζ U R P H c (nabla_t F ζ hζ U R P H f c z.2 z.1)) := by
      have hdiv : Continuous (fun z : Y_c F ζ hζ U R P H c × ℝ =>
          gradientDensity F ζ hζ U R P H f c z.1 z.2 / Real.exp (-2 * d F * z.2)) :=
        (gradientDensity_joint_continuous F ζ hζ U R P H realization f c).div
          (Real.continuous_exp.comp (continuous_const.mul continuous_snd))
          (fun z => (Real.exp_pos _).ne')
      simpa only [gradientDensity, mul_div_cancel_left₀ _ (Real.exp_pos _).ne'] using hdiv
    exact (ENNReal.measurable_ofReal.comp (hcont.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).measurable).aemeasurable
  have hpoint : ∀ z : Y_c F ζ hζ U R P H c × Set.Ioi T,
      ENNReal.ofReal ((d F)⁻¹) * ENNReal.ofReal
        (lineNormSq F ζ hζ U R P H c (nabla_t F ζ hζ U R P H f c z.2.val z.1)) ≤
      L (endChart F ζ hζ U R P H c T z) := by
    rintro ⟨y,t⟩
    induction y using Quotient.inductionOn with
    | h p =>
      unfold nabla_t endChart
      rw [Quotient.lift_mk, hermitian_norm_proof,
        (((H.atlas U).cuspAtlas c.1).geometry c.2).highPresentation_formula,
        ← (H.atlas U).components_formula,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr (positive_dimension_proof F).le)]
      exact ENNReal.ofReal_le_ofReal (radialDerivative_intrinsic_bound F ζ hζ U R P H realization f c p t.val)
  have hlin : ENNReal.ofReal ((d F)⁻¹) * J ≤ ∫⁻ x, L x
      ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
    rw [hJ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc _ ≤ ∫⁻ z, L (endChart F ζ hζ U R P H c T z)
        ∂(nu_c F ζ hζ U R P H c).prod μt := lintegral_mono hpoint
      _ = ∫⁻ x in endSet F ζ hζ U R P H c T, L x
          ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U := by
        rw [← fixed_haar_proof F ζ hζ U R P H c T hT,
          lintegral_map hL (base_embedding_proof F ζ hζ U R P H c T hT).1.continuous.measurable]
      _ ≤ ∫⁻ x, L x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P :=
        lintegral_mono' Measure.restrict_le_self le_rfl
  have hreal := ENNReal.toReal_mono
    ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x =>
      (KPContActualCotangentMeasurableFamilies.normSquare _ x).coe_nonneg)).mp hNi.hasFiniteIntegral).ne hlin
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (positive_dimension_proof F).le)] at hreal
  rw [coreLift_gradient_integral F ζ hζ U R P H μG hμG hR realization f]
  rw [← integral_prod _ hi]
  have hgpos : 0 ≤ᵐ[(nu_c F ζ hζ U R P H c).prod (volume.restrict (Set.Ioi T))]
      (fun z : Y_c F ζ hζ U R P H c × ℝ => gradientDensity F ζ hζ U R P H f c z.1 z.2) :=
    Filter.Eventually.of_forall fun z => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  rw [integral_eq_lintegral_of_nonneg_ae hgpos hi.aestronglyMeasurable]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x =>
    (KPContActualCotangentMeasurableFamilies.normSquare _ x).coe_nonneg) hNi.aestronglyMeasurable]
  exact hreal

theorem high_cusp_relation_parallel
    (c : Cusp F ζ hζ U R P H) (γ : KPCuspGenuineMonodromy.Component F ζ hζ U
      ((H.atlas U).representative c.1))
    (p q : KPCuspCharts.Cross F) (t s : ℝ)
    (ht : ((H.atlas U).cuspAtlas c.1).threshold < t)
    (hs : ((H.atlas U).cuspAtlas c.1).threshold < s)
    (he : cuspPoint F ζ hζ U R P H c.1 c.2 (q,s) =
      (γ : KPCuspArithmetic.PGL2 F) • cuspPoint F ζ hζ U R P H c.1 c.2 (p,t)) :
    s = t ∧ ∀ r : ℝ, cuspPoint F ζ hζ U R P H c.1 c.2 (q,r) =
      (γ : KPCuspArithmetic.PGL2 F) • cuspPoint F ζ hζ U R P H c.1 c.2 (p,r) := by
  let At := H.atlas U
  let σ := (At.cuspAtlas c.1).representative c.2
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U (At.representative c.1)
  have hd := (At.cuspAtlas c.1).geometry c.2 |>.positive_dimension
  have hz : σ • KPCuspCharts.toArch F (p,t) ∈
      KPCuspSiegel.highCusp F σ (At.cuspAtlas c.1).threshold := by
    refine ⟨KPCuspCharts.toArch F (p,t), ?_, rfl⟩
    change (At.cuspAtlas c.1).threshold < KPCuspLogShape.meanHeight _ _
    rw [KPCuspCharts.toArch_meanHeight F hd]
    exact ht
  have hγz : (γ : KPCuspArithmetic.PGL2 F) • (σ • KPCuspCharts.toArch F (p,t)) ∈
      KPCuspSiegel.highCusp F σ (At.cuspAtlas c.1).threshold := by
    change (γ : KPCuspArithmetic.PGL2 F) • cuspPoint F ζ hζ U R P H c.1 c.2 (p,t) ∈ _
    rw [← he]
    refine ⟨KPCuspCharts.toArch F (q,s), ?_, rfl⟩
    change (At.cuspAtlas c.1).threshold < KPCuspLogShape.meanHeight _ _
    rw [KPCuspCharts.toArch_meanHeight F hd]
    exact hs
  have hp := KPContGenericEndMapRigidity.actual_high_intersection_of_endMap_injective
    F hd Γ ((At.cuspAtlas c.1).cusp c.2) σ (At.cuspAtlas c.1).threshold
    ((At.cuspAtlas c.1).end_embedding c.2).injective γ _ hz hγz
  let g : Stabilizer F ζ hζ U R P H c :=
    ⟨σ⁻¹ * (γ : KPCuspArithmetic.PGL2 F) * σ,
      Subgroup.mem_map.mpr ⟨γ, hp, by
        change σ⁻¹ * (γ : KPCuspArithmetic.PGL2 F) * (σ⁻¹)⁻¹ = _
        rw [inv_inv]⟩⟩
  have hg : (KPCuspGenuineMonodromy.cuspInclusion F Γ
      ((At.cuspAtlas c.1).cusp c.2) σ g : KPCuspArithmetic.PGL2 F) = γ := by
    rw [KPCuspGenuineMonodromy.cuspInclusion_formula]
    change σ * (σ⁻¹ * (γ : KPCuspArithmetic.PGL2 F) * σ) * σ⁻¹ = _
    group
  have hflat : KPCuspCharts.toArch F (q,s) =
      KPCuspCharts.toArch F ((((At.cuspAtlas c.1).geometry c.2).crossAction g p),t) := by
    have h := he
    have ht' := cuspPoint_transition F ζ hζ U R P H c g p t
    have hg' : KPCuspGenuineMonodromy.cuspInclusion F Γ
        ((At.cuspAtlas c.1).cusp c.2) σ g = γ := Subtype.ext hg
    change cuspPoint F ζ hζ U R P H c.1 c.2
        ((((At.cuspAtlas c.1).geometry c.2).crossAction g p),t) =
      (KPCuspGenuineMonodromy.cuspInclusion F Γ
        ((At.cuspAtlas c.1).cusp c.2) σ g : KPCuspArithmetic.PGL2 F) •
        cuspPoint F ζ hζ U R P H c.1 c.2 (p,t) at ht'
    rw [hg'] at ht'
    rw [← ht'] at h
    exact MulAction.injective σ h
  have hcoord := (KPCuspCharts.toArchHomeomorph F hd).injective hflat
  refine ⟨(Prod.ext_iff.mp hcoord).2, ?_⟩
  intro r
  have hq : q = ((At.cuspAtlas c.1).geometry c.2).crossAction g p := (Prod.ext_iff.mp hcoord).1
  rw [hq, cuspPoint_transition]
  have hg' : KPCuspGenuineMonodromy.cuspInclusion F Γ
      ((At.cuspAtlas c.1).cusp c.2) σ g = γ := Subtype.ext hg
  exact congrArg (fun δ : Γ => (δ : KPCuspArithmetic.PGL2 F) •
    cuspPoint F ζ hζ U R P H c.1 c.2 (p,r)) hg'

theorem endLineRelation_iff_parallel
    (c : Cusp F ζ hζ U R P H) (T : ℝ)
    (hT : ((H.atlas U).cuspAtlas c.1).threshold < T)
    (z z' : (KPCuspCharts.Cross F × Set.Ioi T) × Coefficient F ζ hζ U) :
    endLineRelation F ζ hζ U R P H c T z z' ↔
      transverseLineRelation F ζ hζ U R P H c (z.1.1,z.2) (z'.1.1,z'.2) ∧
      z.1.2 = z'.1.2 := by
  constructor
  · rintro ⟨γ, hp, hc⟩
    have hh := high_cusp_relation_parallel F ζ hζ U R P H c γ z.1.1 z'.1.1
      z.1.2.val z'.1.2.val (lt_trans hT z.1.2.property) (lt_trans hT z'.1.2.property) hp
    exact ⟨⟨γ, hh.2 _, hc⟩, Subtype.ext hh.1.symm⟩
  · rintro ⟨⟨γ, hp, hc⟩, ht⟩
    have hh := high_cusp_relation_parallel F ζ hζ U R P H c γ z.1.1 z'.1.1
      (((H.atlas U).cuspAtlas c.1).threshold + 1)
      (((H.atlas U).cuspAtlas c.1).threshold + 1) (by linarith) (by linarith) hp
    refine ⟨γ, ?_, hc⟩
    change cuspPoint F ζ hζ U R P H c.1 c.2 (z'.1.1,z'.1.2.val) =
      (γ : KPCuspArithmetic.PGL2 F) • cuspPoint F ζ hζ U R P H c.1 c.2 (z.1.1,z.1.2.val)
    rw [← ht]
    exact hh.2 _

 def radialLineForward (c : Cusp F ζ hζ U R P H) (T : ℝ)
    (hT : ((H.atlas U).cuspAtlas c.1).threshold < T)
    (z : L_c F ζ hζ U R P H c × Set.Ioi T) : EndLine F ζ hζ U R P H c T :=
  Quotient.lift (fun w : KPCuspCharts.Cross F × Coefficient F ζ hζ U =>
    Quotient.mk _ ((w.1,z.2),w.2)) (fun w w' hw => Quotient.sound
      ((endLineRelation_iff_parallel F ζ hζ U R P H c T hT _ _).mpr ⟨hw,rfl⟩)) z.1

 def radialLineBackward (c : Cusp F ζ hζ U R P H) (T : ℝ)
    (hT : ((H.atlas U).cuspAtlas c.1).threshold < T) :
    EndLine F ζ hζ U R P H c T → L_c F ζ hζ U R P H c × Set.Ioi T :=
  Quotient.lift (fun w => (Quotient.mk _ (w.1.1,w.2),w.1.2)) (fun w w' hw => by
    obtain ⟨hl,ht⟩ := (endLineRelation_iff_parallel F ζ hζ U R P H c T hT w w').mp hw
    exact Prod.ext (Quotient.sound hl) ht)

def radialLineHomeomorph (c : Cusp F ζ hζ U R P H) (T : ℝ)
    (hT : ((H.atlas U).cuspAtlas c.1).threshold < T) :
    L_c F ζ hζ U R P H c × Set.Ioi T ≃ₜ EndLine F ζ hζ U R P H c T where
  toFun := radialLineForward F ζ hζ U R P H c T hT
  invFun := radialLineBackward F ζ hζ U R P H c T hT
  left_inv := by
    rintro ⟨y,t⟩
    induction y using Quotient.inductionOn with
    | h p => rfl
  right_inv := by
    intro y
    induction y using Quotient.inductionOn with
    | h p => rfl
  continuous_toFun := by
    letI : LocallyCompactSpace (Set.Ioi T) := isOpen_Ioi.locallyCompactSpace
    apply (isQuotientMap_quotient_mk'
      (s := transverseLineRelation F ζ hζ U R P H c)).continuous_lift_prod_left
    have he : (fun z : (KPCuspCharts.Cross F × Coefficient F ζ hζ U) × Set.Ioi T =>
        radialLineForward F ζ hζ U R P H c T hT (Quotient.mk _ z.1,z.2)) =
        fun z => Quotient.mk (endLineRelation F ζ hζ U R P H c T) ((z.1.1,z.2),z.1.2) := rfl
    change Continuous (fun z : (KPCuspCharts.Cross F × Coefficient F ζ hζ U) × Set.Ioi T =>
      radialLineForward F ζ hζ U R P H c T hT (Quotient.mk _ z.1,z.2))
    rw [he]
    exact continuous_quotient_mk'.comp
      ((continuous_fst.fst.prodMk continuous_snd).prodMk continuous_fst.snd)
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact ((continuous_quotient_mk'.comp (continuous_fst.fst.prodMk continuous_snd)).prodMk
      continuous_fst.snd)

@[simp] theorem radialLineHomeomorph_mk
    (c : Cusp F ζ hζ U R P H) (T : ℝ)
    (hT : ((H.atlas U).cuspAtlas c.1).threshold < T)
    (p : KPCuspCharts.Cross F) (a : Coefficient F ζ hζ U) (t : Set.Ioi T) :
    radialLineHomeomorph F ζ hζ U R P H c T hT (Quotient.mk _ (p,a),t) =
      Quotient.mk _ ((p,t),a) := rfl

private theorem actualLine_quotient_open (c : Cusp F ζ hζ U R P H) :
    IsOpenMap (Quotient.mk (KPCuspGenuineMonodromy.flatLineRelation F ζ hζ U
      ((H.atlas U).representative c.1) ((H.atlas U).line c.1).rho)) := by
  letI := KPFiniteAdelicCuspEnds.canonicalAction_continuousConstSMul F
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1)
  let Q := Quotient.mk (KPCuspGenuineMonodromy.flatLineRelation F ζ hζ U
    ((H.atlas U).representative c.1) ((H.atlas U).line c.1).rho)
  let act : Γ → (KPCuspGenuineMonodromy.SymmetricSpace F × Coefficient F ζ hζ U ≃ₜ
      KPCuspGenuineMonodromy.SymmetricSpace F × Coefficient F ζ hζ U) := fun γ =>
    (Homeomorph.smul (γ : KPCuspArithmetic.PGL2 F)).prodCongr
      (phaseTransport F ζ hζ U (((H.atlas U).line c.1).rho γ)).toHomeomorph
  intro V hV
  change IsOpen (Q '' V)
  rw [isOpen_coinduced]
  have hsat : Q ⁻¹' (Q '' V) = ⋃ γ : Γ, act γ '' V := by
    ext z
    constructor
    · rintro ⟨w, hw, he⟩
      obtain ⟨γ, hp, hc⟩ := Quotient.exact he
      apply Set.mem_iUnion.mpr
      refine ⟨γ, w, hw, ?_⟩
      apply Prod.ext hp.symm
      apply Subtype.ext
      exact hc.symm
    · intro hz
      obtain ⟨γ,w,hw,he⟩ := Set.mem_iUnion.mp hz
      refine ⟨w,hw,Quotient.sound ⟨γ, ?_, ?_⟩⟩
      · exact (congrArg Prod.fst he).symm
      · exact (congrArg (fun z => (z.2 : ℂ)) he).symm
  change IsOpen (Q ⁻¹' (Q '' V))
  rw [hsat]
  exact isOpen_iUnion (fun γ => (act γ).isOpenMap V hV)

private theorem rawEndLine_openEmbedding (c : Cusp F ζ hζ U R P H) (T : ℝ) :
    IsOpenEmbedding (fun z : (KPCuspCharts.Cross F × Set.Ioi T) × Coefficient F ζ hζ U =>
      (cuspPoint F ζ hζ U R P H c.1 c.2 (z.1.1,z.1.2.val),z.2)) := by
  letI := KPFiniteAdelicCuspEnds.canonicalAction_continuousConstSMul F
  let E := (KPCuspCharts.toArchHomeomorph F
    (((H.atlas U).cuspAtlas c.1).geometry c.2).positive_dimension).trans
      (Homeomorph.smul (((H.atlas U).cuspAtlas c.1).representative c.2))
  have hsub : IsOpenEmbedding (fun z : KPCuspCharts.Cross F × Set.Ioi T => (z.1,z.2.val)) :=
    IsOpenEmbedding.id.prodMap isOpen_Ioi.isOpenEmbedding_subtypeVal
  have he : IsOpenEmbedding (fun z : KPCuspCharts.Cross F × Set.Ioi T =>
      cuspPoint F ζ hζ U R P H c.1 c.2 (z.1,z.2.val)) := by
    exact E.isOpenEmbedding.comp hsub
  exact he.prodMap IsOpenEmbedding.id

theorem endLineToActual_isEmbedding (c : Cusp F ζ hζ U R P H) (T : ℝ) :
    IsEmbedding (endLineToActual F ζ hζ U R P H c T) := by
  let raw := fun z : (KPCuspCharts.Cross F × Set.Ioi T) × Coefficient F ζ hζ U =>
    (cuspPoint F ζ hζ U R P H c.1 c.2 (z.1.1,z.1.2.val),z.2)
  let Q := Quotient.mk (KPCuspGenuineMonodromy.flatLineRelation F ζ hζ U
    ((H.atlas U).representative c.1) ((H.atlas U).line c.1).rho)
  have hraw := rawEndLine_openEmbedding F ζ hζ U R P H c T
  have hcont : Continuous (endLineToActual F ζ hζ U R P H c T) := by
    apply Continuous.quotient_lift
    exact continuous_quotient_mk'.comp hraw.continuous
  have hinj : Function.Injective (endLineToActual F ζ hζ U R P H c T) := by
    intro z z' he
    induction z using Quotient.inductionOn with
    | h w =>
      induction z' using Quotient.inductionOn with
      | h w' =>
        change Q (raw w) = Q (raw w') at he
        have hrel : KPCuspGenuineMonodromy.flatLineRelation F ζ hζ U
            ((H.atlas U).representative c.1) ((H.atlas U).line c.1).rho (raw w) (raw w') :=
          Quotient.exact he
        exact Quotient.sound hrel
  have hopen : IsOpenMap (endLineToActual F ζ hζ U R P H c T) := by
    intro V hV
    have hpre : IsOpen (Quotient.mk (endLineRelation F ζ hζ U R P H c T) ⁻¹' V) :=
      hV.preimage continuous_quotient_mk'
    have he : endLineToActual F ζ hζ U R P H c T '' V =
        Q '' (raw '' (Quotient.mk (endLineRelation F ζ hζ U R P H c T) ⁻¹' V)) := by
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        obtain ⟨v,rfl⟩ := Quotient.exists_rep w
        exact ⟨raw v, ⟨v,hw,rfl⟩,rfl⟩
      · rintro ⟨_,⟨v,hv,rfl⟩,rfl⟩
        exact ⟨Quotient.mk _ v,hv,rfl⟩
    rw [he]
    exact actualLine_quotient_open F ζ hζ U R P H c _ (hraw.isOpenMap _ hpre)
  exact (IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen).isEmbedding

structure Properties : Prop where
  positive_dimension : 0 < d F
  dimension_eq : d F = (KPCuspLogShape.dimension F : ℝ)
  compact_transverse : ∀ c : Cusp F ζ hζ U R P H, CompactSpace (Y_c F ζ hζ U R P H c)
  finite_transverse : ∀ c : Cusp F ζ hζ U R P H, IsFiniteMeasure (nu_c F ζ hζ U R P H c)
  positive_transverse : ∀ c : Cusp F ζ hζ U R P H, 0 < nu_c F ζ hζ U R P H c Set.univ
  hermitian_norm : ∀ (c : Cusp F ζ hζ U R P H) (p : KPCuspCharts.Cross F)
      (a : Coefficient F ζ hζ U),
    lineNormSq F ζ hζ U R P H c (Quotient.mk _ (p,a)) = ‖a‖ ^ 2
  section_base : ∀ (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H) t y,
    lineBase F ζ hζ U R P H c (v_c F ζ hζ U R P H f c t y) = y ∧
    lineBase F ζ hζ U R P H c (nabla_t F ζ hζ U R P H f c t y) = y
  core_inclusion : ∀ f : S_U F ζ hζ U R P H,
    j_U F ζ hζ U R P H μG hμG hR realization
      (coreLift F ζ hζ U R P H μG hμG hR realization f) = iota f
  core_energy : ∀ f : S_U F ζ hζ U R P H,
    q_U F ζ hζ U R P H μG hμG hR realization
      (coreLift F ζ hζ U R P H μG hμG hR realization f) =
    KPContActualSectorFriedrichsSynthesis.energy F ζ hζ U R P H μG hμG hR realization
      (KPContActualSectorFriedrichsSynthesis.formTest F ζ hζ U R P H μG hμG hR realization f)

  radial_pullback : ∀ (c : Cusp F ζ hζ U R P H) (T : ℝ),
    ((H.atlas U).cuspAtlas c.1).threshold < T →
      ∃ e : L_c F ζ hζ U R P H c × Set.Ioi T ≃ₜ EndLine F ζ hζ U R P H c T,
        (∀ (p : KPCuspCharts.Cross F) (a : Coefficient F ζ hζ U) (t : Set.Ioi T),
          e (Quotient.mk _ (p,a),t) = Quotient.mk _ ((p,t),a)) ∧
        Topology.IsEmbedding (endLineToActual F ζ hζ U R P H c T)
  base_embedding : ∀ (c : Cusp F ζ hζ U R P H) (T : ℝ),
    ((H.atlas U).cuspAtlas c.1).threshold < T →
    Topology.IsEmbedding (endChart F ζ hζ U R P H c T) ∧
    Set.range (endChart F ζ hζ U R P H c T) = endSet F ζ hζ U R P H c T

  fixed_haar : ∀ (c : Cusp F ζ hζ U R P H) (T : ℝ),
    ((H.atlas U).cuspAtlas c.1).threshold < T →
    Measure.map (endChart F ζ hζ U R P H c T)
      ((nu_c F ζ hζ U R P H c).prod
        (Measure.comap (Subtype.val : Set.Ioi T → ℝ)
          (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)))) =
      (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict
        (endSet F ζ hζ U R P H c T)

  transition : ∀ (f : S_U F ζ hζ U R P H) (c : Cusp F ζ hζ U R P H)
      (g : Stabilizer F ζ hζ U R P H c) (p : KPCuspCharts.Cross F) (t : ℝ),
    let γ := KPCuspGenuineMonodromy.cuspInclusion F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
      (((H.atlas U).cuspAtlas c.1).cusp c.2)
      (((H.atlas U).cuspAtlas c.1).representative c.2) g
    coefficient F ζ hζ U R P H f c
      ((((H.atlas U).cuspAtlas c.1).geometry c.2).crossAction g p) t =
      phaseTransport F ζ hζ U (((H.atlas U).line c.1).rho γ)
        (coefficient F ζ hζ U R P H f c p t) ∧
    radialDerivative F ζ hζ U R P H f c
      ((((H.atlas U).cuspAtlas c.1).geometry c.2).crossAction g p) t =
      (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line c.1).rho γ) : ℂ) *
        radialDerivative F ζ hζ U R P H f c p t

  finite_integrals : ∀ (c : Cusp F ζ hζ U R P H) (T : ℝ),
    ((H.atlas U).cuspAtlas c.1).threshold < T →
    ∀ f : S_U F ζ hζ U R P H,
      scalarSupport f.val ⊆ endSet F ζ hζ U R P H c T →
      (∀ y, IntegrableOn (scalarDensity F ζ hζ U R P H f c y) (Set.Ioi T) volume ∧
        IntegrableOn (gradientDensity F ζ hζ U R P H f c y) (Set.Ioi T) volume) ∧
      Integrable (fun y => ∫ t in Set.Ioi T, scalarDensity F ζ hζ U R P H f c y t ∂volume)
        (nu_c F ζ hζ U R P H c) ∧
      Integrable (fun y => ∫ t in Set.Ioi T, gradientDensity F ζ hζ U R P H f c y t ∂volume)
        (nu_c F ζ hζ U R P H c)

  comparison : ∀ (c : Cusp F ζ hζ U R P H) (T : ℝ),
    ((H.atlas U).cuspAtlas c.1).threshold < T →
    ∀ f : S_U F ζ hζ U R P H,
      scalarSupport f.val ⊆ endSet F ζ hζ U R P H c T →
      Integrable (fun z : Y_c F ζ hζ U R P H c × ℝ =>
        scalarDensity F ζ hζ U R P H f c z.1 z.2)
        ((nu_c F ζ hζ U R P H c).prod (volume.restrict (Set.Ioi T))) ∧
      Integrable (fun z : Y_c F ζ hζ U R P H c × ℝ =>
        gradientDensity F ζ hζ U R P H f c z.1 z.2)
        ((nu_c F ζ hζ U R P H c).prod (volume.restrict (Set.Ioi T))) ∧
      ‖iota f‖ ^ 2 =
        ∫ y, ∫ t in Set.Ioi T, scalarDensity F ζ hζ U R P H f c y t
          ∂volume ∂nu_c F ζ hζ U R P H c ∧
      (d F)⁻¹ * (∫ y, ∫ t in Set.Ioi T, gradientDensity F ζ hζ U R P H f c y t
          ∂volume ∂nu_c F ζ hζ U R P H c) ≤
        q_U F ζ hζ U R P H μG hμG hR realization
          (coreLift F ζ hζ U R P H μG hμG hR realization f)

end DedekindZetaZeroFree.KPContActualCuspRadialFormComparison

namespace DedekindZetaZeroFree

theorem kp_cont_actual_cusp_radial_form_comparison
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (friedrichs : KPContActualSectorTestFriedrichs.Properties F ζ hζ U R P H
      μG hμG hR realization) :
    KPContActualCuspRadialFormComparison.Properties F ζ hζ U R P H μG hμG hR realization := by
  refine
    { positive_dimension :=
        KPContActualCuspRadialFormComparison.positive_dimension_proof F
      dimension_eq :=
        KPContActualCuspRadialFormComparison.dimension_eq_proof F ζ hζ
      compact_transverse := fun c =>
        KPContActualCuspRadialFormComparison.compact_transverse_proof F ζ hζ U R P H c
      finite_transverse := fun c =>
        KPContActualCuspRadialFormComparison.finite_transverse_proof F ζ hζ U R P H c
      positive_transverse := fun c =>
        KPContActualCuspRadialFormComparison.positive_transverse_proof F ζ hζ U R P H c
      hermitian_norm := fun c p a =>
        KPContActualCuspRadialFormComparison.hermitian_norm_proof F ζ hζ U R P H c p a
      section_base := fun f c t y =>
        KPContActualCuspRadialFormComparison.section_base_proof F ζ hζ U R P H f c t y
      core_inclusion := fun f =>
        KPContActualCuspRadialFormComparison.core_inclusion_proof F ζ hζ U R P H μG hμG hR
          realization f
      core_energy := fun f =>
        KPContActualCuspRadialFormComparison.core_energy_proof F ζ hζ U R P H μG hμG hR
          realization f
      radial_pullback := by
        intro c T hT
        refine ⟨KPContActualCuspRadialFormComparison.radialLineHomeomorph F ζ hζ U R P H c T hT,
          fun p a t => rfl,
          KPContActualCuspRadialFormComparison.endLineToActual_isEmbedding F ζ hζ U R P H c T⟩
      base_embedding := fun c T hT =>
        KPContActualCuspRadialFormComparison.base_embedding_proof F ζ hζ U R P H c T hT
      fixed_haar := fun c T hT =>
        KPContActualCuspRadialFormComparison.fixed_haar_proof F ζ hζ U R P H c T hT
      transition := fun f c g p t =>
        ⟨KPContActualCuspRadialFormComparison.transition_coefficient F ζ hζ U R P H f c g p t,
          KPContActualCuspRadialFormComparison.transition_radialDerivative F ζ hζ U R P H f c g p t⟩
      finite_integrals := by
        intro c T hT f hf
        letI := KPContActualCuspRadialFormComparison.finite_transverse_proof F ζ hζ U R P H c
        have hi := KPContActualCuspRadialFormComparison.radialDensities_integrable
          F ζ hζ U R P H realization c T hT f hf
        exact ⟨hi.1, hi.2.1.integral_prod_left, hi.2.2.integral_prod_left⟩
      comparison := by
        intro c T hT f hf
        have hi := KPContActualCuspRadialFormComparison.radialDensities_integrable
          F ζ hζ U R P H realization c T hT f hf
        refine ⟨hi.2.1, hi.2.2,
          KPContActualCuspRadialFormComparison.scalar_radial_norm
            F ζ hζ U R P H realization c T hT f hf, ?_⟩
        exact KPContActualCuspRadialFormComparison.radial_energy_comparison
          F ζ hζ U R P H μG hμG hR realization c T hT f hf }

end DedekindZetaZeroFree

end
