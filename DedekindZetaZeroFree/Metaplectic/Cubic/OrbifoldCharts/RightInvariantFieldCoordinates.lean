module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LocalCharts.NormalChartsAndHyperbolicDensity
public import DedekindZetaZeroFree.Metaplectic.Cubic.Haar.SphericalSectorRealization
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightDifferentialWords.CoordinateJetEstimates

@[expose] public section

noncomputable section
open scoped Classical NumberField
open Topology

namespace DedekindZetaZeroFree.KPContActualSphericalRightFieldIdentification

open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra
open KPContSectorSmoothFramesSupport KPContSectorQuotientRelationsComparison

variable (F : Type) [Field F] [NumberField F]

def groupCoordinates : KPContLocalNorm.Space (groupDimension F) ≃L[ℝ]
    KPSmoothLocalQuotientCharts.Coordinates F :=
  (EuclideanSpace.equiv _ ℝ).trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : LieIndex F => ℝ) (lieEnumeration F))

abbrev baseDimension := Module.finrank ℝ (SymmetricSpace F)

def baseCoordinates : KPContLocalNorm.Space (baseDimension F) ≃L[ℝ]
    SymmetricSpace F :=
  (EuclideanSpace.equiv _ ℝ).trans (Module.finBasis ℝ _).equivFunL.symm

open scoped Manifold ContDiff

@[instance_reducible] def actualLieChartedSpace : ChartedSpace (KPSmoothLocalQuotientCharts.Coordinates F)
    (KPSmoothLocalQuotientCharts.ArchGroup F) :=
  Classical.choose (LocalQuotientCharts.ExponentialHaarFrame.raw_lie_exponential_data F)
@[instance_reducible] def actualLieGroup :
    letI := actualLieChartedSpace F
    LieGroup (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞)
      (KPSmoothLocalQuotientCharts.ArchGroup F) :=
  Classical.choose (Classical.choose_spec
    (LocalQuotientCharts.ExponentialHaarFrame.raw_lie_exponential_data F))
def actualLieData :
    letI := actualLieChartedSpace F
    letI := actualLieGroup F
    HilbertLieExponentialData (KPSmoothLocalQuotientCharts.ArchGroup F)
      (KPSmoothLocalQuotientCharts.Coordinates F) (LieIndex F) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (LocalQuotientCharts.ExponentialHaarFrame.raw_lie_exponential_data F)))
lemma actualLieData_exponential :
    letI := actualLieChartedSpace F
    letI := actualLieGroup F
    (actualLieData F).exponential = KPSmoothLocalQuotientCharts.matrixExp F :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (LocalQuotientCharts.ExponentialHaarFrame.raw_lie_exponential_data F)))).1
lemma actualLieData_basis (b : LieIndex F) :
    letI := actualLieChartedSpace F
    letI := actualLieGroup F
    (actualLieData F).basis b = Pi.single b 1 :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (LocalQuotientCharts.ExponentialHaarFrame.raw_lie_exponential_data F)))).2.1 b
lemma chosen_actual_exponential_chart (g : KPSmoothLocalQuotientCharts.ArchGroup F) :
    letI := actualLieChartedSpace F
    letI := actualLieGroup F
    ∃ E : KPSmoothLocalQuotientCharts.ExponentialChart F g,
      ∃ O : OpenPartialHomeomorph (KPSmoothLocalQuotientCharts.Coordinates F)
        (KPSmoothLocalQuotientCharts.ArchGroup F),
      O.toPartialHomeomorph = E.chart ∧
      ContMDiffOn (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
        (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞) O O.source ∧
      ContMDiffOn (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
        (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞) O.symm O.target ∧
      (∀ b, ContDiffOn ℝ (⊤ : ℕ∞)
        (KPSmoothLocalQuotientCharts.rightLieField F E b) E.chart.source) := by
  letI := actualLieChartedSpace F
  letI := actualLieGroup F
  obtain ⟨O, h0, he, hs, hi, hv, _⟩ :=
    PGLExponential.translated_exponential_frame (actualLieData F) g
  refine ⟨⟨O.toPartialHomeomorph, h0, ?_⟩, O, rfl, hs, hi, ?_⟩
  · intro x hx
    exact (he x hx).trans (congrArg (g * ·) (congrFun (actualLieData_exponential F) x))
  · intro b
    change ContDiffOn ℝ (⊤ : ℕ∞)
      (fun a => deriv (fun t : ℝ => O.symm
        (O a * KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single b 1))) 0) O.source
    simpa only [actualLieData_exponential, actualLieData_basis] using hv b

variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

structure LocalSection (i : Fin (H.atlas U).componentCount) (a : SymmetricSpace F)
    (A : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i a) where
  coefficient : SymmetricSpace F → Coefficient F ζ hζ U
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (coefficient x : ℂ)) A.neighborhood
  equivariant : ∀ σ : MulAction.stabilizer
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i) a,
    ∀ x ∈ A.neighborhood,
      coefficient ((σ.val : KPCuspArithmetic.PGL2 F) • x) =
        phaseTransport F ζ hζ U (((H.atlas U).line i).rho σ.val) (coefficient x)

def localCoveredScalar {i : Fin (H.atlas U).componentCount} {a : SymmetricSpace F}
    {A : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i a}
    (u : LocalSection F ζ hζ U R P H i a A) :
    (q F ζ hζ U ⁻¹'
      KPContSectorPhaseComponentCharts.baseChartImage F ζ hζ U R P H i a A) → ℂ :=
  fun v => Quotient.lift
    (fun p : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U × A.neighborhood =>
      Quotient.lift
        (fun ε : rootsOfUnity 3 F =>
          (phaseTransport F ζ hζ U ε (u.coefficient p.2.val) : ℂ))
        (by
          intro a b hab
          change QuotientGroup.leftRel
            (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ U) a b at hab
          rw [QuotientGroup.leftRel_apply] at hab
          exact congrArg (fun w : Coefficient F ζ hζ U => (w : ℂ))
            (phaseTransport_level_ambiguity F ζ hζ U b a
              (by simpa [KPContSectorPhaseComponentCharts.centralLevel] using hab)
              (u.coefficient p.2.val)).symm) p.1)
    (by
      intro p q hpq
      change MulAction.orbitRel
        (MulAction.stabilizer
          (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i) a)
        (KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U × A.neighborhood) p q at hpq
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hpq
      obtain ⟨σ, hσ⟩ := hpq
      rw [← hσ]
      obtain ⟨m, y⟩ := q
      set ρ : rootsOfUnity 3 F := ((H.atlas U).line i).rho σ.val with hρdef
      have hcoe : u.coefficient ((σ.val : KPCuspArithmetic.PGL2 F) • (y : SymmetricSpace F)) =
          phaseTransport F ζ hζ U ρ (u.coefficient y.val) :=
        u.equivariant σ y.val y.property
      refine Quotient.inductionOn m (fun ε => ?_)
      letI := KPContSectorPhaseComponentCharts.instMulActionChartProduct F ζ hζ U R P H i a A
      have hcs := KPContSectorPhaseComponentCharts.chartProduct_smul F ζ hζ U R P H i a A σ
        (ε : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U) y
      have hpair : σ • ((ε :
            KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U), y) =
          (Quotient.mk _ (ε * ρ⁻¹),
            ⟨(σ.val : KPCuspArithmetic.PGL2 F) • (y : SymmetricSpace F), by
              have h2 : ((σ • ((ε :
                  KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U), y)).2 :
                    SymmetricSpace F) = (σ.val : KPCuspArithmetic.PGL2 F) • (y : SymmetricSpace F) := by
                simpa using congrArg (fun z => z.2) hcs
              rw [← h2]
              exact (σ • ((ε :
                KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U), y)).2.property⟩) := by
        apply Prod.ext
        · exact (congrArg Prod.fst hcs : (σ • ((ε :
                KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U), y)).1 =
              (ε : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U) *
                KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U ρ⁻¹)
        · apply Subtype.ext
          simpa using congrArg (fun z => z.2) hcs
      rw [hpair]
      simp only [Quotient.lift_mk]
      rw [hcoe, phaseTransport_apply, phaseTransport_apply, phaseTransport_apply]
      have hchi : (chi F ζ hζ (ε * ρ⁻¹) : ℂ) * (chi F ζ hζ ρ : ℂ) = (chi F ζ hζ ε : ℂ) := by
        rw [chi_coe, chi_coe, chi_coe, ← Units.val_mul, ← map_mul]
        congr 1
        group
      rw [← mul_assoc, hchi])
    ((KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i a A).symm v)

def sectionGroupLift {i : Fin (H.atlas U).componentCount} {a : SymmetricSpace F}
    {A : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i a}
    (u : LocalSection F ζ hζ U R P H i a A) : ActualCover F ζ hζ → ℂ := fun g =>
  if hg : piTilde F ζ hζ U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) ∈
      q F ζ hζ U ⁻¹'
        KPContSectorPhaseComponentCharts.baseChartImage F ζ hζ U R P H i a A then
    localCoveredScalar F ζ hζ U R P H u ⟨_, hg⟩
  else 0

structure GroupChart where
  groupCenter : KPSmoothLocalQuotientCharts.ArchGroup F
  finiteRepresentative : FiniteCover F ζ hζ
  exponential : KPSmoothLocalQuotientCharts.ExponentialChart F groupCenter
  T : KPContLocalNorm.LocalBall (groupDimension F)
  zero_mem : (0 : KPContLocalNorm.Space (groupDimension F)) ∈ T.carrier
  closure_source : groupCoordinates F '' closure T.carrier ⊆ exponential.chart.source
  component : Fin (H.atlas U).componentCount
  rationalComparison : KPCuspArithmetic.PGL2 F
  phase : rootsOfUnity 3 F
  levelComparison : U.toOpenSubgroup
  finite_comparison :
    KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ rationalComparison * finiteRepresentative =
      KPCuspGenuineMonodromy.central F ζ hζ phase *
        (H.atlas U).representative component * levelComparison
  baseCenter : SymmetricSpace F
  baseCenter_actual : baseCenter = rationalComparison •
    KPMsFixedHaarDisintegration.archBasepoint F groupCenter
  A : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H component baseCenter
  baseBall : KPContLocalNorm.LocalBall (baseDimension F)
  baseBall_inside : baseCoordinates F '' closure baseBall.carrier ⊆ A.neighborhood
  image_inside : ∀ x ∈ closure T.carrier,
    (baseCoordinates F).symm (rationalComparison •
      KPMsFixedHaarDisintegration.archBasepoint F
        (exponential.chart (groupCoordinates F x))) ∈ baseBall.carrier

  inverse_smooth :
    letI := actualLieChartedSpace F
    ∃ E : OpenPartialHomeomorph (KPSmoothLocalQuotientCharts.Coordinates F)
        (KPSmoothLocalQuotientCharts.ArchGroup F),
      E.toPartialHomeomorph = exponential.chart ∧
      ContMDiffOn (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
        (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞) E.symm E.target

namespace GroupChart

variable {F ζ hζ U R P H}

def groupLift (D : GroupChart F ζ hζ U R P H)
    (x : KPContLocalNorm.Space (groupDimension F)) : ActualCover F ζ hζ :=
  KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (D.exponential.chart (groupCoordinates F x)) * D.finiteRepresentative

def π (D : GroupChart F ζ hζ U R P H) :
    KPContLocalNorm.Space (groupDimension F) → KPContLocalNorm.Space (baseDimension F) :=
  fun x => (baseCoordinates F).symm (D.rationalComparison •
    KPMsFixedHaarDisintegration.archBasepoint F
      (D.exponential.chart (groupCoordinates F x)))

def frame (D : GroupChart F ζ hζ U R P H) :
    KPContLocalNorm.Space (groupDimension F) → ℂ :=
  fun _ => (chi F ζ hζ D.phase : ℂ)

def fields (D : GroupChart F ζ hζ U R P H) : Fin (groupDimension F) →
    KPContLocalNorm.Space (groupDimension F) → KPContLocalNorm.Space (groupDimension F) :=
  fun b x => (groupCoordinates F).symm
    (KPSmoothLocalQuotientCharts.rightLieField F D.exponential
      (lieEnumeration F b) (groupCoordinates F x))

lemma π_inside_actual_chart (D : GroupChart F ζ hζ U R P H)
    (x : KPContLocalNorm.Space (groupDimension F)) (hx : x ∈ D.T.carrier) :
    baseCoordinates F (D.π x) ∈ D.A.neighborhood := by
  exact D.baseBall_inside ⟨D.π x,
    subset_closure (D.image_inside x (subset_closure hx)), rfl⟩

def sectionExpression (D : GroupChart F ζ hζ U R P H)
    (u : LocalSection F ζ hζ U R P H D.component D.baseCenter D.A) :
    KPContLocalNorm.Space (baseDimension F) → ℂ :=
  fun x => (u.coefficient (baseCoordinates F x) : ℂ)

def piece (D : GroupChart F ζ hζ U R P H)
    (K : Set (KPContLocalNorm.Space (groupDimension F))) : Set (ActualCover F ζ hζ) :=
  {g | ∃ x ∈ K, ∃ u : U.toOpenSubgroup,
    g = D.groupLift x * ((u : FiniteCover F ζ hζ) : ActualCover F ζ hζ)}

end GroupChart

structure Identification (D : GroupChart F ζ hζ U R P H) : Prop where
  relatively_compact : IsCompact (closure D.T.carrier)
  π_smooth : ContDiffOn ℝ (⊤ : ℕ∞) D.π D.T.carrier
  frame_smooth : ContDiffOn ℝ (⊤ : ℕ∞) D.frame D.T.carrier
  frame_unitary : ∀ x ∈ D.T.carrier, ‖D.frame x‖ = 1
  fields_smooth : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (D.fields b) D.T.carrier
  actual_base_chart : ∀ (x : KPContLocalNorm.Space (groupDimension F)) (hx : x ∈ D.T.carrier),
    piTilde F ζ hζ U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (D.groupLift x)) =
      (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H
        D.component D.baseCenter D.A
        (Quotient.mk _ (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U D.phase,
          (⟨baseCoordinates F (D.π x), D.π_inside_actual_chart x hx⟩ : D.A.neighborhood)))).val
  scalar_pullback : ∀ u : LocalSection F ζ hζ U R P H D.component D.baseCenter D.A,
    ∀ x ∈ D.T.carrier,
      sectionGroupLift F ζ hζ U R P H u (D.groupLift x) =
        KPContRightJets.scalarLift D.π D.frame (D.sectionExpression u) x

  global_scalar_pullback : ∀ f : GenuineCoveredScalars F ζ hζ U,
    IsSmoothCovered F ζ hζ U f → ∀ x ∈ D.T.carrier,
      f.val (piTilde F ζ hζ U
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (D.groupLift x))) =
      KPContRightJets.scalarLift D.π D.frame
        (fun y => (S F ζ hζ U R P H f D.component).val (baseCoordinates F y)) x
  scalar_smooth : ∀ u : LocalSection F ζ hζ U R P H D.component D.baseCenter D.A,
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => sectionGroupLift F ζ hζ U R P H u (D.groupLift x)) D.T.carrier
  right_differential : ∀ (f : ActualCover F ζ hζ → ℂ),
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f (D.groupLift x)) D.T.carrier →
    ∀ b, ∀ x ∈ D.T.carrier,
      actualRight F ζ hζ b f (D.groupLift x) =
        fderiv ℝ (fun y => f (D.groupLift y)) x (D.fields b x)
  right_iteration : ∀ (f : ActualCover F ζ hζ → ℂ),
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f (D.groupLift x)) D.T.carrier →
    ∀ w, ∀ x ∈ D.T.carrier,
      actualRightWord F ζ hζ w f (D.groupLift x) =
        KPContRightJets.rightWord D.fields w (fun y => f (D.groupLift y)) x
  compact_image : ∀ K : Set (KPContLocalNorm.Space (groupDimension F)),
    IsCompact K → K ⊆ D.T.carrier →
      IsCompact (D.π '' K) ∧ D.π '' K ⊆ D.baseBall.carrier

section IdentificationProof
set_option backward.isDefEq.respectTransparency false

variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
open scoped Matrix.Norms.Operator

private lemma variable_origin_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hA : ContDiff ℝ (⊤ : ℕ∞) (fun x => (A x : Matrix (Fin 2) (Fin 2) ℂ))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => KPArch.action (A x) (0, 0)) := by
  have he (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j) :=
    (PGLComplex.entry i j).contDiff.comp hA
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x => KPArch.actionDenominator (A x) (0, 0)) := by
    simp only [KPArch.actionDenominator, KPArch.height, Real.exp_zero, one_pow,
      mul_one, mul_zero, zero_add, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    exact (((Complex.reCLM.contDiff.comp (he 1 1)).mul
        (Complex.reCLM.contDiff.comp (he 1 1))).add
      ((Complex.imCLM.contDiff.comp (he 1 1)).mul
        (Complex.imCLM.contDiff.comp (he 1 1)))).add
      (((Complex.reCLM.contDiff.comp (he 1 0)).mul
        (Complex.reCLM.contDiff.comp (he 1 0))).add
        ((Complex.imCLM.contDiff.comp (he 1 0)).mul
          (Complex.imCLM.contDiff.comp (he 1 0))))
  have hdet : ContDiff ℝ (⊤ : ℕ∞) (fun x => ‖(A x : Matrix (Fin 2) (Fin 2) ℂ).det‖) := by
    apply ContDiff.norm (𝕜 := ℝ)
    · simp only [Matrix.det_fin_two]
      exact ((he 0 0).mul (he 1 1)).sub ((he 0 1).mul (he 1 0))
    · exact fun x => (A x).det_ne_zero
  unfold KPArch.action
  apply ContDiff.prodMk
  · simp only [KPArch.height, Real.exp_zero, one_pow, Complex.ofReal_one, mul_one,
      mul_zero, zero_add]
    simp only [div_eq_mul_inv]
    apply ContDiff.mul
    · exact ((he 0 1).mul (Complex.conjCLE.contDiff.comp (he 1 1))).add
        ((he 0 0).mul (Complex.conjCLE.contDiff.comp (he 1 0)))
    · simpa only [Function.comp_def, Pi.inv_apply, Complex.ofRealCLM_apply, Complex.ofReal_inv] using
        Complex.ofRealCLM.contDiff.comp (hd.inv
          (fun x => (KPArch.actionDenominator_pos (A x) (0, 0)).ne'))
  · apply ContDiff.log
    · exact (hdet.mul contDiff_const).div hd
        (fun x => (KPArch.actionDenominator_pos (A x) (0, 0)).ne')
    · intro x
      exact (div_pos (mul_pos (norm_pos_iff.mpr (A x).det_ne_zero)
        (Real.exp_pos _)) (KPArch.actionDenominator_pos (A x) (0, 0))).ne'
private lemma lieMatrix_smooth (w : NumberField.InfinitePlace F) :
    ContDiff ℝ (⊤ : ℕ∞) (KPSmoothLocalQuotientCharts.lieMatrix F · w) := by
  let L : KPSmoothLocalQuotientCharts.Coordinates F →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    { toFun := fun a => KPSmoothLocalQuotientCharts.lieMatrix F a w
      map_add' := by
        intro a b
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [KPSmoothLocalQuotientCharts.lieMatrix] <;> apply Complex.ext <;> simp [add_comm]
      map_smul' := by
        intro r a
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [KPSmoothLocalQuotientCharts.lieMatrix] <;> apply Complex.ext <;> simp [add_comm] }
  exact L.toContinuousLinearMap.contDiff

 lemma exponential_base_smooth (g : KPSmoothLocalQuotientCharts.ArchGroup F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a => KPMsFixedHaarDisintegration.archBasepoint F
      (g * KPSmoothLocalQuotientCharts.matrixExp F a)) := by
  apply contDiff_pi.mpr
  intro i
  let w := KPCusp.complexPlace F i
  let A : KPSmoothLocalQuotientCharts.Coordinates F → Matrix.GeneralLinearGroup (Fin 2) ℂ :=
    fun a => (g w).out * ((NormedSpace.isUnit_exp
      (KPSmoothLocalQuotientCharts.lieMatrix F a w)).unit)
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun a => (A a : Matrix (Fin 2) (Fin 2) ℂ)) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun a => (g w).out.val *
      NormedSpace.exp (KPSmoothLocalQuotientCharts.lieMatrix F a w))
    have hex : ContDiff ℝ (⊤ : ℕ∞) (fun a =>
        NormedSpace.exp (KPSmoothLocalQuotientCharts.lieMatrix F a w)) := by
      apply contDiff_iff_contDiffAt.mpr
      intro a
      exact ((NormedSpace.exp_analytic (𝕂 := ℝ)
        (KPSmoothLocalQuotientCharts.lieMatrix F a w)).contDiffAt).comp a
        ((lieMatrix_smooth w).contDiffAt)
    exact contDiff_const.mul hex
  have hp (a) : (g * KPSmoothLocalQuotientCharts.matrixExp F a) w =
      Matrix.ProjGenLinGroup.mk (A a) := by
    simp only [Pi.mul_apply, KPSmoothLocalQuotientCharts.matrixExp, A, map_mul]
    exact congrArg (· * _) (Quotient.out_eq (g w)).symm
  have he : (fun a => KPMsFixedHaarDisintegration.archBasepoint F
      (g * KPSmoothLocalQuotientCharts.matrixExp F a) i) =
        (fun a => KPArch.action (A a) (0, 0)) := by
    funext a
    change KPArch.action ((g * KPSmoothLocalQuotientCharts.matrixExp F a) w).out (0, 0) = _
    rw [hp]
    exact KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.projective_action_mk
      (A a) (0, 0)
  rw [he]
  exact variable_origin_smooth A hA

namespace GroupChart
lemma π_smooth (D : GroupChart F ζ hζ U R P H) :
    ContDiffOn ℝ (⊤ : ℕ∞) D.π D.T.carrier := by
  have hs := (baseCoordinates F).symm.contDiff.comp
    ((CoreChartLocalizers.CutoffConstruction.StabilizerLinearization.rational_action_contDiff
      F D.rationalComparison).comp (exponential_base_smooth D.groupCenter)) |>.comp
        (groupCoordinates F).contDiff
  apply hs.contDiffOn.congr
  intro x hx
  rw [π, D.exponential.exponential_formula (groupCoordinates F x)
    (D.closure_source ⟨x, subset_closure hx, rfl⟩)]
  rfl

lemma actual_base_chart (D : GroupChart F ζ hζ U R P H)
    (x : KPContLocalNorm.Space (groupDimension F)) (hx : x ∈ D.T.carrier) :
    piTilde F ζ hζ U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (D.groupLift x)) =
      (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H
        D.component D.baseCenter D.A
        (Quotient.mk _ (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U D.phase,
          (⟨baseCoordinates F (D.π x), D.π_inside_actual_chart x hx⟩ : D.A.neighborhood)))).val := by
  rw [groupLift, piTilde_quotientMap, KPContSectorPhaseComponentCharts.coveredChart_mk]
  apply Quotient.sound
  refine ⟨D.rationalComparison, D.levelComparison⁻¹, ?_, ?_⟩
  · simp [π]
  · rw [D.finite_comparison]
    simp
lemma scalar_pullback (D : GroupChart F ζ hζ U R P H)
    (u : LocalSection F ζ hζ U R P H D.component D.baseCenter D.A)
    (x : KPContLocalNorm.Space (groupDimension F)) (hx : x ∈ D.T.carrier) :
    sectionGroupLift F ζ hζ U R P H u (D.groupLift x) =
      KPContRightJets.scalarLift D.π D.frame (D.sectionExpression u) x := by
  let p : KPContSectorPhaseComponentCharts.CoveredChartDomain F ζ hζ U R P H
      D.component D.baseCenter D.A := Quotient.mk _
      (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U D.phase,
        (⟨baseCoordinates F (D.π x), D.π_inside_actual_chart x hx⟩ : D.A.neighborhood))
  let v := KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H
      D.component D.baseCenter D.A p
  have hv : piTilde F ζ hζ U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (D.groupLift x)) = v.val :=
    D.actual_base_chart x hx
  have hm : piTilde F ζ hζ U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (D.groupLift x)) ∈
      q F ζ hζ U ⁻¹' KPContSectorPhaseComponentCharts.baseChartImage F ζ hζ U R P H
        D.component D.baseCenter D.A := hv.symm ▸ v.property
  rw [sectionGroupLift, dif_pos hm]
  have he : (⟨_, hm⟩ : q F ζ hζ U ⁻¹'
      KPContSectorPhaseComponentCharts.baseChartImage F ζ hζ U R P H D.component D.baseCenter D.A) = v :=
    Subtype.ext hv
  rw [he]
  simp only [localCoveredScalar, v, Homeomorph.symm_apply_apply]
  simp only [p, KPContSectorPhaseComponentCharts.phaseClass, Quotient.lift_mk,
    phaseTransport_apply, KPContRightJets.scalarLift, frame, sectionExpression]
  rfl

lemma global_scalar_pullback (D : GroupChart F ζ hζ U R P H)
    (f : GenuineCoveredScalars F ζ hζ U)
    (x : KPContLocalNorm.Space (groupDimension F)) (hx : x ∈ D.T.carrier) :
    f.val (piTilde F ζ hζ U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (D.groupLift x))) =
      KPContRightJets.scalarLift D.π D.frame
        (fun y => (S F ζ hζ U R P H f D.component).val (baseCoordinates F y)) x := by
  rw [D.actual_base_chart x hx, KPContSectorPhaseComponentCharts.coveredChart_mk,
    ← z_mk, f.property]
  simp only [KPContRightJets.scalarLift, frame, S_apply]

lemma relatively_compact (D : GroupChart F ζ hζ U R P H) :
    IsCompact (closure D.T.carrier) := by
  rw [KPContLocalNorm.LocalBall.carrier, closure_ball _ D.T.radius_pos.ne']
  exact isCompact_closedBall _ _

lemma frame_smooth (D : GroupChart F ζ hζ U R P H) :
    ContDiffOn ℝ (⊤ : ℕ∞) D.frame D.T.carrier := contDiffOn_const

lemma frame_unitary (D : GroupChart F ζ hζ U R P H)
    (x : KPContLocalNorm.Space (groupDimension F)) : ‖D.frame x‖ = 1 :=
  chi_norm F ζ hζ D.phase

lemma compact_image (D : GroupChart F ζ hζ U R P H)
    (hπ : ContDiffOn ℝ (⊤ : ℕ∞) D.π D.T.carrier)
    (K : Set (KPContLocalNorm.Space (groupDimension F)))
    (hK : IsCompact K) (hKT : K ⊆ D.T.carrier) :
    IsCompact (D.π '' K) ∧ D.π '' K ⊆ D.baseBall.carrier := by
  refine ⟨hK.image_of_continuousOn (hπ.continuousOn.mono hKT), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact D.image_inside x (subset_closure (hKT hx))

lemma scalar_smooth (D : GroupChart F ζ hζ U R P H)
    (hπ : ContDiffOn ℝ (⊤ : ℕ∞) D.π D.T.carrier)
    (u : LocalSection F ζ hζ U R P H D.component D.baseCenter D.A) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => sectionGroupLift F ζ hζ U R P H u (D.groupLift x)) D.T.carrier := by
  have hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => baseCoordinates F (D.π x)) D.T.carrier :=
    (baseCoordinates F).contDiff.comp_contDiffOn hπ
  have hs := u.smooth.comp hp (fun x hx => D.π_inside_actual_chart x hx)
  apply (D.frame_smooth.mul hs).congr
  intro x hx
  exact D.scalar_pullback u x hx
lemma fields_smooth (D : GroupChart F ζ hζ U R P H)
    (hs : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞)
      (KPSmoothLocalQuotientCharts.rightLieField F D.exponential b) D.exponential.chart.source)
    (b : Fin (groupDimension F)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (D.fields b) D.T.carrier := by
  apply (groupCoordinates F).symm.contDiff.comp_contDiffOn
  exact (hs (lieEnumeration F b)).comp (groupCoordinates F).contDiff.contDiffOn
    (fun x hx => D.closure_source ⟨x, subset_closure hx, rfl⟩)

lemma right_iteration_of_differential (D : GroupChart F ζ hζ U R P H)
    (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (D.fields b) D.T.carrier)
    (hd : ∀ (f : KPContSectorCoveredQuotientVocabulary.ActualCover F ζ hζ → ℂ),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f (D.groupLift x)) D.T.carrier →
      ∀ b, ∀ x ∈ D.T.carrier,
        actualRight F ζ hζ b f (D.groupLift x) =
          fderiv ℝ (fun y => f (D.groupLift y)) x (D.fields b x))
    (f : KPContSectorCoveredQuotientVocabulary.ActualCover F ζ hζ → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f (D.groupLift x)) D.T.carrier)
    (w : List (Fin (groupDimension F))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => actualRightWord F ζ hζ w f (D.groupLift x)) D.T.carrier ∧
    (∀ x ∈ D.T.carrier, actualRightWord F ζ hζ w f (D.groupLift x) =
      KPContRightJets.rightWord D.fields w (fun y => f (D.groupLift y)) x) := by
  induction w with
  | nil => exact ⟨hf, fun _ _ => rfl⟩
  | cons b w ih =>
    have hs := (ih.1.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply (hfields b)
    have he : ∀ x ∈ D.T.carrier,
        actualRightWord F ζ hζ (b :: w) f (D.groupLift x) =
          fderiv ℝ (fun y => actualRightWord F ζ hζ w f (D.groupLift y)) x (D.fields b x) :=
      hd (actualRightWord F ζ hζ w f) ih.1 b
    refine ⟨hs.congr he, ?_⟩
    intro x hx
    rw [he x hx, KPContRightJets.rightWord]
    congr 1
    exact Filter.EventuallyEq.fderiv_eq
      (Filter.eventuallyEq_iff_exists_mem.mpr ⟨D.T.carrier,
        Metric.isOpen_ball.mem_nhds hx, ih.2⟩)
private lemma inverse_curve (D : GroupChart F ζ hζ U R P H)
    (O : OpenPartialHomeomorph (KPSmoothLocalQuotientCharts.Coordinates F)
      (KPSmoothLocalQuotientCharts.ArchGroup F))
    (he : O.toPartialHomeomorph = D.exponential.chart)
    (hi : letI := actualLieChartedSpace F
      ContMDiffOn (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
        (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞) O.symm O.target)
    (b : Fin (groupDimension F)) (x : KPSmoothLocalQuotientCharts.Coordinates F)
    (hx : x ∈ D.exponential.chart.source) :
    DifferentiableAt ℝ (fun t : ℝ => D.exponential.chart.symm
        (D.exponential.chart x * KPSmoothLocalQuotientCharts.matrixExp F
          (t • Pi.single (lieEnumeration F b) 1))) 0 := by
  letI := actualLieChartedSpace F
  letI := actualLieGroup F
  have hsx : x ∈ O.source := he.symm ▸ hx
  have hex0 : KPSmoothLocalQuotientCharts.matrixExp F 0 = 1 := by
    simpa only [actualLieData_exponential] using (actualLieData F).exponential_zero
  have ht : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞)
      (fun t : ℝ => O x * KPSmoothLocalQuotientCharts.matrixExp F
        (t • Pi.single (lieEnumeration F b) 1)) := by
    have hex : ContMDiff (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
        (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞)
        (KPSmoothLocalQuotientCharts.matrixExp F) := by
      simpa only [actualLieData_exponential] using (actualLieData F).exponential_smooth
    exact contMDiff_const.mul (hex.comp ((contDiff_id.smul contDiff_const).contMDiff))
  have h0 : O x * KPSmoothLocalQuotientCharts.matrixExp F
      ((0 : ℝ) • Pi.single (lieEnumeration F b) 1) ∈ O.target := by
    simpa only [zero_smul, hex0, mul_one] using O.map_source hsx
  have hs := (hi.contMDiffAt (O.open_target.mem_nhds h0)).comp 0 ht.contMDiffAt
  rw [← he]
  exact hs.contDiffAt.differentiableAt (by simp)

private lemma fields_smooth_of_inverse (D : GroupChart F ζ hζ U R P H)
    (O : OpenPartialHomeomorph (KPSmoothLocalQuotientCharts.Coordinates F)
      (KPSmoothLocalQuotientCharts.ArchGroup F))
    (he : O.toPartialHomeomorph = D.exponential.chart)
    (hi : letI := actualLieChartedSpace F
      ContMDiffOn (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
        (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞) O.symm O.target) :
    ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (D.fields b) D.T.carrier := by
  letI := actualLieChartedSpace F
  letI := actualLieGroup F
  have hex : ContMDiff (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
      (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞)
      (KPSmoothLocalQuotientCharts.matrixExp F) := by
    simpa only [actualLieData_exponential] using (actualLieData F).exponential_smooth
  have hex0 : KPSmoothLocalQuotientCharts.matrixExp F 0 = 1 := by
    simpa only [actualLieData_exponential] using (actualLieData F).exponential_zero
  have hO : ContMDiffOn (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
      (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞) O O.source := by
    apply ((contMDiff_const (c := D.groupCenter)).mul hex).contMDiffOn.congr
    intro a ha
    have h : a ∈ D.exponential.chart.source := he ▸ ha
    have hf := D.exponential.exponential_formula a h
    rw [← he] at hf
    exact hf
  apply D.fields_smooth
  intro b
  unfold KPSmoothLocalQuotientCharts.rightLieField
  rw [← he]
  change ContDiffOn ℝ (⊤ : ℕ∞)
    (fun a => deriv (fun t : ℝ => O.symm
      (O a * KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single b 1))) 0) O.source
  intro a ha
  let f : KPSmoothLocalQuotientCharts.Coordinates F → ℝ →
      KPSmoothLocalQuotientCharts.Coordinates F := fun x t => O.symm
        (O x * KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single b 1))
  have hEa := hO.contMDiffAt (O.open_source.mem_nhds ha)
  have hEi := hi.contMDiffAt (O.open_target.mem_nhds (O.map_source ha))
  have hprod : ContMDiffAt ((𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞)
      (Function.uncurry f) (a, 0) := by
    have hx := hEa.comp (a, (0 : ℝ))
      (contMDiffAt_fst (I := 𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (J := 𝓘(ℝ, ℝ)))
    have ht : ContMDiffAt ((𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)).prod (𝓘(ℝ, ℝ)))
        (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞)
        (fun p : KPSmoothLocalQuotientCharts.Coordinates F × ℝ => p.2 • Pi.single b 1) (a, 0) :=
      (contMDiffAt_snd (I := 𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (J := 𝓘(ℝ, ℝ))).smul
        (contMDiffAt_const (I := (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)).prod (𝓘(ℝ, ℝ)))
          (I' := 𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (c := Pi.single b 1))
    exact hEi.comp_of_eq (hx.mul (hex.contMDiffAt.comp (a, (0 : ℝ)) ht))
      (by simp [hex0])
  have hd := ContMDiffAt.mfderiv (m := (⊤ : ℕ∞)) f
    (fun _ : KPSmoothLocalQuotientCharts.Coordinates F => (0 : ℝ))
    hprod contMDiffAt_const (by simp)
  simp +unfoldPartialApp only [inTangentCoordinates,
    inCoordinates_tangent_bundle_core_model_space] at hd
  have hd' := hd.clm_apply (contMDiffAt_const (c := (1 : ℝ)))
  have hd'' : ContMDiffAt (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
      (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞)
      (fun x => deriv (f x) 0) a := by
    convert hd' using 1
    funext x
    rw [mfderiv_eq_fderiv]
    rfl
  exact hd''.contDiffAt.contDiffWithinAt
private lemma differential_of_inverse (D : GroupChart F ζ hζ U R P H)
    (hopen : IsOpen D.exponential.chart.target)
    (hcurve : ∀ b x, x ∈ D.exponential.chart.source →
      DifferentiableAt ℝ (fun t : ℝ => D.exponential.chart.symm
        (D.exponential.chart x * KPSmoothLocalQuotientCharts.matrixExp F
          (t • Pi.single (lieEnumeration F b) 1))) 0)
    (f : ActualCover F ζ hζ → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f (D.groupLift x)) D.T.carrier)
    (b : Fin (groupDimension F)) (x : KPContLocalNorm.Space (groupDimension F))
    (hx : x ∈ D.T.carrier) : actualRight F ζ hζ b f (D.groupLift x) =
      fderiv ℝ (fun y => f (D.groupLift y)) x (D.fields b x) := by
  let y := groupCoordinates F x
  have hy : y ∈ D.exponential.chart.source := D.closure_source ⟨x, subset_closure hx, rfl⟩
  let c : ℝ → KPSmoothLocalQuotientCharts.Coordinates F := fun t => D.exponential.chart.symm
    (D.exponential.chart y * KPSmoothLocalQuotientCharts.matrixExp F
      (t • Pi.single (lieEnumeration F b) 1))
  have hex0 : KPSmoothLocalQuotientCharts.matrixExp F 0 = 1 := by
    obtain ⟨C, L, A, he, _, _⟩ :=
      LocalQuotientCharts.ExponentialHaarFrame.raw_lie_exponential_data F
    have he' : A.exponential = KPSmoothLocalQuotientCharts.matrixExp F := he
    simpa only [he'] using A.exponential_zero
  have hc0 : c 0 = y := by
    simp only [c, zero_smul, hex0, mul_one]
    exact D.exponential.chart.left_inv hy
  have hc : HasDerivAt c (KPSmoothLocalQuotientCharts.rightLieField F D.exponential
      (lieEnumeration F b) y) 0 := (hcurve b y hy).hasDerivAt
  let z : ℝ → KPContLocalNorm.Space (groupDimension F) := fun t => (groupCoordinates F).symm (c t)
  have hz0 : z 0 = x := by simp [z, hc0, y]
  have hz : HasDerivAt z (D.fields b x) 0 :=
    (groupCoordinates F).symm.hasFDerivAt.comp_hasDerivAt 0 hc
  have hfd : HasFDerivAt (fun y => f (D.groupLift y))
      (fderiv ℝ (fun y => f (D.groupLift y)) x) (z 0) := by
    rw [hz0]
    exact (hf.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp) |>.hasFDerivAt
  have hcomp := hfd.comp_hasDerivAt 0 hz
  have hsource : ∀ᶠ t in 𝓝 (0 : ℝ), D.exponential.chart y *
      KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single (lieEnumeration F b) 1) ∈
        D.exponential.chart.target := by
    obtain ⟨C, L, A, he, _, _⟩ :=
      LocalQuotientCharts.ExponentialHaarFrame.raw_lie_exponential_data F
    letI := C
    letI := L
    have hm : Continuous (KPSmoothLocalQuotientCharts.matrixExp F) := by
      have he' : A.exponential = KPSmoothLocalQuotientCharts.matrixExp F := he
      simpa only [he'] using A.exponential_smooth.continuous
    have ht : Continuous (fun t : ℝ => D.exponential.chart y *
      KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single (lieEnumeration F b) 1)) :=
        continuous_const.mul (hm.comp (continuous_id.smul continuous_const))
    have h0 : D.exponential.chart y *
        KPSmoothLocalQuotientCharts.matrixExp F ((0 : ℝ) • Pi.single (lieEnumeration F b) 1) ∈
        D.exponential.chart.target := by simpa only [zero_smul, hex0, mul_one] using D.exponential.chart.map_source hy
    exact ht.continuousAt.eventually (hopen.mem_nhds h0)
  have heq : (fun t => f (D.groupLift x * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single (lieEnumeration F b) 1)))) =ᶠ[𝓝 0]
        (fun t => f (D.groupLift (z t))) := by
    filter_upwards [hsource] with t ht
    congr 1
    dsimp [groupLift, z, c, y]
    rw [ContinuousLinearEquiv.apply_symm_apply, D.exponential.chart.right_inv ht]
    rw [(KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
    have hc := KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.insertion_commutes_cover
      F ζ hζ (KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single (lieEnumeration F b) 1))
      D.finiteRepresentative
    rw [mul_assoc, ← hc.eq, ← mul_assoc]
  exact (hcomp.congr_of_eventuallyEq heq).deriv

lemma fields_smooth_actual (D : GroupChart F ζ hζ U R P H) :
    ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (D.fields b) D.T.carrier := by
  obtain ⟨O, he, hi⟩ := D.inverse_smooth
  exact D.fields_smooth_of_inverse O he hi

lemma right_differential (D : GroupChart F ζ hζ U R P H)
    (f : ActualCover F ζ hζ → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f (D.groupLift x)) D.T.carrier)
    (b : Fin (groupDimension F)) (x : KPContLocalNorm.Space (groupDimension F))
    (hx : x ∈ D.T.carrier) :
    actualRight F ζ hζ b f (D.groupLift x) =
      fderiv ℝ (fun y => f (D.groupLift y)) x (D.fields b x) := by
  obtain ⟨O, he, hi⟩ := D.inverse_smooth
  have ho : IsOpen D.exponential.chart.target := he ▸ O.open_target
  exact D.differential_of_inverse ho (fun b y hy => D.inverse_curve O he hi b y hy) f hf b x hx

lemma identification (D : GroupChart F ζ hζ U R P H) :
    Identification F ζ hζ U R P H D := by
  refine
    { relatively_compact := D.relatively_compact
      π_smooth := D.π_smooth
      frame_smooth := D.frame_smooth
      frame_unitary := fun x _ => D.frame_unitary x
      fields_smooth := D.fields_smooth_actual
      actual_base_chart := D.actual_base_chart
      scalar_pullback := D.scalar_pullback
      global_scalar_pullback := fun f _ => D.global_scalar_pullback f
      scalar_smooth := D.scalar_smooth D.π_smooth
      right_differential := D.right_differential
      right_iteration := ?_
      compact_image := D.compact_image D.π_smooth }
  intro f hf w
  exact (D.right_iteration_of_differential D.fields_smooth_actual
    D.right_differential f hf w).2

end GroupChart

open scoped Manifold ContDiff

end IdentificationProof

section GeometricExistence
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

lemma groupDimension_pos : 0 < groupDimension F := by
  exact Fintype.card_pos
include ζ hζ in
lemma baseDimension_pos : 0 < baseDimension F := by
  have hd := KPCuspLogShape.dimension_pos F (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).1
  letI : Nonempty (Fin (KPCuspLogShape.dimension F)) := ⟨⟨0, hd⟩⟩
  exact Module.finrank_pos
lemma finite_comparison_exists (c : FiniteCover F ζ hζ) :
    ∃ i : Fin (H.atlas U).componentCount, ∃ γ : KPCuspArithmetic.PGL2 F,
      ∃ ε : rootsOfUnity 3 F, ∃ u : U.toOpenSubgroup,
      KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ * c =
        KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative i * u := by
  obtain ⟨⟨i, y⟩, hy⟩ := (H.atlas U).components.surjective
    (Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
      ((fun _ => (0,0)), c))
  obtain ⟨x, rfl⟩ := Quotient.exists_rep y
  rw [(H.atlas U).components_formula] at hy
  obtain ⟨γ, ε, u, _, hc⟩ := Quotient.exact hy
  change c = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
    KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative i * u at hc
  refine ⟨i, γ⁻¹, ε, u, ?_⟩
  rw [hc, map_inv]
  group
lemma chart_at_split (g : KPSmoothLocalQuotientCharts.ArchGroup F)
    (c : FiniteCover F ζ hζ) :
    ∃ D : GroupChart F ζ hζ U R P H,
      D.groupLift 0 = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ g * c := by
  obtain ⟨i, γ, ε, u, hfinite⟩ := finite_comparison_exists F ζ hζ U R P H c
  let a : SymmetricSpace F := γ • KPMsFixedHaarDisintegration.archBasepoint F g
  obtain ⟨A⟩ := KPContSectorPhaseComponentCharts.orbifoldChart_exists F ζ hζ U R P H i a
  letI := actualLieChartedSpace F
  letI := actualLieGroup F
  obtain ⟨E, O, he, _, hi, _⟩ := chosen_actual_exponential_chart F g
  let z := (baseCoordinates F).symm a
  have hn : (baseCoordinates F ⁻¹' A.neighborhood) ∈ 𝓝 z :=
    (baseCoordinates F).continuous.continuousAt.preimage_mem_nhds
      (A.isOpen.mem_nhds (by simpa [z] using A.center_mem))
  obtain ⟨r, hr, hrc⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hn
  let B : KPContLocalNorm.LocalBall (baseDimension F) :=
    ⟨baseDimension_pos F ζ hζ, z, r, hr⟩
  have hb : baseCoordinates F '' closure B.carrier ⊆ A.neighborhood := by
    rintro _ ⟨x, hx, rfl⟩
    apply hrc
    simpa only [KPContLocalNorm.LocalBall.carrier, B, closure_ball _ hr.ne'] using hx
  let p : KPContLocalNorm.Space (groupDimension F) → KPContLocalNorm.Space (baseDimension F) :=
    fun x => (baseCoordinates F).symm (γ • KPMsFixedHaarDisintegration.archBasepoint F
      (O (groupCoordinates F x)))
  have hex0 : KPSmoothLocalQuotientCharts.matrixExp F 0 = 1 := by
    simpa only [actualLieData_exponential] using (actualLieData F).exponential_zero
  have hO0 : O 0 = g := by
    have hh := E.exponential_formula 0 E.zero_mem
    rw [← he] at hh
    change O 0 = g * KPSmoothLocalQuotientCharts.matrixExp F 0 at hh
    simpa only [hex0, mul_one] using hh
  have hp0 : p 0 = z := by simp [p, hO0, z, a]
  have hs0 : (0 : KPContLocalNorm.Space (groupDimension F)) ∈
      groupCoordinates F ⁻¹' O.source := by simpa only [Set.mem_preimage, map_zero, he] using E.zero_mem
  have hsopen : IsOpen (groupCoordinates F ⁻¹' O.source) :=
    O.open_source.preimage (groupCoordinates F).continuous
  have hp : ContinuousAt p 0 := by
    apply (baseCoordinates F).symm.continuous.continuousAt.comp
    apply (CoreChartLocalizers.CutoffConstruction.StabilizerLinearization.rational_action_contDiff
      F γ).continuous.continuousAt.comp
    apply (KPContSectorArchSphericalFibers.archBasepoint_continuous F).continuousAt.comp
    exact (O.continuousOn.continuousAt (O.open_source.mem_nhds (by simpa using hs0))).comp
      (groupCoordinates F).continuous.continuousAt
  have hpB : p ⁻¹' B.carrier ∈ 𝓝 (0 : KPContLocalNorm.Space (groupDimension F)) :=
    hp.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (by simpa [B, hp0, KPContLocalNorm.LocalBall.carrier] using hr))
  obtain ⟨s, hs, hsc⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (Filter.inter_mem (hsopen.mem_nhds hs0) hpB)
  let T : KPContLocalNorm.LocalBall (groupDimension F) := ⟨groupDimension_pos F, 0, s, hs⟩
  have ht : closure T.carrier ⊆ groupCoordinates F ⁻¹' O.source ∩ p ⁻¹' B.carrier := by
    simpa only [T, KPContLocalNorm.LocalBall.carrier, closure_ball _ hs.ne'] using hsc
  let D : GroupChart F ζ hζ U R P H :=
    { groupCenter := g
      finiteRepresentative := c
      exponential := E
      T := T
      zero_mem := by simpa [T, KPContLocalNorm.LocalBall.carrier] using hs
      closure_source := by
        rintro _ ⟨x, hx, rfl⟩
        rw [← he]
        exact (ht hx).1
      component := i
      rationalComparison := γ
      phase := ε
      levelComparison := u
      finite_comparison := hfinite
      baseCenter := a
      baseCenter_actual := rfl
      A := A
      baseBall := B
      baseBall_inside := hb
      image_inside := by
        intro x hx
        rw [← he]
        exact (ht hx).2
      inverse_smooth := ⟨O, he, hi⟩ }
  refine ⟨D, ?_⟩
  change KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (E.chart (groupCoordinates F 0)) * c = _
  rw [map_zero, ← he]
  change KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (O 0) * c = _
  rw [hO0]
lemma chart_at_point (g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :
    ∃ D : GroupChart F ζ hζ U R P H, D.groupLift 0 = g := by
  obtain ⟨e, he, _⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  let v := e.symm g
  have hf : v.2.val ∈ FiniteCover F ζ hζ := by
    change v.2.val ∈ KPFiniteCuspAtlas.FiniteCover F ζ hζ
    rw [← KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_finiteSubgroup_eq F ζ hζ]
    exact v.2.property
  obtain ⟨D, hD⟩ := chart_at_split F ζ hζ U R P H v.1 ⟨v.2.val, hf⟩
  refine ⟨D, hD.trans ?_⟩
  exact (he v.1 v.2).symm.trans (e.apply_symm_apply g)

end GeometricExistence

section CompactRefinement
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

namespace GroupChart
lemma groupLift_continuous (D : GroupChart F ζ hζ U R P H) :
    ContinuousOn D.groupLift D.T.carrier := by
  have he : ContinuousOn (fun x => D.exponential.chart (groupCoordinates F x)) D.T.carrier :=
    D.exponential.chart.continuousOn.comp (groupCoordinates F).continuous.continuousOn
      (fun x hx => D.closure_source ⟨x, subset_closure hx, rfl⟩)
  exact (((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.continuousOn).comp
    he (fun _ _ => Set.mem_univ _)).mul_const _
lemma piece_compact (D : GroupChart F ζ hζ U R P H)
    (K : Set (KPContLocalNorm.Space (groupDimension F))) (hK : IsCompact K)
    (hKT : K ⊆ D.T.carrier) : IsCompact (D.piece K) := by
  have hu : IsCompact (Set.univ : Set U.toOpenSubgroup) := by
    exact isCompact_iff_compactSpace.mp U.isCompact |>.isCompact_univ
  have heq : D.piece K = (fun p : KPContLocalNorm.Space (groupDimension F) × U.toOpenSubgroup =>
      D.groupLift p.1 * ((p.2 : FiniteCover F ζ hζ) : ActualCover F ζ hζ)) ''
      (K ×ˢ Set.univ) := by
    ext g
    constructor
    · rintro ⟨x, hx, u, rfl⟩
      exact ⟨(x,u), ⟨hx, Set.mem_univ _⟩, rfl⟩
    · rintro ⟨⟨x,u⟩, ⟨hx,_⟩, rfl⟩
      exact ⟨x, hx, u, rfl⟩
  rw [heq]
  apply (hK.prod hu).image_of_continuousOn
  exact ((D.groupLift_continuous.mono hKT).comp continuous_fst.continuousOn
    (fun p hp => hp.1)).mul
      ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd).continuousOn
lemma piece_nhds (D : GroupChart F ζ hζ U R P H)
    (K : Set (KPContLocalNorm.Space (groupDimension F)))
    (hK0 : K ∈ 𝓝 (0 : KPContLocalNorm.Space (groupDimension F)))
    (hKT : K ⊆ D.T.carrier) : D.piece K ∈ 𝓝 (D.groupLift 0) := by
  obtain ⟨O, heO, _⟩ := D.inverse_smooth
  have hex : ∃ e : (KPSmoothLocalQuotientCharts.ArchGroup F × FiniteCover F ζ hζ) ≃ₜ*
      ActualCover F ζ hζ,
      ∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c := by
    have hsub := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_finiteSubgroup_eq F ζ hζ
    have hh := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
    rw [hsub] at hh
    obtain ⟨e,he,_⟩ := hh
    exact ⟨e,he⟩
  obtain ⟨e,he⟩ := hex
  let V := O '' (groupCoordinates F '' K)
  have hs : groupCoordinates F '' K ⊆ O.source := by
    rintro _ ⟨x, hx, rfl⟩
    have hh := D.closure_source ⟨x, subset_closure (hKT hx), rfl⟩
    simpa only [← heO] using hh
  have hcoord : groupCoordinates F '' K ∈ 𝓝 (groupCoordinates F 0) :=
    (groupCoordinates F).toHomeomorph.isOpenMap.image_mem_nhds hK0
  have hV : V ∈ 𝓝 (O (groupCoordinates F 0)) := by
    rw [← O.map_nhds_eq (hs ⟨0, mem_of_mem_nhds hK0, rfl⟩)]
    apply Filter.mem_map.mpr
    exact Filter.mem_of_superset hcoord (Set.subset_preimage_image _ _)
  have hU : (fun u : FiniteCover F ζ hζ => D.finiteRepresentative * u) ''
      (U.toOpenSubgroup : Set (FiniteCover F ζ hζ)) ∈ 𝓝 D.finiteRepresentative := by
    have h := (Homeomorph.mulLeft D.finiteRepresentative).isOpenMap _ U.toOpenSubgroup.isOpen
    apply h.mem_nhds
    exact ⟨1, U.toOpenSubgroup.one_mem, mul_one _⟩
  have hprod := Filter.prod_mem_prod hV hU
  have himg : e '' (V ×ˢ ((fun u : FiniteCover F ζ hζ => D.finiteRepresentative * u) ''
      (U.toOpenSubgroup : Set (FiniteCover F ζ hζ)))) ∈
      𝓝 (e (O (groupCoordinates F 0), D.finiteRepresentative)) := by
    exact e.toHomeomorph.isOpenMap.image_mem_nhds (by simpa only [nhds_prod_eq] using hprod)
  have hcenter : e (O (groupCoordinates F 0), D.finiteRepresentative) = D.groupLift 0 := by
    rw [he]
    rw [groupLift, ← heO]
    rfl
  rw [hcenter] at himg
  apply Filter.mem_of_superset himg
  rintro g ⟨⟨a,c⟩, ⟨ha,hc⟩, rfl⟩
  obtain ⟨v, ⟨x,hx,rfl⟩, rfl⟩ := ha
  obtain ⟨u, hu, rfl⟩ := hc
  refine ⟨x,hx,⟨u,hu⟩,?_⟩
  rw [he, groupLift, ← heO]
  change _ = (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (O (groupCoordinates F x)) *
    (D.finiteRepresentative : ActualCover F ζ hζ)) * (u : ActualCover F ζ hζ)
  simp only [Subgroup.coe_mul, mul_assoc]
lemma compact_piece_nhds (D : GroupChart F ζ hζ U R P H) :
    ∃ K : Set (KPContLocalNorm.Space (groupDimension F)),
      IsCompact K ∧ K ⊆ D.T.carrier ∧ IsCompact (D.piece K) ∧
      D.piece K ∈ 𝓝 (D.groupLift 0) := by
  obtain ⟨r,hr,hrT⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (Metric.isOpen_ball.mem_nhds D.zero_mem)
  let K := Metric.closedBall (0 : KPContLocalNorm.Space (groupDimension F)) r
  exact ⟨K, isCompact_closedBall _ _, hrT,
    D.piece_compact K (isCompact_closedBall _ _) hrT,
    D.piece_nhds K (Metric.closedBall_mem_nhds _ hr) hrT⟩
end GroupChart

variable (F ζ hζ U R P H)

end CompactRefinement

end DedekindZetaZeroFree.KPContActualSphericalRightFieldIdentification

namespace DedekindZetaZeroFree

open KPContActualSphericalRightFieldIdentification

end DedekindZetaZeroFree

end
