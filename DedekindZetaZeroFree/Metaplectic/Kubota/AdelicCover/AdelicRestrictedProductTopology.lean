module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicCover.RationalSection
public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicCover.PGLAmalgamationTopology

@[expose] public section

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPAdelicCoverRestrictedProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def depth (q : HeightOneSpectrum (𝓞 F)) : ℕ :=
  (KPLocalChartTopology.deep_chart_topology F ζ hζ q).choose

theorem depth_admissible (q : HeightOneSpectrum (𝓞 F)) :
    KPLocalChartTopology.MatrixChartDepth F q (depth F ζ hζ q) :=
  (KPLocalChartTopology.deep_chart_topology F ζ hζ q).choose_spec.1

def localTopology (v : KPHilbert.Place F) :
    TopologicalSpace (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
  match v with
  | Sum.inl w => KPLocalChartTopology.complexTopology F ζ hζ w
  | Sum.inr q => KPLocalChartTopology.translatedTopology F ζ hζ q (depth F ζ hζ q)

attribute [local instance] localTopology

def Bad (q : HeightOneSpectrum (𝓞 F)) : Prop :=
  ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) = 2 ∨
    ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) = 3

theorem bad_finite : {q : HeightOneSpectrum (𝓞 F) | Bad F q}.Finite := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.bad_finite F

theorem deepLift_mul (q : HeightOneSpectrum (𝓞 F))
    (g h : KPLocalCube.Gamma F q (depth F ζ hζ q)) :
    KPLocalCover.sectionMap F ζ hζ (Sum.inr q) (g * h).val =
      KPLocalCover.sectionMap F ζ hζ (Sum.inr q) g.val *
        KPLocalCover.sectionMap F ζ hζ (Sum.inr q) h.val := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.deepLift_mul F ζ hζ q g h

def deepLift (q : HeightOneSpectrum (𝓞 F)) :
    KPLocalCube.Gamma F q (depth F ζ hζ q) →*
      KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q) where
  toFun g := KPLocalCover.sectionMap F ζ hζ (Sum.inr q) g.val
  map_one' := rfl
  map_mul' := deepLift_mul F ζ hζ q

def finiteCompact (q : HeightOneSpectrum (𝓞 F)) :
    Subgroup (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :=
  if h : Bad F q then (deepLift F ζ hζ q).range
  else (KPGoodCompactSplitting.kStar F ζ hζ q
    (fun h3 => h (Or.inr h3))).range

def compact (v : KPHilbert.Place F) : Subgroup (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
  match v with
  | Sum.inl _ => ⊤
  | Sum.inr q => finiteCompact F ζ hζ q

abbrev RestrictedCover := RestrictedProduct
  (fun v : KPHilbert.Place F => KPLocalCover.CubicGL2Raw F ζ hζ v)
  (fun v => (compact F ζ hζ v : Set _)) Filter.cofinite

instance restrictedTopology : TopologicalSpace (RestrictedCover F ζ hζ) :=
  inferInstanceAs (TopologicalSpace (RestrictedProduct
    (fun v : KPHilbert.Place F => KPLocalCover.CubicGL2Raw F ζ hζ v)
    (fun v => (compact F ζ hζ v : Set _)) Filter.cofinite))

def localToRestricted (v : KPHilbert.Place F) :
    KPLocalCover.CubicGL2Raw F ζ hζ v →* RestrictedCover F ζ hζ :=
  RestrictedProduct.mulSingleMonoidHom (compact F ζ hζ) v

abbrev CentralTuples := RestrictedProduct
  (fun _ : KPHilbert.Place F => rootsOfUnity 3 F)
  (fun _ => ((⊥ : Subgroup (rootsOfUnity 3 F)) : Set _)) Filter.cofinite

theorem centralTuples_finiteSupport (ε : CentralTuples F) :
    Function.HasFiniteMulSupport (fun v => ε v) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.centralTuples_finiteSupport F ε

def centralProduct : CentralTuples F →* rootsOfUnity 3 F where
  toFun ε := ∏ᶠ v, ε v
  map_one' := by simp
  map_mul' ε δ := finprod_mul_distrib
    (centralTuples_finiteSupport F ε) (centralTuples_finiteSupport F δ)

def centralTupleMap : CentralTuples F →* RestrictedCover F ζ hζ :=
  RestrictedProduct.mapAlongMonoidHom _ _ id Filter.tendsto_id
    (fun v => KPLocalCover.centralInjection F ζ hζ v)
    (Filter.Eventually.of_forall (fun v => by
      intro ε hε
      have : ε = 1 := hε
      simpa [this] using (compact F ζ hζ v).one_mem))

theorem centralTupleMap_central :
    (centralTupleMap F ζ hζ).range ≤ Subgroup.center (RestrictedCover F ζ hζ) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.centralTupleMap_central F ζ hζ

def M : Subgroup (RestrictedCover F ζ hζ) :=
  (centralProduct F).ker.map (centralTupleMap F ζ hζ)

theorem M_central : M F ζ hζ ≤ Subgroup.center (RestrictedCover F ζ hζ) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.M_central F ζ hζ

instance M_normal : (M F ζ hζ).Normal :=
  Subgroup.normal_of_le_center (M_central F ζ hζ)

abbrev CubicGL2Adelic := RestrictedCover F ζ hζ ⧸ M F ζ hζ

def amalgamation : RestrictedCover F ζ hζ →* CubicGL2Adelic F ζ hζ :=
  QuotientGroup.mk' (M F ζ hζ)

def localInjection (v : KPHilbert.Place F) :
    KPLocalCover.CubicGL2Raw F ζ hζ v →* CubicGL2Adelic F ζ hζ :=
  (amalgamation F ζ hζ).comp (localToRestricted F ζ hζ v)

def distinguishedPlace : KPHilbert.Place F :=
  Sum.inl (Classical.choice (inferInstance : Nonempty (InfinitePlace F)))

def centralInjection : rootsOfUnity 3 F →* CubicGL2Adelic F ζ hζ :=
  (localInjection F ζ hζ (distinguishedPlace F)).comp
    (KPLocalCover.centralInjection F ζ hζ (distinguishedPlace F))

theorem localInjection_central (v : KPHilbert.Place F) (ε : rootsOfUnity 3 F) :
    localInjection F ζ hζ v (KPLocalCover.centralInjection F ζ hζ v ε) =
      centralInjection F ζ hζ ε := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.localInjection_central F ζ hζ v ε

abbrev Adeles := NumberField.AdeleRing (𝓞 F) F
abbrev AdelicGL2 := Matrix.GeneralLinearGroup (Fin 2) (Adeles F)

def adeleEval (v : KPHilbert.Place F) : Adeles F →+* KPHilbert.Completion F v :=
  match v with
  | Sum.inl w => (Pi.evalRingHom _ w).comp (RingHom.fst _ _)
  | Sum.inr q => (RestrictedProduct.evalRingHom (fun q : HeightOneSpectrum (𝓞 F) => q.adicCompletion F) q).comp (RingHom.snd _ _)

def matrixEval (v : KPHilbert.Place F) : AdelicGL2 F →* KPLocalCover.LocalGL2 F v :=
  Matrix.GeneralLinearGroup.map (adeleEval F v)

theorem matrixEntry_integral (x : RestrictedCover F ζ hζ) (i j : Fin 2) :
    ∀ᶠ q in Filter.cofinite,
      (x (Sum.inr q)).g i j ∈ q.adicCompletionIntegers F := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.matrixEntry_integral F ζ hζ x i j

def matrixEntry (x : RestrictedCover F ζ hζ) (i j : Fin 2) : Adeles F :=
  (fun w => (x (Sum.inl w)).g i j,
    RestrictedProduct.mk (fun q => (x (Sum.inr q)).g i j)
      (matrixEntry_integral F ζ hζ x i j))

def matrixValue (x : RestrictedCover F ζ hζ) : Matrix (Fin 2) (Fin 2) (Adeles F) :=
  fun i j => matrixEntry F ζ hζ x i j

theorem matrixValue_inv (x : RestrictedCover F ζ hζ) :
    matrixValue F ζ hζ x * matrixValue F ζ hζ x⁻¹ = 1 := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.matrixValue_inv F ζ hζ x

theorem matrixValue_inv_left (x : RestrictedCover F ζ hζ) :
    matrixValue F ζ hζ x⁻¹ * matrixValue F ζ hζ x = 1 := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.matrixValue_inv_left F ζ hζ x

theorem matrixValue_one : matrixValue F ζ hζ 1 = 1 := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.matrixValue_one F ζ hζ

theorem matrixValue_mul (x y : RestrictedCover F ζ hζ) :
    matrixValue F ζ hζ (x * y) = matrixValue F ζ hζ x * matrixValue F ζ hζ y := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.matrixValue_mul F ζ hζ x y

def restrictedProjection : RestrictedCover F ζ hζ →* AdelicGL2 F where
  toFun x := ⟨matrixValue F ζ hζ x, matrixValue F ζ hζ x⁻¹,
    matrixValue_inv F ζ hζ x, matrixValue_inv_left F ζ hζ x⟩
  map_one' := Units.ext (matrixValue_one F ζ hζ)
  map_mul' x y := Units.ext (matrixValue_mul F ζ hζ x y)

theorem restrictedProjection_eval (x : RestrictedCover F ζ hζ) (v : KPHilbert.Place F) :
    matrixEval F v (restrictedProjection F ζ hζ x) =
      KPLocalCover.projection F ζ hζ v (x v) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.restrictedProjection_eval F ζ hζ x v

theorem restrictedProjection_surjective : Function.Surjective (restrictedProjection F ζ hζ) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.restrictedProjection_surjective F ζ hζ

theorem restrictedProjection_continuous : Continuous (restrictedProjection F ζ hζ) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.restrictedProjection_continuous F ζ hζ

theorem M_le_ker : M F ζ hζ ≤ (restrictedProjection F ζ hζ).ker := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.M_le_ker F ζ hζ

def projection : CubicGL2Adelic F ζ hζ →* AdelicGL2 F :=
  QuotientGroup.lift (M F ζ hζ) (restrictedProjection F ζ hζ) (M_le_ker F ζ hζ)

@[simp] theorem projection_amalgamation (x : RestrictedCover F ζ hζ) :
    projection F ζ hζ (amalgamation F ζ hζ x) = restrictedProjection F ζ hζ x := rfl

theorem range_centralInjection_eq_ker :
    (centralInjection F ζ hζ).range = (projection F ζ hζ).ker := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.range_centralInjection_eq_ker F ζ hζ

theorem adelic_topological_cover :
    T2Space (CubicGL2Adelic F ζ hζ) ∧ LocallyCompactSpace (CubicGL2Adelic F ζ hζ) ∧
      IsTopologicalGroup (CubicGL2Adelic F ζ hζ) ∧
      IsLocalHomeomorph (projection F ζ hζ) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.adelic_topological_cover F ζ hζ

theorem projection_localInjection (v w : KPHilbert.Place F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ v) :
    matrixEval F w (projection F ζ hζ (localInjection F ζ hζ v g)) =
      (localToRestricted F ζ hζ v g w).g := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.projection_localInjection F ζ hζ v w g

abbrev Ideles := (Adeles F)ˣ

def scalarCoordinates (z : Ideles F) (v : KPHilbert.Place F) :
    KPLocalCover.CubicGL2Raw F ζ hζ v :=
  KPScalarSplitCentral.scalarHom F ζ hζ v (Units.map (adeleEval F v) z)

theorem scalarTuple_restricted (z : Ideles F) :
    ∀ᶠ v in Filter.cofinite,
      scalarCoordinates F ζ hζ z v ∈ (compact F ζ hζ v : Set _) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.scalarTuple_restricted F ζ hζ z

def scalarTupleValue (z : Ideles F) : RestrictedCover F ζ hζ :=
  ⟨scalarCoordinates F ζ hζ z, scalarTuple_restricted F ζ hζ z⟩

theorem scalarTupleValue_one : scalarTupleValue F ζ hζ 1 = 1 := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.scalarTupleValue_one F ζ hζ

theorem scalarTupleValue_mul (z z' : Ideles F) :
    scalarTupleValue F ζ hζ (z * z') = scalarTupleValue F ζ hζ z * scalarTupleValue F ζ hζ z' := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.scalarTupleValue_mul F ζ hζ z z'

def scalarTuple : Ideles F →* RestrictedCover F ζ hζ where
  toFun := scalarTupleValue F ζ hζ
  map_one' := scalarTupleValue_one F ζ hζ
  map_mul' := scalarTupleValue_mul F ζ hζ

def scalarHom : Ideles F →* CubicGL2Adelic F ζ hζ :=
  (amalgamation F ζ hζ).comp (scalarTuple F ζ hζ)

theorem projection_scalarHom (z : Ideles F) :
    projection F ζ hζ (scalarHom F ζ hζ z) = Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.projection_scalarHom F ζ hζ z

theorem scalarHom_central :
    (scalarHom F ζ hζ).range ≤ Subgroup.center (CubicGL2Adelic F ζ hζ) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.scalarHom_central F ζ hζ

def splitScalarSubgroup : Subgroup (CubicGL2Adelic F ζ hζ) := (scalarHom F ζ hζ).range

instance splitScalarSubgroup_normal : (splitScalarSubgroup F ζ hζ).Normal :=
  Subgroup.normal_of_le_center (scalarHom_central F ζ hζ)

abbrev CubicPGL2Adelic := CubicGL2Adelic F ζ hζ ⧸ splitScalarSubgroup F ζ hζ

def scalarQuotient : CubicGL2Adelic F ζ hζ →* CubicPGL2Adelic F ζ hζ :=
  QuotientGroup.mk' (splitScalarSubgroup F ζ hζ)

def scalarSubgroup : Subgroup (AdelicGL2 F) :=
  (Matrix.GeneralLinearGroup.scalar (Fin 2) : Ideles F →* AdelicGL2 F).range

theorem scalarSubgroup_central : scalarSubgroup F ≤ Subgroup.center (AdelicGL2 F) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.scalarSubgroup_central F

instance scalarSubgroup_normal : (scalarSubgroup F).Normal :=
  Subgroup.normal_of_le_center (scalarSubgroup_central F)

abbrev AdelicPGL2 := AdelicGL2 F ⧸ scalarSubgroup F

theorem splitScalar_le_ker : splitScalarSubgroup F ζ hζ ≤
    ((QuotientGroup.mk' (scalarSubgroup F)).comp (projection F ζ hζ)).ker := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.splitScalar_le_ker F ζ hζ

def pglProjection : CubicPGL2Adelic F ζ hζ →* AdelicPGL2 F :=
  QuotientGroup.lift (splitScalarSubgroup F ζ hζ)
    ((QuotientGroup.mk' (scalarSubgroup F)).comp (projection F ζ hζ))
    (splitScalar_le_ker F ζ hζ)

def pglCentralInjection : rootsOfUnity 3 F →* CubicPGL2Adelic F ζ hζ :=
  (scalarQuotient F ζ hζ).comp (centralInjection F ζ hζ)

theorem pglCentralInjection_injective : Function.Injective (pglCentralInjection F ζ hζ) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.pglCentralInjection_injective F ζ hζ

theorem pglProjection_surjective : Function.Surjective (pglProjection F ζ hζ) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.pglProjection_surjective F ζ hζ

theorem pglCentralInjection_kernel :
    (pglCentralInjection F ζ hζ).range = (pglProjection F ζ hζ).ker := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.pglCentralInjection_kernel F ζ hζ

theorem pglCentralInjection_central :
    (pglCentralInjection F ζ hζ).range ≤ Subgroup.center (CubicPGL2Adelic F ζ hζ) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.pglCentralInjection_central F ζ hζ

theorem adelic_pgl_topological_cover :
    T2Space (CubicPGL2Adelic F ζ hζ) ∧ LocallyCompactSpace (CubicPGL2Adelic F ζ hζ) ∧
      IsTopologicalGroup (CubicPGL2Adelic F ζ hζ) ∧
      IsLocalHomeomorph (pglProjection F ζ hζ) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.adelic_pgl_topological_cover F ζ hζ

def rationalBase : KubotaRankTwo.GL2 F →* AdelicGL2 F :=
  Matrix.GeneralLinearGroup.map (algebraMap F (Adeles F))

def rationalCoordinates (g : KubotaRankTwo.GL2 F) (v : KPHilbert.Place F) :
    KPLocalCover.CubicGL2Raw F ζ hζ v :=
  KPLocalCover.sectionMap F ζ hζ v
    (Matrix.GeneralLinearGroup.map (algebraMap F (KPHilbert.Completion F v)) g)

theorem rationalCoordinates_restricted (g : KubotaRankTwo.GL2 F) :
    ∀ᶠ v in Filter.cofinite,
      rationalCoordinates F ζ hζ g v ∈ (compact F ζ hζ v : Set _) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.rationalCoordinates_restricted F ζ hζ g

def rationalTuple (g : KubotaRankTwo.GL2 F) : RestrictedCover F ζ hζ :=
  ⟨rationalCoordinates F ζ hζ g, rationalCoordinates_restricted F ζ hζ g⟩

def rationalSection (g : KubotaRankTwo.GL2 F) : CubicGL2Adelic F ζ hζ :=
  amalgamation F ζ hζ (rationalTuple F ζ hζ g)

@[simp] theorem rationalTuple_eval (g : KubotaRankTwo.GL2 F) (v : KPHilbert.Place F) :
    rationalTuple F ζ hζ g v = rationalCoordinates F ζ hζ g v := rfl

theorem projection_rationalSection (g : KubotaRankTwo.GL2 F) :
    projection F ζ hζ (rationalSection F ζ hζ g) = rationalBase F g := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.projection_rationalSection F ζ hζ g

theorem rationalSection_mul (g h : KubotaRankTwo.GL2 F) :
    rationalSection F ζ hζ (g * h) = rationalSection F ζ hζ g * rationalSection F ζ hζ h := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.rationalSection_mul F ζ hζ g h

theorem rationalSection_one : rationalSection F ζ hζ 1 = 1 := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.rationalSection_one F ζ hζ

def rationalHom : KubotaRankTwo.GL2 F →* CubicGL2Adelic F ζ hζ where
  toFun := rationalSection F ζ hζ
  map_one' := rationalSection_one F ζ hζ
  map_mul' := rationalSection_mul F ζ hζ

theorem rationalSection_scalar (z : Fˣ) :
    rationalSection F ζ hζ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      scalarHom F ζ hζ (Units.map (algebraMap F (Adeles F)) z) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.rationalSection_scalar F ζ hζ z

theorem rationalCoordinates_N (x : F) (v : KPHilbert.Place F) :
    rationalCoordinates F ζ hζ (KubotaRankTwo.n F x) v =
      KPStandardLocalRootLifts.N F ζ hζ v (algebraMap F (KPHilbert.Completion F v) x) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.rationalCoordinates_N F ζ hζ x v

theorem rationalCoordinates_A (y : Fˣ) (v : KPHilbert.Place F) :
    rationalCoordinates F ζ hζ (KubotaRankTwo.d F y 1) v =
      KPStandardLocalRootLifts.A F ζ hζ v (Units.map (algebraMap F (KPHilbert.Completion F v)) y) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.rationalCoordinates_A F ζ hζ y v

theorem rationalCoordinates_W (v : KPHilbert.Place F) :
    rationalCoordinates F ζ hζ (KPStandardLocalRootLifts.weylSwap F) v =
      KPStandardLocalRootLifts.W F ζ hζ v := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.rationalCoordinates_W F ζ hζ v

def pglCompact (v : KPHilbert.Place F) : Subgroup (KPPGLLocalCover.CubicPGL2 F ζ hζ v) :=
  (compact F ζ hζ v).map (KPPGLLocalCover.coverQuotient F ζ hζ v)

def pglLocalTopology (v : KPHilbert.Place F) :
    TopologicalSpace (KPPGLLocalCover.CubicPGL2 F ζ hζ v) := inferInstance

attribute [local instance] pglLocalTopology

abbrev RestrictedPGLCover := RestrictedProduct
  (fun v : KPHilbert.Place F => KPPGLLocalCover.CubicPGL2 F ζ hζ v)
  (fun v => (pglCompact F ζ hζ v : Set _)) Filter.cofinite

def restrictedPGLQuotient : RestrictedCover F ζ hζ →* RestrictedPGLCover F ζ hζ :=
  RestrictedProduct.mapAlongMonoidHom _ _ id Filter.tendsto_id
    (fun v => KPPGLLocalCover.coverQuotient F ζ hζ v)
    (Filter.Eventually.of_forall (fun v => by
      intro g hg
      exact ⟨g, hg, rfl⟩))

def pglCentralTupleMap : CentralTuples F →* RestrictedPGLCover F ζ hζ :=
  (restrictedPGLQuotient F ζ hζ).comp (centralTupleMap F ζ hζ)

def pglM : Subgroup (RestrictedPGLCover F ζ hζ) :=
  (centralProduct F).ker.map (pglCentralTupleMap F ζ hζ)

theorem pglM_central : pglM F ζ hζ ≤ Subgroup.center (RestrictedPGLCover F ζ hζ) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.pglM_central F ζ hζ

instance pglM_normal : (pglM F ζ hζ).Normal :=
  Subgroup.normal_of_le_center (pglM_central F ζ hζ)

abbrev AmalgamatedRestrictedPGLCover := RestrictedPGLCover F ζ hζ ⧸ pglM F ζ hζ

theorem scalar_quotient_commutes_with_amalgamation :
    ∃ e : CubicPGL2Adelic F ζ hζ ≃* AmalgamatedRestrictedPGLCover F ζ hζ,
      Continuous e ∧ Continuous e.symm ∧
      ∀ x : RestrictedCover F ζ hζ,
        e (scalarQuotient F ζ hζ (amalgamation F ζ hζ x)) =
          QuotientGroup.mk' (pglM F ζ hζ) (restrictedPGLQuotient F ζ hζ x) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.scalar_quotient_commutes_with_amalgamation F ζ hζ

theorem local_pgl_injection (v : KPHilbert.Place F) :
    ∃ j : KPPGLLocalCover.CubicPGL2 F ζ hζ v →* CubicPGL2Adelic F ζ hζ,
      Function.Injective j ∧ Continuous j ∧
      ∀ g : KPLocalCover.CubicGL2Raw F ζ hζ v,
        j (KPPGLLocalCover.coverQuotient F ζ hζ v g) =
          scalarQuotient F ζ hζ (localInjection F ζ hζ v g) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.local_pgl_injection F ζ hζ v

theorem finiteCompact_compact_open (q : HeightOneSpectrum (𝓞 F)) :
    IsCompact (finiteCompact F ζ hζ q : Set (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))) ∧
      IsOpen (finiteCompact F ζ hζ q : Set (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.finiteCompact_compact_open F ζ hζ q

theorem compact_open (v : KPHilbert.Place F) :
    IsOpen (compact F ζ hζ v : Set (KPLocalCover.CubicGL2Raw F ζ hζ v)) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.compact_open F ζ hζ v

end
end DedekindZetaZeroFree.KPAdelicCoverRestrictedProduct

section

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPAdelicCoverRestrictedProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

attribute [local instance] localTopology

theorem centralInjection_injective : Function.Injective (centralInjection F ζ hζ) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.centralInjection_injective F ζ hζ

theorem projection_surjective : Function.Surjective (projection F ζ hζ) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.projection_surjective F ζ hζ

def extension : GroupExtension (rootsOfUnity 3 F) (CubicGL2Adelic F ζ hζ) (AdelicGL2 F) where
  inl := centralInjection F ζ hζ
  rightHom := projection F ζ hζ
  inl_injective := centralInjection_injective F ζ hζ
  range_inl_eq_ker_rightHom := range_centralInjection_eq_ker F ζ hζ
  rightHom_surjective := projection_surjective F ζ hζ

def pglExtension : GroupExtension (rootsOfUnity 3 F)
    (CubicPGL2Adelic F ζ hζ) (AdelicPGL2 F) where
  inl := pglCentralInjection F ζ hζ
  rightHom := pglProjection F ζ hζ
  inl_injective := pglCentralInjection_injective F ζ hζ
  range_inl_eq_ker_rightHom := pglCentralInjection_kernel F ζ hζ
  rightHom_surjective := pglProjection_surjective F ζ hζ

theorem rationalHom_injective : Function.Injective (rationalHom F ζ hζ) := by
  exact DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw.rationalHom_injective F ζ hζ

attribute [local instance] pglLocalTopology

end
end DedekindZetaZeroFree.KPAdelicCoverRestrictedProduct

end
