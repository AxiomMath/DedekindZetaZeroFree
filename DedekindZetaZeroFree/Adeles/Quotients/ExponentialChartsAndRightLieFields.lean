module

public import DedekindZetaZeroFree.Metaplectic.Kubota.CubicLocalAndAdelicCovers
public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms
public import DedekindZetaZeroFree.Adeles.Quotients.PGL.MeasurableSquaredNormDescent

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.LocalQuotientCharts.Raw

open MeasureTheory Topology
open scoped NumberField Classical Topology ENNReal Matrix.Norms.Operator

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev ActualCover := KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ

abbrev rationalSplit := KPRationalAdelicSplitting.rationalPGLHom F ζ hζ

abbrev rationalSubgroup : Subgroup (ActualCover F ζ hζ) :=
  (rationalSplit F ζ hζ).range

abbrev X := _root_.Quotient (QuotientGroup.rightRel (rationalSubgroup F ζ hζ))

instance : MeasurableSpace (ActualCover F ζ hζ) := borel _

instance : MeasurableSpace (X F ζ hζ) := borel _

def finiteTuples : Subgroup (KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ) where
  carrier := {g | ∀ w : NumberField.InfinitePlace F, g (Sum.inl w) = 1}
  one_mem' := by simp
  mul_mem' := by intro g h hg hh w; simp [hg w, hh w]
  inv_mem' := by intro g hg w; simp [hg w]

def finiteSubgroup : Subgroup (ActualCover F ζ hζ) :=
  (finiteTuples F ζ hζ).map
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ))

abbrev FiniteLevel := CompactOpenLevel (finiteSubgroup F ζ hζ)

def levelSubgroup (U : FiniteLevel F ζ hζ) : Subgroup (ActualCover F ζ hζ) :=
  U.toOpenSubgroup.toSubgroup.map (finiteSubgroup F ζ hζ).subtype

abbrev centreMap := KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ

def rightSubgroup (U : FiniteLevel F ζ hζ) (geometric : Bool) :
    Subgroup (ActualCover F ζ hζ) :=
  if geometric then levelSubgroup F ζ hζ U ⊔ (centreMap F ζ hζ).range
  else levelSubgroup F ζ hζ U

abbrev LevelSpace (U : FiniteLevel F ζ hζ) (geometric : Bool) :=
  DoubleCoset.Quotient (rationalSubgroup F ζ hζ : Set (ActualCover F ζ hζ))
    (rightSubgroup F ζ hζ U geometric : Set (ActualCover F ζ hζ))

instance (U : FiniteLevel F ζ hζ) (geometric : Bool) :
    TopologicalSpace (LevelSpace F ζ hζ U geometric) :=
  inferInstanceAs (TopologicalSpace (_root_.Quotient _))

instance (U : FiniteLevel F ζ hζ) (geometric : Bool) :
    MeasurableSpace (LevelSpace F ζ hζ U geometric) := borel _

abbrev ArchGroup := NumberField.InfinitePlace F → Matrix.ProjGenLinGroup (Fin 2) ℂ

instance : TopologicalSpace (ArchGroup F) := Pi.topologicalSpace

instance : MeasurableSpace (ArchGroup F) := borel _

abbrev Coordinates := (NumberField.InfinitePlace F × Fin 3 × Fin 2) → ℝ

end DedekindZetaZeroFree.LocalQuotientCharts.Raw

end

section

noncomputable section
namespace DedekindZetaZeroFree.LocalQuotientCharts.Raw

open MeasureTheory Topology
open scoped NumberField Classical Topology ENNReal Matrix.Norms.Operator

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def quotientMap : ActualCover F ζ hζ → X F ζ hζ :=
  _root_.Quotient.mk _

def levelMap (U : FiniteLevel F ζ hζ) (geometric : Bool) :
    ActualCover F ζ hζ → LevelSpace F ζ hζ U geometric :=
  DoubleCoset.mk (rationalSubgroup F ζ hζ) (rightSubgroup F ζ hζ U geometric)

def lieMatrix (x : Coordinates F) (w : NumberField.InfinitePlace F) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let z : Fin 3 → ℂ := fun i => ⟨x (w, i, 0), x (w, i, 1)⟩
  !![z 0, z 1; z 2, -z 0]

def matrixExp (x : Coordinates F) : ArchGroup F := fun w =>
  Matrix.ProjGenLinGroup.mk
    ((NormedSpace.isUnit_exp (lieMatrix F x w)).unit)

def glArchProjection : KPAdelicCoverRestrictedProduct.AdelicGL2 F →* ArchGroup F where
  toFun g w := Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.map
      ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom.comp
        (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w))) g)
  map_one' := by ext w; simp
  map_mul' := by intro g h; ext w; simp

theorem scalars_le_arch_kernel : KPAdelicCoverRestrictedProduct.scalarSubgroup F ≤
    (glArchProjection F ζ hζ).ker := by
  rintro g ⟨u, rfl⟩
  change glArchProjection F ζ hζ (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = 1
  ext w
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
    (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) = 1
  rw [Matrix.GeneralLinearGroup.map_scalar, Matrix.ProjGenLinGroup.mk_scalar]

def archProjection : ActualCover F ζ hζ →* ArchGroup F :=
  (QuotientGroup.lift (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
    (glArchProjection F ζ hζ) (scalars_le_arch_kernel F ζ hζ)).comp
      (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ)

def ArchSupported (g : ActualCover F ζ hζ) : Prop :=
  ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
    ∃ r : KPAdelicCoverRestrictedProduct.AdelicGL2 F,
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) r =
        KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ g ∧
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map
          (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr q)) r) = 1

structure HaarRecipe where
  adelicHaar : Measure (ActualCover F ζ hζ)
  adelic_isHaar : adelicHaar.IsHaarMeasure
  archHaar : Measure (ArchGroup F)
  arch_isHaar : archHaar.IsHaarMeasure
  quotientHaar : Measure (X F ζ hζ)
  domain : Set (ActualCover F ζ hζ)
  domain_measurable : MeasurableSet domain
  domain_fundamental : IsFundamentalDomain (rationalSubgroup F ζ hζ) domain adelicHaar
  quotient_normalization :
    Measure.map (quotientMap F ζ hζ) (adelicHaar.restrict domain) = quotientHaar

def UFixedScalar (U : FiniteLevel F ζ hζ) (f : ActualCover F ζ hζ → ℂ) : Prop :=
  (∀ γ : rationalSubgroup F ζ hζ, ∀ g, f (γ * g) = f g) ∧
  (∀ u : levelSubgroup F ζ hζ U, ∀ g, f (g * u) = f g)

def ScalarAtLevel (U : FiniteLevel F ζ hζ) (χ : rootsOfUnity 3 F →* Circle)
    (f : ActualCover F ζ hζ → ℂ) : Prop :=
  (∀ γ : rationalSubgroup F ζ hζ, ∀ g, f (γ * g) = f g) ∧
  (∀ u : levelSubgroup F ζ hζ U, ∀ g, f (g * u) = f g) ∧
  (∀ ε : rootsOfUnity 3 F, ∀ g,
    f (g * centreMap F ζ hζ ε) = (χ ε : ℂ) * f g)

def ChartScalar (U : FiniteLevel F ζ hζ) (geometric : Bool)
    (χ : rootsOfUnity 3 F →* Circle) (f : ActualCover F ζ hζ → ℂ) : Prop :=
  if geometric then ScalarAtLevel F ζ hζ U χ f else UFixedScalar F ζ hζ U f

structure LiftedChart (U : FiniteLevel F ζ hζ) (geometric : Bool)
    (χ : rootsOfUnity 3 F →* Circle) where
  openSet : Set (ArchGroup F)
  openSet_open : IsOpen openSet
  stabilizer : Type
  stabilizer_group : Group stabilizer
  stabilizer_finite : Fintype stabilizer
  action : stabilizer →* (openSet ≃ₜ openSet)
  centralLabel : stabilizer →* rootsOfUnity 3 F
  lift : openSet → ActualCover F ζ hζ
  lift_continuous : Continuous lift

  finiteRepresentative : ActualCover F ζ hζ
  lift_arch_projection : ∀ x : openSet,
    archProjection F ζ hζ (lift x * finiteRepresentative⁻¹) = x.val
  lift_finite_support : ∀ x : openSet,
    ArchSupported F ζ hζ (lift x * finiteRepresentative⁻¹)
  chartMap : openSet → LevelSpace F ζ hζ U geometric
  chartMap_lift : ∀ x, chartMap x = levelMap F ζ hζ U geometric (lift x)
  neighborhood : Set (LevelSpace F ζ hζ U geometric)
  neighborhood_open : IsOpen neighborhood
  chartMap_range : Set.range chartMap = neighborhood
  chartMap_quotient : IsQuotientMap (fun x : openSet =>
    (⟨chartMap x, by rw [← chartMap_range]; exact Set.mem_range_self x⟩ : neighborhood))
  orbit_fibers : ∀ x y, chartMap x = chartMap y ↔
    ∃ s : stabilizer, action s x = y
  section_equivariance : ∀ f, ChartScalar F ζ hζ U geometric χ f →
    ∀ s : stabilizer, ∀ x, f (lift (action s x)) =
      (if geometric then (χ (centralLabel s) : ℂ) else 1) * f (lift x)

attribute [instance] LiftedChart.stabilizer_group LiftedChart.stabilizer_finite

structure SmallerChart {U : FiniteLevel F ζ hζ} {geometric : Bool}
    {χ : rootsOfUnity 3 F →* Circle} (C : LiftedChart F ζ hζ U geometric χ) where
  carrier : Set (ArchGroup F)
  isOpen : IsOpen carrier
  closure_compact : IsCompact (closure carrier)
  closure_subset : closure carrier ⊆ C.openSet

structure ExponentialChart (g : ArchGroup F) where
  chart : PartialHomeomorph (Coordinates F) (ArchGroup F)
  zero_mem : (0 : Coordinates F) ∈ chart.source
  exponential_formula : ∀ x ∈ chart.source, chart x = g * matrixExp F x

end DedekindZetaZeroFree.LocalQuotientCharts.Raw

end
end
