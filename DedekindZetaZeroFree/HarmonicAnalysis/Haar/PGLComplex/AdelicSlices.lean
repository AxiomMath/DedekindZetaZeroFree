module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.PGLComplex.ExponentialCoordinates
public import DedekindZetaZeroFree.Adeles.Quotients.ArchimedeanFiniteProduct

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.PGLComplex.AdelicSlices
open MeasureTheory Topology NumberField
open scoped Classical Pointwise NumberField ENNReal Matrix.Norms.Operator
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev ActualCover := KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ
abbrev rationalSplit := KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
abbrev rationalSubgroup : Subgroup (ActualCover F ζ hζ) :=
  (rationalSplit F ζ hζ).range

abbrev X := _root_.Quotient (QuotientGroup.rightRel (rationalSubgroup F ζ hζ))

instance : MeasurableSpace (ActualCover F ζ hζ) := borel _

instance : MeasurableSpace (X F ζ hζ) := borel _

instance : BorelSpace (ActualCover F ζ hζ) := ⟨rfl⟩

instance : BorelSpace (X F ζ hζ) := ⟨rfl⟩

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

def archimedeanInsertion (g : ArchGroup F) : ActualCover F ζ hζ :=
  ((Finset.univ : Finset (InfinitePlace F)).toList.map fun v =>
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl v)
        (KPLocalCover.sectionMap F ζ hζ (Sum.inl v)
          (Matrix.GeneralLinearGroup.map
            (InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (KPHilbert.infinite_isComplex F ζ hζ v)).symm.toRingHom (g v).out)))).prod

theorem actual_product_splitting :
    ∃ e : (ArchGroup F × finiteSubgroup F ζ hζ) ≃ₜ* ActualCover F ζ hζ,
      (∀ a h, e (a, h) = archimedeanInsertion F ζ hζ a * h) ∧
      (∀ g, (e.symm g).1 = archProjection F ζ hζ g) ∧
      (∀ a, archProjection F ζ hζ (archimedeanInsertion F ζ hζ a) = a) ∧
      (archProjection F ζ hζ).ker = finiteSubgroup F ζ hζ ∧
      (centreMap F ζ hζ).range ≤ finiteSubgroup F ζ hζ ∧
      T2Space (ActualCover F ζ hζ) ∧ LocallyCompactSpace (ActualCover F ζ hζ) ∧
      SecondCountableTopology (ActualCover F ζ hζ) ∧
      T2Space (finiteSubgroup F ζ hζ) ∧ LocallyCompactSpace (finiteSubgroup F ζ hζ) := by
  obtain ⟨e, he, hinv, hsplit, hker, hcentre, hfiniteLC⟩ :=
    AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  refine ⟨e, he, hinv, hsplit, hker, hcentre, inferInstance, ?_, ?_,
    inferInstance, hfiniteLC⟩
  · exact (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  · exact ActualQuotient.actual_cover_secondCountable F ζ hζ

end DedekindZetaZeroFree.PGLComplex.AdelicSlices

end
