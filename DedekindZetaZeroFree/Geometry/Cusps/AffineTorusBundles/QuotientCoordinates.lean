module

public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.PGLOrbitNeighborhoods

@[expose] public section

noncomputable section
open scoped Classical Matrix
open MeasureTheory
namespace DedekindZetaZeroFree
namespace KPCuspChart

abbrev Horizontal (F : Type*) [Field F] [NumberField F] :=
  Fin (KPCuspLogShape.dimension F) → ℂ

abbrev Shape (F : Type*) [Field F] [NumberField F] :=
  KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F)

abbrev Cross (F : Type*) [Field F] [NumberField F] := Horizontal F × Shape F

abbrev Coordinates (F : Type*) [Field F] [NumberField F] := Cross F × ℝ

def embedding (F : Type*) [Field F] [NumberField F] : F →+ Horizontal F where
  toFun x := fun i => (KPCusp.complexPlace F i).embedding x
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

def translationLattice (F : Type*) [Field F] [NumberField F] (L : AddSubgroup F) :
    AddSubgroup (Horizontal F) := L.map (embedding F)

abbrev Torus (F : Type*) [Field F] [NumberField F] (L : AddSubgroup F) :=
  Horizontal F ⧸ translationLattice F L

abbrev Base (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F) :=
  Shape F ⧸ (KPCuspLogShape.logLattice F hF E hE).toAddSubgroup

def toArch (F : Type*) [Field F] [NumberField F] (p : Coordinates F) :
    KPArch.Space (KPCuspLogShape.dimension F) :=
  fun i => (p.1.1 i, p.2 + (p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i)

def affine (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (u : E) (v : F) (p : Coordinates F) : Coordinates F :=
  ((fun i => embedding F ((u : Fˣ) : F) i * p.1.1 i + embedding F v i,
    p.1.2 + KPCuspLogShape.logarithm F hF E hE (Additive.ofMul u)), p.2)

def crossRelation (F : Type*) [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) : Setoid (Cross F) :=
  Setoid.comap (fun p => toArch F (p, 0))
    (MulAction.orbitRel S (KPArch.Space (KPCuspLogShape.dimension F)))

abbrev CrossQuotient (F : Type*) [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) := Quotient (crossRelation F S)

def highRelation (F : Type*) [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (T : ℝ) :
    Setoid {p : Coordinates F // T < p.2} :=
  Setoid.comap (fun p => toArch F p.val)
    (MulAction.orbitRel S (KPArch.Space (KPCuspLogShape.dimension F)))

abbrev HighQuotient (F : Type*) [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (T : ℝ) := Quotient (highRelation F S T)

@[instance_reducible] def homeomorphAction {G X : Type*} [Group G] [TopologicalSpace X]
    (β : G →* (X ≃ₜ X)) : MulAction G X where
  smul g x := β g x
  one_smul x := by change (β 1) x = x; rw [map_one]; rfl
  mul_smul g h x := by change (β (g * h)) x = (β g) ((β h) x); rw [map_mul]; rfl

abbrev AffineOrbit {G X : Type*} [Group G] [TopologicalSpace X]
    (β : G →* (X ≃ₜ X)) :=
  letI := homeomorphAction β
  Quotient (MulAction.orbitRel G X)

def kernelUnits (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F) : Subgroup E where
  carrier := {u | KPCuspLogShape.logarithm F hF E hE (Additive.ofMul u) = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change KPCuspLogShape.logarithm F hF E hE
      (Additive.ofMul a + Additive.ofMul b) = 0
    rw [map_add, ha, hb, add_zero]
  inv_mem' := by
    intro a ha
    change KPCuspLogShape.logarithm F hF E hE (-Additive.ofMul a) = 0
    rw [map_neg, ha, neg_zero]

abbrev CoarseFiber (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (L : AddSubgroup F) (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (β : E →* (Torus F L ≃ₜ Torus F L)) :=
  AffineOrbit (β.comp (kernelUnits F hF E hE).subtype)

def coarseProjection (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (L : AddSubgroup F) (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (β : E →* (Torus F L ≃ₜ Torus F L)) :
    Torus F L → CoarseFiber F hF L E hE β := Quotient.mk _

structure ExtensionData (F : Type*) [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) where
  L : AddSubgroup F
  E : Subgroup Fˣ
  inclusion : Multiplicative L →* S
  ratio : S →* E
  integralUnits : E ≤ KPCuspArithmetic.rationalUnits F
  unitIndex : (E.subgroupOf (KPCuspArithmetic.rationalUnits F)).FiniteIndex
  injective : Function.Injective inclusion
  surjective : Function.Surjective ratio
  exact : inclusion.range = ratio.ker
  upper : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g
  unipotentFormula : ∀ (x : L) (A : Matrix.GeneralLinearGroup (Fin 2) F),
    Matrix.ProjGenLinGroup.mk A = (inclusion (Multiplicative.ofAdd x) :
      KPCuspArithmetic.PGL2 F) →
    A 1 0 = 0 ∧ A 0 0 = A 1 1 ∧ A 0 1 = (x : F) * A 0 0
  ratioFormula : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
    Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) →
    A 1 0 = 0 → A 0 0 = ((ratio g : Fˣ) : F) * A 1 1

def totalRelation (F : Type*) [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) : Setoid (Coordinates F) :=
  Setoid.comap (toArch F)
    (MulAction.orbitRel S (KPArch.Space (KPCuspLogShape.dimension F)))

abbrev TotalQuotient (F : Type*) [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) := Quotient (totalRelation F S)

def crossAffine (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (u : E) (v : F) (p : Cross F) : Cross F :=
  (affine F hF E hE u v (p, 0)).1

def radialMeasure (d : ℕ) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (Real.exp (-2 * (d : ℝ) * t)))

structure AtlasData (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (β : D.E →* (Torus F D.L ≃ₜ Torus F D.L)) where
  projection : CrossQuotient F S → Base F hF D.E D.integralUnits
  continuous_projection : Continuous projection
  projection_formula : ∀ p : Cross F,
    projection (Quotient.mk _ p) = QuotientAddGroup.mk p.2
  lift : Torus F D.L × Shape F → CrossQuotient F S
  continuous_lift : Continuous lift
  lift_formula : ∀ (x : Horizontal F) (b : Shape F),
    lift (QuotientAddGroup.mk x, b) = Quotient.mk _ (x, b)
  orbit_equivalence : ∀ (z z' : Torus F D.L) (b b' : Shape F),
    lift (z, b) = lift (z', b') ↔ ∃ u : D.E,
      β u z = z' ∧ b' = b +
        KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul u)
  chartCount : ℕ
  positive_chartCount : 0 < chartCount
  shapeLift : Fin chartCount → Set (Shape F)
  open_shapeLift : ∀ i, IsOpen (shapeLift i)
  nonempty_shapeLift : ∀ i, (shapeLift i).Nonempty
  small_shapeLift : ∀ (i : Fin chartCount) (b b' : Shape F) (u : D.E),
    b ∈ shapeLift i → b' ∈ shapeLift i →
    b' = b + KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul u) →
    KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul u) = 0
  baseOpen : Fin chartCount → Set (Base F hF D.E D.integralUnits)
  open_baseOpen : ∀ i, IsOpen (baseOpen i)
  baseOpen_formula : ∀ i, baseOpen i = QuotientAddGroup.mk '' shapeLift i
  cover : (⋃ i, baseOpen i) = Set.univ
  baseChart : ∀ i, shapeLift i ≃ₜ baseOpen i
  baseChart_formula : ∀ (i : Fin chartCount) (b : shapeLift i),
    (baseChart i b).val = QuotientAddGroup.mk b.val
  coarseChart : ∀ i,
    CoarseFiber F hF D.L D.E D.integralUnits β × shapeLift i ≃ₜ
      {c : CrossQuotient F S // projection c ∈ baseOpen i}
  coarseChart_formula : ∀ (i : Fin chartCount) (z : Torus F D.L) (b : shapeLift i),
    (coarseChart i (coarseProjection F hF D.L D.E D.integralUnits β z, b)).val =
      lift (z, b.val)

  transitions : ∀ (i j : Fin chartCount) (b : shapeLift i) (b' : shapeLift j),
    (QuotientAddGroup.mk b.val : Base F hF D.E D.integralUnits) =
      QuotientAddGroup.mk b'.val →
    ∃ g : S,
      b'.val = b.val + KPCuspLogShape.logarithm F hF D.E D.integralUnits
        (Additive.ofMul (D.ratio g)) ∧
      ∀ z : Torus F D.L, lift (z, b.val) = lift (β (D.ratio g) z, b'.val)

structure GeometryData (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S) where
  compact_torus : CompactSpace (Torus F D.L)
  compact_base : CompactSpace (Base F hF D.E D.integralUnits)
  finite_isotropy : Finite (kernelUnits F hF D.E D.integralUnits)
  torusAction : D.E →* (Torus F D.L ≃ₜ Torus F D.L)
  torusAction_formula : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F)
      (x : Horizontal F),
    Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
    torusAction (D.ratio g) (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (fun i => embedding F ((D.ratio g : Fˣ) : F) i * x i +
        embedding F (A 0 1 / A 1 1) i)
  atlas : AtlasData F hF S D torusAction
  compact_cross : CompactSpace (CrossQuotient F S)
  crossAction : S →* (Cross F ≃ₜ Cross F)
  crossAction_formula : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
    Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
    ∀ p : Cross F,
      crossAction g p = crossAffine F hF D.E D.integralUnits (D.ratio g)
        (A 0 1 / A 1 1) p

structure SectionData (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) where
  shapeMeasure : Measure (Shape F)
  haar_shapeMeasure : shapeMeasure.IsAddHaarMeasure
  archVolume_formula :
    Measure.map (toArch F)
      ((volume.prod shapeMeasure).prod (radialMeasure (KPCuspLogShape.dimension F))) =
      KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)
  measure_invariant : ∀ g : S,
    Measure.map (G.crossAction g) (volume.prod shapeMeasure) = volume.prod shapeMeasure
  fundamentalDomain : Set (Cross F)
  measurable_fundamentalDomain : MeasurableSet fundamentalDomain
  isFundamentalDomain :
    letI := homeomorphAction G.crossAction
    IsFundamentalDomain S fundamentalDomain (volume.prod shapeMeasure)
  sectionMeasure : Measure (CrossQuotient F S)
  sectionMeasure_formula : sectionMeasure = Measure.map (Quotient.mk (crossRelation F S))
    ((volume.prod shapeMeasure).restrict fundamentalDomain)
  finite_sectionMeasure : IsFiniteMeasure sectionMeasure
  positive_sectionMeasure : sectionMeasure Set.univ ≠ 0

structure RadialData (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (V : SectionData F hF S D G) where
  radialPresentation : CrossQuotient F S × ℝ ≃ₜ TotalQuotient F S
  radialPresentation_formula : ∀ (p : Cross F) (t : ℝ),
    radialPresentation (Quotient.mk _ p, t) = Quotient.mk _ (p, t)
  quotientVolume_formula :
    Measure.map radialPresentation
      (V.sectionMeasure.prod (radialMeasure (KPCuspLogShape.dimension F))) =
    Measure.map (Quotient.mk (totalRelation F S))
      (((volume.prod V.shapeMeasure).prod (radialMeasure (KPCuspLogShape.dimension F))).restrict
        {p : Coordinates F | p.1 ∈ V.fundamentalDomain})
  highPresentation : ∀ T : ℝ,
    CrossQuotient F S × Set.Ioi T ≃ₜ HighQuotient F S T
  highPresentation_formula : ∀ (T : ℝ) (p : Cross F) (t : Set.Ioi T),
    highPresentation T (Quotient.mk _ p, t) = Quotient.mk _ ⟨(p, t.val), t.property⟩
  highVolume_formula : ∀ T : ℝ,
    Measure.map (highPresentation T)
      (V.sectionMeasure.prod (Measure.comap (Subtype.val : Set.Ioi T → ℝ)
        (radialMeasure (KPCuspLogShape.dimension F)))) =
    Measure.map (Quotient.mk (highRelation F S T))
      (Measure.comap (Subtype.val : {p : Coordinates F // T < p.2} → Coordinates F)
        (((volume.prod V.shapeMeasure).prod (radialMeasure (KPCuspLogShape.dimension F))).restrict
          {p : Coordinates F | p.1 ∈ V.fundamentalDomain}))

end KPCuspChart
end DedekindZetaZeroFree

end
