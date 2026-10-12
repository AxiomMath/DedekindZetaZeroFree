module

public import DedekindZetaZeroFree.Arithmetic.PGL.Cusps.TranslationLattice
public import DedekindZetaZeroFree.Geometry.Cusps.AffineTorusBundles.FiniteOrbifoldAtlas
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspCrossSections.FiniteInvariantMeasure
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspCrossSections.RadialQuotientDisintegration

@[expose] public section

noncomputable section
open scoped Classical Matrix
open MeasureTheory

namespace DedekindZetaZeroFree
namespace KPCuspCharts

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

theorem toArch_meanHeight (F : Type*) [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F) (p : Coordinates F) :
    KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) (toArch F p) = p.2 := by
  have hb : ∑ i, (p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i = 0 := by
    exact p.1.2.property
  have hn : (KPCuspLogShape.dimension F : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  simp only [KPCuspLogShape.meanHeight, toArch, Finset.sum_add_distrib, hb,
    add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ p.2 hn

def metric (F : Type*) [Field F] [NumberField F] (p v : Coordinates F) : ℝ :=
  KPArch.metric (KPCuspLogShape.dimension F) (toArch F p) (toArch F v)

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

structure ParabolicData (F : Type*) [Field F] [NumberField F]
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

structure BundleAtlas (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S)
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

structure ChartOutput (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S) where
  positive_dimension : 0 < KPCuspLogShape.dimension F
  lattice : ∃ hdisc : DiscreteTopology (translationLattice F D.L).toIntSubmodule,
    letI := hdisc; IsZLattice ℝ (translationLattice F D.L).toIntSubmodule
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
  atlas : BundleAtlas F hF S D torusAction
  compact_cross : CompactSpace (CrossQuotient F S)

  crossAction : S →* (Cross F ≃ₜ Cross F)
  crossAction_formula : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
    Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
    ∀ p : Cross F,
      crossAction g p = crossAffine F hF D.E D.integralUnits (D.ratio g)
        (A 0 1 / A 1 1) p

  actual_action : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
    Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
    ∀ p : Coordinates F,
      KPCuspSiegel.action F (g : KPCuspArithmetic.PGL2 F) (toArch F p) =
        toArch F (affine F hF D.E D.integralUnits (D.ratio g) (A 0 1 / A 1 1) p)
  unipotent_action : ∀ (x : D.L) (p : Coordinates F),
    KPCuspSiegel.action F
      (D.inclusion (Multiplicative.ofAdd x) : KPCuspArithmetic.PGL2 F) (toArch F p) =
      toArch F ((p.1.1 + embedding F (x : F), p.1.2), p.2)
  metric_invariant : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
    Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
    ∀ p v : Coordinates F,
      let f := affine F hF D.E D.integralUnits (D.ratio g) (A 0 1 / A 1 1)
      metric F (f p) (fderiv ℝ f p v) = metric F p v
  smooth_transitions : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
    Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
    ContDiff ℝ ⊤ (affine F hF D.E D.integralUnits (D.ratio g) (A 0 1 / A 1 1))
  density_formula : ∀ p : Coordinates F,
    KPArch.volumeDensity (KPCuspLogShape.dimension F) (toArch F p) =
      Real.exp (-2 * (KPCuspLogShape.dimension F : ℝ) * p.2)
  shapeMeasure : Measure (Shape F)
  haar_shapeMeasure : shapeMeasure.IsAddHaarMeasure
  archVolume_formula :
    Measure.map (toArch F)
      ((volume.prod shapeMeasure).prod (radialMeasure (KPCuspLogShape.dimension F))) =
      KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)
  measure_invariant : ∀ g : S,
    Measure.map (crossAction g) (volume.prod shapeMeasure) = volume.prod shapeMeasure
  fundamentalDomain : Set (Cross F)
  measurable_fundamentalDomain : MeasurableSet fundamentalDomain
  isFundamentalDomain :
    letI := homeomorphAction crossAction
    IsFundamentalDomain S fundamentalDomain (volume.prod shapeMeasure)
  sectionMeasure : Measure (CrossQuotient F S)
  sectionMeasure_formula : sectionMeasure = Measure.map (Quotient.mk (crossRelation F S))
    ((volume.prod shapeMeasure).restrict fundamentalDomain)
  finite_sectionMeasure : IsFiniteMeasure sectionMeasure
  positive_sectionMeasure : sectionMeasure Set.univ ≠ 0

  radialPresentation : CrossQuotient F S × ℝ ≃ₜ TotalQuotient F S
  radialPresentation_formula : ∀ (p : Cross F) (t : ℝ),
    radialPresentation (Quotient.mk _ p, t) = Quotient.mk _ (p, t)

  quotientVolume_formula :
    Measure.map radialPresentation
      (sectionMeasure.prod (radialMeasure (KPCuspLogShape.dimension F))) =
    Measure.map (Quotient.mk (totalRelation F S))
      (((volume.prod shapeMeasure).prod (radialMeasure (KPCuspLogShape.dimension F))).restrict
        {p : Coordinates F | p.1 ∈ fundamentalDomain})
  highPresentation : ∀ T : ℝ,
    CrossQuotient F S × Set.Ioi T ≃ₜ HighQuotient F S T
  highPresentation_formula : ∀ (T : ℝ) (p : Cross F) (t : Set.Ioi T),
    highPresentation T (Quotient.mk _ p, t) = Quotient.mk _ ⟨(p, t.val), t.property⟩

  highVolume_formula : ∀ T : ℝ,
    Measure.map (highPresentation T)
      (sectionMeasure.prod (Measure.comap (Subtype.val : Set.Ioi T → ℝ)
        (radialMeasure (KPCuspLogShape.dimension F)))) =
    Measure.map (Quotient.mk (highRelation F S T))
      (Measure.comap (Subtype.val : {p : Coordinates F // T < p.2} → Coordinates F)
        (((volume.prod shapeMeasure).prod (radialMeasure (KPCuspLogShape.dimension F))).restrict
          {p : Coordinates F | p.1 ∈ fundamentalDomain}))

theorem volumeDensity_toArch (F : Type*) [Field F] [NumberField F]
    (p : Coordinates F) :
    KPArch.volumeDensity (KPCuspLogShape.dimension F) (toArch F p) =
      Real.exp (-2 * (KPCuspLogShape.dimension F : ℝ) * p.2) := by
  have hs : ∑ i, (p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i = 0 :=
    p.1.2.property
  have he (u : ℝ) : (Real.exp u)⁻¹ ^ 2 = Real.exp (-2 * u) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  simp only [KPArch.volumeDensity, KPArch.height, toArch, he]
  rw [← Real.exp_sum]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, hs, mul_zero,
    add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem affine_radial (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (u : E) (v : F) (p : Coordinates F) :
    (affine F hF E hE u v p).2 = p.2 := rfl

theorem toArch_contDiff (F : Type*) [Field F] [NumberField F] :
    ContDiff ℝ ⊤ (toArch F) := by
  have hb : ContDiff ℝ ⊤ (fun p : Coordinates F =>
      (p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ)) :=
    (Shape F).subtypeL.contDiff.comp (contDiff_snd.comp contDiff_fst)
  unfold toArch
  apply contDiff_pi.mpr
  intro i
  exact (by fun_prop : ContDiff ℝ ⊤ (fun p : Coordinates F => p.1.1 i)).prodMk
    (contDiff_snd.add ((contDiff_apply ℝ ℝ i).comp hb))

theorem affine_contDiff (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (u : E) (v : F) : ContDiff ℝ ⊤ (affine F hF E hE u v) := by
  unfold affine
  fun_prop

 theorem upper_action (g : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hc : g 1 0 = 0) (u : ℂ) (hu : u ≠ 0) (ha : g 0 0 = u * g 1 1)
    (z : KPArch.H3) :
    KPArch.action g z = (u * z.1 + g 0 1 / g 1 1, z.2 + Real.log ‖u‖) := by
  have hd : g 1 1 ≠ 0 := by
    intro h
    apply g.det_ne_zero
    simp [Matrix.det_fin_two, hc, h]
  have hdR : ‖g 1 1‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  have huR : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  apply Prod.ext
  · simp only [KPArch.action, KPArch.actionDenominator, hc, zero_mul, zero_add,
      norm_zero, zero_pow (by norm_num : 2 ≠ 0), star_zero, mul_zero, add_zero]
    have hn : (‖g 1 1‖ ^ 2 : ℝ) = (g 1 1 * star (g 1 1) : ℂ) := by
      simpa [Complex.normSq_eq_norm_sq] using (Complex.mul_conj (g 1 1)).symm
    rw [hn, ha]
    have hds : star (g 1 1) ≠ 0 := star_ne_zero.mpr hd
    field_simp
  · simp only [KPArch.action, KPArch.actionDenominator, hc, zero_mul, zero_add,
      norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero,
      Matrix.det_fin_two, sub_zero, ha, norm_mul]
    have he : ‖u‖ * ‖g 1 1‖ * ‖g 1 1‖ * KPArch.height z / ‖g 1 1‖ ^ 2 =
        ‖u‖ * KPArch.height z := by field_simp
    rw [he, KPArch.height, Real.log_mul huR (ne_of_gt (Real.exp_pos _)), Real.log_exp]
    ring

theorem actual_affine_action (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S)
    (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F))
    (hc : A 1 0 = 0) (p : Coordinates F) :
    KPCuspSiegel.action F (g : KPCuspArithmetic.PGL2 F) (toArch F p) =
      toArch F (affine F hF D.E D.integralUnits (D.ratio g) (A 0 1 / A 1 1) p) := by
  rw [← hA, KPCuspSiegel.action_mk]
  funext i
  let σ := (KPCusp.complexPlace F i).embedding
  have hi : (Matrix.GeneralLinearGroup.map σ A) 1 0 = 0 := by
    change σ (A 1 0) = 0
    simp [hc]
  have hu : σ ((D.ratio g : Fˣ) : F) ≠ 0 :=
    (map_ne_zero σ).mpr (Units.ne_zero _)
  have ha : (Matrix.GeneralLinearGroup.map σ A) 0 0 =
      σ ((D.ratio g : Fˣ) : F) * (Matrix.GeneralLinearGroup.map σ A) 1 1 := by
    change σ (A 0 0) = _
    rw [D.ratioFormula g A hA hc, map_mul]
    rfl
  change KPArch.action (Matrix.GeneralLinearGroup.map σ A) (toArch F p i) = _
  rw [upper_action _ hi _ hu ha]
  apply Prod.ext
  · change σ ((D.ratio g : Fˣ) : F) * p.1.1 i + σ (A 0 1) / σ (A 1 1) =
      σ ((D.ratio g : Fˣ) : F) * p.1.1 i + σ (A 0 1 / A 1 1)
    rw [map_div₀]
  · change p.2 + (p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i + Real.log ‖σ _‖ =
      p.2 + ((p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i +
        Real.log ((KPCusp.complexPlace F i) ((D.ratio g : Fˣ) : F)))
    rw [NumberField.InfinitePlace.norm_embedding_eq]
    ring

theorem actual_unipotent_action (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S)
    (x : D.L) (p : Coordinates F) :
    KPCuspSiegel.action F
      (D.inclusion (Multiplicative.ofAdd x) : KPCuspArithmetic.PGL2 F) (toArch F p) =
      toArch F ((p.1.1 + embedding F (x : F), p.1.2), p.2) := by
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective
    (D.inclusion (Multiplicative.ofAdd x) : KPCuspArithmetic.PGL2 F)
  obtain ⟨hc, ha, hb⟩ := D.unipotentFormula x A hA
  have hd : A 1 1 ≠ 0 := by
    intro h
    apply A.det_ne_zero
    simp [Matrix.det_fin_two, hc, h]
  have hr : D.ratio (D.inclusion (Multiplicative.ofAdd x)) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [← D.exact]
    exact ⟨_, rfl⟩
  rw [actual_affine_action F hF S D _ A hA hc p, hr]
  have hv : A 0 1 / A 1 1 = (x : F) := by rw [hb, ha, mul_div_cancel_right₀ _ hd]
  rw [hv]
  congr 1
  ext i <;> simp [affine, embedding]

 def affineLinear (F : Type*) [Field F] [NumberField F] (u : F) :
    Coordinates F →L[ℝ] Coordinates F :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p => ((fun i => embedding F u i * p.1.1 i, p.1.2), p.2)
    map_add' := by intros; ext i <;> simp [mul_add]
    map_smul' := by
      intro a p
      ext i <;> simp [Algebra.smul_def] <;> ring
  }

private theorem affine_fderiv (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (u : E) (v : F) (p : Coordinates F) :
    fderiv ℝ (affine F hF E hE u v) p = affineLinear F ((u : Fˣ) : F) := by
  have hf : affine F hF E hE u v = fun q =>
      affineLinear F ((u : Fˣ) : F) q + affine F hF E hE u v 0 := by
    funext q
    ext i <;> simp [affine, affineLinear]
  rw [hf]
  exact ((affineLinear F ((u : Fˣ) : F)).hasFDerivAt.add_const _).fderiv

theorem affine_metric_invariant (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (u : E) (v : F) (p w : Coordinates F) :
    metric F (affine F hF E hE u v p) (fderiv ℝ (affine F hF E hE u v) p w) =
      metric F p w := by
  rw [affine_fderiv]
  unfold metric KPArch.metric
  apply Finset.sum_congr rfl
  intro i _
  have hu : (KPCusp.complexPlace F i) ((u : Fˣ) : F) > 0 := by
    rw [← NumberField.InfinitePlace.norm_embedding_eq]
    exact norm_pos_iff.mpr ((map_ne_zero _).mpr (Units.ne_zero _))
  change (Real.exp (p.2 + ((p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i +
        Real.log ((KPCusp.complexPlace F i) ((u : Fˣ) : F)))))⁻¹ ^ 2 *
      ‖embedding F ((u : Fˣ) : F) i * w.1.1 i‖ ^ 2 + (w.2 + (w.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i)^2 =
    (Real.exp (p.2 + (p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i))⁻¹ ^ 2 * ‖w.1.1 i‖ ^ 2 +
      (w.2 + (w.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i)^2
  rw [norm_mul]
  have hn : ‖embedding F ((u : Fˣ) : F) i‖ = (KPCusp.complexPlace F i) ((u : Fˣ) : F) :=
    NumberField.InfinitePlace.norm_embedding_eq _ _
  rw [hn, ← add_assoc, Real.exp_add _ (Real.log _), Real.exp_log hu]
  field_simp
  <;> ring

 theorem shape_sum_zero (F : Type*) [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPCuspLogShape.shapeCoordinates (KPCuspLogShape.dimension F) z ∈ Shape F := by
  have hn : (KPCuspLogShape.dimension F : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  change ∑ i, ((z i).2 - KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z) = 0
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, KPCuspLogShape.meanHeight]
  field_simp
  ring

def toArchHomeomorph (F : Type*) [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F) :
    Coordinates F ≃ₜ KPArch.Space (KPCuspLogShape.dimension F) where
  toFun := toArch F
  invFun z := ((fun i => (z i).1,
    ⟨KPCuspLogShape.shapeCoordinates (KPCuspLogShape.dimension F) z,
      shape_sum_zero F hd z⟩), KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z)
  left_inv p := by
    have ht := toArch_meanHeight F hd p
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        funext i
        change (toArch F p i).2 - _ = _
        rw [ht]
        simp [toArch]
    · exact ht
  right_inv z := by
    funext i
    apply Prod.ext
    · rfl
    · change _ + ((z i).2 - _) = (z i).2
      ring
  continuous_toFun := (toArch_contDiff F).continuous
  continuous_invFun := by
    have ht : Continuous (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)) := by
      unfold KPCuspLogShape.meanHeight
      fun_prop
    have hb : Continuous (KPCuspLogShape.shapeCoordinates (KPCuspLogShape.dimension F)) := by
      unfold KPCuspLogShape.shapeCoordinates
      fun_prop
    exact (by fun_prop : Continuous (fun z : KPArch.Space (KPCuspLogShape.dimension F) =>
      fun i => (z i).1)).prodMk (hb.subtype_mk (shape_sum_zero F hd)) |>.prodMk ht

def projectiveHomeomorph (F : Type*) [Field F] [NumberField F]
    (g : KPCuspArithmetic.PGL2 F) :
    KPArch.Space (KPCuspLogShape.dimension F) ≃ₜ KPArch.Space (KPCuspLogShape.dimension F) where
  toFun := KPCuspSiegel.action F g
  invFun := KPCuspSiegel.action F g⁻¹
  left_inv := inv_smul_smul g
  right_inv := smul_inv_smul g
  continuous_toFun := by
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have he : KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk A) = KPCuspSiegel.glAction F A := by
      funext z; exact KPCuspSiegel.action_mk F A z
    rw [he]
    exact (KPArch.productAction_contDiff _ _).continuous
  continuous_invFun := by
    obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective g⁻¹
    have he : KPCuspSiegel.action F g⁻¹ = KPCuspSiegel.glAction F A := by
      funext z; rw [← hA]; exact KPCuspSiegel.action_mk F A z
    rw [he]
    exact (KPArch.productAction_contDiff _ _).continuous

def highCoordinatesHomeomorph (F : Type*) [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F) (σ : KPCuspArithmetic.PGL2 F) (T : ℝ) :
    {p : Coordinates F // T < p.2} ≃ₜ KPCuspSiegel.highCusp F σ T :=
  ((toArchHomeomorph F hd).subtype (fun p => by
    change T < p.2 ↔ T < KPCuspLogShape.meanHeight _ (toArch F p)
    rw [toArch_meanHeight F hd])).trans
    ((projectiveHomeomorph F σ).image {z | T < KPCuspLogShape.meanHeight _ z})

 theorem conjugated_orbit_iff (F : Type*) [Field F] [NumberField F]
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (q : KPCuspArithmetic.Cusp F)
    (σ : KPCuspArithmetic.PGL2 F) (z w : KPArch.Space (KPCuspLogShape.dimension F)) :
    MulAction.orbitRel (KPCuspArithmetic.conjugatedStabilizer F Γ q σ) _ z w ↔
    MulAction.orbitRel (KPCuspSiegel.parabolic F Γ q) _ (σ • z) (σ • w) := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp g.property
    refine ⟨⟨k, hk⟩, ?_⟩
    have hkg' : σ⁻¹ * k * σ = (g : KPCuspArithmetic.PGL2 F) := by
      simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] using hkg
    change k • (σ • w) = σ • z
    rw [← hg]
    change k • (σ • w) = σ • ((g : KPCuspArithmetic.PGL2 F) • w)
    rw [← hkg']
    simp only [mul_smul, smul_inv_smul]
  · rintro ⟨k, hk⟩
    let g : KPCuspArithmetic.conjugatedStabilizer F Γ q σ :=
      ⟨σ⁻¹ * (k : KPCuspArithmetic.PGL2 F) * σ,
        Subgroup.mem_map.mpr ⟨k.val, k.property, by
          simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]⟩⟩
    refine ⟨g, ?_⟩
    change (σ⁻¹ * (k : KPCuspArithmetic.PGL2 F) * σ) • w = z
    change (k : KPCuspArithmetic.PGL2 F) • (σ • w) = σ • z at hk
    simpa only [mul_smul, inv_smul_smul] using congrArg (fun v => σ⁻¹ • v) hk

def highCuspQuotientHomeomorph (F : Type*) [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (q : KPCuspArithmetic.Cusp F)
    (σ : KPCuspArithmetic.PGL2 F) (T : ℝ) :
    HighQuotient F (KPCuspArithmetic.conjugatedStabilizer F Γ q σ) T ≃ₜ
      KPCuspSiegel.CuspQuotient F Γ q (KPCuspSiegel.highCusp F σ T) :=
  Homeomorph.Quotient.congr (highCoordinatesHomeomorph F hd σ T) (fun p r =>
    conjugated_orbit_iff F Γ q σ (toArch F p.val) (toArch F r.val))

theorem highCuspQuotientHomeomorph_formula (F : Type*) [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (q : KPCuspArithmetic.Cusp F)
    (σ : KPCuspArithmetic.PGL2 F) (T : ℝ)
    (p : {p : Coordinates F // T < p.2}) :
    ∃ z : KPCuspSiegel.highCusp F σ T,
      z.val = KPCuspSiegel.action F σ (toArch F p.val) ∧
      highCuspQuotientHomeomorph F hd Γ q σ T (Quotient.mk _ p) = Quotient.mk _ z := by
  exact ⟨highCoordinatesHomeomorph F hd σ T p, rfl, rfl⟩

theorem positive_dimension (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) :
    0 < KPCuspLogShape.dimension F := by
  have hr := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank F
  have hp : 0 < Module.finrank ℚ F := Module.finrank_pos
  change 0 < NumberField.InfinitePlace.nrComplexPlaces F
  omega

theorem highCuspQuotient_presentation (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (q : KPCuspArithmetic.Cusp F)
    (σ : KPCuspArithmetic.PGL2 F) (T : ℝ) :
    ∃ e : HighQuotient F (KPCuspArithmetic.conjugatedStabilizer F Γ q σ) T ≃ₜ
      KPCuspSiegel.CuspQuotient F Γ q (KPCuspSiegel.highCusp F σ T),
      ∀ p : {p : Coordinates F // T < p.2},
        ∃ z : KPCuspSiegel.highCusp F σ T,
          z.val = KPCuspSiegel.action F σ (toArch F p.val) ∧
          e (Quotient.mk _ p) = Quotient.mk _ z := by
  exact ⟨highCuspQuotientHomeomorph F (positive_dimension F hF) Γ q σ T,
    highCuspQuotientHomeomorph_formula F (positive_dimension F hF) Γ q σ T⟩

end KPCuspCharts

theorem kp_cusp_equivariant_nilmanifold_charts
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hΓ : ∀ g ∈ Γ, KPCuspArithmetic.PreservesUpToHomothety F M g)
    (hcomm : Γ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M))
    (q : KPCuspArithmetic.Cusp F)
    (σ : KPCuspArithmetic.PGL2 F) (hσ : σ • KPCuspArithmetic.infinity F = q) :
    let S := KPCuspArithmetic.conjugatedStabilizer F Γ q σ
    ∃ (D : KPCuspCharts.ParabolicData F S) (O : KPCuspCharts.ChartOutput F hF S D),
      ∀ T : ℝ,
      ∃ e : KPCuspCharts.HighQuotient F S T ≃ₜ
        KPCuspSiegel.CuspQuotient F Γ q (KPCuspSiegel.highCusp F σ T),
      ∀ p : {p : KPCuspCharts.Coordinates F // T < p.2},
        ∃ z : KPCuspSiegel.highCusp F σ T,
          z.val = KPCuspSiegel.action F σ (KPCuspCharts.toArch F p.val) ∧
          e (Quotient.mk _ p) = Quotient.mk _ z := by
  obtain ⟨D₀, hdisc, hlattice⟩ := KPCuspChart.arithmetic_extension_lattice
    F hF M hM Γ hΓ hcomm q σ hσ
  obtain ⟨G⟩ := KPCuspChart.finite_affine_bundle_atlas F hF _ D₀ hdisc hlattice
  obtain ⟨V⟩ := KPCuspChart.normalized_finite_section F hF _ D₀ hdisc hlattice G
  obtain ⟨R⟩ := KPCuspChart.radial_quotient_disintegration F hF _ D₀ G V
  let D : KPCuspCharts.ParabolicData F
      (KPCuspArithmetic.conjugatedStabilizer F Γ q σ) := {
    L := D₀.L
    E := D₀.E
    inclusion := D₀.inclusion
    ratio := D₀.ratio
    integralUnits := D₀.integralUnits
    unitIndex := D₀.unitIndex
    injective := D₀.injective
    surjective := D₀.surjective
    exact := D₀.exact
    upper := D₀.upper
    unipotentFormula := D₀.unipotentFormula
    ratioFormula := D₀.ratioFormula
  }
  let atlas : KPCuspCharts.BundleAtlas F hF _ D G.torusAction := {
    projection := G.atlas.projection
    continuous_projection := G.atlas.continuous_projection
    projection_formula := G.atlas.projection_formula
    lift := G.atlas.lift
    continuous_lift := G.atlas.continuous_lift
    lift_formula := G.atlas.lift_formula
    orbit_equivalence := G.atlas.orbit_equivalence
    chartCount := G.atlas.chartCount
    positive_chartCount := G.atlas.positive_chartCount
    shapeLift := G.atlas.shapeLift
    open_shapeLift := G.atlas.open_shapeLift
    nonempty_shapeLift := G.atlas.nonempty_shapeLift
    small_shapeLift := G.atlas.small_shapeLift
    baseOpen := G.atlas.baseOpen
    open_baseOpen := G.atlas.open_baseOpen
    baseOpen_formula := G.atlas.baseOpen_formula
    cover := G.atlas.cover
    baseChart := G.atlas.baseChart
    baseChart_formula := G.atlas.baseChart_formula
    coarseChart := G.atlas.coarseChart
    coarseChart_formula := G.atlas.coarseChart_formula
    transitions := G.atlas.transitions
  }
  let O : KPCuspCharts.ChartOutput F hF _ D := {
    positive_dimension := KPCuspCharts.positive_dimension F hF
    lattice := ⟨hdisc, hlattice⟩
    compact_torus := G.compact_torus
    compact_base := G.compact_base
    finite_isotropy := G.finite_isotropy
    torusAction := G.torusAction
    torusAction_formula := G.torusAction_formula
    compact_cross := G.compact_cross
    crossAction := G.crossAction
    crossAction_formula := G.crossAction_formula
    atlas := atlas
    actual_action := KPCuspCharts.actual_affine_action F hF _ D
    unipotent_action := KPCuspCharts.actual_unipotent_action F hF _ D
    metric_invariant := by
      intro g A _ _ p v
      exact KPCuspCharts.affine_metric_invariant F hF D.E D.integralUnits
        (D.ratio g) (A 0 1 / A 1 1) p v
    smooth_transitions := by
      intro g A _ _
      exact KPCuspCharts.affine_contDiff F hF D.E D.integralUnits
        (D.ratio g) (A 0 1 / A 1 1)
    density_formula := KPCuspCharts.volumeDensity_toArch F
    shapeMeasure := V.shapeMeasure
    haar_shapeMeasure := V.haar_shapeMeasure
    archVolume_formula := V.archVolume_formula
    measure_invariant := V.measure_invariant
    fundamentalDomain := V.fundamentalDomain
    measurable_fundamentalDomain := V.measurable_fundamentalDomain
    isFundamentalDomain := V.isFundamentalDomain
    sectionMeasure := V.sectionMeasure
    sectionMeasure_formula := V.sectionMeasure_formula
    finite_sectionMeasure := V.finite_sectionMeasure
    positive_sectionMeasure := V.positive_sectionMeasure
    radialPresentation := R.radialPresentation
    radialPresentation_formula := R.radialPresentation_formula
    quotientVolume_formula := R.quotientVolume_formula
    highPresentation := R.highPresentation
    highPresentation_formula := R.highPresentation_formula
    highVolume_formula := R.highVolume_formula
  }
  refine ⟨D, O, ?_⟩
  intro T
  exact KPCuspCharts.highCuspQuotient_presentation F hF Γ q σ T

end DedekindZetaZeroFree

end
