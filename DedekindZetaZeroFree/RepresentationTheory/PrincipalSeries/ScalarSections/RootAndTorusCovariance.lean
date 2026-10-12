module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.EvaluatorSmoothness

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12

theorem localValue_finite_torus (q : KPFinitePlace F)
    (f : Plus A P C (Sum.inr q)) (u g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (ht : t.val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) u) :
    localValue A P C (Sum.inr q) (u * g) f =
      KPLocalPrincipalSeries.deltaHalf (C.canonical q).borel
        ((C.canonical q).borel.torus t) •
      localTau F ζ hζ P C q t (localValue A P C (Sum.inr q) g f) := by
  let S := C.canonical q
  have hf := f.property.1 (S.borel.torus t) (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g)
  change f.val (_ * _) = KPLocalPrincipalSeries.inducingScalar S.borel 0 (S.borel.torus t) •
    KPLocalStoneVonNeumann.tau (C.polarization q) (S.borel.retract (S.borel.torus t)) (f.val _) at hf
  rw [S.torus_full, ht, S.borel.retract_torus] at hf
  change f.val (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (u * g)) = _
  rw [map_mul]
  simpa only [S, localValue, localTau, KPLocalPrincipalSeries.inducingScalar,
    KPLocalPrincipalSeries.normPower, zero_mul, Complex.exp_zero, mul_one] using hf

theorem localValue_arch_torus (w : InfinitePlace F) (f : Plus A P C (Sum.inl w))
    (u g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) (a d : ℂˣ) (b : ℂ)
    (hu : complexMatrix A w u = KPCplxPrincipalSeriesCharts.upperTriangular a d b) :
    localValue A P C (Sum.inl w) (u * g) f =
      (KPCplxPrincipalSeriesCharts.inductionWeight KPCplxPrincipalSeriesCharts.positiveParameter a d : ℂ) *
      (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ u.epsilon : ℂ) *
      localValue A P C (Sum.inl w) g f := by
  have he : (u * g).epsilon = u.epsilon * g.epsilon := by
    rw [KPLocalCover.mul_epsilon, KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one]
  have hm : complexMatrix A w (u * g) = complexMatrix A w u * complexMatrix A w g := by
    unfold complexMatrix
    exact map_mul _ _ _
  change (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (u * g).epsilon : ℂ) *
    f.val (complexMatrix A w (u * g)) = _
  rw [he, hm, hu, f.val.property.1, map_mul, Units.val_mul]
  change _ = _ * _ * ((KPSourceConvention.ordinaryGenuineCharacter F ζ hζ g.epsilon : ℂ) *
    f.val (complexMatrix A w g))
  ring

theorem localValue_upper (v : KPHilbert.Place F) (f : Plus A P C v)
    (y : KPHilbert.Completion F v) (g : KPLocalCover.CubicGL2Raw F ζ hζ v) :
    localValue A P C v (KPStandardLocalRootLifts.N F ζ hζ v y * g) f = localValue A P C v g f := by
  cases v with
  | inr q =>
    let S := C.canonical q
    have hf := f.property.1 (S.borel.upperRoot (Multiplicative.ofAdd y))
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g)
    rw [KPLocalPrincipalSeries.upperRoot_trivial] at hf
    have hn := (S.openCell (C.polarization q)).upper_eq y
    change f.val (_ * _) = _ at hf
    rw [hn] at hf
    change f.val (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (_ * _)) = _
    rw [map_mul]
    exact hf
  | inl w =>
    let y' := (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)) y
    have hm : complexMatrix A w (KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) y) =
        KPCplxPrincipalSeriesCharts.upperTriangular 1 1 y' := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [complexMatrix, KPStandardLocalRootLifts.N, KubotaRankTwo.n,
          Matrix.GeneralLinearGroup.map, KPCplxPrincipalSeriesCharts.upperTriangular, y']
    rw [localValue_arch_torus A P C w f _ _ 1 1 y' hm]
    simp [KPStandardLocalRootLifts.N, KPLocalCover.sectionMap,
      KPCplxPrincipalSeriesCharts.inductionWeight, KPCplxPrincipalSeriesCharts.complexAbs]

theorem rawCoreInsertion_upper
    (x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C))
    (y : KPAdeles F) (g : Raw A) :
    rawCoreInsertion A P C x (KPGlobalTorusFunctionData.rootTuple F ζ hζ y * g) =
      rawCoreInsertion A P C x g := by
  apply rawCoreInsertion_congr
  intro v f
  exact localValue_upper A P C v f _ _

theorem quotientCoreEvaluator_upper
    (x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C))
    (y : KPAdeles F) (g : KPGlobalResidualConstruction.G F ζ hζ) :
    quotientCoreEvaluator A P C x (KPGlobalTorusFunctionData.N F ζ hζ y * g) =
      quotientCoreEvaluator A P C x g := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H g =>
      change quotientCoreValue A P C x
        (scalarQuotient F ζ hζ (amalgamation F ζ hζ (KPGlobalTorusFunctionData.rootTuple F ζ hζ y)) *
          scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) = _
      rw [← map_mul, ← map_mul, quotientCoreValue_raw]
      exact rawCoreInsertion_upper A P C x y g
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
