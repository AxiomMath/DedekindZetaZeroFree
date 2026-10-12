module

public import DedekindZetaZeroFree.Metaplectic.Torus.LocalSectionValues
public import DedekindZetaZeroFree.Eisenstein.Induction.CentralDescentAndRationalPeriodization

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

theorem localValue_upperRoot (p : KPHilbert.Place F) (f : Plus R N P C p)
    (y : KPHilbert.Completion F p)
    (g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p) :
    localValue R N P C p (KPStandardLocalRootLifts.N F R.A.zeta12
      R.A.primitive_zeta12 p y * g) f = localValue R N P C p g f := by
  cases p with
  | inr q =>
    let T := (imageData R N P C q).inducing
    have hf := f.property.1 (T.borel.upperRoot (Multiplicative.ofAdd y))
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) g)
    rw [KPLocalPrincipalSeries.upperRoot_trivial] at hf
    have hn := (T.openCell T.polarization).upper_eq y
    change f.val (_ * _) = _ at hf
    rw [hn] at hf
    change f.val (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12
      (Sum.inr q) (_ * _)) = _
    rw [map_mul]
    exact hf
  | inl w =>
    have he : (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12
        (Sum.inl w) y * g).epsilon = g.epsilon := by
      change 1 * g.epsilon * KPLocalCover.sigmaTwo F R.A.zeta12
        R.A.primitive_zeta12 (Sum.inl w) _ _ = _
      rw [KPLocalChartTopology.complex_sigmaTwo_eq_one]
      simp
    let y' := (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)) y
    have hm : complexMatrix R w (KPStandardLocalRootLifts.N F R.A.zeta12
        R.A.primitive_zeta12 (Sum.inl w) y * g) =
        KPCplxPrincipalSeriesCharts.upperTriangular 1 1 y' * complexMatrix R w g := by
      unfold complexMatrix
      change Matrix.GeneralLinearGroup.map _ (_ * g.g) = _
      rw [map_mul]
      congr 1
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [KPStandardLocalRootLifts.N, KubotaRankTwo.n,
          Matrix.GeneralLinearGroup.map, KPCplxPrincipalSeriesCharts.upperTriangular, y']
    change (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
      R.A.primitive_zeta12 _ : ℂ) * f.val _ = _
    rw [he, hm, f.val.property.1]
    simp [KPCplxPrincipalSeriesCharts.inductionWeight,
      KPCplxPrincipalSeriesCharts.complexAbs, localValue]

theorem rawCoreVector_rootTuple (x : PlusCore R N P C)
    (y : KPAdelicCoverRestrictedProduct.Adeles F) (g : Raw R) :
    rawCoreVector R N P C (KPGlobalTorusFunctionData.rootTuple F R.A.zeta12
      R.A.primitive_zeta12 y * g) x = rawCoreVector R N P C g x := by
  letI : Nonempty (RestrictedTensorSimple.Level (bad R P C)) := ⟨⟨bad R P C, le_rfl⟩⟩
  obtain ⟨s, z, rfl⟩ := Module.DirectLimit.exists_of x
  apply rawCoreVector_congr
  intro p f
  exact localValue_upperRoot R N P C p f _ (g p)

theorem quotientCoreVector_upperRoot (x : PlusCore R N P C)
    (y : KPAdelicCoverRestrictedProduct.Adeles F) (g : Group R) :
    quotientCoreVector R N P C x (KPGlobalTorusFunctionData.N F R.A.zeta12
      R.A.primitive_zeta12 y * g) = quotientCoreVector R N P C x g := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H g =>
      change quotientCoreVector R N P C x
        (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12
            (KPGlobalTorusFunctionData.rootTuple F R.A.zeta12 R.A.primitive_zeta12 y)) *
          KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
            (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)) = _
      rw [← map_mul, ← map_mul, quotientCoreVector_raw]
      exact rawCoreVector_rootTuple R N P C x y g

theorem quotientRationalEvaluator_upperRoot (x : PlusCore R N P C)
    (y : KPAdelicCoverRestrictedProduct.Adeles F) (g : Group R) :
    quotientRationalEvaluator R N P C x (KPGlobalTorusFunctionData.N F R.A.zeta12
      R.A.primitive_zeta12 y * g) = quotientRationalEvaluator R N P C x g := by
  change comparisonSmooth R P C (quotientCoreVector R N P C x _) = _
  rw [quotientCoreVector_upperRoot]
  rfl

theorem localValue_finite_torus (q : KPFinitePlace F) (f : Plus R N P C (Sum.inr q))
    (u g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (t : KPLocalExceptionalConstruction.actualTorus F R.A.zeta12 R.A.primitive_zeta12 q)
    (ht : t.val = KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) u) :
    localValue R N P C (Sum.inr q) (u * g) f =
      KPLocalPrincipalSeries.deltaHalf (C.canonical q).borel ((C.canonical q).borel.torus t) •
        localTau F R.A.zeta12 R.A.primitive_zeta12 P C q t
          (localValue R N P C (Sum.inr q) g f) := by
  let T := (imageData R N P C q).inducing
  have hf := f.property.1 (T.borel.torus t)
    (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) g)
  change f.val (_ * _) = KPLocalPrincipalSeries.inducingScalar T.borel 0 (T.borel.torus t) •
    KPLocalStoneVonNeumann.tau T.polarization (T.borel.retract (T.borel.torus t)) (f.val _) at hf
  rw [T.torus_full, ht, T.borel.retract_torus] at hf
  change f.val (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) (_ * _)) = _
  rw [map_mul]
  simpa only [T, imageData, localTau, localValue, LinearMap.coe_mk, AddHom.coe_mk,
    KPLocalPrincipalSeries.inducingScalar,
    KPLocalPrincipalSeries.normPower, zero_mul, Complex.exp_zero, mul_one] using hf

theorem localValue_arch_torus (w : InfinitePlace F) (f : Plus R N P C (Sum.inl w))
    (u g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w))
    (a d : ℂˣ) (b : ℂ)
    (hu : complexMatrix R w u = KPCplxPrincipalSeriesCharts.upperTriangular a d b) :
    localValue R N P C (Sum.inl w) (u * g) f =
      (KPCplxPrincipalSeriesCharts.inductionWeight KPCplxPrincipalSeriesCharts.positiveParameter a d : ℂ) *
        (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12 u.epsilon : ℂ) *
          localValue R N P C (Sum.inl w) g f := by
  have he : (u * g).epsilon = u.epsilon * g.epsilon := by
    rw [KPLocalCover.mul_epsilon, KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one]
  have hm : complexMatrix R w (u * g) = complexMatrix R w u * complexMatrix R w g := by
    unfold complexMatrix
    exact map_mul _ _ _
  change (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
    R.A.primitive_zeta12 _ : ℂ) * f.val _ = _
  rw [he, hm, hu, f.val.property.1, map_mul, Units.val_mul]
  simp only [localValue, LinearMap.coe_mk, AddHom.coe_mk]
  ring

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
