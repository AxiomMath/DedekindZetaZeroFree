module

public import DedekindZetaZeroFree.Arithmetic.Units.FundamentalDomainIntegration
public import DedekindZetaZeroFree.Theta.Profiles.MixedTraceNorm
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.GaussianExistence
public import DedekindZetaZeroFree.Arithmetic.Ideals.UnitReindexing

@[expose] public section

noncomputable section

open Classical NumberField NumberField.InfinitePlace
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open DedekindZetaZeroFree.Theta
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

open Classical in

def mixedGaussian (x : K) (q : InfinitePlace K → ℝ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    ((∑ v : InfinitePlace K, (v.mult : ℝ) * (q v) ^ 2 * (v x) ^ 2 : ℝ) : ℂ))

theorem norm_sq_traceRadialScale_traceEmbedding
    (q : InfinitePlace K → ℝ) (hq : ∀ v, q v ≠ 0) (x : K) :
    ‖traceRadialScale K q hq (traceEmbedding K x)‖ ^ 2 =
      ∑ v : InfinitePlace K, (v.mult : ℝ) * (q v) ^ 2 * (v x) ^ 2 := by
  exact GaussianSchwartz.mixed_norm_sq K q hq x

theorem mixedGaussian_eq_latticeGaussian
    (x : K) (q : InfinitePlace K → ℝ) (hq : ∀ v, q v ≠ 0) :
    mixedGaussian K x q =
      latticeGaussian Real.pi (traceRadialScale K q hq (traceEmbedding K x)) := by
  simp only [mixedGaussian, latticeGaussian, ← Complex.ofReal_pow,
    norm_sq_traceRadialScale_traceEmbedding K q hq]

theorem fractionalShapeIdealTheta_eq_tsum_mixedGaussian
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ v, q v ≠ 0) :
    fractionalShapeIdealTheta K I q hq =
      ∑' x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
        mixedGaussian K (x : K) q := by
  unfold fractionalShapeIdealTheta latticeTheta
  rw [← (fractionalIdealElementShapeEquiv K I q hq).tsum_eq]
  apply tsum_congr
  intro x
  rw [fractionalIdealElementShapeEquiv_coe, mixedGaussian_eq_latticeGaussian]

theorem mixedGaussian_mul_unit
    (u : (𝓞 K)ˣ) (x : K) (q : InfinitePlace K → ℝ) :
    mixedGaussian K ((algebraMap (𝓞 K) K (u : 𝓞 K)) * x) q =
      mixedGaussian K x
        (fun v ↦ v (algebraMap (𝓞 K) K (u : 𝓞 K)) * q v) := by
  unfold mixedGaussian
  congr 3
  apply Finset.sum_congr rfl
  intro v _
  rw [map_mul]
  ring

theorem fractionalShapeIdealTheta_unit_invariant
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : (𝓞 K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ v, q v ≠ 0)
    (huq : ∀ v, v (algebraMap (𝓞 K) K (u : 𝓞 K)) * q v ≠ 0) :
    fractionalShapeIdealTheta K I
        (fun v ↦ v (algebraMap (𝓞 K) K (u : 𝓞 K)) * q v) huq =
      fractionalShapeIdealTheta K I q hq := by
  rw [fractionalShapeIdealTheta_eq_tsum_mixedGaussian,
    fractionalShapeIdealTheta_eq_tsum_mixedGaussian]
  simp_rw [← mixedGaussian_mul_unit]
  exact GaussianSchwartz.tsum_fractionalIdeal_mul_unit K
    (I : FractionalIdeal (𝓞 K)⁰ K) u (fun x ↦ mixedGaussian K x q)

theorem fractionalShapeIdealTheta_expMapBasis_add_unitCoordinateShift
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : realSpace K)
    (z : {w : InfinitePlace K // w ≠ Units.dirichletUnitTheorem.w₀} → ℤ) :
    fractionalShapeIdealTheta K I
        (expMapBasis (x + unitCoordinateShift z))
        (fun w ↦ ne_of_gt (expMapBasis_pos _ w)) =
      fractionalShapeIdealTheta K I (expMapBasis x)
        (fun w ↦ ne_of_gt (expMapBasis_pos _ w)) := by
  have heq : expMapBasis (x + unitCoordinateShift z) =
      (fun w ↦ w (algebraMap (𝓞 K) K
        (fundamentalUnitForShift z : 𝓞 K)) * expMapBasis x w) := by
    funext w
    exact congrFun (expMapBasis_add_unitCoordinateShift x z) w
  rw [fractionalShapeIdealTheta_eq_tsum_mixedGaussian,
    fractionalShapeIdealTheta_eq_tsum_mixedGaussian]
  simp_rw [heq, ← mixedGaussian_mul_unit]
  exact GaussianSchwartz.tsum_fractionalIdeal_mul_unit K
    (I : FractionalIdeal (𝓞 K)⁰ K) (fundamentalUnitForShift z)
    (fun y ↦ mixedGaussian K y (expMapBasis x))

def traceCoordinates :
    euclidean.mixedSpace K ≃ₗᵢ[ℝ] EuclideanSpace ℝ (mixedEmbedding.index K) :=
  (euclidean.stdOrthonormalBasis K).repr

def traceCoordinateCLM (i : mixedEmbedding.index K) :
    euclidean.mixedSpace K →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ : mixedEmbedding.index K ↦ ℝ) i).comp
    (traceCoordinates K).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem traceCoordinateCLM_apply
    (i : mixedEmbedding.index K) (x : euclidean.mixedSpace K) :
    traceCoordinateCLM K i x = traceCoordinates K x i := rfl

def traceRealCoordinateCLM (w : {v : InfinitePlace K // IsReal v}) :
    euclidean.mixedSpace K →L[ℝ] ℝ :=
  traceCoordinateCLM K (Sum.inl w)

@[simp] theorem traceRealCoordinateCLM_apply
    (w : {v : InfinitePlace K // IsReal v}) (x : euclidean.mixedSpace K) :
    traceRealCoordinateCLM K w x = traceCoordinates K x (Sum.inl w) := rfl

theorem exists_latticeGaussianSchwartz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (a : ℝ) (ha : 0 < a) :
    ∃ f : SchwartzMap E ℂ, ∀ x, f x = latticeGaussian a x := by
  exact GaussianSchwartz.exists_gaussian a ha

theorem exists_traceGaussianSchwartz :
    ∃ f : SchwartzMap (euclidean.mixedSpace K) ℂ,
      ∀ x, f x = latticeGaussian Real.pi x :=
  exists_latticeGaussianSchwartz Real.pi Real.pi_pos

def traceGaussianSchwartz : SchwartzMap (euclidean.mixedSpace K) ℂ :=
  Classical.choose (exists_traceGaussianSchwartz K)

@[simp] theorem traceGaussianSchwartz_apply (x : euclidean.mixedSpace K) :
    traceGaussianSchwartz K x = latticeGaussian Real.pi x :=
  Classical.choose_spec (exists_traceGaussianSchwartz K) x

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
