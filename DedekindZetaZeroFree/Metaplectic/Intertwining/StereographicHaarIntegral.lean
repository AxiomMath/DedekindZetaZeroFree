module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.HopfMatrixCoordinates
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.PGLComplex.BruhatHopfCoordinates

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open MeasureTheory

theorem haar_fractionalIntegral_of_stereographic_pushforward (β : ℂˣ) (p : ℂ → Sphere) (hp : Measurable p)
    (hpush : Measure.map p (euclideanArea.withDensity
      (fun z => ENNReal.ofReal ((1 + ‖z‖ ^ 2) ^ (-2 : ℝ) / Real.pi))) = sphereArea)
    (F : Sphere → ℂ) (hF : IsSphereSmooth F) (x : Sphere) (g : ℂ → ℂ)
    (hg : ∀ᵐ z ∂euclideanArea, g z = (3 * Real.pi : ℂ) *
      (((1 + ‖z‖ ^ 2) ^ (-2 : ℝ) / Real.pi : ℝ) : ℂ) *
      ((fractionalKernel (1 / 3) x (p z) : ℂ) * F (p z))) :
    (∫ z, g z ∂characterHaar β) =
      (sphericalScalar β : ℂ) * fractionalIntegral (1 / 3) F x := by
  let d : ℂ → ℝ := fun z => (1 + ‖z‖ ^ 2) ^ (-2 : ℝ) / Real.pi
  let K : Sphere → ℂ := fun y => (fractionalKernel (1 / 3) x y : ℂ) * F y
  have hd : Measurable (fun z => ENNReal.ofReal (d z)) := by
    dsimp [d]
    fun_prop
  have hdpos (z : ℂ) : 0 ≤ d z := by
    dsimp [d]
    exact div_nonneg (Real.rpow_nonneg (by positivity) _) Real.pi_pos.le
  have hi : AEStronglyMeasurable K sphereArea :=
    (fractionalIntegral_integrable (1 / 3) (by norm_num) hF x).aestronglyMeasurable
  have hm := integral_map hp.aemeasurable (hpush ▸ hi)
  have he : (∫ z, (d z : ℂ) * K (p z) ∂euclideanArea) =
      fractionalIntegral (1 / 3) F x := by
    rw [hpush] at hm
    rw [integral_withDensity_eq_integral_toReal_smul hd
      (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))] at hm
    simpa only [ENNReal.toReal_ofReal (hdpos _), Complex.real_smul,
      fractionalIntegral, K] using hm.symm
  have hc : 0 ≤ characterScale β / (2 * Real.pi) :=
    div_nonneg (characterScale_pos β).le (mul_pos (by norm_num) Real.pi_pos).le
  rw [characterHaar, integral_smul_measure, ENNReal.toReal_ofReal hc,
    Complex.real_smul]
  rw [integral_congr_ae hg]
  change ((characterScale β / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ z, (3 * Real.pi : ℂ) * (d z : ℂ) * K (p z) ∂euclideanArea) = _
  simp_rw [show ∀ z, (3 * Real.pi : ℂ) * (d z : ℂ) * K (p z) =
    (3 * Real.pi : ℂ) * ((d z : ℂ) * K (p z)) from fun z => mul_assoc _ _ _]
  rw [integral_const_mul (3 * Real.pi : ℂ), he]
  unfold sphericalScalar
  push_cast
  field_simp
  <;> ring

theorem intertwiner_hopf_integral (H : ComplexSU2 → Sphere) (hH : HasHopfCoordinates H)
    (β : ℂˣ) (f : PrincipalSeries positiveParameter) (F : Sphere → ℂ)
    (hF : IsSphereSmooth F)
    (hf : ∀ k : ComplexSU2, compactRestriction positiveParameter f k = F (H k))
    (k : ComplexSU2) :
    (∫ z : ℂ, f (weyl * upperUnipotent z * complexSU2Embedding k) ∂characterHaar β) =
      (sphericalScalar β : ℂ) * fractionalIntegral (1 / 3) F (H k) := by
  have hraw : ComplexLocal.StereographicTransport.HasRawHopfCoordinates H := hH
  obtain ⟨hmp, heval⟩ :=
    ComplexLocal.StereographicTransport.positive_section_stereographic H hraw f F hf k
  apply haar_fractionalIntegral_of_stereographic_pushforward β
    (fun z => H (ComplexLocal.StereographicTransport.kappa z * k)) hmp.measurable
    hmp.map_eq F hF (H k)
  exact Filter.Eventually.of_forall (fun z => by
    simpa only [ComplexLocal.StereographicTransport.denominator, fractionalKernel,
      Real.rpow_eq_pow, mul_assoc] using heval z)

end DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts
