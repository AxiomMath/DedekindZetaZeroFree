module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.PositiveIntertwinerConvergence
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.SphericalHarmonics.LegendreBeta
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.Sphere.PolynomialFunkHecke

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped BigOperators

theorem positive_haar_integral_of_transport
    (β : ℂˣ)
    (q : ℂ → ComplexFractionalInverse.RawSphereProjection.rawSphere)
    (hq : MeasurePreserving q
      ComplexLocal.StereographicTransport.planeProbability
      ComplexFractionalInverse.RawSphereProjection.rawSphereArea)
    (K : ComplexFractionalInverse.RawSphereProjection.rawSphere → ℂ)
    (hK : AEStronglyMeasurable K
      ComplexFractionalInverse.RawSphereProjection.rawSphereArea)
    (g : ℂ → ℂ)
    (hg : ∀ z, g z = (3 * Real.pi : ℂ) *
      (ComplexLocal.StereographicTransport.denominator z ^ (-2 : ℝ) / Real.pi : ℝ) *
        K (q z)) :
    (∫ z, g z ∂characterHaar β) =
      ((3 * characterScale β / 2 : ℝ) : ℂ) *
        ∫ y, K y ∂ComplexFractionalInverse.RawSphereProjection.rawSphereArea := by
  let d : ℂ → ℝ := fun z =>
    ComplexLocal.StereographicTransport.denominator z ^ (-2 : ℝ) / Real.pi
  have hd : Measurable (fun z => ENNReal.ofReal (d z)) := by
    dsimp [d, ComplexLocal.StereographicTransport.denominator]
    fun_prop
  have hdpos (z : ℂ) : 0 ≤ d z := by
    dsimp [d]
    exact div_nonneg (Real.rpow_nonneg (by
      unfold ComplexLocal.StereographicTransport.denominator
      positivity) _) Real.pi_pos.le
  have hm := integral_map hq.measurable.aemeasurable (hq.map_eq ▸ hK)
  rw [hq.map_eq] at hm
  have he : (∫ z, (d z : ℂ) * K (q z) ∂euclideanArea) =
      ∫ y, K y ∂ComplexFractionalInverse.RawSphereProjection.rawSphereArea := by
    change _ = _ at hm
    rw [ComplexLocal.StereographicTransport.planeProbability,
      integral_withDensity_eq_integral_toReal_smul hd
        (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))] at hm
    simpa only [ENNReal.toReal_ofReal (hdpos _), Complex.real_smul] using hm.symm
  have hc : 0 ≤ characterScale β / (2 * Real.pi) :=
    div_nonneg (characterScale_pos β).le (mul_pos (by norm_num) Real.pi_pos).le
  rw [characterHaar, integral_smul_measure, ENNReal.toReal_ofReal hc,
    Complex.real_smul]
  simp_rw [hg]
  change ((characterScale β / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ z, (3 * Real.pi : ℂ) * (d z : ℂ) * K (q z) ∂euclideanArea) = _
  simp_rw [show ∀ z, (3 * Real.pi : ℂ) * (d z : ℂ) * K (q z) =
    (3 * Real.pi : ℂ) * ((d z : ℂ) * K (q z)) from fun z => mul_assoc _ _ _]
  rw [integral_const_mul (3 * Real.pi : ℂ), he]
  push_cast
  field_simp
  <;> ring

theorem positive_intertwiner_harmonic_integral (β : ℂˣ) (ℓ : ℕ)
    (p : MvPolynomial (Fin 3) ℂ) (hp : p ∈ harmonicPolynomials ℓ)
    (f : PrincipalSeries positiveParameter)
    (hf : ∀ k : ComplexSU2,
      f (complexSU2Embedding k) = MvPolynomial.eval (compactSphereCoordinate k) p)
    (k : ComplexSU2) :
    (∫ x : ℂ, f (weyl * upperUnipotent x * complexSU2Embedding k) ∂characterHaar β) =
      (((3 * characterScale β / 2) *
        ∏ j ∈ Finset.Icc 1 ℓ, (((j : ℝ) - 1 / 3) / ((j : ℝ) + 1 / 3)) : ℝ) : ℂ) *
      MvPolynomial.eval (compactSphereCoordinate k) p := by
  obtain ⟨x, q, hx, hq, hsection⟩ :=
    HarmonicIntegral.compact_section_spherical_transport k
  let w : ℝ → ℝ := fun u => (1 / 3) * u ^ (1 / 3 - 1 : ℝ)
  have hw : Integrable w (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ComplexFractionalInverse.HarmonicIdentity.powerWeight_integrable
      (1 / 3) (by norm_num)
  have hK := HarmonicIntegral.raw_polynomial_latitude_integrable p w hw x
  rw [positive_haar_integral_of_transport β q hq
    (HarmonicIntegral.rawLatitudeKernel w x p) hK.aestronglyMeasurable
    (fun z => f (weyl * upperUnipotent z * complexSU2Embedding k))
    (hsection p f hf)]
  rw [HarmonicIntegral.raw_polynomial_funkHecke ℓ p hp w hw x]
  have hbeta := ComplexFractionalInverse.HarmonicIdentity.shiftedLegendre_beta
    ℓ (1 / 3) (by norm_num) (by norm_num)
  change (∫ u : ℝ in Set.Icc 0 1,
    w u * (Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) u) = _ at hbeta
  rw [hbeta]
  have hpoint : HarmonicIntegral.rawPolynomialSphere p x =
      MvPolynomial.eval (compactSphereCoordinate k) p := by
    unfold HarmonicIntegral.rawPolynomialSphere
    rw [show (fun i => ((x : ComplexFractionalInverse.RawSphereProjection.rawAmbient) i : ℂ)) =
      compactSphereCoordinate k from funext hx]
  rw [hpoint]
  push_cast
  ring

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
