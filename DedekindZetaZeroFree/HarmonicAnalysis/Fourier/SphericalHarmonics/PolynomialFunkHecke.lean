module

public import DedekindZetaZeroFree.HarmonicAnalysis.SphericalHarmonics.FunkHecke.CircleAverage

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.HarmonicIdentity
open MeasureTheory KPCplxIntertwinerEigenvalues
open scoped RealInnerProductSpace

theorem polynomial_latitude_integrable (p : MvPolynomial (Fin 3) ℂ) (k : ℝ → ℝ)
    (hk : Integrable k (volume.restrict (Set.Icc (0 : ℝ) 1))) (x : Sphere) :
    Integrable (fun y : Sphere =>
      (k ((1 - inner ℝ (x : Ambient) (y : Ambient)) / 2) : ℂ) *
        polynomialSphere p y) sphereArea := by
  let φ : Sphere → ℝ := fun y => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2
  have hφ : Measurable φ := by dsimp [φ]; fun_prop
  have hkm : Integrable k (Measure.map φ sphereArea) := by
    rw [sphereArea_uniform_projection x]
    exact hk
  have hi : Integrable (fun y => (k (φ y) : ℂ)) sphereArea :=
    ((integrable_map_measure hkm.aestronglyMeasurable hφ.aemeasurable).mp hkm).ofReal
  have hp : Continuous (polynomialSphere p) := by
    unfold polynomialSphere
    induction p using MvPolynomial.induction_on with
    | C c => simpa using (continuous_const : Continuous (fun _ : Sphere => c))
    | add p q hp hq =>
      convert hp.add hq using 1 <;> ext y <;> simp
    | mul_X p i hp =>
      convert hp.mul (Complex.continuous_ofReal.comp
        ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val)) using 1
      ext y
      simp
  have h := (show IntegrableOn (fun y => (k (φ y) : ℂ)) Set.univ sphereArea by
    simpa using hi).mul_continuousOn hp.continuousOn isCompact_univ
  simpa [φ] using h

theorem polynomial_funkHecke_zero (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials 0) (k : ℝ → ℝ)
    (hk : Integrable k (volume.restrict (Set.Icc (0 : ℝ) 1))) (x : Sphere) :
    (∫ y : Sphere,
      (k ((1 - inner ℝ (x : Ambient) (y : Ambient)) / 2) : ℂ) *
        polynomialSphere p y ∂sphereArea) =
      ((∫ u : ℝ in Set.Icc 0 1,
        k u * (Polynomial.shiftedLegendre 0).eval₂ (Int.castRingHom ℝ) u : ℝ) : ℂ) *
        polynomialSphere p x := by
  have hp' : p = MvPolynomial.C (p.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hp.1)
  conv_lhs => rw [hp']
  conv_rhs => rw [hp']
  simp only [polynomialSphere, MvPolynomial.eval_C]
  have hleg (u : ℝ) : (Polynomial.shiftedLegendre 0).eval₂ (Int.castRingHom ℝ) u = 1 := by
    simp [Polynomial.shiftedLegendre]
  simp_rw [hleg, mul_one]
  rw [integral_mul_const, integral_complex_ofReal]
  congr 1
  congr 1
  let φ : Sphere → ℝ := fun y => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2
  have hφ : Measurable φ := by dsimp [φ]; fun_prop
  have hkm : Integrable k (Measure.map φ sphereArea) := by
    rw [sphereArea_uniform_projection x]
    exact hk
  have h := integral_map hφ.aemeasurable hkm.aestronglyMeasurable
  rw [sphereArea_uniform_projection x] at h
  exact h.symm

theorem polynomial_funkHecke (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) (k : ℝ → ℝ)
    (hk : Integrable k (volume.restrict (Set.Icc (0 : ℝ) 1))) (x : Sphere) :
    Integrable (fun y : Sphere =>
      (k ((1 - inner ℝ (x : Ambient) (y : Ambient)) / 2) : ℂ) *
        polynomialSphere p y) sphereArea ∧
    (∫ y : Sphere,
      (k ((1 - inner ℝ (x : Ambient) (y : Ambient)) / 2) : ℂ) *
        polynomialSphere p y ∂sphereArea) =
      ((∫ u : ℝ in Set.Icc 0 1,
        k u * (Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) u : ℝ) : ℂ) *
          polynomialSphere p x := by
  refine ⟨polynomial_latitude_integrable p k hk x, ?_⟩
  by_cases hp0 : p = 0
  · simp [hp0, polynomialSphere]
  by_cases hℓ : ℓ = 0
  · subst ℓ
    exact polynomial_funkHecke_zero p hp k hk x
  obtain ⟨g, hg⟩ := FunkHecke.exists_north_rotation x
  let F : Sphere → ℂ := fun y =>
    (k ((1 - inner ℝ (x : Ambient) (y : Ambient)) / 2) : ℂ) * polynomialSphere p y
  have hF : Integrable F sphereArea := polynomial_latitude_integrable p k hk x
  have hμ := FunkHecke.latitude_disintegration g
  have hprod := hμ.integrable_comp_of_integrable hF
  have hmap := integral_map hμ.measurable.aemeasurable
    (show AEStronglyMeasurable F (Measure.map
      (fun z : ℝ × ℝ => FunkHecke.latitudePoint g z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod FunkHecke.angleMeasure)) by
        rw [hμ.map_eq]
        exact hF.aestronglyMeasurable)
  rw [hμ.map_eq] at hmap
  change (∫ y, F y ∂sphereArea) = _
  rw [hmap]
  have hprod' : Integrable (fun z : ℝ × ℝ => F (FunkHecke.latitudePoint g z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod FunkHecke.angleMeasure) := hprod
  rw [integral_prod _ hprod']
  have hx : (⟨g FunkHecke.north,
      mem_sphere_zero_iff_norm.mpr (by rw [g.norm_map, FunkHecke.north_norm])⟩ : Sphere) = x :=
    Subtype.ext hg
  calc
    _ = ∫ u : ℝ in Set.Icc 0 1,
        (k u : ℂ) *
          ((Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) u : ℝ) *
            polynomialSphere p x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      change (∫ θ : ℝ, F (FunkHecke.latitudePoint g u θ) ∂FunkHecke.angleMeasure) = _
      have hpoint (θ : ℝ) : F (FunkHecke.latitudePoint g u θ) =
          (k u : ℂ) * polynomialSphere p (FunkHecke.latitudePoint g u θ) := by
        dsimp [F]
        rw [FunkHecke.latitudePoint_projection x g hg u θ hu]
      simp_rw [hpoint]
      rw [integral_const_mul, FunkHecke.harmonic_latitude_average ℓ p hp g u hu, hx]
      ring
    _ = _ := by
      rw [integral_mul_const]
      congr 1
      simp_rw [← Complex.ofReal_mul]
      exact integral_complex_ofReal

end DedekindZetaZeroFree.ComplexFractionalInverse.HarmonicIdentity
