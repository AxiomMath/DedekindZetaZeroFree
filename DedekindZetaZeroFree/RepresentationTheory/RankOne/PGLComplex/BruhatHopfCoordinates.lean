module

public import DedekindZetaZeroFree.MeasureTheory.StereographicProjection.MeasureTransport
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicKTypes

@[expose] public section

namespace DedekindZetaZeroFree.ComplexLocal.StereographicTransport
open MeasureTheory
open ComplexFractionalInverse.RawSphereProjection
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxHarmonicIntertwinerSpectrum
open scoped RealInnerProductSpace

noncomputable def radius (z : ℂ) : ℝ := Real.sqrt (denominator z)

theorem radius_pos (z : ℂ) : 0 < radius z := by
  apply Real.sqrt_pos.mpr
  unfold denominator
  positivity

theorem radius_sq (z : ℂ) : radius z ^ 2 = denominator z := by
  apply Real.sq_sqrt
  unfold denominator
  positivity

noncomputable def kappa (z : ℂ) : ComplexSU2 :=
  ⟨!![star z / (radius z : ℂ), -1 / (radius z : ℂ);
      1 / (radius z : ℂ), z / (radius z : ℂ)], by
    have hn : ‖(1 : ℂ) / (radius z : ℂ)‖ ^ 2 +
        ‖z / (radius z : ℂ)‖ ^ 2 = 1 := by
      rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (radius_pos z), norm_one, div_pow, div_pow, radius_sq]
      unfold denominator
      field_simp
    have hm : !![star z / (radius z : ℂ), -1 / (radius z : ℂ);
        1 / (radius z : ℂ), z / (radius z : ℂ)] =
        !![star (z / (radius z : ℂ)), -star (1 / (radius z : ℂ));
        1 / (radius z : ℂ), z / (radius z : ℂ)] := by
      simp [star_div₀, neg_div]
    rw [hm]
    generalize ha : (1 : ℂ) / (radius z : ℂ) = a at *
    generalize hb : z / (radius z : ℂ) = b at *
    have hn' : ‖b‖ ^ 2 + ‖a‖ ^ 2 = 1 := by linarith
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
          Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow,
          ← Complex.ofReal_add, hn, hn', mul_comm]
    · simp [Matrix.det_fin_two, Complex.star_def, Complex.mul_conj',
        mul_comm, ← Complex.ofReal_pow, ← Complex.ofReal_add, hn, hn']⟩

noncomputable def unsignedUpper (z : ℂ) : ComplexGL2 :=
  upperTriangular (Units.mk0 (-1 / (radius z : ℂ)) (by
    exact div_ne_zero (by simp) (Complex.ofReal_ne_zero.mpr (radius_pos z).ne')))
    (Units.mk0 (radius z : ℂ) (Complex.ofReal_ne_zero.mpr (radius_pos z).ne'))
    (star z / (radius z : ℂ))

theorem normalized_bruhat_factorization (z : ℂ) :
    weyl * upperUnipotent z = unsignedUpper z * complexSU2Embedding (kappa z) ∧
      (∀ (f : PrincipalSeries positiveParameter) (k : ComplexSU2),
        f (weyl * upperUnipotent z * complexSU2Embedding k) =
          ((denominator z ^ (-(4 / 3) : ℝ) : ℝ) : ℂ) *
            compactRestriction positiveParameter f (kappa z * k)) := by
  have hr : (radius z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (radius_pos z).ne'
  have hs : (radius z : ℂ)^2 = 1 + z * star z := by
    rw [← Complex.ofReal_pow, radius_sq, denominator, Complex.star_def,
      Complex.mul_conj', ← Complex.ofReal_pow]
    simp
  have hfac : weyl * upperUnipotent z = unsignedUpper z * complexSU2Embedding (kappa z) := by
    apply Units.ext
    change !![(0 : ℂ), 1; 1, 0] * !![(1 : ℂ), z; 0, 1] =
      !![-1 / (radius z : ℂ), star z / (radius z : ℂ); 0, (radius z : ℂ)] *
      !![star z / (radius z : ℂ), -1 / (radius z : ℂ);
        1 / (radius z : ℂ), z / (radius z : ℂ)]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · field_simp
      ring
    · field_simp
      simpa [Complex.star_def, mul_comm] using hs
    · field_simp
    · field_simp
  refine ⟨hfac, ?_⟩
  intro f k
  rw [hfac, mul_assoc, ← map_mul]
  have hc := f.property.1
  dsimp [HasCovariance] at hc
  rw [unsignedUpper, hc]
  change _ * _ = _ * _
  congr 1
  congr 1
  dsimp [inductionWeight, complexAbs]
  have hn : ‖(-1 / (radius z : ℂ)) / (radius z : ℂ)‖ ^ 2 =
      denominator z ^ (-2 : ℝ) := by
    simp only [norm_div, norm_neg, norm_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (radius_pos z)]
    rw [div_div, ← sq, div_pow, radius_sq, one_pow, Real.rpow_neg (by
      unfold denominator; positivity), Real.rpow_two]
    ring
  rw [hn, ← Real.rpow_mul (by unfold denominator; positivity)]
  congr 1
  norm_num [positiveParameter]

def HasRawHopfCoordinates (H : ComplexSU2 → rawSphere) : Prop :=
  ∀ k, (H k : rawAmbient) =
    WithLp.toLp 2 (fun i => (compactSphereCoordinate k i).re)

private theorem su2_entries (k : ComplexSU2) : (k : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = star ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1) ∧
  (k : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = -star ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0) := by
  let m : Matrix (Fin 2) (Fin 2) ℂ := k
  have hu := Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup k.property)
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  have ha : star m = Matrix.adjugate m := by
    calc
      star m = 1 * star m := by simp
      _ = (Matrix.adjugate m * m) * star m := by rw [Matrix.adjugate_mul, hd]; simp
      _ = Matrix.adjugate m * (m * star m) := by rw [mul_assoc]
      _ = Matrix.adjugate m := by rw [hu]; simp
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) ha
  have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 0) ha
  simp only [Matrix.star_apply, Matrix.adjugate_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h00 h10
  constructor
  · simpa using congrArg star h00
  · simpa using congrArg star h10

private theorem su2_row_norm (k : ComplexSU2) :
    ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re ^ 2 +
    ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im ^ 2 +
    ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re ^ 2 +
    ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1).im ^ 2 = 1 := by
  have hu := Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup k.property)
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 1 1).re) hu
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Complex.mul_re, Complex.star_def, Complex.normSq_apply] at h
  nlinarith

noncomputable def hopfLinear (a b : ℂ) : rawAmbient →ₗ[ℝ] rawAmbient where
  toFun x := WithLp.toLp 2 ![
    (b.re^2-b.im^2-a.re^2+a.im^2)*x 0 + (2*b.re*b.im-2*a.re*a.im)*x 1 +
      (-2*a.re*b.re-2*a.im*b.im)*x 2,
    (-2*b.re*b.im-2*a.re*a.im)*x 0 + (b.re^2-b.im^2+a.re^2-a.im^2)*x 1 +
      (-2*a.im*b.re+2*a.re*b.im)*x 2,
    (2*a.re*b.re-2*a.im*b.im)*x 0 + (2*a.re*b.im+2*a.im*b.re)*x 1 +
      (b.re^2+b.im^2-a.re^2-a.im^2)*x 2]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp <;> ring

private theorem hopfLinear_norm (a b : ℂ)
    (h : a.re^2+a.im^2+b.re^2+b.im^2 = 1) (x : rawAmbient) :
    ‖hopfLinear a b x‖ = ‖x‖ := by
  have hs : ‖hopfLinear a b x‖^2 = ‖x‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_three, hopfLinear, LinearMap.coe_mk, AddHom.coe_mk,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one]
    calc
      _ = (a.re^2+a.im^2+b.re^2+b.im^2)^2 * (x 0^2+x 1^2+x 2^2) := by ring
      _ = _ := by rw [h]; ring
  nlinarith [norm_nonneg x, norm_nonneg (hopfLinear a b x)]

private theorem hopfLinear_action (H : ComplexSU2 → rawSphere)
    (hH : HasRawHopfCoordinates H) (l k : ComplexSU2) :
    (H (l * k) : rawAmbient) = hopfLinear
      ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
      ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1) (H l) := by
  rw [hH, hH]
  obtain ⟨h0, h1⟩ := su2_entries k
  ext i
  fin_cases i <;>
    simp [compactSphereCoordinate, hopfLinear, Matrix.mul_apply, Fin.sum_univ_two,
      h0, h1, Complex.mul_re, Complex.mul_im, Complex.star_def,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply] <;> ring

private theorem hopf_kappa (H : ComplexSU2 → rawSphere)
    (hH : HasRawHopfCoordinates H) (z : ℂ) : H (kappa z) = sigma z := by
  apply Subtype.ext
  rw [hH]
  have hr : radius z ≠ 0 := (radius_pos z).ne'
  ext i
  fin_cases i <;>
    simp [compactSphereCoordinate, kappa, sigma, sigmaVector, Complex.star_def,
      Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
      Complex.normSq_apply, ← Complex.normSq_eq_norm_sq]
  · rw [← radius_sq]
    field_simp
  · rw [← radius_sq]
    field_simp
  · simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
      zero_pow (by decide : 2 ≠ 0), add_zero, ← Complex.ofReal_div,
      ← Complex.ofReal_pow, Complex.ofReal_re, abs_of_pos (radius_pos z)]
    have hn := Complex.normSq_eq_norm_sq z
    simp [Complex.normSq_apply] at hn
    rw [div_pow, ← hn, ← radius_sq]
    field_simp
    ring

theorem hopf_rotation_geometry (H : ComplexSU2 → rawSphere)
    (hH : HasRawHopfCoordinates H) :
    (∀ z : ℂ, H (kappa z) = sigma z) ∧
      (∀ k : ComplexSU2, ∃ R : rawAmbient ≃ₗᵢ[ℝ] rawAmbient,
        (∀ l : ComplexSU2, H (l * k) = rotation R (H l)) ∧
        (∀ z : ℂ, (1 - inner ℝ (H k : rawAmbient)
          (H (kappa z * k) : rawAmbient)) / 2 = 1 / denominator z)) := by
  refine ⟨hopf_kappa H hH, ?_⟩
  intro k
  let L := hopfLinear ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
    ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
  let J : rawAmbient →ₗᵢ[ℝ] rawAmbient :=
    ⟨L, hopfLinear_norm _ _ (su2_row_norm k)⟩
  let R : rawAmbient ≃ₗᵢ[ℝ] rawAmbient := J.toLinearIsometryEquiv rfl
  have ha (l : ComplexSU2) : H (l * k) = rotation R (H l) := by
    apply Subtype.ext
    exact hopfLinear_action H hH l k
  refine ⟨R, ha, ?_⟩
  intro z
  have h1 : (H (1 : ComplexSU2) : rawAmbient) = WithLp.toLp 2 ![0, 0, -1] := by
    rw [hH]
    ext i
    fin_cases i <;> simp [compactSphereCoordinate]
  have hk : H k = rotation R (H 1) := by simpa using ha 1
  rw [hk, ha, hopf_kappa H hH]
  change (1 - inner ℝ (R (H 1 : rawAmbient)) (R (sigma z : rawAmbient))) / 2 = _
  rw [R.inner_map_map, h1]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three,
    sigma, sigmaVector]
  unfold denominator
  field_simp
  ring

theorem positive_section_stereographic (H : ComplexSU2 → rawSphere)
    (hH : HasRawHopfCoordinates H) (f : PrincipalSeries positiveParameter)
    (F : rawSphere → ℂ)
    (hf : ∀ k, compactRestriction positiveParameter f k = F (H k))
    (k : ComplexSU2) :
    MeasurePreserving (fun z => H (kappa z * k)) planeProbability rawSphereArea ∧
      (∀ z : ℂ, f (weyl * upperUnipotent z * complexSU2Embedding k) =
        (3 * Real.pi : ℂ) *
          (denominator z ^ (-2 : ℝ) / Real.pi : ℝ) *
          (((1 / 3 : ℝ) *
            ((1 - inner ℝ (H k : rawAmbient)
              (H (kappa z * k) : rawAmbient)) / 2) ^ (1 / 3 - 1 : ℝ) : ℝ) : ℂ) *
          F (H (kappa z * k))) := by
  obtain ⟨hσ, hg⟩ := hopf_rotation_geometry H hH
  obtain ⟨R, hR, ht⟩ := hg k
  constructor
  · have he : (fun z => H (kappa z * k)) = rotation R ∘ sigma := by
      funext z
      rw [hR, hσ]
      rfl
    rw [he]
    have hmp : MeasurePreserving (rotation R) rawSphereArea rawSphereArea := by
      refine ⟨(rotation_continuous R).measurable, ?_⟩
      rw [rawSphereArea, Measure.map_smul, (rotation_preserving R).map_eq]
      exact (rotation_continuous R).measurable.aemeasurable
    exact hmp.comp stereographic_measure_transport.1
  · intro z
    rw [(normalized_bruhat_factorization z).2 f k, hf, ht]
    have hD : 0 < denominator z := by unfold denominator; positivity
    have hs : denominator z ^ (-(4 / 3) : ℝ) =
        3 * Real.pi * (denominator z ^ (-2 : ℝ) / Real.pi) *
        ((1 / 3 : ℝ) * (1 / denominator z) ^ (1 / 3 - 1 : ℝ)) := by
      rw [show (1 / denominator z) = (denominator z)⁻¹ by simp,
        ← Real.rpow_neg_eq_inv_rpow]
      have he : -(4 / 3 : ℝ) = -2 + -(1 / 3 - 1) := by norm_num
      rw [he, Real.rpow_add hD]
      field_simp
    rw [show (3 * Real.pi : ℂ) *
        (↑(denominator z ^ (-2 : ℝ) / Real.pi) : ℂ) *
        (↑((1 / 3 : ℝ) * (1 / denominator z) ^ (1 / 3 - 1 : ℝ)) : ℂ) =
        ↑(denominator z ^ (-(4 / 3) : ℝ)) by
      exact_mod_cast hs.symm]

end DedekindZetaZeroFree.ComplexLocal.StereographicTransport
