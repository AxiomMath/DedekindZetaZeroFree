module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicKTypes
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar
open scoped BigOperators

namespace CompactDimension
open MvPolynomial

noncomputable def radiusQuadratic : MvPolynomial (Fin 3) ℂ :=
  ∑ i : Fin 3, MvPolynomial.X i ^ 2

private lemma deriv_radius (i : Fin 3) :
    pderiv i radiusQuadratic = 2 * X i := by
  classical
  simp only [radiusQuadratic, map_sum, pderiv_pow, pderiv_X, pow_one]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji; simp [Pi.single_eq_of_ne hji]
  · simp
private lemma radius_homogeneous : radiusQuadratic.IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i hi
  exact isHomogeneous_X_pow i 2
private lemma lap_radius_mul (q : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (radiusQuadratic * q) =
      radiusQuadratic * polynomialLaplacian q + 6 * q +
        4 * ∑ i : Fin 3, X i * pderiv i q := by
  change (∑ i : Fin 3, pderiv i (pderiv i (radiusQuadratic * q))) = _
  have hc (i : Fin 3) : pderiv i (2 : MvPolynomial (Fin 3) ℂ) = 0 := by
    simpa only [map_ofNat] using (pderiv_C (a := (2 : ℂ)) (i := i))
  simp only [pderiv_mul, deriv_radius, map_add, hc, pderiv_X_self]
  change _ = radiusQuadratic * (∑ i : Fin 3, pderiv i (pderiv i q)) + _ + _
  simp only [Fin.sum_univ_three]
  ring
private lemma lap_radius_hom {q : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hq : q.IsHomogeneous d) :
    polynomialLaplacian (radiusQuadratic * q) =
      radiusQuadratic * polynomialLaplacian q +
        (2 * (2 * (d : ℂ) + 3)) • q := by
  rw [lap_radius_mul, hq.sum_X_mul_pderiv]
  simp only [nsmul_eq_mul, smul_eq_C_mul, map_mul, map_add, map_ofNat, map_one, C_eq_coe_nat]
  ring

private theorem laplacian_radius_pow {q : MvPolynomial (Fin 3) ℂ} {degree : ℕ}
    (hq : q.IsHomogeneous degree) (k : ℕ) :
    polynomialLaplacian (radiusQuadratic ^ k * q) =
      radiusQuadratic ^ k * polynomialLaplacian q +
        (2 * (k : ℂ) * (2 * (degree : ℂ) + 2 * (k : ℂ) + 1)) •
          (radiusQuadratic ^ (k - 1) * q) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh : (radiusQuadratic ^ k * q).IsHomogeneous (2 * k + degree) :=
      (radius_homogeneous.pow k).mul hq
    rw [pow_succ', mul_assoc, lap_radius_hom hh, ih]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ,
      Nat.add_sub_cancel, smul_eq_C_mul, map_mul, map_add, map_ofNat, map_one, C_eq_coe_nat]
    cases k with
    | zero => simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_mul,
        zero_add, add_zero, map_zero, pow_one]; ring
    | succ k =>
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

private lemma lap_hom {p : MvPolynomial (Fin 3) ℂ} {n : ℕ}
    (hp : p.IsHomogeneous n) : (polynomialLaplacian p).IsHomogeneous (n - 2) := by
  change (∑ i : Fin 3, pderiv i (pderiv i p)).IsHomogeneous _
  apply IsHomogeneous.sum
  intro i hi
  simpa only [Nat.sub_sub] using hp.pderiv.pderiv (i := i)
private lemma lap_low {p : MvPolynomial (Fin 3) ℂ} {n : ℕ}
    (hp : p.IsHomogeneous n) (hn : n ≤ 1) : polynomialLaplacian p = 0 := by
  have hzero {q : MvPolynomial (Fin 3) ℂ} (hq : q.IsHomogeneous 0) (i : Fin 3) :
      pderiv i q = 0 := by
    rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hq
    rw [hq, pderiv_C]
  change (∑ i : Fin 3, pderiv i (pderiv i p)) = 0
  apply Finset.sum_eq_zero
  intro i hi
  apply hzero
  simpa only [Nat.sub_eq_zero_of_le hn] using hp.pderiv (i := i)
private lemma harmonic_smul {p : MvPolynomial (Fin 3) ℂ} {n : ℕ}
    (hp : p ∈ harmonicPolynomials n) (c : ℂ) : c • p ∈ harmonicPolynomials n :=
  (harmonicPolynomials n).smul_mem c hp
private lemma radial_inverse {p : MvPolynomial (Fin 3) ℂ} {n : ℕ}
    (hp : p ∈ harmonicPolynomials n) (k : ℕ) :
    polynomialLaplacian (radiusQuadratic ^ (k + 1) *
      ((2 * ((k + 1 : ℕ) : ℂ) * (2 * (n : ℂ) + 2 * ((k + 1 : ℕ) : ℂ) + 1))⁻¹ • p)) =
      radiusQuadratic ^ k * p := by
  let c : ℂ := 2 * ((k + 1 : ℕ) : ℂ) * (2 * (n : ℂ) + 2 * ((k + 1 : ℕ) : ℂ) + 1)
  have hc : c ≠ 0 := by
    dsimp [c]
    norm_cast
  have hh := harmonic_smul hp c⁻¹
  rw [laplacian_radius_pow hh.1]
  have hz : polynomialLaplacian (c⁻¹ • p) = 0 := hh.2
  change polynomialLaplacian (c⁻¹ • p) = 0 at hz
  change _ + c • (radiusQuadratic ^ (k + 1 - 1) * (c⁻¹ • p)) = _
  rw [hz]
  simp only [mul_zero, zero_add, Nat.add_sub_cancel, mul_smul_comm,
    smul_smul, mul_inv_cancel₀ hc, one_smul]

private theorem homogeneous_fischer {p : MvPolynomial (Fin 3) ℂ} {degree : ℕ}
    (hp : p.IsHomogeneous degree) :
    ∃ h : ℕ → MvPolynomial (Fin 3) ℂ,
      (∀ k ≤ degree / 2, h k ∈ harmonicPolynomials (degree - 2 * k)) ∧
      p = ∑ k ∈ Finset.range (degree / 2 + 1), radiusQuadratic ^ k * h k := by
  classical
  induction degree using Nat.strong_induction_on generalizing p with
  | h d ih =>
    by_cases hd : d ≤ 1
    · refine ⟨fun _ => p, ?_, ?_⟩
      · intro k hk
        have hk0 : k = 0 := by omega
        subst k
        exact ⟨hp, lap_low hp hd⟩
      · have hd0 : d / 2 = 0 := by omega
        simp [hd0]
    · obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
      have hl : (polynomialLaplacian p).IsHomogeneous n := by
        simpa using lap_hom hp
      obtain ⟨h, hh, he⟩ := ih n (by omega) hl
      let c (k : ℕ) : ℂ :=
        2 * ((k + 1 : ℕ) : ℂ) * (2 * ((n - 2 * k : ℕ) : ℂ) + 2 * ((k + 1 : ℕ) : ℂ) + 1)
      let g (k : ℕ) : MvPolynomial (Fin 3) ℂ := (c k)⁻¹ • h k
      let r : MvPolynomial (Fin 3) ℂ :=
        ∑ k ∈ Finset.range (n / 2 + 1), radiusQuadratic ^ (k + 1) * g k
      have hg (k : ℕ) (hk : k ≤ n / 2) : g k ∈ harmonicPolynomials (n - 2 * k) :=
        harmonic_smul (hh k hk) _
      have hr : r.IsHomogeneous (n + 2) := by
        apply IsHomogeneous.sum
        intro k hk
        have hk' : k < n / 2 + 1 := Finset.mem_range.mp hk
        have hb : 2 * k ≤ n := by omega
        have hs := (radius_homogeneous.pow (k + 1)).mul (hg k (by omega)).1
        convert hs using 1 <;> omega
      have hrl : polynomialLaplacian r = polynomialLaplacian p := by
        dsimp [r]
        rw [map_sum]
        rw [he]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < n / 2 + 1 := Finset.mem_range.mp hk
        exact radial_inverse (hh k (by omega)) k
      have hediv : (n + 2) / 2 = n / 2 + 1 := by omega
      refine ⟨fun k => if k = 0 then p - r else g (k - 1), ?_, ?_⟩
      · intro k hk
        by_cases hk0 : k = 0
        · subst k
          simp only [ite_true, mul_zero, Nat.sub_zero]
          exact ⟨hp.sub hr, by change polynomialLaplacian (p - r) = 0; rw [map_sub, hrl, sub_self]⟩
        · simp only [hk0, ite_false]
          convert hg (k - 1) (by omega) using 1
          congr 1
          omega
      · have hediv : (n + 2) / 2 + 1 = (n / 2 + 1) + 1 := by omega
        rw [hediv, Finset.sum_range_succ']
        simp only [pow_zero, ite_true, one_mul, Nat.add_eq_zero_iff, Nat.one_ne_zero,
          and_false, ite_false, Nat.add_sub_cancel]
        change p = r + (p - r)
        ring

noncomputable def homogeneousSphereBasis (ℓ : ℕ) :
    Module.Basis {d : Fin 3 →₀ ℕ | d.degree = ℓ} ℂ
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ) :=
  (MvPolynomial.basisRestrictSupport ℂ {d : Fin 3 →₀ ℕ | d.degree = ℓ}).map
    (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 3) ℂ ℓ).symm)
private theorem homogeneousSphere_finrank (ℓ : ℕ) :
    Module.finrank ℂ (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ) = Nat.multichoose 3 ℓ := by
  classical
  letI := (Finsupp.finite_of_degree_eq (σ := Fin 3) ℓ).fintype
  rw [Module.finrank_eq_card_basis (homogeneousSphereBasis ℓ)]
  have he : {d : Fin 3 →₀ ℕ | d.degree = ℓ} ≃
      ↥((Finset.univ : Finset (Fin 3)).finsuppAntidiag ℓ) :=
    Equiv.Set.congr (by
      ext d
      simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum])
  rw [Fintype.card_congr he, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_multichoose]
  simp

theorem polynomialLaplacian_homogeneous {p : MvPolynomial (Fin 3) ℂ} {ℓ : ℕ}
    (hp : p.IsHomogeneous ℓ) : (polynomialLaplacian p).IsHomogeneous (ℓ - 2) := by
  change (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)).IsHomogeneous _
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  simpa only [Nat.sub_sub] using hp.pderiv.pderiv (i := i)
noncomputable def homogeneousLaplacian (ℓ : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ (ℓ + 2)) →ₗ[ℂ]
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ) :=
  (polynomialLaplacian.comp (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ (ℓ + 2)).subtype).codRestrict
    _ (fun p => by simpa using polynomialLaplacian_homogeneous p.property)
noncomputable def harmonicLaplacianKerEquiv (ℓ : ℕ) :
    harmonicPolynomials (ℓ + 2) ≃ₗ[ℂ] (homogeneousLaplacian ℓ).ker where
  toFun p := ⟨⟨p.val, p.property.1⟩, by
    apply Subtype.ext
    exact p.property.2⟩
  invFun p := ⟨p.val.val, ⟨p.val.property, by
    have hh := p.property
    exact congrArg Subtype.val hh⟩⟩
  left_inv p := rfl
  right_inv p := rfl
  map_add' p q := rfl
  map_smul' c p := rfl
private theorem harmonic_finrank_of_laplacian_surjective (ℓ : ℕ)
    (h : Function.Surjective (homogeneousLaplacian ℓ)) :
    Module.finrank ℂ (harmonicPolynomials (ℓ + 2)) + Nat.multichoose 3 ℓ =
      Nat.multichoose 3 (ℓ + 2) := by
  letI : Module.Finite ℂ (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ (ℓ + 2)) :=
    Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ (ℓ + 2))
  have hh := LinearMap.finrank_range_add_finrank_ker (homogeneousLaplacian ℓ)
  rw [LinearMap.range_eq_top.mpr h, finrank_top,
    homogeneousSphere_finrank, ← (harmonicLaplacianKerEquiv ℓ).finrank_eq] at hh
  simpa [homogeneousSphere_finrank, Nat.add_comm] using hh

private theorem homogeneous_zero_pderiv {p : MvPolynomial (Fin 3) ℂ}
    (hp : p.IsHomogeneous 0) (i : Fin 3) : MvPolynomial.pderiv i p = 0 := by
  have htd : p.totalDegree = 0 := (MvPolynomial.totalDegree_zero_iff_isHomogeneous (σ := Fin 3)).mpr hp
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd]
  exact MvPolynomial.pderiv_C
private theorem polynomialLaplacian_low_degree {p : MvPolynomial (Fin 3) ℂ} {ℓ : ℕ}
    (hp : p.IsHomogeneous ℓ) (hℓ : ℓ ≤ 1) : polynomialLaplacian p = 0 := by
  change (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0
  apply Finset.sum_eq_zero
  intro i hi
  apply homogeneous_zero_pderiv
  simpa only [Nat.sub_eq_zero_of_le hℓ] using hp.pderiv (i := i)
private theorem harmonicPolynomials_low_degree {ℓ : ℕ} (hℓ : ℓ ≤ 1) :
    harmonicPolynomials ℓ = MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ := by
  apply le_antisymm inf_le_left
  intro p hp
  exact ⟨hp, polynomialLaplacian_low_degree hp hℓ⟩
private theorem harmonicPolynomials_finrank_zero : Module.finrank ℂ (harmonicPolynomials 0) = 1 := by
  rw [harmonicPolynomials_low_degree (by omega), homogeneousSphere_finrank]
  simp [Nat.multichoose]
private theorem harmonicPolynomials_finrank_one : Module.finrank ℂ (harmonicPolynomials 1) = 3 := by
  rw [harmonicPolynomials_low_degree (by omega), homogeneousSphere_finrank]
  simp [Nat.multichoose]
private theorem harmonic_dimension_of_laplacian_surjective (ℓ : ℕ)
    (h : Function.Surjective (homogeneousLaplacian ℓ)) :
    Module.finrank ℂ (harmonicPolynomials (ℓ + 2)) = 2 * (ℓ + 2) + 1 := by
  have hh := harmonic_finrank_of_laplacian_surjective ℓ h
  have hm : Nat.multichoose 3 (ℓ + 2) = Nat.multichoose 3 ℓ + (2 * (ℓ + 2) + 1) := by
    have h1 := Nat.multichoose_succ_succ 2 (ℓ + 1)
    have h2 := Nat.multichoose_succ_succ 2 ℓ
    simp only [Nat.multichoose_two] at h1 h2
    change Nat.multichoose 3 (ℓ + 2) = (ℓ + 1 + 1 + 1) + Nat.multichoose 3 (ℓ + 1) at h1
    change Nat.multichoose 3 (ℓ + 1) = (ℓ + 1 + 1) + Nat.multichoose 3 ℓ at h2
    omega
  omega

private theorem homogeneousLaplacian_surjective (n : ℕ) :
    Function.Surjective (homogeneousLaplacian n) := by
  classical
  intro p
  obtain ⟨h, hh, he⟩ := homogeneous_fischer p.property
  let c (k : ℕ) : ℂ :=
    2 * ((k + 1 : ℕ) : ℂ) *
      (2 * ((n - 2 * k : ℕ) : ℂ) + 2 * ((k + 1 : ℕ) : ℂ) + 1)
  let g (k : ℕ) : MvPolynomial (Fin 3) ℂ := (c k)⁻¹ • h k
  let r : MvPolynomial (Fin 3) ℂ :=
    ∑ k ∈ Finset.range (n / 2 + 1), radiusQuadratic ^ (k + 1) * g k
  have hg (k : ℕ) (hk : k ≤ n / 2) :
      g k ∈ harmonicPolynomials (n - 2 * k) :=
    (harmonicPolynomials _).smul_mem _ (hh k hk)
  have hradius : radiusQuadratic.IsHomogeneous 2 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    exact MvPolynomial.isHomogeneous_X_pow i 2
  have hr : r.IsHomogeneous (n + 2) := by
    apply MvPolynomial.IsHomogeneous.sum
    intro k hk
    have hk' : k < n / 2 + 1 := Finset.mem_range.mp hk
    have hs := (hradius.pow (k + 1)).mul (hg k (by omega)).1
    convert hs using 1 <;> omega
  refine ⟨⟨r, hr⟩, ?_⟩
  apply Subtype.ext
  change polynomialLaplacian r = p.val
  dsimp [r]
  rw [map_sum, he]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n / 2 + 1 := Finset.mem_range.mp hk
  have hzero : polynomialLaplacian (g k) = 0 := (hg k (by omega)).2
  have hc : c k ≠ 0 := by
    dsimp [c]
    norm_cast
  rw [laplacian_radius_pow (hg k (by omega)).1, hzero]
  change _ + c k • (radiusQuadratic ^ (k + 1 - 1) *
    ((c k)⁻¹ • h k)) = _
  simp only [mul_zero, zero_add, Nat.add_sub_cancel, mul_smul_comm,
    smul_smul, mul_inv_cancel₀ hc, one_smul]

private theorem finrank_harmonicPolynomials (ℓ : ℕ) :
    Module.finrank ℂ (harmonicPolynomials ℓ) = 2 * ℓ + 1 := by
  rcases ℓ with _ | _ | ℓ
  · simpa using harmonicPolynomials_finrank_zero
  · simpa using harmonicPolynomials_finrank_one
  · exact harmonic_dimension_of_laplacian_surjective ℓ (homogeneousLaplacian_surjective ℓ)

abbrev Ambient := EuclideanSpace ℝ (Fin 3)
abbrev Sphere := {x : Ambient // x ∈ Metric.sphere 0 1}

noncomputable def hopfVector (k : ComplexSU2) : Ambient :=
  WithLp.toLp 2 (fun i => (compactSphereCoordinate k i).re)

theorem hopfVector_norm (k : ComplexSU2) : ‖hopfVector k‖ = 1 := by
  let m : Matrix (Fin 2) (Fin 2) ℂ := k
  have hu : m * star m = 1 := Matrix.mem_unitaryGroup_iff.mp
    (Matrix.specialUnitaryGroup_le_unitaryGroup k.property)
  have hr := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 1 1).re) hu
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Matrix.one_apply_eq] at hr
  simp only [Complex.star_def, Complex.mul_conj', Complex.add_re, ← Complex.ofReal_pow,
    Complex.ofReal_re, Complex.one_re] at hr
  have hprod : (m 1 0 * star (m 1 1)).re ^ 2 +
      (m 1 0 * star (m 1 1)).im ^ 2 = ‖m 1 0‖ ^ 2 * ‖m 1 1‖ ^ 2 := by
    calc
      _ = Complex.normSq (m 1 0 * star (m 1 1)) := by
        simp only [Complex.normSq_apply, sq]
      _ = _ := by rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, norm_star]
  have hs : ‖hopfVector k‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [hopfVector, compactSphereCoordinate, Fin.sum_univ_three,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Complex.ofReal_re, Real.norm_eq_abs, sq_abs,
      ← Complex.ofReal_pow, Complex.sub_re]
    change (2 * (m 1 0 * star (m 1 1)).re) ^ 2 +
      (2 * (m 1 0 * star (m 1 1)).im) ^ 2 +
      (‖m 1 0‖ ^ 2 - ‖m 1 1‖ ^ 2) ^ 2 = 1
    nlinarith [hprod, sq_nonneg (‖m 1 0‖ ^ 2 + ‖m 1 1‖ ^ 2 - 1)]
  nlinarith [norm_nonneg (hopfVector k)]

noncomputable def hopf (k : ComplexSU2) : Sphere :=
  ⟨hopfVector k, by simpa only [Metric.mem_sphere, dist_zero_right] using hopfVector_norm k⟩

def rowSU2 (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : ComplexSU2 :=
  ⟨!![star b, -star a; a, b], by
    have h' : ‖b‖ ^ 2 + ‖a‖ ^ 2 = 1 := by linarith
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
          Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow,
          ← Complex.ofReal_add, h, h', mul_comm]
    · simp [Matrix.det_fin_two, Complex.star_def, Complex.mul_conj',
        mul_comm, ← Complex.ofReal_pow, ← Complex.ofReal_add, h, h']⟩

private theorem hopf_surjective : Function.Surjective hopf := by
  intro x
  have hs : (x : Ambient) 0 ^ 2 + (x : Ambient) 1 ^ 2 + (x : Ambient) 2 ^ 2 = 1 := by
    have hx : ‖(x : Ambient)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    have := congrArg (fun r : ℝ => r ^ 2) hx
    simpa only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs,
      sq_abs, one_pow] using this
  have hz : (x : Ambient) 2 ≤ 1 := by
    nlinarith [sq_nonneg ((x : Ambient) 0), sq_nonneg ((x : Ambient) 1)]
  by_cases he : (x : Ambient) 2 = 1
  · have h0 : (x : Ambient) 0 = 0 := by nlinarith [sq_nonneg ((x : Ambient) 1)]
    have h1 : (x : Ambient) 1 = 0 := by nlinarith [sq_nonneg ((x : Ambient) 0)]
    refine ⟨rowSU2 1 0 (by simp), ?_⟩
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [hopf, hopfVector, compactSphereCoordinate, rowSU2, h0, h1, he]
  · let r : ℝ := Real.sqrt ((1 - (x : Ambient) 2) / 2)
    have hr : 0 < r := Real.sqrt_pos.2 (by have hz' : (x : Ambient) 2 < 1 := lt_of_le_of_ne hz he; linarith)
    have hr2 : r ^ 2 = (1 - (x : Ambient) 2) / 2 :=
      Real.sq_sqrt (by linarith)
    let a : ℂ := ⟨(x : Ambient) 0 / (2*r), (x : Ambient) 1 / (2*r)⟩
    let b : ℂ := r
    have ha : ‖a‖ ^ 2 = (1 + (x : Ambient) 2) / 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      dsimp [a]
      field_simp
      nlinarith [hr2]
    have hb : ‖b‖ ^ 2 = (1 - (x : Ambient) 2) / 2 := by
      simpa [b, Complex.norm_real, sq_abs] using hr2
    refine ⟨rowSU2 a b (by rw [ha, hb]; ring), ?_⟩
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [hopf, hopfVector, compactSphereCoordinate, rowSU2,
      ha, hb, a, b, Complex.mul_re, Complex.mul_im, ne_of_gt hr,
      ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_div, hr2]
    all_goals field_simp
    all_goals ring

noncomputable def polynomialSphere (p : MvPolynomial (Fin 3) ℂ) (x : Sphere) : ℂ :=
  MvPolynomial.eval (fun i => ((x : Ambient) i : ℂ)) p

private theorem homogeneous_eval_scale {p : MvPolynomial (Fin 3) ℂ} {ℓ : ℕ}
    (hp : p.IsHomogeneous ℓ) (t : ℂ) (x : Fin 3 → ℂ) :
    MvPolynomial.eval (fun i => t * x i) p = t ^ ℓ * MvPolynomial.eval x p := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : ∑ i : Fin 3, d i = ℓ := by
    have hh := hp (MvPolynomial.mem_support_iff.mp hd)
    change Finsupp.weight (fun _ : Fin 3 => (1 : ℕ)) d = ℓ at hh
    rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum] at hh
    exact hh
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, hdeg]
  ring
private theorem homogeneous_sphere_eq_zero {p : MvPolynomial (Fin 3) ℂ} {ℓ : ℕ}
    (hp : p.IsHomogeneous ℓ) (h : ∀ x : Sphere, polynomialSphere p x = 0) : p = 0 := by
  apply MvPolynomial.funext_set (fun _ => Set.range Complex.ofReal)
    (fun _ => by simpa using Set.infinite_univ.image Complex.ofReal_injective.injOn)
  intro z hz
  have hreal : ∀ i : Fin 3, ∃ r : ℝ, (r : ℂ) = z i := fun i => hz i (Set.mem_univ _)
  choose r hr using hreal
  let x : Ambient := WithLp.toLp 2 r
  have eval_real (y : Ambient) (hy : y ≠ 0) :
      MvPolynomial.eval (fun i => (y i : ℂ)) p = 0 := by
    let u : Sphere := ⟨‖y‖⁻¹ • y, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]⟩
    have hu := h u
    change MvPolynomial.eval (fun i => ((u : Ambient) i : ℂ)) p = 0 at hu
    have hs := homogeneous_eval_scale hp (‖y‖ : ℂ) (fun i => ((u : Ambient) i : ℂ))
    have he : (fun i => (‖y‖ : ℂ) * ((u : Ambient) i : ℂ)) = (fun i => (y i : ℂ)) := by
      funext i
      change (‖y‖ : ℂ) * ((‖y‖⁻¹ * y i : ℝ) : ℂ) = _
      rw [← Complex.ofReal_mul]
      congr 1
      rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_mul]
    rw [he] at hs
    simpa only [polynomialSphere] using hs.trans (by rw [hu]; simp)
  have hx : x ≠ 0 ∨ x = 0 := ne_or_eq x 0
  rcases hx with hx | hx
  · have hh := eval_real x hx
    simpa only [x, hr, PiLp.toLp_apply, map_zero] using hh
  · have he : MvPolynomial.eval (fun i => (x i : ℂ)) p = 0 := by
      by_cases hℓ : ℓ = 0
      · subst ℓ
        have htd : p.totalDegree = 0 := (MvPolynomial.totalDegree_zero_iff_isHomogeneous (σ := Fin 3)).mpr hp
        have hc : p = MvPolynomial.C (p.coeff 0) := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd
        rw [hc]
        have hs := h (⟨WithLp.toLp 2 ![1,0,0], by simp [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩ : Sphere)
        rw [hc] at hs
        simpa only [polynomialSphere, MvPolynomial.eval_C] using hs
      · have hs := homogeneous_eval_scale hp 0 (fun _ => 0)
        simp [hℓ] at hs
        simpa [hx] using hs
    simpa only [x, hr, PiLp.toLp_apply, map_zero] using he

private theorem harmonicSphere_injective (ℓ : ℕ) :
    Function.Injective (fun p : harmonicPolynomials ℓ => polynomialSphere p.val) := by
  intro p q hpq
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply homogeneous_sphere_eq_zero (p.property.1.sub q.property.1)
  intro x
  simpa [polynomialSphere, map_sub] using sub_eq_zero.mpr (congrFun hpq x)

end CompactDimension

theorem polynomialCompactHarmonics_finrank (ℓ : ℕ) :
    Module.finrank ℂ ((harmonicPolynomials ℓ).map polynomialCompactRestriction) =
      2 * ℓ + 1 := by
  let f : harmonicPolynomials ℓ →ₗ[ℂ]
      ((harmonicPolynomials ℓ).map polynomialCompactRestriction) :=
    (polynomialCompactRestriction.domRestrict (harmonicPolynomials ℓ)).codRestrict _
      (fun p => Submodule.mem_map.mpr ⟨p, p.property, rfl⟩)
  have hinj : Function.Injective f := by
    intro p q hpq
    apply CompactDimension.harmonicSphere_injective ℓ
    funext x
    obtain ⟨k, hk⟩ := CompactDimension.hopf_surjective x
    have h := congrFun (congrArg Subtype.val hpq) k
    have hc : (fun i => (((CompactDimension.hopf k : CompactDimension.Ambient) i) : ℂ)) =
        compactSphereCoordinate k := by
      funext i
      fin_cases i <;> simp [CompactDimension.hopf, CompactDimension.hopfVector,
        compactSphereCoordinate, ← Complex.ofReal_pow]
    change MvPolynomial.eval (fun i => ((x : CompactDimension.Ambient) i : ℂ)) p.val =
      MvPolynomial.eval (fun i => ((x : CompactDimension.Ambient) i : ℂ)) q.val
    rw [← hk, hc]
    exact h
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨p, hp, he⟩ := Submodule.mem_map.mp y.property
    refine ⟨⟨p, hp⟩, ?_⟩
    exact Subtype.ext he
  exact (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq.symm.trans
    (CompactDimension.finrank_harmonicPolynomials ℓ)

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
