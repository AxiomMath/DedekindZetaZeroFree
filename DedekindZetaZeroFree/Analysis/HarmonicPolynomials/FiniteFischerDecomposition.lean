module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.ComplexHarmonicEigenvaluesAndSmoothness

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.FiniteFischerRaw
open KPCplxIntertwinerEigenvalues
open scoped BigOperators
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

theorem laplacian_radius_pow {q : MvPolynomial (Fin 3) ℂ} {degree : ℕ}
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

theorem homogeneous_fischer {p : MvPolynomial (Fin 3) ℂ} {degree : ℕ}
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

end DedekindZetaZeroFree.ComplexFractionalInverse.FiniteFischerRaw
