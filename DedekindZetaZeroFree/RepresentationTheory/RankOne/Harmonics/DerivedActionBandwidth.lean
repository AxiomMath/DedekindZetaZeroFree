module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.NormalizedPauliFlows
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.CompactHarmonicEigenvalues

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.PolynomialCompactRestriction

open KPCplxIntertwinerEigenvalues

theorem polynomialCompactRestriction_lift (s : ℝ) (p : MvPolynomial (Fin 3) ℂ) :
    ∃ f : KPCplxPrincipalSeriesCharts.PrincipalSeries s,
      compactRestriction s f = polynomialCompactRestriction p := by
  obtain ⟨f, hf⟩ := ComplexFractionalInverse.sphereProfile_surjective s
    (ComplexFractionalInverse.polynomialSphere p)
    (ComplexFractionalInverse.polynomialSphere_smooth p)
  refine ⟨f, ?_⟩
  funext k
  change compactRestriction s f k = MvPolynomial.eval (compactSphereCoordinate k) p
  rw [(ComplexFractionalInverse.sphereProfile_spec s f).2 k, hf]
  unfold ComplexFractionalInverse.polynomialSphere ComplexFractionalInverse.hopf
    ComplexFractionalInverse.hopfVector
  congr 2
  funext i
  fin_cases i <;> simp [compactSphereCoordinate, ← Complex.ofReal_pow]

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.PolynomialCompactRestriction

end

end

section

open scoped BigOperators
open MvPolynomial

namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.PolynomialDegreeBounds

private lemma pderiv_totalDegree_le_sub_one {σ R : Type*} [Fintype σ] [CommRing R]
    (p : MvPolynomial σ R) (i : σ) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  rw [totalDegree]
  apply Finset.sup_le
  intro m hm
  have hm' : (pderiv i p).coeff m ≠ 0 := Finsupp.mem_support_iff.mp hm
  rw [coeff_pderiv] at hm'
  have hcoeff : p.coeff (m + Finsupp.single i 1) ≠ 0 := fun h => hm' (by rw [h, zero_mul])
  have hmem : m + Finsupp.single i 1 ∈ p.support := Finsupp.mem_support_iff.mpr hcoeff
  have hle := le_totalDegree hmem
  have hsum : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index']
    · simp
    · intro a; simp
    · intro a b₁ b₂; simp [add_assoc]
  omega

private lemma mul_pderiv_totalDegree_le {σ R : Type*} [Fintype σ] [CommRing R]
    (A p : MvPolynomial σ R) (i : σ) (hA : A.totalDegree ≤ 2) :
    (A * pderiv i p).totalDegree ≤ p.totalDegree + 1 := by
  classical
  rcases eq_or_ne p.totalDegree 0 with h0 | h0
  · rw [totalDegree_eq_zero_iff_eq_C] at h0
    rw [h0, pderiv_C, mul_zero, totalDegree_zero]
    exact Nat.zero_le _
  · have h1 : 1 ≤ p.totalDegree := Nat.pos_of_ne_zero h0
    calc (A * pderiv i p).totalDegree
        ≤ A.totalDegree + (pderiv i p).totalDegree := totalDegree_mul _ _
      _ ≤ 2 + (p.totalDegree - 1) := add_le_add hA (pderiv_totalDegree_le_sub_one p i)
      _ = p.totalDegree + 1 := by omega

theorem polynomial_first_order_totalDegree_le
    {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]
    (A : σ → MvPolynomial σ R) (B p : MvPolynomial σ R) (n : ℕ)
    (hA : ∀ i, (A i).totalDegree ≤ 2) (hB : B.totalDegree ≤ 1)
    (hp : p.totalDegree ≤ n) :
    (B * p + ∑ i : σ, A i * MvPolynomial.pderiv i p).totalDegree ≤ n + 1 := by
  classical
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · calc (B * p).totalDegree ≤ B.totalDegree + p.totalDegree := totalDegree_mul _ _
      _ ≤ 1 + n := add_le_add hB hp
      _ = n + 1 := by omega
  · refine totalDegree_finsetSum_le (s := Finset.univ) ?_
    intro i _
    calc (A i * pderiv i p).totalDegree ≤ p.totalDegree + 1 := mul_pderiv_totalDegree_le _ _ _ (hA i)
      _ ≤ n + 1 := by omega

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.PolynomialDegreeBounds

end

section
noncomputable section
open scoped BigOperators Classical
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.HarmonicBandDerivatives
open InfinitesimalAction KPCplxIntertwinerEigenvalues
open ComplexFractionalInverse.FiniteFischerRaw
private theorem compact_radius (k : KPCplxCharacterHaar.ComplexSU2) :
    MvPolynomial.eval (compactSphereCoordinate k) radiusQuadratic = 1 := by
  let m : Matrix (Fin 2) (Fin 2) ℂ := k
  have hu : m * star m = 1 := Matrix.mem_unitaryGroup_iff.mp
    (Matrix.specialUnitaryGroup_le_unitaryGroup k.property)
  have hr := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 1 1).re) hu
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Matrix.one_apply_eq] at hr
  simp only [Complex.star_def, Complex.mul_conj', Complex.add_re,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re] at hr
  have hprod : (m 1 0 * star (m 1 1)).re ^ 2 +
      (m 1 0 * star (m 1 1)).im ^ 2 = ‖m 1 0‖ ^ 2 * ‖m 1 1‖ ^ 2 := by
    calc
      _ = Complex.normSq (m 1 0 * star (m 1 1)) := by
        simp only [Complex.normSq_apply, sq]
      _ = _ := by rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, norm_star]
  simp only [radiusQuadratic, Fin.sum_univ_three, map_add, map_pow, MvPolynomial.eval_X,
    compactSphereCoordinate, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  change ((2 * (m 1 0 * star (m 1 1)).re : ℝ) : ℂ)^2 +
    ((2 * (m 1 0 * star (m 1 1)).im : ℝ) : ℂ)^2 +
    ((‖m 1 0‖^2 - ‖m 1 1‖^2 : ℝ) : ℂ)^2 = 1
  norm_cast
  nlinarith [hprod, sq_nonneg (‖m 1 0‖^2 + ‖m 1 1‖^2 - 1)]

theorem polynomialCompactRestriction_homogeneous_band (p : MvPolynomial (Fin 3) ℂ)
    (d n : ℕ) (hp : p.IsHomogeneous d) (hd : d ≤ n) :
    polynomialCompactRestriction p ∈ (Finset.range (n + 1)).sup
      (fun j => (harmonicPolynomials j).map polynomialCompactRestriction) := by
  obtain ⟨h, hh, he⟩ := homogeneous_fischer hp
  have hr : polynomialCompactRestriction p =
      ∑ k ∈ Finset.range (d / 2 + 1), polynomialCompactRestriction (h k) := by
    ext x
    change MvPolynomial.eval (compactSphereCoordinate x) p = _
    rw [he]
    simp [compact_radius, polynomialCompactRestriction]
  rw [hr]
  apply Submodule.sum_mem
  intro k hk
  have hk' : k ≤ d / 2 := by have := Finset.mem_range.mp hk; omega
  apply (Finset.le_sup (f := fun j => (harmonicPolynomials j).map
    polynomialCompactRestriction) (Finset.mem_range.mpr (show d - 2*k < n+1 by omega)))
  exact Submodule.mem_map.mpr ⟨h k, hh k hk', rfl⟩

theorem polynomialCompactRestriction_degree_band (p : MvPolynomial (Fin 3) ℂ)
    (n : ℕ) (hp : p.totalDegree ≤ n) :
    polynomialCompactRestriction p ∈ (Finset.range (n + 1)).sup
      (fun j => (harmonicPolynomials j).map polynomialCompactRestriction) := by
  rw [← MvPolynomial.sum_homogeneousComponent p, map_sum]
  apply Submodule.sum_mem
  intro d hd
  exact polynomialCompactRestriction_homogeneous_band _ d n
    (MvPolynomial.homogeneousComponent_mem d p)
    (by have := Finset.mem_range.mp hd; omega)

theorem harmonic_band_of_compact_image (s : ℝ) (I : Finset ℕ)
    (hInjective : Function.Injective (compactRestriction s))
    (hLift : ∀ j ∈ I, (harmonicPolynomials j).map polynomialCompactRestriction ≤
      (harmonicKType s j).map (compactRestriction s))
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (hf : compactRestriction s f ∈ I.sup
      (fun j => (harmonicPolynomials j).map polynomialCompactRestriction)) :
    f ∈ I.sup (harmonicKType s) := by
  have hm : (I.sup (harmonicKType s)).map (compactRestriction s) =
      I.sup (fun j => (harmonicKType s j).map (compactRestriction s)) := by
    clear hLift hf
    induction I using Finset.induction_on with
    | empty => simp
    | @insert j I hj ih => simp [Finset.sup_insert, ih]
  have he : I.sup (fun j => (harmonicPolynomials j).map polynomialCompactRestriction) ≤
      I.sup (fun j => (harmonicKType s j).map (compactRestriction s)) := by
    apply Finset.sup_le
    intro j hj
    exact (hLift j hj).trans (Finset.le_sup (f := fun j =>
      (harmonicKType s j).map (compactRestriction s)) hj)
  have hmem : compactRestriction s f ∈
      (I.sup (harmonicKType s)).map (compactRestriction s) := by
    rw [hm]
    exact he hf
  obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.mp hmem
  exact hInjective hgf ▸ hg

open CompactDerivativeTransport MvPolynomial
private theorem partials_commute (p : MvPolynomial (Fin 3) ℂ) (i j : Fin 3) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add]; rw [hp, hq]
  | mul_X p k hp =>
    simp only [pderiv_mul, map_add, pderiv_X, Pi.single_apply]
    split_ifs <;> simp_all <;> ring
private theorem lap_rotation (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (polynomialRotation i p) =
      polynomialRotation i (polynomialLaplacian p) := by
  simp only [polynomialLaplacian, polynomialRotation, Fin.sum_univ_three,
    LinearMap.add_apply, LinearMap.comp_apply, Derivation.coeFn_coe,
    map_add, map_sub, pderiv_mul, pderiv_X, Pi.single_apply]
  fin_cases i <;> norm_num <;>
    simp only [partials_commute] <;> ring

private theorem rotation_homogeneous (i : Fin 3) (ℓ : ℕ)
    (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ) :
    (polynomialRotation i p).IsHomogeneous ℓ := by
  cases ℓ with
  | zero =>
    have he : p = C (p.coeff 0) :=
      (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp
        ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hp)
    unfold polynomialRotation
    rw [he]
    simp only [pderiv_C, mul_zero, sub_zero]
    exact isHomogeneous_zero (Fin 3) ℂ 0
  | succ n =>
    have ha := (isHomogeneous_X ℂ (i + 1)).mul (hp.pderiv (i := i + 2))
    have hb := (isHomogeneous_X ℂ (i + 2)).mul (hp.pderiv (i := i + 1))
    simpa only [polynomialRotation, Nat.add_sub_cancel, Nat.add_comm] using ha.sub hb

private theorem rotation_harmonic (i : Fin 3) (ℓ : ℕ)
    (p : MvPolynomial (Fin 3) ℂ) (hp : p ∈ harmonicPolynomials ℓ) :
    polynomialRotation i p ∈ harmonicPolynomials ℓ := by
  refine ⟨rotation_homogeneous i ℓ p hp.1, ?_⟩
  change polynomialLaplacian (polynomialRotation i p) = 0
  rw [lap_rotation, show polynomialLaplacian p = 0 from hp.2]
  simp [polynomialRotation]

theorem compact_derivative_harmonic (s : ℝ) (j : Fin 3) (ℓ : ℕ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (hf : f ∈ harmonicKType s ℓ) :
    localDerivative s (true, j) f ∈ harmonicKType s ℓ := by
  obtain ⟨p, hp, he⟩ := hf
  have hD : compactRestriction s (localDerivative s (true, j) f) =
      polynomialCompactRestriction (compactPolynomialDerivative j p) := by
    apply compact_derivative_transport_of_curves s _ j p f he.symm
    intro j k
    obtain ⟨c, hc, hd⟩ := compact_trig_curve_exists j k
    exact ⟨c, hc, hd, hopf_derivative_of_matrix_tangent j k c hc hd⟩
  refine ⟨compactPolynomialDerivative j p, ?_, hD.symm⟩
  exact (harmonicPolynomials ℓ).smul_mem _ (rotation_harmonic _ ℓ p hp)

theorem compact_derivative_harmonic_band (s : ℝ) (j : Fin 3) (ℓ : ℕ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (hf : f ∈ harmonicKType s ℓ) :
    localDerivative s (true, j) f ∈
      (Finset.range (ℓ + 2)).sup (harmonicKType s) := by
  exact (Finset.le_sup (f := harmonicKType s) (Finset.mem_range.mpr (by omega : ℓ < ℓ + 2)))
    (compact_derivative_harmonic s j ℓ f hf)

theorem derivative_harmonic_band (s : ℝ) (b : LocalBasis) (ℓ : ℕ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (hf : f ∈ KPCplxIntertwinerEigenvalues.harmonicKType s ℓ) :
    localDerivative s b f ∈
      (Finset.range (ℓ + 2)).sup (KPCplxIntertwinerEigenvalues.harmonicKType s) := by
  obtain ⟨b, j⟩ := b
  cases b with
  | true => exact compact_derivative_harmonic_band s j ℓ f hf
  | false =>
    obtain ⟨p, hp, hpf⟩ := Submodule.mem_map.mp hf
    obtain ⟨A, B, hA, hB, hD⟩ :=
      NoncompactAction.PolynomialDerivatives.noncompact_derivative_polynomial_coefficients s j
    have hq : (B * p + ∑ i : Fin 3, A i * MvPolynomial.pderiv i p).totalDegree ≤
        ℓ + 1 :=
      NoncompactAction.PolynomialDegreeBounds.polynomial_first_order_totalDegree_le A B p ℓ hA hB
        (show p.IsHomogeneous ℓ from hp.1).totalDegree_le
    apply harmonic_band_of_compact_image s _
      (harmonicKType_compact_identification s s 0).1
    · intro d _ u hu
      obtain ⟨r, hr, hru⟩ := Submodule.mem_map.mp hu
      obtain ⟨g, hg⟩ := NoncompactAction.PolynomialCompactRestriction.polynomialCompactRestriction_lift s r
      apply Submodule.mem_map.mpr
      refine ⟨g, ?_, hg.trans hru⟩
      change compactRestriction s g ∈
        (harmonicPolynomials d).map polynomialCompactRestriction
      rw [hg]
      exact Submodule.mem_map.mpr ⟨r, hr, rfl⟩
    · rw [hD p f hpf.symm]
      convert polynomialCompactRestriction_degree_band _ (ℓ + 1) hq using 1

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.HarmonicBandDerivatives

end

end
