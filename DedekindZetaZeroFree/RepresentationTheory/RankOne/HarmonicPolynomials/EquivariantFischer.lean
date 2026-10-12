module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.HarmonicPolynomials.HomogeneousTrace
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import DedekindZetaZeroFree.RepresentationTheory.FiniteDimensional.CharactersAndKernels

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.HarmonicVendor.HomogeneousRaw
open KPCplxHarmonicIntertwinerSpectrum KPCplxCharacterHaar
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
lemma radius_homogeneous : radiusQuadratic.IsHomogeneous 2 := by
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

lemma lap_hom {p : MvPolynomial (Fin 3) ℂ} {n : ℕ}
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

private lemma bottom_norm (g : ComplexSU2) :
    ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re^2 +
    ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im^2 +
    ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re^2 +
    ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1).im^2 = 1 := by
  have hg := g.property.1.2
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 1 1).re) hg
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
    Complex.mul_re, sq] at hh
  nlinarith
private lemma rows (g : ComplexSU2) (i k : Fin 3) :
    ∑ j, sphereMatrix g i j * sphereMatrix g k j = if i=k then 1 else 0 := by
  have hn := bottom_norm g
  have hnc := congrArg (fun x : ℝ => (x : ℂ)) hn
  push_cast at hnc
  have hh : ( (((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re : ℂ)^2 +
    (((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im : ℂ)^2 +
    (((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re : ℂ)^2 +
    (((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1).im : ℂ)^2 )^2 = 1 := by rw [hnc]; norm_num
  fin_cases i <;> fin_cases k <;> simp [sphereMatrix, Fin.sum_univ_three] <;>
    solve | ring | (convert hh using 1 <;> ring)
private lemma cols (g : ComplexSU2) (i k : Fin 3) :
    ∑ j, sphereMatrix g j i * sphereMatrix g j k = if i=k then 1 else 0 := by
  have hn := bottom_norm g
  have hnc := congrArg (fun x : ℝ => (x : ℂ)) hn
  push_cast at hnc
  have hh : ( (((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re : ℂ)^2 +
    (((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im : ℂ)^2 +
    (((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re : ℂ)^2 +
    (((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1).im : ℂ)^2 )^2 = 1 := by rw [hnc]; norm_num
  fin_cases i <;> fin_cases k <;> simp [sphereMatrix, Fin.sum_univ_three] <;>
    solve | ring | (convert hh using 1 <;> ring)

noncomputable def linearSubstitution (A : Matrix (Fin 3) (Fin 3) ℂ) :
    MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j)

private theorem pderiv_linearSubstitution (A : Matrix (Fin 3) (Fin 3) ℂ)
    (p : MvPolynomial (Fin 3) ℂ) (j : Fin 3) :
    MvPolynomial.pderiv j (linearSubstitution A p) =
      ∑ i, MvPolynomial.C (A i j) * linearSubstitution A (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [linearSubstitution]
  | add p q ihp ihq =>
      simp only [map_add, ihp, ihq, mul_add, Finset.sum_add_distrib]
  | mul_X p i ih =>
      simp only [map_mul, linearSubstitution, MvPolynomial.aeval_X]
      rw [MvPolynomial.pderiv_mul]
      simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
        map_add, map_mul, map_sum, MvPolynomial.pderiv_C, zero_mul, zero_add]
      unfold linearSubstitution at ih
      rw [ih]
      simp [Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib,
        Pi.single_apply, mul_add, mul_ite, mul_assoc, mul_comm, mul_left_comm]

private theorem polynomialLaplacian_linearSubstitution (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ i k, ∑ j, A i j * A k j = if i = k then 1 else 0)
    (p : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (linearSubstitution A p) = linearSubstitution A (polynomialLaplacian p) := by
  classical
  simp only [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    map_sum]
  change (∑ j, MvPolynomial.pderiv j (MvPolynomial.pderiv j (linearSubstitution A p))) =
    ∑ j, linearSubstitution A (MvPolynomial.pderiv j (MvPolynomial.pderiv j p))
  simp only [pderiv_linearSubstitution, map_sum, MvPolynomial.pderiv_C_mul]
  simp only [pderiv_linearSubstitution, Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum]
  simp_rw [hA]
  simp

theorem coefficientAction_harmonic (n : ℕ) (g : ComplexSU2) (p : Harmonic n) :
    coefficientAction g p ∈ harmonicPolynomials n := by
  refine ⟨coefficientAction_homogeneous n g ⟨p.val, p.property.1⟩, ?_⟩
  change polynomialLaplacian (linearSubstitution (sphereMatrix g) p.val) = 0
  rw [polynomialLaplacian_linearSubstitution _ (rows g)]
  have hp : polynomialLaplacian p.val = 0 := p.property.2
  rw [hp, map_zero]

def harmonicRepresentation (n : ℕ) : Representation ℂ ComplexSU2 (Harmonic n) where
  toFun g :=
    { toFun p := ⟨coefficientAction g p, coefficientAction_harmonic n g p⟩
      map_add' p q := Subtype.ext (map_add _ _ _)
      map_smul' c p := Subtype.ext (map_smul _ _ _) }
  map_one' := by
    apply LinearMap.ext
    intro p
    exact Subtype.ext (coefficientAction_one p)
  map_mul' g h := by
    apply LinearMap.ext
    intro p
    exact Subtype.ext (coefficientAction_mul g h p)

instance harmonicFiniteDimensional (n : ℕ) : FiniteDimensional ℂ (Harmonic n) :=
  Submodule.finiteDimensional_of_le inf_le_left

theorem coefficientAction_radius (g : ComplexSU2) :
    coefficientAction g radiusQuadratic = radiusQuadratic := by
  simp only [radiusQuadratic, map_sum, map_pow, coefficientAction, pow_two, map_mul, aeval_X,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    arg 2
    intro j
    arg 2
    intro i
    arg 2
    intro k
    rw [mul_mul_mul_comm, ← C_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum, cols]
  simp

def radialLap (n : ℕ) : Homogeneous n →ₗ[ℂ] Homogeneous n where
  toFun p := ⟨polynomialLaplacian (radiusQuadratic * p.val), by
    simpa using lap_hom (radius_homogeneous.mul p.property)⟩
  map_add' p q := by apply Subtype.ext; simp [mul_add]
  map_smul' c p := by apply Subtype.ext; simp [mul_smul_comm]
private lemma radialLap_surj (n : ℕ) : Function.Surjective (radialLap n) := by
  intro q
  obtain ⟨h,hh,he⟩ := homogeneous_fischer q.property
  let c (k : ℕ) : ℂ :=
    2 * ((k+1 : ℕ) : ℂ) * (2 * ((n - 2*k : ℕ) : ℂ) + 2 * ((k+1 : ℕ) : ℂ) + 1)
  let p : Polynomial := ∑ k ∈ Finset.range (n/2+1), radiusQuadratic^k * ((c k)⁻¹ • h k)
  have hp : p.IsHomogeneous n := by
    apply IsHomogeneous.sum
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hs : (radiusQuadratic^k * ((c k)⁻¹ • h k)).IsHomogeneous (2*k + (n-2*k)) :=
      (radius_homogeneous.pow k).mul ((harmonicPolynomials _).smul_mem (c k)⁻¹ (hh k (by omega))).1
    convert hs using 1 <;> omega
  refine ⟨⟨p,hp⟩, ?_⟩
  apply Subtype.ext
  change polynomialLaplacian (radiusQuadratic * p) = q.val
  rw [he]
  dsimp [p]
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hhk := hh k (by omega)
  have hg : ((c k)⁻¹ • h k) ∈ harmonicPolynomials (n - 2*k) :=
    (harmonicPolynomials _).smul_mem _ hhk
  have hc : c k ≠ 0 := by
    dsimp [c]
    norm_cast
  rw [← mul_assoc, ← pow_succ', laplacian_radius_pow hg.1]
  have hz : polynomialLaplacian ((c k)⁻¹ • h k) = 0 := hg.2
  change _ + c k • (radiusQuadratic ^ (k+1-1) * ((c k)⁻¹ • h k)) = _
  rw [hz]
  simp only [mul_zero, zero_add, Nat.add_sub_cancel, mul_smul_comm, smul_smul,
    mul_inv_cancel₀ hc, one_smul]
private lemma radialLap_inj (n : ℕ) : Function.Injective (radialLap n) :=
  (LinearMap.injective_iff_surjective).mpr (radialLap_surj n)

theorem equivariant_fischer_split (n : ℕ) :
    ∃ e : (Representation.prod (harmonicRepresentation (n + 2))
        (homogeneousRepresentation n)).Equiv (homogeneousRepresentation (n + 2)),
      ∀ h p, (e (h, p) : Polynomial) = (h : Polynomial) + radiusQuadratic * (p : Polynomial) := by
  let f : (Representation.prod (harmonicRepresentation (n+2)) (homogeneousRepresentation n)).IntertwiningMap
      (homogeneousRepresentation (n+2)) :=
    { toFun hp := ⟨hp.1.val + radiusQuadratic * hp.2.val,
        hp.1.property.1.add (by simpa [Nat.add_comm] using radius_homogeneous.mul hp.2.property)⟩
      map_add' p q := by apply Subtype.ext; simp; ring
      map_smul' c p := by apply Subtype.ext; simp [mul_smul_comm]
      isIntertwining' g := by
        apply LinearMap.ext
        intro hp
        apply Subtype.ext
        change coefficientAction g hp.1.val + radiusQuadratic * coefficientAction g hp.2.val =
          coefficientAction g (hp.1.val + radiusQuadratic * hp.2.val)
        simp [coefficientAction_radius, map_add, map_mul] }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hxy' : x.1.val + radiusQuadratic * x.2.val = y.1.val + radiusQuadratic * y.2.val :=
        congrArg (fun z : Homogeneous (n+2) => z.val) hxy
      have hxl : polynomialLaplacian x.1.val = 0 := x.1.property.2
      have hyl : polynomialLaplacian y.1.val = 0 := y.1.property.2
      have hl := congrArg polynomialLaplacian hxy'
      simp only [map_add, hxl, hyl, zero_add] at hl
      have hp : x.2 = y.2 := radialLap_inj n (Subtype.ext hl)
      have hhp : x.1 = y.1 := by
        apply Subtype.ext
        rw [hp] at hxy'
        exact add_right_cancel hxy'
      exact Prod.ext hhp hp
    · intro q
      let l : Homogeneous n := ⟨polynomialLaplacian q.val, by simpa using lap_hom q.property⟩
      obtain ⟨p,hp⟩ := radialLap_surj n l
      have hp' : polynomialLaplacian (radiusQuadratic * p.val) = polynomialLaplacian q.val :=
        congrArg (fun z : Homogeneous n => z.val) hp
      let h : Harmonic (n+2) := ⟨q.val - radiusQuadratic * p.val,
        q.property.sub (by simpa [Nat.add_comm] using radius_homogeneous.mul p.property), by
          change polynomialLaplacian (q.val - radiusQuadratic * p.val) = 0
          rw [map_sub, hp', sub_self]⟩
      refine ⟨(h,p), ?_⟩
      apply Subtype.ext
      change q.val - radiusQuadratic * p.val + radiusQuadratic * p.val = q.val
      ring
  exact ⟨f.ofBijective hf, fun h p => rfl⟩

theorem equivariant_fischer_low (n : ℕ) (hn : n ≤ 1) :
    ∃ e : (harmonicRepresentation n).Equiv (homogeneousRepresentation n),
      ∀ h, (e h : Polynomial) = (h : Polynomial) := by
  let f : (harmonicRepresentation n).IntertwiningMap (homogeneousRepresentation n) :=
    { toFun p := ⟨p.val,p.property.1⟩
      map_add' p q := rfl
      map_smul' c p := rfl
      isIntertwining' g := by ext p; rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      apply Subtype.ext
      exact congrArg (fun x : Homogeneous n => (x : Polynomial)) h
    · intro p
      refine ⟨⟨p.val, p.property, ?_⟩, rfl⟩
      change polynomialLaplacian p.val = 0
      have hp : p.val.IsHomogeneous n := p.property
      have hzero {q : Polynomial} (hq : q.IsHomogeneous 0) (i : Fin 3) : pderiv i q = 0 := by
        rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hq
        rw [hq, pderiv_C]
      change (∑ i : Fin 3, pderiv i (pderiv i p.val)) = 0
      apply Finset.sum_eq_zero
      intro i hi
      apply hzero
      convert hp.pderiv using 1
      omega
  exact ⟨f.ofBijective hf, fun h => rfl⟩

theorem homogeneous_character_recurrence (n : ℕ) (g : ComplexSU2) :
    (homogeneousRepresentation (n + 2)).character g =
      (harmonicRepresentation (n + 2)).character g + (homogeneousRepresentation n).character g := by
  obtain ⟨e, he⟩ := equivariant_fischer_split n
  rw [← Representation.char_iso e]
  exact Representation.char_prod _ _ g

theorem homogeneous_character_zero (g : ComplexSU2) :
    (homogeneousRepresentation 0).character g = (harmonicRepresentation 0).character g := by
  obtain ⟨e, he⟩ := equivariant_fischer_low 0 (by omega)
  exact congrFun (Representation.char_iso e).symm g

theorem homogeneous_character_one (g : ComplexSU2) :
    (homogeneousRepresentation 1).character g = (harmonicRepresentation 1).character g := by
  obtain ⟨e, he⟩ := equivariant_fischer_low 1 (by omega)
  exact congrFun (Representation.char_iso e).symm g

end DedekindZetaZeroFree.HarmonicVendor.HomogeneousRaw

end
