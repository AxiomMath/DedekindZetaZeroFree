module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.HarmonicPolynomials.EquivariantFischer
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.HarmonicVendor
open KPCplxCharacterHaar KPCplxHarmonicIntertwinerSpectrum
open scoped BigOperators
open scoped ComplexConjugate

abbrev Polynomial := MvPolynomial (Fin 3) ℂ
abbrev Harmonic (ℓ : ℕ) := ↥(harmonicPolynomials ℓ)

def Q (x : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![x 2, x 0 - Complex.I * x 1; x 0 + Complex.I * x 1, -x 2]

def sphereMatrix (g : ComplexSU2) : Matrix (Fin 3) (Fin 3) ℂ :=
  let a := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  let b := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
  fun i j => (((!![
    b.re^2-b.im^2-a.re^2+a.im^2, 2*b.re*b.im-2*a.re*a.im, -2*a.re*b.re-2*a.im*b.im;
    -2*b.re*b.im-2*a.re*a.im, b.re^2-b.im^2+a.re^2-a.im^2, -2*a.im*b.re+2*a.re*b.im;
    2*a.re*b.re-2*a.im*b.im, 2*a.re*b.im+2*a.im*b.re, b.re^2+b.im^2-a.re^2-a.im^2]
      : Matrix (Fin 3) (Fin 3) ℝ) i j) : ℂ)

def S (g : ComplexSU2) (x : Fin 3 → ℂ) : Fin 3 → ℂ := (sphereMatrix g).mulVec x

private theorem hopf_top00 (g : ComplexSU2) : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) (Matrix.specialUnitaryGroup.star_eq_adjugate g)
  simp only [Matrix.adjugate_fin_two, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at h
  exact h.symm
private theorem hopf_top01 (g : ComplexSU2) : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = -star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) (Matrix.specialUnitaryGroup.star_eq_adjugate g)
  simp only [Matrix.adjugate_fin_two, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at h
  simpa only [neg_neg] using congrArg Neg.neg h.symm

private theorem hopf_Q_injective : Function.Injective Q := by
  intro x y h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) h
  simp [Q] at h00 h01 h10
  funext i
  fin_cases i
  · change x 0 = y 0
    linear_combination (h01 + h10) / 2
  · change x 1 = y 1
    linear_combination (norm := (ring_nf; simp [Complex.I_sq])) Complex.I * (h01 - h10) / 2
  · exact h00

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in

theorem Q_S (g : ComplexSU2) (x : Fin 3 → ℂ) :
    Q (S g x) = star (g : Matrix (Fin 2) (Fin 2) ℂ) * Q x * g := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    simp [Q, S, sphereMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Fin.sum_univ_succ, Matrix.star_eq_conjTranspose,
      hopf_top00, hopf_top01] <;>
    apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      ← Complex.ofReal_pow] <;> ring

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in

theorem compactSphereCoordinate_mul (k g : ComplexSU2) :
    compactSphereCoordinate (k * g) = S g (compactSphereCoordinate k) := by
  have hmul : ((k * g : ComplexSU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      (k : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  funext i
  fin_cases i <;>
    simp [compactSphereCoordinate, S, sphereMatrix, hmul, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_succ,
      hopf_top00, hopf_top01, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply] <;>
    apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      ← Complex.ofReal_pow] <;> ring

theorem sphereMatrix_mul (g h : ComplexSU2) :
    sphereMatrix (g * h) = sphereMatrix h * sphereMatrix g := by
  apply Matrix.mulVec_injective
  funext x
  change S (g * h) x = (sphereMatrix h * sphereMatrix g).mulVec x
  rw [← Matrix.mulVec_mulVec]
  change S (g * h) x = S h (S g x)
  apply hopf_Q_injective
  rw [Q_S, Q_S, Q_S]
  have hmul : ((g * h : ComplexSU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) * (h : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  rw [hmul, star_mul]
  simp only [Matrix.mul_assoc]

theorem sphereMatrix_one : sphereMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sphereMatrix]

def coefficientAction (g : ComplexSU2) : Polynomial →ₐ[ℂ] Polynomial :=
  MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (sphereMatrix g i j) * MvPolynomial.X j)

theorem coefficientAction_eval (g : ComplexSU2) (p : Polynomial) (x : Fin 3 → ℂ) :
    MvPolynomial.eval x (coefficientAction g p) = MvPolynomial.eval (S g x) p := by
  change MvPolynomial.aeval x (MvPolynomial.aeval _ p) = MvPolynomial.aeval _ p
  rw [MvPolynomial.comp_aeval_apply]
  congr 2
  funext i
  simp [S, Matrix.mulVec, dotProduct]

theorem coefficientAction_one (p : Polynomial) : coefficientAction 1 p = p := by
  have h : coefficientAction 1 = AlgHom.id ℂ Polynomial := by
    ext i
    simp [coefficientAction, sphereMatrix_one, Matrix.one_apply]
  exact congrArg (fun f : Polynomial →ₐ[ℂ] Polynomial => f p) h

theorem coefficientAction_mul (g h : ComplexSU2) (p : Polynomial) :
    coefficientAction (g * h) p = coefficientAction g (coefficientAction h p) := by
  have hh : coefficientAction (g * h) = (coefficientAction g).comp (coefficientAction h) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [coefficientAction, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum,
      map_mul, MvPolynomial.aeval_C, sphereMatrix_mul, Matrix.mul_apply]
    simp only [Finset.mul_sum, Finset.sum_mul, ← mul_assoc, ← MvPolynomial.C_mul,
      ← map_sum]
    simp only [MvPolynomial.algebraMap_eq, map_sum, Finset.sum_mul, ← MvPolynomial.C_mul]
    rw [Finset.sum_comm]
  exact congrArg (fun f : Polynomial →ₐ[ℂ] Polynomial => f p) hh

private theorem pderiv_coefficientAction (g : ComplexSU2)
    (p : MvPolynomial (Fin 3) ℂ) (j : Fin 3) :
    MvPolynomial.pderiv j (coefficientAction g p) =
      ∑ i, MvPolynomial.C (sphereMatrix g i j) * coefficientAction g (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [coefficientAction]
  | add p q ihp ihq =>
      simp only [map_add, ihp, ihq, mul_add, Finset.sum_add_distrib]
  | mul_X p i ih =>
      simp only [map_mul, coefficientAction, MvPolynomial.aeval_X]
      rw [MvPolynomial.pderiv_mul]
      simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
        map_add, map_mul, map_sum, MvPolynomial.pderiv_C, zero_mul, zero_add]
      unfold coefficientAction at ih
      rw [ih]
      simp [Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib,
        Pi.single_apply, mul_add, mul_ite, mul_assoc, mul_comm, mul_left_comm]

private theorem polynomialLaplacian_coefficientAction (g : ComplexSU2)
    (hA : ∀ i k, ∑ j, sphereMatrix g i j * sphereMatrix g k j = if i = k then 1 else 0)
    (p : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (coefficientAction g p) = coefficientAction g (polynomialLaplacian p) := by
  classical
  simp only [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    map_sum]
  change (∑ j, MvPolynomial.pderiv j (MvPolynomial.pderiv j (coefficientAction g p))) =
    ∑ j, coefficientAction g (MvPolynomial.pderiv j (MvPolynomial.pderiv j p))
  simp only [pderiv_coefficientAction, map_sum, MvPolynomial.pderiv_C_mul]
  simp only [pderiv_coefficientAction, Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum]
  simp_rw [hA]
  simp

private theorem coefficientAction_homogeneous (g : ComplexSU2)
    (p : MvPolynomial (Fin 3) ℂ) (ℓ : ℕ) (hp : p.IsHomogeneous ℓ) :
    (coefficientAction g p).IsHomogeneous ℓ := by
  unfold coefficientAction
  simpa using hp.aeval (fun i => ∑ j, MvPolynomial.C (sphereMatrix g i j) * MvPolynomial.X j)
    (fun i => MvPolynomial.IsHomogeneous.sum _ _ 1 (fun j _ =>
      MvPolynomial.isHomogeneous_C_mul_X _ _))

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

private theorem sphereMatrix_orthogonal (g : ComplexSU2) (i k : Fin 3) :
    ∑ j, sphereMatrix g i j * sphereMatrix g k j = if i = k then 1 else 0 := by
  let a := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  let b := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
  have h := su2_row_norm g
  fin_cases i <;> fin_cases k <;>
    simp [sphereMatrix, Fin.sum_univ_three, ← Complex.ofReal_mul,
      ← Complex.ofReal_add]
  all_goals norm_cast
  all_goals first | (solve | ring) | (calc
    _ = (a.re^2+a.im^2+b.re^2+b.im^2)^2 := by dsimp [a, b]; ring
    _ = _ := by rw [h]; norm_num)

theorem coefficientAction_mem (ℓ : ℕ) (g : ComplexSU2) (p : Harmonic ℓ) :
    coefficientAction g p ∈ harmonicPolynomials ℓ := by
  refine ⟨coefficientAction_homogeneous g p ℓ p.property.1, ?_⟩
  change polynomialLaplacian (coefficientAction g p) = 0
  rw [polynomialLaplacian_coefficientAction g (sphereMatrix_orthogonal g)]
  have hp : polynomialLaplacian p = 0 := p.property.2
  rw [hp, map_zero]

def harmonicRepresentation (ℓ : ℕ) : Representation ℂ ComplexSU2 (Harmonic ℓ) where
  toFun g :=
    { toFun p := ⟨coefficientAction g p, coefficientAction_mem ℓ g p⟩
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

theorem harmonicRepresentation_restriction (ℓ : ℕ) (g k : ComplexSU2) (p : Harmonic ℓ) :
    polynomialCompactRestriction (harmonicRepresentation ℓ g p) k =
      polynomialCompactRestriction p (k * g) := by
  change MvPolynomial.eval (compactSphereCoordinate k) (coefficientAction g p) =
    MvPolynomial.eval (compactSphereCoordinate (k * g)) p
  rw [coefficientAction_eval, compactSphereCoordinate_mul]

instance harmonicFiniteDimensional (ℓ : ℕ) : FiniteDimensional ℂ (Harmonic ℓ) := by
  letI : Module.Finite ℂ ↥(MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ) :=
    Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ ℓ)
  exact Submodule.finiteDimensional_of_le inf_le_left

def harmonicCoordinates (ℓ : ℕ) :
    Harmonic ℓ ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ (Harmonic ℓ))) :=
  (Module.finBasis ℂ (Harmonic ℓ)).equivFun.trans
    (EuclideanSpace.equiv _ ℂ).toLinearEquiv.symm

instance harmonicNormedAddCommGroup (ℓ : ℕ) : NormedAddCommGroup (Harmonic ℓ) :=
  NormedAddCommGroup.induced _ _ (harmonicCoordinates ℓ).toLinearMap
    (harmonicCoordinates ℓ).injective
instance harmonicNormedSpace (ℓ : ℕ) : NormedSpace ℂ (Harmonic ℓ) :=
  NormedSpace.induced ℂ _ _ (harmonicCoordinates ℓ).toLinearMap

def harmonicContRepresentation (ℓ : ℕ) : ContRepresentation ℂ ComplexSU2 (Harmonic ℓ) where
  toMonoidHom :=
    { toFun g := LinearMap.toContinuousLinearMap (harmonicRepresentation ℓ g)
      map_one' := by
        apply ContinuousLinearMap.ext
        intro p
        exact congrArg (fun f : Module.End ℂ (Harmonic ℓ) => f p)
          (harmonicRepresentation ℓ).map_one
      map_mul' g h := by
        apply ContinuousLinearMap.ext
        intro p
        exact congrArg (fun f : Module.End ℂ (Harmonic ℓ) => f p)
          ((harmonicRepresentation ℓ).map_mul g h) }

private theorem sphereMatrix_entry_continuous (i j : Fin 3) :
    Continuous (fun g : ComplexSU2 => sphereMatrix g i j) := by
  have h (i j : Fin 2) : Continuous (fun g : ComplexSU2 =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  have hr (i j : Fin 2) := Complex.continuous_re.comp (h i j)
  have hi (i j : Fin 2) := Complex.continuous_im.comp (h i j)
  fin_cases i <;> fin_cases j <;> dsimp [sphereMatrix]
  all_goals fun_prop

private theorem coefficientAction_coeff_continuous (p : Polynomial)
    (d : Fin 3 →₀ ℕ) :
    Continuous (fun g : ComplexSU2 => (coefficientAction g p).coeff d) := by
  classical
  induction p using MvPolynomial.induction_on generalizing d with
  | C c => simpa [coefficientAction] using
      (continuous_const : Continuous (fun _ : ComplexSU2 => (MvPolynomial.C c).coeff d))
  | add p q hp hq =>
      simp only [map_add, MvPolynomial.coeff_add]
      exact (hp d).add (hq d)
  | mul_X p i hp =>
      simp only [map_mul, coefficientAction, MvPolynomial.aeval_X,
        Finset.mul_sum, MvPolynomial.coeff_sum]
      apply continuous_finset_sum
      intro j hj
      simp only [mul_left_comm (MvPolynomial.aeval _ p), MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_mul_X']
      split_ifs
      · exact (sphereMatrix_entry_continuous i j).mul (hp _)
      · simp only [mul_zero]
        exact continuous_const

def harmonicCoefficientMap (ℓ : ℕ) :
    Harmonic ℓ →ₗ[ℂ] ((Fin 3 →₀ ℕ) → ℂ) :=
  LinearMap.pi (fun d => (MvPolynomial.lcoeff ℂ d).comp (harmonicPolynomials ℓ).subtype)

theorem harmonicContRepresentation_continuous (ℓ : ℕ) :
    Continuous (harmonicContRepresentation ℓ) := by
  rw [continuous_clm_apply]
  intro p
  have hinj : Function.Injective (harmonicCoefficientMap ℓ) := by
    intro a b h
    apply Subtype.ext
    apply MvPolynomial.ext
    intro d
    exact congrFun h d
  have he := LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  apply he.isEmbedding.isInducing.continuous_iff.mpr
  apply continuous_pi
  intro d
  exact coefficientAction_coeff_continuous p d

def triangle (n : ℕ) (f : ℤ → ℂ) :=
  ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n - a + 1), f ((a : ℤ) - b)
private theorem triangle_border (n : ℕ) (f : ℤ → ℂ) :
    triangle (n + 2) f = (∑ a ∈ Finset.range (n + 3), f a) +
      (∑ b ∈ Finset.range (n + 2), f (-(b : ℤ) - 1)) + triangle n f := by
  unfold triangle
  rw [show n + 2 + 1 = (n + 2) + 1 by omega, Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_sub, Nat.sub_zero]
  have h (a : ℕ) (ha : a ∈ Finset.range (n + 2)) :
      (∑ b ∈ Finset.range (n + 2 - (a + 1) + 1), f ((↑(a + 1) : ℤ) - b)) =
        f (a + 1) + ∑ b ∈ Finset.range (n + 1 - a), f ((a : ℤ) - b) := by
    have ha' := Finset.mem_range.mp ha
    rw [show n + 2 - (a + 1) + 1 = (n + 1 - a) + 1 by omega, Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, sub_zero]
    simp_rw [show ∀ b : ℕ, ((a : ℤ) + 1 - (b + 1)) = (a : ℤ) - b by intro b; push_cast; ring]
    simp [add_comm]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib]
  have hinter : (∑ a ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 1 - a), f ((a : ℤ) - b)) =
      ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n - a + 1), f ((a : ℤ) - b) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ]
    simp only [Nat.sub_self, Finset.range_zero, Finset.sum_empty, add_zero]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' := Finset.mem_range.mp ha
    rw [show n + 1 - a = n - a + 1 by omega]
  rw [hinter]
  rw [Finset.sum_range_succ' (f := fun a : ℕ => f (a : ℤ)) (n := n + 2)]
  rw [Finset.sum_range_succ' (f := fun b : ℕ => f (-(b : ℤ))) (n := n + 2)]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, neg_zero, neg_add, sub_eq_add_neg]
  ring
private theorem border_string (n : ℕ) (f : ℤ → ℂ) :
    (∑ a ∈ Finset.range (n + 1), f a) +
      (∑ b ∈ Finset.range n, f (-(b : ℤ) - 1)) =
      ∑ i ∈ Finset.range (2 * n + 1), f ((i : ℤ) - n) := by
  have hpos : (∑ a ∈ Finset.range (n + 1), f a) =
      ∑ a ∈ Finset.range (n + 1), f (((n + a : ℕ) : ℤ) - n) := by
    simp
  have hneg : (∑ b ∈ Finset.range n, f (-(b : ℤ) - 1)) =
      ∑ b ∈ Finset.range n, f ((b : ℤ) - n) := by
    rw [← Finset.sum_range_reflect (fun b : ℕ => f ((b : ℤ) - n)) n]
    apply Finset.sum_congr rfl
    intro b hb
    have hb' := Finset.mem_range.mp hb
    congr 1
    omega
  rw [hpos, hneg, add_comm]
  rw [show 2 * n + 1 = n + (n + 1) by omega]
  exact (Finset.sum_range_add (fun i : ℕ => f ((i : ℤ) - n)) n (n + 1)).symm
private theorem triangle_low (f : ℤ → ℂ) :
    triangle 0 f = ∑ i ∈ Finset.range 1, f ((i : ℤ) - 0) := by
  simp [triangle]
private theorem triangle_one (f : ℤ → ℂ) :
    triangle 1 f = ∑ i ∈ Finset.range 3, f ((i : ℤ) - 1) := by
  simp [triangle, Finset.sum_range_succ]
  ring
private theorem raw_harmonic_eq (n : ℕ) :
    HomogeneousRaw.harmonicRepresentation n = harmonicRepresentation n := by
  ext g p : 2
  apply Subtype.ext
  rfl
private theorem raw_character_torus (n : ℕ) (z : Circle) :
    (HomogeneousRaw.harmonicRepresentation n).character (TauCeti.SU2.torusHom z) =
      (TauCeti.SU2.symPower (2 * n)).character (TauCeti.SU2.torusHom z) := by
  have hh (m : ℕ) : (HomogeneousRaw.homogeneousRepresentation m).character (TauCeti.SU2.torusHom z) =
      triangle m (fun i => (z : ℂ) ^ (2 * i)) := HomogeneousRaw.homogeneous_torus_trace m z
  have hs (m : ℕ) : (TauCeti.SU2.symPower (2 * m)).character (TauCeti.SU2.torusHom z) =
      ∑ i ∈ Finset.range (2 * m + 1), (z : ℂ) ^ (2 * ((i : ℤ) - m)) := by
    rw [TauCeti.SU2.character_symPower_torusHom_zpow]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    push_cast
    ring
  by_cases hn : n ≤ 1
  · interval_cases n
    · rw [← HomogeneousRaw.homogeneous_character_zero, hh, hs]
      exact triangle_low _
    · rw [← HomogeneousRaw.homogeneous_character_one, hh, hs]
      exact triangle_one _
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hrec := HomogeneousRaw.homogeneous_character_recurrence m (TauCeti.SU2.torusHom z)
    rw [hh, hh, triangle_border] at hrec
    rw [show m + 3 = (m + 2) + 1 by omega,
      border_string (m + 2) (fun i => (z : ℂ) ^ (2 * i)), ← hs] at hrec
    linear_combination -hrec

theorem harmonic_character (ℓ : ℕ) (g : ComplexSU2) :
    (harmonicRepresentation ℓ).character g = (TauCeti.SU2.symPower (2 * ℓ)).character g := by
  obtain ⟨z, hz⟩ := TauCeti.SU2.exists_isConj_torusHom g
  obtain ⟨a, ha⟩ := isConj_iff.mp hz
  have h := raw_character_torus ℓ z
  rw [raw_harmonic_eq, ← ha, Representation.char_conj, Representation.char_conj] at h
  exact h

theorem harmonic_equiv_symPower (ℓ : ℕ) :
    Nonempty ((harmonicRepresentation ℓ).Equiv (TauCeti.SU2.symPower (2 * ℓ))) := by
  open TauCeti in
    let e := (harmonicCoordinates ℓ).toContinuousLinearEquiv
    let ρ := ContRepresentation.congr e (harmonicContRepresentation ℓ)
    have hρ : Continuous ρ := ContRepresentation.continuous_congr e
      (harmonicContRepresentation_continuous ℓ)
    let s := SU2.symPowerModel (2 * ℓ)
    have hs : Continuous s := SU2.continuous_symPowerModel _
    obtain ⟨a, ha⟩ := _root_.ContRepresentation.exists_isUnitary_congr s hs
    let π := ContRepresentation.congr a s
    have hπ : Continuous π := ContRepresentation.continuous_congr a hs
    have hi : Representation.IsIrreducible π.toRepresentation :=
      ContRepresentation.isIrreducible_congr a (SU2.isIrreducible_symPowerModel _)
    let Eρ : (harmonicRepresentation ℓ).Equiv ρ.toRepresentation :=
      Representation.Equiv.mk e.toLinearEquiv (fun g => by
        apply LinearMap.ext
        intro p
        change e (harmonicRepresentation ℓ g p) = ρ g (e p)
        simp only [ρ, ContRepresentation.congr_apply, ContinuousLinearEquiv.symm_apply_apply]
        rfl)
    let Eπ : (SU2.symPower (2 * ℓ)).Equiv π.toRepresentation :=
      (SU2.symPowerModelEquiv _).trans (Representation.Equiv.mk a.toLinearEquiv (fun g => by
        apply LinearMap.ext
        intro p
        change a (s g p) = π g (a p)
        simp only [π, ContRepresentation.congr_apply, ContinuousLinearEquiv.symm_apply_apply]))
    have hc : ρ.character hρ = π.character hπ := by
      ext g
      simp only [_root_.ContRepresentation.coe_character]
      rw [← Representation.char_iso Eρ, ← Representation.char_iso Eπ]
      exact harmonic_character ℓ g
    have hd : Module.finrank ℂ (EuclideanSpace ℂ (Fin (Module.finrank ℂ (Harmonic ℓ)))) =
        Module.finrank ℂ (EuclideanSpace ℂ (Fin (2 * ℓ + 1))) := by
      have := congrArg (fun f : ComplexSU2 → ℂ => f 1)
        (congrArg DFunLike.coe hc)
      simp only [_root_.ContRepresentation.coe_character, Representation.char_one] at this
      exact_mod_cast this
    by_contra hn
    have hz : ∀ f : ContIntertwiningMap ρ π, f.toContinuousLinearMap = 0 := by
      intro f
      letI : Representation.IsIrreducible π.toRepresentation := hi
      rcases Representation.IsIrreducible.surjective_or_eq_zero f.toIntertwiningMap with hf | hf
      · have hb : Function.Bijective f.toIntertwiningMap :=
          ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).2 hf, hf⟩
        exact (hn ⟨Eρ.trans ((f.toIntertwiningMap.ofBijective hb).trans Eπ.symm)⟩).elim
      · exact congrArg (fun f : ρ.toRepresentation.IntertwiningMap π.toRepresentation =>
          LinearMap.toContinuousLinearMap f.toLinearMap) hf
    have hzero := _root_.ContRepresentation.character_orthonormal_distinct π hπ ρ hρ ha hz
    have hself := _root_.ContRepresentation.character_orthonormal_self π hπ ha hi
    have hclp : ρ.characterLp hρ = π.characterLp hπ := by
      rw [_root_.ContRepresentation.characterLp_def, _root_.ContRepresentation.characterLp_def, hc]
    rw [hclp, hself] at hzero
    exact one_ne_zero hzero

end DedekindZetaZeroFree.HarmonicVendor

end
