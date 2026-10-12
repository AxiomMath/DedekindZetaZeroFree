module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicKTypes
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.IrreducibleClassification

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.HarmonicVendor.HomogeneousRaw
open KPCplxCharacterHaar KPCplxHarmonicIntertwinerSpectrum
open scoped BigOperators

abbrev Polynomial := MvPolynomial (Fin 3) ℂ
abbrev Harmonic (ℓ : ℕ) := ↥(harmonicPolynomials ℓ)

def sphereMatrix (g : ComplexSU2) : Matrix (Fin 3) (Fin 3) ℂ :=
  let a := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  let b := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
  fun i j => (((!![
    b.re^2-b.im^2-a.re^2+a.im^2, 2*b.re*b.im-2*a.re*a.im, -2*a.re*b.re-2*a.im*b.im;
    -2*b.re*b.im-2*a.re*a.im, b.re^2-b.im^2+a.re^2-a.im^2, -2*a.im*b.re+2*a.re*b.im;
    2*a.re*b.re-2*a.im*b.im, 2*a.re*b.im+2*a.im*b.re, b.re^2+b.im^2-a.re^2-a.im^2]
      : Matrix (Fin 3) (Fin 3) ℝ) i j) : ℂ)

private lemma top_entries (g : ComplexSU2) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) ∧
    (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = -star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) := by
  have hg := Matrix.specialUnitaryGroup.star_eq_adjugate g
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hg
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hg
  simp [Matrix.star_eq_conjTranspose, Matrix.adjugate_fin_two, Matrix.trace_fin_two] at h00
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hg
  simp [Matrix.star_eq_conjTranspose, Matrix.adjugate_fin_two] at h10
  exact ⟨h00.symm, by simpa using (neg_eq_iff_eq_neg.mpr h10).symm⟩

theorem sphereMatrix_mul (g h : ComplexSU2) :
    sphereMatrix (g * h) = sphereMatrix h * sphereMatrix g := by
  obtain ⟨hg0,hg1⟩ := top_entries h
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [sphereMatrix, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      hg0,hg1, Complex.mul_re, Complex.mul_im] <;> ring

theorem sphereMatrix_one : sphereMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sphereMatrix]

def coefficientAction (g : ComplexSU2) : Polynomial →ₐ[ℂ] Polynomial :=
  MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (sphereMatrix g i j) * MvPolynomial.X j)

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

def u : Polynomial := MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1
def v : Polynomial := MvPolynomial.X 0 - MvPolynomial.C Complex.I * MvPolynomial.X 1
def w : Polynomial := MvPolynomial.X 2

theorem torus_weights (z : Circle) :
    coefficientAction (TauCeti.SU2.torusHom z) u = (z : ℂ)^2 • u ∧
    coefficientAction (TauCeti.SU2.torusHom z) v = (z : ℂ)^(-2 : ℤ) • v ∧
    coefficientAction (TauCeti.SU2.torusHom z) w = w := by
  have hz : (z : ℂ) = ((z : ℂ).re : ℂ) + Complex.I * ((z : ℂ).im : ℂ) := by
    exact (Complex.re_add_im _).symm.trans (by ring)
  have hinv : ((z : ℂ)^2)⁻¹ = (starRingEnd ℂ (z : ℂ)) ^ 2 := by
    rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, inv_pow]
  have hn : (((z : ℂ).re : ℂ)^2 + ((z : ℂ).im : ℂ)^2) = 1 := by
    have h : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
      simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe z
    exact_mod_cast h
  simp only [coefficientAction, u, v, w, map_add, map_sub, map_mul,
    MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  simp only [sphereMatrix, TauCeti.SU2.coe_torusHom, TauCeti.SU2.torusMatrix,
    Fin.sum_univ_succ, Circle.coe_inv, Complex.inv_re, Complex.inv_im]
  simp
  rw [hinv]
  constructor
  · rw [hz]
    simp only [MvPolynomial.smul_eq_C_mul, map_pow, map_add, map_mul]
    have hI : (MvPolynomial.C Complex.I : Polynomial)^2 = -1 := by
      rw [← map_pow, Complex.I_sq, map_neg, map_one]
    ring_nf
    have hI3 : (MvPolynomial.C Complex.I : Polynomial)^3 = -MvPolynomial.C Complex.I := by
      rw [pow_succ, hI]; ring
    simp [hI, hI3, map_ofNat]
    ring
  constructor
  · rw [hz]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
      MvPolynomial.smul_eq_C_mul, map_pow, map_neg]
    have hI : (MvPolynomial.C Complex.I : Polynomial)^2 = -1 := by
      rw [← map_pow, Complex.I_sq, map_neg, map_one]
    ring_nf
    have hI3 : (MvPolynomial.C Complex.I : Polynomial)^3 = -MvPolynomial.C Complex.I := by
      rw [pow_succ, hI]; ring
    simp [hI, hI3, map_ofNat]
    ring
  · simpa only [map_add, map_pow, map_one] using congrArg (MvPolynomial.C (σ := Fin 3)) hn

abbrev Homogeneous (n : ℕ) := ↥(MvPolynomial.homogeneousSubmodule (Fin 3) ℂ n)

instance homogeneousFiniteDimensional (n : ℕ) : FiniteDimensional ℂ (Homogeneous n) :=
  Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ n)

theorem coefficientAction_homogeneous (n : ℕ) (g : ComplexSU2) (p : Homogeneous n) :
    coefficientAction g p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℂ n := by
  classical
  have hp : (p : Polynomial).IsHomogeneous n := p.property
  change ((coefficientAction g) (p : Polynomial)).IsHomogeneous n
  simpa only [one_mul, coefficientAction] using hp.aeval
    (fun i => ∑ j, MvPolynomial.C (sphereMatrix g i j) * MvPolynomial.X j)
    (fun i => MvPolynomial.IsHomogeneous.sum _ _ _
      (fun j _ => MvPolynomial.isHomogeneous_C_mul_X _ _))

def homogeneousRepresentation (n : ℕ) : Representation ℂ ComplexSU2 (Homogeneous n) where
  toFun g :=
    { toFun p := ⟨coefficientAction g p, coefficientAction_homogeneous n g p⟩
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

abbrev HomogeneousExponent (n : ℕ) := {d : Fin 3 →₀ ℕ | d.degree = n}

open MvPolynomial

private lemma chalf : (C (1/2 : ℂ) : MvPolynomial (Fin 3) ℂ) * 2 = 1 := by
  have h := congrArg (C (σ := Fin 3)) (show (1/2 : ℂ) * 2 = 1 by norm_num)
  simpa only [map_mul, map_ofNat, map_one] using h
private lemma cI : (C Complex.I : MvPolynomial (Fin 3) ℂ)^2 = -1 := by
  rw [← map_pow, Complex.I_sq, map_neg, map_one]
def uvwSub : Polynomial →ₐ[ℂ] Polynomial := aeval ![u,v,w]
def uvwInv : Polynomial →ₐ[ℂ] Polynomial := aeval ![C (1/2 : ℂ) * (X 0 + X 1), C (1/(2*Complex.I) : ℂ) * (X 0 - X 1), X 2]
lemma uvw_left : uvwInv.comp uvwSub = AlgHom.id ℂ Polynomial := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [uvwInv,uvwSub,u,v,w, div_eq_mul_inv, mul_inv_rev] <;>
    ring_nf <;> (try simp only [cI]) <;>
    solve | rfl | (convert congrArg (fun p : Polynomial => p * X 0) chalf using 1 <;> ring) |
      (convert congrArg (fun p : Polynomial => p * X 1) chalf using 1 <;> ring)
lemma uvw_right : uvwSub.comp uvwInv = AlgHom.id ℂ Polynomial := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [uvwInv,uvwSub,u,v,w, div_eq_mul_inv, mul_inv_rev] <;>
    ring_nf <;> (try simp only [cI]) <;>
    solve | rfl | (convert congrArg (fun p : Polynomial => p * X 0) chalf using 1 <;> ring) |
      (convert congrArg (fun p : Polynomial => p * X 1) chalf using 1 <;> ring)
lemma uvw_hom (n : ℕ) (p : Homogeneous n) : (uvwSub p).IsHomogeneous n := by
  have hv (i : Fin 3) : (![u,v,w] i).IsHomogeneous 1 := by
    fin_cases i
    · exact (isHomogeneous_X ℂ 0).add (isHomogeneous_C_mul_X _ _)
    · exact (isHomogeneous_X ℂ 0).sub (isHomogeneous_C_mul_X _ _)
    · exact isHomogeneous_X ℂ 2
  simpa [uvwSub] using p.property.aeval ![u,v,w] hv
lemma inv_hom (n : ℕ) (p : Homogeneous n) : (uvwInv p).IsHomogeneous n := by
  have hv (i : Fin 3) : (![C (1/2 : ℂ) * (X 0 + X 1), C (1/(2*Complex.I) : ℂ) * (X 0 - X 1), X 2] i : Polynomial).IsHomogeneous 1 := by
    fin_cases i
    · exact ((isHomogeneous_X ℂ 0).add (isHomogeneous_X ℂ 1)).C_mul _
    · exact ((isHomogeneous_X ℂ 0).sub (isHomogeneous_X ℂ 1)).C_mul _
    · exact isHomogeneous_X ℂ 2
  simpa [uvwInv] using p.property.aeval _ hv
def uvwEquiv (n : ℕ) : Homogeneous n ≃ₗ[ℂ] Homogeneous n where
  toFun p := ⟨uvwSub p, uvw_hom n p⟩
  invFun p := ⟨uvwInv p, inv_hom n p⟩
  map_add' p q := Subtype.ext (map_add _ _ _)
  map_smul' c p := Subtype.ext (map_smul _ _ _)
  left_inv p := Subtype.ext (congrArg (fun f : Polynomial →ₐ[ℂ] Polynomial => f p) uvw_left)
  right_inv p := Subtype.ext (congrArg (fun f : Polynomial →ₐ[ℂ] Polynomial => f p) uvw_right)
def xyzBasis (n : ℕ) : Module.Basis (HomogeneousExponent n) ℂ (Homogeneous n) :=
  (basisRestrictSupport ℂ {d : Fin 3 →₀ ℕ | d.degree = n}).map
    (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported (Fin 3) ℂ n).symm)

theorem homogeneous_uvw_basis (n : ℕ) :
    ∃ b : Module.Basis (HomogeneousExponent n) ℂ (Homogeneous n),
      ∀ d, (b d : Polynomial) = u ^ (d.val 0) * v ^ (d.val 1) * w ^ (d.val 2) := by
  refine ⟨(xyzBasis n).map (uvwEquiv n), ?_⟩
  intro d
  change uvwSub ((xyzBasis n) d) = _
  have hb : ((xyzBasis n) d : Polynomial) = monomial d.val 1 := by
    change AddMonoidAlgebra.ofCoeff
      (((Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ) {d : Fin 3 →₀ ℕ | d.degree = n}).symm (Finsupp.single d 1)) : (Fin 3 →₀ ℕ) →₀ ℂ) = _
    rw [Finsupp.supportedEquivFinsupp_symm_single]
    rfl
  rw [hb]
  rw [uvwSub, aeval_monomial]
  simp [Finsupp.prod_fintype, Fin.prod_univ_three]

private lemma uvw_eigen (n : ℕ) (z : Circle) (d : HomogeneousExponent n) :
    coefficientAction (TauCeti.SU2.torusHom z) (u ^ d.val 0 * v ^ d.val 1 * w ^ d.val 2) =
    (z : ℂ) ^ (2 * ((d.val 0 : ℤ) - (d.val 1 : ℤ))) •
      (u ^ d.val 0 * v ^ d.val 1 * w ^ d.val 2) := by
  obtain ⟨hu,hv,hw⟩ := torus_weights z
  simp only [map_mul, map_pow, hu,hv,hw, smul_eq_C_mul, mul_pow]
  have hz : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  have he : ((z : ℂ)^2) ^ d.val 0 * ((z : ℂ)^(-2 : ℤ)) ^ d.val 1 =
      (z : ℂ) ^ (2 * ((d.val 0 : ℤ) - (d.val 1 : ℤ))) := by
    rw [← zpow_natCast (z : ℂ) 2]
    norm_num only [Nat.cast_ofNat]
    rw [← zpow_natCast ((z : ℂ) ^ (2 : ℤ)) (d.val 0),
      ← zpow_mul, ← zpow_natCast ((z : ℂ) ^ (-2 : ℤ)) (d.val 1), ← zpow_mul,
      ← zpow_add₀ hz]
    congr 1
    ring
  simp only [← map_pow]
  calc
    _ = C (((z : ℂ)^2) ^ d.val 0 * ((z : ℂ)^(-2 : ℤ)) ^ d.val 1) *
      (u ^ d.val 0 * v ^ d.val 1 * w ^ d.val 2) := by rw [map_mul]; ring
    _ = _ := by rw [he]
private lemma exponent_sum (n : ℕ) (d : HomogeneousExponent n) : d.val 0 + d.val 1 + d.val 2 = n := by
  have hd : d.val.degree = n := d.property
  simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_three] using hd

theorem homogeneous_torus_trace (n : ℕ) (z : Circle) :
    (homogeneousRepresentation n).character (TauCeti.SU2.torusHom z) =
      ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n - a + 1),
        (z : ℂ) ^ (2 * ((a : ℤ) - (b : ℤ))) := by
  classical
  letI : Fintype (HomogeneousExponent n) := (Finsupp.finite_of_degree_eq (σ := Fin 3) n).fintype
  obtain ⟨b,hb⟩ := homogeneous_uvw_basis n
  have he (d : HomogeneousExponent n) : homogeneousRepresentation n (TauCeti.SU2.torusHom z) (b d) =
      (z : ℂ) ^ (2 * ((d.val 0 : ℤ) - (d.val 1 : ℤ))) • b d := by
    apply Subtype.ext
    change coefficientAction _ (b d : Polynomial) = _
    change coefficientAction _ (b d : Polynomial) = _ • (b d : Polynomial)
    rw [hb]
    exact uvw_eigen n z d
  change LinearMap.trace ℂ _ _ = _
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, he, map_smul, Module.Basis.repr_self,
    Finsupp.smul_single, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  trans ∑ x ∈ (Finset.range (n+1)).sigma (fun a => Finset.range (n-a+1)),
    (z : ℂ) ^ (2 * ((x.1 : ℤ) - (x.2 : ℤ)))
  swap
  · exact Finset.sum_sigma _ _ _
  apply Finset.sum_bij (fun d _ => ⟨d.val 0,d.val 1⟩)
  · intro d hd
    have hs := exponent_sum n d
    simp only [Finset.mem_sigma, Finset.mem_range]
    omega
  · intro d hd e he hde
    apply Subtype.ext
    have h0 : d.val 0 = e.val 0 := congrArg Sigma.fst hde
    have h1 : d.val 1 = e.val 1 := by simpa using congrArg (fun x : Σ _ : ℕ, ℕ => x.2) hde
    have hs := exponent_sum n d
    have ht := exponent_sum n e
    ext i
    fin_cases i <;> simp_all <;> omega
  · intro x hx
    have hx' := Finset.mem_sigma.mp hx
    have ha := Finset.mem_range.mp hx'.1
    have hb := Finset.mem_range.mp hx'.2
    let d : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![x.1,x.2,n-x.1-x.2]
    have hd : d.degree = n := by
      simp [Finsupp.degree_eq_sum, Fin.sum_univ_three, d]
      omega
    refine ⟨⟨d,hd⟩, Finset.mem_univ _, ?_⟩
    rfl
  · intro d hd
    rfl

end DedekindZetaZeroFree.HarmonicVendor.HomogeneousRaw

end
